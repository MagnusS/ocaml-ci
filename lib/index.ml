let src = Logs.Src.create "ocaml_ci.index" ~doc:"ocaml-ci indexer"
module Log = (val Logs.src_log src : Logs.LOG)

module Db = Current.Db

type t = {
  db : Sqlite3.db;
  record : Sqlite3.stmt;
  owner_exists : Sqlite3.stmt;
  repo_exists : Sqlite3.stmt;
  get_jobs : Sqlite3.stmt;
  get_job : Sqlite3.stmt;
  list_owners : Sqlite3.stmt;
  list_repos : Sqlite3.stmt;
  full_hash : Sqlite3.stmt;
}

type job_state = [`Not_started | `Active | `Failed of string | `Passed | `Aborted ] [@@deriving show]

let or_fail label x =
  match x with
  | Sqlite3.Rc.OK -> ()
  | err -> Fmt.failwith "Sqlite3 %s error: %s" label (Sqlite3.Rc.to_string err)

let is_valid_hash hash =
  let open Astring in
  String.length hash >= 6 && String.for_all Char.Ascii.is_alphanum hash

let db = lazy (
  let db = Lazy.force Current.Db.v in
  Current_cache.Db.init ();
  Sqlite3.exec db "CREATE TABLE IF NOT EXISTS ci_build_index ( \
                   owner     TEXT NOT NULL, \
                   name      TEXT NOT NULL, \
                   hash      TEXT NOT NULL, \
                   variant   TEXT NOT NULL, \
                   job_id    TEXT, \
                   PRIMARY KEY (owner, name, hash, variant))" |> or_fail "create table";
  let record = Sqlite3.prepare db "INSERT OR REPLACE INTO ci_build_index \
                                     (owner, name, hash, variant, job_id) \
                                     VALUES (?, ?, ?, ?, ?)" in
  let list_owners = Sqlite3.prepare db "SELECT DISTINCT owner FROM ci_build_index" in
  let list_repos = Sqlite3.prepare db "SELECT DISTINCT name FROM ci_build_index WHERE owner = ?" in
  let owner_exists = Sqlite3.prepare db "SELECT EXISTS (SELECT 1 FROM ci_build_index \
                                                        WHERE owner = ?)" in
  let repo_exists = Sqlite3.prepare db "SELECT EXISTS (SELECT 1 FROM ci_build_index \
                                                       WHERE owner = ? AND name = ?)" in
  let get_jobs = Sqlite3.prepare db "SELECT ci_build_index.variant, ci_build_index.job_id, cache.ok, cache.outcome \
                                     FROM ci_build_index \
                                     LEFT JOIN cache ON ci_build_index.job_id = cache.job_id \
                                     WHERE ci_build_index.owner = ? AND ci_build_index.name = ? AND ci_build_index.hash = ?" in
  let get_job = Sqlite3.prepare db "SELECT job_id FROM ci_build_index \
                                     WHERE owner = ? AND name = ? AND hash = ? AND variant = ?" in
  let full_hash = Sqlite3.prepare db "SELECT DISTINCT hash FROM ci_build_index \
                                      WHERE owner = ? AND name = ? AND hash LIKE ?" in
  { db; record; owner_exists; repo_exists; get_jobs; get_job; list_owners; list_repos; full_hash }
)

let has_changed t ~owner ~name ~hash (variant, job_id) =
  match job_id, Db.query_some t.get_job Sqlite3.Data.[ TEXT owner; TEXT name; TEXT hash; TEXT variant ] with
  | None, Some [ Sqlite3.Data.NULL ] -> false
  | Some j1, Some [ Sqlite3.Data.TEXT j2 ] -> j1 <> j2
  | _ -> true

let record ~repo ~hash jobs =
  let { Current_github.Repo_id.owner; name } = repo in
  let t = Lazy.force db in
  jobs |> List.filter (has_changed t ~owner ~name ~hash) |> List.iter (fun (variant, job_id) ->
      Log.info (fun f -> f "@[<h>Index.record %s/%s %s %s -> %a@]"
                   owner name (Astring.String.with_range ~len:6 hash) variant Fmt.(option ~none:(unit "-") string) job_id);
      let job_id =
        match job_id with
        | None -> Sqlite3.Data.NULL
        | Some job_id -> Sqlite3.Data.TEXT job_id
      in
      Db.exec t.record Sqlite3.Data.[ TEXT owner; TEXT name; TEXT hash; TEXT variant; job_id ]
    )

let is_known_owner owner =
  let t = Lazy.force db in
  match Db.query_one t.owner_exists Sqlite3.Data.[ TEXT owner ] with
  | Sqlite3.Data.[ INT x ] -> x = 1L
  | _ -> failwith "owner_exists failed!"

let is_known_repo ~owner ~name =
  let t = Lazy.force db in
  match Db.query_one t.repo_exists Sqlite3.Data.[ TEXT owner; TEXT name ] with
  | Sqlite3.Data.[ INT x ] -> x = 1L
  | _ -> failwith "repo_exists failed!"

let get_full_hash ~owner ~name short_hash =
  let t = Lazy.force db in
  if is_valid_hash short_hash then (
    match Db.query t.full_hash Sqlite3.Data.[ TEXT owner; TEXT name; TEXT (short_hash ^ "%") ] with
    | [] -> Error `Unknown
    | [Sqlite3.Data.[ TEXT hash ]] -> Ok hash
    | [_] -> failwith "full_hash: invalid result!"
    | _ :: _ :: _ -> Error `Ambiguous
  ) else Error `Invalid

let get_jobs ~owner ~name hash =
  let t = Lazy.force db in
  Db.query t.get_jobs Sqlite3.Data.[ TEXT owner; TEXT name; TEXT hash ]
  |> List.map @@ function
  | Sqlite3.Data.[ TEXT variant; TEXT job_id; NULL; NULL ] ->
    let outcome = if Current.Job.lookup_running job_id = None then `Aborted else `Active in
    variant, outcome
  | Sqlite3.Data.[ TEXT variant; TEXT _; INT ok; BLOB outcome ] ->
    let outcome =
      if ok = 1L then `Passed else `Failed outcome
    in
    variant, outcome
  | Sqlite3.Data.[ TEXT variant; NULL; NULL; NULL ] ->
    variant, `Not_started
  | row ->
    Fmt.failwith "get_jobs: invalid result: %a" Db.dump_row row

let get_job ~owner ~name ~hash ~variant =
  let t = Lazy.force db in
  match Db.query_some t.get_job Sqlite3.Data.[ TEXT owner; TEXT name; TEXT hash; TEXT variant ] with
  | None -> Error `No_such_variant
  | Some Sqlite3.Data.[ TEXT id ] -> Ok (Some id)
  | Some Sqlite3.Data.[ NULL ] -> Ok None
  | _ -> failwith "get_job: invalid result!"

let list_owners () =
  let t = Lazy.force db in
  Db.query t.list_owners []
  |> List.map @@ function
  | Sqlite3.Data.[ TEXT x ] -> x
  | _ -> failwith "list_owners: invalid data returned!"

let list_repos owner =
  let t = Lazy.force db in
  Db.query t.list_repos Sqlite3.Data.[ TEXT owner ]
  |> List.map @@ function
  | Sqlite3.Data.[ TEXT x ] -> x
  | _ -> failwith "list_repos: invalid data returned!"

module Repo_map = Map.Make(Current_github.Repo_id)

let active_refs = ref Repo_map.empty

let set_active_refs ~repo (refs : (string * string) list) =
  active_refs := Repo_map.add repo refs !active_refs

let get_active_refs repo =
  Repo_map.find_opt repo !active_refs |> Option.value ~default:[]