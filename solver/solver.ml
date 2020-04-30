open Lwt.Infix

let src = Logs.Src.create "ocaml_ci_solver" ~doc:"ocaml-ci dependency solver"
module Log = (val Logs.src_log src : Logs.LOG)

module Selection = Ocaml_ci_api.Worker.Selection
module Vars = Ocaml_ci_api.Worker.Vars

let ( / ) = Filename.concat

let with_dir path fn =
  let ch = Unix.opendir path in
  match fn ch with
  | x -> Unix.closedir ch; x
  | exception ex -> Unix.closedir ch; raise ex

let list_dir path =
  let rec aux ch =
    match Unix.readdir ch with
    | name -> name :: aux ch
    | exception End_of_file -> []
  in
  with_dir path aux

module Context = struct
  type rejection = UserConstraint of OpamFormula.atom

  type t = {
    vars : Vars.t;
    packages_dir : string;
    pins : (OpamPackage.Version.t * OpamFile.OPAM.t) OpamPackage.Name.Map.t;
    constraints : OpamFormula.version_constraint OpamTypes.name_map;    (* User-provided constraints *)
    test : OpamPackage.Name.Set.t;
  }

  let load t pkg =
    let { OpamPackage.name; version = _ } = pkg in
    match OpamPackage.Name.Map.find_opt name t.pins with
    | Some (_, opam) -> opam
    | None ->
      let opam_path = t.packages_dir / OpamPackage.Name.to_string name / OpamPackage.to_string pkg / "opam" in
      OpamFile.OPAM.read (OpamFile.make (OpamFilename.raw opam_path))

  let user_restrictions t name =
    OpamPackage.Name.Map.find_opt name t.constraints

  let env t pkg v =
    if List.mem v OpamPackageVar.predefined_depends_variables then None
    else match OpamVariable.Full.to_string v with
      | "version" -> Some (OpamTypes.S (OpamPackage.Version.to_string (OpamPackage.version pkg)))
      | "arch" -> Some (OpamTypes.S t.vars.arch)
      | "os" -> Some (OpamTypes.S t.vars.os)
      | "os-distribution" -> Some (OpamTypes.S t.vars.os_distribution)
      | "os-version" -> Some (OpamTypes.S t.vars.os_version)
      | "os-family" -> Some (OpamTypes.S t.vars.os_family)
      | _ ->
        OpamConsole.warning "Unknown variable %S" (OpamVariable.Full.to_string v);
        None

  let filter_deps t pkg f =
    let test = OpamPackage.Name.Set.mem (OpamPackage.name pkg) t.test in
    f
    |> OpamFilter.partial_filter_formula (env t pkg)
    |> OpamFilter.filter_deps ~build:true ~post:true ~test ~doc:false ~dev:false ~default:false

  let candidates t name =
    match OpamPackage.Name.Map.find_opt name t.pins with
    | Some (version, _) -> [version, None]
    | None ->
      match list_dir (t.packages_dir / OpamPackage.Name.to_string name) with
      | versions ->
        let user_constraints = user_restrictions t name in
        versions
        |> List.filter_map (fun dir ->
            match OpamPackage.of_string_opt dir with
            | Some pkg -> Some (OpamPackage.version pkg)
            | None -> None
          )
        |> List.sort (fun a b -> OpamPackage.Version.compare b a)
        |> List.map (fun v ->
            match user_constraints with
            | Some test when not (OpamFormula.check_version_formula (OpamFormula.Atom test) v) ->
              v, Some (UserConstraint (name, Some test))  (* Reject *)
            | _ -> v, None
          )
      | exception Unix.Unix_error (Unix.ENOENT, _, _) ->
        OpamConsole.log "opam-zi" "Package %S not found!" (OpamPackage.Name.to_string name);
        []

  let pp_rejection f = function
    | UserConstraint x -> Fmt.pf f "Rejected by user-specified constraint %s" (OpamFormula.string_of_atom x)
end

module Input = Opam_zi.Model(Context)
module Solver = Zeroinstall_solver.Make(Input)
module Diagnostics = Zeroinstall_solver.Diagnostics(Solver.Output)

let requirements ~context pkgs =
  let role =
    match pkgs with
    | [pkg] -> Input.role context pkg
    | pkgs ->
      let impl = Input.virtual_impl ~context ~depends:pkgs () in
      Input.virtual_role [impl]
  in
  { Input.role; command = None }

let ocaml_name = OpamPackage.Name.of_string "ocaml"

(* Use "git-log" to find the oldest commit with these package versions.
   This avoids invalidating the Docker build cache on every update to opam-repository. *)
let oldest_commit_with ~opam_repository pkgs =
  let paths =
    pkgs |> List.filter_map (fun pkg ->
        let { OpamPackage.name; version } = OpamPackage.of_string pkg in
        let name = OpamPackage.Name.to_string name in
        let version = OpamPackage.Version.to_string version in
        if version = "dev" then None
        else Some (Printf.sprintf "%s/%s.%s" name name version)
      )
  in
  let cmd = "git" :: "-C" :: opam_repository / "packages" :: "log" :: "-n" :: "1" :: "--format=format:%H" :: paths in
  let cmd = ("", Array.of_list cmd) in
  Process.pread cmd >|= String.trim

let version_2 = OpamVersion.of_string "2"

let parse_opam (name, contents) =
  let pkg = OpamPackage.of_string name in
  let opam = OpamFile.OPAM.read_from_string contents in
  let opam_version = OpamFile.OPAM.opam_version opam in
  if OpamVersion.compare opam_version version_2 < 0 then
    Fmt.failwith "Package %S uses unsupported opam version %s (need >= 2)" name (OpamVersion.to_string opam_version);
  OpamPackage.name pkg, (OpamPackage.version pkg, opam)

let run_child ~opam_repository ~pins ~root_pkgs vars =
  let ocaml_version = OpamPackage.Version.of_string vars.Vars.ocaml_version in
  let context = { Context.
                  vars;
                  packages_dir = opam_repository / "packages";
                  pins;
                  constraints = OpamPackage.Name.Map.singleton ocaml_name (`Eq, ocaml_version);
                  test = OpamPackage.Name.Set.of_list root_pkgs;
                } in
  let req = requirements ~context root_pkgs in
  let t0 = Unix.gettimeofday () in
  let r = Solver.do_solve ~closest_match:false req in
  let t1 = Unix.gettimeofday () in
  Printf.printf "%.2f\n" (t1 -. t0);
  match r with
  | Some sels ->
    let pkgs =
      sels
      |> Solver.Output.to_map |> Solver.Output.RoleMap.to_seq |> List.of_seq
      |> List.filter_map (fun (_role, sel) -> Input.version (Solver.Output.unwrap sel))
    in
    let packages = List.map OpamPackage.to_string pkgs in
    Printf.printf "+%s%!" @@ String.concat " " packages
  | None ->
    let msg =
      Solver.do_solve ~closest_match:true req
      |> Option.get
      |> Diagnostics.get_failure_reason ~verbose:false
    in
    Printf.printf "-%s%!" msg

let rec waitpid_non_intr pid =
  try Unix.waitpid [] pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_non_intr pid

let check_exit_status = function
  | Unix.WEXITED 0 -> ()
  | Unix.WEXITED code -> Fmt.failwith "Child returned error exit status %d" code
  | Unix.WSIGNALED signal -> Fmt.failwith "Child aborted (signal %d)" signal
  | Unix.WSTOPPED signal -> Fmt.failwith "Child is currently stopped (signal %d)" signal

let spawn_child run (id, vars) =
  let r, w = Unix.pipe ~cloexec:true () in
  match Unix.fork () with
  | 0 -> (* We are the child *)
    begin
      try
        Unix.close r;
        Unix.dup2 w Unix.stdout;
        run vars;
        exit 0
      with ex ->
        Printf.printf "-%s\n%!" (Printexc.to_string ex);
        exit 1
    end
  | child ->
    Unix.close w;
    id, child, r

let solve { Ocaml_ci_api.Worker.Solve_request.opam_repository; root_pkgs; pinned_pkgs; platforms } =
  let root_pkgs = List.map parse_opam root_pkgs in
  let pinned_pkgs = List.map parse_opam pinned_pkgs in
  let pins =
    root_pkgs @ pinned_pkgs
    |> OpamPackage.Name.Map.of_list
  in
  let root_pkgs = List.map fst root_pkgs in
  let pp_name f name = Fmt.string f (OpamPackage.Name.to_string name) in
  Log.info (fun f -> f "Solving for %a" (Fmt.(list ~sep:comma) pp_name) root_pkgs);
  let jobs = List.map (spawn_child (run_child ~opam_repository ~pins ~root_pkgs)) platforms in
  let results =
    jobs |> List.map (fun (id, pid, from_child) ->
        let buf = Bytes.create 4096 in
        let results = Buffer.create 1024 in
        let rec read () =
          let got = Unix.read from_child buf 0 (Bytes.length buf) in
          if got > 0 then (
            Buffer.add_subbytes results buf 0 got;
            read ()
          ) else (
            Unix.close from_child;
            Buffer.contents results
          )
        in
        let results = read () in
        waitpid_non_intr pid |> snd |> check_exit_status;
        match Astring.String.cut ~sep:"\n" results with
        | None -> Fmt.failwith "Missing newline in solver results: %S" results
        | Some (time, results) ->
          if String.length results = 0 then Fmt.failwith "No output from solve worker!";
          match results.[0] with
          | '+' ->
            Log.info (fun f -> f "%s: found solution in %s s" id time);
            let packages =
              Astring.String.with_range ~first:1 results
              |> Astring.String.cuts ~sep:" "
            in
            (id, Ok packages)
          | '-' ->
            Log.info (fun f -> f "%s: eliminated all possibilities in %s s" id time);
            let msg = results |> Astring.String.with_range ~first:1 in
            (id, Error msg)
          | _ ->
            Fmt.failwith "BUG: bad output: %s" results
      ) in
  (* Now all the sub-processes are gone, we can safely start Lwt. *)
  Lwt_main.run begin
    results
    |> Lwt_list.map_p (fun (id, output) ->
        match output with
        | Ok packages ->
          oldest_commit_with packages ~opam_repository >|= fun commit ->
          id, Ok { Selection.id; packages; commit }
        | Error _ as e -> Lwt.return (id, e)
      )
    >|= List.filter_map (fun (id, result) ->
        Log.info (fun f -> f "= %s =" id);
        match result with
        | Ok result ->
          Log.info (fun f -> f "-> @[<hov>%a@]" Fmt.(list ~sep:sp string) result.Selection.packages);
          Log.info (fun f -> f "(valid since opam-repository commit %s)" result.Selection.commit);
          Some result
        | Error msg ->
          Log.info (fun f -> f "%s" msg);
          None
      )
  end
