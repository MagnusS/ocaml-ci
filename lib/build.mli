module Spec : sig
  type t

  val opam :
    label:string ->
    selection:Ocaml_ci_api.Worker.Selection.t ->
    analysis:Analyse.Analysis.t ->
    [ `Build | `Lint of [`Doc | `Fmt] ] ->
    t

  val duniverse : label:string -> variant:string -> t

  val pp : t Fmt.t
  val compare : t -> t -> int
  val label : t -> string
end

(** Build and test all the opam packages in a given build context on the given platform.
    [~repo] is the ID of the repository-under-test on GitHub. *)
val v :
  platforms:Platform.t list Current.t ->
  repo:Current_github.Repo_id.t Current.t ->
  spec:Spec.t Current.t ->
  Current_git.Commit.t Current.t ->
  ([> `Built | `Checked ] Current_term.Output.t * Current.job_id option) Current.t
