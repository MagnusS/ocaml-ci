val fmt_dockerfile :
  base:string ->
  ocamlformat_source:Analyse_ocamlformat.source option ->
  for_user:bool ->
  Dockerfile.t
(** A Dockerfile that checks the formatting. *)

val doc_dockerfile :
  base:string ->
  opam_files:string list ->
  selection:Ocaml_ci_api.Worker.Selection.t ->
  for_user:bool ->
  Dockerfile.t
(** A Dockerfile that checks that the documentation in [./src/] builds without warnings. *)
