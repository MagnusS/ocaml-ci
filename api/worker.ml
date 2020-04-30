(** Communication between ocaml-ci and the workers. *)

(** Variables describing a build environment. *)
module Vars = struct
  type t = {
    arch : string;
    os : string;
    os_family : string;
    os_distribution : string;
    os_version : string;
    ocaml_version : string;
  } [@@deriving yojson]
end

(** A request to select sets of packages for the builds. *)
module Solve_request = struct
  type t = {
    opam_repository : string;                   (** Path of opam repository checkout. *)
    root_pkgs : (string * string) list;         (** Name and contents of top-level opam files. *)
    pinned_pkgs : (string * string) list;       (** Name and contents of other pinned opam files. *)
    platforms : (string * Vars.t) list;         (** Possible build platforms, by ID. *)
  } [@@deriving yojson]
end

(** A set of packages for a single build. *)
module Selection = struct
  type t = {
    id : string;                        (** The platform ID from the request. *)
    packages : string list;             (** The selected packages ("name.version"). *)
    commit : string;                    (** A commit in opam-repository to use. *)
  } [@@deriving yojson]
end
