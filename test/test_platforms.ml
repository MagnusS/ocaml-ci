let debian_10_vars ocaml_version =
  { Ocaml_ci.Platform.Vars.
    os = "debian";
    arch = "x86_64";
    os_family = "debian";
    os_distribution = "debian";
    os_version = "10";
    ocaml_version
  }

let v = [
  "debian-10-ocaml-4.10", debian_10_vars "4.10";
  "debian-10-ocaml-4.09", debian_10_vars "4.09";
  "debian-10-ocaml-4.08", debian_10_vars "4.08";
  "debian-10-ocaml-4.07", debian_10_vars "4.07";
]
