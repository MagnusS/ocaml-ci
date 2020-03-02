module Selection = Ocaml_ci_api.Worker.Selection

let main () =
  Logs.(set_level (Some Info));
  Logs.set_reporter @@ Logs_fmt.reporter ();
  Logs.info (fun f -> f "ocaml-ci-solver: waiting for request on stdin...");
  match Ocaml_ci_api.Worker.Solve_request.of_yojson (Yojson.Safe.from_channel stdin) with
  | Error msg -> Fmt.failwith "Bad request: %s" msg
  | Ok request ->
    Logs.info (fun f -> f "Got request");
    let response = Solver.solve request in
    let json = [%derive.to_yojson:Selection.t list] response in
    Yojson.Safe.to_channel stdout json
