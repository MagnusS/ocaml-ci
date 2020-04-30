module Worker = Ocaml_ci_api.Worker

let main () =
  Logs.(set_level (Some Info));
  Logs.set_reporter @@ Logs_fmt.reporter ();
  Logs.info (fun f -> f "ocaml-ci-solver: waiting for request on stdin...");
  match Worker.Solve_request.of_yojson (Yojson.Safe.from_channel stdin) with
  | Error msg -> Fmt.failwith "Bad request: %s" msg
  | Ok request ->
    Logs.info (fun f -> f "Got request");
    let response =
      try Ok (Solver.solve request)
      with
      | Failure msg -> Error (`Msg msg)
      | ex -> Fmt.error_msg "%a" Fmt.exn ex
    in
    Yojson.Safe.to_channel stdout (Worker.Solve_response.to_yojson response)
