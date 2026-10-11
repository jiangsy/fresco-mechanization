let read channel =
  let buffer = Buffer.create 4096 in
  (try while true do Buffer.add_channel buffer channel 1 done with End_of_file -> ());
  Buffer.contents buffer

let check filename =
  try
    let source = if filename = "-" then read stdin else
      let channel = open_in_bin filename in
      Fun.protect ~finally:(fun () -> close_in channel) (fun () -> read channel) in
    let program = Parser.parse source in
    let open Fresco_guess in
    let result = match program.context with
      | [] -> fresco_infer program.expression
      | context ->
          let supply = List.fold_left (fun s (a, _) -> AtomSetImpl.add a s)
            (entry_supply Pskl_ghost program.expression) context in
          e_typing_run supply Mode_ti context Pskl_ghost program.expression in
    match result with
    | Some result ->
        Printf.printf "%s: %s\n%!" filename
          (Printer.typ result.ty_ctx program.type_names result.ty_out); 0
    | None -> Printf.eprintf "%s: type error: expression is not typable\n%!" filename; 1
  with
  | Parser.Error (line, column, message) ->
      Printf.eprintf "%s:%d:%d: %s\n%!" filename line column message; 2
  | Sys_error message -> Printf.eprintf "%s\n%!" message; 2

let () =
  let files = ref [] in
  Arg.parse ["-", Arg.Unit (fun () -> files := "-" :: !files), "Read standard input"]
    (fun file -> files := file :: !files)
    "Usage: fresco FILE... (use - for stdin)";
  if !files = [] then (Printf.eprintf "Usage: fresco FILE... (use - for stdin)\n"; exit 2);
  let status = List.fold_left (fun status file -> max status (check file)) 0 (List.rev !files) in
  exit status
