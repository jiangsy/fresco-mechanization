open Fresco_guess

let typ context type_names t =
  let variables = ref [] in
  let variable x =
    match List.assoc_opt x !variables with
    | Some name -> name
    | None ->
        let name = "?m" ^ string_of_int (List.length !variables) in
        variables := (x, name) :: !variables; name
  in
  let paren needed s = if needed then "(" ^ s ^ ")" else s in
  let rec print env precedence = function
    | Ptyp_unit -> "unit"
    | Ptyp_var_b i -> List.nth env i
    | Ptyp_var_f x ->
        (match List.assoc_opt x context with
         | Some (Abind_flex_mono_def a) -> print env precedence a
         | _ -> (match List.assoc_opt x type_names with
             | Some name -> name | None -> variable x))
    | Ptyp_arrow (a, b) ->
        let left = print env 1 a in
        let right = print env 0 b in
        paren (precedence > 0) (left ^ " -> " ^ right)
    | Ptyp_all body ->
        let rec fresh i =
          let x = "a" ^ string_of_int i in
          if List.mem x env || List.exists (fun (_, name) -> name = x) type_names
          then fresh (i + 1) else x in
        let x = fresh (List.length env) in
        paren (precedence > 0) ("forall " ^ x ^ ". " ^ print (x :: env) 0 body)
  in print [] 0 t
