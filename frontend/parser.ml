(* Expressions mirror the extracted calculus. Optional type/val headers describe
   the initial context, not additional expression forms or definitions. *)
open Fresco_guess

type token = Id of string | Fun | Forall | Type | Val | Unit | Lpar | Rpar
           | Colon | Arrow | Dot | Semi | Freeze | Thaw | End

type program = { context : aenv; type_names : (Atom.atom * string) list;
                 expression : exp }

type located = { token : token; line : int; column : int }
exception Error of int * int * string
let error p message = raise (Error (p.line, p.column, message))

let lex source =
  let n = String.length source in
  let letter = function 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false in
  let ident c = letter c || match c with '0'..'9' | '\'' -> true | _ -> false in
  let rec scan i line column acc =
    let emit token width =
      scan (i + width) line (column + width) ({token; line; column} :: acc) in
    if i = n then List.rev ({token = End; line; column} :: acc)
    else match source.[i] with
    | ' ' | '\t' | '\r' -> scan (i + 1) line (column + 1) acc
    | '\n' -> scan (i + 1) (line + 1) 1 acc
    | '-' when i + 1 < n && source.[i + 1] = '-' ->
        let j = ref (i + 2) in
        while !j < n && source.[!j] <> '\n' do incr j done;
        scan !j line (column + !j - i) acc
    | '-' when i + 1 < n && source.[i + 1] = '>' -> emit Arrow 2
    | '{' when i + 1 < n && source.[i + 1] = '|' -> emit Freeze 2
    | '|' when i + 1 < n && source.[i + 1] = '}' -> emit Thaw 2
    | '(' -> emit Lpar 1 | ')' -> emit Rpar 1 | ':' -> emit Colon 1
    | '.' -> emit Dot 1 | ';' -> emit Semi 1
    | c when letter c ->
        let j = ref (i + 1) in
        while !j < n && ident source.[!j] do incr j done;
        let word = String.sub source i (!j - i) in
        let token = match word with
          | "fun" -> Fun | "forall" -> Forall | "unit" -> Unit
          | "type" -> Type | "val" -> Val | _ -> Id word in
        emit token (!j - i)
    | c -> raise (Error (line, column, Printf.sprintf "unexpected character %C" c))
  in scan 0 1 1 []

let parse source =
  let tokens = ref (lex source) in
  let peek () = List.hd !tokens in
  let take () = let p = peek () in tokens := List.tl !tokens; p in
  let accept t = if (peek ()).token = t then (ignore (take ()); true) else false in
  let expect t description = if not (accept t) then error (peek ()) ("expected " ^ description) in
  let name () = let p = take () in match p.token with
    | Id x when x <> "_" -> x
    | _ -> error p "expected a binder name" in
  let context = ref [] and types = ref [] and terms = ref [] in
  let fresh () = Atom.fresh (List.map fst !context) in
  let index x env =
    let rec go i = function
      | [] -> None
      | y :: ys -> if x = y then Some i else go (i + 1) ys
    in go 0 env in
  let free p x names kind = match List.assoc_opt x names with
    | Some a -> a
    | None -> error p ("unbound " ^ kind ^ " variable " ^ x) in
  let rec typ env =
    if accept Forall then (
      let rec bind env =
        let x = name () in
        let body = if accept Dot then typ (x :: env) else bind (x :: env) in
        Ptyp_all body
      in bind env)
    else let a = type_atom env in
      if accept Arrow then Ptyp_arrow (a, typ env) else a
  and type_atom env =
    let p = take () in match p.token with
    | Unit -> Ptyp_unit
    | Id x -> (match index x env with
        | Some i -> Ptyp_var_b i
        | None -> Ptyp_var_f (free p x !types "type"))
    | Lpar -> let a = typ env in expect Rpar "')'"; a
    | _ -> error p "expected a type (unit, bound variable, forall, or parentheses)"
  in
  let rec expr env =
    if accept Fun then lambda env
    else let e = application env in
      if accept Colon then Exp_anno (e, typ []) else e
  and lambda env =
    let p = take () in
    let x, annotation = match p.token with
      | Id x -> x, None
      | Lpar -> let x = name () in expect Colon "':'";
          let a = typ [] in expect Rpar "')'"; x, Some a
      | _ -> error p "expected a function parameter" in
    let body = if accept Arrow then expr (x :: env) else lambda (x :: env) in
    match annotation with None -> Exp_abs body | Some a -> Exp_abs_anno (a, body)
  and application env =
    let rec more e = match (peek ()).token with
      | Id _ | Lpar | Freeze -> let arg = atom env in more (Exp_app (e, arg))
      | _ -> e in
    more (atom env)
  and atom env =
    let p = take () in match p.token with
    | Id "_" -> error p "wildcard '_' cannot be referenced"
    | Id x -> (match index x env with
        | Some i -> Exp_var_b i
        | None -> Exp_var_f (free p x !terms "term"))
    | Lpar -> if accept Rpar then Exp_unit else (
        let e = expr env in expect Rpar "')'"; e)
    | Freeze -> let e = expr env in expect Thaw "'|}'"; Exp_freeze e
    | _ -> error p "expected an expression"
  in
  let rec declarations () =
    let p = peek () in
    let declare names binding =
      let x = name () in
      if List.mem_assoc x !names then error p ("duplicate declaration " ^ x);
      let b = binding () in
      expect Semi "';'";
      let a = fresh () in
      names := (x, a) :: !names; context := (a, b) :: !context;
      declarations () in
    if accept Type then declare types (fun () -> Abind_tvar)
    else if accept Val then declare terms (fun () ->
      expect Colon "':'"; Abind_var_typ (typ []))
  in
  declarations ();
  let expression = expr [] in expect End "end of file";
  {context = !context; type_names = List.map (fun (x, a) -> a, x) !types; expression}
