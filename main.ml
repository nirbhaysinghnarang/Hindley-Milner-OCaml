type ty =
  | Int
  | String
  | Fun of ty * ty

(* Define a data structure to represent the terms of your programming language. *)
type term =
  | Var of string
  | Const of int
  | Plus of term * term
  | Concat of term * term
  | Lam of string * ty * term
  | App of term * term

(* Implement a type inference function that takes a term and returns its type. *)
let rec infer (env : (string * ty) list) (t : term) : ty =
  match t with
  | Var x -> List.assoc x env
  | Const _ -> Int
  | Plus (t1, t2) ->
      let ty1 = infer env t1 in
      let ty2 = infer env t2 in
      if ty1 = Int && ty2 = Int then Int
      else failwith "Plus: expected Int, got something else"
  | Concat (t1, t2) ->
      let ty1 = infer env t1 in
      let ty2 = infer env t2 in
      if ty1 = String && ty2 = String then String
      else failwith "Concat: expected String, got something else"
  | Lam (x, ty, t) ->
      let env' = (x, ty) :: env in
      let ty_body = infer env' t in
      Fun (ty, ty_body)
  | App (t1, t2) ->
      let ty1 = infer env t1 in
      let ty2 = infer env t2 in
      begin match ty1 with
      | Fun (ty_arg, ty_ret) ->
          if ty2 = ty_arg then ty_ret
          else failwith "App: type mismatch"
      | _ -> failwith "App: expected function type"
      end


  (* Define a function to parse input strings into terms. *)
let rec parse (input : string) : term =
  (* Remove leading and trailing whitespace. *)
  let input = String.trim input in
  (* Match the first character of the input string. *)
  match input.[0] with
  (* If the first character is a digit, parse an integer constant. *)
  | '0' .. '9' ->
      Const (int_of_string input)
  (* If the first character is a letter, parse a variable. *)
  | 'a' .. 'z' | 'A' .. 'Z' ->
      Var input
  (* If the first character is an open parenthesis, parse a function application or lambda expression. *)
  | '(' ->
      print_endline("here");
      let len = String.length input in
      (* Find the matching close parenthesis. *)
      let rec find_close i =
        if i >= len then failwith "unbalanced parentheses"
        else if input.[i] = '(' then find_close (i + 1)
        else if input.[i] = ')' then i
        else find_close (i + 1)
      in
      let i = find_close 1 in
      (* Split the input string into the function and argument parts. *)
      let f_str = String.trim (String.sub input 1 (i - 1)) in
      let arg_str = String.trim (String.sub input (i + 1) (len - i - 1)) in
      print_endline(f_str);
      (* Parse the function and argument. *)
      let f = parse f_str in
      let arg = parse arg_str in
      (* If the function is "lam", parse a lambda expression. Otherwise, parse a function application. *)
      if f_str = "lam" then
        (* Split the argument into its components. *)
        let j = String.index arg_str ':' in
        let x = String.trim (String.sub arg_str 0 j) in
        let ty_str = String.trim (String.sub arg_str (j + 1) (String.length arg_str - j - 1)) in
        let ty =
          match ty_str with
          | "Int" -> Int
          | "String" -> String
          | _ -> failwith ("invalid type: " ^ ty_str)
        in
        Lam (x, ty, arg)
      else
        App (f, arg)
  | x ->
      failwith ("invalid input: " ^ input)
    


(* Define a function to print types as strings. *)
let rec string_of_ty (ty : ty) : string =
  match ty with
  | Int -> "Int"
  | String -> "String"
  | Fun (ty1, ty2) ->
      let str1 = string_of_ty ty1 in
      let str2 = string_of_ty ty2 in
      "(" ^ str1 ^ " -> " ^ str2 ^ ")"

(* Define the REPL loop. *)
let rec repl () : unit =
  print_string "> ";
  match read_line () with
  | exception End_of_file -> ()
  | input ->
      try
        let t = parse input in
        let ty = infer [] t in
        let ty_str = string_of_ty ty in
        print_endline ("Type: " ^ ty_str);
      with
      | Failure s -> print_endline s;
      repl ()