open Ast

(** The error message produced if a variable is unbound. *)
let unbound_var_err = "Unbound variable"

(** The error message produced if binary operators and their operands do
    not have the correct types. *)
let bop_err = "Operator and operand type mismatch"

(** The error message produced if the guard of an [if] does not have
    type [bool]. *)
let if_guard_err = "Guard of if must have type bool"

(** [is_value e] is whether [e] is a value. *)
let is_value : expr -> bool = function
  | Int _
  | Bool _
  | Fun _ ->
      true
  | Var _
  | Let _
  | Binop _
  | If _
  | App _ ->
      false

(** [subst e v x] is [e] with [v] substituted for [x], that is,
    [e{v/x}]. *)
let rec subst e v x =
  match e with
  | Var y -> if x = y then v else e
  | Int _ -> e
  | Bool _ -> e
  | Binop (bop, e1, e2) -> Binop (bop, subst e1 v x, subst e2 v x)
  | Let (y, e1, e2) ->
      let e1' = subst e1 v x in
      if x = y then Let (y, e1', e2) else Let (y, e1', subst e2 v x)
  | If (e1, e2, e3) -> If (subst e1 v x, subst e2 v x, subst e3 v x)
  | Fun (y, e) -> if x = y then Fun (y, e) else Fun (y, subst e v x)
  | App (e1, e2) -> App (subst e1 v x, subst e2 v x)

(** [step_bop bop v1 v2] implements the primitive operation [v1 bop v2].
    Requires: [v1] and [v2] are both values. *)
let step_bop bop e1 e2 =
  match (bop, e1, e2) with
  | Add, Int a, Int b -> Int (a + b)
  | Add, _, _ -> failwith bop_err
  | Mult, Int a, Int b -> Int (a * b)
  | Mult, _, _ -> failwith bop_err
  | Leq, Int a, Int b -> Bool (a <= b)
  | Leq, _, _ -> failwith bop_err

(** [eval_big] is the [==>] relation. *)
let rec eval_big : expr -> expr = function
  | Int i -> Int i
  | Bool b -> Bool b
  | Var _ -> failwith unbound_var_err
  | Binop (bop, e1, e2) -> step_bop bop (eval_big e1) (eval_big e2)
  | Let (x, e1, e2) ->
      let v1 = eval_big e1 in
      eval_big (subst e2 v1 x)
  | If (e1, e2, e3) -> (
      let v = eval_big e1 in
      match v with
      | Bool true -> eval_big e2
      | Bool false -> eval_big e3
      | _ -> failwith "bad condition expression")
  | Fun (x, e) -> Fun (x, e)
  | App (e1, e2) -> (
      let v1 = eval_big e1 in
      match v1 with
      | Fun (x, e) ->
          let v2 = eval_big e2 in
          eval_big (subst e v2 x)
      | _ -> failwith "Only functions can be applied")

(** [parse s] parses [s] into an AST. *)
let parse (s : string) : expr =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

(** [string_of_val e] converts [e] to a string. Requires: [e] is a
    value. *)
let string_of_val (e : expr) : string =
  match e with
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | Fun (x, e) -> "<function>"
  | Var _
  | Binop _
  | Let _
  | If _
  | App _ ->
      failwith "precondition violated"

(** [interp s] interprets [s] by lexing and parsing it, evaluating it,
    and converting the result to a string. *)
let interp (s : string) : string =
  s |> parse |> eval_big |> string_of_val

(** Some programs of interest *)
let omega = "((fun x -> (x x)) (fun x -> (x x)))"

let incr_twice =
  "let twice = fun f -> (fun x -> (f (f x))) in\n\
   let incr = fun x -> x + 1 in\n\
   ((twice incr) 3108)\n"

let show_progs () =
  Printf.printf "incr_twice:\n%s\nomega:\n%s\n" incr_twice omega
