(*
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expresions
 *)

type unop =
  | Negate
;;

type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
  (* below my additions *)
  | LessEq
  | GreaterThan
  | GreaterEq
;;

type varid = string ;;

type expr =
  | Var of varid
  | Num of int
  | Bool of bool
  | Unop of unop * expr
  | Binop of binop * expr * expr
  | Conditional of expr * expr * expr
  | Fun of varid * expr
  | Let of varid * expr * expr
  | Letrec of varid * expr * expr
  | Raise of string           (* exceptions with notes *)
  | Unassigned
  | App of expr * expr
;;

(*......................................................................
  Manipulation of variable names (varids)
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars :  varidset -> varidset -> bool
   Test to see if two sets of variables have the same elements (for
   testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list : string list -> varidset
   Generate a set of variable names from a list of strings (for
   testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;

(* free_vars : expr -> varidset
   Return a set of the variable names that are free in expression
   exp *)
let free_vars (exp : expr) : varidset =
  let set = SS.empty in
  let rec eval (exp_c : expr) : varidset =
    match exp_c with
    | Var var                        -> SS.add var set
    | Num _                          -> set
    | Bool _                         -> set
    | Unop (_, exp)                  -> eval exp
    | Binop (_, exp1, exp2)          ->
      SS.union (eval exp1) (eval exp2)
    | Conditional (exp1, exp2, exp3) ->
      SS.union (SS.union (eval exp1) (eval exp2)) (eval exp3)
    | Fun (var, exp)                 ->
      SS.remove var (eval exp)
    | Let (var, exp1, exp2)          ->
      SS.union (SS.remove var (eval exp2)) (eval exp1)
    | Letrec (var, exp1, exp2)       ->
      SS.union (SS.remove var (eval exp2)) (SS.remove var (eval exp1))
    | Raise _                        -> set
    | Unassigned                     -> set
    | App (exp1, exp2)               -> SS.union (eval exp1) (eval exp2)
  in eval exp
;;

(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)
let new_varname () : varid =
  let suffix = ref 0 in
  let str = "var" ^ string_of_int !suffix in
             suffix := !suffix + 1;
             str ;;

(*......................................................................
  Substitution

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let short = subst var_name repl in
    match exp with
    | Var var -> if var = var_name then repl
                 else Var var
    | Num num -> Num num
    | Bool bool -> Bool bool
    | Unop (unop, exp1) -> Unop (unop, short exp1)
    | Binop (binop, exp1, exp2) -> Binop (binop, short exp1, short exp2)
    | Conditional (exp1, exp2, exp3) -> Conditional (short exp1,
                                                     short exp2,
                                                     short exp3)
    | Fun (var, exp1) ->
      (* Branch 1: var_name *is* var
         ex: fun x -> x + x [x |-> 2]  --> fun x -> 2 + 2
         fun x -> x + a [x |-> 2] --> fun x -> 2 + a *)
      if var_name = var then Fun (var, subst var repl exp1)
      (* Branch 2: "var_name" different from "var" but var is not a free variable of repl
         ex: fun y -> x + x [x |-> 2]
         fun y -> x + y [x |-> a + b] --> fun y -> a + b + y *)
      else if not (SS.mem var (free_vars repl))
      then Fun (var, short exp1)
      (* Branch 3: "var_name" different from "var" and var *is* a free variable of repl
        ex: fun y -> x + y [x |-> 2 + y] = fun z -> 2 + z + z *)
      else if (SS.mem var (free_vars repl))
      then let z = new_varname () in Fun (z, subst var (Var z) (short exp1))
      (* else weirdness so raise *)
      else Raise "Error in substituting"
    | Let (var, exp1, exp2) ->
      (* case 1: var_name is var; var_name already bound in exp2, so
         just need to sub var_name into exp1
         ex: let x = x + 3 in x + x [x |-> 2]--> let x = 2 + 3 in x + x
      let x = a + 3 in x + x [x |-> 2]--> let x = a + 3 in x + x *)
      if var_name = var then Let (var, short exp1, exp2)
      (* case 2: var different from var_name, but var is not a free variable of repl
         ex: let y = x + 2 in y + x [x |-> 2] --> let y = 2 + 2 in y + 2 ;
         let y = a + x in x + x [x |-> 2 + b]--> let y = a + 2 + b in 4 + b + b *)
      else if not (SS.mem var (free_vars repl))
      then Let (var, short exp1, short exp2)
      (* case 3: var different from var_name, and var *is* a free variable of repl
          let y = a + x in x + x [x |-> 2 + y + b]--> let z = a + 2 + y + b in 2 + 2 + z + z + b + b *)
      else if SS.mem var (free_vars repl)
      then let z = new_varname () in
        Let (z, short exp1, subst var (Var z) (short exp2))
      else Raise "Error in substitution in a let expression"
    | Letrec (var, exp1, exp2) ->
      (* Case 1: var is already bound in both exp1 and exp2 *)
      if var = var_name then Letrec (var, exp1, exp2)
      else if not (SS.mem var (free_vars repl))
      then Letrec (var, short exp1, short exp2)
      else if SS.mem var (free_vars repl)
      then
        Letrec (var, short exp1, short exp2)
      else Raise "Error in substitution in a let rec statement"
    | App (exp1, exp2) -> App (short exp1, short exp2)
    | Raise str -> Raise str
    | Unassigned -> Unassigned

(* Below are tests for the above functions.
These tests are run at the bottom of evaluation.ml*)

let free_vars_test () =
  let x = SS.elements (free_vars (Var("x"))) in
  let y = ["x"] in
  assert (x = y) ;
  let x = SS.elements (free_vars (Let("x", Num(1), App(Fun("y", Binop(Plus, Binop(Plus, Binop(Plus, Var("x"), Var("y")), Num(1)), Var("z"))), Num(1))))) in
  let y = ["z"] in
  assert (x = y) ;
  let x = SS.elements (free_vars (Letrec("f", Fun("n", Conditional(Binop(Equals, Var("n"), Num(0)), Num(1), Binop(Times, Var("n"), App(Var("f"), Binop(Minus, Var("n"), Num(1)))))), App(Var("f"), Num(2))))) in
  let y = [] in
  assert (x = y) ;
  let x = SS.elements (free_vars (Let("x", Binop(Plus, Var("x"), Var("y")), Binop(Plus, Var("x"), Var("z"))))) in
  let y = ["x"; "y"; "z"] in
  assert (x = y) ;
  let x = SS.elements (free_vars (Let("x", Num(4), Var("y")))) in
  let y = ["y"] in
  assert (x = y) ;
  let x = SS.elements (free_vars (Let("y", Fun("x", Binop(Times, Num(4), Var("x"))), Binop(Equals, Var("y"), Num(4))))) in
  let y = [] in
  assert (x = y) ;
  let x = SS.elements (free_vars (Conditional(Binop(GreaterEq, Num(4), Num(3)), Let("x", Num(3), Var("y")), Let("x", Num(4), Var("z"))))) in
  let y = ["y"; "z"] in
  assert (x = y) ;
  let x = SS.elements (free_vars (Unop(Negate, Num(1)))) in
  let y = [] in
  assert (x = y) ;
  () ;;

let subst_test () =
  let x = subst "x" (Num(3)) (Var("x")) in
  let y = Num 3 in
  assert (x = y) ;
  let x = subst "x" (Num(3)) (Var("x"))  in
  let y = Num 3 in
  assert (x = y) ;
  let x = subst "x" (Num(3)) (Var("y")) in
  let y = Var "y" in
  assert (x = y) ;
  let x = subst "x" (Num(3)) (Unop(Negate, Num(5))) in
  let y = Unop (Negate, Num 5) in
  assert (x = y) ;
  let x = subst "x" (Num(3)) (Unop(Negate, Var("x"))) in
  let y = Unop (Negate, Num 3) in
  assert (x = y) ;
  let x = subst "x" (Num(3)) (Unop(Negate, Var("y"))) in
  let y = Unop (Negate, Var "y") in
  assert (x = y) ;
  (* Testing (Q + R)[x↦P]=Q[x↦P] + R[x↦P] *)
  let x = subst "x" (Num(3)) (Binop(Plus, Var("x"), Var("y"))) in
  let y = Binop (Plus, Num 3, Var "y") in
  assert (x = y) ;
  let x = subst "x" (Num(3)) (Binop(Plus, Binop(Minus, Num(4), Binop(Times, Var("x"), Var("y"))), Var("z"))) in
  let y = Binop (Plus, Binop (Minus, Num 4, Binop (Times, Num 3, Var "y")), Var "z") in
  assert (x = y) ;
  let x = subst "x" (Num(5)) (Binop(Plus, Var("x"), Num(5))) in
  let y = Binop (Plus, Num 5, Num 5) in
  assert (x = y) ;
  (* Testing FUN *)
  let s = subst "x" (Num(2)) (Fun("x", Binop(Plus, Var("x"), Var("a")))) in
  let d = Fun ("x", Binop (Plus, Num 2, Var "a")) in
  assert (s = d) ;
  let x = subst "x" (Binop(Plus, Var("a"), Var("b"))) ((Fun("y", Binop(Plus, Var("x"), Var("y"))))) in
  let y = Fun ("y", Binop (Plus, Binop (Plus, Var "a", Var "b"), Var "y")) in
  assert (x = y) ;
  let x = subst "x" (Binop(Plus, Num(2), Var("y"))) (Fun("y", Binop(Plus, Var("x"), Var("y")))) in
  let y = Fun ("var0", Binop (Plus, Binop (Plus, Num 2, Var "var0"), Var "var0")) in
  assert (x = y) ;
  (* Testing LET *)
  let x = subst "y" (Num(3)) (Let("x", Num(3), Binop(Plus, Binop(Plus, Var("x"), Var("y")), Num(3)))) in
  let y = Let ("x", Num 3, Binop (Plus, Binop (Plus, Var("x"), Num 3), Num 3)) in
  assert (x = y) ;
  let x = subst "z" (Num(3)) (Let("x", Num(3), Var("y"))) in
  let y = Let ("x", Num 3, Var "y") in
  assert (x = y) ;
  let x = subst "x" (Num(2)) (Let("x", Binop(Plus, Var("a"), Num(3)), Binop(Plus, Var("x"), Var("x"))))  in
  let y = Let ("x", Binop (Plus, Var "a", Num 3), Binop (Plus, Var "x", Var "x")) in
  assert (x = y) ;
  let x = subst "x" ( Binop(Plus, Num(2), Var("b"))) (Let("y", Binop(Plus, Var("a"), Var("x")), Binop(Plus, Var("x"), Var("x")))) in
  let y = Let ("y", Binop (Plus, Var "a", Binop (Plus, Num 2, Var "b")), Binop (Plus, Binop (Plus, Num 2, Var "b"), Binop (Plus, Num 2, Var "b"))) in
  assert (x = y) ;
  let x = subst "x" (Binop(Plus, Binop(Plus, Num(2), Var("y")), Var("b"))) (Let("y", Binop(Plus, Var("a"), Var("x")), Binop(Plus, Var("x"), Var("x")))) in
  let y = Let ("var0", Binop (Plus, Var "a", Binop (Plus, Binop (Plus, Num 2, Var "y"), Var "b")), Binop (Plus, Binop (Plus, Binop (Plus, Num 2, Var "var0"), Var "b"), Binop (Plus, Binop (Plus, Num 2, Var "var0"), Var "b"))) in
  assert (x = y) ;
  (* Letrec *)
  let x = subst "l" (Num(2)) (Letrec("f", Fun("n", Conditional(Binop(Equals, Var("n"), Num(0)), Num(1), Binop(Times, Var("n"), App(Var("f"), Binop(Minus, Var("n"), Num(1)))))), App(Var("f"), Var("l"))))  in
  let y = Letrec ("f", Fun ("n", Conditional (Binop (Equals, Var "n", Num 0), Num 1, Binop (Times, Var "n", App (Var "f", Binop (Minus, Var "n", Num 1))))), App (Var "f", Num 2)) in
  assert (x = y) ;
  let x = subst "y" (Num(1)) (App(Fun("x", Binop(Plus, Binop(Plus, Var("x"), Var("y")), Num(1))), Num(1))) in
  let y = App (Fun ("x", Binop (Plus, Binop (Plus, Var "x", Num 1), Num 1)), Num 1) in
  assert (x = y) ;
  () ;;

let tests_in_expr () =
  free_vars_test () ;
  subst_test () ;
  () ;;


(*......................................................................
  String representations of expressions
 *)


(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var var -> var
  | Num num -> string_of_int num
  | Bool bool -> string_of_bool bool
  | Unop (_, exp1) -> "~-" ^ exp_to_concrete_string exp1
  | Binop (binop, exp1, exp2) ->
    "(" ^
      (match binop with
    | Plus -> exp_to_concrete_string exp1 ^ " + " ^ exp_to_concrete_string exp2
    | Minus -> exp_to_concrete_string exp1 ^ " - " ^ exp_to_concrete_string exp2
    | Times -> exp_to_concrete_string exp1 ^ " * " ^ exp_to_concrete_string exp2
    | Equals -> exp_to_concrete_string exp1 ^ " = " ^ exp_to_concrete_string exp2
    | LessThan -> exp_to_concrete_string exp1 ^ " < " ^ exp_to_concrete_string exp2
    | LessEq -> exp_to_concrete_string exp1 ^ " <= " ^ exp_to_concrete_string exp2
    | GreaterThan -> exp_to_concrete_string exp1 ^ " > " ^ exp_to_concrete_string exp2
    | GreaterEq -> exp_to_concrete_string exp1 ^ " >= " ^ exp_to_concrete_string exp2) ^ ")"
  | Conditional (exp1, exp2, exp3) -> "if " ^
                                      exp_to_concrete_string exp1 ^
                                      " then " ^
                                      exp_to_concrete_string exp2 ^
                                      " else " ^
                                      exp_to_concrete_string exp3
  | Fun (var, exp1) -> "(fun " ^ var ^ " -> " ^
                       exp_to_concrete_string exp1 ^ ")"
                         (* fix cases here where "let" defines a funciton *)
  | Let (var, exp1, exp2) -> "let " ^
                             var ^
                             " = " ^
                             exp_to_concrete_string exp1 ^
                             " in " ^
                             exp_to_concrete_string exp2
  | Letrec (var, exp1, exp2) -> "let rec " ^
                                 var ^ " = " ^
                                exp_to_concrete_string exp1 ^ " in " ^
                                exp_to_concrete_string exp2
  | Raise str -> "failure: " ^ str
  | Unassigned -> "Unassigned"
  | App (exp1, exp2) -> exp_to_concrete_string exp1 ^
                        " " ^
                        exp_to_concrete_string exp2

(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var var -> "Var(\"" ^ var ^ "\")"
  | Num num -> "Num(" ^ string_of_int num ^ ")"
  | Bool bool -> "Bool(" ^ if bool then "true)" else "false)"
  | Unop (_, exp1) -> "Unop(Negate, " ^ exp_to_abstract_string exp1 ^ ")"
  | Binop (binop, exp1, exp2) -> "Binop(" ^
    (match binop with
    | Plus -> "Plus, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2
    | Minus -> "Minus, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2
    | Times -> "Times, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2
    | Equals -> "Equals, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2
    | LessThan -> "LessThan, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2
    | LessEq -> "LessEq, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2
    | GreaterThan -> "GreaterThan, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2
    | GreaterEq -> "GreaterEq, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2) ^ ")"
  | Conditional (exp1, exp2, exp3) -> "Conditional(" ^
                                      exp_to_abstract_string exp1 ^
                                      ", " ^
                                      exp_to_abstract_string exp2 ^
                                      ", " ^
                                      exp_to_abstract_string exp3 ^
                                      ")"

  | Fun (var, exp1) -> "Fun(\"" ^
                       var ^
                       "\", " ^
                       exp_to_abstract_string exp1 ^
                       ")"
                         (* fix cases here where "let" defines a funciton *)
  | Let (var, exp1, exp2) -> "Let(\"" ^ var ^ "\", " ^
                             exp_to_abstract_string exp1 ^ ", " ^
                             exp_to_abstract_string exp2 ^ ")"
  | Letrec (var, exp1, exp2) -> "Letrec(\"" ^ var ^ "\", " ^
                                exp_to_abstract_string exp1 ^ ", " ^
                                exp_to_abstract_string exp2 ^ ")"
  | Raise str -> "Failure: " ^ str
  | Unassigned -> "(Unassigned)"
  | App (exp1, exp2) -> "App(" ^
                        exp_to_abstract_string exp1 ^
                        ", " ^
                        exp_to_abstract_string exp2 ^
                        ")"
