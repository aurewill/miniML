(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

open CS51Utils ;;
open Absbook ;;

exception EvalError of string ;;

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;

type varid = string ;;
  
type expr =
  
  
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids) and sets of them
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
(* ACCORDING TO FIGURE 13.3 *)
(* IMPLEMENT UNBOUND VARIABLE MESSAGES, ex. let f = fun x -> if x = 0 then 1 else f (x - 1) in f 5 ;; *)
  (* Should give an unbound variable message in subst and lex semantics, should still eval in dynamic semantics *)
  (* For subst, all variables should eventually be substituted away, so if we come across one that wasn't, raise the error *)
let rec free_vars (expression : expr) : varidset =
  match expression with
  | Bool (_) -> SS.empty
  | Num (_) -> SS.empty
  | Var (x) -> SS.add x SS.empty
  | Unop (_, exp1) -> free_vars (Binop(Minus, Num(0), exp1))
  | Binop (_, exp1, exp2) -> SS.union (free_vars exp1) (free_vars exp2)
  | Fun (id, exp) -> SS.diff (free_vars exp) (free_vars (Var (id)))
  | Let (id, p, q) -> SS.union (SS.diff (free_vars q) (free_vars (Var (id)))) (free_vars p)
  | App (exp1, exp2) -> SS.union (free_vars exp1) (free_vars exp2)
  | Conditional (_, _, _) -> SS.empty
  | Letrec (id, p, q) -> SS.union (SS.diff (free_vars q) (free_vars (Var (id)))) (free_vars p)
  | Raise -> raise (EvalError "expr arg matched with Raise")
  | Unassigned -> raise (EvalError "expr arg matched with Unassigned")
;;

(* let free_vars_test () =
  unit_test (free_vars (Num (1)) = SS.empty) "empty set w int arg v1";
  unit_test (free_vars (Num (1)) <> SS.add "x" SS.empty) "empty set w int arg v2";
  unit_test (free_vars (Var ("x")) = SS.add "x" SS.empty) "set with x v1";
  unit_test (free_vars (Var ("x")) <> SS.add "y" SS.empty) "set with x v2";
  let expression = Let ("f", Fun ("x", Binop (Plus, Var ("x"), Var ("y"))), (App (Var ("f"), Var ("x")))) in
  unit_test (let s1 = free_vars expression in let s2 = SS.add "x" (SS.add "y" SS.empty) in SS.equal s1 s2) "let expr test";
  let expression = App (Fun ("x", Binop (Plus, Var ("x"), Num (1))), Num (3)) in
  unit_test (let s1 = free_vars expression in let s2 = SS.empty in SS.equal s1 s2) "app test 1";
  let expression = App (Fun ("x", Var ("x")), Fun ("y", Var ("x"))) in 
  unit_test (let s1 = free_vars expression in let s2 = SS.add "x" SS.empty in SS.equal s1 s2) "app test 2";
  let expression = Fun ("x", App (Fun ("y", Var ("x")), Var ("x"))) in
  unit_test (let s1 = free_vars expression in let s2 = SS.empty in SS.equal s1 s2) "fun (app) test";
;;

free_vars_test () ;; *)
  
(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no variable names use the
   prefix "var". (Otherwise, they might accidentally be the same as a
   generated variable name.) *)

let gensym =
  let ctr = ref 0 in
  fun (s : string) : string ->
    let xs = [s; string_of_int !ctr] in
    ctr := !ctr + 1;
    String.concat "" xs ;;

let new_varname () : varid = gensym "aw" ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  match exp with
  | Bool (b) -> Bool (b)
  | Num (i) -> Num (i)
  | Var (id) -> if id = var_name then repl else exp
  | Unop (_, exp1) -> subst var_name repl (Binop(Minus, Num(0), exp1))
  | Binop (op, q, r) -> Binop (op, subst var_name repl q, subst var_name repl r)
  | Fun (id, q) -> 
    (if id = var_name then Fun (id, q)
     else let free_vars_set = free_vars repl in
      if SS.mem id free_vars_set = false then Fun (id, subst var_name repl q)
      else let z = new_varname () in
        Fun (z, subst var_name repl (subst id (Var (z)) q)))
  | Let (id, q, r) -> 
    (if id = var_name then Let (id, subst var_name repl q, r)
     else let free_vars_set = free_vars repl in
      (if SS.mem id free_vars_set = false then Let (id, subst var_name repl q, subst var_name repl r)
       else let z = new_varname () in
       Let (z, subst var_name repl q, subst var_name repl (subst id (Var (z)) r))))
  | App (q, r) -> App (subst var_name repl q, subst var_name repl r)
  | Conditional (if_exp, then_exp, else_exp) ->
    Conditional (subst var_name repl if_exp, 
                 subst var_name repl then_exp, 
                 subst var_name repl else_exp)
  | Letrec (id, q, r) -> 
    (if id = var_name then Letrec (id, subst var_name repl q, r)
     else let free_vars_set = free_vars repl in
      (if SS.mem id free_vars_set = false then Letrec (id, subst var_name repl q, subst var_name repl r)
       else let z = new_varname () in
       Letrec (z, subst var_name repl q, subst var_name repl (subst id (Var (z)) r))))
  | Raise -> raise (EvalError "Raise match not used in subst semantics")
  | Unassigned -> raise (EvalError "Unassigned match not used in subst semantics")
;;

(* let subst_test () = 
  unit_test (subst "x" (Num(42)) (Fun("y", Var("x"))) = (Fun("y", Num(42)))) "midterm2 q1";
  let sub_var, repl_exp, input_exp, answer_exp =
    "x",
    Num(42),
    App(Fun("y", Var("x")), Num(21)),
    App(Fun("y", Num(42)), Num(21)) in
    unit_test (subst sub_var repl_exp input_exp = answer_exp) "midterm2 q2";
  let sub_var, repl_exp, input_exp, answer_exp =
    "x",
    Num(42),
    Let("x", Binop(Plus, Var("x"), Num(1)), Binop(Plus, Var("x"), Num(2))),
    Let("x", Binop(Plus, Num(42), Num(1)), Binop(Plus, Var("x"), Num(2))) in
    unit_test (subst sub_var repl_exp input_exp = answer_exp) "midterm2 q3";
  let sub_var, repl_exp, input_exp, answer_exp =
    "y",
    Binop(Plus, Var("x"), Num(1)),
    Let("x", Num(5), App(Var("f"), Var("y"))),
    Let("aw0", Num(5), App(Var("f"), Binop(Plus, Var("x"), Num(1)))) in
    unit_test (subst sub_var repl_exp input_exp = answer_exp) "midterm2 q4";
;;

subst_test () ;; *)
     
(*......................................................................
  String representations of expressions
 *)
   
(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
let rec exp_to_concrete_string (expression : expr) : string =
  match expression with
  | Bool (b) -> Stdlib.string_of_bool b
  | Num (i) -> Stdlib.string_of_int i
  | Var (v) -> v
  | Unop (_, exp) -> "~-" ^ exp_to_concrete_string exp
  | Binop (op, exp1, exp2) -> 
    (match op with
    | Plus -> exp_to_concrete_string exp1 ^ " + " ^ exp_to_concrete_string exp2
    | Minus -> exp_to_concrete_string exp1 ^ " - " ^ exp_to_concrete_string exp2
    | Times -> exp_to_concrete_string exp1 ^ " * " ^ exp_to_concrete_string exp2
    | Equals -> exp_to_concrete_string exp1 ^ " = " ^ exp_to_concrete_string exp2
    | LessThan -> exp_to_concrete_string exp1 ^ " < " ^ exp_to_concrete_string exp2)
  | Fun (id, def_exp) -> "fun " ^ id ^ " -> " ^ exp_to_concrete_string def_exp
  | Let (id, def_exp, body_exp) -> "let " ^ id ^ " = " ^ 
                                    exp_to_concrete_string def_exp ^ " in " ^ 
                                    exp_to_concrete_string body_exp
  | App (fun_exp, app_exp) -> "(" ^ exp_to_concrete_string fun_exp ^ ") " ^ "(" ^ exp_to_concrete_string app_exp ^ ")"
  | Conditional (if_exp, then_exp, else_exp) -> "if " ^ exp_to_concrete_string if_exp ^
                                             " then " ^ exp_to_concrete_string then_exp ^
                                             " else " ^ exp_to_concrete_string else_exp
  | Letrec (id, def_exp, body_exp) -> "let rec " ^ id ^ " = " ^ exp_to_concrete_string def_exp ^
                                                       " in " ^ exp_to_concrete_string body_exp
  (* Not too sure what to output for Raise and Unassigned *)
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
;;
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (expression : expr) : string =
  match expression with
  | Bool (b) -> "Bool(" ^ Stdlib.string_of_bool b ^ ")"
  | Num (i) -> "Num(" ^ Stdlib.string_of_int i ^ ")"
  | Var (v) -> "Var(" ^ v ^ ")"
  | Unop (_, exp) -> "Unop(" ^ "Negate, " ^ exp_to_abstract_string exp ^ ")"
  | Binop (bin, exp1, exp2) -> 
    (match bin with
    | Plus -> "Binop(Plus, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2 ^ ")"
    | Minus -> "Binop(Minus, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2 ^ ")"
    | Times -> "Binop(Times, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2 ^ ")"
    | Equals -> "Binop(Equals, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2 ^ ")"
    | LessThan -> "Binop(LessThan, " ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2 ^ ")")
  | Fun (id, def_exp) -> "Fun(" ^ id ^ ", " ^ exp_to_abstract_string def_exp ^ ")"
  | Let (id, def_exp, body_exp) -> "Let(" ^ id ^ ", " ^ 
                                        exp_to_abstract_string def_exp ^ ", " ^ 
                                        exp_to_abstract_string body_exp ^ ")"
  | App (fun_exp, app_exp) -> "App(" ^ exp_to_abstract_string fun_exp ^ ", " ^ exp_to_abstract_string app_exp ^ ")"
  | Conditional (if_exp, then_exp, else_exp) -> "Conditional(" ^ exp_to_abstract_string if_exp ^ ", " ^ 
                                                                 exp_to_abstract_string then_exp ^ ", " ^ 
                                                                 exp_to_abstract_string else_exp ^ ")"
  | Letrec (v, def_exp, body_exp) -> "Letrec(" ^ v ^ ", " ^ 
                                            exp_to_abstract_string def_exp ^ ", " ^ 
                                            exp_to_abstract_string body_exp ^ ")"
  (* Again, not too sure what to output for Raise and Unassigned *)
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
;;
