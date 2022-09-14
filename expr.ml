(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
  | FNegate
;;
    
type binop =
  | Plus
  | FPlus
  | Minus
  | FMinus
  | Times
  | FTimes
  | Equals
  | LessThan
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Float of float                       (* floats *)
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
  SS.equal ;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;

(* print_set s -- Prints a new line "\n" after each string is printed *)
(* let print_set : varidset -> unit = 
  SS.iter print_endline ;; *)
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var x -> SS.singleton x
  | Unop (_, e) -> free_vars e
  | Binop (_, e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | Conditional (e1, e2, e3) -> 
    SS.union (free_vars e1) (SS.union (free_vars e2) (free_vars e3))
  | Fun (x, e) -> SS.diff (free_vars e) (SS.singleton x)
  (* x not bound if in e1 *)
  | Let (x, e1, e2) -> 
    SS.union (SS.diff (free_vars e2) (SS.singleton x)) (free_vars e1)
  (* x bound if in e1 *)
  | Letrec (x, e1, e2) -> 
    SS.diff (SS.union (free_vars e2) (free_vars e1)) (SS.singleton x)
  | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | _ -> SS.empty ;;
  
(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no variable names use the
   prefix "var". (Otherwise, they might accidentally be the same as a
   generated variable name.) *)
let new_varname : unit -> varid =
  let ctr = ref ~-1 in
  fun () ->
    ctr := succ !ctr;
    "var" ^ (string_of_int !ctr) ;;

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
  | Var x -> if x = var_name then repl else exp
  | Num _
  | Float _
  | Bool _ -> exp
  | Unop (op, e) -> Unop (op, subst var_name repl e)
  | Binop (op, e1, e2) -> 
    Binop (op, subst var_name repl e1, subst var_name repl e2)
  | Conditional (e1, e2, e3) ->
    Conditional (subst var_name repl e1, 
                 subst var_name repl e2, 
                 subst var_name repl e3)
  | Fun (y, e) -> 
    if y = var_name then exp
    else if not (SS.mem y (free_vars repl))
      then Fun (y, subst var_name repl e)
    else 
      let fresh_var = new_varname () in
      let e' = subst y (Var fresh_var) e in
      Fun (fresh_var, subst var_name repl e')
  | Let (y, e1, e2) ->
    if y = var_name then Let (y, subst var_name repl e1, e2)
    else if not (SS.mem y (free_vars repl))
      then Let (y, subst var_name repl e1, subst var_name repl e2)
    else
      let fresh_var = new_varname () in
      let e2' = subst y (Var fresh_var) e2 in
      Let (fresh_var, subst var_name repl e1, subst var_name repl e2')
  | Letrec (y, e1, e2) -> 
    if y = var_name then Letrec (y, e1, e2)
    else if not (SS.mem y (free_vars repl))
      then Letrec (y, subst var_name repl e1, subst var_name repl e2)
    else
      let fresh_var = new_varname () in
      let e1' = subst y (Var fresh_var) e1 in
      let e2' = subst y (Var fresh_var) e2 in
      Letrec (fresh_var, subst var_name repl e1', subst var_name repl e2')
  | Raise -> exp
  | Unassigned -> exp
  | App (e1, e2) -> App (subst var_name repl e1, subst var_name repl e2) ;;
     
(*......................................................................
  String representations of expressions
 *)
   
(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var x -> x
  | Num n -> string_of_int n
  | Float n -> string_of_float n
  | Bool b -> string_of_bool b
  | Unop (_, e) -> "-(" ^ exp_to_concrete_string e ^ ")"
  | Binop (op, e1, e2) ->
    (match op with
    | Plus -> exp_to_concrete_string e1 ^ " + " ^ exp_to_concrete_string e2
    | FPlus -> exp_to_concrete_string e1 ^ " +. " ^ exp_to_concrete_string e2
    | Minus -> exp_to_concrete_string e1 ^ " - " ^ exp_to_concrete_string e2
    | FMinus -> exp_to_concrete_string e1 ^ " -. " ^ exp_to_concrete_string e2
    | Times -> exp_to_concrete_string e1 ^ " * " ^ exp_to_concrete_string e2
    | FTimes -> exp_to_concrete_string e1 ^ " *. " ^ exp_to_concrete_string e2
    | Equals -> exp_to_concrete_string e1 ^ " = " ^ exp_to_concrete_string e2
    | LessThan -> exp_to_concrete_string e1 ^ " < " ^ exp_to_concrete_string e2)
  | Conditional (e1, e2, e3) ->
    "if " ^ exp_to_concrete_string e1 ^ " then " ^ exp_to_concrete_string e2 ^
    " else " ^ exp_to_concrete_string e3
  | Fun (x, e) -> "fun " ^ x ^ " -> " ^ exp_to_concrete_string e
  | Let (x, e1, e2) -> 
    "let " ^ x ^ " = " ^ exp_to_concrete_string e1 ^ 
    " in " ^ exp_to_concrete_string e2
  | Letrec (x, e1, e2) ->
    "let rec " ^ x ^ " = " ^ exp_to_concrete_string e1 ^ 
    " in " ^ exp_to_concrete_string e2
  | Raise -> "raise Error"
  | Unassigned -> "Unassigned"
  | App (e1, e2) -> 
    "(" ^ exp_to_concrete_string e1 ^ ")(" ^ exp_to_concrete_string e2 ^ ")" ;;
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var x -> "Var " ^ x
  | Num n -> "Num " ^ string_of_int n
  | Float n -> "Float " ^ string_of_float n
  | Bool b -> "Bool " ^ string_of_bool b
  | Unop (Negate, e) -> "Unop (Negate, " ^ exp_to_abstract_string e ^ ")"
  | Unop (FNegate, e) -> "Unop (FNegate, " ^ exp_to_abstract_string e ^ ")"
  | Binop (op, e1, e2) ->
    (match op with
    | Plus -> "Binop (Plus, " ^ exp_to_abstract_string e1 ^ ", " ^
                                exp_to_abstract_string e2 ^ ")"
    | FPlus -> "Binop (FPlus, " ^ exp_to_abstract_string e1 ^ ", " ^
                                exp_to_abstract_string e2 ^ ")"
    | Minus -> "Binop (Minus, " ^ exp_to_abstract_string e1 ^ ", " ^
                                  exp_to_abstract_string e2 ^ ")"
    | FMinus -> "Binop (FMinus, " ^ exp_to_abstract_string e1 ^ ", " ^
                                  exp_to_abstract_string e2 ^ ")"
    | Times -> "Binop (Times, " ^ exp_to_abstract_string e1 ^ ", " ^
                                  exp_to_abstract_string e2 ^ ")"
    | FTimes -> "Binop (FTimes, " ^ exp_to_abstract_string e1 ^ ", " ^
                                  exp_to_abstract_string e2 ^ ")"
    | Equals -> "Binop (Equals, " ^ exp_to_abstract_string e1 ^ ", " ^
                                    exp_to_abstract_string e2 ^ ")"
    | LessThan -> "Binop (LessThan, " ^ exp_to_abstract_string e1 ^ ", " ^
                                        exp_to_abstract_string e2 ^ ")")
  | Conditional (e1, e2, e3) ->
    "Conditional (" ^ exp_to_abstract_string e1 ^ ", " ^
                      exp_to_abstract_string e2 ^ ", " ^
                      exp_to_abstract_string e3 ^ ")"
  | Fun (x, e) -> "Fun (" ^ x ^ ", " ^ exp_to_abstract_string e ^ ")"
  | Let (x, e1, e2) -> "Let (" ^ x ^ ", " ^ 
                                 exp_to_abstract_string e1 ^ ", " ^ 
                                 exp_to_abstract_string e2 ^ ")"
  | Letrec (x, e1, e2) -> "Letrec (" ^ x ^ ", " ^ 
                                       exp_to_abstract_string e1 ^ ", " ^ 
                                       exp_to_abstract_string e2 ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (e1, e2) -> "App (" ^ exp_to_abstract_string e1 ^ ", " ^ 
                              exp_to_abstract_string e2 ^ ")" ;;
