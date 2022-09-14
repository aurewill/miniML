(* CS 51 Final Project Tests *)

open CS51Utils ;;
open Absbook ;;
open Expr ;;
open Evaluation ;;

(* expressions that evaluate differently under dynamic environment semantics *)
let shieber1 = Let ("x", 
                    Num 2, 
                    Let ("f", 
                         Fun ("y", Binop (Times, Var "x", Var "y")), 
                         Let ("x", 
                              Num 1, 
                              App (Var "f", Num 21)))) ;;

let shieber2 = Let ("x", 
                    Num 10, 
                    Let ("f", 
                         Fun ("y", 
                             Fun ("z", 
                                  Binop (Times, 
                                         Var "z", 
                                         Binop (Plus, 
                                                Var "x", 
                                                Var "y")))), 
                         App (App (Var "f", Num 11), 
                              Num 2))) ;;

(* expr.ml tests *)
let exp_to_concr_str_test () =
  unit_test (exp_to_concrete_string (Var "x") = "x")
            "exp_to_concr: Var 'x' = 'x' |" ;
  unit_test (exp_to_concrete_string (Num 0) = "0")
            "exp_to_concr: Num 0 = '0' |" ;
  unit_test (exp_to_concrete_string (Float 0.) = "0.")
            "exp_to_concr: Float 0. = '0.' |" ;
  unit_test (exp_to_concrete_string (Bool true) = "true")
            "exp_to_concr: Bool true = 'true' |" ;
  unit_test (exp_to_concrete_string (Bool false) = "false")
            "exp_to_concr: Bool false = 'false' |" ;
  unit_test (exp_to_concrete_string (Unop (FNegate, Float 0.)) = "-(0.)")
            "exp_to_concr: Unop (FNegate, Float 0.) = '-(0.)' |" ;
  unit_test (exp_to_concrete_string (Binop (Plus, Num 1, Num 2)) = "1 + 2")
            "exp_to_concr: Binop (Plus, Num 1, Num 2) = '1 + 2' |" ;
  unit_test (exp_to_concrete_string (Binop (FPlus, Float 1.5, Float 2.5)) 
            = "1.5 +. 2.5")
            "exp_to_concr: 1.5 +. 2.5 |" ;
  unit_test (exp_to_concrete_string (Binop (Minus, Num 1, Num 2)) = "1 - 2")
            "exp_to_concr: Binop (Minus, Num 1, Num 2) = '1 - 2' |" ;
  unit_test (exp_to_concrete_string (Binop (FMinus, Float 1.5, Float 2.5)) 
            = "1.5 -. 2.5")
            "exp_to_concr: 1.5 -. 2.5 |" ;
  unit_test (exp_to_concrete_string (Binop (Times, Num 1, Num 2)) = "1 * 2")
            "exp_to_concr: Binop (Times, Num 1, Num 2) = '1 * 2' |" ;
  unit_test (exp_to_concrete_string (Binop (FTimes, Float 1.5, Float 2.))
            = "1.5 *. 2.")
            "exp_to_concr: 1.5 *. 2. |" ;
  unit_test (exp_to_concrete_string (Binop (Equals, Num 1, Num 2)) = "1 = 2")
            "exp_to_concr: Binop (Equals, Num 1, Num 2) = '1 = 2' |" ;
  unit_test (exp_to_concrete_string (Binop (LessThan, Num 1, Num 2)) = "1 < 2")
            "exp_to_concr: Binop (LessThan, Num 1, Num 2) = '1 < 2' |" ;
  unit_test (exp_to_concrete_string (Conditional (Bool true, Num 1, Num 2)) 
                                     = "if true then 1 else 2")
            "exp_to_concr: Conditional (Bool true, Num 1, Num 2) \
             = 'if true then 1 else 2' |" ;
  unit_test (exp_to_concrete_string (Fun ("x", Binop (Plus, Var "x", Num 1))) 
                                     = "fun x -> x + 1")
            "exp_to_concr: Fun ('x', Binop (Plus, Var 'x', Num 1)) \
            = 'fun x -> x + 1' |" ;
  unit_test (exp_to_concrete_string (Let ("x", Num 1, Binop (Plus, 
                                                             Var "x", 
                                                             Num 1))) 
                                     = "let x = 1 in x + 1")
            "exp_to_concr: Let ('x', Num 1, Binop (Plus, Var 'x', Num 1)) \
            = 'let x = 1 in x + 1' |" ;
  unit_test (exp_to_concrete_string (Letrec ("x", Num 1, Binop (Plus, 
                                                                Var "x", 
                                                                Num 1))) 
                                     = "let rec x = 1 in x + 1")
            "exp_to_concr: Letrec ('x', Num 1, Binop (Plus, Var 'x', Num 1)) \
            = 'let rec x = 1 in x + 1' |" ;
  unit_test (exp_to_concrete_string (Raise) = "raise Error")
            "exp_to_concr: Raise = 'raise Error' |" ;
  unit_test (exp_to_concrete_string (Unassigned) = "Unassigned")
            "exp_to_concr: Unassigned = 'Unassigned' |" ;
  unit_test (exp_to_concrete_string (App (Fun ("x", Binop (Plus, Var "x", 
                                                                 Num 1)),
                                          Num 1)) 
                                     = "(fun x -> x + 1)(1)")
           "exp_to_concr: App (Fun ('x', Binop (Plus, Var 'x', Num 1)), Num 1) \
           = '(fun x -> x + 1)(1)' |" ;;

let exp_to_abstr_str_test () =
  unit_test (exp_to_abstract_string (Var "x") = "Var x")
            "exp_to_abstr: Var 'x' = 'Var x' |" ;
  unit_test (exp_to_abstract_string (Num 0) = "Num 0")
            "exp_to_abstr: Num 0 = 'Num 0' |" ;
  unit_test (exp_to_abstract_string (Float 0.) = "Float 0.")
            "exp_to_abstr: Float 0. |" ;
  unit_test (exp_to_abstract_string (Bool true) = "Bool true")
            "exp_to_abstr: Bool true = 'Bool true' |" ;
  unit_test (exp_to_abstract_string (Bool false) = "Bool false")
            "exp_to_abstr: Bool false = 'Bool false' |" ;
  unit_test (exp_to_abstract_string (Unop (Negate, Var "x")) 
                                     = "Unop (Negate, Var x)")
            "exp_to_abstr: Unop (Negate, Var 'x') = 'Unop (Negate, Var x)' |" ;
  unit_test (exp_to_abstract_string (Binop (Plus, Num 1, Num 2)) 
                                     = "Binop (Plus, Num 1, Num 2)")
            "exp_to_abstr: Binop (Plus, Num 1, Num 2) \
            = 'Binop (Plus, Num 1, Num 2)' |" ;
  unit_test (exp_to_abstract_string (Binop (FPlus, Float 1.5, Float 2.5)) 
                                     = "Binop (FPlus, Float 1.5, Float 2.5)")
            "exp_to_abstr: Binop (FPlus, Float 1.5, Float 2.5 |" ;
  unit_test (exp_to_abstract_string (Binop (Minus, Num 1, Num 2)) 
                                     = "Binop (Minus, Num 1, Num 2)")
            "exp_to_abstr: Binop (Minus, Num 1, Num 2) \
            = 'Binop (Minus, Num 1, Num 2)' |" ;
  unit_test (exp_to_abstract_string (Binop (FMinus, Float 1.5, Float 2.5)) 
                                     = "Binop (FMinus, Float 1.5, Float 2.5)")
            "exp_to_abstr: Binop (FMinus, Float 1.5, Float 2.5 |" ;
  unit_test (exp_to_abstract_string (Binop (Times, Num 1, Num 2)) 
                                     = "Binop (Times, Num 1, Num 2)")
            "exp_to_abstr: Binop (Times, Num 1, Num 2) \
            = 'Binop (Times, Num 1, Num 2)' |" ;
  unit_test (exp_to_abstract_string (Binop (FTimes, Float 1.5, Float 2.5)) 
                                     = "Binop (FTimes, Float 1.5, Float 2.5)")
            "exp_to_abstr: Binop (FTimes, Float 1.5, Float 2.5 |" ;
  unit_test (exp_to_abstract_string (Binop (Equals, Num 1, Num 2)) 
                                     = "Binop (Equals, Num 1, Num 2)")
            "exp_to_abstr: Binop (Equals, Num 1, Num 2) \
            = 'Binop (Equals, Num 1, Num 2)' |" ;
  unit_test (exp_to_abstract_string (Binop (LessThan, Num 1, Num 2)) 
                                     = "Binop (LessThan, Num 1, Num 2)")
            "exp_to_abstr: Binop (LessThan, Num 1, Num 2) \
            = 'Binop (LessThan, Num 1, Num 2)' |" ;
  unit_test (exp_to_abstract_string (Conditional (Bool true, Num 1, Num 2)) 
                                     = "Conditional (Bool true, Num 1, Num 2)")
            "exp_to_abstr: Conditional (Bool true, Num 1, Num 2) \
             = 'Conditional (Bool true, Num 1, Num 2)' |" ;
  unit_test (exp_to_abstract_string (Fun ("x", Binop (Plus, Var "x", Num 1))) 
                                     = "Fun (x, Binop (Plus, Var x, Num 1))")
            "exp_to_abstr: Fun ('x', Binop (Plus, Var 'x', Num 1)) \
            = 'Fun (x, Binop (Plus, Var x, Num 1))' |" ;
  unit_test (exp_to_abstract_string (Let ("x", Num 1, Binop (Plus, 
                                                             Var "x", 
                                                             Num 1))) 
                                     = "Let (x, Num 1, Binop (Plus, \
                                                              Var x, \
                                                              Num 1))")
            "exp_to_abstr: Let ('x', Num 1, Binop (Plus, Var 'x', Num 1)) \
            = 'Let (x, Num 1, Binop (Plus, Var x, Num 1))' |" ;
  unit_test (exp_to_abstract_string (Letrec ("x", Num 1, Binop (Plus, 
                                                                Var "x", 
                                                                Num 1))) 
                                     = "Letrec (x, Num 1, Binop (Plus, \
                                                                 Var x, \
                                                                 Num 1))")
            "exp_to_abstr: Letrec ('x', Num 1, Binop (Plus, Var 'x', Num 1)) \
            = 'Letrec (x, Num 1, Binop (Plus, Var x, Num 1))' |" ;
  unit_test (exp_to_abstract_string (Raise) = "Raise")
            "exp_to_abstr: Raise = 'Raise' |" ;
  unit_test (exp_to_abstract_string (Unassigned) = "Unassigned")
            "exp_to_abstr: Unassigned = 'Unassigned' |" ;
  unit_test (exp_to_abstract_string (App (Fun ("x", 
                                               Binop (Plus, Var "x", Num 1)),
                                          Num 1)) 
                                  = "App (Fun (x, Binop (Plus, Var x, Num 1)), \
                                          Num 1)")
          "exp_to_abstr: App (Fun ('x', Binop (Plus, Var 'x', Num 1)), Num 1) \
          = 'App (Fun (x, Binop (Plus, Var x, Num 1)), Num 1)' |" ;;

let free_vars_test () =
  unit_test (same_vars (free_vars (Var "x")) (vars_of_list ["x"]))
            "free_vars: var |" ;
  unit_test (same_vars (free_vars (Num 0)) (vars_of_list [])) 
            "free_vars: num |" ;
  unit_test (same_vars (free_vars (Float 0.)) (vars_of_list [])) 
            "free_vars: float |" ;
  unit_test (same_vars (free_vars (Bool true)) (vars_of_list [])) 
            "free_vars: bool |" ;
  unit_test (same_vars (free_vars (Unop (Negate, Var "x"))) 
                       (vars_of_list ["x"]))
            "free_vars: neg var |" ;
  unit_test (same_vars (free_vars (Unop (Negate, Binop (Times, Var "z", 
                                                               Num 4)))) 
                       (vars_of_list ["z"]))
            "free_vars: neg Times |" ;
  unit_test (same_vars (free_vars (Unop (FNegate, Binop (FTimes, Var "z", 
                                                               Float 4.5)))) 
                       (vars_of_list ["z"]))
            "free_vars: neg FTimes |" ;
  unit_test (same_vars (free_vars (Unop (Negate, Binop (LessThan, Var "z", 
                                                                  Num 4)))) 
                       (vars_of_list ["z"]))
            "free_vars: neg LessThan |" ;
  unit_test (same_vars (free_vars (Conditional (Binop (Equals, Var "x", Num 4), 
                                                Binop (Times, Var "z", Num 4), 
                                                Binop (Minus, Var "y", Num 2))))
                       (vars_of_list ["x"; "y"; "z"]))
            "free_vars: conditional |" ;
  unit_test (same_vars (free_vars (Let ("x", 
                                        Binop (Plus, Var "x", Var "y"),
                                        Binop (Times, Var "z", Num 3))))
                       (vars_of_list ["x"; "y"; "z"]))
            "free_vars: embedded let #1 |" ;
  unit_test (same_vars (free_vars (Let ("x", Num 3, 
                                     Let ("y", Var "x", 
                                       App (App (Var "f", Var "x"), Var "y"))))) 
                       (vars_of_list ["f"]))
            "free_vars: embedded let #2 |" ;
  unit_test (same_vars (free_vars (Let ("x", Var "x", 
                                     Let ("y", Var "x", 
                                       App (App (Var "f", Var "x"), Var "y"))))) 
                       (vars_of_list ["f"; "x"]))
            "free_vars: embedded let #3 |" ;
  unit_test (same_vars (free_vars (Let ("x", Var "y", 
                                     Let ("y", Var "x", 
                                       App (App (Var "f", Var "x"), Var "y"))))) 
                       (vars_of_list ["f"; "y"]))
            "free_vars: embedded let #4 |" ;
  unit_test (same_vars (free_vars (Fun ("y", Binop (Plus, Var "y", Var "x"))))
                       (vars_of_list ["x"]))
            "free_vars: simple function |" ;
  unit_test (same_vars (free_vars (Let ("x", Fun ("y", Var "x"), Var "x"))) 
                       (vars_of_list ["x"]))
            "free_vars: fun embedded in let |" ;
  unit_test (same_vars 
              (free_vars (Letrec ("f", 
                                  Fun ("x", 
                                       Conditional (Binop (Equals, 
                                                           Var "x", 
                                                           Num 0), 
                                                    Num 1, 
                                                    App (Var "f", 
                                                         Binop (Minus, 
                                                                Var "x", 
                                                                Num 1)))), 
                                    App (Var "f", Num 4))))
              (vars_of_list []))
            "free_vars: factorial function |" ;
  unit_test (same_vars 
              (free_vars (Letrec ("f", 
                                  Fun ("x", 
                                       Conditional (Binop (Equals, 
                                                           Var "y", 
                                                           Num 0), 
                                                    Num 1, 
                                                    App (Var "f", 
                                                         Binop (Minus, 
                                                                Var "x", 
                                                                Num 1)))), 
                                    App (Var "f", Num 4))))
              (vars_of_list ["y"]))
            "free_vars: factorial func w free var |" ;
  unit_test (free_vars Raise = vars_of_list []) "free_vars: Raise |" ;
  unit_test (free_vars Unassigned = vars_of_list []) "free_vars: Unassigned |" ;
  unit_test (same_vars (free_vars (App (Var "f", 
                                        Binop (Times, Var "x", Var "y"))))
                       (vars_of_list ["f"; "x"; "y"]))
            "free_vars: application #1 |" ;
  unit_test (same_vars (free_vars (App (Fun ("x", Binop (Plus, Var "x", Num 1)), 
                                        Num 1)))
                       (vars_of_list []))
            "free_vars: application #2 |" ;;

let new_varname_test () =
  unit_test (new_varname () = "var0") "new_varname: var0 |" ;
  unit_test (new_varname () = "var1") "new_varname: var1 |" ;
  unit_test (new_varname () = "var2") "new_varname: var2 |" ;
  unit_test (new_varname () = "var3") "new_varname: var3 |" ;;

let subst_test () =
  unit_test (subst "x" (Num 1) (Var "y") = Var "y") "subst: var #1 |" ;
  unit_test (subst "x" (Num 1) (Var "x") = Num 1) "subst: var #2 |" ;
  unit_test (subst "x" (Num 1) (Num 1) = Num 1) "subst: int |" ;
  unit_test (subst "x" (Num 1) (Bool true) = Bool true) "subst: bool |" ;
  unit_test (subst "x" (Num 1) (Unop (Negate, Var "x")) = Unop (Negate, Num 1))
            "subst: negated var |" ;
  unit_test (subst "x" (Float 1.5) (Unop (FNegate, Var "x")) 
            = Unop (FNegate, Float 1.5))
            "subst: F-negated var |" ;
  unit_test (subst "x" (Num 42) (Binop (Plus, Var "x", Var "y")) 
            = Binop (Plus, Num 42, Var "y"))
            "subst: binop |" ;
  unit_test (subst "x" (Float 42.1) (Binop (FPlus, Var "x", Var "y")) 
            = Binop (FPlus, Float 42.1, Var "y"))
            "subst: Fbinop |" ;
  unit_test (subst "x" (Num 1) (Fun ("x", Var "x")) = Fun ("x", Var "x"))
            "subst: function s.t. var_name is bound |" ;
  unit_test (subst "x" (Num 1) (Fun ("y", Var "x")) = Fun ("y", Num 1))
            "subst: function s.t. var_name <> fun var and not FV(repl) |" ;
  unit_test (subst "x" (Var "y") (Fun ("y", Binop (Plus, Var "x", Var "y"))) 
            = Fun ("var4", Binop (Plus, Var "y", Var "var4")))
            "subst: function s.t. var_name <> fun var and is FV(repl) |" ;
  unit_test (subst "x" (Num 1) (Let ("x", Var "x", Var "x")) 
            = Let ("x", Num 1, Var "x"))
            "subst: let s.t. var_name = let var |" ;
  unit_test (subst "x" (Num 1) (Let ("y", Var "x", Var "x")) 
            = Let ("y", Num 1, Num 1))
            "subst: let s.t. var_name <> let var & let var not FR(repl) |" ;
  unit_test (subst "x" (Var "y") (Let ("y", 
                                       Var "x", 
                                       Binop (Plus, Var "y", Var "x"))) 
            = Let ("var5", Var "y", Binop (Plus, Var "var5", Var "y")))
            "subst: let s.t. var_name <> let var & let var is FR(repl) |" ;
  unit_test (subst "f" (Num 1) (Letrec ("f", Var "f", App (Var "f", Num 2)))
            = Letrec ("f", Var "f", App (Var "f", Num 2)))
            "subst: letrec s.t. var_name = let var |" ;
  unit_test (subst "z" (Num 0) (Letrec ("f", 
                                        Fun ("x", 
                                             Conditional (Binop (Equals, 
                                                                 Var "x", 
                                                                 Var "z"), 
                                                          Num 1, 
                                                          App (Var "f", 
                                                               Binop (Minus, 
                                                                      Var "x", 
                                                                      Num 1)))), 
                                        App (Var "f", Binop (Plus, 
                                                             Num 4, 
                                                             Var "z"))))
            = (Letrec ("f", 
                       Fun ("x", 
                            Conditional (Binop (Equals, 
                                                Var "x", 
                                                Num 0), 
                                         Num 1, 
                                         App (Var "f", 
                                              Binop (Minus, 
                                                     Var "x", 
                                                     Num 1)))), 
                       App (Var "f", Binop (Plus, Num 4, Num 0)))))
            "subst: letrec s.t. var_name <> let var & let var not FR(repl) |" ;
  unit_test (subst "z" (Binop (Times, Var "f", Num 1))
                       (Letrec ("f", 
                                Fun ("x", 
                                      Conditional (Binop (Equals, 
                                                          Var "x", 
                                                          Var "z"), 
                                                  Num 1, 
                                                  App (Var "f", 
                                                        Binop (Minus, 
                                                              Var "x", 
                                                              Num 1)))), 
                                App (Var "f", Binop (Plus, 
                                                      Num 4, 
                                                      Var "z"))))
            = (Letrec ("var6", 
                       Fun ("x", 
                            Conditional (Binop (Equals, 
                                                Var "x", 
                                                Binop (Times, Var "f", Num 1)), 
                                         Num 1, 
                                         App (Var "var6", 
                                              Binop (Minus, 
                                                     Var "x", 
                                                     Num 1)))), 
                      App (Var "var6", Binop (Plus, 
                                              Num 4, 
                                              Binop (Times, Var "f", Num 1))))))
            "subst: letrec s.t. var_name <> let var & let var is FR(repl) |" ;
  unit_test (subst "x" (Num 1) Raise = Raise) "subst: Raise |" ;
  unit_test (subst "x" (Num 1) Unassigned = Unassigned) "subst: Unassigned |" ;
  unit_test (subst "x" (Num 1) (App (Fun ("x", Var "x"), Var "x"))
            = App (Fun ("x", Var "x"), Num 1))
            "subst: application |" ;;

let eval_s_test () = 
  let empty = Env.empty () in
  unit_test (eval_s (Num 0) empty = Env.Val (Num 0))
            "eval_s: Num n |" ;
  unit_test (eval_s (Float 0.) empty = Env.Val (Float 0.))
            "eval_s: Float n |" ;
  unit_test (eval_s (Bool true) empty = Env.Val (Bool true))
            "eval_s: Bool b |" ;
  unit_test (eval_s (Unop (Negate, Num 0)) empty = Env.Val (Num ~-0))
            "eval_s: Unop (Negate, Num n) |" ;
  unit_test (eval_s (Unop (FNegate, Float 0.)) empty = Env.Val (Float ~-.0.))
            "eval_s: Unop (FNegate, Float n) |" ;
  unit_test (eval_s (Binop (Plus, Num 1, Num 2)) empty = Env.Val (Num 3))
            "eval_s: Binop (Plus, Num 1, Num 2) |" ;
  unit_test (eval_s (Binop (Minus, Num 1, Num 2)) empty = Env.Val (Num ~-1))
            "eval_s: Binop (Minus, Num 1, Num 2) |" ;
  unit_test (eval_s (Binop (Times, Num 1, Num 2)) empty = Env.Val (Num 2))
            "eval_s: Binop (Times, Num 1, Num 2) |" ;
  unit_test (eval_s (Binop (FPlus, Float 1.5, Float 2.5)) empty 
            = Env.Val (Float 4.))
            "eval_s: Binop (FPlus, Float 1.5, Float 2.5) |" ;
  unit_test (eval_s (Binop (FMinus, Float 1.5, Float 2.5)) empty 
            = Env.Val (Float ~-.1.))
            "eval_s: Binop (FMinus, Float 1.5, Float 2.5) |" ;
  unit_test (eval_s (Binop (FTimes, Float 1.5, Float 2.5)) empty 
            = Env.Val (Float 3.75))
            "eval_s: Binop (FTimes, Float 1.5, Float 2.5) |" ;
  unit_test (eval_s (Binop (Equals, Num 1, Num 2)) empty = Env.Val (Bool false))
            "eval_s: Binop (Equals, Num 1, Num 2) |" ;
  unit_test (eval_s (Binop (LessThan, Num 1, Num 2)) empty 
            = Env.Val (Bool true))
            "eval_s: Binop (LessThan, Num 1, Num 2) |" ;
  unit_test (eval_s (Binop (Equals, Float 1.5, Float 2.5)) empty 
            = Env.Val (Bool false))
            "eval_s: Binop (Equals, Float 1.5, Float 2.5) |" ;
  unit_test (eval_s (Binop (LessThan, Float 1.5, Float 2.5)) empty 
            = Env.Val (Bool true))
            "eval_s: Binop (LessThan, Float 1.5, Float 2.5) |" ;
  unit_test (eval_s (Binop (Equals, Binop (LessThan, Num 2, Num 1), Bool false))
                     empty 
            = Env.Val (Bool true))
            "eval_s: 2 < 1 = false |" ;
  unit_test (eval_s (Binop (LessThan, Binop (LessThan, Num 2, Num 1),Bool true))
                     empty 
            = Env.Val (Bool true))
            "eval_s: (2 < 1) < true |" ;
  unit_test (eval_s (Conditional (Binop (Equals, Num 1, Num 2), Num 1, Num 2)) 
                     empty 
            = Env.Val (Num 2))
            "eval_s: if (1 = 2) then 1 else 2 |" ;
  unit_test (eval_s (Conditional (Binop (Equals, Num 1, Num 1), Num 1, Num 2)) 
                     empty 
            = Env.Val (Num 1))
            "eval_s: if (1 = 1) then 1 else 2 |" ;
  unit_test (eval_s (Fun ("x", Var "x")) empty = Env.Val (Fun ("x", Var "x")))
            "eval_s: fun x -> x |" ;
  unit_test (eval_s (Let ("x", Num 1, Binop (Plus, Var "x", Num 2))) empty
            = Env.Val (Num 3))
            "eval_s: let x = 1 in x + 2 |" ;
  unit_test (eval_s (Let ("x", Float 1., Binop (FPlus, Var "x", Float 2.5))) 
            empty
            = Env.Val (Float 3.5))
            "eval_s: let x = 1. in x +. 2.5 |" ;
  unit_test (eval_s (Letrec ("f", 
                             Fun ("n", 
                                  Conditional (Binop (Equals, Var "n", Num 1), 
                                               Num 1, 
                                               Binop (Times, 
                                                      Var "n", 
                                                      App (Var "f", 
                                                           Binop (Minus, 
                                                                  Var "n", 
                                                                  Num 1))))),
                              App (Var "f", Num 4)))
                     empty
            = Env.Val (Num 24))
            "eval_s: fact 4 |" ;
  unit_test (eval_s (App (Fun ("x", Var "x"), Num 1)) empty = Env.Val (Num 1))
            "eval_s: (fun x -> x) 1 |" ;
  unit_test (eval_s shieber1 empty = Env.Val (Num 42))
            "eval_s: shieber1 |" ;
  unit_test (eval_s shieber2 empty = Env.Val (Num 42))
            "eval_s: shieber2 |" ;;
  
let env_mod_test () =
  let x_ref = ref (Env.Val (Num (2))) in
  let env1 = Env.extend (Env.empty ()) "x" x_ref in
  unit_test (Env.env_to_string env1 = "{x |--> 2}") "env: x maps to 2 |";
  (* print_string (Env.env_to_string env1 ^ "\n") ; *)
  x_ref := Env.Val (Binop (Plus, Var ("y"), Num (2)));
  let env2 = Env.extend env1 "x" x_ref in
  unit_test (Env.env_to_string env2 = "{x |--> y + 2}") 
            "env: x maps to y + 2 |";
  (* print_string (Env.env_to_string env2 ^ "\n") ; *)
  let y_ref = ref (Env.Val (Fun ("x", Binop (Plus, Var ("x"), Num (2))))) in
  let env3 = Env.extend env2 "y" y_ref in
  unit_test (Env.env_to_string env3 
            = "{y |--> fun x -> x + 2; x |--> y + 2}") 
            "env: y maps to fun, x maps to Binop |";
  (* print_string (Env.env_to_string env3 ^ "\n") ; *)
  let y_ref = ref (Env.Val (Num (2))) in
  let env4 = Env.extend env3 "y" y_ref in
  unit_test (Env.env_to_string env4 
            = "{y |--> 2; x |--> y + 2}") 
            "env: y maps to 2, x maps to Binop |" ;
  (* print_string (Env.env_to_string env4 ^ "\n") ; *)
  let fun1 = Fun ("z", Binop (Plus, Var ("z"), Var ("x"))) in
  let closure1_ref = ref (Env.Closure (fun1, env4)) in
  let env5 = Env.extend env4 "f" closure1_ref in
  unit_test (Env.env_to_string env5 
            = "{f |--> [{y |--> 2; x |--> y + 2} |-- fun z -> z + x]; \
              y |--> 2; x |--> y + 2}")
            "env: f maps to closure, y maps to 2, x maps to Binop |";
  (* print_string (Env.env_to_string env5 ^ "\n") *) ;;

let eval_d_test () = 
  let empty = Env.empty () in
  unit_test (eval_d (Num 0) empty = Env.Val (Num 0))
            "eval_d: Num n |" ;
  unit_test (eval_d (Bool true) empty = Env.Val (Bool true))
            "eval_d: Bool b |" ;
  unit_test (eval_d (Unop (Negate, Num 0)) empty = Env.Val (Num ~-0))
            "eval_d: Unop (Negate, Num n) |" ;
  unit_test (eval_d (Unop (FNegate, Float 0.)) empty = Env.Val (Float ~-.0.))
            "eval_d: Unop (FNegate, Float n) |" ;
  unit_test (eval_d (Binop (Plus, Num 1, Num 2)) empty = Env.Val (Num 3))
            "eval_d: Binop (Plus, Num 1, Num 2) |" ;
  unit_test (eval_d (Binop (Minus, Num 1, Num 2)) empty = Env.Val (Num ~-1))
            "eval_d: Binop (Minus, Num 1, Num 2) |" ;
  unit_test (eval_d (Binop (Times, Num 1, Num 2)) empty = Env.Val (Num 2))
            "eval_d: Binop (Times, Num 1, Num 2) |" ;
  unit_test (eval_d (Binop (FPlus, Float 1.5, Float 2.5)) empty 
            = Env.Val (Float 4.))
            "eval_d: Binop (FPlus, Float 1.5, Float 2.5) |" ;
  unit_test (eval_d (Binop (FMinus, Float 1.5, Float 2.5)) empty 
            = Env.Val (Float ~-.1.))
            "eval_d: Binop (FMinus, Float 1.5, Float 2.5) |" ;
  unit_test (eval_d (Binop (FTimes, Float 1.5, Float 2.5)) empty 
            = Env.Val (Float 3.75))
            "eval_d: Binop (FTimes, Float 1.5, Float 2.5) |" ;
  unit_test (eval_d (Binop (Equals, Float 1.5, Float 2.5)) empty 
            = Env.Val (Bool false))
            "eval_d: Binop (Equals, Float 1.5, Float 2.5) |" ;
  unit_test (eval_d (Binop (LessThan, Float 1.5, Float 2.5)) empty 
            = Env.Val (Bool true))
            "eval_d: Binop (LessThan, Float 1.5, Float 2.5) |" ;
  unit_test (eval_d (Binop (Equals, Num 1, Num 2)) empty = Env.Val (Bool false))
            "eval_d: Binop (Equals, Num 1, Num 2) |" ;
  unit_test (eval_d (Binop (LessThan, Num 1,Num 2)) empty = Env.Val (Bool true))
            "eval_d: Binop (LessThan, Num 1, Num 2) |" ;
  unit_test (eval_d (Binop (Equals, Binop (LessThan, Num 2, Num 1), Bool false))
                     empty 
            = Env.Val (Bool true))
            "eval_d: 2 < 1 = false |" ;
  unit_test (eval_d (Binop (LessThan, Binop (LessThan, Num 2,Num 1), Bool true))
                     empty 
            = Env.Val (Bool true))
            "eval_d: (2 < 1) < true |" ;
  unit_test (eval_s (Conditional (Binop (Equals, Num 1, Num 2), Num 1, Num 2)) 
                     empty 
            = Env.Val (Num 2))
            "eval_d: if (1 = 2) then 1 else 2 |" ;
  unit_test (eval_d (Conditional (Binop (Equals, Num 1, Num 1), Num 1, Num 2)) 
                     empty 
            = Env.Val (Num 1))
            "eval_d: if (1 = 1) then 1 else 2 |" ;
  unit_test (eval_d (Fun ("x", Var "x")) empty = Env.Val (Fun ("x", Var "x")))
            "eval_d: fun x -> x |" ;
  unit_test (eval_d (Let ("x", Num 1, Binop (Plus, Var "x", Num 2))) empty
            = Env.Val (Num 3))
            "eval_d: let x = 1 in x + 2 |" ;
  unit_test (eval_d (Let ("x", Float 1., Binop (FPlus, Var "x", Float 2.5))) 
            empty
            = Env.Val (Float 3.5))
            "eval_d: let x = 1. in x +. 2.5 |" ;
  unit_test (eval_d (Letrec ("f", 
                             Fun ("n", 
                                  Conditional (Binop (Equals, Var "n", Num 1), 
                                               Num 1, 
                                               Binop (Times, 
                                                      Var "n", 
                                                      App (Var "f", 
                                                           Binop (Minus, 
                                                                  Var "n", 
                                                                  Num 1))))),
                              App (Var "f", Num 4)))
                     empty
            = Env.Val (Num 24))
            "eval_d: fact 4 |" ;
  unit_test (eval_d (App (Fun ("x", Var "x"), Num 1)) empty = Env.Val (Num 1))
            "eval_d: (fun x -> x) 1 |" ;
  unit_test (eval_d shieber1 empty = Env.Val (Num 21))
            "eval_d: shieber1 |" ;
  unit_test (try
              eval_d shieber2 empty = Env.Val (Num 42)
             with
              EvalError _ -> true)
            "eval_d: shieber2 |" ;;

let eval_l_test () =
  let empty = Env.empty () in
  unit_test (eval_l (Num 0) empty = Env.Val (Num 0))
            "eval_l: Num n |" ;
  unit_test (eval_l (Bool true) empty = Env.Val (Bool true))
            "eval_l: Bool b |" ;
  unit_test (eval_l (Unop (Negate, Num 0)) empty = Env.Val (Num ~-0))
            "eval_l: Unop (Negate, Num n) |" ;
  unit_test (eval_l (Unop (FNegate, Float 0.)) empty = Env.Val (Float ~-.0.))
            "eval_l: Unop (FNegate, Float n) |" ;
  unit_test (eval_l (Binop (Plus, Num 1, Num 2)) empty = Env.Val (Num 3))
            "eval_l: Binop (Plus, Num 1, Num 2) |" ;
  unit_test (eval_l (Binop (Minus, Num 1, Num 2)) empty = Env.Val (Num ~-1))
            "eval_l: Binop (Minus, Num 1, Num 2) |" ;
  unit_test (eval_l (Binop (Times, Num 1, Num 2)) empty = Env.Val (Num 2))
            "eval_l: Binop (Times, Num 1, Num 2) |" ;
  unit_test (eval_l (Binop (FPlus, Float 1.5, Float 2.5)) empty 
            = Env.Val (Float 4.))
            "eval_l: Binop (FPlus, Float 1.5, Float 2.5) |" ;
  unit_test (eval_l (Binop (FMinus, Float 1.5, Float 2.5)) empty 
            = Env.Val (Float ~-.1.))
            "eval_l: Binop (FMinus, Float 1.5, Float 2.5) |" ;
  unit_test (eval_l (Binop (FTimes, Float 1.5, Float 2.5)) empty 
            = Env.Val (Float 3.75))
            "eval_l: Binop (FTimes, Float 1.5, Float 2.5) |" ;
  unit_test (eval_l (Binop (Equals, Float 1.5, Float 2.5)) empty 
            = Env.Val (Bool false))
            "eval_l: Binop (Equals, Float 1.5, Float 2.5) |" ;
  unit_test (eval_l (Binop (LessThan, Float 1.5, Float 2.5)) empty 
            = Env.Val (Bool true))
            "eval_l: Binop (LessThan, Float 1.5, Float 2.5) |" ;
  unit_test (eval_l (Binop (Equals, Num 1, Num 2)) empty = Env.Val (Bool false))
            "eval_l: Binop (Equals, Num 1, Num 2) |" ;
  unit_test (eval_l (Binop (LessThan, Num 1,Num 2)) empty = Env.Val (Bool true))
            "eval_l: Binop (LessThan, Num 1, Num 2) |" ;
  unit_test (eval_l (Binop (Equals, Binop (LessThan, Num 2, Num 1), Bool false))
                     empty 
            = Env.Val (Bool true))
            "eval_l: 2 < 1 = false |" ;
  unit_test (eval_l (Binop (LessThan, Binop (LessThan, Num 2,Num 1), Bool true))
                     empty 
            = Env.Val (Bool true))
            "eval_l: (2 < 1) < true |" ;
  unit_test (eval_l (Conditional (Binop (Equals, Num 1, Num 2), Num 1, Num 2)) 
                     empty 
            = Env.Val (Num 2))
            "eval_l: if (1 = 2) then 1 else 2 |" ;
  unit_test (eval_l (Conditional (Binop (Equals, Num 1, Num 1), Num 1, Num 2)) 
                     empty 
            = Env.Val (Num 1))
            "eval_l: if (1 = 1) then 1 else 2 |" ;
  unit_test (eval_l (Fun ("x", Var "x")) empty
            = Env.Closure (Fun ("x", Var "x"), empty))
            "eval_l: fun x -> x |" ;
  unit_test (eval_l (Let ("x", Num 1, Binop (Plus, Var "x", Num 2))) empty
            = Env.Val (Num 3))
            "eval_l: let x = 1 in x + 2 |" ;
  unit_test (eval_l (Let ("x", Float 1., Binop (FPlus, Var "x", Float 2.5))) 
            empty
            = Env.Val (Float 3.5))
            "eval_l: let x = 1. in x +. 2.5 |" ;
  unit_test (eval_l (Letrec ("f", 
                             Fun ("n", 
                                  Conditional (Binop (Equals, Var "n", Num 1), 
                                               Num 1, 
                                               Binop (Times, 
                                                      Var "n", 
                                                      App (Var "f", 
                                                           Binop (Minus, 
                                                                  Var "n", 
                                                                  Num 1))))),
                              App (Var "f", Num 4)))
                     empty
            = Env.Val (Num 24))
            "eval_l: fact 4 |" ;
  unit_test (eval_l (App (Fun ("x", Var "x"), Num 1)) empty = Env.Val (Num 1))
            "eval_l: (fun x -> x) 1 |" ;
  unit_test (eval_l shieber1 empty = Env.Val (Num 42))
            "eval_l: shieber1 |" ;
  unit_test (eval_l shieber2 empty = Env.Val (Num 42))
            "eval_l: shieber2 |" ;;

(* run tests *)
let _ = 
  exp_to_concr_str_test () ;
  exp_to_abstr_str_test () ;
  free_vars_test () ;
  new_varname_test () ;
  subst_test () ;
  eval_s_test () ;
  env_mod_test () ;
  eval_d_test () ;
  eval_l_test () ;;
