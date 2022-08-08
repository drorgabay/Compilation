#use "reader.ml";; 

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;
exception X_invalid_input of string;; (* mine *)

let rec list_to_proper_list = function
  | [] -> ScmNil
  | hd::[] -> ScmPair (hd, ScmNil)
  | hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
  | [] -> raise X_proper_list_error
  | hd::[] -> hd
  | hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
  match scm_list with
    | ScmNil -> sexpr
    | ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
    | _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
  match sexpr with
    | ScmNil -> ScmNil
    | ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
    | _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
  match sexpr1, sexpr2 with
    | ScmNil, ScmNil -> ScmNil
    | ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
    | _, _ ->
      let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
      raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
  | ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
  | ScmNil -> []
  | sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function 
  | ScmPair (hd, tl) -> scm_is_list tl
  | ScmNil -> true
  | _ -> false

let rec scm_list_length = function
  | ScmPair (hd, tl) -> 1 + (scm_list_length tl)
  | ScmNil -> 0
  | sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
  let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
  let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

  let untag_lambda_opt vars var body =
  let vars = match vars with
    | [] -> ScmSymbol var
    | _ -> list_to_improper_list (untag_vars (vars@[var])) in
  list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

  match expr with
    | (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
    | ScmConst s -> s
    | ScmVar (name) -> ScmSymbol(name)
    | ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
    | ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
    | ScmSeq(exprs) -> untag_tagged_list "begin" exprs
    | ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
    | ScmDef (var, value) -> untag_tagged_list "define" [var; value]
    | ScmOr (exprs) -> untag_tagged_list "or" exprs
    | ScmLambdaSimple (vars, ScmSeq(body)) ->
      let vars = list_to_proper_list (untag_vars vars) in
      let body = List.map untag body in
      list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
    | ScmLambdaSimple (vars, body) ->
      let vars = list_to_proper_list (untag_vars vars) in
      list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
    | ScmLambdaOpt (vars, var, ScmSeq(body)) ->
      let body = List.map untag body in
      untag_lambda_opt vars var body
    | ScmLambdaOpt (vars, var, body) ->
      let body = [untag body] in
      untag_lambda_opt vars var body
    | ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;

let rec string_of_expr expr =
  string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
  match n1, n2 with
    | ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
      numerator1 = numerator2 && denominator1 = denominator2
    | ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
    | _, _ -> false

let rec sexpr_eq s1 s2 =
  match s1, s2 with
    | (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
    | ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
    | ScmChar(char1), ScmChar(char2) -> char1 = char2
    | ScmString(string1), ScmString(string2) -> String.equal string1 string2
    | ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
    | ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
    | ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
    | ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
    | _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
    | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
    | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
    | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                                            (expr_eq dit1 dit2) &&
                                                              (expr_eq dif1 dif2)
    | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
    List.for_all2 expr_eq exprs1 exprs2
    | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
    (expr_eq var1 var2) && (expr_eq val1 val2)
    | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
    (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
    | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
    (String.equal var1 var2) &&
      (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
    | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
    (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
    | _ -> false;;

module type TAG_PARSER = sig
val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
["and"; "begin"; "cond"; "define"; "else";
  "if"; "lambda"; "let"; "let*"; "letrec"; "or";
  "quasiquote"; "quote"; "set!"; "unquote";
  "unquote-splicing"];;

(* HELPER FUNCTIONS FOR TAG PARSER *)
(* FOR IF *)

let if_case f test dit dif = match dif with
  | ScmNil -> ScmIf((f test), (f dit), ScmConst(ScmVoid))
  | ScmPair(car, ScmNil) -> ScmIf((f test), (f dit), (f car))
  | _ -> raise (X_syntax_error (dif, "Illegal dif- in if_case function"));;

(* FOR OR *)

let or_case f sexprs = match sexprs with
  | ScmNil -> ScmConst(ScmBoolean(false))
  | ScmPair(car, ScmNil) -> f car
  | _ -> let exprs = scm_list_to_list sexprs in
      let exprs = List.map f exprs in
      ScmOr exprs;;

(* FOR LAMBDA CASES *)

let reserved word =
  if (List.mem word reserved_word_list) then true else false;;

let var_case var e =
  if (not (reserved var)) then ScmVar var else raise(e);;

let rec dup_exist = function 
  | [] -> false
  | hd :: tl -> List.exists ((=) hd) tl || dup_exist tl;;

let rec tail = function
  | [] -> raise (X_invalid_input "Cant apply the function tail on empty list")
  | [x] -> x
  | hd :: tl -> (tail tl);;

let rec remove_last = function
  | [] -> raise (X_invalid_input "Cant apply the function remove_last on empty list")
  | [x] -> []
  | hd :: tl -> hd :: (remove_last tl);;

let rec is_proper_list = function
  | ScmNil -> true
  | ScmPair(car,cdr) -> is_proper_list cdr
  | _ -> false;;

let rec is_improper_list = function
  | ScmNil -> false
  | ScmPair(car,cdr) -> is_improper_list cdr
  | _ -> true;;

let rec proper_list_to_string_list arglist = match arglist with 
  | ScmNil -> []
  | ScmPair(ScmSymbol(car), cdr) when (not (reserved car)) -> car :: proper_list_to_string_list cdr 
  | _ -> raise (X_syntax_error (arglist, "Illegal arglist- in proper_list_to_string_list function"));;

let rec improper_list_to_string_list arglist = match arglist with
  | ScmPair(ScmSymbol(car), cdr) when (not (reserved car)) -> car :: (improper_list_to_string_list cdr)
  | ScmSymbol(x) -> x :: []
  | _ -> raise (X_syntax_error (arglist, "Illegal arglist- in improper_list_to_string_list function"));;

let arglist_validity arglist =
  let dup = dup_exist arglist in
  if dup then raise (X_invalid_input "Illegal arglist- in arglist_validity function") else arglist;;  

let body_validity f body = match body with
  | ScmPair(ScmNil, ScmNil) -> raise (X_syntax_error (body, "Illegal body in body_validity function"))
  | ScmPair(car, ScmNil) -> f car
  | ScmPair(car, cdr) -> ScmSeq(List.map f (scm_list_to_list body))
  | _ -> raise (X_syntax_error (body, "Illegal body in body_validity function"));;

let lambda_simple_case f arglist body = 
  let arglist = proper_list_to_string_list arglist in
  let arglist = arglist_validity arglist in
  let body = body_validity f body in
  ScmLambdaSimple (arglist, body);;

let lambda_optional_case f arglist body =
  let arglist = improper_list_to_string_list arglist in
  let arglist = arglist_validity arglist in
  let last = tail arglist in
  let arglist = remove_last arglist in
  let body = body_validity f body in
  ScmLambdaOpt (arglist, last, body);;

let lambda_variadic_case f var body =
  let body = body_validity f body in
  if (not (reserved var)) then ScmLambdaOpt ([], var, body) else raise (X_syntax_error (ScmSymbol(var), "Illegal var- in lambda_variadic_case function"));;

(* FOR APPLIC *)

let first_expr_validity f expr = match expr with
  | ScmSymbol(sym) when (reserved sym) -> raise (X_syntax_error (ScmSymbol(sym), "Illegal var- in first_expr_validity function"))
  | _ -> f expr;;

let rest_of_exprs_validity f exprs = match exprs with 
  | ScmNil -> []
  | ScmPair(expr, ScmNil) -> [f expr] 
  | ScmPair(expr, rest_of_exprs) -> List.map f (scm_list_to_list exprs)
  | _ -> raise (X_syntax_error (exprs, "Illegal exprs- in rest_exprs_validity function"));; 

let applic_case f expr exprs =
  let expr = first_expr_validity f expr in
  let exprs = rest_of_exprs_validity f exprs in
  ScmApplic (expr, exprs);;

(* FOR SET AND DEFINE *)

let var_validity var e = match var with
  | ScmSymbol(sym) when (not (reserved sym)) -> ScmVar sym
  | _ -> raise(e);;

let value_validity f value e = match value with
  | ScmPair(car, ScmNil) -> f car
  | _ -> raise(e);; 

let set_case f var value = 
  let var = var_validity var (X_syntax_error (var, "Illegal var- in set_case function")) in
  let value = value_validity f value (X_syntax_error (value, "Illegal value- in set_case function")) in
  ScmSet(var, value);;

let define_simple_case f var value =
  let var = var_validity var (X_syntax_error (var, "Illegal var- in define_simple_case function")) in
  let value = value_validity f value (X_syntax_error (value, "Illegal value- in define_simple_case function")) in
  ScmDef(var, value);;

(* FOR BEGIN *)

let begin_case f exprs = match exprs with
  | ScmPair(car, ScmNil) -> f car 
  | ScmPair(car, cdr) -> ScmSeq (List.map f (scm_list_to_list exprs)) 
  | _ -> raise (X_syntax_error (exprs, "Illegal exprs- in begin_case function"));;

(* MACRO EXPANSIONS *)
(* MACRO EXPANSION FOR DEFINE *)

let macro_expand_define lst expr = match lst with
  | ScmPair(car, cdr) -> ScmPair(ScmSymbol "define", ScmPair(car, ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(cdr,expr)), ScmNil)))
  | _ -> ScmPair(ScmSymbol "define", ScmPair(lst, expr));;

(* MACRO EXPANSION FOR QUASIQUOTE *) 

let vector_case f sexprlist =
  let vector_to_scm_list = list_to_proper_list sexprlist in
  match vector_to_scm_list with
    | ScmNil -> ScmPair(ScmSymbol "list->vector", f ScmNil)
    | ScmPair(car, cdr) -> ScmPair(ScmSymbol "list->vector", ScmPair((f vector_to_scm_list), ScmNil))
    | _ -> raise (X_syntax_error (vector_to_scm_list, "Illegal vector- in vector_case function"))

let rec macro_expand_quasiquote sexpr = match sexpr with
  | ScmPair(ScmSymbol "unquote", ScmPair(sexp, ScmNil)) -> sexp
  | ScmPair(ScmSymbol "unquote-splicing", ScmPair(sexp, ScmNil)) -> 
    ScmPair(ScmSymbol "quote", ScmPair(ScmPair(ScmSymbol "unquote-splicing", ScmPair(sexp, ScmNil)), ScmNil))
  | ScmNil -> ScmPair(ScmSymbol "quote", ScmPair(ScmNil, ScmNil))
  | ScmSymbol(_) -> ScmPair(ScmSymbol "quote", ScmPair(sexpr, ScmNil))
  | ScmVector sexprlist -> vector_case macro_expand_quasiquote sexprlist 
  | ScmPair(ScmPair(ScmSymbol "unquote-splicing", ScmPair(sexp, ScmNil)), sexprs) ->
    ScmPair(ScmSymbol "append", ScmPair(sexp, ScmPair((macro_expand_quasiquote sexprs), ScmNil)))
  | ScmPair(car, cdr) -> 
    ScmPair(ScmSymbol "cons", ScmPair((macro_expand_quasiquote car), ScmPair((macro_expand_quasiquote cdr), ScmNil)))
  | _ -> sexpr 

 (* MACRO EXPANSION FOR AND *) 

let rec macro_expand_and exprs = match exprs with
  | ScmNil -> ScmBoolean(true)
  | ScmPair(expr, ScmNil) -> expr
  | ScmPair(expr, rest_of_exprs) ->
      let exprs' = macro_expand_and rest_of_exprs in
      ScmPair(ScmSymbol "if", ScmPair(expr, ScmPair(exprs', ScmPair(ScmBoolean(false), ScmNil))))
  | _ -> raise (X_syntax_error (exprs, "Illegal exprs- in macro_expand_and"));;

(* MACRO EXPANSION FOR COND *)

let not_nill = function
  | ScmNil -> false
  | _ -> true;;

let rec macro_expand_cond = function
  | ScmNil -> ScmVoid
  | ScmPair(ScmPair(ScmSymbol "else", sexprs), ribs) -> else_rib_case sexprs
  | ScmPair(ScmPair(expr, ScmPair(ScmSymbol "=>", ScmPair(func, ScmNil))), ribs) ->
    arrow_rib_case expr func ribs
  | ScmPair(ScmPair(test, sexprs), ribs) ->
    simple_rib_case test sexprs ribs
  | ribs -> raise (X_syntax_error(ribs, "Illegal rib- in macro_expand_cond function")) 

and simple_rib_case test sexprs ribs = 
  let dit = ScmPair (ScmSymbol "begin", sexprs) in
  let dif = macro_expand_cond ribs in
  ScmPair
    (ScmSymbol "if",
      ScmPair
        (test,
          ScmPair (dit, ScmPair (dif, ScmNil))))

and arrow_rib_case expr func ribs =
  let ribs' = macro_expand_cond ribs in
ScmPair
  (ScmSymbol "let",
    ScmPair
      (ScmPair
        (ScmPair (ScmSymbol "value", ScmPair (expr, ScmNil)),
      ScmPair
        (ScmPair
          (ScmSymbol "f",
            ScmPair
              (ScmPair
          (ScmSymbol "lambda",
          ScmPair (ScmNil, ScmPair (func, ScmNil))),
        ScmNil)),
    ScmPair
      (ScmPair
        (ScmSymbol "rest",
        ScmPair
          (ScmPair
            (ScmSymbol "lambda",
            ScmPair (ScmNil, ScmPair (ribs', ScmNil))),
          ScmNil)),
      ScmNil))),
ScmPair
  (ScmPair
    (ScmSymbol "if",
    ScmPair
      (ScmSymbol "value",
      ScmPair
        (ScmPair
          (ScmPair (ScmSymbol "f", ScmNil),
          ScmPair (ScmSymbol "value", ScmNil)),
        ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
  ScmNil))) 

and else_rib_case sexprs =
  ScmPair(ScmSymbol "begin", sexprs);; 

(* MACRO EXPANSION FOR LET *)

let rec take_arguments_from bindings = match bindings with
  | ScmPair(ScmPair(arg, value), rest_of_bindings) -> 
      let rest_of_args = take_arguments_from rest_of_bindings in
      ScmPair(arg, rest_of_args)
  | ScmNil -> ScmNil
  | _ -> raise (X_syntax_error (bindings, "Illegal bindings- in take_arguments_from function"))

let rec apply_with bindings = match bindings with
  | ScmPair(ScmPair(arg, ScmPair(value, ScmNil)), rest_of_bindings) -> 
      let rest_of_values = apply_with rest_of_bindings in
      ScmPair(value, rest_of_values)
  | ScmNil -> ScmNil
  | _ -> raise (X_syntax_error (bindings, "Illegal bindings- in apply_with function"))

let macro_expand_let bindings body = 
  let params = take_arguments_from bindings in
  let applic = apply_with bindings in
  ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(params, body)), applic)

(* MACRO EXPANSION FOR LET* *)

let rec macro_expand_let_star bindings body = match bindings with
  | ScmNil -> ScmPair(ScmSymbol "let", ScmPair (ScmNil, body))
  | ScmPair(ScmPair(arg, ScmPair(binding, ScmNil)), ScmNil) ->
    ScmPair(ScmSymbol "let", ScmPair(bindings, body))
  | ScmPair(binding, rest_of_bindings) -> 
      let bindings' = ScmPair(binding, ScmNil) in
      let body = macro_expand_let_star rest_of_bindings body in
      ScmPair(ScmSymbol "let", ScmPair(bindings', ScmPair(body, ScmNil))) 
  | _ -> raise (X_syntax_error (bindings, "Illegal bindings- in macro_expand_let_star function"))

(* MACRO EXPANSION FOR LETREC *)

let rec scheme_list_to_ocaml = function
  | ScmNil -> ([], ScmNil)
  | ScmPair(car, cdr) ->
     ((fun (rdc, rac) -> (car :: rdc, rac))
        (scheme_list_to_ocaml cdr))
  | sexpr -> ([], sexpr);;

let macro_expand_let_rec ribs exprs =
  match (scheme_list_to_ocaml ribs) with
  | params, ScmNil ->
     let names =
       List.map
         (function
            | ScmPair(name, ScmPair (_, ScmNil)) -> name
            | _ -> raise (X_invalid_input "Illegal ribs in macro_expand_let_rec function"))
         params in
     let args =
       List.map
         (function
            | ScmPair (_, ScmPair (arg, ScmNil)) -> arg
            | _ -> raise (X_invalid_input "Illegal ribs in macro_expand_let_rec function"))
         params in
     let ribs =
       List.map
         (fun name ->
           ScmPair(name,
                    ScmPair(ScmPair(ScmSymbol "quote",
                                      ScmPair (ScmSymbol "whatever", ScmNil)),
                             ScmNil)))
         names in
     let ribs =
       List.fold_right
         (fun car cdr -> ScmPair(car, cdr))
         ribs
         ScmNil in
     let set_exprs =
       List.map2
         (fun name arg ->
           ScmPair(ScmSymbol "set!",
                    ScmPair(name, ScmPair(arg, ScmNil))))
         names
         args in
     let exprs =
       List.fold_right
         (fun car cdr -> ScmPair(car, cdr))
         set_exprs
         exprs in
     ScmPair
       (ScmSymbol "let",
        ScmPair(ribs, exprs))
  | _ -> raise (X_invalid_input "Illegal ribs in macro_expand_let_rec function");;

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in 
  match sexpr with 
    (* for SELF-EVALUATING *)
    | ScmVoid -> ScmConst ScmVoid
    | (ScmNil as sexpr) -> ScmConst sexpr
    | (ScmBoolean(_) as sexpr) -> ScmConst sexpr
    | (ScmChar(_) as sexpr) -> ScmConst sexpr
    | (ScmNumber(_) as sexpr) -> ScmConst sexpr
    | (ScmString(_) as sexpr) -> ScmConst sexpr
    (* for QUOTE *)
    | (ScmPair(ScmSymbol "quote", ScmPair(sexpr, ScmNil))) -> ScmConst sexpr 
    (* for VARS *)
    | ScmSymbol(var) -> var_case var (X_reserved_word (var));
    (* for IF-STATEMENT *) 
    | (ScmPair(ScmSymbol "if", ScmPair(test, ScmPair(dit, dif)))) -> if_case tag_parse_expression test dit dif
    (* for OR *)
    | (ScmPair(ScmSymbol "or", sexprs)) -> or_case tag_parse_expression sexprs
    (* for SIMPLE-LAMBDA *)
    | (ScmPair(ScmSymbol "lambda", ScmPair(arglist, body))) when (is_proper_list arglist) ->
        lambda_simple_case tag_parse_expression arglist body
    (* for OPTIONAL-LAMBDA *)
    | (ScmPair(ScmSymbol "lambda", ScmPair(arglist, body))) when (is_improper_list arglist) ->
        lambda_optional_case tag_parse_expression arglist body
    (* for VARIADIC-LAMBDA *)
    | (ScmPair(ScmSymbol "lambda", ScmPair(ScmSymbol var, body))) -> 
        lambda_variadic_case tag_parse_expression var body
    (* for DEFINE *)
    | (ScmPair(ScmSymbol "define", ScmPair(var, value))) -> define_simple_case tag_parse_expression var value
    (* for SET! *)
    | (ScmPair(ScmSymbol "set!", ScmPair(var,value))) -> set_case tag_parse_expression var value
    (* for SEQUENCES *)
    | (ScmPair(ScmSymbol "begin", exprs)) -> begin_case tag_parse_expression exprs
    (* for APPLICATION *)
    | (ScmPair(car, cdr)) -> applic_case tag_parse_expression car cdr 
    | _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

and macro_expand sexpr =
  match sexpr with
    | (ScmPair(ScmSymbol "let", ScmPair(bindings, body))) -> macro_expand_let bindings body 
    | (ScmPair(ScmSymbol "let*", ScmPair(bindings, body))) -> macro_expand (macro_expand_let_star bindings body)
    | (ScmPair(ScmSymbol "letrec", ScmPair(ribs, exprs))) -> macro_expand (macro_expand_let_rec ribs exprs)
    | (ScmPair(ScmSymbol "and", sexprs)) -> macro_expand_and sexprs 
    | (ScmPair(ScmSymbol "cond", ribs)) when (not_nill ribs) -> macro_expand (macro_expand_cond ribs) (* new *)
    | (ScmPair(ScmSymbol "define", ScmPair(lst, expr))) -> macro_expand_define lst expr 
    | (ScmPair(ScmSymbol "quasiquote", ScmPair(sexpr, ScmNil))) -> macro_expand_quasiquote sexpr 
    | _ -> sexpr

end;;

