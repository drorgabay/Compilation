(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
exception X_error of string;; (* mine *)

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

let rec lookup_in_rib name = function
  | [] -> None
  | name' :: rib ->
    if name = name'
      then Some(0)
      else (match (lookup_in_rib name rib) with
            | None -> None
            | Some minor -> Some (minor + 1));;

let rec lookup_in_env name = function
  | [] -> None
  | rib :: env ->
      (match (lookup_in_rib name rib) with
       | None ->
          (match (lookup_in_env name env) with
           | None -> None
           | Some(major, minor) -> Some(major + 1, minor))
       | Some minor -> Some(0, minor));;

let tag_lexical_address_for_var name params env = 
  match (lookup_in_rib name params) with
   | None ->
    (match (lookup_in_env name env) with
     | None -> VarFree name
     | Some(major, minor) -> VarBound(name, major, minor))
   | Some minor -> VarParam(name, minor);;   

  (* run this first! *)

let annotate_lexical_addresses pe = 
  let rec run params env pe =
    match pe with
    | ScmConst sexpr -> ScmConst' (sexpr)
    | ScmVar variable -> ScmVar' (tag_lexical_address_for_var variable params env)
    | ScmIf (test, dit, dif) -> ScmIf' ((run params env test),
                                        (run params env dit),
                                        (run params env dif))
    | ScmSeq exprs -> ScmSeq' (List.map (run params env) exprs)
    | ScmSet (ScmVar variable, value) -> ScmSet' ((tag_lexical_address_for_var variable params env),
                                                  (run params env value))
    | ScmDef (ScmVar variable, value) ->  ScmDef' (VarFree (variable),
                                                   (run params env value))
    | ScmOr exprs -> ScmOr' (List.map (run params env) exprs)   
    | ScmLambdaSimple (params', expr') -> ScmLambdaSimple' (params',
                                                            (run params' ([params] @ env) expr'))
    | ScmLambdaOpt (params', opt, expr') -> ScmLambdaOpt' (params',
                                                           opt,
                                                           (run (params' @ [opt]) ([params] @ env) expr'))
    | ScmApplic (proc, args) -> ScmApplic' ((run params env proc),
                                            (List.map (run params env) args))
    | _ -> raise (X_error ("Failed in annotate_lexical_addresses function"))
  in
  run [] [] pe;;

let rec rdc_rac s = 
  match s with
  | [e] -> ([], e)
  | e :: s ->
      let (rdc, rac) = rdc_rac s
      in (e :: rdc, rac)
  | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)

let annotate_tail_calls pe =
  let rec run in_tail pe =
   match pe with
   | ScmConst' _ -> pe
   | ScmVar' _ -> pe
   | ScmIf' (test, dit, dif) -> let test' = run false test in
                                (match in_tail with
                                | true -> ScmIf' (test, (run true dit), (run true dif))
                                | false -> ScmIf' (test', (run false dit), (run false dif)))
   | ScmSeq' exprs -> let (exprs', expr) = rdc_rac exprs in
                      let exprs' = List.map (run false) exprs' in
                      (match in_tail with
                      | true -> ScmSeq' (exprs' @ [(run true expr)])
                      | false -> ScmSeq' (exprs' @ [(run false expr)]))
   | ScmSet' (variable, value) -> ScmSet' (variable, (run false value))
   | ScmDef' (variable, value) -> ScmDef' (variable, (run false value))
   | ScmOr' exprs -> let (exprs', expr) = rdc_rac exprs in
                     let exprs' = List.map (run false) exprs' in
                     (match in_tail with
                     | true -> ScmOr' (exprs' @ [(run true expr)])
                     | false -> ScmOr' (exprs' @ [(run false expr)]))
   | ScmLambdaSimple' (params, expr') -> ScmLambdaSimple' (params, (run true expr'))
   | ScmLambdaOpt' (params, opt, expr') -> ScmLambdaOpt' (params, opt, (run true expr'))
   | ScmApplic' (proc, args) -> let proc' = run false proc in
                                let args' = List.map (run false) args in
                                      (match in_tail with
                                      | true -> ScmApplicTP' (proc', args')
                                      | false -> ScmApplic' (proc', args'))                            
   | _ -> raise (X_error ("Failed in annotate_tail_calls function"))
  in 
  run false pe;;

  (* boxing *)

let copy_list lst = List.map (fun element -> element) lst;;

let combine_pairs =
  List.fold_left
    (fun (rs1, ws1) (rs2, ws2) -> (rs1 @ rs2, ws1 @ ws2))
      ([], []);;

let find_reads_and_writes =
  let rec run name expr params env =
    match expr with
    | ScmConst' _ -> ([], [])
    | ScmVar' variable -> (match variable with
                          | VarParam (name', _) -> if name' = name then ([(variable, env)], []) else ([],[])
                          | VarBound (name', _, _) -> if name' = name then ([(variable, env)], []) else ([],[])
                          | _ -> ([], []))
    | ScmBox' _ -> ([], [])
    | ScmBoxGet' _ -> ([], [])
    | ScmBoxSet' (_, value) -> run name value params env
    | ScmIf' (test, dit, dif) ->
      let (rs1, ws1) = run name test params env in
      let (rs2, ws2) = run name dit params env in
      let (rs3, ws3) = run name dif params env in
      (rs1 @ rs2 @ rs3, ws1 @ ws2 @ ws3)
    | ScmSeq' exprs ->
        combine_pairs
          (List.map
            (fun expr -> run name expr params env)
              exprs)
    | ScmSet' (variable, value) -> let (rs1, ws1) = run name value params env in
                                   let (rs2, ws2) = (match variable with
                                                    | VarParam (name', _) ->
                                                      if name' = name then ([], [(variable, env)]) else ([],[])
                                                    | VarBound (name', _, _) ->
                                                      if name' = name then ([], [(variable, env)]) else ([],[])
                                                    | _ -> ([], [])) in
                                   (rs1 @ rs2, ws1 @ ws2)      
    | ScmDef' (_, value) -> run name value params env
    | ScmOr' exprs ->
      combine_pairs
        (List.map
          (fun expr -> run name expr params env)
            exprs)
    | ScmLambdaSimple' (params_, expr_) ->
      if (List.mem name params_)
        then ([], [])
        else run name expr_ params_ ((copy_list params) :: env)
    | ScmLambdaOpt' (params_, opt, expr_) ->
      let params_ = params_ @ [opt] in
      if (List.mem name params_)
        then ([], [])
        else run name expr_ params_ ((copy_list params) :: env)
    | ScmApplic' (proc, args) ->
      let (rs1, ws1) = run name proc params env in
      let (rs2, ws2) =
        combine_pairs
          (List.map
            (fun arg -> run name arg params env)
              args) in
      (rs1 @ rs2, ws1 @ ws2)
    | ScmApplicTP' (proc, args) ->
        let (rs1, ws1) = run name proc params env in
        let (rs2, ws2) =
          combine_pairs
            (List.map
              (fun arg -> run name arg params env)
                args) in
        (rs1 @ rs2, ws1 @ ws2)
    in
    fun name expr params ->
    run name expr params [];;

let cross as' bs' =
  List.concat (List.map (fun ai ->
    List.map (fun bj -> (ai, bj)) bs')
      as');;

let should_box_var name expr params =
  let (reads, writes) = find_reads_and_writes name expr params in
  let rsXws = cross reads writes in
  let rec run = function
    | [] -> false
    | ((VarParam (_, _), _),
       (VarParam (_, _), _)) :: rest -> run rest
    | ((VarParam (_, _), _),
       (VarBound (_, _, _), _)) :: rest -> true
    | ((VarBound (_, _, _), _),
       (VarParam (_, _), _)) :: rest -> true
    | ((VarBound (_, _, _), env1),
       (VarBound (_, _, _), env2)) :: rest ->
        (not ((find_var_rib name env1) == (find_var_rib name env2)))
        || (run rest)
    | _ :: rest -> run rest
      and find_var_rib name = function
        | [] -> raise X_this_should_not_happen
        | rib :: env ->
          if (List.mem name rib)
          then rib
          else find_var_rib name env
    in run rsXws;; 


let replace_get_and_set name expr =
  let rec run expr =
    match expr with
    | ScmConst' _ -> expr
    | ScmVar' variable -> (match variable with
                          | VarParam (name', _) -> if (name' = name) then ScmBoxGet' variable else expr
                          | VarBound (name', _, _) -> if (name' = name) then ScmBoxGet' variable else expr
                          | _ -> expr)
    | ScmBox' _ -> expr
    | ScmBoxGet' _ -> expr
    | ScmBoxSet' (variable, value) -> ScmBoxSet' (variable, run value)
    | ScmIf' (test, dit, dif) -> ScmIf' (run test, run dit, run dif)
    | ScmSeq' exprs -> ScmSeq' (List.map run exprs)      
    | ScmSet' (variable, value) -> let value' = run value in
                                   (match variable with
                                   | VarParam (name', _) -> if (name' = name) then ScmBoxSet' (variable, value') else ScmSet' (variable, value')
                                   | VarBound (name', _, _) -> if (name' = name) then ScmBoxSet' (variable, value') else ScmSet' (variable, value')
                                   | _ -> ScmSet' (variable, value')) 
    | ScmDef' (variable, value) -> ScmDef' (variable, run value)
    | ScmOr' exprs -> ScmOr' (List.map run exprs) 
    | ScmLambdaSimple' (params, expr') -> if (List.mem name params)
                                            then expr
                                            else ScmLambdaSimple' (params, run expr')   
    | ScmLambdaOpt' (params, opt, expr') -> if ((List.mem name params) || (name = opt))
                                              then expr
                                              else ScmLambdaOpt' (params, opt, run expr')                             
    | ScmApplic' (proc, args) -> ScmApplic' (run proc, (List.map run args))
    | ScmApplicTP' (proc, args) -> ScmApplicTP' (run proc, (List.map run args))
  in
  run expr;;

let make_sets box_these params = 
  let rec run box_these params minor =
    match box_these, params with
    | [], _ -> []
    | hdb :: tlb, hdp :: tlp -> if hdb = hdp then
                                             let variable = VarParam (hdb, minor) in
                                             ScmSet' (variable, ScmBox' variable) :: run tlb tlp (minor + 1)
                                             else
                                             run box_these tlp (minor + 1)
    | _ -> raise (X_error ("Failed in add_sets function"))
    in
    run box_these params 0;;

let rec box_set expr =
  match expr with
  | ScmConst' _ -> expr
  | ScmVar' _ -> expr
  | ScmBox' _ -> expr
  | ScmBoxGet' _ -> expr
  | ScmBoxSet' (variable, value) -> ScmBoxSet' (variable, box_set value)
  | ScmIf' (test, dit, dif) -> ScmIf' (box_set test, box_set dit, box_set dif)
  | ScmSeq' exprs -> ScmSeq'(List.map box_set exprs)
  | ScmSet' (variable, value) -> ScmSet' (variable, box_set value)
  | ScmDef' (variable, value) -> ScmDef' (variable, box_set value)
  | ScmOr' exprs -> ScmOr' (List.map box_set exprs) 
  | ScmLambdaSimple' (params, expr') ->
    let box_these = List.filter (fun param -> should_box_var param expr' params) params in
    let new_body = List.fold_left (fun body name -> replace_get_and_set name body) expr' box_these in
    let new_sets = make_sets box_these params in
    let new_body =
      match box_these, new_body with
      | [], _ -> box_set new_body
      | _, ScmSeq' exprs -> ScmSeq' (new_sets @ (List.map box_set exprs))
      | _, _ -> ScmSeq'(new_sets @ [box_set new_body]) in
    ScmLambdaSimple' (params, new_body)
  | ScmLambdaOpt' (params, opt, expr') ->
    let params' = params @ [opt] in
    let box_these = List.filter (fun param -> should_box_var param expr' params') params' in
    let new_body = List.fold_left (fun body name -> replace_get_and_set name body) expr' box_these in
    let new_sets = make_sets box_these params' in
    let new_body =
      match box_these, new_body with
      | [], _ -> box_set new_body
      | _, ScmSeq' exprs -> ScmSeq' (new_sets @ (List.map box_set exprs))
      | _, _ -> ScmSeq'(new_sets @ [box_set new_body]) in
    ScmLambdaOpt' (params, opt, new_body)
  | ScmApplic' (proc, args) -> ScmApplic' (box_set proc, (List.map box_set args))
  | ScmApplicTP' (proc, args) -> ScmApplicTP' (box_set proc, (List.map box_set args))

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
