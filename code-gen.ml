#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  let global_index = ref 0;;

  let make_label name =
    (global_index := !global_index + 1);
    Printf.sprintf "%s%d" name !global_index;;

  let rec rdc_rac s = 
    match s with
    | [e] -> ([], e)
    | e :: s ->
        let (rdc, rac) = rdc_rac s
        in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;

  let extend_const const =
    let rec run const =
      match const with
      | ScmNil -> [] 
      | ScmSymbol str -> [ScmString str] @ [const]
      | ScmPair (car, cdr) -> (run car) @ (run cdr) @ [const]
      | ScmVector exprs -> let convert_to_pair = List.fold_right (fun expr acc ->
                                                                    ScmPair(expr, acc)) exprs ScmNil in
                           (run convert_to_pair) @ [const] 

      | _ -> [const]
    in run const;;

  let rec remove_dup_in_consts_lst consts_lst const =
    match consts_lst with
    | [] -> [] 
    | const' :: tl ->
      if (sexpr_eq const' const)
        then let rec run rest const =
              match rest with
              | [] -> []
              | const' :: tl ->
                if (sexpr_eq const' const)
                  then (run tl const)
                  else [const'] @ (run tl const) in [const'] @ (run tl const)
      else [const'] @ (remove_dup_in_consts_lst tl const)

  let find_offset_for_vector_exprs tbl exprs =
    let rec run exprs =
      match exprs with
      | [] -> ""
      | expr :: [] -> let ptr = List.find (fun (const, (_, _)) -> sexpr_eq const expr) tbl in
                      (Printf.sprintf "const_tbl+%d" ((fun (_, (offset, _)) -> offset) ptr))
      | expr :: rest -> let ptr = List.find (fun (const, (_, _)) -> sexpr_eq const expr) tbl in
                        (Printf.sprintf "const_tbl+%d, " ((fun (_, (offset, _)) -> offset) ptr)) ^ run rest
    in run exprs

  let make_consts_tbl_for_all_asts lst =
    let rec run lst offset tbl = 
      match lst with
      | [] -> tbl
      | sexpr :: rest ->
        match sexpr with
        | ScmVector exprs -> let offsets = find_offset_for_vector_exprs tbl exprs in
                             run rest (offset + 9 + (8 * (List.length exprs))) (tbl @ [(sexpr, (offset, (Printf.sprintf "MAKE_LITERAL_VECTOR %s" offsets)))])
        | ScmChar ch -> run rest (offset + 2) (tbl @ [(sexpr, (offset, (Printf.sprintf "MAKE_LITERAL_CHAR(%s)" (string_of_int (Char.code ch)))))]) (* check if need the bracs *)
        | ScmNumber (ScmRational (num, dem)) -> run rest (offset + 17) (tbl @ [(sexpr, (offset, Printf.sprintf "MAKE_LITERAL_RATIONAL(%d,%d)" num dem))])
        | ScmNumber (ScmReal num) -> run rest (offset + 9) (tbl @ [(sexpr, (offset, (Printf.sprintf "MAKE_LITERAL_FLOAT(%f)" num)))])
        | ScmString str -> run rest (offset + 9 + (String.length str)) (tbl @ [(sexpr, (offset, (Printf.sprintf "MAKE_LITERAL_STRING \"%s\"" str)))]) (* check if need the bracs *)
        | ScmSymbol str -> let ptr = List.find (fun (const, (_, _)) -> sexpr_eq const (ScmString str)) tbl in
                           let ptr = (fun (_, (offset, _)) -> offset) ptr in
                           run rest (offset + 9) (tbl @ [(sexpr, (offset, (Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" ptr)))])
        | ScmPair (car, cdr) ->
          let car' = List.find (fun (const, (_, _)) -> sexpr_eq const car) tbl in
          let car' = (fun (_, (offset, _)) -> offset) car' in
          let cdr' = List.find (fun (const, (_, _)) -> sexpr_eq const cdr) tbl in
          let cdr' = (fun (_, (offset, _)) -> offset) cdr' in
          run rest (offset + 17) (tbl @ [(sexpr, (offset, (Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d)" car' cdr')))])
        | _ -> run rest offset tbl
    in run lst 6 [(ScmVoid, (0, "db T_VOID"));
                  (ScmNil, (1, "db T_NIL"));
                  (ScmBoolean(false), (2, "db T_BOOL, 0"));
                  (ScmBoolean(true), (4, "db T_BOOL, 1"))];;

  let make_consts_lst_for_ast ast =
    let rec run ast =
      match ast with
      | ScmConst' sexpr -> [sexpr]
      | ScmVar' _ -> []
      | ScmBox' _ -> []
      | ScmBoxGet' _ -> []
      | ScmBoxSet' (_, value) -> run value
      | ScmIf' (test, dit, dif) -> (run test) @ (run dit) @ (run dif)
      | ScmSeq' exprs -> List.fold_left (fun a b -> a @ (run b)) [] exprs
      | ScmSet' (variable, value) -> (run (ScmVar' variable)) @ run value
      | ScmDef' (variable, value) -> (run (ScmVar' variable)) @ run value
      | ScmOr' exprs -> List.fold_left (fun acc expr -> acc @ (run expr)) [] exprs
      | ScmLambdaSimple' (params, expr') -> run expr'
      | ScmLambdaOpt' (params, opt, expr') -> run expr'
      | ScmApplic' (proc, args) -> (run proc) @ (List.fold_left (fun acc arg -> acc @ (run arg)) [] args)
      | ScmApplicTP' (proc, args) -> (run proc) @ (List.fold_left (fun acc arg -> acc @ (run arg)) [] args)
    in
    run ast;;

  let rec remove_dup_in_fvars_lst fvars_lst fvar =
    match fvars_lst with
    | [] -> [] 
    | fvar' :: tl ->
      if (fvar' = fvar)
        then let rec run rest const =
              match rest with
              | [] -> []
              | fvar' :: tl ->
                if (fvar' = fvar)
                  then (run tl fvar)
                  else [fvar'] @ (run tl fvar) in [fvar'] @ (run tl fvar)
      else [fvar'] @ (remove_dup_in_fvars_lst tl fvar)

  let make_fvar_lst_for_ast asts =
    let rec run asts =
      match asts with
      | ScmConst' _ -> []
      | ScmVar' variable -> (match variable with
                            | VarFree name' -> [name']
                            | _ -> [])
      | ScmBox' _ -> []
      | ScmBoxGet' _ -> []
      | ScmBoxSet' (_, value) -> run value
      | ScmIf' (test, dit, dif) -> (run test) @ (run dit) @ (run dif)
      | ScmSeq' exprs -> List.fold_left (fun a b -> a @ (run b)) [] exprs
      | ScmSet' (variable, value) -> (run (ScmVar' variable)) @ (run value)
      | ScmDef' (variable, value) -> (run (ScmVar' variable)) @ (run value)
      | ScmOr' exprs -> List.fold_left (fun acc expr -> acc @ (run expr)) [] exprs
      | ScmLambdaSimple' (params, expr') -> run expr'
      | ScmLambdaOpt' (params, opt, expr') -> run expr'
      | ScmApplic' (proc, args) -> (run proc) @ (List.fold_left (fun acc arg -> acc @ (run arg)) [] args)
      | ScmApplicTP' (proc, args) -> (run proc) @ (List.fold_left (fun acc arg -> acc @ (run arg)) [] args)
    in
    run asts;;
    
  let make_fvars_tbl_for_all_asts fvars_lst =
    let rec run fvars_lst index tbl =
      match fvars_lst with
      | [] -> tbl
      | fvar :: rest -> run rest (index + 1) (tbl @ [(fvar, (index * 8))])
    in run fvars_lst 32 [("boolean?", 0*8); ("flonum?", 1*8); ("rational?", 2*8);
                          ("null?", 3*8); ("char?", 4*8); ("string?", 5*8);
                          ("procedure?", 6*8); ("symbol?", 7*8); ("pair?", 8*8);
                          ("string-length", 9*8); ("string-ref", 10*8); ("string-set!", 11*8);
                          ("make-string", 12*8); ("symbol->string", 13*8);
                          ("char->integer", 14*8); ("integer->char", 15*8); ("exact->inexact", 16*8);
                          ("eq?", 17*8);
                          ("+", 18*8); ("*", 19*8); ("/", 20*8); ("=", 21*8); ("<", 22*8);
                          ("numerator", 23*8); ("denominator", 24*8); ("gcd", 25*8); ("cons", 26*8); ("car", 27*8); ("cdr", 28*8);
                          ("set-car!", 29*8); ("set-cdr!", 30*8); ("apply", 31*8)]
  
  let make_consts_tbl asts =
    let consts_lst_of_all_asts = List.fold_left (fun acc ast ->
                                                  acc @ make_consts_lst_for_ast ast) [] asts in
    let consts_lst_of_all_asts = List.fold_left (fun lst const ->
                                                  remove_dup_in_consts_lst lst const)
                                                  consts_lst_of_all_asts consts_lst_of_all_asts in
    let consts_lst_of_all_asts = List.fold_left (fun acc const ->
                                                  acc @ extend_const const) [] consts_lst_of_all_asts in
    let consts_lst_of_all_asts = List.fold_left (fun lst const ->
                                                  remove_dup_in_consts_lst lst const)
                                                  consts_lst_of_all_asts consts_lst_of_all_asts in
    make_consts_tbl_for_all_asts consts_lst_of_all_asts

  let make_fvars_tbl asts =
    let fvars_lst_of_all_asts = List.fold_left (fun acc ast ->
                                                  acc @ make_fvar_lst_for_ast ast) [] asts in
    let fvars_lst_of_all_asts = List.fold_left (fun lst fvar ->
                                                  remove_dup_in_fvars_lst lst fvar)
                                                  fvars_lst_of_all_asts fvars_lst_of_all_asts in
    make_fvars_tbl_for_all_asts fvars_lst_of_all_asts

  
  let generate consts fvars e = 
    let rec run e depth =
      match e with
      | ScmConst' const -> let const_row = List.find (fun (const', (_, _)) -> sexpr_eq const' const) consts in
                           let offset = (fun (_, (off, _)) -> off) const_row in
                           Printf.sprintf
                           "\tmov rax, const_tbl+%d\n"
                           offset
      | ScmVar' variable -> (match variable with
                            | VarParam (name, minor) -> Printf.sprintf
                                                        "\tmov rax, qword [rbp + (4 + %d) * WORD_SIZE]\n"
                                                        minor
                            | VarBound (name, major, minor) -> Printf.sprintf
                                                               "\tmov rax, qword [rbp + 2 * WORD_SIZE]\n\t
                                                               mov rax, qword [rax + %d * WORD_SIZE]\n\t
                                                               mov rax, qword [rax + %d * WORD_SIZE]\n"
                                                               major minor
                            | VarFree name -> let fvar_row = List.find (fun (fvar, _) -> fvar = name) fvars in
                                              let index = (fun (_, index') -> index') fvar_row in
                                              Printf.sprintf
                                              "\tmov rax, [fvar_tbl+%d]\n" 
                                              index)
      | ScmBox' variable -> (Printf.sprintf "%s" (run (ScmVar' variable) depth)) ^
                            "\tmov rbx, 1\n" ^
                            "\tlea rbx, [rbx * WORD_SIZE]\n" ^
                            "\tMALLOC rbx, rbx\n" ^
                            "\tmov [rbx], rax\n" ^
                            "\tmov rax, rbx\n"
      | ScmBoxGet' variable -> Printf.sprintf
                               "%s\tmov rax, qword [rax]\n"
                               (run (ScmVar' variable) depth)
      | ScmBoxSet' (variable, value) -> Printf.sprintf
                                        "%s\tpush rax\n\t%s\tpop qword [rax]\n\tmov rax, SOB_VOID_ADDRESS\n"
                                        (run value depth) (run (ScmVar' variable) depth)
      | ScmIf' (test, dit, dif) -> let else_label = make_label "Lelse" in
                                   let exit_label = make_label "Lexit" in
                                   Printf.sprintf
                                   "%s\tcmp rax, SOB_FALSE_ADDRESS\n\tje %s\n%s\tjmp %s\n\t%s\n%s\t%s\n"
                                   (run test depth) else_label (run dit depth) exit_label (else_label ^ ":") (run dif depth) (exit_label ^ ":")
      | ScmSeq' exprs -> List.fold_left (fun acc expr ->
                                          Printf.sprintf
                                          "%s%s"
                                          acc (run expr depth)) "" exprs
      | ScmSet' (variable, value) -> (match variable with
                                     | VarParam (_, minor) -> Printf.sprintf
                                                                 "%s\tmov qword [rbp + (4 + %d) * WORD_SIZE], rax\n\tmov rax, SOB_VOID_ADDRESS\n"
                                                                 (run value depth) minor
                                     | VarBound (_, minor, major) -> Printf.sprintf
                                                                        "%s\tmov rbx, qword [rbp + 2 * WORD_SIZE]\n\t
                                                                        mov rbx, qword [rbx + 8 * %d]\n\tmov qword [rbx + 8 * %d], rax\n\t
                                                                        mov rax, SOB_VOID_ADDRESS\n"
                                                                        (run value depth) major minor
                                     | VarFree name -> let fvar_row = List.find (fun (fvar, _) -> fvar = name) fvars in
                                                       let index = (fun (_, index') -> index') fvar_row in
                                                       Printf.sprintf
                                                       "%s\tmov [fvar_tbl+%d], rax\n\tmov rax, SOB_VOID_ADDRESS\n"
                                                       (run value depth)  index)
      | ScmDef' (variable, value) -> (match variable with
                                     | VarFree name -> let fvar_row = List.find (fun (fvar, _) -> fvar = name) fvars in
                                                       let index = (fun (_, index') -> index') fvar_row in
                                                       Printf.sprintf
                                                       "%s\tmov [fvar_tbl+%d], rax\n\tmov rax, SOB_VOID_ADDRESS\n"
                                                       (run value depth) index
                                     | _ -> raise (X_error ("Failed in generate function- not a VarFree in ScmDef' expr'"))) 
      | ScmOr' exprs -> let exit_label = make_label "Lexit" in
                        let (exprs', last_expr) = rdc_rac exprs in
                        let exprs' = List.map (fun expr ->
                                                Printf.sprintf
                                                "%s\tcmp rax, SOB_FALSE_ADDRESS\n\tjne %s\n"
                                                (run expr depth) exit_label) exprs' in
                        let exprs' = List.fold_left (fun acc expr ->
                                                      Printf.sprintf
                                                      "%s%s"
                                                      acc expr) "" exprs' in
                        let last_expr = Printf.sprintf
                                        "%s\t%s\n"
                                        (run last_expr depth) (exit_label ^ ":") in
                        Printf.sprintf
                        "%s%s"
                        exprs' last_expr
      | ScmLambdaSimple' (params, expr') ->
          let ext_env_not_needed_label = make_label "Lext_env_not_needed" in
          let ext_env_needed_label = make_label "Lext_env_needed" in
          let copy_params_label = make_label "Lcopy_params" in
          let loop_label = make_label "Lloop" in
          let make_closure_with_ext_env_label = make_label "Lmake_closure_with_ext_env" in
          let code_label = make_label "Lcode" in
          let cont_label = make_label "Lcont" in
          (Printf.sprintf "\tmov rcx, %d\n" depth) ^ (* rcx = |Env| *)
          "\tcmp rcx, 0\n" ^ (* if |Env| = 0 we dont need to the extend the env *)
          (Printf.sprintf "\tje %s\n" ext_env_not_needed_label) ^
          (Printf.sprintf "\tMALLOC rbx, ((%d + 1) * WORD_SIZE)\n" depth) ^ (* rbx points to ExtEnv with size |Env| + 1 *)
          "\tpush rbx\n" ^ (* save rbx *)
          "\tmov rdx, [rbp + 2 * WORD_SIZE]\n" ^ (* rdx points to Env *)
          (Printf.sprintf "\t%s\n" (ext_env_needed_label ^ ":")) ^
          "\tadd rbx, WORD_SIZE\n" ^ (* this loop performs ExtEnv[j] = Env[i] where j start from 1 and i starts from 0 *)
          "\tmov rax, [rdx]\n" ^
          "\tmov [rbx], rax\n" ^ 
          "\tadd rdx, WORD_SIZE\n" ^
          "\tdec rcx\n" ^ 
          "\tcmp rcx, 0\n" ^ 
          (Printf.sprintf "\tjne %s\n" ext_env_needed_label) ^
          (Printf.sprintf "\t%s\n" (copy_params_label ^ ":")) ^
          "\tmov rax, qword [rbp + 3 * WORD_SIZE]\n" ^ (* rax = num of params in stack *)
          "\tmov rcx, rax\n" ^
          "\tlea rax, [rax * WORD_SIZE]\n" ^ 
          "\tMALLOC rax, rax\n" ^ (* rax points to a vector that will store the params *)
          "\tpush rax\n" ^ (* save rax *)
          "\tlea rdx, [rbp + 4 * WORD_SIZE]\n" ^ (* rdx points to the first param in stack *)
          (Printf.sprintf "\t%s\n" (loop_label ^ ":")) ^ (* this loop performs rax = params *)
          "\tcmp rcx, 0\n" ^
          (Printf.sprintf "\tje %s\n" make_closure_with_ext_env_label) ^
          "\tmov r9, [rdx]\n" ^ 
          "\tmov [rax], r9\n" ^ 
          "\tadd rdx, WORD_SIZE\n" ^ 
          "\tadd rax, WORD_SIZE\n" ^ 
          "\tdec rcx\n" ^ 
          (Printf.sprintf "\tjmp %s\n" loop_label) ^
          (Printf.sprintf "\t%s\n" (make_closure_with_ext_env_label ^ ":")) ^
          "\tpop rax\n" ^
          "\tpop rbx\n" ^
          "\tmov [rbx], rax\n" ^ (* ExtEnv[0] = params*)
          (Printf.sprintf "\tMAKE_CLOSURE(rax, rbx, %s)\n" code_label) ^
          (Printf.sprintf "\tjmp %s\n" cont_label) ^
          (Printf.sprintf "\t%s\n" (ext_env_not_needed_label ^ ":")) ^
          (Printf.sprintf "\tMAKE_CLOSURE(rax, SOB_NIL_ADDRESS, %s)\n" code_label) ^
          (Printf.sprintf "\tjmp %s\n" cont_label) ^
          (Printf.sprintf "\t%s\n" (code_label ^ ":")) ^
          "\tpush rbp\n" ^
          "\tmov rbp, rsp\n" ^
          (Printf.sprintf "%s" (run expr' (depth + 1))) ^
          "\tleave\n" ^
          "\tret\n" ^
          (Printf.sprintf "\t%s\n" (cont_label ^ ":"))

      | ScmLambdaOpt' (params, opt, expr') ->
          let ext_env_not_needed_label = make_label "Lext_env_not_needed" in
          let ext_env_needed_label = make_label "Lext_env_needed" in
          let copy_params_label = make_label "Lcopy_params" in
          let continue_copy_params_label = make_label "Lcontinue_copy_params" in
          let make_closure_with_ext_env_label = make_label "Lmake_closure_with_ext_env" in
          let code_label = make_label "Lcode" in
          let cont_label = make_label "Lcont" in
          let opt_is_not_null_label = make_label "Lopt_is_not_null" in
          let push_null_label = make_label "Lpush_null" in
          let end_fix_label = make_label "Lend_fix" in
          let convert_opt_label = make_label "Lconvert_opt" in
          let convert_opt_to_a_list_with_one_element_label = make_label "Lconvert_opt_to_a_list_with_one_element" in
          let shift_label = make_label "Lshift_label" in
          let end_shift_label = make_label "Lend_shift" in
          let end_iter_label = make_label "Lend_iter" in
          (Printf.sprintf "\tmov rcx, %d\n" depth) ^ (* rcx = |Env| *)
          "\tcmp rcx, 0\n" ^ (* if |Env| = 0 we dont need to the extend the env *)
          (Printf.sprintf "\tje %s\n" ext_env_not_needed_label) ^
          (Printf.sprintf "\tMALLOC rbx, ((%d + 1) * WORD_SIZE)\n" depth) ^ (* rbx points to ExtEnv with size |Env| + 1 *)
          "\tpush rbx\n" ^ (* save rbx *)
          "\tmov rdx, [rbp + 2 * WORD_SIZE]\n" ^ (* rdx points to Env *)
          (Printf.sprintf "\t%s\n" (ext_env_needed_label ^ ":")) ^
          "\tadd rbx, WORD_SIZE\n" ^ (* this loop performs ExtEnv[j] = Env[i] where j start from 1 and i starts from 0 *)
          "\tmov rax, [rdx]\n" ^
          "\tmov [rbx], rax\n" ^ 
          "\tadd rdx, WORD_SIZE\n" ^
          "\tdec rcx\n" ^ 
          "\tcmp rcx, 0\n" ^ 
          (Printf.sprintf "\tjne %s\n" ext_env_needed_label) ^
          (Printf.sprintf "\t%s\n" (copy_params_label ^ ":")) ^
          "\tmov rax, qword [rbp + 3 * WORD_SIZE]\n" ^ (* rax = num of params in stack *)
          "\tmov rcx, rax\n" ^
          "\tlea rax, [rax * WORD_SIZE]\n" ^ 
          "\tMALLOC rax, rax\n" ^ (* rax points to a vector that will store the params *)
          "\tpush rax\n" ^ (* save rax *)
          "\tlea rdx, [rbp + 4 * WORD_SIZE]\n" ^ (* rdx points to the first param in stack *)
          (Printf.sprintf "\t%s\n" (continue_copy_params_label ^ ":")) ^ (* this loop performs rax = params *)
          "\tcmp rcx, 0\n" ^
          (Printf.sprintf "\tje %s\n" make_closure_with_ext_env_label) ^
          "\tmov r9, [rdx]\n" ^ 
          "\tmov [rax], r9\n" ^ 
          "\tadd rdx, WORD_SIZE\n" ^ 
          "\tadd rax, WORD_SIZE\n" ^ 
          "\tdec rcx\n" ^ 
          (Printf.sprintf "\tjmp %s\n" continue_copy_params_label) ^
          (Printf.sprintf "\t%s\n" (make_closure_with_ext_env_label ^ ":")) ^
          "\tpop rax\n" ^
          "\tpop rbx\n" ^
          "\tmov [rbx], rax\n" ^ (* ExtEnv[0] = params*)
          (Printf.sprintf "\tMAKE_CLOSURE(rax, rbx, %s)\n" code_label) ^
          (Printf.sprintf "\tjmp %s\n" cont_label) ^
          (Printf.sprintf "\t%s\n" (ext_env_not_needed_label ^ ":")) ^
          (Printf.sprintf "\tMAKE_CLOSURE(rax, SOB_NIL_ADDRESS, %s)\n" code_label) ^
          (Printf.sprintf "\tjmp %s\n" cont_label) ^
          (Printf.sprintf "\t%s\n" (code_label ^ ":")) ^
          (* FIX STACK!!! *)
          "\tmov rcx, qword [rsp + 2 * WORD_SIZE]\n" ^  (* rcx = num of params in the stack *)                         
          (Printf.sprintf "\tcmp rcx, %d\n" (List.length params)) ^ (* cmp rcx with num of mandatory params *)          
          (Printf.sprintf "\tjne %s\n" opt_is_not_null_label) ^  (* if rcx != mandatory_num then opt is not an empty list *) 
          (* FIX THE STACK WHEN OPT IS NULL *)                                                      
          (Printf.sprintf "\tmov qword [rsp + 2 * WORD_SIZE], %d\n" ((List.length params) + 1)) ^ (* change num of params in the stack *)
          "\tsub rsp, WORD_SIZE\n" ^ (* in that case, opt = null and we need to make room for null in the stack *)
          "\tmov rsi, rsp\n" ^ 
          "\tmov rdi, rsp\n" ^
          (Printf.sprintf "\tmov rcx, %d\n" (3 + (List.length params))) ^ (* rcx used as a counter *)
          (Printf.sprintf "\t%s\n" (push_null_label ^ ":")) ^
          "\tadd rsi, WORD_SIZE\n" ^
          "\tmov r10, [rsi]\n" ^
          "\tmov [rdi], r10\n" ^
          "\tadd rdi, WORD_SIZE\n" ^
          "\tdec rcx\n" ^
          "\tcmp rcx, 0\n" ^
          (Printf.sprintf "\tjne %s\n" push_null_label) ^  
          "\tmov qword [rdi], SOB_NIL_ADDRESS\n" ^ (* at the end of the loop, rdi points to to place we should push null *)
          (Printf.sprintf "jmp %s\n" end_fix_label) ^
          (* FIX STACK WHEN OPT IS NOT NULL: 2 CASES *)
          (Printf.sprintf "\t%s\n" (opt_is_not_null_label ^ ":")) ^ 
          "\tmov r9, SOB_NIL_ADDRESS\n" ^ (* r9 used as the list we will push to the stack *)
          (Printf.sprintf "\tsub rcx, %d\n" (List.length params)) ^ (* rcx = num of params in the stack - mandatory_num *)
          "\tcmp rcx, 1\n" ^
          (Printf.sprintf "\tje %s\n" convert_opt_to_a_list_with_one_element_label) ^
          (Printf.sprintf "\t%s\n" (convert_opt_label ^ ":")) ^
          (Printf.sprintf "\tmov rbx, [rsp + (3 + (rcx + %d)) * WORD_SIZE]\n" ((List.length params) - 1)) ^ (* start with the last element in the list *)                    
          "\tMAKE_PAIR(rdx, rbx, r9)\n" ^
          "\tmov r9, rdx\n" ^
          "\tdec rcx\n" ^
          "\tcmp rcx, 0\n" ^
          (Printf.sprintf "\tjne %s\n" convert_opt_label) ^
          (* CASE 2: SIZE OF OPT > 1 *)
          "\tmov rbx, qword [rsp + 2 * WORD_SIZE]\n" ^
          "\tmov r13, 1\n" ^
          "\tneg r13\n" ^
          (Printf.sprintf "\tsub rbx, %d\n" (1 + (List.length params))) ^
          "\tinc rbx\n" ^
          "\tmov r10, qword [rsp + 2 * WORD_SIZE]\n" ^
          (Printf.sprintf "\t%s\n" (end_shift_label ^ ":")) ^
          "\tinc r13\n" ^
          "\tsub rbx, 1\n" ^
          "\tcmp rbx, 0\n" ^
          (Printf.sprintf "\tje %s\n" end_iter_label) ^
          "\tmov rcx, r10\n" ^
          "\tsub rcx, r13\n" ^
          "\tinc rcx\n" ^
          "\tmov rdi, rsp\n" ^
          "\tadd rdi, WORD_SIZE\n" ^
          "\tmov rax, [rsp]\n" ^
          "\tadd rsp, WORD_SIZE\n" ^
          (Printf.sprintf "\t%s\n" (shift_label ^ ":")) ^
          "\tcmp rcx, 0\n" ^
          (Printf.sprintf "\tje %s\n" end_shift_label) ^
          "\tmov r12, [rdi]\n" ^
          "\tmov [rdi], rax\n" ^
          "\tmov rax, r12\n" ^
          "\tadd rdi, WORD_SIZE\n" ^
          "\tdec rcx\n" ^
          (Printf.sprintf "\tjmp %s\n" shift_label) ^
          (Printf.sprintf "\t%s\n" (end_iter_label ^ ":")) ^
          "\tmov [rdi], r9\n" ^
          (Printf.sprintf "\tmov qword [rsp + 2 * WORD_SIZE], %d\n" ((List.length params) + 1)) ^
          (Printf.sprintf "\tjmp %s\n" end_fix_label) ^
          (* CASE 1: SIZE OF OPT = 1 *)
          (Printf.sprintf "\t%s\n" (convert_opt_to_a_list_with_one_element_label ^ ":")) ^
          (Printf.sprintf "\tmov rbx, [rsp + (3 + (rcx + %d)) * WORD_SIZE]\n" ((List.length params) - 1)) ^
          "\tMAKE_PAIR(rax, rbx, r9)\n" ^
          (Printf.sprintf "\tmov [rsp + (3 + (rcx + %d)) * WORD_SIZE], rax\n" ((List.length params) - 1)) ^
          (Printf.sprintf "\t%s\n" (end_fix_label ^ ":")) ^
          "\tpush rbp\n" ^
          "\tmov rbp, rsp\n" ^
          (Printf.sprintf "%s" (run expr' (depth + 1))) ^
          "\tleave\n" ^
          "\tret\n" ^
          (Printf.sprintf "\t%s\n" (cont_label ^ ":"))

      | ScmApplic' (proc, args) -> let args' = List.fold_right (fun arg acc ->
                                                                Printf.sprintf
                                                                "%s%s\tpush rax\n"
                                                                acc (run arg depth)) args "" in
                                   let proc' = (Printf.sprintf "\tpush %d\n" (List.length args)) ^
                                               (Printf.sprintf "%s" (run proc depth)) ^
                                               "\tCLOSURE_ENV rbx, rax\n" ^
                                               "\tpush rbx\n" ^
                                               "\tCLOSURE_CODE rbx, rax\n" ^
                                               "\tcall rbx\n" ^
                                               "\tadd rsp, WORD_SIZE\n" ^
                                               "\tpop rbx\n" ^
                                               "\tshl rbx, 3\n" ^
                                               "\tadd rsp, rbx\n" in
                                  args' ^ proc'
      | ScmApplicTP' (proc, args) -> let args' = List.fold_right (fun arg acc ->
                                                                  Printf.sprintf
                                                                  "%s%s\tpush rax\n"
                                                                  acc (run arg depth)) args "" in
                                     let proc' = (Printf.sprintf "\tpush %d\n" (List.length args)) ^
                                                 (Printf.sprintf "%s" (run proc depth)) ^
                                                 "\tCLOSURE_ENV rcx, rax\n" ^
                                                 "\tpush rcx\n" ^
                                                 "\tCLOSURE_CODE rcx, rax\n" ^
                                                 "\tpush qword [rbp + WORD_SIZE]\n" ^ (* old ret address *)
                                                 "\tpush qword [rbp]\n" ^
                                                 (Printf.sprintf "\tSHIFT_FRAME %d\n" ((List.length args) + 4)) ^
                                                 "\tpop rbp\n" ^
                                                 "\tjmp rcx\n" in
                                     args' ^ proc' 
                                      
    in run e 0;;

end;; 

