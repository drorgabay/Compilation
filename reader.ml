(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)

 module Reader : READER = struct  
open PC;;

type new_string =
  | StaticString of string
  | DynamicString of sexpr;;

let nt_optional_sign =
  let nt1 = pack (char '+') (fun _ -> 1) in                                                                                                                                              
  let nt2 = pack (char '-') (fun _ -> -1) in                                    
  let nt1 = disj nt1 nt2 in                                                 
  let nt1 = maybe nt1 in
  let nt1 = pack nt1 (function                                              
  | None -> 1
  | Some(c) -> c) in
  nt1;;

let rec merge_static strl =   
    match strl with
    | [] -> []
    | [DynamicString(x)] -> [DynamicString(x)]
    | [StaticString(x)] -> [StaticString(x)]
    | StaticString(x) :: StaticString(y) :: rest -> 
                        (merge_static ([StaticString(x^y)] @ rest))
    | StaticString(x) :: DynamicString(y) :: rest ->
                        [StaticString(x); DynamicString(y)] @ (merge_static rest)
    | DynamicString(x) :: StaticString(y) :: rest ->
                        [DynamicString(x); StaticString(y)] @ (merge_static rest)
    | DynamicString(x) :: DynamicString(y) :: rest ->
                        [DynamicString(x); DynamicString(y)] @ (merge_static rest);; 

let nt_digit =
    let nt1 = range '0' '9' in
    let nt1 = pack nt1 (let delta = int_of_char '0' in
    fun ch -> (int_of_char ch) - delta) in
    nt1;;

let nt_natural =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1 (fun digits -> List.fold_left
    (fun num digit -> 10 * num + digit)
    0
    digits) in
    nt1;;

let nt_zero =
  let nt1 = char '0' in
  let nt1 = pack nt1 (let delta = int_of_char '0' in
                      fun ch -> (int_of_char ch) - delta) in
  let nt1 = plus nt1 in
  let nt1 = pack nt1 (fun digits -> List.fold_left
  (fun num digit -> 10 * num + digit)
  0
  digits) in
  nt1;;

let make_maybe nt none_value =
    pack (maybe nt)
      (function
      | None -> none_value
      | Some(x) -> x);;

let unitify nt = pack nt (fun _ -> ());;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str

and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str

and nt_line_comment str =
  let nt_end = disj (unitify (char '\n')) (unitify nt_end_of_input) in
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end) in
  let nt1 = unitify nt1 in
  nt1 str

and nt_paired_comment str = 
  let nt1 = char '{' in 
  let nt2 = disj_list [unitify nt_char; unitify nt_string; nt_comment] in 
  let nt3 = disj nt2 (unitify (one_of "{}")) in 
  let nt3 = diff nt_any nt3 in
  let nt3 = disj (unitify nt3) nt2 in
  let nt2 = star nt3 in
  let nt3 = char '}' in
  let nt1 = unitify (caten nt1 (caten nt2 nt3)) in
  nt1 str

and nt_sexpr_comment str = 
  let nt_prefix_cmt = word "#;" in
  let nt_sexp = nt_sexpr in
  let nt_sexpr_cmt = caten nt_prefix_cmt nt_sexp in
  let nt_sexpr_cmt = unitify nt_sexpr_cmt in
  nt_sexpr_cmt str

and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str

and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str

and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1

and nt_int str =
  let nt1 = caten nt_optional_sign nt_natural in
  let nt1 = pack nt1
  (fun (s, n) ->
  if s = 1 then n else -n) in
  nt1 str
  
and nt_frac str =                                   
  let nt1 = nt_int in
  let nt2 = char '/' in
  let nt3 = diff nt_natural nt_zero in
  let nt1 = pack (caten (caten nt1 nt2) nt3) (fun ((a,b),c) -> ScmRational((a/(gcd (abs a) c),c/(gcd (abs a) c)))) in
  nt1 str

and nt_integer_part str =
  let nt1 = plus nt_digit in
  let nt1 = pack nt1 (fun digits -> List.fold_left
  (fun num digit ->
  10 * num + digit)
  0
  digits) in
  nt1 str

and nt_mantissa str =
  let nt1 = plus nt_digit in
  let nt1 = pack nt1 (fun digits ->
  List.fold_right
  (fun digit num ->
  ((float_of_int digit) +. num) /. 10.0) digits 0.0) in
  nt1 str
             
and nt_exponent str = 
  let nt1 = disj_list [
    (unitify (char_ci 'e'));
    (unitify (word "*10^"));
    (unitify (word "*10**"))] in
  let nt2 = nt_int in
  let nt1 = pack (caten nt1 nt2) (fun (_,i) -> Float.pow 10. (float_of_int i)) in
  nt1 str 

and nt_float str =
  let nt1 = nt_optional_sign in
  let nt2 = nt_integer_part in
  let nt3 = char '.' in
  let nt4 = make_maybe nt_mantissa 0.0 in 
  let nt5 = make_maybe nt_exponent 1.0 in
  let nt2 = caten nt2 (caten nt3 (caten nt4 nt5)) in
  let nt2 = pack nt2 (fun (i,(d,(m,e))) -> (((float_of_int i) +. m) *. e))  in
  let nt3 = char '.' in
  let nt4 = nt_mantissa in
  let nt5 = make_maybe nt_exponent 1.0 in
  let nt3 = caten nt3 (caten nt4 nt5) in
  let nt3 = pack nt3 (fun (_, (m, e)) -> m *. e) in
  let nt4 = caten nt_integer_part nt_exponent in
  let nt4 = pack nt4 (fun (i, e) -> ((float_of_int i) *. e)) in
  let nt2 = disj nt2 (disj nt3 nt4) in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (s , n) ->
  if s = 1 then ScmReal(n) else ScmReal(-.n)) in
  nt1 str

and nt_number str =             
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and nt_boolean str =                            
  let nt1 = pack (word_ci "#t") (fun _ -> true) in
  let nt2 = pack (word_ci "#f") (fun _ -> false) in
  let nt1 = disj nt1 nt2 in
  let nt1 = pack nt1 (fun b -> ScmBoolean b) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and nt_char_simple str =                   
  let nt1 = pack (const (fun ch -> ch > ' ')) (fun ch -> ch) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and make_named_char char_name ch = 
  let nt1 = pack (word_ci char_name) (fun chn -> ch) in
  nt1

and nt_char_named str =
  let nt1 = disj_list [(make_named_char "newline" '\n');
          (make_named_char "page" '\012');
          (make_named_char "return" '\r');
          (make_named_char "space" ' ');
          (make_named_char "tab" '\t');
          (make_named_char "nul" '\000')] in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and nt_char_hex str =                         
  let nt1 = char_ci 'x' in
  let nt2 = nt_digit in 
  let nt3 = range_ci 'a' 'f' in 
  let nt3 = pack nt3 (let delta = (int_of_char 'a') - 10 in
                      fun ch -> (int_of_char ch) - delta) in
  let nt2 = disj nt2 nt3 in
  let nt2 = plus nt2 in
  let nt2 = pack nt2 (fun digits ->
                      List.fold_left (fun a b -> 16 * a + b) 0 digits) in
  (* let nt2 = only_if nt2 (fun n -> n < 256) in *) 
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, n) -> (char_of_int n)) in
  let nt1 = not_followed_by nt1 nt_symbol_char in (* check *)
  nt1 str

and nt_char str =                             
  let nt1 = char '#' in
  let nt2 = char '\\' in
  let nt1 = caten nt1 nt2 in
  let nt2 = disj nt_char_named (disj nt_char_hex nt_char_simple) in
  let nt2 = pack (caten nt1 nt2) (fun (_,ch2) -> ScmChar ch2) in
  nt2 str

and nt_symbol_char str =                                      
    disj_list [
      (range '0' '9');
      (range_ci 'a' 'z');
      (one_of "!$^*-_=+<>?/:");
    ] str

and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str

and dynamic_format sexpr =
  ScmPair(ScmSymbol "format", ScmPair(ScmString "~a", ScmPair(sexpr, ScmNil)))

and nt_string_char str =
    disj_list [nt_string_literal_char; 
    nt_string_meta_char;
    nt_string_hex_char;
    nt_string_interpolated] 
    str

and nt_string_literal_char str =
  pack (const (fun ch -> ch != '\\' && ch != '"' && ch != '~')) (fun ch -> StaticString (String.make 1 ch)) str

and nt_string_meta_char str = 
  let nt1 = disj_list [
    pack (word "\\\\") (fun _ -> StaticString "\\");
    pack (word "\\\"") (fun _ -> StaticString "\"");
    pack (word "\\t") (fun _ -> StaticString "\t");
    pack (word "\\f") (fun _ -> StaticString "\012");
    pack (word "\\n") (fun _ -> StaticString "\n");
    pack (word "\\r") (fun _ -> StaticString "\r");
    pack (word "~~") (fun _ -> StaticString "~")] in
    nt1 str
    
and nt_string_hex_char str =
  let nt1 = char '\\' in
  let nt2 = plus nt_char_hex in
  let nt3 = char ';' in
  let nt1 = pack (caten (caten nt1 nt2) nt3) (fun ((_, lst), _) ->
                                                  StaticString (list_to_string lst)) in
  nt1 str

and nt_string_interpolated str =
  let nt1 = word "~{" in
  let nt2 = nt_sexpr in
  let nt3 = char '}' in
  let nt1 = pack (caten nt1 (caten nt2 nt3)) (fun (_,(sexp,_)) -> DynamicString sexp)  in
  nt1 str
  
and nt_string str = 
  let nt1 = char '"' in
  let nt2 = star nt_string_char in
  let nt3 = char '"' in
  let nt1 = pack (pack (caten (caten nt1 nt2) nt3) (fun ((_,strl),_) -> merge_static strl)) (fun strl -> 
  match strl with
  | [] -> ScmString ""
  | [StaticString(str)] -> ScmString str
  | [DynamicString(sexp)] -> dynamic_format sexp
  | compoundList ->
    let lst =
      (List.fold_right (fun a b ->
                        ScmPair((match a with
                        | StaticString(str) -> ScmString str
                        | DynamicString(sexp) -> dynamic_format sexp),b)) strl ScmNil) in
                        ScmPair(ScmSymbol "string-append", lst)) in
  nt1 str

and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str

and nt_list str = 
  let nt1 = char '(' in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmNil) in
  let nt3 = plus nt_sexpr in
  let nt4 = caten (char '.') (caten nt_sexpr (char ')')) in
  let nt4 = pack nt4 (fun (_, (sexpr,_)) -> sexpr) in
  let nt5 = pack (char ')') (fun _ -> ScmNil) in
  let nt4 = disj nt4 nt5 in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprl,sexpr) ->
                      List.fold_right (fun a b -> ScmPair(a,b)) sexprl sexpr) in
  let nt2 = disj nt2 nt3 in
  let nt1 = pack (caten nt1 nt2) (fun (_,list) -> list) in
  nt1 str

and nt_quoted_forms str = 
  disj_list [
    pack (caten (char (char_of_int 39)) nt_sexpr) (fun (ch,sexp) -> ScmPair(ScmSymbol "quote", ScmPair(sexp, ScmNil)));
    pack (caten (char '`') nt_sexpr) (fun (ch,sexp) -> ScmPair(ScmSymbol "quasiquote", ScmPair(sexp, ScmNil)));
    pack (caten (char ',') nt_sexpr) (fun (ch,sexp) -> ScmPair(ScmSymbol "unquote", ScmPair(sexp, ScmNil)));
    pack (caten (caten (char ',') (char '@')) nt_sexpr) (fun ((ch1,ch2),sexp) -> ScmPair(ScmSymbol "unquote-splicing", ScmPair(sexp, ScmNil)))] 
    str

and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
          nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

  end;;  (* end of struct Reader *) 

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  (*| ScmChar('\000') -> "#\\nul" mine! check with lior *)
  | ScmChar(ch) ->
    if (ch < ' ')
      then let n = int_of_char ch in
        Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
    Printf.sprintf "\"%s\""
      (String.concat ""
        (List.map
            (function
            | '\n' -> "\\n"
            | '\012' -> "\\f"
            | '\r' -> "\\r"
            | '\t' -> "\\t"
            | ch ->
                if (ch < ' ')
                then Printf.sprintf "\\x%x;" (int_of_char ch)
                else Printf.sprintf "%c" ch)
            (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
    Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
          ScmPair(sexpr, ScmNil)) ->
    Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
          ScmPair(sexpr, ScmNil)) ->
    Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
          ScmPair(sexpr, ScmNil)) ->
    Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
          ScmPair(sexpr, ScmNil)) ->
    Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
    string_of_sexpr' (string_of_sexpr car) cdr

and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
  let new_car_string =
      Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
    string_of_sexpr' new_car_string cddr
  | cdr ->
    let cdr_string = (string_of_sexpr cdr) in
    Printf.sprintf "(%s . %s)" car_string cdr_string;;
