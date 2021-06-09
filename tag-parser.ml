#use "reader.ml";;
open Reader;;
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER   raise X_syntax_error *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

   let disjAST nt1 nt2 =
    fun s ->
    try (nt1 s)
    with X_syntax_error -> (nt2 s);;
  
  let nt_noneAST _ = raise X_syntax_error;;
    
  let disj_list_AST nts = List.fold_right disjAST nts nt_noneAST;;

(* work on the tag parser starts here *)
let rec tag_parser s = disj_list_AST[mit_dif_exp;lambda_exp;const;if_exp;or_exp;define_exp;set_exp;begin_exp;applic_exp;
let_expen;let_kleen_expen;and_wrraper;quasiquote_expen_wrraper;cond_exp;pset_exp;let_rec_expen_wrraper] s 

and const s = match s with
| Nil -> Const(Sexpr(Nil)) (* ask *)
| Bool(e) -> Const(Sexpr(Bool(e)))
| Char(e)-> Const(Sexpr(Char(e)))
| Number(e)->Const(Sexpr(Number(e)))
| String(e)->Const(Sexpr(String(e)))
| Pair(Symbol("quote"),Pair(x,Nil))->Const(Sexpr(x))
| Symbol(e) when  not(List.mem e reserved_word_list) ->  Var(e)  (** do i need to pase "a" *)
|_-> raise  X_syntax_error

and if_exp s = match s with
| Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil))))-> If(tag_parser test, tag_parser dit, tag_parser dif)
| Pair(Symbol("if"), Pair(test,Pair(dit, Nil)))-> If(tag_parser test, tag_parser dit ,Const(Void))
|_-> raise  X_syntax_error

and applic_exp s = match s with
| Pair(sexp,sexplist) -> Applic (tag_parser sexp, List.map (fun a-> (tag_parser a)) (sexprs_to_list sexplist)) 
| _ -> raise X_syntax_error

and or_exp s = match s with
| Pair(Symbol ("or"), Nil) ->  Const (Sexpr(Bool false))
| Pair(Symbol ("or"), Pair(e,Nil)) ->tag_parser e 
| Pair(Symbol ("or"), or_list) ->Or(List.map (fun a-> (tag_parser a)) (sexprs_to_list or_list) )
|_ -> raise X_syntax_error

and define_exp s = match s with 
| Pair (Symbol ("define"),Pair (var,Pair(e,Nil))) -> Def (tag_parser var,tag_parser e) 
|_ ->raise X_syntax_error

and set_exp s = match s with
| Pair (Symbol ("set!"), Pair(var,Pair(e,Nil))) ->  Set (tag_parser var,tag_parser e)
|_ ->raise X_syntax_error

and begin_exp s = match s with
| Pair(Symbol ("begin"), Nil) ->  Const (Void)
| Pair(Symbol ("begin"), Pair(e,Nil)) ->tag_parser e 
| Pair(Symbol ("begin"), begin_list) ->Seq (List.map (fun a-> (tag_parser a)) (flot_begin_exp begin_list) )
|_ -> raise X_syntax_error

and flot_begin_exp s = match s with 
| Pair(Pair(Symbol"begin",s1),s2)-> (flot_begin_exp s1) @ (flot_begin_exp s2)
| Pair(s1,s2)-> s1 :: (flot_begin_exp s2)
| Nil -> []
| s1 -> [s1]

and lambda_exp s = match s with
| Pair(Symbol "lambda",Pair(ribs,body)) -> (match ribs with
| Symbol(e) ->  LambdaOpt ([],e,seq_exp (sexprs_to_list body) )
| _ -> if(not (is_improper ribs)) 
       then LambdaSimple(param ribs,seq_exp (sexprs_to_list body))
       else  LambdaOpt(get_param_improper_list ribs,get_last_element ribs, seq_exp ( sexprs_to_list body)))
|_-> raise  X_syntax_error

and param s= match s with 
|Nil -> []
|Pair(Symbol(e),rest_list)-> [e] @ (param rest_list)
|_ -> raise X_syntax_error

and get_last_element s = match s with
| Pair(_,Symbol(e))-> e
| Pair(_,e)-> get_last_element e
| _->raise X_syntax_error
(*  not   handl a a a   *)
and get_param_improper_list s = match s with
|Pair(Symbol(e),Symbol(_))-> [e]
|Pair(Symbol(e),rest_list)-> [e] @ (get_param_improper_list rest_list)
|_ -> raise X_syntax_error

and seq_exp s = 
 match (List.length s) with
| 0 ->  Const(Void)
| 1 ->  tag_parser (List.hd s)
| _ ->  Seq (seq_helper (List.map (fun a-> (tag_parser a)) s))

and seq_helper list_expr = match list_expr with
| []->[]
| Seq(something) :: tail -> something @ (seq_helper tail)
| something:: tail  -> [something] @ (seq_helper tail)

and sexprs_to_list s= match s with
| Pair(s1,s2)-> s1 :: (sexprs_to_list s2)
| Nil -> []
| s1 -> [s1]

and is_improper s = match s with
| Nil-> false
| Pair(s1,s2)-> is_improper(s2)
| _ -> true 


(*  Macro-expansions *)   
and let_expen s = match s with 
| Pair (Symbol "let", sexp_let) -> (match sexp_let with
   |Pair(ribs,body) -> tag_parser (Pair (Pair (Symbol "lambda",Pair (left_side_ribs ribs,body)),right_side_ribs ribs))
   |_-> raise  X_syntax_error)

|_ -> raise X_syntax_error

and right_side_ribs s = match s with 
| Nil -> Nil
| Pair(Pair(Symbol(a),Pair(sexp,Nil)),e) -> Pair(sexp,(right_side_ribs e))
| _ -> raise X_syntax_error 
and left_side_ribs s = match s with 
| Nil -> Nil
| Pair(Pair(a,Pair(b,Nil)),c) -> Pair(a,left_side_ribs c)
| _ -> raise X_syntax_error

and let_kleen_expen s= match s with 
| Pair (Symbol "let*", sexp_let) -> (match sexp_let with 
| Pair(ribs,body) -> 
  (match ribs with
    |  Nil-> tag_parser(Pair((Symbol "let"), sexp_let))   
    |  Pair(_,Nil) -> tag_parser(Pair((Symbol "let"), sexp_let))
    |  Pair(rib,rest_ribs)->  
          let_kleen_build_expen  (sexp_var_of_ribs_to_exp ribs) (sexp_value_of_ribs_to_exp ribs) (seq_exp (sexprs_to_list body)) 
    |  _ -> raise X_syntax_error)
|_ -> raise X_syntax_error)
|_ -> raise X_syntax_error

and sexp_var_of_ribs_to_exp s = match s with
|Nil-> []
| Pair(Pair(Symbol(var), Pair(value, Nil)),rest_ribs) -> [var] @ (sexp_var_of_ribs_to_exp rest_ribs)
| _ -> raise X_syntax_error

and sexp_value_of_ribs_to_exp s = match s with
|Nil->[]
|Pair(Pair(Symbol(var), Pair(value, Nil)), rest_ribs) -> [tag_parser value] @ (sexp_value_of_ribs_to_exp rest_ribs)
|_ -> raise X_syntax_error

and let_kleen_build_expen vars values body = match vars, values with
| [var], [value] -> Applic(LambdaSimple([var], body), [value])
| var :: rest_var, value :: rest_value -> Applic(LambdaSimple([var], let_kleen_build_expen rest_var rest_value body ),[value])
| _ -> raise X_syntax_error


and and_wrraper s = match s with
| Pair(Symbol "and", sexpr) -> tag_parser (and_expen_rec sexpr)
| _ -> raise X_syntax_error

and and_expen_rec = function
| Nil -> Bool(true)
| Pair(bool_val,Nil) -> bool_val
| Pair(bool_val,bool_tail) ->  Pair(Symbol("if"), Pair(bool_val, Pair(and_expen_rec bool_tail ,Pair(Bool(false),Nil))))
| _ -> raise X_syntax_error

and mit_dif_exp s = match s with
| Pair(Symbol("define"), Pair(Pair (Symbol var,arglist),body)) -> tag_parser (mit_def_rec var arglist body)
| _ -> raise X_syntax_error

and mit_def_rec var arglist body = 
Pair(Symbol("define"), Pair(Symbol(var), Pair(Pair(Symbol("lambda"),Pair(arglist,body)), Nil))) 


and args_helper arg_exp = match arg_exp with
| Var(x) -> [x]
| Seq(lst)-> list_arg lst 
| _ -> raise X_syntax_error


and list_arg list_args = match list_args with
| []->[]
| Var(x)::tail -> [x]@(list_arg tail)
|_-> raise  X_syntax_error
 
and cond_exp s = match s with
| Pair (Symbol "cond" ,ribs) -> cond_ribs ribs
| _ -> raise X_syntax_error

and cond_ribs ribs =  match ribs with
| Nil -> Const(Void)
|Pair(first_rib,rest_ribs) -> 
  (match first_rib with 
    |Pair (Symbol("else"),sexpr) -> seq_exp (sexprs_to_list sexpr)
    |Pair(test,Pair(Symbol("=>"),Pair(then_sexper, Nil))) -> 
      let parm1 = Pair(Symbol("value"), Pair(test, Nil)) in
      let parm2 = Pair(Symbol("f"),  Pair(Pair(Symbol("lambda"),Pair(Nil,Pair(then_sexper,Nil))),Nil)) in 
      let parm3 = Pair(Symbol("rest"),  Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(Pair(Symbol("cond"), rest_ribs), Nil))), Nil)) in
      let body = Pair (Symbol "if", Pair (Symbol "value", Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), Pair (Pair (Symbol "rest", Nil), Nil)))) in
      let params = Pair(parm1,Pair(parm2,Pair(parm3,Nil))) in 
      tag_parser (Pair(Symbol("let"),Pair(params,Pair(body,Nil))))

    |Pair(test,then_sexper) -> If(tag_parser test,seq_exp (sexprs_to_list then_sexper),cond_ribs rest_ribs)
    | _ -> raise X_syntax_error)
 |_-> raise  X_syntax_error

and quasiquote_expen_wrraper s = match s with
| Pair(Symbol "quasiquote", Pair(sexpr, Nil)) -> tag_parser (quasiquote_expen_rec sexpr)
| _ -> raise X_syntax_error

and quasiquote_expen_rec s = match s with
| Nil ->  Pair(Symbol("quote"), Pair(Nil, Nil))
| Symbol(blabla) -> Pair(Symbol("quote"), Pair(Symbol(blabla), Nil))
| Pair(Symbol("unquote"), Pair(sexp, Nil)) -> sexp
| Pair(Symbol("unquote-splicing"), sexp) -> raise X_syntax_error
| Pair(a,b) -> quasiquote_helper s quasiquote_expen_rec
| x -> x

and quasiquote_helper touple expander = match touple with
| Pair(Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)), b) -> Pair(Symbol("append"), Pair(sexpr, Pair(expander b, Nil))) 
(* | Pair(a ,Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil))) -> Pair(Symbol("cons"), Pair(expander a , Pair(sexpr, Nil))) *)
| Pair(a, b) -> Pair(Symbol "cons",Pair(expander a, Pair(expander b,Nil)))
(* Pair(Symbol "cons" , [quasiquote_expen_rec a, quasiquote_expen_rec b]) *)
| _ -> raise X_syntax_error

and pset_exp s =
match s with 
| Pair(Symbol("pset!"),binding) -> pset_binding_exp binding 
| _-> raise X_syntax_error

and pset_binding_exp s = 
let left_string_arr_side = sexprs_to_list_srting (left_side_ribs s) in
let right_side = sexprs_to_list (right_side_ribs s) in
let upper_left = (List.map  (fun a-> String.uppercase_ascii a)  left_string_arr_side)  in
let new_binding = make_new_binding upper_left right_side in
let body = make_body left_string_arr_side upper_left in
let let_exp = Pair(Symbol("let"),Pair(new_binding,body)) in  
tag_parser  let_exp


and make_body lower_left upper_right = match  lower_left,upper_right  with
| [],[] -> Nil
| first_left::tail_left , first_right::tail_right -> Pair(Pair(Symbol("set!"),Pair(Symbol(first_left),Pair(Symbol(first_right),Nil))),make_body tail_left tail_right )
| _ -> raise X_syntax_error

and make_new_binding left right = match  left,right  with
| [],[] -> Nil
| first_left::tail_left , first_right::tail_right -> Pair(Pair(Symbol(first_left),Pair(first_right,Nil)),make_new_binding tail_left tail_right )
| _ -> raise X_syntax_error

and sexprs_to_list_srting  s= match s with
| Pair(Symbol(s1),s2)-> s1 :: (sexprs_to_list_srting s2)
| Nil -> []
|_ -> raise X_syntax_error

and let_rec_split_ribs = function
  | Nil -> Nil
  | Pair(Pair(f,expr),tail) -> Pair(Pair(f ,Pair(Pair(Symbol "quote",Pair(Symbol "whatever", Nil)),Nil)), let_rec_split_ribs tail)
  | _ -> raise X_syntax_error

and let_rec_set ribs body = 
  match ribs with
  | Nil -> body
  | Pair(Pair(f,Pair(expr,Nil)), tail) -> Pair(Pair(Symbol "set!", Pair(f, Pair(expr,Nil))),(let_rec_set tail body))
  | _ -> raise X_syntax_error

and let_rec_expen_wrraper s = match s with 
  | Pair (Symbol "letrec", sexp_let) -> tag_parser (let_rec_expen sexp_let)
  | _ -> raise X_syntax_error

and let_rec_expen s = match s with
  | Pair(Nil, body) -> (Pair(Symbol("let"), Pair(Nil, body)) )
  | Pair(ribs, body) -> let params = let_rec_split_ribs ribs in
                        let new_body = let_rec_set ribs (Pair(Pair(Symbol("let"), (Pair (Nil, body))),Nil)) in
                        Pair(Symbol("let"), Pair(params, new_body))
  | _ -> raise X_syntax_error;;




let tag_parse_expressions sexpr = List.map (tag_parser) sexpr;;

end;; (* struct Tag_Parser *)


(* open Tag_Parser;;
let s = "
(define rocket (char->integer '\\r))
(define frily (char->integer '\\f))

(not (> frily rocket))
";;
(Tag_Parser.tag_parse_expressions
                  (Reader.read_sexprs s)) *)
(* [Pair (Symbol "begin",
Pair (Number (Fraction (1, 1)),
 Pair (Number (Fraction (2, 1)),
  Pair
   (Pair (Symbol "begin",
     Pair (Number (Fraction (4, 1)), Pair (Number (Fraction (5, 1)), Nil))),
   Pair (Pair (Symbol "begin", Pair (Number (Fraction (3, 1)), Nil)), Nil)))))] *)