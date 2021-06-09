#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let update_bounds prev_params bounds =
  let updated_bounds = List.map(fun (name, major, minor)->(name, 1+major, minor))bounds in
  let convert_bounds = List.map(fun (name, minor) -> (name, 0, minor)) prev_params in 
  let new_bounds = List.append convert_bounds updated_bounds in new_bounds
  ;;
  
let rec generate_params args idx =
  match args with
  | [] -> []
  | first :: tail ->
    let param = (first, idx) in
    let tail_params = generate_params tail (idx+1) in
    List.append [param] tail_params;;
    
(* let rec search_in_params name params =
  Some(List.find (fun var -> fst var = name) params);;
*)

let rec search_in_params name params =
    match params with
    | [] -> None
    | (v, mi) :: tail ->
        if v = name then Some(v, mi) else search_in_params name tail;;

(* let rec search_in_bounds name bounds =
  Some(List.find (fun (var, major, minor) -> var=name) bounds);; *)        

let rec search_in_bounds name bounds =
  match bounds with
  | [] -> None
  | (v, ma, mi) :: tail ->
      if v = name then Some((v, ma, mi)) else search_in_bounds name tail;;
  
let create_variable name params bounds =
  let p_value = search_in_params name params in
  match p_value with
  | Some((v, mi)) -> VarParam(v, mi)
  | _ ->
    ( let bound_val = search_in_bounds name bounds in 
        match bound_val with    
      | Some((v, ma, mi)) -> VarBound(v, ma, mi)
      | _ -> VarFree(name));;
  
let to_params args =
  let idx = 0 in
  let params = generate_params args idx in 
  params;;

let rec lex_add e params bounds =
  match e with
  | Var(name) ->
      let new_var = create_variable name params bounds in
      Var'(new_var)

  | Const(c) -> Const'(c)

  | If(test, dit, dif)->
      If'(lex_add test params bounds,
          lex_add dit params bounds,
          lex_add dif params bounds) 

  | Set(Var(name), expr) ->
      Set'(create_variable name params bounds,
          lex_add expr params bounds)  

  | Seq(exprs) -> 
      let e = List.map (fun(expr) -> lex_add expr params bounds) exprs in
      Seq'(e)   

  | Or(exprs) ->
      let e = List.map (fun(expr) -> lex_add expr params bounds) exprs in
      Or'(e)  

  | Def(Var(name), expr) ->
      Def'(create_variable name params bounds,
          lex_add expr params bounds)   
  
  | LambdaSimple(args, body) ->
      let new_body = create_new_body args body params bounds in
      LambdaSimple'(args, new_body)

  | LambdaOpt(args, arg_opt, body) -> 
      let total_args = List.append args [arg_opt] in
      let new_body = create_new_body total_args body params bounds in 
      LambdaOpt'(args, arg_opt, new_body)
  
  | Applic(rator, rands) ->
      let new_rator = lex_add rator params bounds in
      let new_rands = List.map (fun(rand) -> lex_add rand params bounds) rands in
      Applic'(new_rator, new_rands)

  | _ -> raise X_syntax_error
      
  
  and create_new_body args body params bounds=
    let updated_bounds = update_bounds params bounds in
    let new_params = to_params args in
    let new_body = lex_add body new_params updated_bounds in
    new_body;;
        
    
let annotate_lexical_addresses e = lex_add e [] []


let rec annotate_tale_call_rec e in_tp = match e with
      
  (* if in_tp -> dit and dif are in TP *)
  | If'(test, dit, dif) -> 
      If'(test, annotate_tale_call_rec dit in_tp, annotate_tale_call_rec dif in_tp)

  (* find the last expr. if in_tp -> last seq exprs is in TP *)
  | Seq'(seq) ->
      let new_seq = make_last_exps_TP seq in_tp in
      Seq'(new_seq)

  | Or'(lst) ->
      let new_lst = make_last_exps_TP lst in_tp in
      Or'(new_lst)

  (*the body of set!/def is never in TP *)
  | Set'(var, expr) -> Set'(var, annotate_tale_call_rec expr false)

  | Def'(var, expr) -> Def'(var, annotate_tale_call_rec expr false)

  (* every lambda has it's TC, therefor -> in_tp true *)
  | LambdaSimple'(args, body) ->
      LambdaSimple'(args, annotate_tale_call_rec body true)

  | LambdaOpt'(args, arg_opt, body) ->
      LambdaOpt'(args, arg_opt, annotate_tale_call_rec body true)

  (* if in_tp -> ApplicTP' *)
  | Applic'(rator, rands) ->
    let new_rator = annotate_tale_call_rec rator false in
    let new_rands = List.map (fun(rand) -> annotate_tale_call_rec rand false) rands in
    if in_tp
    then ApplicTP'(new_rator, new_rands)
    else Applic'(new_rator, new_rands)
  
  | e -> e
    
  and make_last_exps_TP s in_tp = 
  match s with
    | [] -> raise X_syntax_error
    | head :: tail -> 
    (match tail with
            | [] -> [annotate_tale_call_rec head in_tp]
            | _ ->  List.append 
                    [annotate_tale_call_rec head false]
                    (make_last_exps_TP tail in_tp)
    )
;;
                        

let annotate_tail_calls e =  annotate_tale_call_rec e false;;



(* params = vars list, args = new vars (strings) *)
let rec handle_args args params =
  match params with  
  | VarParam(name, minor) :: tail ->
      if(List.mem name args)
      then handle_args args tail
      else List.append [VarParam(name, minor)] (handle_args args tail)     
  | [] -> []
    | _-> raise X_syntax_error;;

let rec params_to_vars params i =
  match params with
  | param :: tail -> [VarParam(param, i)] @ (params_to_vars tail (i+1))
  | [] -> []

  (* funcion that handel lambdas and boxed params *)
let rec handle_lambda params body =
  match body with
  | Const'(x) -> Const'(x)

  | Var'(var) -> 
    (match var with
    | VarFree(x) -> Var'(var)
    | _ -> BoxGet'(var)
    )

  | BoxSet'(var, expr) ->  BoxSet'(var, handle_lambda params expr)
  
  | If'(test, dit, dif) ->
    If'(handle_lambda params test, handle_lambda params dit, handle_lambda params dif)

  | Or'(exprs) ->
    Or'(List.map (fun(expr) -> handle_lambda params expr) exprs)
  
  | Seq'(exprs) -> 
    Seq'(List.map (fun(expr) -> handle_lambda params expr) exprs)

  | Set'(var, expr) -> 
    (match var with
    | VarFree(x) -> Set'(VarFree(x) , (handle_lambda params expr))
    | _ -> BoxSet'(var, handle_lambda params expr)
    )

  | Def'(var, expr) -> Def'(var, handle_lambda params expr)

  | LambdaSimple'(args, _body) ->
    let new_args = handle_args args params in 
    LambdaSimple'(args, handle_lambda new_args _body)

  | LambdaOpt'(args, args_opt, _body) ->
    let total_args = params_to_vars (args@[args_opt]) 0 in
    let new_args = params @ total_args in 
    LambdaOpt'(args, args_opt, handle_lambda new_args _body)

  | Applic'(rator, rands) ->
    Applic'(handle_lambda params rator, List.map (fun(rand) -> handle_lambda params rand) rands)
  
  | ApplicTP'(rator, rands) ->
    ApplicTP'(handle_lambda params rator, List.map (fun(rand) -> handle_lambda params rand) rands)

  | e -> e ;;

  (* create set! Box exprs for all params *)
let update_body_with_set params body =
  match params with
  | [] -> handle_lambda params body
  | _ -> let set_params = List.map (fun(param) -> Set'(param, Box'(param))) params in
            (match body with
            | Seq'(lst) -> let _body = handle_lambda params body in
                            (match _body with
                            | Seq'(lst) -> Seq'(List.append set_params lst)
                            | _ -> _body)     
                            
            | _ -> 
                let _body = handle_lambda params body in            
                Seq'(List.append set_params [_body]));;
  

  (* main box function *)
let rec box_set_rec e =
  match e with
  | If'(test, dit, dif) ->
    If'(box_set_rec test, box_set_rec dit, box_set_rec dif)

  | Seq'(lst) -> 
    Seq'(List.map (fun(s) -> box_set_rec s) lst)

  | Set'(var, expr) -> 
    Set'(var,  box_set_rec expr)

  | Def'(var, expr) -> 
    Def'(var, box_set_rec expr)

  | Or'(lst) -> 
    Or'(List.map (fun(expr) -> box_set_rec expr) lst)

  | LambdaSimple'(params, body) ->   
    let params_list = params_to_vars params 0 in
    let body_with_set = update_body_with_set params_list body in
    LambdaSimple'(params, box_set_rec body_with_set)

  | LambdaOpt'(params, params_opt, body) ->
    let new_params = params @ [params_opt] in
    let params_list = params_to_vars new_params 0 in
    let body_with_set = update_body_with_set params_list body in
    LambdaOpt'(params, params_opt, box_set_rec body_with_set)

  | Applic'(rator, rands) ->
    let new_rands = List.map (fun(rand) -> box_set_rec rand) rands in
    Applic'(box_set_rec rator, new_rands)

  | ApplicTP'(rator, rands) ->
    let new_rands = List.map (fun(rand) -> box_set_rec rand) rands in
    ApplicTP'(box_set_rec rator, new_rands)

  | BoxSet'(var,expr) -> BoxSet'(var, box_set_rec expr)

  | e -> e;;
  
  ;;

let box_set e = box_set_rec e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  


       end;; (* struct Semantics *)

        (* open Semantics;;
        List.map run_semantics 
        [Def (Var "x", Const (Sexpr (Number (Fraction (5, 1)))));
        Def (Var "x", Const (Sexpr (Number (Fraction (3, 1))))); Var "x"];; *)