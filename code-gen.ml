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
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

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
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct


  let remove_dup pred lst set =
    let rec remove_dup_rec lst set =
    match lst with
    | [] -> set    
    | hd :: tail -> if (List.exists (fun(element) -> pred hd element) set) 
                  then (remove_dup_rec tail set) 
                  else (remove_dup_rec tail (set @ [hd])) in
    remove_dup_rec lst set;; 

  let make_consts_set lst =
    let const_eq v1 v2 =
      match v1, v2 with
      | Const'(Sexpr x), Const'(Sexpr y) -> sexpr_eq x y
      | _ -> false in
    remove_dup const_eq lst [];;

  let consts_to_sexprs const_set =
    let rec const_to_sexpr const =
      match const with 
      | Const'(Void) :: tail -> const_to_sexpr tail
      | Const'(Sexpr(sexpr)) :: tail -> 
      (expand_sexpr sexpr) @ 
      (const_to_sexpr tail)
      | [] -> [] 
      | _ -> raise X_this_should_not_happen

    and expand_sexpr sexpr =
      match sexpr with
      | Pair(car, cdr) -> (expand_sexpr car) @ (expand_sexpr cdr) @ [Sexpr(sexpr)]
      | Symbol(a) -> [Sexpr(String (a)) ; Sexpr(sexpr)]
      | Number(num) -> [Sexpr(Number(num))]
      | Char(c) -> [Sexpr(Char(c))]
      | String(s) -> [Sexpr(String(s))]
      | _ -> [] in

    const_to_sexpr const_set ;;
  let make_sexpr_set lst =
    let _sexpr_eq s1 s2 =
      match s1, s2 with
      | Sexpr(Bool(b1)), Sexpr(Bool(b2)) -> b1 = b2
      | Sexpr(Nil), Sexpr(Nil) -> true
      | Sexpr(Number(Float f1)), Sexpr(Number(Float f2)) -> abs_float(f1 -. f2) < 0.001
      | Sexpr(Number(Fraction (n1, d1))), Sexpr(Number(Fraction (n2, d2))) -> n1 = n2 && d1 = d2
      | Sexpr(Char(c1)), Sexpr(Char(c2)) -> c1 = c2
      | Sexpr(String(s1)), Sexpr(String(s2)) -> s1 = s2
      | Sexpr(Symbol(s1)), Sexpr(Symbol(s2)) -> s1 = s2
      | Sexpr(Pair(car1, cdr1)), Sexpr(Pair(car2, cdr2)) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
      | _ -> false in
    remove_dup _sexpr_eq lst [];;

  let add_offsets sexprs_list =
    let rec add_offset lst offset =
      match lst with
      | [] -> []
      | Void :: tail -> [(Void, offset)] @ add_offset tail (offset+1)
      | Sexpr(Bool x) :: tail -> [(Sexpr(Bool x), offset)] @ add_offset tail (offset+2)
      | Sexpr(Nil) :: tail -> [(Sexpr(Nil), offset)] @ add_offset tail (offset+1)
      | Sexpr(Number(Fraction (x,y))) :: tail -> [(Sexpr(Number(Fraction (x,y))), offset)] @ add_offset tail (offset+17)
      | Sexpr(Number(Float x)) :: tail -> [(Sexpr(Number(Float x)), offset)] @ add_offset tail (offset+9)
      | Sexpr(Char c) :: tail -> [(Sexpr(Char c), offset)] @ add_offset tail (offset+2)
      | Sexpr(String s) :: tail -> [(Sexpr(String s), offset)] @ add_offset tail (offset+ 9 + (String.length s))
      | Sexpr(Symbol s) :: tail -> [(Sexpr(Symbol s), offset)] @ add_offset tail (offset+9)
      | Sexpr(Pair(car, cdr)) :: tail -> [(Sexpr(Pair(car,cdr)), offset)] @ add_offset tail (offset+17) in
      add_offset sexprs_list 0;;
      

    let tupels_to_tripels tupels =
      let find_offset const tupels  = 
        List.assoc const tupels in
      let rec tupel_to_tripel lst = 
        match lst with
        | [] -> []
        | (Void, ofs) :: tail -> [(Void, (ofs, "db T_VOID"))] @ tupel_to_tripel tail 
        | (Sexpr(Bool false), ofs) :: tail -> [(Sexpr(Bool false), (ofs, "db T_BOOL, 0"))] @ tupel_to_tripel tail
        | (Sexpr(Bool true), ofs) :: tail -> [(Sexpr(Bool true), (ofs, "db T_BOOL, 1"))] @ tupel_to_tripel tail
        | (Sexpr(Nil), ofs) :: tail -> [(Sexpr(Nil), (ofs, "db T_NIL"))] @ tupel_to_tripel tail
        | (Sexpr(Number(Fraction (x,y))), ofs) :: tail -> [(Sexpr(Number(Fraction (x, y))), (ofs, "MAKE_LITERAL_RATIONAL ("^(string_of_int x)^" ,"^(string_of_int y)^")"))] @ tupel_to_tripel tail
        | (Sexpr(Number(Float x)), ofs) :: tail -> [(Sexpr(Number(Float x)), (ofs, "MAKE_LITERAL_FLOAT ("^(string_of_float x)^")"))] @ tupel_to_tripel tail
        | (Sexpr(Char c), ofs) :: tail -> [(Sexpr(Char c), (ofs, "MAKE_LITERAL_CHAR ("^ (string_of_int (int_of_char c))^ ")"))] @ tupel_to_tripel tail
        | (Sexpr(String s), ofs) :: tail -> [(Sexpr(String s), (ofs, "MAKE_LITERAL_STRING \""^s^"\" "))] @ tupel_to_tripel tail
        | (Sexpr(Symbol s), ofs) :: tail -> [(Sexpr(Symbol s), (ofs, "MAKE_LITERAL_SYMBOL (const_tbl+" ^ (string_of_int (find_offset (Sexpr(String s)) tupels))^")"))] @ tupel_to_tripel tail
        | (Sexpr(Pair(car, cdr)), ofs) :: tail -> [(Sexpr(Pair(car, cdr)), 
                                                    (ofs, "MAKE_LITERAL_PAIR (const_tbl+" ^ 
                                                          (string_of_int (find_offset (Sexpr(car)) tupels)) ^ " , const_tbl+" ^ 
                                                          (string_of_int (find_offset (Sexpr(cdr)) tupels))^ ")"))] @ tupel_to_tripel tail in
        (* | _ -> X_this_should_not_happen in *)


    tupel_to_tripel tupels;;

  let consts_tbl_maker  asts = 
    let rec find_const expr' = 
      match expr' with
      | Const'(x) ->  [Const'(x)]
      | Var'(x) -> []
      | If'(test, dit, dif) -> (find_const test) @ (find_const dit) @ (find_const dif)
      | Box'(x) -> []
      | BoxSet'(v, e) -> (find_const e)
      | BoxGet'(v) -> []
      | Seq'(lst) -> (List.fold_left List.append [] (List.map find_const lst))
      | Set'(v, e) -> (find_const e)
      | Def'(v, e) -> (find_const e)
      | Or'(lst) -> (List.fold_left List.append [] (List.map find_const lst))
      | LambdaSimple'(args, body) -> (find_const body)
      | LambdaOpt'(args, args_opt ,body) -> (find_const body)
      | Applic'(rator, rands) -> (find_const rator) @ (List.fold_left List.append [] (List.map find_const rands))
      | ApplicTP'(rator, rands) -> (find_const rator) @ (List.fold_left List.append [] (List.map find_const rands)) in

    let consts_set = make_consts_set(List.fold_left List.append [] (List.map find_const asts)) in
    let sexpr_set = [Void; Sexpr(Nil); Sexpr(Bool false); Sexpr(Bool true)] @ make_sexpr_set (consts_to_sexprs consts_set) in
    tupels_to_tripels (add_offsets sexpr_set)  

      ;;

  let rec make_fvar_set lst set  =
    let varfree_eq v1 v2 =
      match v1, v2 with
      | VarFree(x), VarFree(y) -> String.equal x y
      | _ -> false in
    remove_dup varfree_eq lst set;;

  let rec vars_to_pairs vars pairs i =
    match vars with
    | VarFree(x) :: tail -> [x, i] @ (vars_to_pairs tail pairs (i+8))
    | [] -> pairs
    | _ -> raise X_this_should_not_happen;;

  let fvar_tbl_maker asts =
    let rec find_fvars expr' =
    match expr' with
    | Const'(x) -> []
    | Var'(VarFree(x)) -> [VarFree(x)]
    | Var'(x) -> []    
    | If'(test, dit, dif) -> (find_fvars test) @ (find_fvars dit) @ (find_fvars dif)                                  
    | Box'(x) -> []
    | BoxSet'(v, e) -> (find_fvars e)
    | BoxGet'(v) -> []
    | Seq'(lst) -> (List.fold_left List.append [] (List.map find_fvars lst))   
    | Set'(VarFree(x), e) -> [VarFree(x)] @ (find_fvars e)
    | Set'(v, e) -> (find_fvars e)
    | Def'(VarFree(x), e) -> [VarFree(x)] @ (find_fvars e)
    | Def'(v, e) -> (find_fvars e)
    | Or'(lst) -> (List.fold_left List.append [] (List.map find_fvars lst))   
    | LambdaSimple'(args, body) -> (find_fvars body)
    | LambdaOpt'(args, args_opt, body) -> (find_fvars body)
    | Applic'(rator, rands) -> (find_fvars rator) @ (List.fold_left List.append [] (List.map find_fvars rands))  
    | ApplicTP'(rator, rands) -> (find_fvars rator) @ (List.fold_left List.append [] (List.map find_fvars rands))  in 
    
    let freeVarsList = List.flatten (List.map find_fvars asts) in
    let freeVarSet = make_fvar_set freeVarsList [] in
    
    ["boolean?", 0; "flonum?", 8; "rational?", 16;
    "pair?", 24; "null?", 32; "char?", 40; "string?", 48;
    "procedure?", 56; "symbol?", 64;
    (* String procedures *)
    "string-length", 72; "string-ref", 80; "string-set!", 88;
    "make-string", 96; "symbol->string", 104;
    (* Type conversions *)
    "char->integer", 112; "integer->char", 120; "exact->inexact", 128;
    (* Identity test *)
    "eq?", 136;
    (* Arithmetic ops *)
    "+", 144; "*", 152; "/", 160; "=", 168; "<", 176;
    (* Additional rational numebr ops *)
    "numerator", 184; "denominator", 192; "gcd", 200; 
    (* our functions*) 
    "apply", 208; "car", 216; "cons", 224; "cdr", 232; "set-car!", 240; "set-cdr!", 248] @ vars_to_pairs freeVarSet [] 256
    ;; 

  let make_consts_tbl asts = consts_tbl_maker asts ;;
  
  let make_fvars_tbl asts = fvar_tbl_maker asts ;;

  let if_counter = ref 0;;
  let or_counter = ref 0;;
  let lambda_counter = ref 0;;
  let inc_and_get_counter counter = 
    counter := (!counter+1);
    !counter;;    

  let generate consts fvars e =     
    let rec code_gen env_size_counter e =
      let code_gen_same_counter = code_gen env_size_counter in
      match e with 
      | Const'(c) -> 
        let gen_const c = 
          let (i, s) = List.assoc c consts in
          "mov rax, const_tbl+" ^ string_of_int i ^ "\n" in
        gen_const c
      | Var'(VarParam(name, minor)) -> 
        "mov rax, qword [rbp + 8 * (4 + " ^ (string_of_int minor) ^ ")]" ^ " \n"
      | Set'((VarParam(name, minor)), e) ->
        code_gen_same_counter e ^ 
        "mov qword [rbp + 8 * (4 +" ^ (string_of_int minor) ^ ")], rax
         mov rax, SOB_VOID_ADDRESS" ^ "\n"
      | Var'(VarBound(name, major, minor)) -> 
        "mov rax, qword [rbp + 8 * 2]
         mov rax, qword [rax + 8 * " ^ (string_of_int major) ^ "]
         mov rax, qword [rax + 8 * " ^ (string_of_int minor) ^ "]\n"
      | Set'((VarBound(name, major, minor)), e) ->
        code_gen_same_counter e ^ 
        "mov rbx, qword [rbp + 8 * 2]
         mov rbx, qword [rbx + 8 * "^ (string_of_int major) ^ "]
         mov qword [rbx + 8 * "^ (string_of_int minor) ^ "], rax
         mov rax, SOB_VOID_ADDRESS \n"
      | Var'(VarFree(s)) -> 
        "mov rax, qword [fvar_tbl + " ^ (string_of_int (List.assoc s fvars)) ^ "]\n"
      | Set'(VarFree(s), e) ->
        code_gen_same_counter e ^
        "mov qword [fvar_tbl + " ^ (string_of_int (List.assoc s fvars)) ^ "], rax
         mov rax, SOB_VOID_ADDRESS\n"
      | Seq'(lst) -> 
        String.concat "" (List.map code_gen_same_counter lst)   
      | If'(test, dit, dif) ->
        let str_counter = string_of_int (inc_and_get_counter if_counter) in
        code_gen_same_counter test ^
        "cmp rax, SOB_FALSE_ADDRESS\n" ^
        "je Lelse" ^ str_counter ^ "\n" ^
        code_gen_same_counter dit ^
        "jmp IfExit" ^ str_counter ^
        "\nLelse" ^ str_counter ^ ":\n" ^
        code_gen_same_counter dif ^ "\n" ^
        "IfExit" ^ str_counter ^ ":\n"
      | Or'(lst) ->  
        let str_counter = string_of_int(inc_and_get_counter or_counter) in
        let jump =
        "cmp rax, SOB_FALSE_ADDRESS
         jne OrExit" ^ str_counter ^"\n" in
        let concatend = String.concat jump (List.map code_gen_same_counter lst) in
        concatend ^ "OrExit" ^ str_counter ^ ":\n"

      | Box'(v) ->
        (code_gen_same_counter (Var'(v))) ^ 
        "MALLOC rbx,WORD_SIZE
        mov [rbx], rax
        mov rax, rbx\n"
      | BoxGet'(VarFree(s)) ->
        code_gen_same_counter (Var'(VarFree(s)))
      | BoxGet'(v) ->
        (code_gen_same_counter (Var'(v))) 
        ^ "mov rax, qword [rax]\n" 
      | BoxSet'(v, e) ->
        (code_gen_same_counter e) ^
        "push rax \n"^
        (code_gen_same_counter(Var'(v))) ^
        "pop qword [rax]
         mov rax, SOB_VOID_ADDRESS\n"
      | Def'(VarFree(s), e) ->
        code_gen_same_counter e ^
        "mov qword [fvar_tbl + " ^ (string_of_int (List.assoc s fvars)) ^ "], rax
        mov rax, SOB_VOID_ADDRESS"
      | LambdaSimple'(args, body) ->
        let env_size_counter_str = (string_of_int (env_size_counter+1)) in
        let num_of_args_str = string_of_int (List.length args) in
        let lambda_counter_str = string_of_int(inc_and_get_counter lambda_counter) in
        let lambda_body =
          "lambda_code_"^lambda_counter_str ^":
           enter 0,0           
           mov rax, "^num_of_args_str ^"    ; rax <- num of args known from the expr'
           cmp rax, PARAM_COUNT              ; PARAM_COUNT = qword [rbp + 3*8]
           "^ code_gen (env_size_counter+1) body ^
           "leave
           ret
           " 
           in
        

         "mov r13, "^env_size_counter_str^
         "\nMALLOC rbx, ("^env_size_counter_str^" * WORD_SIZE) 			; rbx <- vector of size extEnv*WS
         
         EXT_ENV              ; rbx <- extEnv\n
         MAKE_CLOSURE (rax, rbx, lambda_code_"^lambda_counter_str^")
         jmp end_lambda_body_"^lambda_counter_str ^ "\n"
         ^lambda_body^"
         end_lambda_body_"^lambda_counter_str ^ ":\n"

      | Applic'(proc, args)->
        let generateArgs = (List.fold_left(fun acc curr -> "" ^ (code_gen_same_counter curr)^"push rax \n"^ acc)"" args) in

        let n = (string_of_int (List.length args)) in
        
        let procVal = (code_gen_same_counter proc) ^ "
          push qword [rax + TYPE_SIZE]
          call [rax + TYPE_SIZE + WORD_SIZE]

          add rsp, 8*1      ; pop env
          pop rbx           ; pop arg count
          inc rbx           ; for the magic
          shl rbx, 3        ; rbx = rbx * 8
          add rsp, rbx      ; pop args\n" in

        "push SOB_NIL_ADDRESS\n" ^ generateArgs ^ "push "^n ^ "\n" ^ procVal

      | ApplicTP'(proc, args)->
        let generateArgs = (List.fold_left(fun acc curr -> "" ^ (code_gen_same_counter curr)^"push rax \n"^ acc)"" args) in

        let n = (string_of_int (List.length args)) in
        
        
        let procVal = (code_gen_same_counter proc) ^ "
          mov rsi, rax
          CLOSURE_ENV rcx, rsi
          push rcx

          push qword [rbp + 8 * 1] ; old ret addr
          mov rdx,[rbp]             ; save the old rbp

          mov rdi, "^n^" 
          add rdi,5

          mov rax, [rbp+8*3] 
          add rax, 5     
          mov r11, -8
          mov rbx, rax
          mov rcx,1
          
        .rep:
         cmp rdi,rcx
         je .endRep
  	     dec rax
         
         mov r13, [rbp+r11]
         add r11, -8
         mov qword [rbp+WORD_SIZE*rax], r13
         inc rcx
         jmp .rep
       .endRep:
         dec rdi
         sub rbx, rdi
         mov rdi, rdx
         shl rbx, 3
         mov rsp,rbp                
         add rsp, rbx
  
         mov rbp,rdi         
         jmp [rsi + TYPE_SIZE + WORD_SIZE]
         " in

        ";----------------------ApplicTP-------------------
        push SOB_NIL_ADDRESS\n" ^ generateArgs ^"push qword " ^ n ^ "\n" ^ procVal
      
      | LambdaOpt'(args, arg, body) ->
        let env_size_counter_str = (string_of_int (env_size_counter+1)) in
        let minimum_args_expacted = string_of_int (List.length args) in
        let lambda_counter_str = string_of_int(inc_and_get_counter lambda_counter) in
        let iteration_number_on_shifting = string_of_int ((List.length args)+3) in
        let adjusting_frame =
          "lambda_code_"^lambda_counter_str ^":
            mov r15, rsp           ; backup rsp

            mov r10, [r15]
            mov rax, "^minimum_args_expacted ^"    ; rax <- num of args known from the expr'
            cmp rax, qword [r15+8*2]             ; where argc is right now
            je use_magic"^ lambda_counter_str ^ "

            ;; otherwise, we have args to pack and we need to shift the frame:
            mov r8, qword [r15+8*2] 
            sub r8, "^minimum_args_expacted^"
            mov r9, qword [r15+8*2] 
            add r9, 2
            PACK_OPT_ARGS r8, r9, "^minimum_args_expacted^"
            sub r8, 1
            ADJUST_FRAME r8, "^iteration_number_on_shifting^"            
            mov qword [r15+8*2] , ("^minimum_args_expacted^"+1)
            jmp end_frame_adjust_"^lambda_counter_str ^"

            ;; no need to shift the frame
            use_magic"^ lambda_counter_str ^":
            end_frame_adjust_"^lambda_counter_str^":
            mov rsp, r15            
            "         
          in
        let lambda_body = 
          "push rbp
          mov rbp, rsp\n"
          ^ code_gen (env_size_counter+1) body ^"
          leave
          ret
          " 
           in

        "mov r13, "^env_size_counter_str^
        "\nMALLOC rbx, ("^env_size_counter_str^" * WORD_SIZE) 			; rbx <- vector of size extEnv*WS
        
        EXT_ENV              ; rbx <- extEnv\n
        MAKE_CLOSURE (rax, rbx, lambda_code_"^lambda_counter_str^")
        jmp end_lambda_body_"^lambda_counter_str ^ "\n"
        ^adjusting_frame ^
        lambda_body ^
        "end_lambda_body_"^lambda_counter_str ^ ":\n"
      | _ -> ""
  
    in
    code_gen 0 e;;
    
end;;








