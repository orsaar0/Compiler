  
#use "pc.ml";;
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
  val read_sexprs : string -> sexpr list 

end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

  (**
  val read_sexpr: string -> sexpr 
  let read_sexprs string = raise X_not_yet_implemented;;
  let read_sexpr string = raise X_not_yet_implemented;;
  end;

  *)


(***************bool******************)

let bool_true = pack (caten (char '#') (char_ci 't')) (fun _-> Bool(true));;
let bool_false = pack (caten (char '#') (char_ci 'f')) (fun _->Bool(false));;
let nt_bool =disj bool_true bool_false ;;

(***************Char******************)

let char_prefix = caten (char '#') (char '\\');;
let visible_simple_char = pack (const(fun ch1 -> ch1 > ' ')) (fun ch -> Char(ch));;
let named_char =  pack (disj_list [word_ci "newline";
                                  word_ci "nul";
                                  word_ci "page";
                                  word_ci "return";
                                  word_ci "space";
                                  word_ci "tab"])
(fun charlist  ->  
match (list_to_string (List.map (fun (ch) -> (lowercase_ascii ch)) charlist)) with 
  | "newline" -> Char (Char.chr 10)
  | "nul" -> Char (Char.chr 0)
  | "tab" -> Char (Char.chr 9)
  | "space" -> Char (Char.chr 32)
  | "return" -> Char (Char.chr 13)
  | "page" ->  Char (Char.chr 12)
  |_ -> raise X_this_should_not_happen);;
  let nt_char = pack (caten char_prefix (disj named_char visible_simple_char)) (fun ((_,_),c3) -> c3);;


(**************symbol******************)
  let nt_dot = char '.';;
  let nt_symbol_char_not_dot = 
    let digit = range '0' '9' in
    let nt_low = range 'a' 'z' in
    let nt_up =  pack (range 'A' 'Z') (fun ch-> lowercase_ascii ch)  in
    let nt_punctuation = one_of "!$^*-=+_<>?/:" in
  let nt = disj_list [nt_low; nt_up; nt_punctuation; digit] in nt;;

  let nt_symbol_char = disj nt_dot nt_symbol_char_not_dot ;; 
  let nt_symbol =  disj (pack (caten nt_symbol_char (plus nt_symbol_char))
  (fun (ch,l)-> Symbol(list_to_string ([ch]@l))))
  (pack nt_symbol_char_not_dot (fun (ch)-> Symbol(list_to_string [ch])));;

(**************string******************)

(**when i need to use nt ? and how can i call to string parser?*)
(**what is the meaning of () and where can i need to skip and ch!='\'*)

let nt_string_literal_char = const (fun (ch) -> ch <> '\\' && ch <> '"');;

let nt_string_meta_char = pack ( disj_list [(caten (char '\\') (char_ci '\\')); (caten (char '\\') (char_ci '\"')); (caten (char '\\') (char_ci 't'));
(caten (char '\\') (char_ci 'f'));(caten (char '\\') (char_ci 'n')) ; (caten (char '\\') (char_ci 'r'))])
(fun (bslas,ch)-> 
  match (lowercase_ascii ch) with
  | '\\' -> (char_of_int 92) 
  | '\"' -> (char_of_int 34) 
  | 't'  -> (char_of_int 9)
  | 'f'  -> (char_of_int 12) 
  | 'n'  -> (char_of_int 10)
  | 'r'  -> (char_of_int 13)
  | _ -> raise X_no_match);;

let nt_string_char = disj nt_string_literal_char nt_string_meta_char;;
let nt_string = pack (caten (char '"') (caten (star nt_string_char) (char '"'))) 
(fun ((_,(ch2,_)))-> String (list_to_string ch2));;

(*************numbers*****************)
let nt_digit = pack (range '0' '9') (fun (ch)-> int_of_char ch - 48);;
let nt_natural = plus nt_digit ;;
let nt_integer = pack (caten (maybe (disj (char '+') (char '-'))) nt_natural) 
(fun (sign,num)-> 
let num =(List.fold_left(fun curr acc -> 10 * curr + acc) 0 num)
in match sign with 
| Some('+') -> Number(Fraction(num,1))
| Some('-')-> Number(Fraction(-1*num,1))
| None -> Number(Fraction(num,1))
| _ -> raise X_this_should_not_happen);;

let nt_digit1 = pack (range '0' '9') (fun (ch)-> float_of_int (int_of_char ch - 48));;
let nt_natural1 = plus nt_digit1;;

let nt_float = pack (caten nt_integer (caten nt_dot nt_natural1))
(fun (numeration,(dot,denomerator))->
match numeration with 
| Number(Fraction(numeration,1)) -> Number(Float( (float_of_int (numeration) ) +. (List.fold_right (fun a b-> (a+.b)/.10.0) denomerator 0.0)))
| _ -> raise X_this_should_not_happen);;


let rec gcd a b =
  if b = 0 then a else gcd b (a mod b);;

let nt_fraction = pack (caten nt_integer (caten (char '/') nt_natural))
(fun (numeration,(backs,denomerator))->
match numeration with 
| Number(Fraction(numeration,1)) -> let crate_num = (List.fold_left(fun curr acc -> 10 * curr + acc) 0 denomerator) in
                                    let gcdr = (gcd numeration crate_num) in
                                    if(gcdr>0) then Number(Fraction(numeration/gcdr,crate_num/gcdr)) else 
                                    if(gcdr=0) then Number(Fraction(numeration,crate_num)) else
                                    Number(Fraction(numeration/(-1*gcdr),crate_num/(-1*gcdr)))
| _ -> raise X_this_should_not_happen);;


let nt_scientific_notation = pack (caten (disj nt_float nt_integer) (caten (char_ci 'e') nt_integer) )
(fun (num1,(e,num2))-> match num1,num2 with 
| Number(Float(num1)),Number(Fraction(num2,1))-> Number(Float(num1*.10.0** (float_of_int num2)))
| Number(Fraction(num1,1)),Number(Fraction(num2,1)) -> Number(Float((float_of_int num1) *.10.0** (float_of_int num2)))
| _ -> raise X_this_should_not_happen);;

let nt_number = disj_list [nt_scientific_notation;nt_fraction;nt_float;nt_integer];;


(*************List***************)

let nt_whitespaces_star = star(const (fun ch -> ch <= ' '));;

let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

(***************LineComments******************)
let nt_comm = 
  let nt = (disj (char '\n') 
                 (pack
                 nt_end_of_input
                 (fun e-> '\n'))) in
  let nt=caten (caten (char ';')  (star (diff nt_any nt))) nt in 
  pack nt (fun _ -> []) 

let rec nt_sexpr s = pack (caten (star (disj_list [nt_comm;plus nt_whitespace;nt_sexp_comm])) 
(caten (disj_list [nt_dotted_list;nt_bool;nt_char;(not_followed_by (nt_number) (nt_symbol));nt_string;nt_symbol;nt_list;nt_quoted;nt_q_quoted;nt_un_spliced_quoted;nt_un_quoted]) (star (disj_list [plus nt_whitespace;nt_sexp_comm;nt_comm]))))
(fun (_,(sexp,_))-> sexp) s

and nt_list s = (pack (make_paired (char '(') (char ')') (star nt_sexpr))
        (fun e -> 
        (List.fold_right 
        (fun curr acc -> Pair (curr , acc))
        e
        Nil))) s

 and nt_dotted_list s =  pack (caten (char '(') (caten (plus nt_sexpr) 
 (caten nt_dot (caten nt_sexpr  (char ')') ) ) ) ) 
        (fun (p1,(plus_spex,(dot,(spex,p2))))-> 
        (List.fold_right 
        (fun curr acc -> Pair (curr , acc))
        plus_spex
        spex)) s 

  and nt_quoted s = pack (caten (char '\'') (nt_sexpr)) (fun (a, sex) -> Pair(Symbol("quote"),Pair(sex,Nil))) s
  and nt_q_quoted s = pack (caten (char '`') (nt_sexpr)) (fun (a, sex) -> Pair(Symbol("quasiquote"),Pair(sex,Nil))) s
  and nt_un_quoted s = pack (caten (char ',') (nt_sexpr)) (fun (a, sex) -> Pair(Symbol("unquote"),Pair(sex,Nil))) s
  and nt_un_spliced_quoted s = pack (caten (word ",@") (nt_sexpr)) (fun (a, sex) -> Pair(Symbol("unquote-splicing"),Pair(sex,Nil))) s

   and nt_sexp_comm s = 
    let nt = (pack 
               (caten (word "#;") nt_sexpr)
               (fun _ -> [])) in
     let nt= (disj nt
                   (pack 
                  (caten (caten (word "#;") nt_sexp_comm) nt_sexpr)
                  (fun _ -> []))) in
    pack nt (fun _ -> []) s 

let read_sexprs string = (fun (str) -> let (slist, _) =  ((star nt_sexpr) (string_to_list str)) in slist) string;;
end;;

(* open Reader;;
read_sexprs "(let ((baf (lambda (f)
(lambda (n)
  (if (> n 0)
      `(* ,n ,((f f) (- n 1)))
      \"end\")))))
((baf baf) 1))" *)
