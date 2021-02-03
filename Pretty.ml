(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open String
open List
open Ast
open Printf
open Int32
open Askz3


exception Foo of string


let counter = ref 0;;

let getAnewVar = 
  counter := ! counter + 1; 
  "t" ^ string_of_int !counter;;

let counter_rewriting = ref 0;;



let getAnewVar_rewriting () = 
  counter_rewriting := ! counter_rewriting + 1; 
  "tv" ^ string_of_int !counter_rewriting;;

(*used to generate the free veriables, for subsititution*)
let freeVar = ["t1"; "t2"; "t3"; "t4";"t5";"t6";"t7";"t8";"t9";"t10"
              ;"t11"; "t12"; "t13"; "t14";"t15";"t16";"t17";"t18";"t19";"t20"
              ;"t21"; "t22"; "t23"; "t24";"t25";"t26";"t27";"t28";"t29";"t30"];;



let rec getAfreeVar (varList:string list):string  =
  let rec findOne li = 
    match li with 
        [] -> raise ( Foo "freeVar list too small exception!")
      | x :: xs -> if (exists (fun a -> String.compare a x == 0) varList) == true then findOne xs else x
  in
  findOne freeVar
;;




let rec iter f = function
  | [] -> ()
  | [x] ->
      f true x
  | x :: tl ->
      f false x;
      iter f tl

let to_buffer ?(line_prefix = "") ~get_name ~get_children buf x =
  let rec print_root indent x =
    bprintf buf "%s\n" (get_name x);
    let children = get_children x in
    iter (print_child indent) children
  and print_child indent is_last x =
    let line =
      if is_last then
        "└── "
      else
        "├── "
    in
    bprintf buf "%s%s" indent line;
    let extra_indent =
      if is_last then
        "    "
      else
        "│   "
    in
    print_root (indent ^ extra_indent) x
  in
  Buffer.add_string buf line_prefix;
  print_root line_prefix x

let printTree ?line_prefix ~get_name ~get_children x =
  let buf = Buffer.create 1000 in
  to_buffer ?line_prefix ~get_name ~get_children buf x;
  Buffer.contents buf

type binary_tree =
  | Node of string * (binary_tree  list )
  | Leaf

let get_name = function
    | Leaf -> "."
    | Node (name, li) -> name;;

let get_children = function
    | Leaf -> []
    | Node (_, li) -> List.filter ((<>) Leaf) li;;

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"

  ;;

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"
;;
(*
let rec string_of_action (act:action) : string = 
  match act with 
    Delay n -> "Delay " ^ string_of_int n  
  | Timeout n -> "time out " ^ string_of_int n  
  | NoneAct -> "NoneAct";;
*)
let string_of_state (state :signal):string = 
  match state with 
    One name -> name 
  | Zero name -> "!"^name 
  ;;


let string_of_sl (sl: instance):string = 
  List.fold_left (fun acc (sig_) -> 
  acc ^ "," ^ 
  string_of_state sig_ (*^ (
    match n with 
      None -> ";"
    | Some n -> "(" ^ string_of_int n ^");"
  )*)
  ) "" sl
;;

let string_of_instance (mapping:instance) :string = 
  let temp1 = "{" ^ string_of_sl mapping ^ "}" in 
  temp1
  ;;

let rec string_of_terms (t:terms):string = 
  match t with
    Var name -> name
  | Number n -> string_of_int n
  | Plus (t1, t2) -> (string_of_terms t1) ^ ("+") ^ (string_of_terms t2)
  | Minus (t1, t2) -> (string_of_terms t1) ^ ("-") ^ (string_of_terms t2)

  ;;

(*
let string_of_promise (pro:promise) : string = 
  match pro with 
    Sing (s, arg) -> 
    (
    match arg with 
      None -> ""
    | Some (n) -> "(" ^ string_of_int n ^")"
    )
  | Count (t, (s, arg)) ->
    "count("^string_of_terms t ^ ", "^
    (
    match arg with 
      None -> ""
    | Some (n) -> "(" ^ string_of_int n ^")"
    ) 
;;
*)



let rec showLTL (ltl:ltl):string =
  match ltl with 
    Lable str -> str
  | Next l -> "(" ^"X" ^showLTL l ^")"
  | Until (l1, l2) -> "(" ^showLTL l1 ^ " U " ^showLTL l2 ^")"
  | Global l -> "(" ^"[] " ^showLTL l ^")"
  | Future l -> "(" ^"<> " ^showLTL l ^")"
  | NotLTL l -> "(" ^"! " ^showLTL l ^")"
  | Imply (l1, l2) -> "(" ^showLTL l1 ^ " -> " ^showLTL l2 ^")"
  | AndLTL (l1, l2) -> "(" ^showLTL l1 ^ " && " ^showLTL l2 ^")"
  | OrLTL (l1, l2) -> "(" ^showLTL l1 ^ " || " ^showLTL l2 ^")"
  ;;



(*
let rec string_of_realtime (rt:realtime):string = 
  match rt with 
    Anytime -> ""
  | EqConst n -> "=" ^ string_of_int n 
  | Greater n -> ">" ^ string_of_int n 
  | LessThan n -> "<" ^ string_of_int n 
  | RTAnd (rt1, rt2) -> string_of_realtime rt1 ^ "/\\" ^ string_of_realtime rt2
  | RTOr (rt1, rt2) -> string_of_realtime rt1 ^ "\\/" ^ string_of_realtime rt2
;;
*)

let rec string_of_es (es:es) :string = 
  match es with 
    Bot -> "_|_"  
  | Emp -> "emp"
  | Wait name -> name ^ "?"
  | Instance ins  -> string_of_instance ins
  | Cons (es1, es2) ->  "("^string_of_es es1 ^ " . " ^ string_of_es es2^")"
  | Kleene esIn -> "(" ^ string_of_es esIn ^ ")*" 
  (*| Ttimes (esIn, t) ->"(" ^ string_of_es esIn ^ ")" ^ string_of_terms t *)
  | RealTime (es, t)-> "(" ^ string_of_es es ^ "#" ^string_of_terms t^")"
  | Choice (es1, es2) -> "("^string_of_es es1 ^ " + " ^ string_of_es es2^")"
  | Par (es1, es2) -> "("^string_of_es es1 ^ " || " ^ string_of_es es2^")"
  ;;

(*To pretty print pure formulea*)
let rec string_of_pure (p:pure):string = 
  match p with
    TRUE -> "true"
  | FALSE -> "false"
  | Gt (t1, t2) -> (string_of_terms t1) ^ ">" ^ (string_of_terms t2)
  | Lt (t1, t2) -> (string_of_terms t1) ^ "<" ^ (string_of_terms t2)
  | GtEq (t1, t2) -> (string_of_terms t1) ^ ">=" ^ (string_of_terms t2)
  | LtEq (t1, t2) -> (string_of_terms t1) ^ "<=" ^ (string_of_terms t2)
  | Eq (t1, t2) -> (string_of_terms t1) ^ "=" ^ (string_of_terms t2)
  | PureOr (p1, p2) -> "("^string_of_pure p1 ^ "\\/" ^ string_of_pure p2^")"
  | PureAnd (p1, p2) -> "("^string_of_pure p1 ^ "/\\" ^ string_of_pure p2^")"
  | Neg p -> "(!" ^ "(" ^ string_of_pure p^"))"
  ;; 


let rec string_of_effect(eff:effect): string = 
  match eff with 
    [] -> ""
  | [(p , es)] -> string_of_pure p ^ "&" ^ string_of_es es
  | (p , es)::xs -> string_of_pure p ^ "&" ^ string_of_es es  ^ "\\/" ^ string_of_effect xs 
  
;;


let rec string_of_prog (p : prog) : string =
  match p with
    Halt -> "halt"
  | Yield -> "yield"
  | Seq (p1, p2) ->  string_of_prog p1 ^ ";\n" ^ string_of_prog p2 
  | Fork (p1, p2) ->  "(" ^ string_of_prog p1 ^ ")\n||\n (" ^ string_of_prog p2 ^" )"
  | Loop pIn -> "loop\n " ^ string_of_prog pIn ^ "\nend loop"
  | Declear (s, prog) -> "signal " ^ s ^ " in \n" ^ string_of_prog prog ^ "\nend signal"
  | Emit (s) -> "emit " ^ s   (*^ 

    match arg with 
      None -> ""
    | Some (n) -> "(" ^ string_of_int n ^")"
  *) 
  | Present (s, p1, p2) -> "present " ^ s ^ "\nthen " ^ string_of_prog p1 ^"\nelse " ^ string_of_prog p2 ^"\nend present"
  (*| If (p, p1, p2) -> "if " ^ string_of_pure p ^ "\nthen " ^ string_of_prog p1 ^"\nelse " ^ string_of_prog p2 ^"\nend present"
*)
  | Trap (mn, prog) -> "trap "  ^ mn ^" in\n" ^ string_of_prog prog ^" )"^ "\nend trap"
  | Break  mn -> "exit " ^ mn 
  | Run mn -> "run " ^ mn
  | Abort (s, prog) -> "abort \n" ^ string_of_prog prog ^ "\nwhen "^ string_of_int s
  | Async (mn, prog, act) -> "async "^ mn ^ string_of_prog prog ^ string_of_int act
  | Await (pro) -> "await "^ pro 
  | Assert eff -> "assert "^ string_of_effect eff 
  ;;

let entailConstrains pi1 pi2 = 

  let sat = not (askZ3 (Neg (PureOr (Neg pi1, pi2)))) in
  (*
  print_string (string_of_pure pi1 ^" -> " ^ string_of_pure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat;;

let entailConstrains1 pi1 pi2 = 

  let sat = not (askZ3 
    (PureAnd (pi1, Neg pi2) ) 
    ) in
  (*
  print_string (string_of_pure pi1 ^" -> " ^ string_of_pure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat;;




let string_of_spec_prog (inp:spec_prog):string = 
  let  (nm, ins, outs, pre, post, p) = inp in 
  let body = string_of_prog p in 
  let spec = "\n/*@\nrequire " ^ string_of_effect pre ^"\nensure " ^ string_of_effect post ^"\n@*/\n\n" in 
  
  let inp = "input " ^ (*string_of_sl ins*) (List.fold_left (fun acc a -> acc ^ " " ^ a) "" ins) ^ ";\n" in 
  let outp = "output " ^ (*string_of_sl outs*)  (List.fold_left (fun acc a -> acc ^ " " ^ a) "" outs) ^ ";\n" in 
  let whole = "module " ^ nm  ^": \n\n" ^ inp ^ outp ^ spec ^ body ^ "\n\nend module" in 
  whole ;;

let string_of_full_prog (full: spec_prog list):string = 
  List.fold_left (fun acc (p) -> acc ^ "\n\n" ^ string_of_spec_prog p) "" full
;;



let string_of_inclusion (lhs:effect) (rhs:effect) :string = 
  string_of_effect lhs ^" |- " ^string_of_effect rhs 
  ;;

let string_of_prog_states (ps: prog_states) : string = 
  List.fold_left  (fun acc (p, es, instance,  _) -> 
    acc^ string_of_pure p ^ "/\\" ^ string_of_es es ^ " : " ^ string_of_instance instance  
  ) " "ps
  ;;

let string_of_split (ps) : string = 
  List.fold_left  (fun acc (p, es, instance) -> 
    acc^ string_of_pure p ^ "/\\" ^ string_of_es es ^ " : " ^ string_of_instance instance  
  ) " "ps
  ;;

(*
let compareSignal (s1 :signal * int option) (s2:signal * int option) : bool =
  match (s1, s2) with 
    ((One n1, Some n11), (One n2, Some n22)) -> String.compare n1 n2 == 0 && n11 == n22
  | ((Zero n1, Some n11) , (Zero n2, Some n22) ) -> String.compare n1 n2 == 0 && n11 == n22
  | ((One n1, None), (One n2, None)) -> String.compare n1 n2 == 0 
  | ((Zero n1, None) , (Zero n2, None) ) -> String.compare n1 n2 == 0 

  | _ -> false 
  ;;
*)
let compareSignal (s1 :signal) (s2:signal) : bool =
  
  match (s1, s2) with 
  | (One n1, One n2) -> String.compare n1 n2 == 0
  | (Zero n1, Zero n2) -> String.compare n1 n2 == 0
  | _ -> false 
  ;;

let controdict s1 s2 : bool =
  match (s1, s2) with 
    (One n1, Zero n2) -> String.compare n1 n2 == 0
  | (Zero n1 , One n2 ) -> String.compare n1 n2 == 0 
  | _ -> false 
  ;;

let rec oneOfFalse (sig_:signal) ss : bool =
  match ss with 
    [] -> false 
  | head_sig:: xs -> if controdict sig_ head_sig then true else oneOfFalse sig_ xs
;;
(*true return has controdiction, false means no controdiction *)
let rec checkHasFalse ss : bool = 
  match ss with 
  [] -> false 
| x::xs -> if oneOfFalse x xs then true else checkHasFalse xs 
;;




let rec oneOf (sig_:signal) (ss:instance) : bool =
  match ss with 
    [] -> false 
  | sig_head:: xs -> 

  if compareSignal sig_ sig_head then true else oneOf sig_ xs
;;

let rec deleteRedundent sl : instance = 
  match sl with 
    [] -> sl 
  | x::xs -> if oneOf x xs then deleteRedundent xs else List.append [x] (deleteRedundent xs)

  ;;

(*
let rec realtimeToPure (rt:realtime) :pure = 
  match rt with 
  | Anytime -> TRUE
  | EqConst n -> Eq (Var "n", Number n )
  | Greater n -> Gt (Var "n", Number n )
  | LessThan n -> Lt (Var "n", Number n )
  | RTAnd (rt1, rt2) -> PureAnd (realtimeToPure rt1, realtimeToPure rt2)
  | RTOr (rt1, rt2) -> PureOr (realtimeToPure rt1, realtimeToPure rt2)
;;
*)

let rec nullable (es:es) : bool=
  match es with 
    Bot -> false 
  | Emp -> true
  | Wait _ ->  false 
  | Instance _  -> false 
  | Cons (es1, es2) -> (nullable es1) && (nullable es2)
  | Kleene _ -> true (* now kleene represents infinite trace *)  
  (*| Ttimes (_, t) -> askZ3 (PureAnd (pi, Eq (t, Number 0))) *)
  | RealTime (es, rt) ->  nullable es (* askZ3 (realtimeToPure rt )*)
  | Choice (es1, es2) -> (nullable es1) || (nullable es2)
  | Par (es1, es2) -> (nullable es1) && (nullable es2)
  ;;

let rec normalTerms (t:terms):terms  = 
  match t with 
    Minus (Minus(s, Number n1), Number n2) ->  Minus(s, Number (n1 + n2))
  | Minus (Number n1, Number n2) ->  Number (n1- n2) 
  | Plus (Number n1, Number n2) -> Number (n1 + n2)
  | _ -> t 
  ;;


let rec compareTerm (term1:terms) (term2:terms) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> true
  | (Number n1, Number n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> compareTerm tIn1 tIn2 && compareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> compareTerm tIn1 tIn2 && compareTerm num1  num2
  | _ -> false 
  ;;

let rec aCompareES es1 es2 = 
  (*
  let rec subESsetOf (small : es list) (big : es list) :bool = 
    let rec oneOf a set :bool = 
      match set with 
        [] -> false 
      | y:: ys -> if aCompareES a y then true else oneOf a ys
    in 
    match small with 
      [] -> true 
    | x :: xs -> if oneOf x big == false then false else subESsetOf xs big
  in 
*)
  match (es1, es2) with 
    (Bot, Bot) -> true
  | (Emp, Emp) -> true
  (*| (Event (s1, p1), Event (s2,p2)) -> 
    String.compare s1 s2 == 0 && compareParm p1 p2 
  | (Cons (es1L, es1R), Cons (es2L, es2R)) -> 
    if (aCompareES es1L es2L) == false then false
    else (aCompareES es1R es2R)
  | (ESOr (es1L, es1R), ESOr (es2L, es2R)) -> 
      if ((aCompareES es1L es2L) && (aCompareES es1R es2R)) then true 
      else ((aCompareES es1L es2R) && (aCompareES es1R es2L))
*)
  | (Kleene esL, Kleene esR) -> aCompareES esL esR
  | _ -> false
;;

let instansEntails (ins1:instance) (ins2:instance) :bool = 
  let rec aux instemp = 
    match instemp with 
      [] -> true 
    | x::xs -> if oneOf x ins1 then aux xs else false 
  in aux ins2

  ;;

(*
let rec compareRealTime rt1 rt2 = 
  match (rt1, rt2) with 
    (EqConst n1, EqConst n2) -> n1 == n2
  | (Greater n1, Greater n2) -> n1 == n2
  | (LessThan n1, LessThan n2) -> n1 == n2

  | _ -> raise (Foo "not yet defined compareRealTime")
  ;;
*)

let rec compareES es1 es2 = 
  (*
  let rec subESsetOf (small : es list) (big : es list) :bool = 
    let rec oneOf a set :bool = 
      match set with 
        [] -> false 
      | y:: ys -> if aCompareES a y then true else oneOf a ys
    in 
    match small with 
      [] -> true 
    | x :: xs -> if oneOf x big == false then false else subESsetOf xs big
  in 
  *)
  match (es1, es2) with 
    (Bot, Bot) -> true
  | (Emp, Emp) -> true
  | (Instance ins1, Instance ins2) -> 
    instansEntails ins1 ins2
    
  | (Cons (es1L, es1R), Cons (es2L, es2R)) -> (compareES es1L es2L) && (compareES es1R es2R)
  | (Choice (es1L, es1R), Choice (es2L, es2R)) -> ((compareES es1L es2L) && (compareES es1R es2R))
    || ((compareES es1L es2R ) && (compareES es1R es2L))

  (*| (ESOr (es1L, es1R), ESOr (es2L, es2R)) -> 
      let one = ((compareES es1L es2L) && (compareES es1R es2R)) in
      let two =  ((compareES es1L es2R) && (compareES es1R es2L)) in 
      one || two

  | (Ttimes (esL, termL), Ttimes (esR, termR)) -> 
      let insideEq = (compareES esL esR) in
      let termEq = compareTerm termL termR in
      insideEq && termEq
      *)
  | (Kleene esL, Kleene esR) -> 
      
    compareES esL esR
  | (RealTime (es1, rt1), RealTime (es2, rt2) ) -> compareES es1 es2 && compareTerm rt1 rt2
  | _ -> false
;;


let rec compareEff eff1 eff2 =
  match (eff1, eff2) with
  | ((FALSE, _ ), (FALSE, _)) -> true 
  | ((FALSE, _ ), (_, Bot )) -> true 
  | ((_, Bot), (FALSE, _ )) -> true 
  | ((_, Bot ), (_, Bot)) -> true 

  | ( (pi1, es1),  (pi2, es2 )) -> compareES es1 es2
(*| (Disj (eff11, eff12), Disj (eff21, eff22)) -> 
      let one =  (compareEff eff11  eff21) && (compareEff eff12  eff22) in
      let two =  (compareEff eff11  eff22) && (compareEff eff12  eff21 ) in
      one || two
        | _ -> false
      *)

  ;;

let rec compareTerm (term1:terms) (term2:terms) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> true
  | (Number n1, Number n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> compareTerm tIn1 tIn2 && compareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> compareTerm tIn1 tIn2 && compareTerm num1  num2
  | _ -> false 
  ;;


let rec stricTcompareTerm (term1:terms) (term2:terms) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> String.compare s1 s2 == 0
  | (Number n1, Number n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | _ -> false 
  ;;

let rec comparePure (pi1:pure) (pi2:pure):bool = 
  match (pi1 , pi2) with 
    (TRUE, TRUE) -> true
  | (FALSE, FALSE) -> true 
  | (Gt (t1, t11), Gt (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Lt (t1, t11), Lt (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (GtEq (t1, t11), GtEq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (LtEq (t1, t11), LtEq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Eq (t1, t11), Eq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (PureOr (p1, p2), PureOr (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (PureAnd (p1, p2), PureAnd (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (Neg p1, Neg p2) -> comparePure p1 p2
  | _ -> false

let rec getAllPi piIn acc= 
    (match piIn with 
      PureAnd (pi1, pi2) -> append (getAllPi pi1 acc ) (getAllPi pi2 acc )
    | _ -> append acc [piIn]
    )
    ;;

let rec existPi pi li = 
    (match li with 
      [] -> false 
    | x :: xs -> if comparePure pi x then true else existPi pi xs 
    )
    ;;

let rec concertive (es:es) (t:int): es = 
  if t ==0 then Emp 
  else Cons (es, concertive es (t -1))
  ;;

let rec isThere (ins) (sig_) : bool = 
  match ins with 
    [] -> false 
  | x:: xs -> if compareSignal sig_ x  then true else isThere xs sig_

  ;;

let normalIns (ins:instance): instance =
  let rec aux current =  
    match current with 
    [] -> []
  | x :: xs -> if isThere ins x  then aux xs else x:: aux xs 
  in 
  aux ins
  ;;


let rec normalES (es:es) (pi:pure):es = 
  match es with
    Bot -> es
  | Emp -> es
  | Wait _ -> es
  | Instance ins -> Instance ( ins)  (*logical tick*)
  | RealTime (es, rt) -> RealTime (normalES es pi, rt) 
  | Cons (Cons (esIn1, esIn2), es2)-> normalES (Cons (esIn1, Cons (esIn2, es2))) pi
  | Cons (es1, es2) -> 
      let normalES1 = normalES es1 pi in
      let normalES2 = normalES es2 pi in
      (match (normalES1, normalES2) with 
        (Emp, _) -> normalES2 
      | (_, Emp) -> normalES1
      | (Bot, _) -> Bot
      (*| (Kleene esIn, _) -> Kleene esIn (* kleene now is infinite constructor *)
*)
      (*| (Kleene (esIn1), Kleene (esIn2)) -> 
          if aCompareES esIn1 esIn2 == true then normalES2
          else Cons (normalES1, normalES2)
      | (Kleene (esIn1), Cons(Kleene (esIn2), es2)) -> 
          if aCompareES esIn1 esIn2 == true then normalES2
          else Cons (normalES1, normalES2) 
      *)
      | (normal_es1, normal_es2) -> 

        match (normal_es1, normal_es2) with 
        (*|  (Cons (esIn1, esIn2), es2)-> normalES (Cons (esIn1, Cons (esIn2, es2))) pi *)
        (*|  (Choice (or1, or2), es2) ->  (Choice (normalES  (Cons (or1, es2)) pi,  normalES (Cons (or2, es2)) pi)) *)
        |  (es1, Choice (or1, or2)) -> normalES (Choice ( (Cons (es1, or1)),  (Cons (es1, or2)))) pi
        | _-> Cons (normal_es1, normal_es2)
        
      ;)
  | Choice (es1, es2) -> 
      (match (normalES es1 pi, normalES es2 pi) with 
        (Bot, Bot) -> Bot
      | (Bot, norml_es2) -> norml_es2
      | (norml_es1, Bot) -> norml_es1
      | (Choice(es1In, es2In), norml_es2 ) ->
        if aCompareES norml_es2 es1In || aCompareES norml_es2 es2In then Choice(es1In, es2In)
        else Choice (Choice(es1In, es2In), norml_es2 )
      | (norml_es2, Choice(es1In, es2In) ) ->
        if aCompareES norml_es2 es1In || aCompareES norml_es2 es2In then Choice(es1In, es2In)
        else Choice (norml_es2, Choice(es1In, es2In))
      | (Emp, Kleene norml_es2) ->  Kleene norml_es2
      | (Kleene norml_es2, Emp) ->  Kleene norml_es2

      | (norml_es1, norml_es2) -> 
        if aCompareES  norml_es1 norml_es2 == true then norml_es1
        else 
        (match (norml_es1, norml_es2) with
          (norml_es1, Kleene norml_es2) ->  
          if aCompareES norml_es1 norml_es2 == true then Kleene norml_es2
          else Choice (norml_es1, Kleene norml_es2)
        | (Kleene norml_es2, norml_es1) ->  
          if aCompareES norml_es1 norml_es2 == true then Kleene norml_es2
          else Choice (Kleene norml_es2, norml_es1)
        |  _-> Choice (norml_es1, norml_es2)
        )
      ;)



(*
  | Ttimes (es1, terms) -> 
      let t = normalTerms terms in 
      let normalInside = normalES es1 pi in 
      (match normalInside with
        Emp -> Emp
      | _ -> 
        let allPi = getAllPi pi [] in 
        if (existPi (Eq (terms, Number 0)) allPi) then Emp else 
          match t with
            Number num -> concertive normalInside num 
          | _ -> Ttimes (normalInside, t))
        (*else if (existPi (Eq (terms, n)) allPi)) then Emp else Ttimes (normalInside, t))*)
*)
  | Kleene es1 -> 
      let normalInside = normalES es1 pi in 
      (match normalInside with
        Emp -> Emp
      | Kleene esIn1 ->  Kleene (normalES esIn1 pi)
      | Choice(Emp, aa) -> Kleene aa
      | _ ->  Kleene normalInside)

  | Par (es1, es2) -> Par (es1, es2)
   ;;

let rec compareTerm (term1:terms) (term2:terms) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> true
  | (Number n1, Number n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> compareTerm tIn1 tIn2 && compareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> compareTerm tIn1 tIn2 && compareTerm num1  num2
  | _ -> false 
  ;;


let rec stricTcompareTerm (term1:terms) (term2:terms) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> String.compare s1 s2 == 0
  | (Number n1, Number n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | _ -> false 
  ;;

let rec comparePure (pi1:pure) (pi2:pure):bool = 
  match (pi1 , pi2) with 
    (TRUE, TRUE) -> true
  | (FALSE, FALSE) -> true 
  | (Gt (t1, t11), Gt (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Lt (t1, t11), Lt (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (GtEq (t1, t11), GtEq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (LtEq (t1, t11), LtEq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Eq (t1, t11), Eq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (PureOr (p1, p2), PureOr (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (PureAnd (p1, p2), PureAnd (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (Neg p1, Neg p2) -> comparePure p1 p2
  | _ -> false
  ;;





let rec normalTerms (t:terms):terms  = 
  match t with 
    Minus (Minus(s, Number n1), Number n2) ->  Minus(s, Number (n1 + n2))
  | Minus (Number n1, Number n2) ->  Number (n1- n2) 
  | Plus (Number n1, Number n2) -> Number (n1 + n2)
  | _ -> t 
  ;;




let rec normalPure (pi:pure):pure = 
  let allPi = getAllPi pi [] in
  let rec clear_Pi pi li = 
    (match li with 
      [] -> [pi]
    | x :: xs -> if existPi pi li then clear_Pi x xs else append [pi] (clear_Pi x xs)
    )in 
  let finalPi = clear_Pi TRUE allPi in
  let rec connectPi li acc = 
    (match li with 
      [] -> acc 
    | x :: xs -> if entailConstrains TRUE x then (connectPi xs acc) else PureAnd (x, (connectPi xs acc)) 
    ) in 
  let filte_true = List.filter (fun ele-> not (comparePure ele TRUE)  ) finalPi in 
  if length filte_true == 0 then  TRUE
  else connectPi (tl filte_true) (hd filte_true)
  ;;



let rec normalEffect (eff:effect) : effect =
  match eff with
    [] -> [] 
  | (p, es) :: xs  -> 
      List.append (if (askZ3 p) == false then 
        ( 
          (*print_string (showPure p^"   "^ showES es^ "\n 11********\n");*)
         []
        )
      else 
      
        let p_normal = normalPure p in 
        let es_normal  = normalES es p in
        match es_normal with 
          Bot -> []
          | _ ->
        [( p_normal, es_normal)])  (normalEffect xs)
       (*
        (match es_normal with 
          Choice (es_nor1, es_nor2) -> Choice ( (p_normal, es_nor1),  (p_normal, es_nor2))
        | _ -> Effect 
        )
       *)
  
  (*      | Disj (eff1, eff2) -> 
      let normaedEff1 = normalEffect eff1 in 
      let normaedEff2 = normalEffect eff2 in 
      match (normaedEff1, normaedEff2 ) with
        (Effect (_,  Bot  ), _) -> normaedEff2
      | (_, Effect (_,  Bot)) -> normaedEff1
      | (Effect (FALSE,  _), _) -> normaedEff2
      | (_, Effect (FALSE,  _)) -> normaedEff1

      | (Disj(eff1In, eff2In), norml_eff2 ) ->
        if compareEff norml_eff2 eff1In || compareEff norml_eff2 eff2In then Disj(eff1In, eff2In)
        else Disj (Disj(eff1In, eff2In), norml_eff2 )
      | (norml_eff2, Disj(eff1In, eff2In) ) ->
        if compareEff norml_eff2 eff1In || compareEff norml_eff2 eff2In then Disj(eff1In, eff2In)
        else Disj (norml_eff2, Disj(eff1In, eff2In))

      | _ -> Disj (normaedEff1, normaedEff2)
      *)
  ;;
