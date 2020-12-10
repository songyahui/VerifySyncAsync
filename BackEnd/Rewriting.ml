open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Sys
open Askz3

let rec fst (pi :pure) (es:es): (instance option * terms option) list = 
  (*
  let rec common (left:(string* int option) list) (right:(string*int option) list) (acc:(string*int option) list): (string*int option) list =
    match left with 
      [] -> acc 
    | x :: xs -> 
      let rec oneOF (ele:(string*int option )) (li:(string*int option) list):bool =
        (match li with 
          [] -> false 
        | y::ys -> if compareEvent ele y then true else oneOF ele ys
        )
      in 
      if oneOF x right then common xs right (append acc [x]) else common xs right acc
  in 
  *)
  match es with
    Bot -> []
  | Emp -> []
  | Instance ins ->  [(ins, None)]
  | Ttimes (es1, t) -> fst pi es1
  | Cons (es1 , es2) ->  if nullable pi es1 then append (fst pi es1) (fst pi es2) else fst pi es1
  | Choice (es1, es2) -> append (fst pi es1) (fst pi es2)
  | TimeUnit -> [(None, Number 1)]
  | Kleene es1 -> fst pi es1
  | Par (es1 , es2) ->  raise (Foo "par in ")
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
  (*| _ -> false*)
;;

let rec compareES es1 es2 = 
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
  match (es1, es2) with 
    (Bot, Bot) -> true
  | (Emp, Emp) -> true
  (*| (Event (s1,p1), Event (s2,p2)) -> 
    compareEvent (s1,p1) (s2,p2)
    *)
  | (Cons (es1L, es1R), Cons (es2L, es2R)) -> (compareES es1L es2L) && (compareES es1R es2R)
  (*| (ESOr (es1L, es1R), ESOr (es2L, es2R)) -> 
      let one = ((compareES es1L es2L) && (compareES es1R es2R)) in
      let two =  ((compareES es1L es2R) && (compareES es1R es2L)) in 
      one || two
      *)
  | (Ttimes (esL, termL), Ttimes (esR, termR)) -> 
      let insideEq = (compareES esL esR) in
      let termEq = compareTerm termL termR in
      insideEq && termEq
  | (Kleene esL, Kleene esR) -> compareES esL esR
  | (TimeUnit, TimeUnit ) -> true
  (*| _ -> false*)
;;

let rec compareEff eff1 eff2 =
  match (eff1, eff2) with
  | (Effect(FALSE, _ ), Effect(FALSE, _)) -> true 
  | (Effect(FALSE, _ ), Effect(_, Bot )) -> true 
  | (Effect(_, Bot), Effect(FALSE, _ )) -> true 
  | (Effect(_, Bot ), Effect(_, Bot)) -> true 

  | (Effect (pi1, es1), Effect (pi2, es2 )) -> compareES es1 es2
  | (Disj (eff11, eff12), Disj (eff21, eff22)) -> 
      let one =  (compareEff eff11  eff21) && (compareEff eff12  eff22) in
      let two =  (compareEff eff11  eff22) && (compareEff eff12  eff21 ) in
      one || two
  | _ -> false
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


let rec normalES (es:es) (pi:pure):es = 
  match es with
    Bot -> es
  | Emp -> es
  | Instance ins -> Instance ins  (*logical tick*)
  | TimeUnit -> TimeUnit
  | Cons (Cons (esIn1, esIn2), es2)-> normalES (Cons (esIn1, Cons (esIn2, es2))) pi
  | Cons (es1, es2) -> 
      let normalES1 = normalES es1 pi in
      let normalES2 = normalES es2 pi in
      (match (normalES1, normalES2) with 
        (Emp, _) -> normalES2 
      | (_, Emp) -> normalES1
      | (Bot, _) -> Bot

      | (Kleene (esIn1), Kleene (esIn2)) -> 
          if aCompareES esIn1 esIn2 == true then normalES2
          else Cons (normalES1, normalES2)
      | (Kleene (esIn1), Cons(Kleene (esIn2), es2)) -> 
          if aCompareES esIn1 esIn2 == true then normalES2
          else Cons (normalES1, normalES2) 

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

  | Kleene es1 -> 
      let normalInside = normalES es1 pi in 
      (match normalInside with
        Emp -> Emp
      | Kleene esIn1 ->  Kleene (normalES esIn1 pi)
      | Choice(Emp, aa) -> Kleene aa
      | _ ->  Kleene normalInside)


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


let entailConstrains pi1 pi2 = 

  let sat = not (askZ3 (Neg (PureOr (Neg pi1, pi2)))) in
  (*
  print_string (showPure pi1 ^" -> " ^ showPure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat;;


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
    Effect (p, es) -> 
      if (askZ3 p) == false then 
        ( 
          (*print_string (showPure p^"   "^ showES es^ "\n 11********\n");*)
          Effect (FALSE, es)
        )
      else 
      
        let p_normal = normalPure p in 
        let es_normal  = normalES es p in
        (match es_normal with 
          Choice (es_nor1, es_nor2) -> Disj (Effect (p_normal, es_nor1), Effect (p_normal, es_nor2))
        | _ -> Effect ( p_normal, es_normal)
        )
  | Disj (eff1, eff2) -> 
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
  ;;


let rec checkFst (eff:effect) : (instance option * terms option) list = 
  match eff with
    Effect (pi, es) -> fst pi es
  | Disj (eff1, eff2) -> append (checkFst eff1) (checkFst eff2) 
 ;;


let rec containment (evn: inclusion list) (lhs:effect) (rhs:effect) : (binary_tree * bool) = 
  
  let normalFormL = normalEffect lhs in 
  let normalFormR = normalEffect rhs in 
  let showEntail = string_of_inclusion lhs rhs in 

  let unfold eff1 eff2 del = 
    let fstL = checkFst eff1 in 
    let deltaNew = List.append [(eff1, eff2)] del  in

    let rec chceckResultAND li acc staacc hypoacc:(bool *binary_tree list* int * hypotheses)=
      (match li with 
        [] -> (true, acc, staacc, hypoacc ) 
      | ev::fs -> 
          (*print_string ("\n"^string_of_Event ev^"\n\n");
          *)
          let deriL = checkDerivative eff1 ev varList in
          let deriR = checkDerivative eff2 ev varList in
          let (tree, re, states, hypo) =  containment1 deriL deriR hypoacc mode in 
          if re == false then (false , tree::acc, staacc+states, [])
          else chceckResultAND fs (tree::acc) (staacc+states)  (hypo)
      )
    in 
    let (resultFinal, trees, states, hypy ) = chceckResultAND fstL [] 0 deltaNew in 
    (Node (showEntail ^ "   [UNFOLD]",trees ), resultFinal, states+1, hypy)    
  in

  match (normalFormL, normalFormR) with 
      (*this means the assertion or precondition is already fail*)
    (Effect(FALSE, _), _) -> (Node(showEntail ^ "   [Bot-LHS]", []), true)  
  | (Effect(_, Bot), _) -> (Node(showEntail ^ "   [Bot-LHS]", []), true)  
  | (_, Effect(FALSE, _)) -> (Node(showEntail ^ "   [DISPROVE]", []), false)  
  | (_, Effect(_, Bot)) -> (Node(showEntail ^ "   [DISPROVE]", []), false)  
  | _ -> unfold normalFormL normalFormR evn 
  
  
 
 
  ;;




let check_containment lhs rhs : (binary_tree *bool) = 
  containment [] lhs rhs
  ;;

let printReport (lhs:effect) (rhs:effect) :string =

  let entailment = string_of_inclusion (normalEffect lhs) (normalEffect rhs) in 
  let startTimeStamp = Sys.time() in
  let (tree, re) =  check_containment lhs rhs in
  let verification_time = "[Verification Time: " ^ string_of_float (Sys.time() -. startTimeStamp) ^ " s]\n" in
  let result = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  let buffur = ( "----------------------------------------"^"\n" ^(entailment)^"\n[Result] " ^(if re then "Succeed\n" else "Fail\n")  ^verification_time^" \n\n"^ result)
  in buffur
  
  ;;

(*
let main = 
  let (re, temp) = in 
  let tree = printTree ~line_prefix:"* " ~get_name ~get_children temp in 

  print_string (tree);
  *)

