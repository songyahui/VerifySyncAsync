open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Sys
open Askz3

let rec fst (pi :pure) (es:es): fst list = 
  match es with
    Bot -> []
  | Emp -> []
  | Instance ins ->  [(Instance ins, None)]
  | Ttimes (es1, t) -> fst pi es1
  | Cons (es1 , es2) ->  if nullable pi es1 then append (fst pi es1) (fst pi es2) else fst pi es1
  | Choice (es1, es2) -> append (fst pi es1) (fst pi es2)
  | RealTime rt -> [(Emp, Some rt)]
  | Kleene es1 -> fst pi es1
  | Par (es1 , RealTime rt) -> [(es1, Some rt)]
  | Par (RealTime rt, es1) -> [(es1, Some rt)]
  | _ -> raise (Foo "not definde in fst")
;;



let rec appendEff_ES eff es = 
  match eff with 
    Effect (p , es_eff) ->  Effect(p, Cons (es_eff, es))
  | Disj (eff1 , eff2)  ->  Disj (appendEff_ES eff1 es, appendEff_ES eff2 es)
  
  (*raise ( Foo "appendEff_ES exception!")*)
  ;;

let ifShouldDisj (temp1:effect) (temp2:effect) : effect = 
  match (temp1, temp2) with
      (Effect(pure1, evs1), Effect(pure2, evs2)) -> 
        if comparePure pure1 pure2 then  Effect (pure1, Choice (evs1, evs2))
        else Disj (temp1, temp2 )
      | _ -> 
      Disj (temp1, temp2 )
  ;;





let rec checkFst (eff:effect) : fst list = 
  match eff with
    Effect (pi, es) -> fst pi es
  | Disj (eff1, eff2) -> append (checkFst eff1) (checkFst eff2) 
 ;;

let rec nullableEffect (eff:effect) : bool = 
  match eff with 
    Effect (pi, es) -> nullable pi es
  | Disj (eff1, eff2) -> (nullableEffect eff1) || (nullableEffect eff2) 
 ;;

let rec entailEffects (eff1:effect) (eff2:effect) : bool = 
  match (eff1, eff2) with 
    (Effect (p1, es1), Effect (p2, es2)) -> 
      if comparePure p1 p2 && compareES es1 es2 then true 
      else false 
  | (Disj (f1, f2), Disj (f3, f4)) -> 
  (entailEffects f1 f3 && entailEffects f2 f4) || (entailEffects f2 f3 && entailEffects f1 f4)
  | _ -> false 
;;

let reoccur (evn: inclusion list) (lhs:effect) (rhs:effect): bool = 
  let rec aux inclusions = 
    match inclusions with 
      [] -> false 
    | (lhs1, rhs2)::xs -> 
      if entailEffects lhs lhs1  && entailEffects rhs2 rhs then true
      else aux xs 
  in aux evn
  ;;


let rec containment (evn: inclusion list) (lhs:effect) (rhs:effect) : (bool * binary_tree *  inclusion list) = 
  
  let normalFormL = normalEffect lhs in 
  let normalFormR = normalEffect rhs in 
  let showEntail = string_of_inclusion normalFormL normalFormR in 
  let rec derivative (pi :pure) (es:es) (fst:fst) : effect = 
  match es with
    Bot -> Effect (FALSE, Bot)
  | Emp -> Effect (FALSE, Bot)
  | Instance ins ->  
      (match fst with 
        (Instance ins1, None) -> 
          if instansEntails ins1 ins then Effect (pi, Emp) 
          else Effect (FALSE, Bot)
      |_ -> Effect (FALSE, Bot)
      )
  | Ttimes (es1, t) -> 
      let pi = PureAnd (Gt (t, Number 0), pi) in
      let efF = derivative pi es1 fst in 
      let esT_minus1 = Ttimes (es1,  Minus (t, Number 1)) in
      appendEff_ES efF esT_minus1
  | Cons (es1 , es2) ->  
      if nullable pi es1 
      then let efF = derivative pi es1 fst in 
          let effL =  (appendEff_ES efF es2) in 
          let effR =  (derivative pi es2 fst) in 
          normalEffect (ifShouldDisj effL effR)
      else let efF = derivative pi es1 fst in 
          appendEff_ES efF es2    
  | Choice (es1, es2) -> 
      let temp1 =  (derivative pi es1 fst) in
      let temp2 =  (derivative pi es2 fst) in 
      normalEffect (ifShouldDisj temp1 temp2)
  | RealTime rt -> 
    (match fst with 
        (Emp, Some rt1) -> 
          let rtpure = realtimeToPure rt in 
          let rt1pure = realtimeToPure rt1 in 
          if entailConstrains rt1pure rtpure then Effect (pi, Emp) 
          else Effect (FALSE, Bot)
      |_ -> Effect (FALSE, Bot)
      )
  | Kleene es1 -> appendEff_ES  (derivative pi es1 fst) es
  | Par (es1 , RealTime rt) -> 
    (match fst with 
      (esfst, Some rt1) -> 
        let (re1, _, _) = containment [] (Effect(pi, esfst)) (Effect (pi, es1)) in
        let (re2, _, _) = containment [] (Effect(pi, RealTime rt1)) (Effect (pi, RealTime rt)) in
        if (re1 && re2) then Effect (pi, Emp) 
        else Effect (FALSE, Bot)
    | _ -> Effect (FALSE, Bot)

    )
  | Par (RealTime rt, es1) -> 
    (match fst with 
      (esfst, Some rt1) -> 
        let (re1, _, _) = containment [] (Effect(pi, esfst)) (Effect (pi, es1)) in
        let (re2, _, _) = containment [] (Effect(pi, RealTime rt1)) (Effect (pi, RealTime rt)) in
        if (re1 && re2) then Effect (pi, Emp) 
        else Effect (FALSE, Bot)
    | _ -> Effect (FALSE, Bot)

    )

  in 

  let rec checkDerivative (eff:effect) (fst:fst) : effect = 
    match eff with
      Effect (pi, es) -> derivative pi es fst
    | Disj (eff1, eff2) -> Disj (checkDerivative eff1 fst, checkDerivative eff2 fst) 
  in 

  let unfold eff1 eff2 del = 
    let fstL = checkFst eff1 in 
    let deltaNew = List.append [(eff1, eff2)] del  in

    let rec chceckResultAND li acc hypoacc:(bool * binary_tree list * inclusion list)=
      (match li with 
        [] -> (true, acc, hypoacc ) 
      | ev::fs -> 
          (*print_string ("\n"^string_of_Event ev^"\n\n");
          *)
          let deriL = checkDerivative eff1 ev in
          let deriR = checkDerivative eff2 ev in
          let (re,tree,  hypo) =  containment hypoacc deriL deriR in 
          if re == false then (false , tree::acc, [])
          else chceckResultAND fs (tree::acc) hypo
      )
    in 
    let (resultFinal, trees, hypy ) = chceckResultAND fstL [] deltaNew in 
    (resultFinal, Node (showEntail ^ "   [UNFOLD]",trees ), hypy)    
  in
  
  if ((nullableEffect normalFormL == true) && (nullableEffect normalFormR == false ))  then 
      (false, Node (showEntail ^ "   [NULLABLE]", []), evn)  
  else if reoccur evn normalFormL normalFormR then
      (
      print_string (List.fold_left (fun acc (a1, a2) -> acc ^ string_of_inclusion a1 a2) "" evn);
      (true, Node (showEntail ^ "   [REOCCUR]", []), evn)  
      )
  else 
  match (normalFormL, normalFormR) with 
      (*this means the assertion or precondition is already fail*)
    (Effect(FALSE, _), _) -> (true,  Node(showEntail ^ "   [Bot-LHS]", []), evn)  
  | (Effect(_, Bot), _) -> (true, Node(showEntail ^ "   [Bot-LHS]", []),  evn)  
  | (_, Effect(FALSE, _)) -> (false, Node(showEntail ^ "   [DISPROVE]", []),  evn)  
  | (_, Effect(_, Bot)) -> (false,Node(showEntail ^ "   [DISPROVE]", []),  evn)  
  | _ -> 
  
  unfold normalFormL normalFormR evn 
  
  
 
 
  ;;




let check_containment lhs rhs : (bool * binary_tree *  inclusion list) = 
  containment [] lhs rhs
  ;;

let printReport (lhs:effect) (rhs:effect) :string =

  let entailment = string_of_inclusion (normalEffect lhs) (normalEffect rhs) in 
  let startTimeStamp = Sys.time() in
  let (re, tree, hypos) =  check_containment lhs rhs in
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

