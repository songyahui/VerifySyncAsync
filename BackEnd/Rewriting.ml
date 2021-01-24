open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Sys
open Askz3

let rec zip (ls:'a list * 'b list) : ('a * 'b) list =
  let (xs,ys) = ls in
  match (xs,ys) with
      ([],_) -> []
    | (_,[]) -> []
    | (x::xrest, y::yrest) -> (x,y)::zip (xrest,yrest)
;;

let rec fst_simple (es:es): instance list= 
  match es with
    Bot -> []
  | Emp -> []
  | Instance ins ->  [(ins)]
  | Cons (es1 , es2) ->  if nullable es1 then append (fst_simple  es1) (fst_simple  es2) else fst_simple  es1
  | Choice (es1, es2) -> append (fst_simple  es1) (fst_simple  es2)
  | RealTime (es1, rt) -> fst_simple es1
  | Kleene es1 -> fst_simple  es1
  | Par (es1 , es2) -> 
    let fst1 = fst_simple es1 in
    let fst2 = fst_simple es2 in
    let combine = zip (fst1,  fst2) in 
    List.map (fun (a, b) -> List.append a b) combine
;;

let rec fst (pi:pure) (es:es): fst list =
  match es with
    Bot -> []
  | Emp -> []
  | Instance ins ->  
    let newTV = getAnewVar_rewriting in
    [(ins, newTV, PureAnd (pi, GtEq (Var newTV, Number 0)))]
  | Cons (es1 , es2) ->  if nullable es1 then append (fst pi es1) (fst pi es2) else fst pi es1
  | Choice (es1, es2) -> append (fst pi es1) (fst pi es2)
  | RealTime (Instance ins, rt) -> 
    let newTV = getAnewVar_rewriting in
    [(ins, newTV, (PureAnd (pi, PureAnd(GtEq (Var newTV, Number 0), Eq (Var newTV, rt)) )))]
  | RealTime (es1, rt) -> 
    let ins_List = fst_simple es1 in 
    List.map 
    (fun ins ->
      let newTV = getAnewVar_rewriting in
      (ins, newTV, PureAnd ((PureAnd (pi, GtEq (Var newTV, Number 0))), LtEq (Var newTV, rt)))
    
    ) ins_List
  | Kleene es1 -> fst pi es1
  | Par (es1 , es2) -> 
    let fst1 = fst pi es1 in
    let fst2 = fst pi  es2 in
    let combine = zip (fst1,  fst2) in 
    List.map (fun ((a, term1, pi1) , (b, term2, pi2)) -> 
      (List.append a b, term1, PureAnd(PureAnd(pi1, pi2), Eq(Var term1, Var term2) )))
       combine
;;




let rec appendEff_ES eff es = 
  match eff with 
    (p , es_eff) -> (p, Cons (es_eff, es))
  
  (*
  
   | Disj (eff1 , eff2)  ->  Disj (appendEff_ES eff1 es, appendEff_ES eff2 es)
 
  raise ( Foo "appendEff_ES exception!")*)
  ;;


let ifShouldDisj (temp1:effect) (temp2:effect) : effect = 
  match (temp1, temp2) with
      ((pure1, evs1), (pure2, evs2)) -> 
        (PureAnd(pure1, pure2),  Choice (evs1, evs2))
;;




let rec checkFst (eff:effect) : fst list = 
  match eff with
   (pi, es) -> fst pi es
  (*| Disj (eff1, eff2) -> append (checkFst eff1) (checkFst eff2) *)
 ;;

let rec nullableEffect (eff:effect) : bool = 
  match eff with 
   (pi, es) -> nullable es
  (*| Disj (eff1, eff2) -> (nullableEffect eff1) || (nullableEffect eff2) *)
 ;;

let rec entailEffects (eff1:effect) (eff2:effect) : bool = 
  match (eff1, eff2) with 
    ( (p1, es1),  (p2, es2)) -> 
      if comparePure p1 p2 && compareES es1 es2 then true 
      else false 
  (*| (Disj (f1, f2), Disj (f3, f4)) -> 
  (entailEffects f1 f3 && entailEffects f2 f4) || (entailEffects f2 f3 && entailEffects f1 f4)
  | _ -> false 
  *)
;;

let rec getVarFromTerms (t:terms): string list = 
  match t with 
    Var str -> [str]
  | Number _ -> []
  | Plus (t1, t2) -> List.append (getVarFromTerms t1) (getVarFromTerms t2)
  | Minus (t1, t2) -> List.append (getVarFromTerms t1) (getVarFromTerms t2)
  ;;

let rec getPureForTerms (fst_terms:terms) (fst_pure: pure) : pure = 
  (*let var_List = getVarFromTerms fst_terms in 
  let rec helper pi acc = 
    match pi with 
      TRUE -> acc 
    | FALSE -> acc
    | Gt (t1, t2) -> List.fold 
    | Lt of terms * terms
    | GtEq of terms * terms
    | LtEq of terms * terms
    | Eq of terms * terms
    | PureOr of pure * pure
    | PureAnd of pure * pure
    | Neg of pure

  in helper fst_pure TRUE
  *)
  fst_pure

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

let rec derivative (pi :pure) (es:es) (fst:fst) : effect = 
  let (fst_ins, fst_terms, fst_pure) = fst in 
  match es with
    Bot ->  (FALSE, Bot)
  | Emp ->  (FALSE, Bot)
  | Instance ins ->  

          if instansEntails fst_ins ins then (pi, Emp) 
          else (FALSE, Bot)
      

  (*| Ttimes (es1, t) -> 
      let pi = PureAnd (Gt (t, Number 0), pi) in
      let efF = derivative pi es1 fst in 
      let esT_minus1 = Ttimes (es1,  Minus (t, Number 1)) in
      appendEff_ES efF esT_minus1*)
  | Cons (es1 , es2) ->  
      if nullable es1 
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
  | RealTime (Instance insR, rt) -> 
      if instansEntails fst_ins insR 
      then 
        let pure1 =  fst_pure in 
        let pure2 =  pi in 
        let pure_plus = Eq (rt, Var fst_terms) in 
        (*print_string ("\n********************\n");
        print_string (string_of_pure (PureAnd (pure1, pure_plus)));
        print_string ("\n==>\n");
        print_string (string_of_pure pure2 ^"\n");
        print_string (string_of_bool (entailConstrains1 (PureAnd (pure1, pure_plus)) pure2 )^"\n");
        *)
        if entailConstrains1 (PureAnd (pure1, pure_plus)) pure2 then 
        (pi, Emp) 
        else (FALSE, Bot)
      else (FALSE, Bot)

    
  | RealTime (es1, rt) -> 
    let (pi_temp, es_temp) = normalEffect (derivative pi es1 fst) in
    let newTV = getAnewVar_rewriting in
    let pi_new = PureAnd (Lt (Var newTV, rt), Eq(Var newTV, Var fst_terms)) in 
    if entailConstrains1 (pi_new) TRUE then 
    (pi_new, es_temp)
    else (FALSE, Bot)  
    
    


  | Kleene es1 -> appendEff_ES  (derivative pi es1 fst) es
 (*
  | Par (es1 , es2) -> 
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
 *)
  | Par (_, _) -> raise (Foo "derivative par")

;;


let rec containment (evn: inclusion list) (lhs:effect) (rhs:effect) : (bool * binary_tree *  inclusion list) = 
  
  let normalFormL = normalEffect lhs in 
  let normalFormR = normalEffect rhs in 
  let showEntail = string_of_inclusion normalFormL normalFormR in 

  let rec checkDerivative (eff:effect) (fst:fst) : effect = 
    match eff with
     (pi, es) -> derivative pi es fst
    (*| Disj (eff1, eff2) -> Disj (checkDerivative eff1 fst, checkDerivative eff2 fst) *)
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
      (*
      print_string (List.fold_left (fun acc (a1, a2) -> acc ^ string_of_inclusion a1 a2) "" evn);
      *)
      (true, Node (showEntail ^ "   [REOCCUR]", []), evn)  
      )
  else 
  match (normalFormL, normalFormR) with 
      (*this means the assertion or precondition is already fail*)
    ((FALSE, _), _) -> (true,  Node(showEntail ^ "   [Bot-LHS]", []), evn)  
  | ((_, Bot), _) -> (true, Node(showEntail ^ "   [Bot-LHS]", []),  evn)  
  | (_, (FALSE, _)) -> (false, Node(showEntail ^ "   [DISPROVE]", []),  evn)  
  | (_, (_, Bot)) -> (false,Node(showEntail ^ "   [DISPROVE]", []),  evn)  
  | _ -> 
  
  unfold normalFormL normalFormR evn 
  
;;


(* no mixed usage of t and || *)

let check_containment lhs rhs : (bool * binary_tree *  inclusion list) = 
  (*
  let lhs' = matchAsyncAwaitEffect lhs in 
  let rhs' = matchAsyncAwaitEffect rhs in 
  *)
  containment [] lhs rhs
  ;;

let printReport (lhs:effect) (rhs:effect) (expectation:bool):(string* bool) =

  let entailment = string_of_inclusion (normalEffect lhs) (normalEffect rhs) in 
  let startTimeStamp = Sys.time() in
  let (re, tree, hypos) =  check_containment lhs rhs in
  let verification_time = "[Verification Time: " ^ string_of_float (Sys.time() -. startTimeStamp) ^ " s]\n" in
  let result = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  let correct = if (expectation ==re) then "[Correct]" else "[Incorrect]" in 
  let buffur = ( "----------------------------------------"^"\n" ^(entailment)^"\n[Result] " ^(if re then "Succeed     " else "Fail     ")^ ( correct) ^"\n"  ^verification_time^" \n\n"^ result)
  in (buffur, (expectation ==re))
  
  ;;

(*
let main = 
  let (re, temp) = in 
  let tree = printTree ~line_prefix:"* " ~get_name ~get_children temp in 

  print_string (tree);
  *)

