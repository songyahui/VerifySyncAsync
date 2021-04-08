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
  | Wait _ -> (raise (Foo "fst_simple: there is an unhandled wait"))
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
  | Wait _ -> (raise (Foo "fst: there is an unhandled wait"))
  | Instance ins ->  
    let newTV = getAnewVar_rewriting () in
    [(ins, newTV, PureAnd (pi, GtEq (Var newTV, Number 0)))]
  | Cons (es1 , es2) ->  if nullable es1 then append (fst pi es1) (fst pi es2) else fst pi es1
  | Choice (es1, es2) -> append (fst pi es1) (fst pi es2)
  | RealTime (Instance ins, rt) -> 
    let newTV = getAnewVar_rewriting () in
    [(ins, newTV, (PureAnd (pi, PureAnd(GtEq (Var newTV, Number 0), Eq (Var newTV, rt)) )))]
  | RealTime (es1, rt) -> 
    let ins_List = fst_simple es1 in 
    List.map 
    (fun ins ->
      let newTV = getAnewVar_rewriting () in
      (ins, newTV, PureAnd ((PureAnd (pi, GtEq (Var newTV, Number 0))), LtEq (Var newTV, rt)))
    ) ins_List
  | Kleene es1 -> fst pi es1
  | Par (es1 , es2) -> raise (Foo "Par should not be here in fst")
    (*let fst1 = fst pi es1 in
    let fst2 = fst pi  es2 in
    let combine = zip (fst1,  fst2) in 
    List.map (fun ((a, term1, pi1) , (b, term2, pi2)) -> 
      (List.append a b, term1, 
      (*PureAnd(PureAnd(pi1, pi2), Eq(Var term1, Var term2) )*)
      Eq(Var term1, Var term2)
      ))
       combine
       *)
;;




let rec appendEff_ES eff es:effect = 
  match eff with 
    [] -> []
  | (p , es_eff) :: xs -> (p, Cons (es_eff, es)):: appendEff_ES xs es
  
  (*
  
   | Disj (eff1 , eff2)  ->  Disj (appendEff_ES eff1 es, appendEff_ES eff2 es)
 
  raise ( Foo "appendEff_ES exception!")*)
  ;;







let rec checkFst (eff:effect) : fst list = 
  match eff with
    [] -> []
  | (pi, es) :: xs -> List.append (fst pi es)  (checkFst xs) 
  (*| Disj (eff1, eff2) -> append (checkFst eff1) (checkFst eff2) *)
 ;;

let rec nullableEffect (eff:effect) : bool = 
  match eff with 
    [] -> false
  | (pi, es):: xs -> (nullable es) ||  (nullableEffect  xs)
  (*| Disj (eff1, eff2) -> (nullableEffect eff1) || (nullableEffect eff2) *)
 ;;

let rec entailEffects (eff1:effect) (eff2:effect) : bool = 
  match (eff1, eff2) with 

    ( (p1, es1) ::xs,  (p2, es2)::ys) -> 
      if comparePure p1 p2 && compareES es1 es2  then true
      else false 
  | _ -> false 
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

let rec containTerm (term1:terms) (term2:terms) : bool = 
  match (term2) with 
  | Plus (t1, t2) -> stricTcompareTerm term1 t1 || containTerm term1 t2
  | Minus (t1, t2) -> stricTcompareTerm term1 t1 || containTerm term1 t2
  | _ -> stricTcompareTerm term1 term2
  ;;

let rec getReleventC p t : pure = 
  print_string(string_of_pure p^"\n");
  print_string(string_of_terms t^"\n");
  match p with 
    Eq (t1, t2) -> if containTerm t t1 || containTerm t t2 then p else TRUE
  | PureOr (p1, p2) -> PureOr (getReleventC p1 t , getReleventC p2 t )
  | PureAnd (p1, p2) -> PureAnd (getReleventC p1 t , getReleventC p2 t )
  | Gt (t1, t2) -> if containTerm t t1 || containTerm t t2 then p else TRUE
  | Lt (t1, t2) -> if containTerm t t1 || containTerm t t2 then p else TRUE
  | GtEq (t1, t2) -> if containTerm t t1 || containTerm t t2 then p else TRUE
  | LtEq (t1, t2) -> if containTerm t t1 || containTerm t t2 then p else TRUE
  | TRUE -> TRUE
  | FALSE -> TRUE
  | Neg p1 -> Neg (getReleventC p1 t)


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

let disjEffects eff : effect = 
  normalEffect(
  [List.fold_left (fun (pi_acc, es_acc) (pi, es) -> (PureAnd (pi_acc, pi), Choice (es_acc, es))) (TRUE, Bot) eff
  ]
    )  ;;

let rec getEqFromPure p : pure = 
  match p with 
    Eq (t1, t2) -> p 
  | PureOr (p1, p2) -> PureOr (getEqFromPure p1, getEqFromPure p2)
  | PureAnd (p1, p2) -> PureAnd (getEqFromPure p1, getEqFromPure p2)
  | _ -> TRUE
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

let rec allVarsFromTerm (t:terms): string list =
  match t with
    Var name -> [name]
  | Number n -> []
  | Plus (t1, t2) -> List.append (allVarsFromTerm t1) (allVarsFromTerm t2)
  | Minus (t1, t2) -> List.append (allVarsFromTerm t1) (allVarsFromTerm t2)

  ;;

let rec allVarsFromPure p : string list = 
  match p with 
  | TRUE -> []  
  | FALSE -> []
  | Gt (t1, t2) -> List.append (allVarsFromTerm t1) (allVarsFromTerm t2) 
  | Lt (t1, t2) -> List.append (allVarsFromTerm t1) (allVarsFromTerm t2) 
  | GtEq (t1, t2) -> List.append (allVarsFromTerm t1) (allVarsFromTerm t2) 
  | LtEq (t1, t2) -> List.append (allVarsFromTerm t1) (allVarsFromTerm t2) 
  | Eq (t1, t2) -> List.append (allVarsFromTerm t1) (allVarsFromTerm t2) 
  | PureOr (p1, p2) -> List.append (allVarsFromPure p1) (allVarsFromPure p2) 
  | PureAnd (p1, p2) -> List.append (allVarsFromPure p1) (allVarsFromPure p2) 
  | Neg (p1) -> (allVarsFromPure p1) 
  ;;

let rec oneOfVar str big : bool =
  match big with 
  | [] -> false 
  | x::xs -> if String.compare x str == 0 then true else oneOfVar str xs
  ;;

let rec existCommon small big : bool =
  match small with 
  | [] -> false 
  | x::xs -> if oneOfVar x big then true else existCommon xs big 
  ;;

let getRelavantConstrain (unify:pure) (pi:pure) : pure = 
  let var_Li = allVarsFromPure unify in
  let rec aux p:pure = 
    match p with 
    | TRUE -> p 
    | FALSE -> p
    | Gt (t1, t2) -> 
      let v1 = allVarsFromTerm t1 in 
      let v2 = allVarsFromTerm t2 in 
      if existCommon (List.append v1 v2) var_Li then p else TRUE
    | Lt (t1, t2) -> 
      let v1 = allVarsFromTerm t1 in 
      let v2 = allVarsFromTerm t2 in 
      if existCommon (List.append v1 v2) var_Li then p else TRUE
    | GtEq (t1, t2) -> 
      let v1 = allVarsFromTerm t1 in 
      let v2 = allVarsFromTerm t2 in 
      if existCommon (List.append v1 v2) var_Li then p else TRUE
    | LtEq (t1, t2) -> 
      let v1 = allVarsFromTerm t1 in 
      let v2 = allVarsFromTerm t2 in 
      if existCommon (List.append v1 v2) var_Li then p else TRUE
    | Eq (t1, t2) -> 
      let v1 = allVarsFromTerm t1 in 
      let v2 = allVarsFromTerm t2 in 
      if existCommon (List.append v1 v2) var_Li then p else TRUE
    | PureOr (p1, p2) -> PureOr (aux p1, aux p2)
    | PureAnd (p1, p2) -> PureAnd (aux p1, aux p2)
    | Neg (p1) -> Neg (aux p1)
  in aux pi
  ;;

let rec derivative (pi :pure) (es:es) (fst:fst) (unify:pure): (pure * effect) = 
  let (fst_ins, fst_terms, fst_pure) = fst in 
  match es with
    Bot ->  (unify, [])
  | Emp ->  (unify, [])
  | Wait _ -> (raise (Foo "derivative: there is an unhandled wait"))
  | Instance ins ->  

          if instansEntails fst_ins ins then (unify, [(pi, Emp)] )
          else (unify, [])
      

  (*| Ttimes (es1, t) -> 
      let pi = PureAnd (Gt (t, Number 0), pi) in
      let efF = derivative pi es1 fst in 
      let esT_minus1 = Ttimes (es1,  Minus (t, Number 1)) in
      appendEff_ES efF esT_minus1*)
  | Cons (es1 , es2) ->  
      if nullable es1 
      then let (u1, efF) = derivative pi es1 fst unify in 
          let effL =  (appendEff_ES efF es2) in 
          let (u2, effR) =  (derivative pi es2 fst unify) in 
          (PureAnd(u1, u2), disjEffects (List.append effL effR))
      else let (u1, efF) = derivative pi es1 fst unify in 
          (u1, appendEff_ES efF es2 )   
  | Choice (es1, es2) -> 
      let (u1, temp1) =  (derivative pi es1 fst unify) in
      let (u2, temp2) =  (derivative pi es2 fst unify) in 
      (PureAnd(u1, u2), disjEffects (List.append temp1 temp2))
  | RealTime (Instance insR, rt) -> 
      if instansEntails fst_ins insR 
      then 
        let new_unify = PureAnd(unify, Eq (rt, Var fst_terms)) in 
        let left = normalPure (PureAnd (new_unify, fst_pure)) in 
        let right = normalPure (getRelavantConstrain new_unify pi) in 
        print_string (string_of_pure left ^" ==> "^ string_of_pure right ^ "\n");
        print_string (string_of_bool (entailConstrains1 left right)^"\n");
        if entailConstrains left right then 
        (new_unify, [(pi, Emp)])
        else (new_unify, [])
      else (unify, [])

    
  | RealTime (es1, rt) -> 
    let (unify_temp, effect_temp) = derivative pi es1 fst unify in 
    let ele_list = normalEffect effect_temp in
    let sssyyyhhh = List.fold_left (fun acc (pi_temp, es_temp)-> 
      (let newT1 = getAnewVar_rewriting () in
      let newT2 = getAnewVar_rewriting () in
      let new_unify = PureAnd (Eq (Plus(Var newT1, Var newT2), rt), Eq(Var newT1, Var fst_terms)) in 
     
      (new_unify, (pi_temp, RealTime (es_temp, Var newT2))) :: acc
      (*else acc*)
    )) [] ele_list in 
    List.fold_left (fun (acc_u, acc_e) (u, e) -> (PureAnd(acc_u, u), e::acc_e)) (unify_temp, []) sssyyyhhh
    
    


  | Kleene es1 -> 
    let (new_unify, new_eff) = derivative pi es1 fst unify in 
    (new_unify, appendEff_ES  (new_eff) es)
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
  | Par (es1, es2) -> 
    let (u1, ele_list1) = derivative pi es1 fst unify in 
    let (u2, ele_list2) = derivative pi es2 fst unify in 
    let eles = zip (ele_list1, ele_list2) in 
    (PureAnd (u1, u2)
      ,List.map (fun ((pp1, ees1), (pp2, ees2) ) -> 
    (PureAnd (pp1, pp2), Par (ees1, ees2 ))
    ) eles
    )

;;

                                                                (* unification *)
let rec containment (evn: inclusion list) (lhs:effect) (rhs:effect) (unify:pure) : (pure * bool * binary_tree *  inclusion list) = 
  
  let normalFormL = normalEffect lhs in 
  let normalFormR = normalEffect rhs in 
  let showEntail = string_of_inclusion normalFormL normalFormR in 

  let rec checkDerivative eff (fst:fst) : (pure* effect) = 
    
    List.fold_left (fun (u_acc, e_acc) (pi, es) -> 
      let (new_unify, der) = derivative pi es fst unify in 
      (PureAnd(u_acc, new_unify) , List.append (der) e_acc)
      ) (unify, [])  eff 
   
  in 

  let unfold eff1 eff2 del = 
    let fstL = checkFst eff1 in 
    let deltaNew = List.append [(eff1, eff2)] del  in

    let rec chceckResultAND li acc hypoacc:(pure* bool * binary_tree list * inclusion list)=
      (match li with 
        [] -> (unify, true, acc, hypoacc ) 
      | ev::fs -> 
          
          let (unify_left, deriL) = checkDerivative eff1 ev in
          
          let (unify_right, deriR) = checkDerivative eff2 ev in
          let (new_unify, re,tree,  hypo) =  containment hypoacc deriL deriR (PureAnd(unify_left, unify_right)) in 
          if re == false then (new_unify, false , tree::acc, [])
          else chceckResultAND fs (tree::acc) hypo
      )
    in 
    let (unify_final, resultFinal, trees, hypy ) = chceckResultAND fstL [] deltaNew in 
    (unify_final, resultFinal, Node (showEntail ^ "   [UNFOLD]",trees ), hypy)    
  in
  
  
  match (normalFormL, normalFormR) with 
      (*this means the assertion or precondition is already fail*)
    ([], _) -> (unify, true,  Node(showEntail ^ "   [Bot-LHS]", []), evn)  
  | (_, []) -> (unify, false, Node(showEntail ^ "   [DISPROVE]", []),  evn)  
  | _ ->

  if ((nullableEffect normalFormL == true) && (nullableEffect normalFormR == false ))  then 
      (unify, false, Node (showEntail ^ "   [NULLABLE]", []), evn)  
  else if reoccur evn normalFormL normalFormR then
      (
      (*
      print_string (List.fold_left (fun acc (a1, a2) -> acc ^ string_of_inclusion a1 a2) "" evn);
      *)
      (unify, true, Node (showEntail ^ "   [REOCCUR]", []), evn)  
      )
  else 
  
  unfold normalFormL normalFormR evn 
  
;;


(* no mixed usage of t and || *)

let check_containment lhs rhs : (pure*bool * binary_tree *  inclusion list) = 
  (*
  let lhs' = matchAsyncAwaitEffect lhs in 
  let rhs' = matchAsyncAwaitEffect rhs in 
  *)
  containment [] lhs rhs TRUE
  ;;

let printReport (lhs:effect) (rhs:effect) (expectation:bool):(string* bool) =

  let entailment = string_of_inclusion (normalEffect lhs) (normalEffect rhs) in 
  let startTimeStamp = Sys.time() in
  let (_, re, tree, hypos) =  check_containment lhs rhs in
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

