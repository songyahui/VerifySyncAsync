open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Rewriting
open Sys


(*
let rec can_fun (s:var) (prog:prog) (origin: prog) (full:spec_prog list) :bool = 
  match prog with 
    Nothing -> false 
  | Pause -> false 
  | Seq (p1, p2) -> can_fun s p1 origin full || can_fun s p2 origin full
  | Par (p1, p2) -> can_fun s p1 origin full || can_fun s p2 origin full
  | Loop p -> can_fun s p origin full
  | Declear (v, p) -> can_fun s p origin full
  | Emit str -> if String.compare str s == 0 then true else false 
  | Present (v, p1, p2) -> 
    (*if can_fun v origin origin full then *)
     can_fun s p1 origin full || can_fun s p2 origin full 
     (*else can_fun s p2 origin full*)
  | Trap (mn, p) -> can_fun s p origin full
  | Exit _ -> false 
  | Run proIn -> 
    let rec helper modules = 
        match modules with 
          [] -> raise (Foo ("module "^proIn ^"undefined"))
        | x::xs -> 
        let (name, _, _, _, _, _) = x in
        if String.compare name proIn == 0 then x else helper xs 
      in 
      let (_, in_callee, out_callee, pre_callee, post_callee, body_calles) = helper full in 
      can_fun s body_calles body_calles full
  | Suspend (p, s) -> can_fun s p origin full
  ;;

  

let rec p_es_To_state (es:p_es) :prog_states = 
  let es = normalPES es in 
  match es with 
  | PEmp -> [(PEmp, None, None)]
  | PInstance ins -> [(PEmp, Some ins, None)]
  | PCon (es1, es2) -> 
    let his_cur_list = p_es_To_state es2 in 
    List.map (fun (his,cur,trap) -> (PCon (es1, his),cur, trap)) his_cur_list
    
  | PDisj (es1, es2) -> List.append (p_es_To_state es1) (p_es_To_state es2)
  | PKleene esIn -> 
    let his_cur_list = p_es_To_state esIn in 
    List.map (fun (his,cur, trap) -> (PCon (es, his), cur, trap)) his_cur_list
  | POmega esIn -> 
    let his_cur_list = p_es_To_state esIn in 
    List.map (fun (his,cur, trap) -> (PCon (es, his), cur, trap)) his_cur_list
  | PNtimed (esIn, n) ->
    assert (n>1);
    let his_cur_list = p_es_To_state esIn in 
    List.map (fun (his,cur, trap) -> (PCon (PNtimed (esIn, n-1), his), cur, trap)) his_cur_list

  | PBot -> raise (Foo "there is a BOT HERE")
  ;;


let rec state_To_p_es (state:prog_states):p_es = 
  (* normalPES *)
   (
  List.fold_left (fun acc (a, b, trap) -> 
  match b with 
    None -> PDisj (acc, a)
  | Some b -> 
  PDisj (acc, (PCon (a, PInstance b)))) PBot state
  )
  ;;






let rec zip a b =
  match (a,b) with
    ([],[]) -> []
    | ([],n::ns)-> []
    | (n::ns,[]) -> []
    | (k::ks, h::hs) -> (k,h)::zip ks hs ;;


let rec split_p_es_head_tail (es:p_es) :(p_instance * p_es) list = 
  match es with 
  | PInstance ins -> [(ins, PEmp)]
  | PCon (es1, es2) -> 
    let head_tail_list = split_p_es_head_tail es1 in 
    List.map (fun (head,tail) -> (head, PCon (tail, es2))) head_tail_list
    
  | PDisj (es1, es2) -> List.append (split_p_es_head_tail es1) (split_p_es_head_tail es2)
  | PKleene esIn -> 
    let head_tail_list = split_p_es_head_tail esIn in 
    List.map (fun (head,tail) -> (head, PCon (tail, es))) head_tail_list
  | PNtimed (esIn, n) ->
    assert (n>1);
    let head_tail_list = split_p_es_head_tail esIn in 
    List.map (fun (head,tail) -> (head, PCon (tail, PNtimed (esIn, n-1)))) head_tail_list

  | _ -> raise (Foo "there is a EMP OR BOT HERE in split_p_es_head_tail")
  ;;

let isEmp xs : bool = 
  let noneZero = List.filter (fun a ->
    match a with
      Zero _ -> false
    | _ -> true 
  ) xs   in 
  match noneZero with 
    [] -> true 
  | _ -> false 
;;

let rec filterZero (pes:p_es) : p_es = 
  match pes with 
  | PBot -> PBot
  | PEmp -> PEmp
  | PInstance (p, ins) -> 
  PInstance (p, 
    List.filter (
      fun a -> 
        match a with  
        Zero _ -> false 
      | One _ -> true 
    ) ins )
  | PCon (es1, es2) ->PCon (filterZero es1, filterZero es2)
  | PDisj (es1, es2) ->PDisj (filterZero es1, filterZero es2)
  | PKleene (es1) -> PKleene( filterZero es1)
  | POmega (es1) -> POmega (filterZero es1)
  | PNtimed (es1, n) -> PNtimed (filterZero es1, n)
  ;;

let rec paralleEffLong es1 es2 : p_es = 
  let norES1 = normalPES es1 in 
  let norES2 = normalPES es2 in 
  let norES1 = filterZero norES1 in 
  let norES2 = filterZero norES2 in 
  let fst1 = getFstPes norES1 in
  let fst2 = getFstPes norES2 in 
  let headcom = zip fst1 fst2 in 

  let listPES =  List.map (fun (f1, f2) -> 
  let der1 = derivativePes f1 norES1 in 
  let der2 = derivativePes f2 norES2 in 
  match (der1, der2) with 
    (PEmp, _) -> PCon (PInstance (appendSL f1 f2), der2)
  | (_, PEmp) -> PCon (PInstance (appendSL f1 f2), der1)
  | _ -> PCon (PInstance (appendSL f1 f2), paralleEffLong der1 der2)) headcom
  in
  normalPES (
  List.fold_left (fun acc a -> PDisj (acc, a)) PBot listPES
  )

   ;;

 


let rec lengthPES es : int =
  match es with  
| PEmp -> 0
| PInstance _ -> 1 
| PCon (es1, es2) -> lengthPES es1 + lengthPES es2

| PNtimed (es1, n) -> (lengthPES es1) * n
| _ -> raise (Foo "getlength error ")
;;

let equla_List_of_State left right : bool= 
  true
  ;;






*)


(*
let setState (xs:instance) (s:string) (flag:int):instance =  (* flag 0 - Zero, 1- One, 2-Wait *)
  let rec helper li acc = 
  match li with 
    [] -> acc
  | x::xxs -> 
    match x with 
      (Zero str) -> if String.compare str s == 0 then List.append (List.append xxs acc) 
      [(if flag == 1 then One s else if flag == 0 then Zero s else Wait s)]
                    else helper xxs (List.append acc [x])
    | _ -> helper xxs (List.append acc [x])
  in helper xs [];
  ;;
  *)

let rec isPresent name curr : bool = 
  match curr with 
    [] -> false 
  | (One n)::xs -> if (String.compare n name == 0) then true else isPresent name xs 
  | (_) :: xs -> isPresent name xs 
  ;;

let make_nothing (evn: string list) : instance = 
  List.map (fun (a) ->   
  (Zero a) ) evn 
  ;;

(*

let rec append_es_to_effect es eff : effect = 
  match eff with 
    Effect (p , es1) -> Effect (p, Cons(es1, es))
  | Disj (eff1, eff2) -> Disj (append_es_to_effect es eff1, append_es_to_effect es eff2)
  ;;
  
  *)
let rec findProg name full:spec_prog = 
  match full with 
  | [] -> raise (Foo ("function " ^ name ^ " is not found!"))
  | x::xs -> let (str, _, _, _, _, _) = x in 
              if String.compare str name == 0 then x 
              else findProg name xs
;;
  
let rec append_ins_to_es (ins:instance)  (es:es) : es = 
  Cons(es, Instance ins)
  ;;

let rec lengthOfEs es : int =
  match es with 
    Bot -> raise (Foo "Bot does not have length")
  | Emp -> 0
  | Wait s -> 1
  | Instance _ -> 1
  | Cons (es1, es2) -> lengthOfEs es1 + lengthOfEs es2
  | Choice (es1, es2) -> if lengthOfEs es1 > lengthOfEs es2 then lengthOfEs es1 else lengthOfEs es2
  | Par (es1, es2) -> if lengthOfEs es1 > lengthOfEs es2 then lengthOfEs es1 else lengthOfEs es2
  | RealTime (es1, _) -> lengthOfEs es1 
  | Kleene es1 -> lengthOfEs es1 
  ;;

let rec splitEffects (es:es) (pi:pure) :(pure* es* instance) list = 
  match es with 
    Bot -> []
  | Emp -> [(pi, Emp, [])]
  | Wait s -> [(pi, Wait s, [])]

  | Instance ins -> [(pi, Emp, ins)]
  | Cons (es1, es2) -> 
    let temp = splitEffects es2 pi in 
    List.map (fun (pi2, es2, ins2) -> 
      (pi2, Cons (es1, es2), ins2)
    ) temp
  | Choice (es1, es2) -> 
    List.append (splitEffects es1 pi ) (splitEffects es2 pi)
  | Par (es1, es2) -> 
    let len1 = lengthOfEs es1 in 
    let len2 = lengthOfEs es2 in 
    if len1 > len2 then 
      let temp = splitEffects es1 pi in 
      List.map (fun (p, e, i) -> (p, Par (e, es2), i)) temp
    else if len1 < len2 then 
      let temp = splitEffects es2 pi in 
      List.map (fun (p, e, i) -> (p, Par (e, es1), i)) temp
    else 
      let temp1 = splitEffects es1 pi in 
      let temp2 = splitEffects es2 pi in 
      let combine = zip (temp1, temp2) in 
      List.map (fun ((p1, e1, i1), (p2, e2, i2)) -> (PureAnd(p1, p2), Par(e1, e2), List.append i1 i2)) combine

  | RealTime (es1, t) -> 
    let temp = splitEffects es1 pi in 
    List.map (fun (p, e, i) -> 
    let newTV = getAnewVar_rewriting () in
    (PureAnd(p, LtEq(Var newTV, t)), RealTime (e, Var newTV), i)
    
    ) temp 
    
  | Kleene es1 -> [(pi, es, [])]


  ;;

let rec fstPar (es) :parfst list = 
  match es with 
    Bot -> []
  | Emp -> []
  | Wait s -> [(W s)] 
  | Instance ins ->  [(SL ins)]
  | Cons (es1 , es2) ->  if nullable es1 then append (fstPar  es1) (fstPar  es2) else fstPar  es1
  | Choice (es1, es2) -> append (fstPar  es1) (fstPar  es2)
  | RealTime (es1, rt) -> fstPar es1
  | Kleene es1 -> fstPar  es1
  | Par (es1 , es2) -> 
    (raise (Foo "should not be here fstPar"))
    (*let fst1 = fstPar es1 in
    let fst2 = fstPar es2 in
    let combine = zip (fst1,  fst2) in 
    List.map (fun (a, b) -> 
    
    List.append a b) combine
    *)
  

    ;;

let rec isSigOne s ins: bool  =
  match ins with 
    [] -> false
  | (One e) :: xs -> if String.compare e s == 0 then true else isSigOne s xs 
  | x::xs -> isSigOne s xs 
  ;;


let rec derivativePar (fst: parfst) es :es =
  match es with 
    Bot ->  Bot
  | Emp ->  Bot
  | Wait s -> 
    (
      match fst with 
        W f ->  if String.compare f s == 0 then Emp else Bot
      | SL ins -> if isSigOne s ins then Emp else Bot
    )
  | Instance ins ->  
    (
      match fst with 
        W f ->  if isSigOne f ins then Emp else Bot
      | SL f -> if instansEntails f ins then Emp else Bot
    )
    
  | Cons (es1 , es2) -> 
      let esF = derivativePar fst es1  in 
      let esL = Cons(esF,  es2) in  
      if nullable es1 
      then 
          let esR =  derivativePar fst es2 in 
          Choice (esL, esR)
      else esL

  | Choice (es1, es2) -> 
      let temp1 =  derivativePar fst es1  in
      let temp2 =  derivativePar fst es2  in 
      Choice (temp1,temp2)


  

  ;;




let rec parallelES pi1 pi2 es1 es2 : (pure * es) =
  let norES1 = normalES es1 pi1 in 
  let norES2 = normalES es2 pi2 in 
  print_string ("\n");
  print_string (string_of_es norES1 ^"\n===\n");
  print_string (string_of_es norES2 );
  let fst1 = fstPar norES1 in
  let fst2 = fstPar norES2 in 
  let headcom = zip (fst1, fst2) in 
  let esLIST = List.map (
  fun (f1, f2) -> 

    let der1 = normalES  (derivativePar f1 norES1) pi1 in 
    let der2 = normalES  (derivativePar f2 norES2) pi2 in 

    match (f1, f2) with  
      (W _, W _ ) -> raise (Foo "there is a deadlock")
    | (W s, SL ins) -> 
      if isSigOne s ins then 
        parallelES pi1 pi2 der1 der2
      else 
        let (p, es) = parallelES pi1 pi2 es1 der2  in 
        (p, Cons (Instance ins, es))
    | (SL ins, W s) -> 
      if isSigOne s ins then 
        parallelES pi1 pi2 der1 der2
      else 
        let (p, es) = parallelES pi1 pi2 der1 es2  in 
        (p, Cons (Instance ins, es))
    | (SL ins1, SL ins2) -> 
      (match (der1, der2) with 
      | (Emp, _) -> (TRUE, Cons (Instance (List.append ins1 ins2), der2))
      | (_, Emp) -> (TRUE, Cons (Instance (List.append ins1 ins2), der1))
      | (der1, der2) -> 
        let (pi, es) = (parallelES pi1 pi2 der1 der2) in 
        (pi, Cons (Instance (List.append ins1 ins2), es))
      
    ) 




    
  ) headcom
  in List.fold_left (fun (pacc, esacc) (p, e) -> (PureAnd(pacc, p), Choice(esacc, e)))  (PureAnd(pi1, pi2), Bot) esLIST


  
 ;;

let rec forward (env: string list) (current:prog_states) (prog:prog) (full: spec_prog list): prog_states =

  match prog with 
    Halt -> current
  | Yield -> 
    List.map (fun (pi, his, cur, k) -> (pi, Cons (his,Instance cur) , [](*make_nothing env *), k))  current
  
  | Emit (s) -> 
    List.map (fun (pi, his, cur, k) ->(pi, his , ((One s)::cur )(*setState cur s 1*), k))  current (* flag 0 - Zero, 1- One, 2-Wait *)
  | Await (s) -> 
    List.map (fun (pi, his, cur, k) ->(pi, Cons (his, Cons(Wait s , Instance cur)) , [] (*setState cur s 2*), k))  current (* flag 0 - Zero, 1- One, 2-Wait *)

  | Present (s, p1, p2) ->
    List.fold_left (fun acc (pi, his, cur, k) -> 
      List.append acc (
          if isPresent s cur then forward env current p1 full 
          else forward env current p2 full) 
    ) [] current

  | Declear (s , p) -> 
    forward (List.append env [s]) current p full 

  | Async (s, p, delay) -> 
    List.map (fun (pi1, his1, cur1, k1) ->
      let term = Var getAnewVar in 
      (PureAnd (pi1, GtEq (term, Number delay)), RealTime (Cons (his1, Instance cur1), term), [(One s)](*setState (make_nothing env) s 1*), k1)
        ) (forward env current p full)

  | Assert eff -> 

      let (re, _, _) = check_containment (List.map (fun (pi, his, cur, k) -> (pi, Cons(his, Instance cur))) current) eff in 
      if re then current 
      else raise (Foo "assertion failed")
   
  | Seq (p1, p2) -> 
    
    List.fold_left (fun acc (pi1, his1, cur1, k1) ->  
    List.append acc (  
    (match k1 with 
      Some str -> [(pi1, his1, cur1, k1)] 
    | None -> forward env [(pi1, his1, cur1, k1)] p2 full
    )
    )
    ) [] ( forward env current p1 full)
    

  | Trap (mn, p1) -> 
    List.fold_left (fun acc (pi1, his1, cur1, k1) ->  
      List.append acc (  
    
    [(match k1 with 
      Some str -> if String.compare str mn == 0 then (pi1, his1, cur1, None) else (pi1, his1, cur1, k1)
    | None -> (pi1, his1, cur1, k1)
    )]
      )
    ) [] ( forward env current p1 full)

  | Break name -> 
    List.map (fun (pi, his, cur, k) ->
      (match k with 
        Some str -> (pi, his, cur, k)
      | None -> (pi, his, cur, Some name)
      )
    ) current

  | Abort (delay, p) ->
    List.map (fun (pi1, his1, cur1, k1) ->
    let term = Var getAnewVar in 
    (PureAnd (pi1, Lt (term, Number delay)), RealTime (Cons (his1, Instance cur1),  term) , [] (*make_nothing env*), k1)
    )
    (forward env current p full)

  | Run mn ->
  List.fold_left (fun acc (pi, his, cur, k) ->

    List.append acc (  
      let (fun_name, inp, outp, precon, postcon, _) = findProg mn full in 
      let (re, _, _) = check_containment [(pi, Cons (his, Instance cur))] precon in 
      
      
      List.map (fun (pi1, es1) -> 
      if re then (PureAnd (pi, pi1), Cons (Cons (his, Instance cur), es1), make_nothing env, k)
      else raise (Foo "precondiction check failed")
      ) precon
    )
   ) [] current 

  | Loop p ->
List.flatten(
  List.fold_left (fun acc (pi, his, cur, k) ->


  List.append acc (  
   
    List.map (fun (pi1, his1, cur1, k1) -> 
    (match k1 with 
      Some trap -> [(PureAnd (pi, pi1), Cons (Cons (his, Instance cur), his1), cur1, k1)]
    | None -> 
      List.map ( fun ins ->

      match (ins, cur1) with 
      | ([], _) -> (pi1, Cons (Cons (his, Instance cur), Kleene (Cons (derivativePar (SL ins) his1, Instance cur1))), make_nothing env, k1)
      | (_, []) -> (pi1, Cons (Cons (his, Instance (List.append cur ins)), Kleene (Cons (derivativePar (SL ins) his1, Instance ins))), make_nothing env, k1)
      | _ -> (pi1, Cons (Cons (his, Instance (List.append cur ins)), Kleene (Cons (derivativePar (SL ins) his1, Instance (List.append cur1 ins)))), make_nothing env, k1)
      ) (fst_simple his1)
    
    )
    ) (forward env [(pi, Emp, [], k)] p full)

  )
  
  
  ) [] current )

  | Fork (p1, p2) -> 
  List.flatten (
  List.fold_left (fun acc (pi, his, cur, k) ->

  List.append acc (  

  let temp1 = forward env [(pi, Emp, cur, k)] p1 full in 
  let temp2 = forward env [(pi, Emp, cur, k)] p2 full in 
  let combine = zip (temp1, temp2) in 



  List.map (fun (  (pi1, his1, cur1, k1),(pi2, his2, cur2, k2)) ->

 
  match (k1, k2) with
    (None, None) -> let (pi_new, es_new) = parallelES pi1 pi2 (Cons (his1, Instance cur1)) (Cons (his2, Instance cur2)) in
      
    List.map 
      (fun (pi_new_, his_new, cur_new) -> 
        (pi_new_, Cons(his, his_new), cur_new, None) )
      (splitEffects  (normalES es_new pi_new) pi_new)      
      
      
  | (Some trap, None) -> let (pi_new, es_new) = parallelES pi1 pi2 (Cons (his1, Instance cur1)) (Cons (his2, Instance cur2)) in
                    
      List.map (
        fun (pi_new_, his_new, cur_new) -> 
          (pi_new, Cons(his, his_new), cur_new, k1) )
      (splitEffects  (normalES es_new pi_new) pi_new)        

  
  | (None, Some trap) -> let (pi_new, es_new) = parallelES pi1 pi2 (Cons (his1, Instance cur1)) (Cons (his2, Instance cur2)) in
      List.map (
        fun (pi_new_, his_new, cur_new) -> 
        (pi_new, Cons(his, his_new), cur_new, k2) )
      (splitEffects  (normalES es_new pi_new) pi_new)                    

  | (Some t1, Some t2) -> raise (Foo ("not defined curretly"))

  ) combine
  )) [] current
  )

  ;;

let rec append_instance_to_effect (eff:effect) (ins:instance) : effect = 
  match eff with 
    [] -> []
  | (pi, es) :: xs ->  (pi, Cons (es, Instance ins)) :: (append_instance_to_effect xs ins)
  (*| Disj (eff1, eff2) -> Disj (append_instance_to_effect eff1 ins, append_instance_to_effect eff2 ins)*)
  ;;







let verifier (spec_prog:spec_prog) (full: spec_prog list):string = 
  let (nm, inp_sig, oup_sig, pre,  post, prog) = spec_prog in 
  
  let initial = List.fold_left (fun acc (pi, es) -> List.append (splitEffects es pi) acc) [] pre in 
  let initial_states = List.map (fun (pi_, his, cur) -> (pi_, his, cur, None)) initial in 
  let final_states = forward oup_sig initial_states prog full in 


  let (final:effect) = normalEffect (List.map (fun (pi, his, cur, _) -> 
    match cur with 
    [] -> (pi, his)
  | _ -> 
    (pi, Cons (his, Instance cur))) final_states) in  (*normalEffect merge_states*)
  let (report, _) = printReport final post true in 

  "\n========== Module: "^ nm ^" ==========\n" ^
  "[Pre  Condition] " ^ string_of_effect pre ^"\n"^
  "[Post Condition] " ^ string_of_effect post ^"\n"^
  "[Final  Effects] " ^ string_of_effect final ^"\n\n"^
  (*(string_of_inclusion final_effects post) ^ "\n" ^*)
  "[T.r.s: Verification for Post Condition]\n" ^ 
  report
   
  ;;


let forward_verification (progs:spec_prog list):string = 
  List.fold_left (fun acc a -> acc ^ "\n\n" ^ verifier a progs) "" progs ;; 

let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let progs = Parser.full_prog Lexer.token (Lexing.from_string line) in

      (*print_string (string_of_full_prog progs^"\n");*)
      print_string ( (forward_verification progs) ^"\n");
      
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
