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

 
let rec paralleEffShort es1 es2 : p_es = 
  let norES1 = normalPES es1 in 
  let norES2 = normalPES es2 in 
  let norES1 = filterZero norES1 in 
  let norES2 = filterZero norES2 in 
  let fst1 = getFstPes norES1 in
  let fst2 = getFstPes norES2 in 
  let headcom = zip fst1 fst2 in 


  let listES =  List.map (
  fun (f1, f2) -> 
    let der1 = normalPES (derivativePes f1 norES1) in 
    let der2 = normalPES (derivativePes f2 norES2) in 


    (match (der1, der2) with 
    | (PEmp, _) -> PInstance (appendSL f1 f2)
    | (_, PEmp) -> PInstance (appendSL f1 f2)
    | (der1, der2) -> 
      PCon (PInstance (appendSL f1 f2), paralleEffShort der1 der2))
  ) headcom
  
  in
  normalPES (
  List.fold_left (fun acc a -> PDisj (acc, a)) PBot listES
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
  
let rec append_ins_to_es (ins:instance)  (es:es) : es = 
  Cons(es, Instance ins)
  ;;

let rec forward (env: string list) (current:prog_states) (prog:prog) (full: spec_prog list): prog_states =
  let (pi, his, cur, k) = current in 
  match prog with 
    Halt -> current
  | Yield -> 
    (pi, Cons (his,Instance cur) , make_nothing env, k)
  | Emit (s) -> 
    (pi, Cons (his,Instance cur) , setState cur s 1, k) (* flag 0 - Zero, 1- One, 2-Wait *)
  | Await (s) -> 
    (pi, Cons (his,Instance cur) , setState cur s 2, k) (* flag 0 - Zero, 1- One, 2-Wait *)

  | Present (s, p1, p2) ->
    if isPresent s cur then forward env current p1 full 
    else forward env current p2 full 

  | Declear (s , p) -> forward (List.append env [s]) current p full 
    
  


    (*
    | Async (s, p, delay) ->
      
    let helper (pure, his, curr, trap) = 
      match trap with
      | Some name -> (pure, his, curr, trap)
      | None -> (pure, his, List.append curr [(One s)], trap)
    in List.map (helper) current
  | Seq (p1, p2) ->  
    let helper (pure, his, curr, trap) = 
      match trap with
      | Some name -> [(pure, his, curr, trap)]
      | None -> 
        let states1 = forward current p1 full in 
        List.flatten (List.map (fun (pure1, his1, cur1, trap1)->
              match trap1 with 
                Some _ -> [(pure1, his1, cur1, trap1)]
              | None -> forward [(pure1, his1, cur1, trap1)] p2 full

              )states1)
    
    in  List.flatten (List.map (helper) current)

  
  | If (pi, p1, p2) -> 
    let left = forward (List.map (fun (pure, his, curr, trap ) -> (PureAnd (pure, pi), his, curr, trap )) current) p1 full in 
    let right = forward (List.map (fun (pure, his, curr, trap ) -> (PureAnd (pure, Neg pi), his, curr, trap )) current) p2 full in 
    List.append left right

  
  
  | Trap (mn, prog) -> 
      List.flatten (List.map (fun (pure, his, cur, trap)-> 
      match trap with 
        Some _ -> [(pure, his, cur, trap)]
      | None -> 
          let eff = forward [(pure, his, cur, trap)] prog full in 
          List.map (fun (pureIn, hisIn, curIn, trapIn)->
          match trapIn with 
            Some name -> if String.compare mn name == 0 then (pure, hisIn, curIn, None)
                         else (pureIn, hisIn, curIn, trapIn)
          | None -> (pureIn, hisIn, curIn, trapIn)
          )
          eff
      )current)

  | Break name -> 
      List.map (fun (pure, his, cur, trap)-> 
      match trap with 
        Some _ -> (pure, his, cur, trap)
      | None -> (pure, his, cur, Some name)
      )current


  | _ -> current
  (*
 

  | Fork (p1, p2) ->
      let left = forward current p1 full in 
      let right = forward current p2 full in 
      
      
    
(Fork (_, _)|Loop _|Run _|Suspend (_, _)|Async (_, _, _)|Await _)

  | Loop pIn -> "loop\n " ^ string_of_prog pIn ^ "\nend loop"
   
  | Run mn -> "run " ^ mn
  | Suspend (prog, s) -> "abort \n" ^ string_of_prog prog ^ "\nwhen "^s
  | Async (mn, prog, act) -> "async "^ mn ^ string_of_prog prog ^ string_of_action act
  | Await (mn) -> "await "^ mn 
  *)
  *)
  ;;

let rec append_instance_to_effect (eff:effect) (ins:instance) : effect = 
  match eff with 
   (pi, es) ->  (pi, Cons (es, Instance ins))
  (*| Disj (eff1, eff2) -> Disj (append_instance_to_effect eff1 ins, append_instance_to_effect eff2 ins)*)
  ;;

(*

let rec splitEffects (eff:effect) : (pure*es) list = 
  match eff with 
    Effect (pi, es) -> [(pi, es)]
  | Disj (eff1, eff2) -> List.append (splitEffects eff1) (splitEffects eff2)
  ;;
  
  *)



let verifier (spec_prog:spec_prog) (full: spec_prog list):string = 
  let (nm, inp_sig, oup_sig, pre,  post, prog) = spec_prog in 
  let (pi, es) = pre in 
  let initial_states = (pi, es, [], None) in 
  let prog_states = forward oup_sig initial_states prog full in 
  
    (*
    let merge_states = prog_states in 
    List.fold_left 
    (fun acc (pure, his, current, trap) -> Disj (acc, append_instance_to_effect ((pure, his)) current))
    ((FALSE, Bot)) 
    prog_states  in 
    *)
  let (final:effect) = ((FALSE, Bot))  (*normalEffect merge_states*) in 
  let (report, _) = printReport final post true in 

  "\n========== Module: "^ nm ^" ==========\n" ^
  "(* Temporal verification: "^ "  *)\n" ^
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
