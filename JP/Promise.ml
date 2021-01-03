open String
open List
open Printf
open Int32

exception Foo of string

type dyn = Num of int | Str of string

type state = P | F of dyn | R of dyn

type addr = int 

type promise = (addr * state)

type reaction = Lam | Default

type promise_reaction = (reaction * addr)

type fulfillReaction = (addr * promise_reaction list )

type rejectReaction = (addr * promise_reaction list )

type queue = (dyn * reaction * addr) list

type expr = Undef 
          | Promisify 
          | Resolve of addr * dyn
          | Reject of addr * dyn
          | OnResolve of addr * reaction * addr
          | OnReject of addr * reaction * addr
          | Link of addr * addr

type program_state = ((promise) list * fulfillReaction list * rejectReaction list * queue)

let promise_counter = ref (-1) 

let addr_generator = 
  promise_counter := !promise_counter + 1;
  !promise_counter
  ;;

let rec settle_promise (addr:addr) (x:dyn) (ps:promise list) (flag): promise list = 
  (*flag = true is to resolve, false is to reject *)
  let rec aux front _ps = 
    match _ps with 
      [] -> raise (Foo "settling an non-existing promise")
    | (a, p) ::xs -> 
      if a == addr then 
      (
        match p with 
        | P -> List.append front (if flag then ((a, F x) :: xs) else ((a, R x) :: xs))
        | _-> List.append front _ps
      )
      else aux (List.append front [(a, p)]) xs
  in aux [] ps
      ;;

let register_reacts (addr_pre:addr) (addr_po) (reaction:reaction) (fs:fulfillReaction list) : fulfillReaction list = 
  let rec aux front _fs = 
    match _fs with 
      [] -> (addr_pre, [(reaction, addr_po)]) :: front
    | (a, react_li) :: xs ->
      if a == addr_pre then List.append front ((addr_pre, (reaction, addr_po)::react_li  ):: xs)
      else aux (List.append front [(a, react_li)]) xs
  in aux [] fs 
  ;;

let retrive_reactions (fs:fulfillReaction list) (addr:addr) : (fulfillReaction list * promise_reaction list) = 
  let rec aux front _fs = 
    match _fs with 
      [] -> (front, [])
    | (a, react_li)::xs -> 
      if a == addr then (List.append front xs,  react_li)
      else aux (List.append front [(a, react_li)]) xs 
  in aux [] fs
  ;;

let enqueue (q:queue) (v:dyn) (reacts: promise_reaction list) :queue = 
  List.append q (List.fold_left (fun acc (re, a) -> List.append acc [(v, re, a)]) [] reacts)

let rec state_of_promise (ps:promise list) (addr:addr) : state = 
  match ps with 
    [] -> raise (Foo "getting the state of an undefined promise")
  | (a, s)::xs -> if a == addr then s else  state_of_promise xs addr
  ;;

let one_step_forward (program_state:program_state) (expr:expr) :program_state = 
  let (ps, f_reacts, r_reacts, q) = program_state in 
  match expr with 
  | Undef -> program_state 

  | Promisify -> 
    let (new_p:promise) = (addr_generator, P)  in 
    ((List.append ps [(new_p)]), f_reacts, r_reacts, q)

  | Resolve (a, v) -> 
    (* to change the promese states *)
    let (new_ps:promise list) = settle_promise a v ps true in 
    (* to retrive the reactions registered on a on resolve *)
    let (new_f_reacts, (reacts :promise_reaction list)) = retrive_reactions f_reacts a in 
    (* enqueue the reaction into the queue *)
    let (new_q:queue) = enqueue q v reacts in 
    (* update the ps, f_reacts and  new_q*)
    (new_ps, new_f_reacts, r_reacts, new_q)

  | Reject (a, v) -> 
    (* to change the promese states *)
    let (new_ps:promise list) = settle_promise a v ps false in 
    (* to retrive the reactions registered on a on reject *)
    let (new_r_reacts, (reacts :promise_reaction list)) = retrive_reactions r_reacts a in 
    (* enqueue the reaction into the queue *)
    let (new_q:queue) = enqueue q v reacts in 
    (* update the ps, r_reacts and  new_q*)
    (new_ps, f_reacts, new_r_reacts, new_q)

  | OnResolve (a_pre, reaction, a_po) -> 
    let new_f_reacts = register_reacts a_pre a_po reaction f_reacts in 
    (ps, new_f_reacts, r_reacts, q)

  | OnReject (a_pre, reaction, a_po) -> 
    let new_r_reacts = register_reacts a_pre a_po reaction r_reacts in 
    (ps, f_reacts, new_r_reacts, q)
  
  | Link (a1, a2) -> (*a1.link(a2)*)
    let p1 = state_of_promise ps a1 in 
    match p1 with 
    | P -> 
      let new_f_reacts = register_reacts a1 a2 Default f_reacts in 
      let new_r_reacts = register_reacts a1 a2 Default r_reacts in 
      (ps, new_f_reacts, new_r_reacts, q)
    | F v | R v -> 
      let (new_q:queue) = enqueue q v [(Default, a2)] in 
      (ps, f_reacts, r_reacts, new_q)
  ;;


let () = print_string ("yahui song")