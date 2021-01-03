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
          | OnResolve of addr * reaction
          | OnReject of addr * reaction
          | Link of addr * addr

type program_state = ((promise) list * fulfillReaction list * rejectReaction list * queue)

let promise_counter = ref (-1) 

let addr_generator = 
  promise_counter := !promise_counter + 1;
  !promise_counter
  ;;

let rec settle_promise (addr:addr) (x:dyn) (ps:promise list) (flag): promise list = 
  let rec aux front _ps = 
    match _ps with 
      [] -> raise (Foo "settling an non-existing promise")
    | (a, p) ::xs -> 
      if a == addr then 
      (match p with 
      | P -> List.append front (if flag then ((a, F x) :: xs) else ((a, R x) :: xs))
      | _-> List.append front _ps
      )
      else aux (List.append front [(a, p)]) xs
  in aux [] ps
      ;;



let forward (program_state:program_state) (expr:expr) :program_state = 
  let (ps, f_reacts, r_reacts, q) = program_state in 
  match expr with 
  | Undef -> program_state 
  | Promisify -> 
    let (new_p:promise) = (addr_generator, P)  in 
    ((List.append ps [(new_p)]), f_reacts, r_reacts, q)

  | Resolve (a, v) -> 
    let (new_ps:promise list) = settle_promise a v ps true in 
    (new_ps, f_reacts, r_reacts, q)

  | Reject (a, v) -> 
    let (new_ps:promise list) = settle_promise a v ps false in 
    (new_ps, f_reacts, r_reacts, q)

  (*
  | OnResolve of promise * reaction
  | OnReject of promise * reaction
  | Link of promise * promise
  *)
  | _ -> program_state 
  ;;


let () = print_string ("yahui song")