exception Foo of string

type 'r reaction = ('r -> unit)

type ('a, 'b) promise = Pending of ('a reaction list * 'b reaction list) | F of 'a | R of 'b

type ('a) queue = ('a * 'a reaction lazy_t)  list

type queue1 = (unit lazy_t) list


let (pi: int queue ref) = ref [] ;;

let default = fun a -> a; ();;

let rec exec_until_empty (): unit = 
  match !pi with 
  | [] -> ()
  | (v, task) :: xs -> 
      ((Lazy.force task) v; 
      exec_until_empty () )
;;

let resolve (p:('a, 'b) promise ref) (v:'a) : unit = 
  match !p with 
  | Pending (f_reacts, r_reacts) -> 
      pi:= List.append (!pi) (List.map (fun f -> (v, lazy f)) f_reacts);
      p:= F v;
  | _ -> raise (Foo "Resolving a settled promise")
  ;;


let reject (p:('a, 'b) promise ref) (v:'a) : unit = 
  match !p with 
  | Pending (f_reacts, r_reacts) -> 
      pi:= List.append (!pi) (List.map (fun f -> (v, lazy f)) r_reacts);
      p:= R v;
  | _ -> raise (Foo "Rejecting a settled promise")
  ;;

let onResolve (p:('a, 'b) promise ref) (fn:'a reaction) : unit =
  match !p with 
  | Pending (f_reacts, r_reacts) -> 
      p := Pending (fn :: f_reacts , r_reacts)
  | F v | R v -> raise (Foo "Registering a resolve function on a settled promise")
  ;;

let onReject (p:('a, 'b) promise ref) (fn:'a reaction) : unit =
  match !p with 
  | Pending (f_reacts, r_reacts) -> 
      p := Pending (f_reacts , fn :: r_reacts)
  | F v | R v -> raise (Foo "Registering a reject function on a settled promise")
  ;;

let link (p1:('a, 'b) promise ref) (p2:('a, 'b) promise ref) : unit = 
  match !p1 with 
  | Pending (f_reacts, r_reacts) -> 
      p1 := Pending (default :: f_reacts , default :: r_reacts)
  | F v | R v -> 
      pi := List.append (!pi) [(v, lazy default)]
;;

(*

int lazy_t


type ('a, 'b, 'f) promise = 
  Pending of  (('f * ('a, 'b , 'f) promise ref ) list * ('f * ('a, 'b , 'f) promise ref) list )
| Resolved of 'a 
| Rejected of 'b

type ('a, 'b, 'f) pi = ('a * 'f * ('a, 'b, 'f) promise ref) list


lazy unit


let (pi:lazy unit) = ref [];;

let add_tasks (acts:('f * ('a, 'b , 'f) promise ref) list) (e: 'a) (pi: ('a, 'b, 'f) pi ref) : unit = 
  pi := List.append (!pi) 
  (
    List.fold_left (fun acc (f, p) -> List.append acc [(e, f , p)]) [] acts
  )
;;


let rec resolve (p: ('a, 'b, 'f) promise ref) (pi: ('a, 'b, 'f) pi ref) (e: 'a): unit =
  match !p with 
    Pending (f_act, r_act)->  
      (p := Resolved e;
       add_tasks f_act e pi; 
       exec_until_empty pi
       )
  | _ -> ()
  
and 

exec_until_empty (_pi: ('a, 'b, 'f) pi ref) : unit = 
  match !_pi with 
    [] -> ()
  | (v, f, _p)::xs -> resolve (_p) (ref xs) (f v) ;;




  ===================================
type ('a, 'b, 'f) promise = 
  Pending([(fn,a1)..] ::('a->unit) list, [(rn,a1)..]:('b->unit) list)
| F(..)
| R(..)

(fn::'a -> 'c, a1::Promise 'c _)
(rj::'b -> 'd, a1::Promise _ 'd)

apply_resolve next_promise = (\ a -> resolve next_promise a)

let rec resolve (p: ('a, 'b, 'f) promise ref) (pi: ('a, 'b, 'f) pi ref) (e: 'a): unit =
  match !p with 
    Pending (f_act, r_act)->  
      (p := Resolved e;
       add_tasks f_act e pi; 
       exec_until_empty pi
       )
  | _ -> ()
  
let exec_until_empty (_pi: ('a, 'b, 'f) pi ref) : unit = 
  match !_pi with 
    [] -> ()
  | (v, f, _p)::xs -> resolve (_p) (ref xs) (f v) ;;
  
let exec_until_empty (_pi: ('a, 'b, 'f) pi ref) : unit = 
  match !_pi with 
    [] -> ()
  | (v, f, _p)::xs -> resolve (_p) (ref xs) (f v) ;;
let add_tasks (acts:('f * ('a, 'b , 'f) promise ref) list) (e: 'a) (pi: ('a, 'b, 'f) pi ref) : unit = 
  pi := List.append (!pi) 
  (
    List.fold_left (fun acc (f, p) -> List.append acc [(e, f , p)]) [] acts
  )


(*onResolve (p: ('a, 'b, 'f) promise ref) (p_new: ('a, 'b, 'f) promise ref) (f: 'f): unit =
  match !p with 
  | Pending (f_act, r_act) -> p := Pending ((f, p_new)::f_act, r_act);
  | Resolved v
  | Rejected v 


and*)

(*type ('a, 'b, 'f) reactions = ('f * ('a, 'b) promise) list

type ('a, 'b, 'f) fulfillReaction = (addr * promise_reaction list )

type rejectReaction = (addr * promise_reaction list )

let (fulfillReaction)




let reject (p: ('a, 'b) promise ref) (e: 'b): ('a, 'b) promise ref =
  match !p with 
    Pending -> (p := Rejected e; p)  
  | _ -> p 
;;

let rec waitToBeFuffiled (p: ('a, 'b) promise ref) :  ('a, 'b) promise ref =
  match !p with 
    Pending -> waitToBeFuffiled p 
  | _ -> p
;;

exception Foo of string

let rec onResolve (p_pre: ('a, 'b) promise ref) (f: 'a -> 'c): ('c, 'd) promise ref =
  let p_pre' = waitToBeFuffiled p_pre in 
  match !p_pre' with 
  | Rejected e -> raise (Foo "Got Rejected from onResolve")
  | Resolved e -> ref (Resolved (f e)) 
  | _ -> ref Pending 
;;

let rec onReject (p_pre: ('a, 'b) promise ref) (f: 'b -> 'd): ('c, 'd) promise ref =
  let p_pre' = waitToBeFuffiled p_pre in 
  match !p_pre' with 
  | Rejected e -> ref (Resolved (f e)) 
  | Resolved e -> p_pre'  (* seems no exception in this case*)
  | _ -> ref Pending 
;;

let link (p_pre: ('a, 'b) promise ref) (p_post: ('a, 'b) promise ref) : unit =
  let p_pre' = waitToBeFuffiled p_pre in 
  match !p_post with 
  | Pending -> (p_post := !p_pre')
  | _ -> ()
;; 

  (*
    match !p_pre with 
  | Resolved _ -> 
  | Rejected _ -> 
  | Pending -> let p_pre' = waitToBeFuffiled p_pre in 
  match !p_pre' with 
    

  
  p_post := !p_pre;
  p_post*)

let id a = a ;;

let _then (p: ('a, 'b)  promise ref) (f_resolve: 'a -> 'c) (f_reject: 'b -> 'd) : ('c, 'd) promise ref =
  let p' = waitToBeFuffiled p in 
  match !p' with 
  | Rejected e -> onReject p f_reject
  | Resolved e -> onResolve p f_resolve (* seems no exception in this case*)
  | _ -> raise (Foo "Not possible")
  ;;

let _catch (p: ('a, 'b)  promise ref) (f_reject: 'b -> 'd) = _then p id f_reject ;;
*)

let main = print_string ("song yahui");

*)