(*
type dyn = Num of int | Str of string
let promisify : (dyn, dyn) promise ref = ref Pending 
*)

type ('a, 'b) promise = Pending | Resolved of 'a | Rejected of 'b

let resolve (p: ('a, 'b) promise ref) (e: 'a): ('a, 'b) promise ref =
  match !p with 
    Pending ->  (p := Resolved e; p) 
  | _ -> p 
;;

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

let link (p_pre: ('a, 'b) promise ref) (p_post: ('c, 'd) promise ref) : ('a, 'b) promise ref =
  p_post := !p_pre;
  p_post
  ;;

let id a = a ;;

let _fork (p1: ('a, 'b)  promise ref) (p2 : ('c, 'd) promise ref) : ('a, 'b) promise ref =
  p1;; (* this is just making sure the type is correct *)

let _then (p: ('a, 'b)  promise ref) (f_resolve: 'a -> 'c) (f_reject: 'b -> 'd) : ('c, 'd) promise ref =
  _fork 
  (onResolve p f_resolve )
  (onReject p f_reject)
  ;;

let _catch (p: ('a, 'b)  promise ref) (f_reject: 'b -> 'd) = _then p id f_reject ;;


let main = print_string ("song yahui");