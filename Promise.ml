type dyn = Num of int | Str of string

type ('a, 'b) promise = Pending | Resolved of 'a | Rejected of 'b

let promisify : (dyn, dyn) promise ref = ref Pending 

let resolve (p: (dyn, dyn) promise ref) (e: dyn): (dyn, dyn) promise ref =
  match !p with 
    Pending ->  (p := Resolved e; p) 
  | _ -> p 
;;

let reject (p: (dyn, dyn) promise ref) (e: dyn): (dyn, dyn) promise ref =
  match !p with 
    Pending -> (p := Rejected e; p)  
  | _ -> p 
;;

let rec waitToBeResolved (p: (dyn, dyn) promise ref) :  (dyn, dyn) promise ref =
  match !p with 
    Resolved _ -> p 
  | _ -> waitToBeResolved p 
;;

let rec waitToBeRejected (p: (dyn, dyn) promise ref) :  (dyn, dyn) promise ref =
  match !p with 
    Rejected _ -> p 
  | _ -> waitToBeRejected p 
;;

let rec onResolve (p_pre: (dyn, dyn) promise ref) (p_post: (dyn, dyn) promise ref) (f: dyn -> dyn): (dyn, dyn) promise ref =
  let p_pre' = waitToBeResolved p_pre in 
  match !p_pre' with 
  | Resolved e -> ref (Resolved (f e)) 
  | _ -> ref Pending 
;;

let rec onReject (p_pre: (dyn, dyn) promise ref) (p_post: (dyn, dyn) promise ref) (f: dyn -> dyn): (dyn, dyn) promise ref =
  let p_pre' = waitToBeRejected p_pre in 
  match !p_pre' with 
  | Rejected e -> ref (Resolved (f e)) 
  | _ -> ref Pending 
;;

let link (p_pre: (dyn, dyn) promise ref) (p_post: (dyn, dyn) promise ref) : (dyn, dyn) promise ref =
  p_post := !p_pre;
  p_post
  ;;

let id a = a ;;

let _fork (p1: (dyn, dyn) promise ref) (p2 : (dyn, dyn) promise ref) : (dyn, dyn) promise ref =
  p1;; (* this is just making sure the type is correct *)

let _then (p: (dyn, dyn) promise ref) (f_resolve: dyn -> dyn) (f_reject: dyn -> dyn) : (dyn, dyn) promise ref =
  let newP = promisify in 
  _fork 
  (onResolve p newP f_resolve )
  (onReject p newP f_reject)
  ;;

let _catch (p: (dyn, dyn) promise ref) (f_reject: dyn -> dyn) = _then p id f_reject ;;


let main = print_string ("song yahui");