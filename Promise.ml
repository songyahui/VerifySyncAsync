type dyn = Num of int | Str of string

type promise = Pending | Resolved of dyn | Rejected of dyn

let promisify : promise ref = ref Pending 

let resolve (p: promise ref) (e: dyn): promise ref =
  match !p with 
    Pending -> ref (Resolved e)
  | _ -> p 
;;

let reject (p: promise ref) (e: dyn): promise ref =
  match !p with 
    Pending -> ref (Rejected e)
  | _ -> p 
;;

let rec onResolve (p_pre: promise ref) (p_post: promise ref) (f: dyn -> dyn): promise ref =
  match !p_pre with 
    Pending -> onResolve p_pre p_post f
  | Resolved e -> ref (Resolved (f e)) 
  | _ -> p_pre
;;

let rec onReject (p_pre: promise ref) (p_post: promise ref) (f: dyn -> dyn): promise ref =
  match !p_pre with 
    Pending -> onResolve p_pre p_post f
  | Rejected e -> ref (Resolved (f e)) 
  | _ -> p_pre
;;

let link (p_pre: promise ref) (p_post: promise ref) : promise ref =
  p_post := !p_pre;
  p_post
  ;;


let main = print_string ("song yahui");