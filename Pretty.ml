(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open String
open List
open Ast
open Printf
open Int32
open Askz3


exception Foo of string

let entailConstrains pi1 pi2 = 

  let sat = not (askZ3 (Neg (PureOr (Neg pi1, pi2)))) in
  (*
  print_string (showPure pi1 ^" -> " ^ showPure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat;;


(*used to generate the free veriables, for subsititution*)
let freeVar = ["t1"; "t2"; "t3"; "t4";"t5";"t6";"t7";"t8";"t9";"t10"
              ;"t11"; "t12"; "t13"; "t14";"t15";"t16";"t17";"t18";"t19";"t20"
              ;"t21"; "t22"; "t23"; "t24";"t25";"t26";"t27";"t28";"t29";"t30"];;



let rec getAfreeVar (varList:string list):string  =
  let rec findOne li = 
    match li with 
        [] -> raise ( Foo "freeVar list too small exception!")
      | x :: xs -> if (exists (fun a -> String.compare a x == 0) varList) == true then findOne xs else x
  in
  findOne freeVar
;;




let rec iter f = function
  | [] -> ()
  | [x] ->
      f true x
  | x :: tl ->
      f false x;
      iter f tl

let to_buffer ?(line_prefix = "") ~get_name ~get_children buf x =
  let rec print_root indent x =
    bprintf buf "%s\n" (get_name x);
    let children = get_children x in
    iter (print_child indent) children
  and print_child indent is_last x =
    let line =
      if is_last then
        "└── "
      else
        "├── "
    in
    bprintf buf "%s%s" indent line;
    let extra_indent =
      if is_last then
        "    "
      else
        "│   "
    in
    print_root (indent ^ extra_indent) x
  in
  Buffer.add_string buf line_prefix;
  print_root line_prefix x

let printTree ?line_prefix ~get_name ~get_children x =
  let buf = Buffer.create 1000 in
  to_buffer ?line_prefix ~get_name ~get_children buf x;
  Buffer.contents buf

type binary_tree =
  | Node of string * (binary_tree  list )
  | Leaf

let get_name = function
    | Leaf -> "."
    | Node (name, li) -> name;;

let get_children = function
    | Leaf -> []
    | Node (_, li) -> List.filter ((<>) Leaf) li;;

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"

  ;;

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"
;;

let rec string_of_action (act:action) : string = 
  match act with 
    Delay n -> "Delay " ^ string_of_int n  
  | Timeout n -> "time out " ^ string_of_int n  
  | NoneAct -> "NoneAct";;


let rec string_of_prog (p : prog) : string =
  match p with
    Halt -> "halt"
  | Yield -> "yield"
  | Seq (p1, p2) ->  string_of_prog p1 ^ ";\n" ^ string_of_prog p2 
  | Fork (p1, p2) ->  "(" ^ string_of_prog p1 ^ ")\n||\n (" ^ string_of_prog p2 ^" )"
  | Loop pIn -> "loop\n " ^ string_of_prog pIn ^ "\nend loop"
  | Declear (s, prog) -> "signal " ^ s ^ " in \n" ^ string_of_prog prog ^ "\nend signal"
  | Emit (s, arg) -> "emit " ^ s ^ 
  (
    match arg with 
      None -> ""
    | Some (n) -> "(" ^ string_of_int n ^")"
  ) 
  | If (s, p1, p2) -> "present " ^ s ^ "\nthen " ^ string_of_prog p1 ^"\nelse " ^ string_of_prog p2 ^"\nend present"
  | Trap (mn, prog) -> "trap "  ^ mn ^" in\n" ^ string_of_prog prog ^" )"^ "\nend trap"
  | Break  mn -> "exit " ^ mn 
  | Run mn -> "run " ^ mn
  | Suspend (prog, s) -> "abort \n" ^ string_of_prog prog ^ "\nwhen "^s
  | Async (mn, prog, act) -> "async "^ mn ^ string_of_prog prog ^ string_of_action act
  | Await (mn) -> "await "^ mn 
  ;;

let rec showLTL (ltl:ltl):string =
  match ltl with 
    Lable str -> str
  | Next l -> "(" ^"X" ^showLTL l ^")"
  | Until (l1, l2) -> "(" ^showLTL l1 ^ " U " ^showLTL l2 ^")"
  | Global l -> "(" ^"[] " ^showLTL l ^")"
  | Future l -> "(" ^"<> " ^showLTL l ^")"
  | NotLTL l -> "(" ^"! " ^showLTL l ^")"
  | Imply (l1, l2) -> "(" ^showLTL l1 ^ " -> " ^showLTL l2 ^")"
  | AndLTL (l1, l2) -> "(" ^showLTL l1 ^ " && " ^showLTL l2 ^")"
  | OrLTL (l1, l2) -> "(" ^showLTL l1 ^ " || " ^showLTL l2 ^")"
  ;;

let string_of_state (state :signal):string = 
  match state with 
    One name -> name ^","
  | Zero name -> "!"^name ^"," 
  | Wait name -> "?"^name ^",";;


let string_of_sl (sl: instance):string = 
  List.fold_left (fun acc (sig_, n) -> 
  acc ^ "" ^ 
  string_of_state sig_ ^ (
    match n with 
      None -> ""
    | Some n -> "(" ^ string_of_int n ^")"
  )
  ) "" sl
;;

let string_of_instance (mapping:instance) :string = 
  let temp1 = "{" ^ string_of_sl mapping ^ "}" in 
  temp1
  ;;

let rec string_of_terms (t:terms):string = 
  match t with
    Var name -> name
  | Number n -> string_of_int n
  | Plus (t1, t2) -> (string_of_terms t1) ^ ("+") ^ (string_of_terms t2)
  | Minus (t1, t2) -> (string_of_terms t1) ^ ("-") ^ (string_of_terms t2)

  ;;

let rec string_of_es (es:es) :string = 
  match es with 
    Bot -> "_|_"  
  | Emp -> "emp"
  | Instance ins  -> string_of_instance ins
  | Cons (es1, es2) ->  "("^string_of_es es1 ^ " . " ^ string_of_es es2^")"
  | Kleene esIn -> "(" ^ string_of_es esIn ^ ")*" 
  | Ttimes (esIn, t) ->"(" ^ string_of_es esIn ^ ")" ^ string_of_terms t 
  | TimeUnit -> "t_unit"
  | Choice (es1, es2) -> "("^string_of_es es1 ^ " + " ^ string_of_es es2^")"
  | Par (es1, es2) -> "("^string_of_es es1 ^ " || " ^ string_of_es es2^")"
  ;;

(*To pretty print pure formulea*)
let rec string_of_pure (p:pure):string = 
  match p with
    TRUE -> "true"
  | FALSE -> "false"
  | Gt (t1, t2) -> (string_of_terms t1) ^ ">" ^ (string_of_terms t2)
  | Lt (t1, t2) -> (string_of_terms t1) ^ "<" ^ (string_of_terms t2)
  | GtEq (t1, t2) -> (string_of_terms t1) ^ ">=" ^ (string_of_terms t2)
  | LtEq (t1, t2) -> (string_of_terms t1) ^ "<=" ^ (string_of_terms t2)
  | Eq (t1, t2) -> (string_of_terms t1) ^ "=" ^ (string_of_terms t2)
  | PureOr (p1, p2) -> "("^string_of_pure p1 ^ "\\/" ^ string_of_pure p2^")"
  | PureAnd (p1, p2) -> "("^string_of_pure p1 ^ "/\\" ^ string_of_pure p2^")"
  | Neg p -> "(!" ^ "(" ^ string_of_pure p^"))"
  ;; 

let rec string_of_effect(eff:effect): string = 
  match eff with 
    Effect (p , es) -> string_of_pure p ^ "&" ^ string_of_es es 
  | Disj (es1, es2) -> string_of_effect es1 ^ " \\/ " ^ string_of_effect es2
;;


let string_of_spec_prog (inp:spec_prog):string = 
  let  (nm, ins, outs, pre, post, p) = inp in 
  let body = string_of_prog p in 
  let spec = "\n/*@\nrequire " ^ string_of_effect pre ^"\nensure " ^ string_of_effect post ^"\n@*/\n\n" in 
  
  let inp = "input " ^ string_of_sl ins (*(List.fold_left (fun acc a -> acc ^ " " ^ a) "" ins) ^ ";\n" *)in 
  let outp = "output " ^ string_of_sl outs (* (List.fold_left (fun acc a -> acc ^ " " ^ a) "" outs) ^ ";\n"*) in 
  let whole = "module " ^ nm  ^": \n\n" ^ inp ^ outp ^ spec ^ body ^ "\n\nend module" in 
  whole ;;

let string_of_full_prog (full: spec_prog list):string = 
  List.fold_left (fun acc (p) -> acc ^ "\n\n" ^ string_of_spec_prog p) "" full
;;



let string_of_inclusion (lhs:effect) (rhs:effect) :string = 
  string_of_effect lhs ^" |- " ^string_of_effect rhs 
  ;;


let compareSignal s1 s2 : bool =
  match (s1, s2) with 
    (One n1, One n2) -> String.compare n1 n2 == 0
  | (Zero n1 , Zero n2 ) -> String.compare n1 n2 == 0 
  | _ -> false 
  ;;

let controdict s1 s2 : bool =
  match (s1, s2) with 
    (One n1, Zero n2) -> String.compare n1 n2 == 0
  | (Zero n1 , One n2 ) -> String.compare n1 n2 == 0 
  | _ -> false 
  ;;

let rec oneOfFalse (sig_:signal) ss : bool =
  match ss with 
    [] -> false 
  | head_sig:: xs -> if controdict sig_ head_sig then true else oneOfFalse sig_ xs
;;
(*true return has controdiction, false means no controdiction *)
let rec checkHasFalse ss : bool = 
  match ss with 
  [] -> false 
| x::xs -> if oneOfFalse x xs then true else checkHasFalse xs 
;;




let rec oneOf (sig_:signal) ss : bool =
  match ss with 
    [] -> false 
  | sig_head:: xs -> 

  if compareSignal sig_ sig_head then true else oneOf sig_ xs
;;

let rec deleteRedundent sl : signal list = 
  match sl with 
    [] -> sl 
  | x::xs -> if oneOf x xs then deleteRedundent xs else List.append [x] (deleteRedundent xs)

  ;;

  

let rec nullable (pi :pure) (es:es) : bool=
  match es with 
    Bot -> false 
  | Emp -> true
  | Instance _  -> false 
  | Cons (es1, es2) -> (nullable pi es1) && (nullable pi es2)
  | Kleene _ -> true  
  | Ttimes (_, t) -> askZ3 (PureAnd (pi, Eq (t, Number 0))) 
  | TimeUnit -> false 
  | Choice (es1, es2) -> (nullable pi es1) || (nullable pi es2)
  | Par (es1, es2) -> (nullable pi es1) && (nullable pi es2)
  ;;

