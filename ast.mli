type name = string (*name of the signal e.g., A B C*)
type lable = string


type signal = One of name | Zero of name 

(*signal set*)
type instance = signal list ;;


type terms = Var of name
           | Number of int
           | Plus of terms * terms
           | Minus of terms * terms

(*

type realtime = 
           | Anytime 
           | EqConst of int 
           | Greater of int
           | LessThan of int
           | RTAnd of realtime * realtime
           | RTOr  of realtime * realtime


*)

type es = Bot  (*_|_*)
        | Emp  (* emp *)
        | Wait of name 
        | Instance of instance (*logical tick*) (* {} *)
        | Cons of es * es (* .  *)
        | Choice of es * es (* \/ *)
        | Par of es * es (* ||  *)
        | RealTime of es * terms (*real time tick*) (* es # t *)
        | Kleene of es (* es^* *)

(*Arithimetic pure formulae*)
type pure = TRUE
          | FALSE
          | Gt of terms * terms
          | Lt of terms * terms
          | GtEq of terms * terms
          | LtEq of terms * terms
          | Eq of terms * terms
          | PureOr of pure * pure
          | PureAnd of pure * pure
          | Neg of pure

type effect = (pure * es) list 

type inclusion = effect * effect;;

type inclusion_sleek = effect * effect * bool;;    (*the bool is the expected result*) 

type prog = Halt 
          | Yield 
          | Seq of prog * prog 
          | Fork of prog * prog
          | Loop of prog
          | Declear of name * prog
          | Emit of name
          | Present of name * prog * prog
          | Trap of lable * prog
          | Break of lable
          | Run of name
          | Abort of int * prog
(*Esterel SYNC*)
          | Async of name * prog * int (*the delay*)  (*set a timeout*)
          | Await of name 
          | Assert of effect
(*JS ASYNC*)

type prog_states = (pure * es * instance * name option) list

type fst = (instance * string * pure)

type parfst = SL of instance | W of name

type ltl = Lable of string 
        | Next of ltl
        | Until of ltl * ltl
        | Global of ltl
        | Future of ltl
        | NotLTL of ltl
        | Imply of ltl * ltl
        | AndLTL of ltl * ltl
        | OrLTL of ltl * ltl


type spec_prog = name * string list * string list * effect * effect * prog
              (* name , input,     output, precon, postcon, body*)