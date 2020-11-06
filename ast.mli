type name = string (*name of the signal e.g., A B C*)
type lable = string


type signal = One of name | Zero of name

(*signal set*)
type instance = (signal * int option) list ;;

type terms = Var of name
           | Number of int
           | Plus of terms * terms
           | Minus of terms * terms

type es = Bot 
        | Emp 
        | Instance of instance 
        | Cons of es * es
        | Ttimes of es * terms
        | Kleene of es
        | Omega of es
        

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

type effect = 
            Effect of pure * es
          | Disj of effect * effect


type inclusion = effect * effect;;    

type action = Delay of int | Timeout of int | NoneAct

type prog = Halt 
          | Yield 
          | Seq of prog * prog 
          | Fork of prog * prog
          | Loop of prog
          | Declear of name * prog
          | Emit of name
          | If of name * prog * prog
          | Trap of lable * prog
          | Break of lable
          | Run of name
          | Suspend of prog * name 
(*Esterel SYNC*)
          | Async of name * prog * action  (*set a timeout*)
          | Await of name 
(*JS ASYNC*)



type ltl = Lable of string 
        | Next of ltl
        | Until of ltl * ltl
        | Global of ltl
        | Future of ltl
        | NotLTL of ltl
        | Imply of ltl * ltl
        | AndLTL of ltl * ltl
        | OrLTL of ltl * ltl


type spec_prog = name * instance * instance * effect * effect * prog
              (* name , input,     output, precon, postcon, body*)