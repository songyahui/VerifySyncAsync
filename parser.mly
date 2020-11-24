%{ open Ast %}
%{ open List %}


%token <string> VAR
%token <int> INTE
%token NOTHING PAUSE PAR  LOOP SIGNAL LPAR RPAR EMIT PRESENT TRAP EXIT SIMI
%token AWAIT ASYNC SUSPEND 
%token EOF GT LT EQ CONJ GTEQ LTEQ ENTIL EMPTY DISJ COMMA CONCAT  KLEENE END IN RUN OMEGA
%token THEN ELSE ABORT WHEN LBRACK RBRACK POWER PLUS MINUS TRUE FALSE NEGATION
(* LBrackets  RBrackets POWER*)
%left CONCAT DISJ SIMI 
(* %right SIMI PAR *)
%token FUTURE GLOBAL IMPLY LTLNOT NEXT UNTIL LILAND LILOR 
%token LSPEC RSPEC ENSURE REQUIRE MODULE OUT INOUT
%token LBrackets RBrackets HIPHOP 

%start full_prog specProg pRog ee ltl_p
%type <(Ast.spec_prog) list> full_prog
%type <Ast.spec_prog> specProg
%type <Ast.prog> pRog
%type <(Ast.inclusion) list > ee
%type <(Ast.ltl) list > ltl_p


%%

full_prog:
| EOF {[]}
| a = specProg r = full_prog { append [a] r }


ee: 
| EOF {[]}
| a = entailment SIMI r = ee { append [a] r }

ltl_p: 
| EOF {[]}
| a = ltl SIMI r = ltl_p { append [a] r }

ltl : 
| s = VAR {Lable s} 
| LPAR r = ltl RPAR { r }
| NEXT p = ltl  {Next p}
| LPAR p1= ltl UNTIL p2= ltl RPAR {Until (p1, p2)}
| GLOBAL p = ltl {Global p}
| FUTURE p = ltl {Future p}
| LTLNOT p = ltl {NotLTL p}
| LPAR p1= ltl IMPLY p2= ltl RPAR {Imply (p1, p2)}
| LPAR p1= ltl LILAND p2= ltl RPAR {AndLTL (p1, p2)}  
| LPAR p1= ltl LILOR p2= ltl RPAR {OrLTL (p1, p2)}  

singleVAR: var = VAR {[(One var, None)]}
| LTLNOT var = VAR {[(Zero var, None)]}
| var = VAR LPAR  n = INTE RPAR {[(One var, Some n)]}

existVar:
| {[]}
| p = singleVAR {p}
| p1 = singleVAR  COMMA  p2 = existVar {append p1 p2 }

term:
| str = VAR { Var str }
| n = INTE {Number n}
| LPAR r = term RPAR { r }
| a = term b = INTE {Minus (a, Number (0 -  b))}

| LPAR a = term MINUS b = term RPAR {Minus (a, b )}

| LPAR a = term PLUS b = term RPAR {Plus (a, b)}



pure:
| TRUE {TRUE}
| FALSE {FALSE}
| NEGATION LPAR a = pure RPAR {Neg a}
| LPAR r = pure RPAR { r }
| a = term GT b = term {Gt (a, b)}
| a = term LT b = term {Lt (a, b)}
| a = term GTEQ b = term {GtEq (a, b)}
| a = term LTEQ b = term {LtEq (a, b)}
| a = term EQ b = term {Eq (a, b)}
| a = pure CONJ b = pure {PureAnd (a, b)}
| a = pure DISJ b = pure {PureOr (a, b)}



es:
| EMPTY { Emp }
| LBRACK signals = existVar RBRACK 
{
  
  Instance (signals) }
  
| LPAR r = es RPAR { r }
| a = es CONCAT b = es { Cons(a, b) } 
| LPAR a = es RPAR POWER KLEENE {Kleene a}
| LPAR r = es RPAR n = term { Ttimes (r,  n) }
| LPAR a = es RPAR POWER OMEGA {Omega a}

effect:
| LPAR r = effect RPAR { r }
| a = pure  CONJ  b= es  {Effect (a, b)}
| a = effect  DISJ  b=effect  {Disj (a,b)}
| LPAR LBrackets nn= existVar RBrackets  eff= effect RPAR{
  let rec helper (eff:effect) :effect = 
  (match eff with 
    Effect (p, es) -> Effect (p, es) 
  | Disj (eff1, eff2) ->  Disj (helper eff1, helper eff2)  
  )
  in 
  helper eff}


entailment:
| lhs = effect   ENTIL   rhs = effect { (lhs, rhs)}

pRog_aux:
| {Halt}
| NOTHING { Halt }
| PAUSE   { Yield } 
| EMIT s = VAR  {Emit (s, None)}

| EMIT s = VAR  LPAR n =  INTE RPAR {Emit (s, Some n)}

| LOOP LBRACK p = pRog RBRACK { Loop p}
| SIGNAL s = VAR SIMI p = pRog { Declear (s, p)}
| PRESENT s = VAR THEN p1 = pRog ELSE p2 = pRog END PRESENT { If (s, p1, p2)}
| TRAP mn = VAR IN p1 = pRog END TRAP {Trap (mn, p1)}
| EXIT mn = VAR  {Break mn}
(*| EXIT mn = VAR d = INTE  {Exit (mn, d)}*)
| RUN mn = VAR {Run mn}
| ABORT p = pRog  WHEN s = VAR {Suspend (p, s)}
| AWAIT mn = VAR {Await mn}
| SUSPEND p = pRog WHEN mn = VAR {Suspend(p, mn)}
| ASYNC mn = VAR  LBRACK p = pRog RBRACK {Async(mn, p, NoneAct)}

pRog:
| p = pRog_aux {p}
| p1 = pRog SIMI p2 = pRog{ Seq (p1, p2)}
| LPAR p1 = pRog RPAR PAR LPAR p2 = pRog RPAR{ Fork (p1, p2)}


argueVAR: var = VAR {([(Zero var, None)], [(Zero var, None)])}
| IN var = VAR {([(Zero var, None)], [])}
| OUT var = VAR {([], [(Zero var, None)])}
| INOUT var = VAR {([(Zero var, None)], [(Zero var, None)])}

argueListVar:
| {([], [])}
| p = argueVAR {p}
| p1 = argueVAR  COMMA  p2 = argueListVar {
  let (in1, out1) = p1 in 
  let (in2, out2) = p2 in 
  (append in1 in2, append out1 out2) }


specProg: 
| HIPHOP MODULE nm = VAR LPAR augur = argueListVar  RPAR
  LSPEC REQUIRE pre = effect ENSURE post = effect RSPEC 


  LBRACK p = pRog RBRACK


  
  {
    let (ins, out) = augur in 
    (nm, ins, out, pre, post , p)}

| HIPHOP MODULE nm = VAR LPAR augur = argueListVar  RPAR

  LBRACK p = pRog RBRACK

  {
    let (ins, out) = augur in 
    (nm, ins, out, Effect (TRUE, Emp), Effect (TRUE, Emp), p)}

