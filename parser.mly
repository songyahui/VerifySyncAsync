%{ open Ast %}
%{ open List %}

%token <string> STRING
%token <string> VAR 
%token <int> INTE
%token <float> FLOAT
%token  LPAR RPAR SIMI LBrackets  RBrackets  COMMA LBRACK RBRACK      
%token  MINUS PLUS POWER TRUEToken COLON FALSEToken NEGATION
%token EOF GT LT EQ CONJ GTEQ LTEQ ENTIL EMPTY DISJ  CONCAT 
%token VARKEY KLEENE NEW EXPORTS HIPHOP MODULE IN OUT 
%token EMIT AWAIT


%start program
%type <(Ast.statement) list> program


%%

program:
| EOF {[]}
| a = statement r = program { append [a] r }


access_aux:
| {[]}
| CONCAT f = VAR obj = access_aux  {f::obj}

literal: 
| n = INTE {INT n}
| str = STRING {STRING str}


expression:
| NEW ex = expression {NewExpr ex}
| b = binary {b}
| EMIT LPAR ex = expression RPAR {Emit ex}
| AWAIT LPAR ex = expression RPAR {Await ex}

expr_aux:
| l = literal {Literal l }
| str = VAR ex = varOraccess 
  {
    match ex with 
    | None -> Variable str
    | Some obj -> Access  (str:: obj)
  }


varOraccess:
| {None}
| CONCAT f = VAR  obj =  access_aux {Some (f::obj)}

call_aux:
| {[]}
| ex = expression obj = call_aux1 {ex::obj}

call_aux1:
| {[]}
| COMMA obj = call_aux {obj}

binary :
| ex1 = expr_aux v = maybebinary_aux {
  match v with 
  | None -> ex1 
  | Some (Left (str, ex2)) -> BinOp (str, ex1, ex2)
  | Some (Right (obj)) -> FunctionCall (ex1, obj)
}

maybebinary_aux:
| {None}
| obj = binary_aux {
  Some obj
}

binary_aux:
| LPAR obj  = call_aux RPAR {Right (obj)}
| PLUS e2 = expression   {Left ( "+", e2)}
| MINUS e2 = expression   { Left( "-", e2)}
| EQ e2 = expression   {Left ( "=", e2)}
| KLEENE e2 = expression   {Left ( "*", e2)}
| LT e2 = expression   {Left ( "<", e2)}
| GT e2 = expression   {Left ( ">", e2)}
| LTEQ e2 = expression   {Left ( "<=", e2)}
|  GTEQ e2 = expression   {Left ( ">=", e2)}


statement:
| s = STRING {ImportStatement s}
| VARKEY str = VAR EQ ex = expression SIMI {VarDeclear (str, ex) }
| EXPORTS CONCAT ex = VAR EQ ex2 = expression  SIMI{ExportStatement(Variable ex,ex2)}
| HIPHOP MODULE  mn = VAR LPAR parm = parameter RPAR LBRACK  ex = expression RBRACK {ModelDeclear (mn, parm, ex)}

param:
| IN str = VAR {IN str}
| OUT str = VAR {OUT str}


parameter:
| {[]}
| p = param obj = maybeNext {
  match obj with 
  | None -> [p]
  | Some obj -> p::obj}

maybeNext:
| {None}
| COMMA v = parameter {Some v}
