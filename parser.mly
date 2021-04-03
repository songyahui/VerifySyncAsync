%{ open Ast %}
%{ open List %}

%token <string> STRING
%token <string> VAR 
%token <int> INTE
%token <float> FLOAT
%token  LPAR RPAR SIMI LBrackets  RBrackets  COMMA LBRACK RBRACK      
%token  MINUS PLUS POWER TRUEToken COLON FALSEToken NEGATION
%token EOF GT LT EQ CONJ GTEQ LTEQ ENTIL EMPTY DISJ  CONCAT 
%token VARKEY KLEENE NEW EXPORTS


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
| l = literal {Literal l }
| str = VAR ex = varOraccess 
  {
    match ex with 
    | None -> Variable str
    | Some obj -> Access  (str:: obj)
  }
| ex1 = expression LPAR obj  = call_aux RPAR {FunctionCall (ex1, obj)}
| NEW ex = expression {NewExpr ex}
| b = binOp  {b}

varOraccess:
| {None}
| CONCAT f = VAR  obj =  access_aux {Some (f::obj)}

call_aux:
| {[]}
| ex = expression obj = call_aux1 {ex::obj}

call_aux1:
| {[]}
| COMMA obj = call_aux {obj}

binOp:
| e1 = expression PLUS e2 = expression   {BinOp ( "+", e1, e2)}
| e1 = expression MINUS e2 = expression   {BinOp ( "-", e1, e2)}
| e1 = expression EQ e2 = expression   {BinOp ( "=", e1, e2)}
| e1 = expression KLEENE e2 = expression   {BinOp ( "*", e1, e2)}
| e1 = expression LT e2 = expression   {BinOp ( "<", e1, e2)}
| e1 = expression GT e2 = expression   {BinOp ( ">", e1, e2)}
| e1 = expression LTEQ e2 = expression   {BinOp ( "<=", e1, e2)}
| e1 = expression GTEQ e2 = expression   {BinOp ( ">=", e1, e2)}


statement:
| s = STRING {ImportStatement s}
| VARKEY str = VAR EQ ex =expression SIMI {VarDeclear (str, ex) }
| EXPORTS CONCAT ex = expression EQ ex2 = expression  SIMI{ExportStatement(ex,ex2)}
