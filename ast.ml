(* Hiphop.js Syntax *)
(*-| Representations for modules' exports.*)



type statement = 
    | ImportStatement of string
   


(*
 | TypeAliasDeclaration of _type * _type
     | ModuleDeclaration of mn * exportSet

    | TypeDeclaration of _type * (_type list)
    | PortTypeDeclaration of mn * _type
    | PortDeclaration of mn * ( mn list)  * expression
    | FunctionTypeDeclaration of mn * _type
    | FunctionDeclaration of pattern * expression
    | PortModuleDeclaration of mn * exportSet
type exportSet = AllExport
        | SubsetExport of ( exportSet list)
        | FunctionExport of mn
        | TypeExport of mn *( exportSet option)


(*-| Representations for Elm's type syntax.*)
type _type = 
    | TypeConstructor of (mn list) * ( _type list)
    | TypeVariable of mn
    | TypeRecordConstructor of _type * ( ( mn* _type ) list)
    | TypeRecord of ( ( mn*  _type ) list)
    | TypeTuple of ( _type list)
    | TypeApplication of _type * _type

type literal = Character of char
    | String of string
    | Integer of int
    | Float of float


type pattern = PWildcard
    | PVariable of mn
    | PLiteral of literal
    | PApplication of pattern * pattern
    | PTuple of ( pattern list)
    | PRecord of (mn list)

    (*
    | PConstructor of mn
    | PCons of pattern * pattern
    | PList of ( pattern list)
    | PA of pattern * mn
    *)


type expression = Literal of literal 
    | Variable of mn
    | List of ( expression list)
    | Tuple of ( expression list)
    | Access of expression * ( mn list)
    | AccessFunction of mn
    | Record of ( ( mn * expression ) list)
    | RecordUpdate of mn * ( ( mn * expression )list)
    | If of expression * expression * expression
    | Let of (  ( pattern* expression )list ) * expression
    | Case of expression * ( ( pattern * expression ) list)
    | Lambda of (pattern list) * expression
    | Application of expression * expression
    | BinOp of expression * expression * expression
    | Glsl 

*)