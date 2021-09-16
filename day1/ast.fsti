module Ast

type infer : Type = 
    | Infer     : infer

type check = 
    | Check     : check

type term       : Type -> Type = 
    | Annoted   : term check -> typeL -> term infer
    | Bound     : nat -> term infer
    | Free      : name -> term infer
    | Apply     : term infer -> term check -> term infer
    | Inferable : term infer -> term check
    | Lambda    : term check -> term check

and name        : Type = 
    | Global    : string -> name
    | Local     : nat -> name
    | Quote     : nat -> name

and typeL       : Type = 
    | TFree     : name -> typeL
    | Function  : typeL -> typeL -> typeL

type kindL      : Type = 
    | Star      : kindL

type info       : Type =
    | HasKind   : kindL -> info
    | HasType   : typeL -> info
