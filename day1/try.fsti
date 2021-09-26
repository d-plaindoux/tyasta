module Try

// TODO: Use definitions from F* Pervasive library

type result a  : Type = 
    | Success  : a -> result a
    | Failure  : string -> result a

val return     : #a:Type -> a -> result a
val throwError : #a:Type -> string -> result a

val fold       : #a:Type -> #b:Type -> result a -> (a -> b) -> (string -> b) -> b
val (<$>)      : #a:Type -> #b:Type -> (a -> b) -> result a -> result b
val (<*>)      : #a:Type -> #b:Type -> result (a -> b) -> result a -> result b
val join       : #a:Type -> result (result a) -> result a
val (>>=)      : #a:Type -> #b:Type -> result a -> (a -> result b) -> result b
val unless     : #a:Type -> result a -> (a -> bool) -> result a -> result a

