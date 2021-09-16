module Size

open Ast

let rec size = function
    | Annoted e t -> 1 + size e
    | Bound j     -> 1
    | Free x      -> 1
    | Apply e1 e2 -> size e1 + size e2
    | Inferable e -> 1 + size e
    | Lambda e    -> 1 + size e
