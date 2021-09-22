module Closed

open Try
open Ast

let rec closed l = function
    | Annoted e t -> closed l e
    | Bound j     -> List.mem j l
    | Free x      -> true
    | Apply e1 e2 -> closed l e1 && closed l e2
    | Inferable e -> closed l e
    | Lambda e    -> closed l e
