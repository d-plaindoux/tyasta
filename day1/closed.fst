module Closed

open Try
open Ast

let rec closed l = function
    | Annoted e t -> closed l e
    | Bound j     -> if List.mem j l then return () else throwError "unbound variable"
    | Free x      -> return ()
    | Apply e1 e2 -> closed l e1 >>= (fun _ -> closed l e2)
    | Inferable e -> closed l e
    | Lambda e    -> closed l e
