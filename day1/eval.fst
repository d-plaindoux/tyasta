module Eval

open Utils
open Try
open Ast

val get : nat -> env -> result (vterm value)
let rec get i env =
    match i, env with
    | 0, e::_ -> return e
    | i, _::t -> get (i-1) t
    | _, _ -> throwError "Not found"

val vapply : vterm value -> vterm value -> Dv (result (vterm value))

let rec eval = function
    | Annoted e _ -> eval e
    | Bound j     -> get j
    | Free x      -> constant (return (VNeutral (NFree x)))
    | Apply e1 e2 -> (fun d -> match eval e1 d, eval e2 d with
                     | Success v1, Success v2 -> vapply v1 v2
                     | Failure f, _           -> throwError f
                     | _, Failure f           -> throwError f)
    | Inferable e -> eval e
    | Lambda e    -> VClosure e %> return

and vapply e v =
    match e with 
    | VClosure e d -> eval e (v::d)
    | VNeutral n   -> return (VNeutral (NApp n v))