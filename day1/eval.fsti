module Eval

open Ast

type value      : Type =
    | Value     : value

type neutral    : Type =
    | Neutral   : neutral

type vterm      : Type -> Type =
    | VClosure  : term check -> env -> vterm value
    | VNeutral  : vterm neutral -> vterm value
    | NFree     : name -> vterm neutral
    | NApp      : vterm neutral -> vterm value -> vterm neutral

and env         : Type = list (vterm value)

val eval        : #a:Type -> term a -> env -> Dv (result (vterm value))