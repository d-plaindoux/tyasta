module Eval

open Ast

type value : Type =
    | Value : value

type neutral : Type =
    | Neutral : neutral

type vterm      : Type -> Type =
    | VLam      : nat -> vterm value -> vterm value
    | VNeutral  : vterm neutral -> vterm value
    | NFree     : name -> vterm neutral
    | NApp      : vterm neutral -> vterm value -> vterm neutral

