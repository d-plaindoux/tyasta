module Checker

open Try
open Ast

type context    : Type = list (name * info)

val size : (#a:Type) -> term a -> nat

val typeInfer   : nat -> context -> (e:term infer) -> Tot (result typeL) (decreases (size e))
val typeCheck   : nat -> context -> (e:term check) -> (t:typeL) -> Tot (result unit) (decreases %[size e;t])
val typeInfer0  : context -> term infer -> result typeL
