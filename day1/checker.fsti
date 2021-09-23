module Checker

open Try
open Ast

val size       : #a:Type -> term a -> nat
val closed     : #a:Type -> nat -> e:term a -> Tot bool (decreases (size e))

val toClosed   : #a:Type -> e:term a -> Tot (result (t:(term a){closed 0 t}))

val typeInfer  : n:nat -> context -> e:(term infer){closed n e} -> Tot (result typeL) (decreases (size e))
val typeCheck  : n:nat -> context -> e:(term check){closed n e} -> t:typeL -> Tot (result unit) (decreases %[size e;t])
val typeInfer0 : context -> e:(term infer){closed 0 e} -> result typeL
