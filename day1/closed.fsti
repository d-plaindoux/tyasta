module Closed

open Try
open Ast

val closed : (#a:Type) -> list nat -> e:term a -> Tot (result unit) (decreases e)

