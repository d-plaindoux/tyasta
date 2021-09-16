module Size

open Ast

val size : (#a:Type) -> term a -> nat
