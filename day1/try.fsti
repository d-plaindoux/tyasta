module Try

type result a : Type = either string a

val return     : (#a:Type) -> a -> Tot (result a)
val throwError : (#a:Type) -> string -> Tot (result a)
val (<$>)      : (#a:Type) -> (#b:Type) -> (a -> b) -> result a -> Tot (result b)
val (>>=)      : (#a:Type) -> (#b:Type) -> result a -> (a -> result b) -> Tot (result b)
val unless     : (#a:Type) -> result a -> (a -> bool) -> result a -> Tot (result a)
