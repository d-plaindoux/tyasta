module Utils

val (<%)     : (#a:Type) -> (#b :Type) -> (#c :Type) -> (b -> c) -> (a -> b) -> a -> c
val (%>)     : (#a:Type) -> (#b :Type) -> (#c :Type) -> (a -> b) -> (b -> c) -> a -> c
val constant : (#a:Type) -> (#b :Type) -> b -> a -> Tot b
val flip     : (#a:Type) -> (#b :Type) -> (#c :Type) -> (a -> b -> c) -> (b -> a -> c)
