module Simple

// -------------------------------------------------------------------------------------
// Monadic result
// -------------------------------------------------------------------------------------

type result a : Type = either string a

val return     : (#a:Type) -> a -> Tot (result a)
val throwError : (#a:Type) -> string -> Tot (result a)
val (<$>)      : (#a:Type) -> (#b:Type) -> (a -> b) -> result a -> Tot (result b)
val (>>=)      : (#a:Type) -> (#b:Type) -> result a -> (a -> result b) -> Tot (result b)
val unless     : (#a:Type) -> result a -> (a -> bool) -> result a -> Tot (result a)

// -------------------------------------------------------------------------------------

type infer : Type = 
    | Infer     : infer

type check = 
    | Check     : check

type term       : Type -> Type = 
    | Annoted   : term check -> typeL -> term infer
    | Bound     : nat -> term infer
    | Free      : name -> term infer
    | Apply     : term infer -> term check -> term infer
    | Inferable : term infer -> term check
    | Lambda    : term check -> term check

and name        : Type = 
    | Global    : string -> name
    | Local     : nat -> name
    | Quote     : nat -> name

and typeL       : Type = 
    | TFree     : name -> typeL
    | Function  : typeL -> typeL -> typeL

type kindL      : Type = 
    | Star      : kindL

type info       : Type =
    | HasKind   : kindL -> info
    | HasType   : typeL -> info

type context    : Type = list (name * info)

val constant    : (#a:Type) -> (#b :Type) -> b -> a -> Tot b

val lookup      : name -> context -> option info

val size        : (#a:Type) -> term a -> nat

val subst       : (#a:Type) -> nat -> term infer -> (e:term a) -> Tot (term a) (decreases e)

val kindInfer   : context -> typeL -> kindL -> result unit 

val typeInfer   : nat -> context -> (e:term infer) -> Tot (result typeL) (decreases (size e))
val typeCheck   : nat -> context -> (e:term check) -> (t:typeL) -> Tot (result unit) (decreases %[size e;t])
val typeInfer0  : context -> term infer -> result typeL