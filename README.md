# Tyasta: A journey with F*

[tyasta- Q. verb. to (put to the) test, *verify](https://www.elfdict.com/w/verify?include_old=1)

## Introduction

[A tutorial implementation of a dependently typed lambda calculus](https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf)

## Day 1: Simply Typed Lambda Calculus

### 1am: Desiging the term algebra

The first difference with the original design suggested in the paper is the term algebra. I decide to do it using 
a GADT instead of two separated ADTs.

```f*
type infer : Type = 
    | Infer     : infer

type check : Type = 
    | Check     : check

type term : Type -> Type = 
    | Annoted   : term check -> typeL -> term infer
    | Bound     : nat -> term infer
    | Free      : name -> term infer
    | Apply     : term infer -> term check -> term infer
    | Inferable : term infer -> term check
    | Lambda    : term check -> term check
    
and typeL : Type = ...
```

Then we are able to a generalized `size` and `subst`.

```f*
val size : (#a:Type) -> term a -> nat
let rec size = function
    | Annoted e t -> 1 + length e
    | Bound j     -> 1
    | Free x      -> 1
    | Apply e1 e2 -> length e1 + length e2
    | Inferable e -> 1 + length e
    | Lambda e    -> 1 + length e
```

The same design can be applied to the substitution function.

### 2am: Type checker termination

During this first day the main problem I'm facing is the proof of `typeCheck` and `typeInfer` termination.
This is actually normal when we take a closer look at the abstraction type verification code:

```haskell
type↓ i G (Lam e) (Fun τ τ′)
  =type↓ (i+1) ((Local i,HasType τ):G) (subst↓ 0 (Free (Local i)) e) τ′
```
The system is not able to check if the term `(subst↓ 0 (Free (Local i)) e)` decreases. This can be simply solved 
using our metric dedicated to the term algebra: `size`. Thanks to this metric we can see the size of `Free (Local i)` and
`Bound _` are the same. So we can "easily" define a lemma in this case:

```f*
val subst_constant : 
        #a:Type ->
        i:nat -> 
        r:(term infer){size r = 1} ->
        e:term a ->
        Lemma (ensures
            (let e' = subst i r e in
                 size e' = size e
            )
        )
        (decreases e)
        [SMTPat (subst i r e)]
```

This lemma says: if we replace a bound expression - of size 1 - with a term of size 1 then the size of the initial term 
and the size of the computed term are equals. In addition we specify the decreased term and finally we explicit to the 
STM solver the pattern `subst i r e` i.e. `[SMTPat (subst i r e)]` to be used when the termination proof should be done.

Now we are ready to prove the termination!

```f*
let rec typeInfer i g = function
    ...
    
and typeCheck i g e t =
    match e with
    | Inferable e -> 
        constant () <$> unless (typeInfer i g e) ((=) t) (throwError "type mismatch")
    | Lambda e    -> 
        (match t with
        | Function t t' -> 
            let r  = Free (Local i) in
            (* This assert is used by the STM solver in order to apply the lemma *)
            assert (size r = 1); 
            typeCheck (i + 1) ((Local i, HasType t) :: g) (subst 0 r e) t'
        | _ -> 
            throwError "type mismatch")    
```

QED.

Note: The assert can be replaced by the application of the lemma via `subst_constant i r e`.

### 3am: Open and Closed terms

In the general design, manipulated terms are closed. A closed term has no free 
variable i.e. each De Bruijn indice corresponds to a level of enclosing lambda. 
Neverthless, with the current abstract syntax we can build terms like:

```f*
let ex = Lambda (Inferable (Bound 4))
```

Then type checking such term should leads to an unbound variable error. In the paper we 
can see that such case is missing as expressed page 1010: "The type checker will never 
encounter a bound variable; correspondingly the function type↑ has no case for Bound".

Well that's fine but in F* we cannot remove such pattern matching or we have to prove 
that such case never occurs!

In order to solve this problem we should observe how the type checker works. Each `Bound`
term is replaced by a `Free (Local i)`. Based on this we can define a function deciding
if a given term is closed or not using the same technic e.g the substitution in order to 
eliminate such `Bound` terms. 

```f*
val closed  : #a:Type -> nat -> e:term a -> Tot bool (decreases (size e))

let rec closed i = function
    | Annoted e t -> closed i e
    | Bound j     -> false
    | Free x      -> true
    | Apply e1 e2 -> closed i e1 && closed i e2
    | Inferable e -> closed i e
    | Lambda e    -> let r  = Free (Local i) in
                     assert (size r = 1);
                     closed (i+1) (subst 0 r e)
```

This `closed` predicate uses the same pattern when managing a `Lambda e` i.e. it creates 
a term for the substitution and eliminates the corresponding `Bound`. Then we can provide
refined types in the type checker signatures using such predicate:

```f*
val typeInfer   : n:nat -> context -> e:(term infer){closed n e} -> Tot (result typeL) (decreases (size e))
val typeCheck   : n:nat -> context -> e:(term check){closed n e} -> t:typeL -> Tot (result unit) (decreases %[size e;t])
val typeInfer0  : context -> e:(term infer){closed 0 e} -> result typeL
```

Finally we can remove the pattern matching dedicated to `Bound` term because the term is `closed`.

### 4am: Evaluation and coinductive types

To be continued ...

## Day 2: Dependent types
