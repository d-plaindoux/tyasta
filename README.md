# Tyasta: A journey with F*

[tyasta- Q. verb. to (put to the) test, *verify](https://www.elfdict.com/w/verify?include_old=1)

## Introduction

[A tutorial implementation of a dependently typed lambda calculus](https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf)

## Day 1: Simply Typed Lambda Calculus

### Desiging the term algebra

The first difference with the original design suggested in paper is the term algebra. I decide to do it using 
a GADT instead of two separated ADT.

```f*
type infer : Type = 
    | Infer     : infer

type check = 
    | Check     : check

type term : Type -> Type = 
    | Annoted   : term check -> typeL -> term infer
    | Bound     : nat -> term infer
    | Free      : name -> term infer
    | Apply     : term infer -> term check -> term infer
    | Inferable : term infer -> term check
    | Lambda    : term check -> term check
```

Then we are able to a generalized `length` and `subst`.

```f*
val length : (#a:Type) -> term a -> nat
let rec length = function
    | Annoted e t -> 1 + length e
    | Bound j     -> 1
    | Free x      -> 1
    | Apply e1 e2 -> length e1 + length e2
    | Inferable e -> 1 + length e
    | Lambda e    -> 1 + length e
```

The same design can be applied to the substitution function.

### Type checker termination

During this first day the main problem I'm facing is the proof of `typeCheck` and `typeInfer` termination.
This is actually normal when we take a closer look at the abstraction type verification code:

```haskell
type↓ i G (Lam e) (Fun τ τ′)
  =type↓ (i+1) ((Local i,HasType τ):G) (subst↓ 0 (Free (Local i)) e) τ′
```
The system is not able to check if the term `(subst↓ 0 (Free (Local i)) e)` decreases. This can be simply solved 
using our metric dedicated to the term algebra: `lenght`. Thanks to this metric we can see the size of `Free (Local i)` and
`Bound _` are the same. So we can "easily" define a lemma in this case:

```f*
val subst_constant : 
        #a:Type ->
        i:nat -> 
        r:(term infer){length r = 1} ->
        e:term a ->
        Lemma (ensures
            (let e' = subst i r e in
                 length e' = length e
            )
        )
        (decreases e)
        [SMTPat (subst i r e)]
```

This lemma says: if we replace a bound expression - of size 1 - with a term of size 1 then the size of the initial term 
and the size of the computed term are equals. In addition we specify the decreased term and finally we add explicit to 
the STM solver the pattern `subst i r e` i.e. `[SMTPat (subst i r e)]` to be used when the termination proof should be 
done.

Now we are ready to proof the termination !

```f*
let rec typeInfer i g = function
    ...
    
and typeCheck i g e t =
    match e with
    | Inferable e -> constant () <$> unless (typeInfer i g e) ((=) t) (throwError "type mismatch")
    | Lambda e    -> 
        (match t with
        | Function t t' -> 
            let r  = Free (Local i) in
            (* This assert is used by the STM solver in order to apply the lemma *)
            assert (length r = 1); 
            typeCheck (i + 1) ((Local i, HasType t) :: g) (subst 0 r e) t'
        | _ -> 
            throwError "type mismatch")    
```

### Evaluation and coinductive types

To be continued ...

## Day 2: Dependent types
