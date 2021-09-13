# Tyasta: A journey with F*

[tyasta- Q. verb. to (put to the) test, *verify](https://www.elfdict.com/w/verify?include_old=1)

## Introduction

[A tutorial implementation of a dependently typed lambda calculus](https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf)

## Day 1: Simply Typed Lambda Calculus

During this first day the main problem I'm facing is the proof of `typeCheck` and `typeInfer` termination.
This is in fact normal when we look closer at the type checking code of abstraction:
```haskell
type↓ i G (Lam e) (Fun τ τ′)
  =type↓ (i+1) ((Local i,HasType τ):G) (subst↓ 0 (Free (Local i)) e) τ′
```

The system is not able to check if the term `(subst↓ 0 (Free (Local i)) e)` decreases.

... // TODO

## Day 2: Dependent types
