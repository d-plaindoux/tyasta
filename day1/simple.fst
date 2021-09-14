module Simple

// -------------------------------------------------------------------------------------
// Monadic result
// -------------------------------------------------------------------------------------

let return = Inr

let throwError = Inl

let (<$>) f =
    function
    | Inl s -> throwError s
    | Inr a -> return (f a)

let (>>=) r f =
    match r with
    | Inl s -> throwError s
    | Inr a -> f a

let unless r f e = 
    r >>= (fun r -> if f r then return r else e)

// -------------------------------------------------------------------------------------

let constant b _ = b

let rec lookup n = function
    | Nil        -> None
    | (m,i) :: l -> if m = n then Some i else lookup n l

let rec length = function
    | Annoted e t -> 1 + length e
    | Bound j     -> 1
    | Free x      -> 1
    | Apply e1 e2 -> length e1 + length e2
    | Inferable e -> 1 + length e
    | Lambda e    -> 1 + length e

let rec subst i r = function
    | Annoted e t -> Annoted (subst i r e) t
    | Bound j     -> if i=j then r else Bound j
    | Free x      -> Free x
    | Apply e1 e2 -> Apply (subst i r e1) (subst i r e2)
    | Inferable e -> Inferable (subst i r e)
    | Lambda e    -> Lambda (subst (i + 1) r e)

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

let rec subst_constant i r = function 
    | Annoted e t -> subst_constant i r e
    | Bound j     -> ()
    | Free x      -> ()
    | Apply e1 e2 -> subst_constant i r e1; 
                     subst_constant i r e2
    | Inferable e -> subst_constant i r e
    | Lambda e    -> subst_constant (i+1) r e

let rec kindInfer g ty kd =
    match ty, kd with
    | TFree x, Star -> 
        (match lookup x g with 
        | Some (HasKind Star) -> return ()
        | Some _              -> throwError "identifier is not a Star"
        | None                -> throwError "unknown identifier")
    | Function a b, Star -> 
        kindInfer g a Star >>= (fun _ -> kindInfer g b Star)

let rec typeInfer i g = function
    | Annoted e t -> kindInfer g t Star >>= (fun _ -> constant t <$> typeCheck i g e t)
    | Bound i     -> throwError "Not a bound variable"
    | Free x      ->
        (match lookup x g with
        | Some (HasType t) -> return t
        | Some _           -> throwError "not a type"
        | None             -> throwError "unknown identifier")
    | Apply e e'  ->
        typeInfer i g e >>= (function
        | Function t t' -> constant t' <$> typeCheck i g e' t
        | _             -> throwError "illegal application")
    
and typeCheck i g e t =
    match e with
    | Inferable e -> constant () <$> unless (typeInfer i g e) ((=) t) (throwError "type mismatch")
    | Lambda e    -> 
        (match t with
        | Function t t' -> 
            let r  = Free (Local i) in
            assert (length r = 1);
            typeCheck (i + 1) ((Local i, HasType t) :: g) (subst 0 r e) t'
        | _ -> 
            throwError "type mismatch")

let typeInfer0 = typeInfer 0
