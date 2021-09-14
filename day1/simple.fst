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

let rec lookup n c =
    match c with
    | Nil        -> None
    | (m,i) :: l -> if m = n then Some i else lookup n l

let rec lengthInfer e =
    match e with
    | Annoted e t -> 1 + lengthCheck e
    | Bound j     -> 1
    | Free x      -> 1
    | Apply e1 e2 -> lengthInfer e1 + lengthCheck e2

and lengthCheck e =
    match e with 
    | Inferable e -> 1 + lengthInfer e
    | Lambda e    -> 1 + lengthCheck e

let rec substInfer i r e =
    match e with
    | Annoted e t -> Annoted (substCheck i r e) t
    | Bound j     -> if i=j then r else Bound j
    | Free x      -> Free x
    | Apply e1 e2 -> Apply (substInfer i r e1) (substCheck i r e2)

and substCheck i r e =
    match e with 
    | Inferable e -> Inferable (substInfer i r e)
    | Lambda e    -> Lambda (substCheck (i + 1) r e)

val substInfer_constant : 
        i:nat -> 
        r:(term infer){lengthInfer r = 1} ->
        e:term infer ->
        Lemma (ensures
            (let e' = substInfer i r e in
                 lengthInfer e' = lengthInfer e
            )
        )
        (decreases e)

val substCheck_constant : 
        i:nat -> 
        r:(term infer){lengthInfer r = 1} ->
        e:term check ->
        Lemma (ensures
            (let e' = substCheck i r e in
                 lengthCheck e' = lengthCheck e
            )
        )
        (decreases e)
        [SMTPat (substCheck i r e)]

let rec substInfer_constant i r e = 
    match e with
    | Annoted e t -> substCheck_constant i r e
    | Bound j     -> ()
    | Free x      -> ()
    | Apply e1 e2 -> substInfer_constant i r e1; 
                     substCheck_constant i r e2

and substCheck_constant i r e = 
    match e with
    | Inferable e -> substInfer_constant i r e
    | Lambda e    -> substCheck_constant (i+1) r e

let rec kindInfer g ty kd =
    match ty,kd with
    | TFree x, Star -> 
        (match lookup x g with 
        | Some (HasKind Star) -> return ()
        | Some _              -> throwError "identifier is not a Star"
        | None                -> throwError "unknown identifier")
    | Function a b, Star -> 
        kindInfer g a Star >>= (fun _ -> kindInfer g b Star)

let rec typeInfer i g e =
    match e with
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
            assert (lengthInfer r = 1);
            let e' = substCheck 0 r e in
            typeCheck (i + 1) ((Local i, HasType t) :: g) e' t'
        | _             -> throwError "type mismatch")

let typeInfer0 : context -> term infer -> result typeL = 
    typeInfer 0
