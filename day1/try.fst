module Try

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
