module Try

open Utils

let return = Success

let throwError = Failure

let fold = 
    function
    | Success v -> fun s _ -> s v
    | Failure v -> fun _ e -> e v

let (<$>) f r = 
    fold r (return <% f) throwError

let (<*>) f r =
    fold f (flip (<$>) r) throwError

let join r =
    fold r id throwError

let (>>=) r f = 
    join (f <$> r)

let unless r f e = 
    r >>= (fun r -> if not (f r) then e else return r)
