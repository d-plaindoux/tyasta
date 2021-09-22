module Utils

let (<%) f g = fun a -> f (g a)
let (%>) g f = f <% g
let constant b _ = b
let flip f a b = f b a
