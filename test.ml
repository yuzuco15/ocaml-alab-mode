type t = { a : int; b : float; c : string }

let f x = x + 1;;
let g {a = a; b = b; c = c} (t: t) = match t with
{a = a, b = b, c = c} -> exit(*{ }*)0


