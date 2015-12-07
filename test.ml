type t = { a : int; b : float; c : string }

let f x = x + 1;;
let g ({a = a; b = b; c = c} as v) (t: t) = a + exit(*{}*)3
(*
let z = 3
let h (x: int): int =
  let i y = y + z in
  exit 3
  *)  
