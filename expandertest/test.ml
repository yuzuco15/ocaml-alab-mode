type t = { a : int; b : float }

let f x = x + 1
let g ({a = a; b = b} as r) = a + exit 3
