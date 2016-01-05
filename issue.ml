type ltable = (string * string list) list
type person_t = {name: string; age: int}
type rtable = (person_t list * int list) list
type person_tt = person_t
type tuple_t = (person_t * person_t)

let f: ltable -> int = fun l -> (exit(*{}*)0)

let g: rtable -> int = fun r -> (exit(*{}*)1)

let h: person_tt -> int = fun p -> (exit(*{}*)2)

let i: tuple_t -> int = fun t -> (exit(*{}*)3)
