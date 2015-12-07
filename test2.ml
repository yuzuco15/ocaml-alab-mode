type tree = Empty | Node of tree * int * tree

let rec count (r: tree): (int * int) = exit(*{}*)0





  (*match tree with
    Empty -> 0
  | Node (l, n, r) -> n + (count l) + (count r)
   *)

(*
何番のゴールに対してか: 入力 n
match or refine
どの変数に対して match (or refine) したいか

-> match or refine した結果を返す
 *)					       
