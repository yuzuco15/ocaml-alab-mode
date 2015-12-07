open Asttypes
open Typedtree

(* output channel *)
let ppf = Format.formatter_of_out_channel stdout

(********** add types of variables to env **********)

(* 環境の型。Env.t とは別物なのに注意 *)
(* type env_t = string * type_expr *)

(* add_pattern : env_t -> Typedtree.pattern -> env_t *)
(* add all the pattern variables and their types to env *)
let rec add_pattern env pat = match pat.pat_desc with
    Tpat_any -> env
  | Tpat_var (_, {txt = st}) -> (st, pat.pat_type) :: env
  | Tpat_alias (p, _, {txt = st}) -> (st, pat.pat_type) :: add_pattern env p
  | Tpat_constant (_) -> env
  | Tpat_tuple (ps) -> List.fold_left add_pattern env ps
  | Tpat_construct (_, _, ps) -> List.fold_left add_pattern env ps
  | Tpat_variant (_, None, _) -> env
  | Tpat_variant (_, Some (p), _) -> add_pattern env p
  | Tpat_record (lst, _) ->
      List.fold_left (fun env (_, _, p) -> add_pattern env p) env lst
  | Tpat_array (ps) -> List.fold_left add_pattern env ps
  | Tpat_or (p1, p2, _) -> add_pattern (add_pattern env p1) p2
  | Tpat_lazy (p) -> add_pattern env p

(* add_bindings : env_t -> value_binding list -> env_t *)
let add_bindings env bindings =
  List.fold_left (fun env {vb_pat = pat} -> add_pattern env pat)
                 env bindings

(********** obtain types of hole and variables **********)

(* type_of_hole_in_expr : int -> expression -> type_expr * env_t *)
let rec type_of_hole_in_expr n expr = match expr.exp_desc with
    Texp_ident (_, _, _) -> raise Not_found
  | Texp_constant (_) -> raise Not_found
  | Texp_let (rec_flag, bindings, expr) ->
      begin try
        type_of_hole_in_bindings n rec_flag bindings
      with
        Not_found ->
          let (typ, env) = type_of_hole_in_expr n expr in
          (typ, add_bindings env bindings)
      end
  | Texp_function (_, cases, _) -> type_of_hole_in_cases n cases
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident ("exit")}, _)},
                [(_, Some ({exp_desc = Texp_constant (Const_int (m))}), _)])
    when m = n -> (* exit n を発見 *)
      (expr.exp_type, []) (* 穴の型と空の環境を返す *)
  | Texp_apply (expr, lst) ->
      begin try
        type_of_hole_in_expr n expr
      with
        Not_found ->
          let lst1 = List.filter (function (_, None, _) -> false
                                     | (_, Some (_), _) -> true) lst in
          let lst2 = List.map (function (_, None, _) -> assert false
                               | (_, Some (expr), _) -> expr) lst1 in
          type_of_hole_in_exprs n lst2
      end
  | Texp_match (expr, cases1, cases2, _) ->
      (* cases1 for values, cases2 for exceptions *)
      begin try
        type_of_hole_in_expr n expr
      with
        Not_found ->
          begin try
            type_of_hole_in_cases n cases1
          with
            Not_found -> type_of_hole_in_cases n cases2
          end
      end
  | Texp_try (expr, cases) ->
      begin try
        type_of_hole_in_expr n expr
      with
        Not_found -> type_of_hole_in_cases n cases
      end
  | Texp_tuple (exprs) -> type_of_hole_in_exprs n exprs
  | Texp_construct (_, _, exprs) -> type_of_hole_in_exprs n exprs
  | Texp_variant (_, None) -> raise Not_found
  | Texp_variant (_, Some (expr)) -> type_of_hole_in_expr n expr
  | Texp_record (lst, None) ->
      type_of_hole_in_exprs n (List.map (fun (_, _, expr) -> expr) lst)
  | Texp_record (lst, Some (expr)) ->
      type_of_hole_in_exprs n (expr :: List.map (fun (_, _, expr) -> expr) lst)
  | Texp_field (expr, _, _) -> type_of_hole_in_expr n expr
  | Texp_setfield (expr1, _, _, expr2) -> type_of_hole_in_exprs n [expr1; expr2]
  | Texp_array (exprs) -> type_of_hole_in_exprs n exprs
  | Texp_ifthenelse (expr1, expr2, None) ->
      type_of_hole_in_exprs n [expr1; expr2]
  | Texp_ifthenelse (expr1, expr2, Some (expr3)) ->
      type_of_hole_in_exprs n [expr1; expr2; expr3]
  | Texp_sequence (expr1, expr2) -> type_of_hole_in_exprs n [expr1; expr2]
  | Texp_while (expr1, expr2) -> type_of_hole_in_exprs n [expr1; expr2]
  | Texp_for (_, pat, expr1, expr2, _, expr3) ->
      (* pat is currently ignored *)
      type_of_hole_in_exprs n [expr1; expr2; expr3]
  | Texp_send (expr1, _, None) -> type_of_hole_in_expr n expr
  | Texp_send (expr1, _, Some (expr2)) -> type_of_hole_in_exprs n [expr1; expr2]
  | Texp_new (_, _, _) -> raise Not_found
  | Texp_instvar (_, _, _) -> raise Not_found
  | Texp_setinstvar (_, _, _, expr) -> type_of_hole_in_expr n expr
  | Texp_override (_, lst) ->
      type_of_hole_in_exprs n (List.map (fun (_, _, expr) -> expr) lst)
  | Texp_letmodule (_, _, module_expr, expr) ->
      (* module_expr is currently ignored *)
      type_of_hole_in_expr n expr
  | Texp_assert (expr) -> type_of_hole_in_expr n expr
  | Texp_lazy (expr) -> type_of_hole_in_expr n expr
  | Texp_object (_, _) -> raise Not_found
  | Texp_pack (_) -> raise Not_found

(* type_of_hole_in_exprs : int -> expression list -> type_expr * env_t *)
and type_of_hole_in_exprs n exprs = match exprs with
    [] -> raise Not_found
  | expr :: rest ->
      begin try
        type_of_hole_in_expr n expr
      with
        Not_found -> type_of_hole_in_exprs n rest
      end

(* type_of_hole_in_cases : int -> case list -> type_expr * env_t *)
and type_of_hole_in_cases n cases = match cases with
    [] -> raise Not_found
  | {c_lhs = pat; c_guard = None; c_rhs = expr} :: rest ->
      begin try
        let (typ, env) = type_of_hole_in_expr n expr in
        (typ, add_pattern env pat)
      with
        Not_found -> type_of_hole_in_cases n rest
      end
  | {c_lhs = pat; c_guard = Some (gexpr); c_rhs = expr} :: rest ->
      begin try
        let (typ, env) = type_of_hole_in_exprs n [gexpr; expr] in
        (typ, add_pattern env pat)
      with
        Not_found -> type_of_hole_in_cases n rest
      end

(* type_of_hole_in_bindings : int -> rec_flag -> value_binding list ->
                              type_expr * env_t *)
and type_of_hole_in_bindings n rec_flag bindings = match bindings with
    [] -> raise Not_found
  | {vb_expr = expr} :: rest ->
      begin try
        let (typ, env) = type_of_hole_in_expr n expr in
        if rec_flag = Recursive
        then (typ, add_bindings env bindings)
        else (typ, env)
      with
        Not_found -> type_of_hole_in_bindings n rec_flag rest
      end

(* type_of_hole_in_structure : int -> structure_item list ->
                               type_expr * env_t *)
let rec type_of_hole_in_structure n s_items = match s_items with
    [] ->
      Format.fprintf ppf "@[Expander: hole %d is not found.@]@." n;
      exit 0
  | {str_desc = Tstr_value (rec_flag, bindings)} :: rest ->
      begin try
        type_of_hole_in_bindings n rec_flag bindings
      with
        Not_found -> type_of_hole_in_structure n rest
      end
  | {str_desc = _} :: rest -> type_of_hole_in_structure n rest

(********** main **********)

(* main : Typedtree.structure -> unit *)
let main structure =
  (* 3 番の穴の型とそこから見える変数の型を得る *)
  let (typ, env) = type_of_hole_in_structure 3 structure.str_items in
  Format.fprintf ppf "@[type of hole:@ %a@]@." (* 穴の型を表示 *)
    Printtyp.type_expr typ;
  List.iter (fun (v, typ) ->                   (* 変数の型を表示 *)
              Format.fprintf ppf "@[%s : %a@]@."
                v Printtyp.type_expr typ)
            env

(********** entry point of the expander **********)

(* expander の入り口：型の付いた入力プログラムを受け取ってくる *)
(* Expander.go : Typedtree.structure * Typedtree.module_coercion ->
                 Typedtree.structure * Typedtree.module_coercion *)
let go (structure, coercion) =
  begin match coercion with
      Typedtree.Tcoerce_none -> main structure
    | _ -> failwith "Expander: module_coercion not supported yet."
  end;
  exit 0;
  (structure, coercion) (* 返り値はこの型にしておく *)
