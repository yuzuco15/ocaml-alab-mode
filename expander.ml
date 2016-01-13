open Asttypes
open Typedtree
open Types
open Path
open Printtypes

(* output channel *)
let ppf = Format.formatter_of_out_channel stdout

(* select_mode *)
type select_mode = Refine | RefineArg | Match | If | ShowGoal

(********** add types of variables to env **********)

(* 環境の型。Env.t とは別物なのに注意 *)
(* type env_t = string * type_expr *)

(* add_pattern : env_t -> Typedtree.pattern -> env_t *)
(* add all the pattern variables and their types to env *)
let rec add_pattern env pat =
  Format.fprintf ppf "add_pattern@.";
  match pat.pat_desc with
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
let rec type_of_hole_in_expr n expr =
  (print_expression expr;
   print_expression_desc expr.exp_desc);
  match expr.exp_desc with
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
let rec type_of_hole_in_structure n s_items =
  begin match s_items with
      [] -> Format.fprintf ppf "@[Error (Expander): hole %d is not found.@]@." n;
      exit 0
    | {str_desc = Tstr_value (rec_flag, bindings)} :: rest ->
      begin try
          type_of_hole_in_bindings n rec_flag bindings
        with
          Not_found -> type_of_hole_in_structure n rest
      end
    | {str_desc = _} :: rest -> type_of_hole_in_structure n rest
  end

(********** main **********)

(* main : Typedtree.structure -> int -> (type_expr * env_t) *)
(* 本当は unit を返していた *)
(* type_expr is in Types.ml *)
let main structure n =
  (* n 番の穴の型とそこから見える変数の型を得る *)
  let (typ, env) = type_of_hole_in_structure n structure.str_items in
  (*
  Format.fprintf ppf "@[type of hole:@ %a@]@." (* 穴の型を表示 *)
    Printtyp.type_expr typ;
  List.iter (fun (v, typ) ->                   (* 変数の型を表示 *)
              Format.fprintf ppf "@[%s : %a@]@."
                v Printtyp.type_expr typ)
            env;
   *)
  (typ, env)

(********** entry point of the expander **********)
(* type t_kind: Record or Variant *)
type type_kind_core = Core_type of core_type_desc | Str of string

type type_kind = Record of (string * type_kind list) list | Variant of (string * type_kind list) list
               | Tuple of type_kind list | Core of type_kind_core

(* zip_field: Typedtree.label_declaration -> type_kind *)
(* type_kind: Record of (string * (Core (Core_type of core_type_desc)) list) *)
let zip_field (ld: Typedtree.label_declaration) = match ld with
    {ld_id = id; ld_type = typ} -> (id.name, [Core (Core_type (typ.ctyp_desc))])
  | _ -> failwith "zip_field: this is not label_decration"
				   
(* zip_fields: Typedtree.label_declaration list -> type_kind list *)
(* type_kind: Record of (string * type_kind) list *)
let zip_fields lst = List.map zip_field lst

(* zip_constructor: Typedtree.constructor_declaration -> type_kind *)
(* type_kind: Variant of (string * (Core (Core_type of core_type_desc)) list) list *)
(* return: (name of constructor, [core_type of arguments]) *)
let zip_constructor (cd: Typedtree.constructor_declaration) = match cd with
    {cd_id = id; cd_args = args} -> let ctype_descs = List.map (fun ct -> Core (Core_type (ct.ctyp_desc))) args in
    (id.name, ctype_descs)

(* zip_constructors: Typedtree.constructor_declaration list -> type_kind list *)
(* type_kind: Variant of (string * type_kind list) list *)
let zip_constructors (lst: Typedtree.constructor_declaration list) = List.map zip_constructor lst

(* type_core_to_type_expr: Typedtree.core_type option -> Typedtree.structure_item list -> type_kind list *)
let rec type_core_to_type_expr op_core_type structure_items = match op_core_type with
    None -> Format.fprintf ppf "Error@."; []
  | Some (ct) -> (* Format.fprintf ppf "type_expr in op_core_type: %a@." Printtyp.type_expr ct.ctyp_type; *)
    make_type_kinds ct.ctyp_type structure_items

(* find_constructor: string -> Typedtree.type_declaration list -> Typedtree.structure_item list -> type_kind list *)
and find_constructor name lst structure_items =
  match lst with
    [] -> []
  | (declaration :: rest) ->
    begin match declaration with
	{typ_id = id; typ_kind = kind; typ_manifest = manifest} ->
        if id.name = name then
	  begin match kind with
	      Ttype_record (label_declaration_list) ->
              Record (zip_fields label_declaration_list) :: find_constructor name rest structure_items
	    | Ttype_variant (constructor_declaration_list) ->
              Variant (zip_constructors constructor_declaration_list) :: find_constructor name rest structure_items
            (* Ttype_abstract のときは typ_manifest の中を見にいく *)
            | Ttype_abstract ->
              (type_core_to_type_expr manifest structure_items) @ (find_constructor name rest structure_items)
            | Ttype_open -> find_constructor name rest structure_items
          end
        else find_constructor name rest structure_items
      | _ -> (* Format.fprintf ppf "this is not Types.type_declaration@."; *)
	[]
    end

(* find_constructors: Path.t -> Typedtree.structure_item list -> structure_items list -> type_kind list *)
(* path (ユーザ定義の variant の名前) の型情報を structure から探す *)
and find_constructors path structure_items all_str_items =
  let name = get_path_name path in
  if name = "list" then [Variant ([("[]", []); ("(var0 :: var1)", [])])]
  else if name = "option" then [Variant([("None", []); ("Some", [Core (Core_type (Ttyp_any))])])]
  else
      begin match structure_items with
          [] -> (* Format.fprintf ppf "structure_items is mt@."; *) []
        | item :: rest ->
          begin match item.str_desc with
              Tstr_type (type_declarations) -> (* Format.fprintf ppf "Tstr_type@."; *)
              (find_constructor name type_declarations all_str_items) @ (find_constructors path rest all_str_items)
            | _ -> find_constructors path rest all_str_items
          end
      end

(* make_kinds_of_tuple: type_expr list -> type_kind list *)
(* type_kind: Tuple of (Core of (Str of str)) *)
and make_kinds_of_tuple el =
  let rec f e = match e.desc with
      Tconstr (path, _, _) -> Core (Str (get_path_name path))
    | Ttuple (elist) -> Tuple (make_kinds_of_tuple elist)
    | Tlink (e1) -> f e1
    | _ -> Format.fprintf ppf "Error: This is not a tuple@.";
      match_types_expr e;
      raise Not_found in
  [Tuple (List.map f el)]

(* make_type_kinds: Types.type_expr -> Typedtree.structure_item list -> type_kind list *)
and make_type_kinds typ structure_items =
  match typ.desc with
  (* e.g. type tree = Empty | Node of tree * int * tree は Tconstr (tree, _, _) *)
  (* e.g. 'a list: Tconstr (list, _, _), 'a option: Tconstr (option, _, _) *)
  | Tconstr (path, _, _) ->  (* Format.fprintf ppf "Tconstr path: %a@." Printtyp.path path; *)
    find_constructors path structure_items structure_items (* constructors: type_kind list *)
  (* print_type_kinds exp constructors *)
  (* e.g. type t = {a = int, b = int} は Tlink (t) *)
  | Tlink (t) ->
    (* Format.fprintf ppf "Tlink: %a@." Printtyp.type_expr typ; *)
    make_type_kinds t structure_items
  (* tuple: Ttuple [Tconstr int; Tconstr int; ...] *)
  | Ttuple (el) -> (* Format.fprintf ppf "Ttuple@."; *)
    make_kinds_of_tuple el
  | _ -> Format.fprintf ppf "Error: Not Tconstr or Tlink@."; match_types_expr typ; []

(* find_type_of_var: string -> env_t -> Types.type_expr *)
(* type env_t = string * type_expr *)
and find_type_of_var x env = match env with
    [] -> Format.fprintf ppf "mt@.";
    let str = Printf.sprintf "variable %s is not found in this scope@." x in
    failwith str
  | ((v, typ) :: r) -> (* Format.fprintf ppf "not mt, %s: %a@." v Printtyp.type_expr typ; *)
		       if v = x
		       then typ (* e.g. returns "int list" when matching List *)
	 else find_type_of_var x r

(* print_type_kind: type_kind -> unit *)
and print_type_kind kind =
  begin match kind with
    | Tuple (lst) -> (* Tuple of (Core of (Str of str)) *)
      let s = "(" in
      let rec loop l str n = match l with
          [f] -> str ^ "var" ^ (string_of_int n) ^ ") -> (exit(*{}*)0)"
        | (_ :: rest) -> loop rest (str ^ "var" ^ (string_of_int n) ^ ", ") (n + 1) in
      let str = loop lst s 0 in
      Format.fprintf ppf "%s@?" str
    | Record (lst) ->
      let s = "{" in
      (* Format.fprintf ppf "{@."; *)
      let rec loop l str = match l with
	  [] -> str ^ "} -> (exit(*{}*)0)"
	| [(name, _)] -> loop [] (str ^ name ^ " = " ^ name)
	| ((name, _) :: r) -> loop r (str ^ name ^ " = " ^ name ^ ", ")
      in
      let str = loop lst s in
      Format.fprintf ppf "%s@?" str;
    | Variant (lst) ->
      List.iter (fun (name, ts) ->
	  let length = List.length ts in
	  if length = 0 then (* e.g. Empty -> hole *)
	    begin
	      Format.fprintf ppf "| %s -> (exit(*{}*)0)@." name
	    end
	  else
	    let s = "| " ^ name ^ " (" in
	    let rec loop lst n str = match lst with
		[] -> str
	      | [t] ->
		begin
		  str ^ ("var" ^ string_of_int n) ^ ") -> (exit(*{}*)0)"
		end
	      | (t :: r) ->
		loop r (n + 1) (str ^ "var" ^ (string_of_int n) ^ ", ") in
	    let str = loop ts 0 s in
	    Format.fprintf ppf "%s@?" str)
	lst
  end

(* print_type_kinds: string -> type_kind list -> unit *)
and print_type_kinds var kinds =
  Format.fprintf ppf "match %s with@." var;
  List.iter print_type_kind kinds

(* match_variable: int -> string -> string -> env_t -> Typedtree.structure -> unit *)
(* 変数 x の型を env から取ってくる -> その型を structure から探して出力 *)
(* x は常に "a", print するのは match exp with *)
let print_match_expr n x exp env structure =
  let type_of_x = find_type_of_var x env in (* ユーザ定義の型かどうか調べる, List も "int list" とかが返ってくる *)
  let type_kinds = make_type_kinds type_of_x structure.str_items in
  print_type_kinds exp type_kinds

(* print_refine_record: type_kind list -> unit *)
let print_refine_record kinds =
  let rec loop k =
    match k with
      Record (lst) -> (* lst: (string * type_kind) list *)
      let s = "{" in
      let rec loop2 l str = match l with
	  [] -> str ^ "}"
	| [(name, _)] -> loop2 [] (str ^ name ^ " = " ^ "(exit(*{}*)0)")
	| ((name, _) :: r) -> loop2 r (str ^ name ^ " = " ^ "(exit(*{}*)0)" ^ "; ")
      in
      let str = loop2 lst s in
      Format.fprintf ppf "%s@?" str;
    | _ -> Format.fprintf ppf "Error: Cannot Refine@."
  in
  List.iter loop kinds

(* refine_record: Path.t -> type_expr list structure *)
let refine_record path el structure =
  let fields = find_constructors path structure.str_items structure.str_items in
  print_refine_record fields

(* refine_goal: int -> type_expr -> Typedtree.structure -> unit *)
let rec refine_goal n expr structure =
  begin match expr.desc with
    | Ttuple (lst) ->
      let rec loop l str =
	match l with
	  [] -> str
	| f :: [] ->
	  str ^ "(exit(*{}*)0))"
	| f :: r ->
	  loop r (str ^ "(exit(*{}*)0), ") in
      let str = loop lst "(" in
      (* Format.fprintf ppf "tuple@." *)
      Format.fprintf ppf "%s@?" str
    | Tlink ({desc = Tlink (e)}) -> (* tuple の入れ子 *)
      refine_goal n e structure
    | Tlink (e) -> refine_goal n e structure
    | Tconstr (name, el, _) -> (* record, `name` is its name *)
      refine_record name el structure
    | _ -> Format.fprintf ppf "Error: Not_supported@.";
      match_types_expr expr
  end

(* show_goal: type_expr -> env_t -> unit *)
let show_goal typ env =
  Format.fprintf ppf "@[type of hole:@ %a@]@." (* 穴の型を表示 *)
    Printtyp.type_expr typ;
  List.iter (fun (v, typ) ->                   (* 変数の型を表示 *)
      Format.fprintf ppf "@[%s : %a@]@."
        v Printtyp.type_expr typ)
    env

(* get_matched_variable: int -> string *)
(* n 番目の hole でユーザがどの変数で match したいと入力してるかを取得 *)
let get_matched_variable n =
  (* Format.fprintf ppf "%s@." Sys.argv.(6); *)
  Sys.argv.(6)

(* get_mode: unit -> select_mode *)
let get_mode () = match Sys.argv.(5) with
    "Refine" -> Refine
  | "RefineArg" -> RefineArg
  | "Match" -> Match
  | "If" -> If
  | "ShowGoal" -> ShowGoal
  | _ -> failwith "Error: select_mode is neither Refine or Match"

(* get_type:  Typedtree.structure * Typedtree.module_coercion ->
                 int -> type_expr * env_t *)
let get_type (structure, coercion) n =
  let ppf = Format.formatter_of_out_channel stdout in 
  (*  Format.fprintf ppf "%a@." Printtyped.implementation structure;*)
  begin
    match coercion with
      Typedtree.Tcoerce_none -> (* main structure *)
      let (typ, env) = main structure n in (* typ: goal の型, env: スコープ内の変数の型 *)
      (typ, env)
    | _ -> failwith "Expander: module_coercion not supported yet."
  end

(* expander の入り口：型の付いた入力プログラムを受け取ってくる *)
(* Expander.go : Typedtree.structure * Typedtree.module_coercion ->
                 Typedtree.structure * Typedtree.module_coercion *)
(* ./expander filename n mode Some(var) *)
(*
let go (structure, coercion) =
  let n = int_of_string Sys.argv.(4) in
  let mode = get_mode () in
  begin
    match mode with
      Refine -> let (typ, env) = get_type (structure, coercion) n in
      refine_goal n typ structure
    | RefineArg -> () (* only pass the source program to the compiler *)
    | Match -> let (typ, env) = get_type (structure, coercion) n in
      let var = get_matched_variable n in
      print_match_expr n "a" var env structure
    | If -> Format.fprintf ppf "if (exit(*{}*)0) then (exit(*{}*)0) else (exit(*{}*)0)@?"
    | ShowGoal -> let (typ, env) = get_type (structure, coercion) n in
      show_goal typ env
  end;
  exit 0;
  (structure, coercion) (* 返り値はこの型にしておく *)
*)

(***** テスト用の pretty printer *****)

let rec pprint_expr expr =
  print_expression expr;
  print_expression_extra expr;
  print_expression_desc expr.exp_desc

let rec pprint_exprs exprs = match exprs with
    [] -> Format.fprintf ppf "Finished pprint_exprs@."
  | expr :: rest ->
    pprint_expr expr;
    pprint_exprs rest

let rec pprint_bindings bindings = match bindings with
    [] -> Format.fprintf ppf "Finished pprint_bindings@."
  | {vb_expr = expr} :: rest ->
    pprint_expr expr;
    pprint_bindings rest

let rec pprint_structure s_items =
  begin match s_items with
      [] -> Format.fprintf ppf "Finished pprint_structure@."
    | {str_desc = Tstr_value (rec_flag, bindings)} :: rest ->
      pprint_bindings bindings;
      pprint_structure rest
    | {str_desc = _} :: rest -> pprint_structure rest
  end

let pprint_pattern (structure, coercion) =
  begin
    match coercion with
      Typedtree.Tcoerce_none -> (* main structure *)
      pprint_structure structure.str_items
    | _ -> failwith "Expander: module_coercion not supported yet."
  end

let rec type_of_patterns funname pats =
  match pats with
    [] -> raise Not_found
  | (p :: rest) ->
    try
      type_of_pattern funname p
    with
      Not_found -> type_of_patterns funname rest

and type_of_pattern funname pat =
  match pat.pat_desc with
    Tpat_any -> raise Not_found
  | Tpat_var (fname, _) -> (* function name *)
    if fname.name = funname then pat.pat_type
    else raise Not_found
  | Tpat_alias (p, i, _) ->
    if i.name = funname then p.pat_type (* pat.pat_type ? *)
    else type_of_pattern funname p
  | Tpat_constant (c) -> raise Not_found
  | Tpat_tuple (pats) -> type_of_patterns funname pats
  | Tpat_construct (_, description, pats) -> type_of_patterns funname pats (* need to using description? *)
  | Tpat_variant (_, pop, _) ->
    begin
      match pop with
        None -> raise Not_found
      | Some (p) -> type_of_pattern funname p
    end
  | Tpat_record (l, _) ->
    begin
      match l with
        [] -> raise Not_found
      | (_, description, p) :: rest -> type_of_pattern funname p (* need to using description? *)
    end
  | Tpat_array (pats) -> type_of_patterns funname pats
  | Tpat_or (p1, p2, _) ->
    begin
      try
        type_of_pattern funname p1
      with
        Not_found -> type_of_pattern funname p2
    end
  | Tpat_lazy (p) -> type_of_pattern funname p

(* find_pattern_in_bindings: string -> value_binding list -> type_expr *)
and find_pattern_in_bindings funname bindings = match bindings with
    [] -> raise Not_found
  | {vb_pat = pat} :: rest ->
    begin try
        let typ = type_of_pattern funname pat in
        typ
      (* if rec_flag = Recursive *)
      (* then (typ, add_bindings env bindings) *)
      (* else (typ, env) *)
      with
        Not_found -> find_pattern_in_bindings funname rest
    end

      (* find_bindings_in_structure: string -> structure_item list -> type_expr *)
and find_bindings_in_structure funname s_items =
  begin match s_items with
      [] -> Format.fprintf ppf "@[Error (Expander): type of function %s is not found.@]@." funname;
      exit 0
    | {str_desc = Tstr_value (rec_flag, bindings)} :: rest ->
      begin try
          find_pattern_in_bindings funname bindings
        with
          Not_found -> find_bindings_in_structure funname rest
      end
    | {str_desc = _} :: rest -> find_bindings_in_structure funname rest
  end
    
(* type_of_function: string -> (structure, coercion) -> Types.type_expr *)
let type_of_function funname (structure, coercion) =
  begin
    match coercion with
      Typedtree.Tcoerce_none -> (* main structure *)
      find_bindings_in_structure funname structure.str_items
    | _ -> failwith "Expander: module_coercion not supported yet."
  end

let go (structure, coercion) =
  (* Printtyped.implementation ppf structure; *)
  (* pprint_pattern (structure, coercion); *)
  let funname = Sys.argv.(2) in
  let typ = type_of_function funname (structure, coercion) in
  Format.fprintf ppf "type of function %s: %a@."
    funname Printtyp.type_expr typ;
  exit 0;
  (structure, coercion)
