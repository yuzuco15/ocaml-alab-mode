(* pretty printing for Expander.ml *)

open Asttypes
open Typedtree
open Types
open Path

(* output channel *)
let ppf = Format.formatter_of_out_channel stdout

(***** Types *****)
(* match_types_expr: Types.type_expr -> unit *)
let rec match_types_expr expr = match expr.desc with
    Tvar (Some(s)) -> Format.fprintf ppf "Tvar %s@." s
  | Tvar (_) -> Format.fprintf ppf "Tvar None@."
  | Tarrow (lbl, e1, e2, _) -> Format.fprintf ppf "Tarrow: %s@." lbl;
			       match_types_expr e1;
			       match_types_expr e2
  | Ttuple (el) -> Format.fprintf ppf "Ttuple@.";
		   List.iter (fun e -> match_types_expr e) el
  | Tconstr (name, el, _) -> Format.fprintf ppf "Tconstr %a@." Printtyp.path name;
			     List.iter (fun e -> match_types_expr e) el
  | Tobject (e, _) -> Format.fprintf ppf "Tobject@.";
		      match_types_expr e
  | Tfield (s, _, e1, e2) -> Format.fprintf ppf "Tfield %s@." s;
			     match_types_expr e1;
			     match_types_expr e2
  | Tnil -> Format.fprintf ppf "Tnil@."
  | Tlink (e) -> Format.fprintf ppf "Tlink@.";
		 match_types_expr e
  | Tsubst (e) -> Format.fprintf ppf "Tsubst@.";
		  match_types_expr e
  | Tvariant ({row_more=row_more}) -> Format.fprintf ppf "Tvariant@.";
				      match_types_expr row_more
  | Tunivar (_) -> Format.fprintf ppf "Tunivar@."
  | Tpoly (_, _) -> Format.fprintf ppf "Tpoly@."
  | Tpackage (_, _, _) -> Format.fprintf ppf "Tpackage@."

(***** Typedtree *****)
(* print_expression_desc: Typedtree.expression_desc -> unit *)
let print_expression_desc ed = match ed with
    Texp_ident (path, _, _) -> Format.fprintf ppf "Texp_ident: path %a@." Printtyp.path path
  | _ -> Format.fprintf ppf "Typedtree.expression is not Texp_ident@."
  
(* print_expression: Typedtree.expression -> unit *)
let print_expression e = match e with
    {exp_type = exp_type} -> Format.fprintf ppf "exp_type: %a@." Printtyp.type_expr exp_type

(* print_value_biding_list: Typedtree.value_biding list -> unit *)
let print_value_biding_list vl = List.iter (fun {vb_expr = vb_expr} -> print_expression vb_expr) vl
  
(* print_structure_item: Typedtree.strucre_item -> unit *)
let print_structure_item item = match item.str_desc with
    Tstr_eval (_, _) -> Format.fprintf ppf "Tstr_eval@."
  | Tstr_value (_, vl) -> (Format.fprintf ppf "Tstr_value@."; print_value_biding_list vl)
  | Tstr_primitive (_) -> Format.fprintf ppf "Tstr_primitive@."
  | Tstr_type (_) -> Format.fprintf ppf "Tstr_type@."
  | Tstr_typext (_) -> Format.fprintf ppf "Tstr_typext@."
  | Tstr_exception (_) -> Format.fprintf ppf "Tstr_exception@."
  | Tstr_module (_) -> Format.fprintf ppf "Tstr_module@."
  | Tstr_recmodule (_) -> Format.fprintf ppf "Tstr_recmodule@."
  | Tstr_modtype (_) -> Format.fprintf ppf "Tstr_modtype@."
  | Tstr_open (_) -> Format.fprintf ppf "Tstr_open@."
  | Tstr_class (_) -> Format.fprintf ppf "Tstr_class@."
  | Tstr_class_type (_) -> Format.fprintf ppf "Tstr_class_type@."
  | Tstr_include (_) -> Format.fprintf ppf "Tstr_include@."
  | Tstr_attribute (_) -> Format.fprintf ppf "Tstr_attribute@."
