(* pretty printing for Expander.ml *)

open Asttypes
open Typedtree
open Types
open Path
open Longident

(* output channel *)
let ppf = Format.formatter_of_out_channel stdout

(* get_path_name: Path.t -> string *)
let get_path_name path = match path with
    Pident (ident) -> ident.name
  | _ -> failwith "Error: path is not Pident@."

(*get_longident_name: Longident.t -> string *)
let rec get_longident_name id = match id with
    Lident (s) -> s
  | Ldot (_, s) -> s
  | Lapply (t1, t2) -> get_longident_name t1 ^ " " ^ get_longident_name t2

(***** Asttypes *****)
(* Asttypes.constant -> string *)
let constant2string c = match c with
    Const_int (i) -> string_of_int i
  | Const_char (c) -> Char.escaped c
  | Const_string (s, sop) -> s
  | Const_float (s) -> s
  | Const_int32 (i32) -> Int32.to_string i32
  | Const_int64 (i64) -> Int64.to_string i64
  | Const_nativeint (n) -> Nativeint.to_string n
                         
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
let rec print_expression_desc ed = match ed with
    Texp_ident (path, _, _) -> Format.fprintf ppf "Texp_ident: path %a@." Printtyp.path path
  | Texp_constant (c) -> Format.fprintf ppf "Texp_constant: constant %s@." (constant2string c)
  | Texp_let (_, binds, e) ->
    (Format.fprintf ppf "Texp_let: @?";
     print_value_binding_list binds;
     print_expression e)
  | Texp_function (lbl, cases, _) ->
      begin
        Format.fprintf ppf "Texp_function label: %s, cases:@?" lbl;
        List.iter (fun c ->
            print_pattern c.c_lhs;
            print_expression c.c_rhs
          ) cases
      end
  | Texp_apply (e, lst) ->
    begin
      Format.fprintf ppf "Texp_apply expression: %a, list:@.";
      print_expression e;
      List.iter (fun (lbl, eop, _) ->
          Format.fprintf ppf "label: %s@." lbl;
          begin
            match eop with
              None -> ()
            | Some (e) -> print_expression e
          end
        ) lst
    end
  | _ -> Format.fprintf ppf "Typedtree.expression is not Texp_ident@."
  (* | Texp_match of expression * case list * case list * partial *)
  (* | Texp_try of expression * case list *)
  (* | Texp_tuple of expression list *)
  (* | Texp_construct of *)
  (*     Longident.t loc * constructor_description * expression list *)
  (* | Texp_variant of label * expression option *)
  (* | Texp_record of *)
  (*     (Longident.t loc * label_description * expression) list * *)
  (*       expression option *)
  (* | Texp_field of expression * Longident.t loc * label_description *)
  (* | Texp_setfield of *)
  (*     expression * Longident.t loc * label_description * expression *)
  (* | Texp_array of expression list *)
  (* | Texp_ifthenelse of expression * expression * expression option *)
  (* | Texp_sequence of expression * expression *)
  (* | Texp_while of expression * expression *)
  (* | Texp_for of *)
  (*     Ident.t * Parsetree.pattern * expression * expression * direction_flag * *)
  (*       expression *)
  (* | Texp_send of expression * meth * expression option *)
  (* | Texp_new of Path.t * Longident.t loc * Types.class_declaration *)
  (* | Texp_instvar of Path.t * Path.t * string loc *)
  (* | Texp_setinstvar of Path.t * Path.t * string loc * expression *)
  (* | Texp_override of Path.t * (Path.t * string loc * expression) list *)
  (* | Texp_letmodule of Ident.t * string loc * module_expr * expression *)
  (* | Texp_assert of expression *)
  (* | Texp_lazy of expression *)
  (* | Texp_object of class_structure * string list *)
  (* | Texp_pack of module_expr *)
  
(* print_expression: Typedtree.expression -> unit *)
and print_expression e = match e with
    {exp_type = exp_type; exp_desc = exp_desc} ->
    (Format.fprintf ppf "exp_type: %a@." Printtyp.type_expr exp_type;
     print_expression_desc exp_desc)
    
(* print_value_biding_list: Typedtree.value_biding list -> unit *)
and print_value_binding_list vl =
  List.iter (fun {vb_expr = vb_expr; vb_pat = vb_pat} ->
      begin
        print_expression vb_expr;
        print_pattern vb_pat
      end) vl

(* print_pattern: pattern -> unit *)
and print_pattern pat = match pat.pat_desc with
    Tpat_any -> Format.fprintf ppf "Tpat_any = wild_card@."
  | Tpat_var (i, _) -> Format.fprintf ppf "Tpat_var: %s@." i.name
  | Tpat_alias (pat, i, _) ->
    begin
      Format.fprintf ppf "Tpat_alias pattern:@?";
      print_pattern pat;
      Format.fprintf ppf "Tpat_alias ident: %s@." i.name
    end
  | Tpat_constant (c) -> Format.fprintf ppf "Tpat_constant %s@." (constant2string c)
  | Tpat_tuple (pats) ->
    begin
      Format.fprintf ppf "Tpat_tuple@?";
      List.iter (fun p ->
          print_pattern p
        ) pats
    end
  | Tpat_construct (_, _, pats) ->
    begin
      Format.fprintf ppf "Tpat_tuple@?";
      List.iter (fun p ->
          print_pattern p
        ) pats
    end
  | Tpat_variant (_, patop, _) ->
    begin
      Format.fprintf ppf "Tpat_variant@?";
        begin
          match patop with
            None -> ()
          | Some (pat) ->
            begin
              Format.fprintf ppf "Some:@?";
              print_pattern pat
            end
        end
    end
  | Tpat_record (l, _) ->
    begin
      Format.fprintf ppf "Tpat_record@?";
      List.iter (fun (_, _, pat) -> print_pattern pat) l
    end
  | Tpat_array (pats) ->
    (Format.fprintf ppf "Tpat_array@?";
     List.iter (fun p ->
         print_pattern p
       ) pats)
  | Tpat_or (pat1, pat2, _) ->
    (Format.fprintf ppf "Tpat_or@?";
     print_pattern pat1;
     print_pattern pat2)
  | Tpat_lazy (p) -> print_pattern p
  
(* print_structure_item: Typedtree.strucre_item -> unit *)
let print_structure_item item = match item.str_desc with
    Tstr_eval (_, _) -> Format.fprintf ppf "Tstr_eval@."
  | Tstr_value (_, vl) -> (Format.fprintf ppf "Tstr_value@."; print_value_binding_list vl)
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

(* print_core_type_desc: Typedtree.core_type -> unit *)
let rec print_core_type_desc ct = match ct.ctyp_desc with
   Ttyp_any -> Format.fprintf ppf "core_type: Ttyp_any@."
  | Ttyp_var (s) -> Format.fprintf ppf "core_type: Ttyp_var, %s@." s
  | Ttyp_arrow (_, c1, c2) -> begin
      Format.fprintf ppf "core_type: Ttyp_arrow, c1: @?";
      print_core_type_desc c1;
      Format.fprintf ppf "c2: @?";
      print_core_type_desc c2
    end
  | Ttyp_tuple (ctl) -> begin
      Format.fprintf ppf "core_type: Ttyp_tuple, elements: @?";
      List.iter print_core_type_desc ctl
    end
  | Ttyp_constr (path, _, ctl) -> begin
      Format.fprintf ppf "core_type: Ttyp_constr, path: %s@?"
        (get_path_name path);
      List.iter print_core_type_desc ctl
    end
  | Ttyp_object (lst, _) -> begin
      Format.fprintf ppf "core_type: Ttyp_object@?";
      let f l = match l with
          (s, _, ct) -> Format.fprintf ppf "%s@?" s; print_core_type_desc ct
      in
      List.iter f lst
    end
  | Ttyp_class (path, id, ctl) -> begin
      Format.fprintf ppf "core_type: Ttyp_class, path: %s@?"
        (get_path_name path);
      List.iter print_core_type_desc ctl
    end
  | Ttyp_alias (ct, s) -> Format.fprintf ppf "core_type: Ttyp_alias %s@?" s;
    print_core_type_desc ct
  | Ttyp_variant (_, _, _) -> Format.fprintf ppf "core_type: Ttyp_variant@."
  | Ttyp_poly (sl, ct) -> begin
      Format.fprintf ppf "core_type: Ttyp_poly@?";
      List.iter (fun s -> Format.fprintf ppf "%s @?" s) sl;
      print_core_type_desc ct
    end
  | Ttyp_package (_) -> Format.fprintf ppf "core_type: Ttyp_package@."

(* print_expression_extra: Typedtree.expression_extra -> unit *)
let rec print_expression_extra extras = match extras.exp_extra with
    [] -> ()
  | (ex,_, _) :: rest ->
    begin
      match ex with
      | Texp_constraint (ct) ->
        Format.fprintf ppf "Texp_constraint@?";
        print_core_type_desc ct
      | Texp_coerce (cop, ct) ->
        Format.fprintf ppf "Texp_coerce@?";
        print_core_type_desc ct;
        begin
          match cop with
            None -> ()
          | Some (ct2) -> print_core_type_desc ct2
        end
      | Texp_open (_, path, _, _) -> Format.fprintf ppf "Texp_open path: %s@." (get_path_name path)
      | Texp_poly (cop) ->
        Format.fprintf ppf "Texp_poly@?";
        begin
          match cop with
            None -> ()
          | Some (ct) -> print_core_type_desc ct
        end
      | Texp_newtype (s) ->
        Format.fprintf ppf "Texp_newtype string: %s@." s;
    end

