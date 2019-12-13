(*
 * $Id: mkirg.ml,v 1.1 2009/04/24 16:28:30 casse Exp $
 * Copyright (c) 2009, IRIT - UPS <casse@irit.fr>
 *
 * This file is part of OGliss.
 *
 * GLISS2 is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * GLISS2 is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with GLISS2; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *)

open Irg
open Printf

(* argument list *)
let nmp = ref ""
let out = ref ""
let insts = ref false
let orphans = ref false
let options =
	("--orphan", Arg.Set orphans, "Display list of orphan instructions") ::
	IrgUtil.options


(** Symbols used by GLISS and that are not considered as orphans. *)
let gliss_roots = [
	"bit_image_order";
	"bit_order";
	"exceptions";
	"gliss_debug_only";
	"gliss_isize";
	"init";
	"proc"
]


(** List orphan instructions. *)
let lookup_orphans _ =

	let is_op_mode s =
		match s with
		| AND_OP _
		| OR_OP _
		| AND_MODE _
		| OR_MODE _ -> true
		| _ -> false in

	let rec remove set id =
		if not (StringSet.mem id set) then set else
		let set = StringSet.remove id set in
		match get_symbol id with
		| OR_OP (_, syms, _)
		| OR_MODE (_, syms, _) ->
			List.fold_left remove set syms
		| AND_OP (_, pars, _)
		| AND_MODE (_, pars, _, _) ->
			List.fold_left remove_par set pars
		| _ -> set
	and remove_par set (_, t) =
		match t with
		| TYPE_EXPR _ -> set
		| TYPE_ID i -> remove set i in

	let all = fold
		(fun id spec set -> if is_op_mode spec then StringSet.add id set else set)
		StringSet.empty in
	
	let rem = List.fold_left (fun set id -> remove set id) all ((get_root ()) :: gliss_roots) in
	
	if rem <> StringSet.empty then begin
		fprintf stderr "WARNING: following modes and ops are orphans:\n";
		StringSet.iter (fun id -> fprintf stderr "  * %s\n" id) rem
	end


(* argument decoding *)
let free_arg arg =
	if !nmp = "" then nmp := arg else
	if !out = "" then out := arg else
	raise (Arg.Bad "only NML and out files required")
let usage_msg = "SYNTAX: mkirg [options] NML_FILE IRG_FILE\n\tGenerate IRG file from NML or NMP source."

let arg_error msg =
		Printf.fprintf stderr "ERROR: %s\n" msg;
		Arg.usage options usage_msg;
		exit 1

let _ =
	Arg.parse options free_arg usage_msg;
	if !nmp = "" then arg_error "one NML file must be given !\n";
	if !out = "" then arg_error "one IRG file must be given !\n"

let _ =
	IrgUtil.load_with_error_support !nmp;
	if !orphans then lookup_orphans ();
	try
		Irg.save !out
	with Sys_error m ->
		Printf.fprintf stderr "ERROR: %s\n" m;
		exit 3
