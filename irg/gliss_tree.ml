(*
 * gliss-tree utility -- display hierarchy of ops as a tree
 * Copyright (c) 2019, IRIT - UPS <casse@irit.fr>
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

open Printf
open Irg

(* argument list *)
let nmp = ref ""
let out_path = ref ""
let ops = ref []
let options =
	("-o", Arg.String (fun s -> ops := s :: !ops), "display the given operation") ::
	IrgUtil.options

(** Display the given error and stops the application.
	@param m	Message to display. *)
let fatal m =
	fprintf stderr "ERROR: %s\n" m;
	exit 1


(** Display an edge between the two symbols.
	@param out	Output stream.
	@param src	Source instruction.
	@param snk	Sink instruction. *)
let display_edge out src snk =
	fprintf out "%s -> %s;\n" src snk


(** Generate the graph from this name.
	@param out		Out stream.
	@param name		Symbol name to generate graph for. *)
let rec dump out name =

	let rec look_first ps =
		match ps with 
		| [] -> ()
		| (_, TYPE_EXPR _)::ps -> look_first ps
		| (_, TYPE_ID i)::ps ->
			match get_symbol i with
			| AND_OP _
			| OR_OP _ -> display_edge out name i; dump out i
			| _ -> look_first ps in

	fprintf out "%s;\n" name;
	match get_symbol name with
	| OR_OP (_, ops, _) ->
		List.iter (display_edge out name) ops;
		List.iter (dump out) ops
	| AND_OP (_, pars, _) ->
		look_first pars
	| _ -> failwith "not OP wher it should be!"


(* argument decoding *)
let free_arg arg =
	if !nmp = "" then nmp := arg else
	if !out_path = "" then out_path := arg else
	raise (Arg.Bad "only NML file required")
let usage_msg = "SYNTAX: gliss-tree [options] NML_FILE DOT_FILE\n\tGenerate tree view of the OP hierarchy."

let arg_error msg =
		Printf.fprintf stderr "ERROR: %s\n" msg;
		Arg.usage options usage_msg;
		exit 1

let _ =
	Arg.parse options free_arg usage_msg;
	if !nmp = "" then arg_error "one NML file must be given!\n";
	IrgUtil.load_with_error_support !nmp;
	try
		if !ops = [] then
			let root = get_root () in
			if root = "" then fatal "no instruction root named 'instr' or 'multi'"
			else ops := [root];
		let out = if !out_path = "" then stdout else open_out !out_path in
		fprintf out "digraph %s {\n" (get_proc_name ());
		fprintf out "node [shape=\"rect\"];\n";
		List.iter (dump out) !ops;
		fprintf out "}\n";
		if !out_path <> "" then close_out out
	with Sys_error m ->
		Printf.fprintf stderr "ERROR: %s\n" m;
		exit 3
