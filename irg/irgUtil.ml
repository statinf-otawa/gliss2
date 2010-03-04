(*
 * $Id$
 * Copyright (c) 2010, IRIT - UPS <casse@irit.fr>
 *
 * This file is part of GLISS2.
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

(** Load an NML description either NMP, NML or IRG.
	@param 	path		Path of the file to read from.
	@raise	Sys_error	If there is an error during the read. *)
let load path =

	(* is it an IRG file ? *)
	if Filename.check_suffix path ".irg" then
		Irg.load path

	(* is it NML ? *)
	else if Filename.check_suffix path ".nml" then
		begin
			Lexer.file := path;
			let lexbuf = Lexing.from_channel (open_in path) in
			Parser.top Lexer.main lexbuf;
		end

	(* is it NMP ? *)
	else if Filename.check_suffix path ".nmp" then
		let input = run_nmp2nml path in
		begin
			Lexer.file := path;
			let lexbuf = Lexing.from_channel input in
			Parser.top Lexer.main lexbuf;
			match Unix.close_process_in input with
			| Unix.WEXITED n when n = 0 -> ()
			| _ -> raise (Sys_error "ERROR: preprocessing failed.")
		end

	(* else error *)
	else
		raise (Sys_error (Printf.sprintf "ERROR: unknown file type: %s\n" path))