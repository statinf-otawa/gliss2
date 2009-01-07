(*
 * $Id: gep.ml,v 1.10 2009/01/07 18:44:33 casse Exp $
 * Copyright (c) 2008, IRIT - UPS <casse@irit.fr>
 *
 * This file is part of OGliss.
 *
 * OGliss is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * OGliss is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with OGliss; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *)
open Lexing

exception UnsupportedMemory of Irg.spec

(*module OrderedString = struct
	type t = string
	let compare s1 s2 = String.compare s1 s2
end
module StringSet = Set.Make(OrderedString)*)

module OrderedType = struct
	type t = Toc.c_type
	let compare s1 s2 = if s1 = s2 then 0 else if s1 < s2 then (-1) else 1
end
module TypeSet = Set.Make(OrderedType)

(* module management *)
let modules = ref [("mem", "fast_mem")]
let add_module text =
	let (new_id, new_imp) =
		try
			let idx = String.index text ':' in
			(String.sub text 0 idx,
			String.sub text (idx + 1) ((String.length text) - idx - 1))
		with Not_found ->
			(text, text) in
	let rec set lst =
		match lst with
		  (id, imp)::tl ->
			if id = new_id then (id, new_imp)::tl
			else (id, imp)::(set tl)
		| _ -> [(new_id, new_imp)] in
	modules := set !modules


(* options *)
let nmp: string ref = ref ""
let paths = [
	Config.install_dir ^ "/lib/gliss/lib";
	Config.source_dir ^ "/lib";
	Sys.getcwd ()]
let quiet = ref false
let verbose = ref false
let memory = ref "fast_mem"
let options = [
	("-v", Arg.Set verbose, "verbose mode");
	("-q", Arg.Set quiet, "quiet mode");
	("-m", Arg.String add_module, "add a module (module_name:actual_module)]")
]

let free_arg arg =
	if !nmp = ""
	then nmp := arg
	else raise (Arg.Bad "only one NML file required") 
let usage_msg = "SYNTAX: gep [options] NML_FILE\n\tGenerate code for a simulator"
let _ =
	Arg.parse options free_arg usage_msg;
	if !nmp = "" then begin
		prerr_string "ERROR: one NML file must be given !\n";
		Arg.usage options usage_msg;
		exit 1
	end


(** Build the given directory.
	@param path			Path of the directory.
	@raise Sys_error	If there is an error. *)
let makedir path =
	if not (Sys.file_exists path) then
		try 
			Unix.mkdir path 0o740
		with Unix.Unix_error (code, _, _) ->
			raise (Sys_error (Printf.sprintf "cannot create \"%s\": %s" path (Unix.error_message code)))
	else
		let stats = Unix.stat path in
		if stats.Unix.st_kind <> Unix.S_DIR
		then raise (Sys_error (Printf.sprintf "cannot create directory \"%s\": file in the middle" path))


(** Get the processor name.
	@return	Processor name.
	@raise	Sys_error	Raised if the proc is not defined. *)
let get_proc _ =
	match Irg.get_symbol "proc" with
	  Irg.LET(_, Irg.STRING_CONST name) -> name
	| _ -> raise (Sys_error "no \"proc\" definition available")


(** Format date (in seconds) and return a stirng.
	@param date	Date to format.
	@return		Date formatted as a string. *)
let format_date date =
	let tm = Unix.localtime date in
	Printf.sprintf "%0d/%02d/%02d %02d:%02d:%02d"
		tm.Unix.tm_year tm.Unix.tm_mon tm.Unix.tm_mday
		tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec


(* Test if memory or register attributes contains ALIAS.
	@param attrs	Attributes to test.
	@return			True if it contains "alias", false else. *)
let rec contains_alias attrs =
	match attrs with
	  [] -> false
	| (Irg.ALIAS _)::_ -> true
	| _::tl -> contains_alias tl


(** Build an include file.
	@param f	Function to generate the content of the file.
	@param proc	Processor name.
	@param file	file to create.
	@param dir	Directory containing the includes.
	@raise Sys_error	If the file cannot be created. *)
let make_include f info file =
	let uproc = String.uppercase info.Toc.proc in
	let path = info.Toc.ipath ^ "/" ^ file ^ ".h" in
	if not !quiet then Printf.printf "creating \"%s\"\n" path;
	info.Toc.out <- open_out path;
	
	(* output header *)
	let def = Printf.sprintf "GLISS_%s_%s_H" uproc (String.uppercase file) in
	Printf.fprintf info.Toc.out "/* Generated by gep (%s) copyright (c) 2008 IRIT - UPS */\n" (format_date (Unix.time ()));
	Printf.fprintf info.Toc.out "#ifndef %s\n" def;
	Printf.fprintf info.Toc.out "#define %s\n" def;
	
	(* output the content *)
	f info;
		
	(* output tail *)
	Printf.fprintf info.Toc.out "\n#endif /* %s */\n" def;
	close_out info.Toc.out


(** Build the src/Makefile.
	@param info		Information about the generation. *)
let make_makefile info =
	let path = info.Toc.spath ^ "/Makefile" in
	if not !quiet then Printf.printf "creating \"%s\"\n" path;
	let lib = "lib" ^ info.Toc.proc ^ ".a" in
	let out = open_out path in
	Printf.fprintf out "# Generated by gep (%s) copyright (c) 2008 IRIT - UPS\n\n" (format_date (Unix.time ()));
	
	(* dump definitions *)
	Printf.fprintf out "SOURCES = \\\n\tgliss.c";
	List.iter 
		(fun (name, _) -> Printf.fprintf out " \\\n\t%s.c" name)
		!modules;
	Printf.fprintf out "\nOBJECTS=$(SOURCES:.c=.o)\n";
	Printf.fprintf out "CLEAN = $(OBJECTS) %s\n\n" lib;
	
	(* generate rules *)
	Printf.fprintf out "all: %s\n\n" lib;
	Printf.fprintf out "%s: $(OBJECTS)\n\n" lib;
	Printf.fprintf out "clean:\n\trm -rf $(CLEAN)\n\n";
	close_out out


(** Build the file "proc/include/id.h"
	@param proc		Name of the processor. *)
let make_id_h info =
	let proc = info.Toc.proc in
	let out = info.Toc.out in
	let uproc = String.uppercase proc in
	Printf.fprintf out "\n/* %s_ident_t */\n" proc;
	Printf.fprintf out "typedef enum %s_ident_t {\n" proc;
	Printf.fprintf out "\t%s_UNKNOWN = 0" uproc;
	Iter.iter
		(fun _ i -> Printf.fprintf
			out
			",\n\t%s_%s = %d"
			uproc
			(Iter.get_name i)
			(Iter.get_id i))
		();
	Printf.fprintf out "\n} %s_ident_t;\n" proc


(** Build the XXX/include/api.h file. *)
let make_api_h info =
	let proc = info.Toc.proc in
	let out = info.Toc.out in
	let uproc = String.uppercase proc in

	let make_array size =
		if size = 1 then ""
		else Printf.sprintf "[%d]" size in

	let make_state k s =
		match s with
		  Irg.MEM (name, size, Irg.CARD(8), attrs)
		  when not (contains_alias attrs) ->
			Printf.fprintf out "\tstruct %s_memory_t *%s;\n" proc name
		| Irg.MEM _ ->
			raise (UnsupportedMemory s)
		| Irg.REG (name, size, t, attrs)
		when not (contains_alias attrs) ->
			Printf.fprintf out "\t%s %s%s;\n" (Toc.type_to_string (Toc.convert_type t)) name (make_array size)
		| _ -> () in

	let collect_field set (name, t) =
		match t with
		  Irg.TYPE_EXPR t -> TypeSet.add (Toc.convert_type t) set
		| Irg.TYPE_ID n ->
			(match (Irg.get_symbol n) with
			  Irg.TYPE (_, t) -> TypeSet.add (Toc.convert_type t) set
			| _ -> set) in
	
	let collect_fields set params =
		List.fold_left collect_field set params in
	
	let make_reg_param _ spec =
		match spec with
		  Irg.REG (name, size, t, attrs) ->
			Printf.fprintf out ",\n\t%s_%s_T" uproc (String.uppercase name)
		| _ -> () in		
	
	(* output includes *)
	Printf.fprintf out "\n#include <stdint.h>\n";
	Printf.fprintf out "#include \"id.h\"\n\n";

	(* xxx_state_t typedef generation *)
	Printf.fprintf out "\n/* %s_state_t type */\n" proc;
	Printf.fprintf out "typedef struct %s_state_t {\n" proc;
	Irg.StringHashtbl.iter make_state Irg.syms;
	Printf.fprintf out "} %s_state_t;\n" proc;

	(* output xxx_value_t *)
	Printf.fprintf out "\n/* %s_value_t type */\n" proc;
	Printf.fprintf out "typedef union %s_value_t {\n" proc;
	let set = 
		Iter.iter (fun set i -> collect_fields set (Iter.get_params i)) TypeSet.empty in
	TypeSet.iter
		(fun t -> Printf.fprintf out "\t%s %s;\n" (Toc.type_to_string t) (Toc.type_to_field t))
		set;
	Printf.fprintf out "} %s_value_t;\n" proc;
	
	(* output xxx_param_t *)
	Printf.fprintf out "\n/* %s_param_t type */\n" proc;
	Printf.fprintf out "typedef enum %s_param_t {\n" proc;
	Printf.fprintf out "\tVOID_T = 0";
	TypeSet.iter
		(fun t -> Printf.fprintf out ",\n\t%s_PARAM_%s_T"
			uproc (String.uppercase (Toc.type_to_field t)))
		set;
	Irg.StringHashtbl.iter make_reg_param Irg.syms;
	Printf.fprintf out "\n} %s_param_t;\n" proc;
	
	(* output xxx_ii_t *)
	Printf.fprintf out "\n/* %s_ii_t type */\n" proc;
	Printf.fprintf out "typedef struct %s_ii_t {\n" proc;
	Printf.fprintf out "\t%s_param_t type;\n" proc;
	Printf.fprintf out "\t%s_value_t val;\n" proc;
	Printf.fprintf out "} %s_ii_t;\n" proc;
	
	(* output xxx_inst_t *)
	Printf.fprintf out "\n/* %s_inst_t type */\n" proc;
	Printf.fprintf out "typedef struct %s_inst_t {\n" proc;
	Printf.fprintf out "\t%s_ident_t ident;\n" proc;
	Printf.fprintf out "\t%s_ii_t *instrinput;\n" proc;
	Printf.fprintf out "\t%s_ii_t *instroutput;\n" proc;
	Printf.fprintf out "} %s_inst_t;\n" proc


(** Build the XXX/include/macros.h file.
	@param out	Output channel.
	@param proc	Name of the processor. *)
let make_macros_h info =
	let out = info.Toc.out in
	
	let make_state_macro k s =
		match s with
		  Irg.MEM (name, size, Irg.CARD(8), attrs)
		  when not (contains_alias attrs) ->
			Printf.fprintf out "#define %s(s) ((s)->%s)\n" (Toc.state_macro info name) name
		| Irg.MEM _ ->
			raise (UnsupportedMemory s)
		| Irg.REG (name, size, t, attrs)
		when not (contains_alias attrs) ->
			Printf.fprintf out "#define %s(s) ((s)->%s)\n" (Toc.state_macro info name) name
		| _ -> () in

	let get_type t =
		match t with
		  Irg.TYPE_EXPR t -> t
		| Irg.TYPE_ID n ->
			(match (Irg.get_symbol n) with
			  Irg.TYPE (_, t) -> t
			| _ -> Irg.NO_TYPE) in


	let make_param_macro _ inst =
		let _ = List.fold_left
			(fun i (n, t) ->
				let t = get_type t in
				if t <> Irg.NO_TYPE then
					Printf.fprintf out "#define %s(i) ((i)->instrinput[%d].val.%s\n"
						(Toc.param_macro info inst n) i (Toc.type_to_field (Toc.convert_type t));
				i + 1)
			0
			(Iter.get_params inst) in
		() in

	(* macros for accessing registers *)
	Printf.fprintf out "\n/* state access macros */\n";
	Irg.StringHashtbl.iter make_state_macro Irg.syms;
	
	(* macros for accessing parameters *)
	Printf.fprintf out "\n/* parameter access macros */\n";
	Iter.iter make_param_macro ()


(** Perform a symbolic link.
	@param src	Source file to link.
	@param dst	Destination to link to. *)
let link src dst =
	if Sys.file_exists dst then Sys.remove dst;
	Unix.symlink src dst


(* regular expressions *)
let lower_re = Str.regexp "gliss_"
let upper_re = Str.regexp "GLISS_"

(** Replace the "gliss" and "GLISS" words in the input file
	to create the output file.
	@param info		Generation information.
	@param in_file	Input file.
	@param out_file	Output file. *)
let replace_gliss info in_file out_file =
	let in_stream = open_in in_file in
	let out_stream = open_out out_file in
	let lower = info.Toc.proc ^ "_" in 
	let upper = String.uppercase lower in
	let rec trans _ =
		let line = input_line in_stream in
		output_string out_stream
			(Str.global_replace upper_re upper (Str.global_replace lower_re lower line));
		output_char out_stream '\n';
		trans () in
	try
		trans ()
	with End_of_file ->
		close_in in_stream;
		close_out out_stream


(** Link a module for building.
	@param info	Generation information.
	@param m	Original module name.
	@param name	Final name of the module. *)
let process_module info m name =

	(* find the module *)
	let rec find paths =
		if paths = [] then raise (Sys_error ("cannot find module " ^ m)) else
		let path = (List.hd paths) ^ "/" ^ m in
		if Sys.file_exists (path ^ ".c") then path
		else find (List.tl paths) in
	let path = find paths in
	
	(* link it *)
	let source = info.Toc.spath ^ "/" ^ name ^ ".c" in
	let header = info.Toc.spath ^ "/" ^ name ^ ".h" in
	if not !quiet then Printf.printf "creating \"%s\"\n" source;
	replace_gliss info (path ^ ".c") source;
	if not !quiet then Printf.printf "creating \"%s\"\n" header;
	replace_gliss info (path ^ ".h") header


(* main program *)
let _ =
	try	
		begin
		
			(* parsing NMP *)
			let lexbuf = Lexing.from_channel (open_in !nmp) in
			Parser.top Lexer.main lexbuf;
			let info = Toc.info () in
			
			(* include generation *)
			if not !quiet then Printf.printf "creating \"include/\"\n";
			makedir "include";
			if not !quiet then Printf.printf "creating \"%s\"\n" info.Toc.ipath;
			makedir info.Toc.ipath;
			make_include make_id_h info "id";
			make_include make_api_h info "api";
			make_include make_macros_h info "macros";
			
			(* source generation *)
			if not !quiet then Printf.printf "creating \"include/\"\n";
			makedir "src";
			link
				((Unix.getcwd ()) ^ "/" ^ info.Toc.ipath)
				(info.Toc.spath ^ "/target");
			make_makefile info;
			
			(* module linkig *)
			process_module info "gliss" "gliss";
			List.iter (fun (id, impl) -> process_module info impl id) !modules
		end

	with
	  Parsing.Parse_error ->
		Lexer.display_error "syntax error"; exit 2
	| Lexer.BadChar chr ->
		Lexer.display_error (Printf.sprintf "bad character '%c'" chr); exit 2
	| Sem.SemError msg ->
		Lexer.display_error (Printf.sprintf "semantics error : %s" msg); exit 2
	| Irg.IrgError msg ->
		Lexer.display_error (Printf.sprintf "ERROR: %s" msg); exit 2
	| Sem.SemErrorWithFun (msg, fn) ->
		Lexer.display_error (Printf.sprintf "semantics error : %s" msg);
		fn (); exit 2;
	| Toc.Error msg -> 
		Printf.fprintf stderr "ERROR: %s\n" msg;
		exit 4
	| Sys_error msg ->
		Printf.eprintf "ERROR: %s\n" msg; exit 1
	| Failure e ->
		Lexer.display_error e; exit 3

