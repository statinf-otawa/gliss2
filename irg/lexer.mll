(*
 * $Id: lexer.mll,v 1.8 2008/09/30 11:03:42 casse Exp $
 * Copyright (c) 2007, IRIT - UPS <casse@irit.fr>
 *
 * Lexer of OGEP.
 *)
{

open Parser
open Lexing
exception BadChar of char
exception BadLine

(* Line count *)
let file = ref ""
let line = ref 1
let bitfld = ref false

(* Keyword detection *)
let lexicon = Irg.StringHashtbl.create 211
let keyword id =
	try
		let e=Irg.StringHashtbl.find lexicon id
		in
		match e with
		 EXCEPTION _->EXCEPTION !line
		|LET _->LET !line
		|MEM _->MEM !line
		|MODE _->MODE !line
		|OP _-> OP !line
		|REG _->REG !line
		|VAR _->VAR !line
		|RESOURCE _->RESOURCE !line
		|TYPE _->TYPE !line	
		|_->e
	with Not_found -> (ID id)

let keywords = [ 
	("action",      ACTION);
	("alias",       ALIAS);
	("ports",       PORTS);
	("bool",        BOOL);
	("card",        CARD);
	("case",        CASE);
	("coerce",      COERCE);
	("default",     DEFAULT);
	("else",        ELSE);
	("endif",       ENDIF);
	("enum",        ENUM);
	("error",       ERROR);
	("exception",   EXCEPTION 0);
	("fix",        	FIX);
	("float",       FLOAT);
	("format",      FORMAT);
	("if",        	IF);
	("image",       IMAGE);
	("initial",     INITIALA);
	("int",        	INT);
	("let",        	LET 0);
	("list",        LIST);
	("macro",       MACRO);
	("mem",        	MEM 0);
	("mode",        MODE 0);
	("nop",        	NOP);
	("not",        	NOT);
	("op",        	OP 0);
	("reg",        	REG 0);
	("var",        	VAR 0);
	("resource",    RESOURCE 0);
	("syntax",      SYNTAX);
	("switch",      SWITCH);
	("then",        THEN);
	("type",        TYPE 0);
	("uses",        USES);
	("volatile",    VOLATILE)
]

let _ =
	let add (key, token) = Irg.StringHashtbl.add lexicon key token in
	Irg.StringHashtbl.clear lexicon;
	List.iter add keywords


(* Error management *)
let display_error msg =
	Printf.fprintf stderr "%s:%d:%s\n" !file !line msg

(*warning management *)
let display_warning msg=
	Printf.fprintf stderr "Warning%s:%d:%s\n" !file !line msg

(* Lexing add-ons *)
let rec dotdot lexbuf i found =
	if i >= lexbuf.lex_buffer_len then
		if lexbuf.lex_eof_reached then false
		else begin
			let diff = i - lexbuf.lex_start_pos in
			lexbuf.refill_buff lexbuf;
			dotdot lexbuf (lexbuf.lex_start_pos + diff) found
		end
	else
		match lexbuf.lex_buffer.[i] with
		  '\n' -> false
		| '.' -> if found then true else dotdot lexbuf (i + 1) true
		| '<' | '>' | '=' | ';' | '}' -> false
		| _ -> dotdot lexbuf (i + 1) false

let gt lexbuf token size =
	if not !bitfld then token
	else begin
		(*Printf.printf "len=%d, start=%d, cur=%d, last=%d\n"
			lexbuf.lex_buffer_len
			lexbuf.lex_start_pos
			lexbuf.lex_curr_pos
			lexbuf.lex_last_pos
			;*)
		bitfld := false;
		lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos - size;
		GT
	end

}

let letter	= ['a' - 'z' 'A' - 'Z' '_']
let digit	= ['0' - '9']
let hex		= ['0' - '9' 'a' - 'f' 'A' - 'F']
let alpha	= ['0' - '9' 'a' - 'z' 'A' - 'Z' '_']
let delim	= [' ' '\t']
let newline	= ['\n']
let decint	= digit +
let binint	= '0' ['b' 'B'] ['0' '1']+
let hexint	= '0' ['x' 'X'] hex+
let flt1	= decint '.' decint
let flt2	= decint ['e' 'E'] ['+' '-']? decint
let flt3	= decint '.' decint ['e' 'E'] ['+' '-']? decint
let flt		= flt1 | flt2 | flt3
let id		= letter alpha*

(**)
let num=decint|hexint|binint
(**)
 
rule main = parse

	delim		{ main lexbuf } 
|	newline		{ incr line; main lexbuf }
|	"//"		{ eof_comment lexbuf }
|	"/*"		{ comment lexbuf }

|	"\""		{ STRING_CONST  (str "" lexbuf) }
|	"'"			{ chr "" lexbuf }
|	"#line"		{ scan_line lexbuf; scan_file lexbuf; main lexbuf }

|num as v 		{	try(
					CARD_CONST (Int32.of_string v)
				)with Failure _-> CARD_CONST_64 (Int64.of_string v)
			}

(**)

|	flt as v	{ FIXED_CONST (float_of_string v) }
|	id as v		{  keyword v }
|	">>>"		{ gt lexbuf ROTATE_RIGHT 2 }
|	"<<<"		{ ROTATE_LEFT }
|	">>"		{ gt lexbuf RIGHT_SHIFT 1 }
|	"<<"		{ LEFT_SHIFT }
|	".."		{ DOUBLE_DOT }
|	"::"		{ DOUBLE_COLON }
|	"**"		{ DOUBLE_STAR }
|	">="		{ gt lexbuf GEQ 1 }
|	"=="		{ EQU }
|	"!="		{ NEQ }
|	"&&"		{ AND }
|	"||"		{ OR }
|	"<="		{ LEQ }
|	"<"		{
			 if dotdot lexbuf lexbuf.lex_last_pos false
				then 
					begin bitfld := true; BIT_LEFT end
				else 
					LT
			}
|	">"     	{ bitfld := false; GT }
|	"$"     	{ DOLLAR }
|	"#"		{ SHARP }
|	"="		{ EQ }
|	"."		{ DOT }
|	"&"		{ AMPERS }
|	"|"		{ PIPE }
|	":"		{ COLON }
|	"!"		{ EXCLAM }
|	";"		{ SEMI }
|	","		{ COMMA }
|	"("		{ LPAREN }
|	")"		{ RPAREN }
|	"["		{ LBRACK }
|	"]"		{ RBRACK }
|	"{"		{ LBRACE }
|	"}"		{ RBRACE }
|	"+"		{ PLUS }
|	"-"		{ MINUS }
|	"*"		{ STAR }
|	"/"		{ SLASH }
|	"%"		{ PERCENT }
|	"~"		{ TILD }
|	"^"		{ CIRC }

|	eof		{ EOF }
|	_ as v		{ raise (BadChar v) }

(* eof_comment *)
and eof_comment = parse
	'\n'	{ incr line; main lexbuf }
|	_		{ eof_comment lexbuf }

(* comment *)
and comment = parse
	"*/"	{ main lexbuf }

|	'\n'	{ incr line; (*main*)comment lexbuf }
|	_		{ comment lexbuf }

(* string recognition *)
and str res = parse
	"\""			{ res }
|	"\\" (_	as v)	{ str (res ^ (String.make 1 v)) lexbuf }
|	_ as v			{ str (res ^ (String.make 1 v)) lexbuf }

(* character recognition *)
and chr res = parse
	"\'"			{ STRING_CONST res }
|	"\\" (_	as v)	{ chr (res ^ (String.make 1 v)) lexbuf }
|	_ as v			{ chr (res ^ (String.make 1 v)) lexbuf }

and scan_line = parse
	digit+ as l	{ line := (int_of_string l) - 1 }
|	delim		{ scan_line lexbuf }
|	_			{ raise BadLine }

and scan_file = parse
	delim		{ scan_file lexbuf }
|	"\""		{ file := (str "" lexbuf) }
|	_			{ raise BadLine }
