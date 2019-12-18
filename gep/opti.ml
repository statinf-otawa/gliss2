(*
 * GLISS2 -- optimizations
 * Copyright (c) 2019, IRIT - UPS <casse@irit.fr>
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
open Printf

(** Reduce the constant expressions, possibly removing dead code, in the
	given statement corresponding to the given attribute name (used to
	manage attribute recursive call).
	
	All no recursive attributes are embedded. The parameters and the
	attributes of the current specification must be installed in the
	symbol table.
	
	@param name	Name of the attribute.
	@param s	Statement to reduce.
	@return		Reduce statement. *)
let rec reduce_const_stmt name s = 
	let eval = Sem.eval_const in
	let is_const = Sem.is_const in
	let is_true = Sem.is_true in
	
	let rec select f d c cs =
		match cs with
		| [] ->
			f d
		| (k, x)::cs ->
			if is_true (eval (Sem.get_binop c k EQ))
			then f x
			else select f d c cs
	
	and stmt cs s =
		match s with
		| NOP ->
			NOP
		| SEQ (s1, s2) ->
			SEQ (stmt cs s1, stmt cs s2)
		| EVAL ("", id) ->
			call cs id
		| EVAL _ ->
			failwith "Opti.reduce_const.eval"
		| SET (l, e) ->
			SET(loc l, expr e)
		| CANON_STAT (id, ps) ->
			CANON_STAT (id, List.map expr ps)
		| ERROR _ ->
			s
		| LINE (_, _, s) ->
			stmt cs s
		| LOCAL (vn, on, t, i) ->
			LOCAL (vn, on, t, expr i)
		| FOR (vn, on, t, l, u, s) ->
			FOR (vn, on, t, l, u, stmt cs s)
		| IF_STAT (c, s1, s2) ->
			let c = expr c in
			if not (is_const c)
			then IF_STAT (c, stmt cs s1, stmt cs s2)
			else if is_true (eval c)
			then stmt cs s1
			else stmt cs s2
		| SWITCH_STAT (c, cc, d) ->
			let c = expr c in
			if is_const c then
				select (stmt cs) d c cc
			else
				SWITCH_STAT (c, List.map (fun (c, s) -> (expr c, stmt cs s)) cc, stmt cs d)
	
	and call cs id =
		if List.mem id cs then EVAL ("", id) else
		match get_symbol id with
		| ATTR (ATTR_STAT (_, s)) ->
			stmt (id::cs) s
		| _ ->
			failwith "Opti.reduce_const.call"
	
	and expr = reduce_const_expr

	and loc l =
		match l with
		| LOC_NONE ->
			l
		| LOC_REF (t, id, ix, u, l) ->
			LOC_REF (t, id, expr ix, expr u, expr l)
		| LOC_CONCAT (t, l1, l2) ->
			LOC_CONCAT (t, loc l1, loc l2) in
	
	stmt [name] s

and reduce_const_expr e =
	let eval = Sem.eval_const in
	let is_const = Sem.is_const in

	let rec expr e =
		match e with
		| NONE ->
			e
		| COERCE (t, e) ->
			let e = expr e in
			let ee = COERCE(t, e) in
			if is_const e then CONST (t, eval ee) else ee
		| FORMAT (fmt, ps) ->
			FORMAT(fmt, List.map expr ps)
		| CANON_EXPR (t, fmt, ps) ->
			CANON_EXPR(t, fmt, List.map expr ps)
		| REF (t, id) ->
			(match get_symbol id with
			| ATTR (ATTR_EXPR (_, e)) -> expr e
			| LET (_, t, c, _) -> CONST (t, c)
			| _ -> REF (t, id))
		| FIELDOF _ ->
			failwith "Opti.reduce_const.expr"
		| ITEMOF (t, id, ix) ->
			ITEMOF (t, id, expr ix)
		| BITFIELD (t, b, u, l) ->
			let b, u, l = expr b, expr u, expr l in
			let e = BITFIELD (t, b, u, l) in
			if (is_const b) && (is_const u) && (is_const l)
			then CONST (t, eval e)
			else e
		| UNOP (t, op, e) ->
			let e = expr e in
			let ee = UNOP (t, op, e) in
			if is_const e
			then CONST (t, eval ee)
			else ee
		| BINOP (t, op, e1, e2) ->
			let e1, e2 = expr e1, expr e2 in
			let e = BINOP (t, op, e1, e2) in
			if (is_const e1) && (is_const e2)
			then CONST (t, eval e)
			else e
		| CONST _ ->
			e
		| ELINE (f, l, e) ->
			let e = expr e in
			if is_const e then e else ELINE (f, l, e)
		| CAST (t, e) ->
			let e = expr e in
			let ee = CAST (t, e) in
			if is_const e then CONST (t, eval ee) else ee
		| IF_EXPR (t, c, e1, e2) ->
			let c = expr c in
			let e = IF_EXPR (t, c, expr e1, expr e2) in
			if is_const c then CONST (t, eval e) else e
		| SWITCH_EXPR (t, c, cs, d) ->
			let c = expr c in
			let e = SWITCH_EXPR(t, c, List.map (fun (c, e) -> (expr c, expr e)) cs, expr d) in
			if is_const c
			then CONST (t, eval e)
			else e in
		
	expr e

