(*
 * $Id: sem.ml,v 1.5 2008/07/22 09:49:10 jorquera Exp $
 * Copyright (c) 2007, IRIT - UPS <casse@irit.fr>
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
 * along with Foobar; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *)


open Irg

exception SemError of string
exception SemErrorWithFun of string * (unit -> unit)
exception ManyDefaultsInSwitch


(** False value. *)
let false_const = (*Irg.*)CARD_CONST Int32.zero
(** True value. *)
let true_const = (*Irg.*)CARD_CONST Int32.one


(** Convert from OCAML boolean to SimNML boolean.
	@param v	OCAML boolean.cstcst
	@return		SimNML boolean. *)
let to_bool v = if v then true_const else false_const


(** Convert constant to int32.
	@param c		Constant to convert.
	@return			Matching int32 value.
	@raise SemError	If the constant is not convertible. *)
let to_int32 c =
	match c with
	  CARD_CONST v -> v
	| _ -> raise (SemError "should evaluate to an int")


(** Convert constant to int.
	@param c		Constant to convert.
	@return			Matching int value.			print_expr e1;
			print_string " (";
			print_type_expr t1; 
			print_string ") ";
			print_string (string_of_binop bop);
			print_string " ";
			print_expr e2;
			print_string " (";
			print_type_expr t2;
			print_string ")";
			print_string "\n"; 
	@raise SemError	If the constant is not convertible. *)
let to_int c =
	Int32.to_int (to_int32 c)


(** Test if a constant is true.
	@param c	Constant to test.
	@return		True if constant is true. *)
let is_true c =
	match c with
	  NULL -> false
	| CARD_CONST v -> v <> Int32.zero
	| CARD_CONST_64 v-> v <> Int64.zero
	| STRING_CONST v -> v <> ""
	| FIXED_CONST v -> v <> 0.0





(**)
(* A verifier : 
	-Est ce normal que y soit de type Int32 ?
	-Ne devrait on pas utiliser des shift_<left/right>_logical ?
*)

(** Rotate an int32 to the left.
	@param x	Value to rotate.
	@param y	Amount of rotation.
	@return		Result of the rotation.*)
let rotate_left x y =
	let s = Int32.to_int (Int32.logand y (Int32.of_int 0x1f)) in
	Int32.logor (Int32.shift_left x s) (Int32.shift_right x (32 - s))


(** Rotate an int32 to the right.
	@param x	Value to rotate.
	@param y	Amount of rotation.
	@return		Result of the rotation.*)
let rotate_right x y =
	let s = Int32.to_int (Int32.logand y (Int32.of_int 0x1f)) in
	Int32.logor (Int32.shift_right x s) (Int32.shift_left x (32 - s))


(** Evaluate an unary operator.
	@param op	Unary operator.
	@param c	Constant to apply the operator to.
	@return		Result of the operation. *)
let eval_unop op c =
	match (op, c) with
	  ((*Irg.*)NOT, _) ->
	  	(*Irg.*)CARD_CONST (if (is_true c) then Int32.zero else Int32.one)
	| ((*Irg.*)BIN_NOT, (*Irg.*)CARD_CONST v) ->
		(*Irg.*)CARD_CONST (Int32.lognot v)
	| ((*Irg.*)NEG, (*Irg.*)CARD_CONST v) ->
		(*Irg.*)CARD_CONST (Int32.neg v)
	| ((*Irg.*)NEG, (*Irg.*)FIXED_CONST v) ->
		(*Irg.*)FIXED_CONST (-. v)
	| _ ->
		raise (SemError (Printf.sprintf "bad type operand for '%s'"
			(string_of_unop op))) 


(** Evaluate a binary operation.
	@param op	Operation.
	@param v1	First operand.
	@param v2	Second operand.
	@param 		Result. *)
let eval_binop_card op v1 v2 =
	match op with
	  (*Irg.*)ADD		->
	  	(*Irg.*)CARD_CONST (Int32.add v1 v2)
	| (*Irg.*)SUB		->
		(*Irg.*)CARD_CONST (Int32.sub v1 v2)
	| (*Irg.*)MUL		->
		(*Irg.*)CARD_CONST (Int32.mul v1 v2)
	| (*Irg.*)DIV		->
		(*Irg.*)CARD_CONST (Int32.div v1 v2)
	| (*Irg.*)MOD		->
		(*Irg.*)CARD_CONST (Int32.rem v1 v2)
	| (*Irg.*)EXP		->
		(*Irg.*)CARD_CONST (Int32.of_float ((Int32.to_float v1) ** (Int32.to_float v2)))
	| (*Irg.*)LSHIFT	->
		(*Irg.*)CARD_CONST (Int32.shift_left v1 (Int32.to_int v2))
	| (*Irg.*)RSHIFT	->
		(*Irg.*)CARD_CONST (Int32.shift_right v1 (Int32.to_int v2))
	| (*Irg.*)LROTATE	->
		(*Irg.*)CARD_CONST (rotate_left v1 v2)
	| (*Irg.*)RROTATE	->
		(*Irg.*)CARD_CONST (rotate_right v1 v2)
	| (*Irg.*)LT		->
		to_bool (v1 < v2)
	| (*Irg.*)GT		->
		to_bool (v1 > v2)
	| (*Irg.*)LE		->
		to_bool (v1 <= v2)
	| (*Irg.*)GE		->
		to_bool (v1 >= v2)
	| (*Irg.*)EQ		->
		to_bool (v1 = v2)
	| (*Irg.*)NE		->
		to_bool (v1 <> v2)
	| (*Irg.*)AND		->
		if (v1 <> Int32.zero) && (v2 <> Int32.zero) then true_const else false_const
	| (*Irg.*)OR		->
		if (v1 <> Int32.zero) || (v2 <> Int32.zero) then true_const else false_const
	| (*Irg.*)BIN_AND	->
		(*Irg.*)CARD_CONST (Int32.logand v1 v2)
	| (*Irg.*)BIN_OR	->
		(*Irg.*)CARD_CONST (Int32.logor v1 v2)
	| (*Irg.*)BIN_XOR	->
		(*Irg.*)CARD_CONST (Int32.logxor v1 v2)
	| _ ->
		raise (SemError (Printf.sprintf "bad type operand for '%s'"
			(string_of_binop op))) 


(** Evaluate a fixed binary operation.
	@param op	Operation.
	@param v1	First operand.
	@param v2	Second operand.
	@param 		Result. *)
let eval_binop_fixed op v1 v2 =
	match op with
	  ADD		->
		(*Irg.*)FIXED_CONST (v1 +. v2)
	| SUB		->
		(*Irg.*)FIXED_CONST (v1 -. v2)
	| MUL		->
		(*Irg.*)FIXED_CONST (v1 *. v2)
	| DIV		->
		(*Irg.*)FIXED_CONST (v1 /. v2)
	| EXP		->
		(*Irg.*)FIXED_CONST (v1 ** v2)
	| LT		->
		to_bool (v1 < v2)
	| GT		->
		to_bool (v1 > v2)
	| LE		->
		to_bool (v1 <= v2)
	| GE		->
		to_bool (v1 >= v2)
	| EQ		->
		to_bool (v1 = v2)
	| NE		->
		to_bool (v1 <> v2)
	| AND		->
		if v1 <> 0. && v2 <> 0. then true_const else false_const
	| OR		->
		if v1 <> 0. || v2 <> 0. then true_const else false_const
	| _ ->
		raise (SemError (Printf.sprintf "bad type operand for '%s'"
			(string_of_binop op))) 


(** Evaluate a string binary operation.
	@param op	Operation.
	@param v1	First operand.
	@param v2	Second operand.
	@param 		;Result. *)
let eval_binop_string op v1 v2 =
	match op with
	  LT 		-> to_bool (v1 < v2)
	| GT		-> to_bool (v1 > v2)
	| LE		-> to_bool (v1 <= v2)
	| GE		-> to_bool (v1 >= v2)
	| EQ		-> to_bool (v1 = v2)
	| NE		-> to_bool (v1 <> v2)
	| CONCAT	-> STRING_CONST (v1 ^ v2)
	| _ ->
		raise (SemError (Printf.sprintf "bad type operand for '%s'"
			(string_of_binop op))) 



(** Evaluate a binary operator.
	@param op	Binary operator.
	@param c1	First operand.
	@param c2	Second operand.
	@return		Result of the operation. *)
let eval_binop op c1 c2 =
	match (c1, c2) with
  	  (Irg.CARD_CONST v1, Irg.CARD_CONST v2) ->
		eval_binop_card op v1 v2
	| (Irg.FIXED_CONST v1, Irg.CARD_CONST v2) ->
		eval_binop_fixed op v1 (Int32.to_float v2)
	| (Irg.CARD_CONST v1, Irg.FIXED_CONST v2) ->
		eval_binop_fixed op (Int32.to_float v1) v2
	| (Irg.FIXED_CONST v1, Irg.FIXED_CONST v2) ->
		eval_binop_fixed op v1 v2
	| (Irg.STRING_CONST v1, Irg.STRING_CONST v2) ->
		eval_binop_string op v1 v2
	| _ ->
		raise (SemError (Printf.sprintf "bad type operand for '%s'"
			(string_of_binop op))) 


(** Perform the expression switch.
	@param c		Condition.
	@param cases	Cases of the switch.
	@param def		Default value. *)
let rec select c cases def =
	  match cases with
	    [] -> eval_const def
	  | (cp, e)::_ when cp = c -> eval_const e
	  | _::t -> select c t def

(** Evaluate an expression to constant.
	@param expr		Expression to evaluate. *)
and eval_const expr =
	match expr with
	  CONST (_,cst) ->
	  	cst
	| UNOP (_,op, e) ->
		eval_unop op (eval_const e)
	| BINOP (_,op, e1, e2) ->
		eval_binop op (eval_const e1) (eval_const e2)
	| IF_EXPR(_,c, t, e) ->
		if is_true (eval_const c) then eval_const t else eval_const e
	| SWITCH_EXPR (_,c, cases, def) ->
		select c cases def
	| REF id ->
		(match get_symbol id with
		  LET (_, cst) -> cst
		(**)
		|ENUM_POSS (_,_,v,_)->CARD_CONST v
		(**)
		| _ -> raise (SemError "this expression should be constant")) 
	| _ -> 
		raise (SemError "this expression should be constant")


(** Find a type by its identifier.
	@param id		Identifier of the looked type.
	@return			Type matching the identifier.
	@raise SemError	If the identifier does not exists or if the named item is
not a type. *)
let type_from_id id =
	try
		match StringHashtbl.find syms id with
		  TYPE (_, te) -> te
		| _ ->	raise (SemError (Printf.sprintf "%s does not named a type" id))
	with Not_found ->
		raise (SemError (Printf.sprintf "unknown identifier \"%s\"" id))


(** Check the matching of a type and a constant.
	@param t	Type to check.
	@param c	Constant to check.
	@return		True if they match, false else. *)
let check_constant_type t c =
	match (t, c) with
	  (BOOL, CARD_CONST v) ->
		(v = Int32.zero) || (v = Int32.one)
	| (CARD _, CARD_CONST _)
	| (INT _, CARD_CONST _)
	| (FIX _, FIXED_CONST _)
	| (FLOAT _, FIXED_CONST _) ->
		true
	| (RANGE (l, u), CARD_CONST v) ->
		((Int32.compare v l) >= 0) && ((Int32.compare v u) <= 0)
	| _ ->
		false


(** Give the size of a memory location
   @author PJ
   @param  loc		a memory location
   @return  the number of bit available of the location
*)
(*let rec  get_location_size loc = 
	match loc with
	  LOC_REF id -> (match Irg.get_symbol id with
			UNDEF -> raise (SemError (Printf.sprintf "get_location_size : undeclared memory location :\"%s\"" id))
			|MEM(s,i,t,_)|REG(s,i,t,_)|VAR(s,i,t) ->( match t with
								 NO_TYPE |RANGE _ -> 8  (* maybe à modifier *)
								|INT t|CARD t -> t
								|FIX(n,l)|FLOAT(n,l) -> n+l
								| _ -> raise (SemError "unexpected type")  )
			| _ ->raise (SemError (Printf.sprintf "get_location_size : identifier is not a memory location reference :\"%s\"" id)))

	| LOC_ITEMOF (loc,_) -> (get_location_size loc)
	| LOC_BITFIELD (_,e1,e2) ->(match ((eval_const e2),(eval_const e1))with
					 (CARD_CONST t,CARD_CONST v)-> (Int32.to_int t) - (Int32.to_int v)
					|(FIXED_CONST t,FIXED_CONST v) -> (int_of_float t)-(int_of_float v)
					|(CARD_CONST t,FIXED_CONST v) -> (Int32.to_int t)-(int_of_float v)
					|(FIXED_CONST t,CARD_CONST v) -> (int_of_float t)- (Int32.to_int v)
					|(STRING_CONST t,_)|(_,STRING_CONST t) -> raise (SemError (Printf.sprintf "get_location_size : uncompatible bitfield identifier :\"%s\"" t))
					|(NULL,_)|(_,NULL)->raise (SemError " memory location untyped "))
	| LOC_CONCAT (l1,l2) -> ((get_location_size l1) + (get_location_size l2))*)


(** make the implicit conversion a to b in b op a)
  @author PJ
  @param loc		location 
  @param expr_b		expression to cast
  @ return           expr_b casted to loc
*)

(*nml_cast a b = 
	match (a,b) with
	  (INT k,CARD(n,m)) ->  n+m
	| _ -> failwith*)


(** Test if a float number respects the IEE754 specification
    @param f          a nml float
    @return   true if the float is an IEEE754 float, false otherwise
    bit sign is first bit of the mantisse *)

let is_IEEE754_float f = match f with
	(FLOAT(m,e)) ->(match(m+e) with
			 32 -> (e =8)&&(m=24) 
			| 64 -> (e = 11)&&(m =53)
			| 80 -> (e = 15)&&(m = 65)
			| _  -> raise (SemError "float number doesn't follow IEEE754 specification "))
	| _ -> raise (SemError "function expect float number but parameter is not ")









(** Get the type associated with an identifiant.
	@param id	The identifiant to type.
	@return A type.	*)

let rec get_type_ident id=
	let symb= get_symbol id 
	in
	
	if symb=UNDEF
	then
		raise (SemError (Printf.sprintf "The keyword \"%s\" not defined" id))
	else

	(**)
	(*print_string "Spec : ";
	print_spec symb;*)
	(**)
	match symb with
	 LET (_,c)-> (match c with
			 NULL-> NO_TYPE
			|CARD_CONST _->CARD 32
			|CARD_CONST_64 _->CARD 64
			|STRING_CONST _->STRING
			|FIXED_CONST _->FLOAT (24,8))
	|TYPE (_,t)->(match t with
			ENUM l->(let i = List.length l in
				CARD (int_of_float (ceil ((log (float i)) /. (log 2.)))))
			|_->t)
	|MEM (_,_,t,_)->t
	|REG (_,_,t,_)->t
	|VAR (_,_,t)->t
	|AND_MODE (_,l,e,_)->	(
				 empiler_param l;
				 let t= get_type_expr e
				 in
				 depiler_param l;
				 t
				)
				
	(*|OR_MODE (n,l)->let type_mode = get_type_ident (List.hd l)
			in 
			if List.for_all (fun a-> if (get_type_ident a)=type_mode then true else false) (List.tl l)
				then type_mode
				else 
					let dsp=(fun _-> (	(List.map (fun a->print_string "\n--- ";print_string a;print_string " : ";print_type_expr (get_type_ident a);print_string "\n") l)	);()	)
					in
					raise (SemErrorWithFun ((Printf.sprintf "The or_mode %s is not of consistant type\n" n),dsp))*)
	|OR_MODE _->UNKNOW_TYPE


	(*|UNDEF->failwith "error get_type_ident"*)
	|PARAM (_,t)->(match t with
			 TYPE_ID idb->get_type_ident idb
			|TYPE_EXPR tb->tb)	(* ??? *)
	|ENUM_POSS (_,i,_,_)->get_type_ident i
	|_->NO_TYPE

(** Get the type of an expression
	@param exp 	Expression  to evaluate
	@return		the type of the parameter exp	*)

and get_type_expr exp=
	(**)
	(*print_string "Expr : ";
	print_expr exp;
	print_string "\n";*)
	(**)
	match exp with
		NONE->NO_TYPE
		|COERCE(t,_)->t
		|FORMAT (_,_)->STRING
		|CANON_EXPR (t,_,_) ->t
		|REF id->get_type_ident id 
		|FIELDOF (t,_,_)->t
		|ITEMOF (t,_,_)->t
		|BITFIELD (t,_,_,_)->t
		|UNOP (t,_,_)->t
		|BINOP (t,_,_,_)->t
		|IF_EXPR (t,_,_,_)->t
		|SWITCH_EXPR (t,_,_,_)->t
		|CONST (t,_)->t


(** Check the matching of a unary operation and the type of its operand.
	@param t	Type to check.
	@param uop	Operation to check.
	@return	True if they match, false else. *)

let check_unop_type t uop =
	match t with
	 UNKNOW_TYPE->true
	|(CARD _|INT _	|FIX (_,_) | FLOAT (_,_))->((uop=NOT)||(uop=NEG)||(uop=BIN_NOT))
	|STRING->false
	|_->(uop=NOT||uop=BIN_NOT)
	

(** Create a unary operation with a correct type in function of its operand.
	@param e	First operand.
	@param uop	Operation to apply.
	@return	An UNOP expression. *)

let get_unop e uop=

	let t=get_type_expr e 
	in
	if(not (check_unop_type t uop))
		then	let aff=fun _->(	
						print_string (string_of_unop uop);
						print_string " ";
						print_string "(";
						print_expr e;
						print_string ") -";
						print_type_expr t;
						print_string "-";
						print_string "\n" 
					 )
			in
			raise (SemErrorWithFun ("This unary operation is semantically incorrect",aff))



		else 	(match (uop,t) with
			(_,UNKNOW_TYPE)->UNOP (UNKNOW_TYPE, uop,e)
			|(NEG,CARD n)->UNOP(INT n,uop,e)	(*for the negation of a card, the type is int *)
			|_->UNOP (t,uop,e))
	
(** Check the matching of a binary operation and the type of its operands.
	@param t1	First type to check.
	@param t2	Second type to check
	@param bop	Operation to check.
	@return	True if they match, false else. *)

let check_binop_type t1 t2 bop =
	if(t1=NO_TYPE ||t2=NO_TYPE)
	then false
	else

	if (t1=UNKNOW_TYPE||t2=UNKNOW_TYPE) 
	then true
	else

	match bop with
	|(ADD|SUB)->(match (t1,t2) with
			((CARD _,CARD _)
			 |(INT _,INT _)
			 |(INT _, CARD _)
			 |(CARD _,INT _)
			 |(FLOAT _,FLOAT _)
			 |(FIX _,FIX _))->true
			|_->false)
	|(MUL|DIV|MOD)-> (match (t1,t2) with
			((CARD _,CARD _)
			 |(INT _,INT _)
			 |(INT _, CARD _)
			 |(CARD _,INT _)
			 |(FLOAT _,FLOAT _)
			 |(FIX _,FIX _)
			 |(FIX _,CARD _)
			 |(CARD _,FIX _)
			 |(FLOAT _,CARD _)
			 |(CARD _,FLOAT _)
			 |(FIX _,INT _)
			 |(INT _,FIX _)
			 |(FLOAT _,INT _)
			 |(INT _,FLOAT _))->true
			|_->false)
	|EXP-> (t1!=BOOL)&&(t2!=BOOL)&&(t1!=STRING)&&(t2!=STRING)
	|(LSHIFT|RSHIFT|LROTATE|RROTATE)-> (*(match (t1,t2) with
						((CARD _,CARD _)
						 |(INT _,CARD _)
						 |(FLOAT _, CARD _)
						 |(FIX _, CARD _))->true
						|_->false)*)

					(* nécesssaire pour compatibilité avec arm.nmp *)
					(match t1 with
					(CARD _|INT _|FIX _|FLOAT _)->(match t2 with
									(CARD _|INT _)->true
									|_->false)
					|_->false)
				

	|(LT|GT|LE|GE|EQ|NE)->	(match t1 with
					(CARD _|INT _|FIX _|FLOAT _)->(match t2 with
									(CARD _|INT _|FIX _|FLOAT _)->true
									|_->false)
					|_->false)
	|(AND|OR)->true
	|(BIN_AND|BIN_OR|BIN_XOR)-> (match t1 with
					(BOOL|CARD _|INT _|FIX _|FLOAT _)->(match t2 with
									(BOOL|CARD _|INT _|FIX _|FLOAT _)->true
									|_->false)
					|_->false)
	|CONCAT-> (match t1 with
					(CARD _|INT _)->(match t2 with
									(CARD _|INT _)->true
									|_->false)
					|_->false)



(** Create an add/sub with a correct type in function of its operands.
	This function is used in get_binop.
	@param e1	First operand.
	@param e2	Second operand.
	@param bop	ADD/SUB
	@return	An ADD/SUB expression. *)

let get_add_sub e1 e2 bop=
	let t1=get_type_expr e1 
	and t2=get_type_expr e2
	in
	match (t1,t2) with
	  ((UNKNOW_TYPE,_)|(_,UNKNOW_TYPE))->BINOP (UNKNOW_TYPE, bop,e1,e2)
	|(FLOAT (m,n),FLOAT (m2,n2)) when m2=m && n2=n-> BINOP (FLOAT (m,n), bop,e1,e2)
	|(FIX (m,n),FIX (m2,n2)) when m2=m && n2=n->BINOP (FIX (m,n), bop,e1,e2)
	|(INT n, INT n2) when n2=n-> BINOP (INT n,bop, e1,e2)
	|(CARD n,CARD n2) when n2=n->BINOP(CARD n,bop,e1,e2)
	|(INT m, CARD n)->BINOP(INT ((max m n)+2),bop,e1,e2)
	|(CARD m,INT n)-> BINOP (INT ((max m n)+2),bop, e1, e2)
	|(INT m, INT n)->BINOP (INT ((max m n)+2), bop, e1,e2)
	|(CARD m, CARD n)->BINOP (INT ((max m n)+2), bop, e1,e2)
	|_->failwith "internal error : get_add_sub"		(*A CHANGER *)

(** Create a mult/div/mod with a correct type in function of its operands.
	This function is used in get_binop.
	@param e1	First operand.
	@param e2	Second operand.
	@param bop	MUL/DIV/MOD
	@return	A MUL/DIV/MOD expression. *)

let get_mult_div_mod e1 e2 bop=
	let t1=get_type_expr e1 
	and t2=get_type_expr e2
	in
	match (t1,t2) with
	  ((UNKNOW_TYPE,_)|(_,UNKNOW_TYPE))->BINOP (UNKNOW_TYPE, bop,e1,e2)
	|(FLOAT (m,n),FLOAT (m2,n2)) when m=m2 && n=n2-> BINOP (FLOAT (m,n), bop,e1,e2)
	|(FIX (m,n),FIX (m2,n2))when m=m2 && n=n2->BINOP (FIX (m,n), bop,e1,e2)
	|(INT n, INT n2) when n=n2-> BINOP (INT n,bop, e1,e2)
	|(CARD n,CARD n2) when n=n2->BINOP (CARD n,bop,e1,e2)
	|(INT m, CARD n)->BINOP (INT ((max m n)*2),bop,e1,e2)
	|(CARD m,INT n)-> BINOP (INT ((max m n)*2),bop, e1, e2)
	|(INT m, INT n)->BINOP (INT ((max m n)*2), bop, e1,e2)
	|(CARD m, CARD n)->BINOP (INT ((max m n)*2), bop, e1,e2)
	|((FLOAT (m,n),INT _)|(INT _,FLOAT (m,n))|(FLOAT(m,n),CARD _)|(CARD _,FLOAT(m,n)))->BINOP (FLOAT(m,n), bop,e1,e2)
	|((FIX (m,n),INT _)|(INT _,FIX (m,n))|(FIX(m,n),CARD _)|(CARD _,FIX(m,n)))->BINOP (FIX(m,n), bop,e1,e2)
	|_->failwith "internal error : get_mult_div_mod"		(*A CHANGER *)
	
(** Create a concat with a correct type in function of its operands.
	This function is used in get_binop.
	@param e1	First operand.
	@param e2	Second operand.
	@return	A CONCAT expression. *)

let rec get_concat e1 e2=
	
	let t1=get_type_expr e1 
	and t2=get_type_expr e2
	in
	
	match (t1,t2) with
	  ((UNKNOW_TYPE,_)|(_,UNKNOW_TYPE))->BINOP (UNKNOW_TYPE, CONCAT,e1,e2)
	|(CARD m, CARD n) -> BINOP (CARD (n+m), CONCAT,e1,e2)
(*	|(INT m,_)->	get_concat (cast (CARD m) e1) e2
	|(_,INT n)->	get_concat e1 (cast (CARD n) e2) *)
	|_->failwith "internal error : get_concat"		(*A CHANGER *)

(** Create a binary operation with a correct type in function of its operands.
	@param e1	First operand.
	@param e2	Second operand.
	@param bop	Operation to apply.
	@return	A BINOP expression. *)

let rec get_binop e1 e2 bop=

	let t1=get_type_expr e1 
	and t2=get_type_expr e2
	in

	if( not (check_binop_type t1 t2 bop))
	then 	(	

			let aff=fun _->(	
						print_string "(";
						print_expr e1;
						print_string ") -";
						print_type_expr t1; 
						print_string "- ";
						print_string (string_of_binop bop);
						print_string " ";
						print_string "(";
						print_expr e2;
						print_string ") -";
						print_type_expr t2;
						print_string "-";
						print_string "\n" 
					 )
			in
			raise (SemErrorWithFun ("This binary operation is semantically incorrect",aff))
		)
	else
		match bop with
	 	(ADD|SUB)->get_add_sub e1 e2 bop
		|(MUL|DIV|MOD)->get_mult_div_mod  e1 e2 bop
		|EXP->BINOP (t1,bop,e1,e2)	(* A changer (le type)  *)
		|(LSHIFT|RSHIFT|LROTATE|RROTATE)->BINOP(t1,bop,e1,e2)
		|(LT|GT|LE|GE|EQ|NE)->BINOP(BOOL,bop,e1,e2)
		|(AND|OR)-> BINOP(BOOL,bop,e1,e2)
		|(BIN_AND|BIN_OR|BIN_XOR)->BINOP(t1, bop, e1,e2)
		|CONCAT->get_concat e1 e2





(** Check if the possible expressions of the conditionnal branchs of an if-then-else expression give a valid if-then-else expression.
	It check if the types of the differents possibility are compatible (for this, it use the same compatibility rule than the addition).
	
	@param e1	the then-expression
	@param e2	the else-expression
	@return True if the parameters give a valid conditionnal statement, false otherwise *)

let check_if_expr e1 e2=
	let t1=(get_type_expr e1)
	and t2=(get_type_expr e2)	
	in
	(check_binop_type t1 t2 Irg.ADD) 	(*The allowed types are the sames than those of the operation ADD *)
	(*|| t2=NO_TYPE		NOT ALLOWED*)			






(* plein de sous-fonctions utilisees pour la verification du switch : a commenter *)	(* A CHANGER *)

(*
let get_type_const c=
	match c with
		 NULL->NO_TYPE
		|CARD_CONST _->CARD 32
		|CARD_CONST_64 _ ->CARD 64
		|STRING_CONST _->STRING
		|FIXED_CONST v ->FLOAT (int_of_float (fst (frexp v)),(snd (frexp v)))

let get_string_form_const c=	(* A changer *)
	match c with
	 NULL->""
	|CARD_CONST v->Int32.to_string v
	|CARD_CONST_64 v ->Int64.to_string v
	|STRING_CONST v->v
	|FIXED_CONST v ->string_of_float v
*)

let is_param_of_type_enum e=

 	match e with
		REF i ->( match (get_symbol i) with
				PARAM (_,t)->(match t with
					 	TYPE_ID ti-> (match (get_symbol ti) with
									TYPE (_,t)->(match t with
							 				ENUM _-> true
											|_->false
										     )
									|_->false
								)
						|TYPE_EXPR te->(match te with
									ENUM _->true	(*Possible ?*)
									|_->false
								)
						)
				
				|_->false
			)
		|_->false


let get_list_poss_from_enum_expr e= (* A CHANGER *)
	let rec temp id=(match get_symbol id with
				TYPE (_,t)-> (match t with
						ENUM l->l
						|_->failwith "get_list_poss_from_enum_expr : expr is not an enum"
					)
				|PARAM (_,t)->(match t with
							TYPE_ID s->temp s
							|TYPE_EXPR tb->(match tb with
										ENUM l->l
										|_->failwith "get_list_poss_from_enum_expr : expr is not an enum"
									)
						)
				|_->failwith "get_list_poss_from_enum_expr : expr is not an enum"

			)

	in
	match e with
		REF id -> temp id
		|_->failwith "get_list_poss_from_enum_expr : expr is not an enum"

let is_enum_poss e =
	match e with
	 REF s->(match (get_symbol s) with
			ENUM_POSS _->true
			|_->false
		) 
	|_->false


let get_enum_poss_info e=
	match e with
	REF s->(match (get_symbol s) with
			ENUM_POSS (_,r,t,_)->(r,t)
			|_->failwith ("get_enum : expression is not an enum poss")	(* A CHANGER *)
		)
	|_->failwith "get_enum : expression is not an enum poss"	(* A CHANGER *)



let get_enum_poss_type e= get_type_ident (fst (get_enum_poss_info e))


(*let get_enum_poss_type e=
	match e with
	REF s->(match (get_symbol s) with
			ENUM_POSS (r,_,_)->get_type_ident r
			|_->failwith ("get_enum_type : expression is not an enum poss")	(* A CHANGER *)
		)
	|_->failwith "get_enum_type : expression is not an enum poss"	(* A CHANGER *)
*)

let get_enum_poss_id e=
	match e with
	REF s->(match (get_symbol s) with
			ENUM_POSS (_,_,_,_)->s
			|_->failwith ("get_enum_poss_id : expression is not an enum poss")	(* A CHANGER *)
		)
	|_->failwith "get_enum_poss_id : expression is not an enum poss"	(* A CHANGER *)


(** Check if the given parameters of a switch expression give a valid switch expression.
	It check that all the cases are of the same type than the condition ,
	that all the cases and the default return an expression of the same type,
	that all pssibilites are covered by the cases.
	
	TODO : Allow compatibles types (instead of strictly the same type) to be presents in the conditional part of the cases

	@param test	the condition of the switch.
	@param list_case	the couple list of the cases.
	@param default	the default of the switch.(NONE if no default)
	@return the type of the switch *)

let check_switch_expr test list_case default=

(* This part check if all the cases of a switch are of the type of the expression to be tested*)

let check_switch_cases =

	let rec sub_fun list_c t=
			match list_c with
			 []->true
			|(c,_)::l-> if(is_enum_poss c) 
					then (get_enum_poss_type c=t) && (sub_fun l  t)
					else (get_type_expr c=t ) && (sub_fun l  t)			
	in
	let t= get_type_expr test
	in
	match t with
	CARD _->sub_fun list_case (get_type_expr test)
	|_->false 
	


(* This part check if all the possible result of a switch expression are of the same type *)

and check_switch_return_type =
	let type_default = get_type_expr default
	in
	let rec sub_fun list_c t=
			match list_c with
			 []->true
			|(_,e)::l-> (get_type_expr e)=t  && sub_fun l  t
	in
	if type_default = NO_TYPE
			then sub_fun list_case (get_type_expr (snd (List.hd list_case)))
			else sub_fun list_case type_default

(* This part check if all the possibles values of the expression to test are covered *)

and check_switch_all_possibilities =
	
		if (not (default=NONE)) then true
		else (* a default is needed to be sure that all possibilities are covered, except for ENUM*)
		if is_param_of_type_enum test 
		then	
			let l=get_list_poss_from_enum_expr test	(* l is the id list of the enum type used *)
			in
			let cond_list=List.map get_enum_poss_id (List.map fst list_case)	(*cond_list is the list of id of the enum type who are presents in the swith *)
			in
			List.for_all (fun e->List.exists (fun a->a=e) cond_list) l	(* check that all element of l are contained in cond_list *)
		else false
in

	if not check_switch_cases 
		then raise (SemError "the cases of a functional switch must be consitent with the expression to test")
	else if not check_switch_return_type
		then raise (SemError "the return values of a functionnal switch must be of the sames type")
	else if not check_switch_all_possibilities
		then raise (SemError "the cases of a functional switch must cover all possibilities or contain a default")
	else if (get_type_expr default != NO_TYPE)
		then get_type_expr default
		else get_type_expr (snd (List.hd list_case))


(* is_location est a verifier *)

(** Check is the given id refer to a valid memory location
	@ param id	the id to check
	@return True if the id is a valid memory location, false otherwise *)

let rec is_location id=
	let sym=Irg.get_symbol id
	and is_location_param id=
		let sym=Irg.get_symbol id
		in
		match sym with
			 (MEM (_,_,_,_)|REG (_,_,_,_)|VAR(_,_,_))->true
			|_->false
	in	
	(*print_spec sym;*)
	match sym with
	 (MEM (_,_,_,_)|REG (_,_,_,_)|VAR(_,_,_))->true
	|PARAM (_,t)->(match t with
			 TYPE_ID idb-> is_location_param idb
			| TYPE_EXPR _->false
			)
	|_->false

let rec is_loc_mode id =	(* Necessaire pour reconnaitre certaines instructions du ppc *)
	let sym=Irg.get_symbol id
	and is_location_param id=
		let sym=Irg.get_symbol id
		in
		match sym with	
			(AND_MODE(_,_,_,_)|OR_MODE(_,_))->true			
			|_->false
	in	
	match sym with
	PARAM (_,t)->(match t with
			 TYPE_ID idb-> is_location_param idb
			| TYPE_EXPR _->false
			)
	|_->false

let rec is_loc_spe id=	(* Necessaire pour reconnaitre certaines instructions du predecode *)
	let sym=Irg.get_symbol id
	and is_location_param id=
		let sym=Irg.get_symbol id
		in
		match sym with
			 TYPE _->true
			|_->false
	in
	match sym with
	 PARAM (_,t)->(match t with
			 TYPE_ID idb-> is_location_param idb
			| TYPE_EXPR _->true	
			)
	|_->false	


(** Check if the given location is a parameter.
	This possibility is not allowed in the nML standard. But it was with some versions of GLISS v1 (in the predecode attribute).
	We keep it here for compatibility with previous versions only. *)

let is_setspe loc=	
	match loc with
	LOC_REF id->(let symb= get_symbol id 
			in
			match  symb with
				|PARAM _->true
				|_->false
		   )
	|_->false	


(** Create a FORMAT operation and check if it is well written
	@param str	The string to print
	@param exp_list	The list of parameters to be used as variables in str
	@return A FORMAT expression *)

let build_format str exp_list=

(* subfunctions*)

let reg_exp=Str.regexp "%[0-9]*[dbxs]"	(* The expression %0b was used with some versions of Gliss v1 to avoid a bug, so we allow it here for compatibility *)
in

let get_all_ref str=	(* this subfunction is used to find all references to a parameter in str (the string passed to format) *)
	let str_list=Str.full_split reg_exp str
	in
	let rec temp str_l res_l=
		match str_l with
		 []->res_l
		|e::l->( match e with
				Str.Text _->temp l res_l
				|Str.Delim s->temp l (s::res_l)
			)
	in
	temp str_list []
in

let get_length_from_expr e=	(*this subfunction give the bit lenght of an expression (-1 for a string expression) *)
	let t=get_type_expr e
	in
	match t with
	 BOOL-> 1
	|INT n->n
	|CARD n->n
	|FIX (n,m)->n+m
	|FLOAT(n,m)->n+m
	|STRING->(-1)
	|_->failwith "internal error : get_length_from_type_expr"
in

(* end subfunctions*)

	let ref_list=get_all_ref str
	in
	if (not (List.length ref_list = List.length exp_list)) || List.length exp_list = 0	(* it is not allowed using format to print a string without at least one variable *)
		then
			raise (SemError (Printf.sprintf "incorrect number of parameters in format"))
		else
			let test_list = List.map2 (fun e_s e_i->	(* here we check if all variables are given a parameter of the good type *)
					if (get_type_expr e_i=UNKNOW_TYPE)
					then true
					else
					let num= try(int_of_string (String.sub e_s 1 ((String.length e_s)-2)))with Failure "int_of_string" -> 0
					in
					match Str.last_chars e_s 1 with
						 "d"-> (match (get_type_expr e_i) with 
								(CARD _|INT _)->true
								|_->false)

						|"b"->(try(
								get_length_from_expr e_i = num || get_length_from_expr e_i =(-1)
							)with Failure "internal error : get_length_from_type_expr"->false)

						|"x"->(match (get_type_expr e_i) with 
								(CARD _|INT _)->true
								|_->false)

						|"s"-> (match (get_type_expr e_i) with 
								STRING->true
								|_->false)

						|_->failwith "internal error : build_format"
					) ref_list exp_list
			in
			if not (List.for_all (fun e->e) test_list) then raise (SemError (Printf.sprintf "incorrect type in this format "))
			else
			FORMAT (str, exp_list)


(*

let rec get_length id =
	let sym=get_symbol id
	in
	match sym with
	UNDEF->failwith "get_length : undefined symbol" (* a changer *)
	|LET (_,const)->(match const with
				 NULL->failwith "get_length : id refer to a NULL const" (* a changer *)
				|CARD_CONST _->32	(* a changer *)
				|CARD_CONST_64 _->64
				|STRING_CONST _->let dsp= fun _->(Printf.printf "the id %s refer to a STRING const\n" id;())
						 in
						 raise (SemErrorWithFun ("",dsp))
				|FIXED_CONST _ ->32	(* a changer *)
			)
	|MEM (_,i,_,_)->i
	|REG (_,i,_,_)->i
	|VAR (_,i,_)->i
	|PARAM (s,_)->get_length s
	|_->let dsp =fun _->(Printf.printf "the id %s do no refer to a location\n" id;())
	    in
	    raise (SemErrorWithFun ("",dsp))
*)

(*
let have_attribute id attr=

	let rec loop_verification id mem_list   =
		let sym_temp=get_symbol id
		in
		match sym_temp with
		 OR_MODE (_,l)->if (List.exists (fun e->e==id) mem_list)
					then false 
					else (List.for_all (fun e->loop_verification e (id::mem_list)) l)
		|_->true
	in

	let rec temp id attr aff=
		let sym=get_symbol id
		in
		let rec contains l= match l with
			 []->false
			|e::lt->( match e with 
					 (ATTR_EXPR (v,_)|ATTR_STAT (v,_)) when v=attr->true
					|_->contains lt)
			(*
			match attr with
			 ("syntax"|"image")->List.exist (fun a-> match a with ATTR_EXPR (attr,_)->true | _->false) l
			|_->List.exist (fun a->match a with ATTR_STAT (attr,_)->true | _->false) l
			*)
		in
		match sym with
			 (AND_MODE (_,_,_,l)|AND_OP (_,_,l))->contains l
			|(OR_MODE (_,l)|OR_OP(_,l))->if List.exists (fun e->temp e attr false) l 
							then
								((if List.for_all (fun e->temp e attr false) l && aff
									then
										Lexer.display_warning (Printf.sprintf "not all modes included in the mode %s have the attribute %s" id attr)
								); true)
							else
								false
			|PARAM (_,t)->(match t with TYPE_ID idt->temp idt attr aff
						|_->false)
			|_->false
	in
	if not (loop_verification id []) then raise (SemError (Printf.sprintf "looping declaration of mode %s" id))
	else
	temp id attr true
*)
