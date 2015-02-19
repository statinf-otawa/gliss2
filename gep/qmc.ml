(*
 * GLISS2 -- Quine - Mac Cluskey method implementation.
 * Copyright (c) 2015, IRIT - UPS <casse@irit.fr>
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

type term_t = string

let bot = '_'
let one = '1'
let zero = '0'
let x = 'X'

(** Counter the number of b in the given word w.
	@param w	Word to count in.
	@param b	Counted bit (0, 1 or X).
	@return		Count of b in w. *)
let count w b =
	let rec look i s =
		if i >= (String.length w) then s else
		look (i + 1) (s + (if (String.get w i) == b then 1 else 0)) in
	look 0 0


(** Join both bits.
	@param a	First bit (0, 1 or X).
	@param b	Second bit (0, 1, or X).
	@return		Join result (0, 1, X or _). *)
let join a b =
	if a = b then a else
	if a = x || b = x then bot else
	x


(** Merge word w1 and w2.
	@param w1	First word.
	@param w2	Second word.
	@return		Merged word or "" if merge is impossible. *)
let merge w1 w2 =
	let rec make i s =
		if i >= (String.length w1) then s else
		make (i + 1) (s ^ (String.make 1 (join (String.get w1 i) (String.get w2 i)))) in
	let w = make 0 "" in
	if (String.contains w bot)
	|| (count w x) - (count w1 x) >= 2 
	then "" else w


(** Test if a bit matches a given mask.
	@param b	Bit to test.
	@param m	Mask to test.
	@return		True if mask matches the bit. *) 
let matches_bit b m =
	b = m || m = x


(** Test if a word matches a mask.
	@param w	Word to test.
	@param m	Mask to test.
	@return		True if w matches m. *)
let matches w m =
	let rec test i =
		if i >= (String.length w) then true else
		if matches_bit (String.get w i) (String.get m i) then test (i + 1)
		else false in
	test 0


module OrderedTerm = struct
	type t = term_t
	let compare t1 t2 = String.compare t1 t2
end
module TermSet = Set.Make(OrderedTerm)	


(** Compute the prime terms for the given term.
	@param terms	Term to compute primes on.
	@return			Minimal set of primes. *)
let compute_primes terms =

	let rec select i terms =
		if i > (String.length (fst (List.hd terms))) then [] else
		(List.fold_left (fun tl (t, n) -> if n = i then t::tl else tl) [] terms) :: (select (i + 1) terms) in
	
	let make_classes terms =
		select 0 (List.map (fun t -> (t, count t one)) terms) in
	
	let rec count_classes classes =
		match classes with
		| [] -> 0
		| []::t -> count_classes t
		| _::t -> 1 + count_classes t in
	
	let rec combine_b set a bb =
		match bb with
		| [] -> set
		| b::t -> combine_b (TermSet.add (merge a b) set) a t in
	
	let rec combine_a set aa bb =
		match aa with
		| [] -> set
		| a::t -> combine_a (combine_b set a bb) t bb in
	
	let rec combine set cs1 cs2 =
		match (cs1, cs2) with
		| ([], _) -> set
		| (c1::t1, c2::t2) -> combine (combine_a set c1 c2) t1 t2
		| _ -> failwith "qmc.compute_primes/combine" in
	
	let rec add_missing terms set =
		List.fold_left
			(fun set term -> if (TermSet.exists (fun m -> matches term m) set) then set else TermSet.add term set)
			set
			terms in
		
	let rec iter terms =
		let classes = make_classes terms in
		if (count_classes classes) == 1 then terms else
		let set = add_missing terms (TermSet.remove "" (combine TermSet.empty (List.tl classes) classes)) in
		let nterms = TermSet.elements set in
		if terms = nterms then nterms else
		iter nterms in
	
	iter terms


let _ =
	(*let ex = [
		"00";
		"01";
		"10"
	] in*) 
	(*let ex = [
		"001";
		"010";
		"100";
		"011";
		"101";
		"111"
	] in*)
	let ex = [
		"0000";
		"0001";
		"0010";
		"0011";
		"0100";
		"0101";
		"0110";
		"0111";
		"1000";
		"1001";
		"1010";
		"1011";
		"1100";
		"1101";
		"1110"
	] in
	List.iter (Printf.printf "%s\n") (compute_primes ex)

	
 
	