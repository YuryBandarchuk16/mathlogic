open Tree;;
open Buffer;;
open Printf;;

module MyMap = Map.Make(String);;
module MySet = Set.Make(String);;

let (>>) x f = f x;;

let first_element_of_list l = 
	match l with
	| head::[]   -> ""
	| head::tail -> head
	| [] 		 -> ""
;;

let can_be_proved = MyMap.empty;;
let already_proved = MyMap.empty;;
let list_of_guesses expr = Str.split (Str.regexp ",") expr;;
let string_of_guesses expr = first_element_of_list (Str.split (Str.regexp "|-") expr);; 

let string_of_tree tree = 
  let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" | Comma -> "," | Proof -> "|-" in

  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v ->  add_string buf v
    | Neg t -> add_char buf '!'; s_t t
    | Binop (op,l,r) -> add_char buf '('; (s_t l); add_string buf (s_op op); (s_t r); add_char buf ')'
  in s_t tree;
  contents buf;;

let get_pair_of_ints s = 
	let l = Str.split (Str.regexp ",") s in
	match l with
	| a::b::[]  -> (int_of_string a, int_of_string b)
	| _         -> (0, 0)
;;

let tree_of_string s = s >> Lexing.from_string >> Parser.main Lexer.main;;

let rec save_guesses l index = 
	match l with
	| element::[] -> MyMap.add (string_of_tree (tree_of_string element)) index MyMap.empty
	| element::tail -> MyMap.add (string_of_tree (tree_of_string element)) index (save_guesses tail (index + 1))
	| [] -> MyMap.empty
;;

let (ic, oc) = (open_in "input.txt", open_out "output.txt");;

let remove_blanks = Str.global_replace (Str.regexp " \\|	") "";;

let header = ic >> input_line;;
let map_of_guesses = MyMap.empty;;
let map_of_guesses = save_guesses (list_of_guesses (string_of_guesses header)) 1;;
let get_index_from_map map_of_guesses guess = 
	try 
		MyMap.find guess map_of_guesses
	with Not_found -> -1;;

let get_guess_index guess = get_index_from_map map_of_guesses guess;;

let append_item lst a = lst @ [a];;

let read_file ic = 
	let lines = ref [] in
	try
  		while true; do
  			let kek = remove_blanks (input_line ic) in
    		if kek <> "" then lines := (string_of_tree (tree_of_string kek)) :: !lines
  		done; !lines
	with End_of_file ->
  		close_in ic;
  		List.rev !lines ;;

(*let equal_two t1 t2 id = if ((string_of_tree t1) = (string_of_tree t2)) then id else 0;;
let equal_three t1 t2 t3 id = 
	let st1 = string_of_tree t1 in
	let st2 = string_of_tree t2 in
	let st3 = string_of_tree t3 in
	if (st1 = st2 && st2 = st3) then id else 0;;*)

let rec equal_two_tree t1 t2 =
	match t1 with
	| Binop(op, left, right) -> begin
		match t2 with
		| Binop(op', left', right') -> if (op = op' && (equal_two_tree left left') && (equal_two_tree right right')) then true else false
		| _ -> false
	end
	| Neg t -> begin
		match t2 with
		| Neg t' -> equal_two_tree t t'
		| _ -> false
	end
	| Var v -> begin
		match t2 with
		| Var v' -> if v = v' then true else false
		| _ -> false
	end
;;

let equal_two t1 t2 id = if equal_two_tree t1 t2 then id else 0;;
let equal_three t1 t2 t3 id = if ((equal_two_tree t1 t2) && (equal_two_tree t2 t3)) then id else 0;;

let rec some_in_list lst comparing_function = 
		match lst with
		| [] -> 0
		| x :: [] -> x
		| x :: xs ->
			let v = some_in_list xs comparing_function in
			comparing_function x v
;;

let min_in_list lst = some_in_list lst (fun x y -> if x < y then x else y);;
let max_in_list lst = some_in_list lst (fun x y -> if x > y then x else y);;

let fifth_or_fourth l r res = if equal_two l res 4 = 4 then 4 else equal_two r res 5;;
let six_or_seventh l r1 r2 = if equal_two l r1 6 = 6 then 6 else equal_two l r2 7;;

let match_with_axiom tree =
	let f1 = match tree with
	| Binop(Impl, Binop(Impl, alpha1, gamma1), Binop(Impl, Binop(Impl, beta1, gamma2), Binop(Impl, Binop(Disj, alpha2, beta2), gamma3))) -> min_in_list [equal_three gamma1 gamma2 gamma3 8; equal_two alpha1 alpha2 8; equal_two beta1 beta2 8]
	| _ -> 0 in
	let f2 = match tree with
	| Binop(Impl, Binop(Impl, alpha1, beta1), Binop(Impl, Binop(Impl, alpha2, Neg beta2), Neg alpha3)) -> min_in_list [equal_three alpha1 alpha2 alpha3 9; equal_two beta1 beta2 9;]
	| _ -> 0 in
	let f3 = match tree with
	| Binop(Impl, Binop(Impl, alpha1, beta1), Binop(Impl, Binop(Impl, alpha2, Binop(Impl, beta2, gamma1)), Binop(Impl, alpha3, gamma2))) -> min_in_list [equal_three alpha1 alpha2 alpha3 2; equal_two beta1 beta2 2; equal_two gamma1 gamma2 2;]
	| _ -> 0 in
	let f4 = match tree with
	| Binop(Impl, alpha1, Binop(Impl, beta1, Binop(Conj, alpha2, beta2))) -> min_in_list [equal_two alpha1 alpha2 3; equal_two beta1 beta2 3]
	| _ -> 0 in
	let f5 = match tree with
	| Binop(Impl, Binop(Conj, alpha1, beta), alpha2) -> fifth_or_fourth alpha1 beta alpha2
	| _ -> 0 in
	let f6 = match tree with
	| Binop(Impl, alpha1, Binop(Disj, alpha2, beta)) -> six_or_seventh alpha1 alpha2 beta
	| _ -> 0 in
	let f7 = match tree with
	| Binop(Impl, Neg(Neg alpha1), alpha2) -> equal_two alpha1 alpha2 10
	| _ -> 0 in
	let f8 = match tree with
	| Binop(Impl, alpha1, Binop(Impl, beta, alpha2)) -> equal_two alpha1 alpha2 1
	| _ -> 0 in
	max_in_list [f1; f2; f3; f4; f5; f6; f7; f8]
;;


let print_ans tr s index list_of_proofs already_proved_map oc =
	let s_i = string_of_int index in
	let tree = tr in
	let ss = s in
	let axiom = match_with_axiom tree in
	let position = get_guess_index ss in
	let buf = create 1000 in
	add_char buf '('; add_string buf s_i; add_string buf ") "; add_string buf ss;
	let create_new_map = if MyMap.mem ss already_proved_map then already_proved_map else MyMap.add ss s_i already_proved_map in
	let dump_and_return w n = 
		add_string buf w;
		add_string buf (string_of_int n);
		add_char buf ')';
		(contents buf) >> fprintf oc "%s\n";
		create_new_map  in
	if axiom > 0 then dump_and_return " (Сх. акс. " axiom
	else if position > 0 then dump_and_return " (Предп. " position
	else 
		begin
			let find_match2 l =
				let alpha = try MyMap.find ss l with Not_found -> "" in
				let index_of_alpha = try int_of_string (MyMap.find alpha already_proved_map) with Not_found -> -1 in
				if index_of_alpha > 0 then
					begin
						let buf = create 1000 in
						add_char buf '(';add_string buf alpha;add_string buf "->";add_string buf ss;add_char buf ')';
						let ft = contents buf in
						let i = try int_of_string (MyMap.find ft already_proved_map) with Not_found -> -1 in
						if i > 0 then (i, index_of_alpha) else (0, 0)
					end
				else (0, 0) in
			let mp = find_match2 list_of_proofs in
			match mp with
			| (0, 0) -> add_string buf " (Не доказано)"; (contents buf) >> fprintf oc "%s\n"; create_new_map
			| (a, b) -> add_string buf " (M.P. "; add_string buf (string_of_int a); add_string buf ", "; add_string buf (string_of_int b); add_char buf ')'; (contents buf) >> fprintf oc "%s\n"; create_new_map
		end
;;

(*
(* Check whether tree is axiom or its string representation s_of_t is guess *)
let is_axiom_or_guess tree s_of_t = if (match_with_axiom tree) > 0 then true else if (get_guess_index s_of_t) then true else false;;

(* Stores pair of d_k = d_j -> d_i; stores d_j for d_i *)
let store_implication tree saved_implications_map = 
	match tree with
	| Binop(Impl, left, right) -> MyMap.add right left saved_implications_map
	| _ -> saved_implications_map
;;

(* Check whether tree is equal to alpha *)
let equal_alpha tree alpha = match tree with alpha -> true | _ -> false;;

(* *)
*)

let rec calc_index_map l index = 
	match l with
	| [] -> MyMap.empty
	| head::[] -> MyMap.singleton head index
	| head::tail -> MyMap.add head index (calc_index_map tail (index + 1))
;;

let rec print_list l index list_of_proofs already_proved_map oc index_map = 
	match l with
	| h::[] -> let _ = print_ans (tree_of_string h) h index list_of_proofs already_proved_map oc in close_out oc; ()
	| h::tail -> begin
					let tt = tree_of_string h in
					let new_map = (print_ans tt h index list_of_proofs already_proved_map oc) in
						let new_list = match tt with
						| Binop(Impl, alpha, beta) -> begin
							let s_b = string_of_tree beta in
							let s_a = string_of_tree alpha in
							let prev_alpha = try MyMap.find s_b list_of_proofs with Not_found -> "" in
							let prev_alpha_id = try MyMap.find prev_alpha index_map with Not_found -> 1000000 in
							let cur_alpha_id = try MyMap.find s_a index_map with Not_found -> 1000000 in
							if cur_alpha_id < prev_alpha_id then MyMap.add (s_b) (s_a) list_of_proofs else list_of_proofs
						end
						| _ -> list_of_proofs in
						print_list tail (index + 1) new_list new_map oc index_map
				end
	| _ -> ()
;;

let lines = read_file ic;;
let index_map = calc_index_map lines 1;;
print_list lines 1 MyMap.empty MyMap.empty oc index_map;;

