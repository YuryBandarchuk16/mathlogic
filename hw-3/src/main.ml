open Tree;;
open Buffer;;
open Printf;;
open Proofs;;

let (ic,oc) = (open_in "input.txt", open_out "output.txt");;
let map_variable_name_to_index = (HT.create 256: (string, int) HT.t);;
let map_index_to_variable_name = (HT.create 256: (int, string) HT.t);;
let map_mask_to_proof = (HT.create 256: (int, (string) list) HT.t);;

(* UTILS *)

let print_that_expression_is_lie bitMask =
  fprintf oc "Высказывание ложно при ";
  let bool_to_russian_string b = if b = true then "И" else "Л" in
  let matchedVariablesWithValues = HT.fold (fun varName varIndex accumulator -> (varName ^ "=" ^ (bool_to_russian_string bitMask.(varIndex))) :: accumulator) map_variable_name_to_index [] in
  let resultString = String.concat ", " matchedVariablesWithValues in
  fprintf oc "%s\n" resultString
;;

let get_variable_index_by_name variableName = HT.find map_variable_name_to_index variableName;;
let get_variable_name_by_index variableIndex = HT.find map_index_to_variable_name variableIndex;;

let two_element_list_to_pair listItems =
  match listItems with
  | firstElement::[] -> ("", firstElement)
  | firstElement::secondElement::[] -> (firstElement, secondElement)
  | _ -> ("", "")
;;

let rec print_tree_list listItems =
  match listItems with
  | [] -> ()
  | firstElement::otherElements -> fprintf oc "%s\n" (string_of_tree firstElement); print_tree_list otherElements
;;

let rec print_string_list listItems =
  match listItems with
  | [] -> ()
  | firstElement::otherElements -> fprintf oc "%s\n" firstElement; print_string_list otherElements
;;

let rec string_list_to_tree_list listItems =
  match listItems with
  | [] -> []
  | firstElement::otherElements -> (tree_of_string firstElement) :: (string_list_to_tree_list otherElements)
;;

let splitInput s =
  let (guesses, main_item) = two_element_list_to_pair (split s "|=") in
  ((string_list_to_tree_list (split guesses ",")), tree_of_string main_item)
;;

let rec move_list_right listItems t =
  match listItems with
  | [] -> t
  | firstElement::otherElements -> Binop(Impl, firstElement, (move_list_right otherElements t))
;;

let rec append_list_to_front listToAppend lst =
  match listToAppend with
  | [] -> lst
  | firstElement::otherElements -> firstElement::(append_list_to_front otherElements lst)
;;

let rec extract_variables tree =
  match tree with
  | Binop(op, left, right) -> (append_list_to_front (extract_variables left) (extract_variables right))
  | Neg expr -> (extract_variables expr)
  | Var v -> v::[]
;;

let rec fill_variables_map varsList =
  match varsList with
  | [] -> ()
  | firstElement::otherElements -> begin
    if ((HT.mem map_variable_name_to_index firstElement) = false) then begin
        let id = (HT.length map_variable_name_to_index) in
        HT.add map_variable_name_to_index firstElement id;
        HT.add map_index_to_variable_name id firstElement;
    end;
    fill_variables_map otherElements
  end
;;
(* UTILS *)


(* EVALUATION *)

let bitMask = Array.make 20 false;;

let evalOp op left right =
	match op with
	| Impl -> if (left = true && right = false) then false else true
	| Conj -> if (left = true && right = true) then true else false
	| Disj -> if (left = true || right == true) then true else false
;;

let rec evaluate expressionTree =
  match expressionTree with
  | Binop(op, left, right) -> (evalOp op (evaluate left) (evaluate right))
  | Neg expression -> (not (evaluate expression))
  | Var varName -> (bitMask.(get_variable_index_by_name varName))
;;

let rec findFalse varsCount index expression =
  if (index = varsCount) then begin
    if (evaluate expression) = false then begin
      print_that_expression_is_lie bitMask;
      close_in ic;
      close_out oc;
      exit 0;
    end
  end else begin
    bitMask.(index) <- false;
    findFalse varsCount (index + 1) expression;
    bitMask.(index) <- true;
    findFalse varsCount (index + 1) expression;
  end
;;

let rec bitMask_array_to_int index size power_of_two bitMask =
  if (index = size) then 0 else begin
    if bitMask.(index) then power_of_two + (bitMask_array_to_int (index + 1) size (power_of_two * 2) bitMask) else (bitMask_array_to_int (index + 1) size (power_of_two * 2) bitMask)
  end
;;

let rec int_to_bitMask_array intValue index size bitMask =
  if (index < size) then begin
    let rem = (intValue mod 2) in
    if rem = 0 then bitMask.(index) <- false else bitMask.(index) <- true;
    int_to_bitMask_array (intValue / 2) (index + 1) size bitMask
  end else ()
;;

(* EVALUATION *)

let input_line = remove_blanks (ic >> input_line);;
let (guesses_trees, main_tree) = splitInput input_line;;

(* all_moved_right -- это выражение, полученное переносом всего слева от турникета в правую сторону *)
(* print_endline (string_of_tree all_moved_right);; *)
let all_moved_right = move_list_right guesses_trees main_tree;;
let all_variables = extract_variables all_moved_right;;
fill_variables_map all_variables;;

let varsCount = HT.length map_variable_name_to_index;;

findFalse varsCount 0 all_moved_right;;

let rec bitMask_array_to_tree_list index size =
  if (index = size) then [] else begin
      let value = bitMask.(index) in
      let t = match value with
              | b when (b = true)  -> (Var (get_variable_name_by_index index))
              | b when (b = false) -> (Neg (Var (get_variable_name_by_index index)))
              | _ -> Var "" in
      t::(bitMask_array_to_tree_list (index + 1) size)
  end
;;

let rec bitMask_array_to_string_list index size =
  if (index = size) then [] else begin
      let value = bitMask.(index) in
      let t = match value with
              | b when (b = true)  -> (get_variable_name_by_index index)
              | b when (b = false) -> ("(!" ^ (get_variable_name_by_index index) ^ ")")
              | _ -> "" in
      t::(bitMask_array_to_string_list (index + 1) size)
  end
;;

let get_variable_tree_by_bit_index index =
  let value = bitMask.(index) in
  let t = match value with
      | b when (b = true)  -> (Var (get_variable_name_by_index index))
      | b when (b = false) -> (Neg (Var (get_variable_name_by_index index)))
      | _ -> Var "" in
  t
;;

let rec makeProof expression =
  let helper e = if (evaluate e) then e else (Neg e) in
  let binopSolver left right = begin
    let leftProof  = makeProof (helper left) in
    let rightProof = makeProof (helper right) in
    let partialProof = List.rev (split (getProof (helper left) (helper right) expression) "\n") in
    let fullProof = append_list_to_front partialProof (append_list_to_front leftProof rightProof) in
    fullProof
  end in
  match expression with
  | Binop(op, left, right) -> binopSolver left right
  | Neg(Binop(op, left, right)) -> binopSolver left right
  | Var v -> [v]
  | Neg (Var v) -> [("(!" ^ v ^ ")")]
  | Neg (Neg e) -> begin
    let proofOfE = makeProof e in
    let listOfBigString = List.rev (split (getProofSingle e expression) "\n") in
    let full_proof_list = append_list_to_front listOfBigString proofOfE in
    full_proof_list
  end
;;

let getFullExcludedThird e =
  let firstItem   = Binop(Impl, e, Binop(Disj, e, (Neg e))) in
  let secondItem  = Binop(Impl, (Neg e), Binop(Disj, e, (Neg e))) in
  let thirdItem   = split (getContraposition e (Binop(Disj, e, (Neg e)))) "\n" in
  let fourthItem  = split (getContraposition (Neg e) (Binop(Disj, e, (Neg e)))) "\n" in
  let tmp = Binop(Disj, e, (Neg e)) in
  let fifthItem   = Binop(Impl, (Neg tmp), (Neg e)) in
  let sixItem     = Binop(Impl, (Neg tmp), (Neg (Neg e))) in
  let seventhItem = split (getProofExcluded e) "\n" in
  let part = append_list_to_front [(string_of_tree fifthItem); (string_of_tree sixItem)] seventhItem in
  let part2 = append_list_to_front fourthItem part in
  let part3 = append_list_to_front thirdItem part2 in
  let part4 = append_list_to_front [(string_of_tree firstItem); (string_of_tree secondItem)] part3 in
  part4
;;

let rec generateProofs index size =
  if (index < size) then begin
    bitMask.(index) <- false;
    let (proofWithNotAlpha, _) = generateProofs (index + 1) size in
    bitMask.(index) <- true;
    let (proofWithAlpha, beta) = generateProofs (index + 1) size in
    let currentVariablesList = bitMask_array_to_string_list 0 index in
    let alpha = get_variable_tree_by_bit_index index in
    let proofWithAlphaAfterDeduction = applyHardDeduction currentVariablesList alpha beta proofWithAlpha in
    let proofWithNotAlphaAfterDeduction = applyHardDeduction currentVariablesList (Neg alpha) beta proofWithNotAlpha in
    let proofList = append_list_to_front proofWithAlphaAfterDeduction proofWithNotAlphaAfterDeduction in
    let excludedAlphaProofList = getFullExcludedThird alpha in
    let exclusion = split (getProofExclusion alpha beta) "\n" in
    let finalProofListUpdates = append_list_to_front excludedAlphaProofList exclusion in
    let resultProofList = append_list_to_front proofList finalProofListUpdates in
    (resultProofList, beta)
  end else if (index = size) then begin
    let maskIntValue = bitMask_array_to_int 0 size 1 bitMask in
    let guessesList  = bitMask_array_to_tree_list 0 size in
    let proofList    = List.rev (makeProof all_moved_right) in
    (proofList, all_moved_right)
  end else ([], Var "")
;;

let rec cutSomePrefix prefixSize tree =
  if prefixSize <= 0 then ()
  else match tree with
    | Binop(Impl, a, b) -> fprintf oc "%s\n" (string_of_tree b); cutSomePrefix (prefixSize - 1) b
    | _ -> print_endline "Something went wrong :("; exit 228
;;

let (proofsList, finalExpression) = generateProofs 0 varsCount;;
let amountToCut = List.length guesses_trees;;
fprintf oc "%s\n" (replace input_line "=" "-");;
print_string_list proofsList;;
print_tree_list guesses_trees;
cutSomePrefix amountToCut all_moved_right;;

close_out oc;;
close_in ic;;
