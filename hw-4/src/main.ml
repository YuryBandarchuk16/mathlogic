open Tree;;
open Buffer;;
open Printf;;

module HT = Hashtbl;;

let (ic,oc) = (open_in "input.txt", open_out "output.txt");;
let graph = (HT.create 256: (int, (int) list) HT.t);;
let inv_graph = (HT.create 256: (int, (int) list) HT.t);;
let sum = (HT.create 256: (int * int, int) HT.t);;
let mul = (HT.create 256: (int * int, int) HT.t);;
let imp = (HT.create 256: (int * int, int) HT.t);;

let split stringValue separatorValue = Str.split (Str.regexp separatorValue) stringValue;;

let rec debug_int_list listItems =
  match listItems with
  | [] -> ()
  | firstElement::otherElements -> print_endline (string_of_int firstElement); debug_int_list otherElements
;;

let appendInv whatToAppend neighbours = begin
  let rec helper elements = begin
    match elements with
    | firstElement::otherElements -> begin
      if ((HT.mem inv_graph firstElement) = false) then begin
        HT.add inv_graph firstElement [];
      end;
      let curList = HT.find inv_graph firstElement in
      HT.replace inv_graph firstElement (whatToAppend::curList);
      helper otherElements;
    end
    | [] -> ()
  end in
  helper (whatToAppend::neighbours)
end;;

let rec buildGraph vertexId linesLeft = begin
  if linesLeft > 0 then begin
    let nextLine = input_line ic in
      let neighbours = List.map int_of_string (split nextLine " ") in
        HT.replace graph vertexId neighbours;
        appendInv vertexId neighbours;
        buildGraph (vertexId + 1) (linesLeft - 1);
  end
end;;

let rec getSubtree v visitedMap = begin
  let answer_map = (HT.create 256: (int, int) HT.t) in
  let rec helper neighbours = begin
    match neighbours with
    | firstElement::otherElements -> begin
      helper otherElements;
      if ((HT.mem visitedMap firstElement) = false) then begin
        HT.replace answer_map firstElement 1;
        HT.replace visitedMap firstElement 1;
        let his_answer = getSubtree firstElement visitedMap in
          HT.iter (fun key value -> HT.replace answer_map key 1) his_answer;
      end
    end
    | [] -> ()
  end in
  helper (HT.find graph v);
  HT.replace answer_map v 1;
  answer_map
end;;

let rec getSubtreeForMul v visitedMap = begin
  let answer_map = (HT.create 256: (int, int) HT.t) in
  let rec helper neighbours = begin
    match neighbours with
    | firstElement::otherElements -> begin
      helper otherElements;
      if ((HT.mem visitedMap firstElement) = false) then begin
        HT.replace answer_map firstElement 1;
        HT.replace visitedMap firstElement 1;
        let his_answer = getSubtreeForMul firstElement visitedMap in
          HT.iter (fun key value -> HT.replace answer_map key 1) his_answer;
      end
    end
    | [] -> ()
  end in
  helper (HT.find inv_graph v);
  HT.replace answer_map v 1;
  answer_map
end;;

let get_all_keys h = HT.fold (fun key value now -> key::now) h [];;
let has_all_keys h1 h2 = HT.fold (fun key value now -> if (now = true && (HT.mem h2 key)) then true else false) h1 true;;
let two_h_equal h1 h2 = has_all_keys h1 h2 && has_all_keys h2 h1;;

let dieOnPlus v1 v2 = begin
  fprintf oc "Операция '+' не определена: %d+%d\n" v1 v2;
  close_in ic;
  close_out oc;
  exit 0;
end;;

let dieOnMul v1 v2 = begin
  fprintf oc "Операция '*' не определена: %d*%d\n" v1 v2;
  close_in ic;
  close_out oc;
  exit 0;
end;;

let dieOnDistr v1 v2 v3 = begin
  fprintf oc "Нарушается дистрибутивность: %d*(%d+%d)\n" v1 v2 v3;
  close_in ic;
  close_out oc;
  exit 0;
end;;

let dieOnImp v1 v2 = begin
  fprintf oc "Операция '->' не определена: %d->%d\n" v1 v2;
  close_in ic;
  close_out oc;
  exit 0;
end;;

let dieOnAlgebra v = begin
  fprintf oc "Не булева алгебра: %d+~%d\n" v v;
  close_in ic;
  close_out oc;
  exit 0;
end;;

let getPlus v1 v2 = begin
  if (HT.mem sum (v1, v2)) then HT.find sum (v1, v2) else begin
  let vis1 = (HT.create 256: (int, int) HT.t) in
  let vis2 = (HT.create 256: (int, int) HT.t) in
  let sub1 = getSubtree v1 vis1 in
  let sub2 = getSubtree v2 vis2 in
  let inter_of_subs = (HT.create 256: (int, int) HT.t) in
  HT.iter (fun key value -> if ((HT.mem sub2 key) = true) then (HT.replace inter_of_subs key 1)) sub1;
  let roots = HT.fold (fun key value result -> begin
    if ((List.length result) > 1) then begin
      result
    end else begin
      let tmp_vis = (HT.create 256: (int, int) HT.t) in
      let s = getSubtree key tmp_vis in
      if ((two_h_equal s inter_of_subs) = true) then key::result else result
      end
  end) inter_of_subs [] in
  if ((List.length roots) <> 1) then begin dieOnPlus v1 v2 end else match roots with
  | [] -> dieOnPlus v1 v2;
  | x::xs  -> HT.replace sum (v1, v2) x; x end
end;;


let getMul v1 v2 = begin
  if (HT.mem mul (v1, v2)) then HT.find mul (v1, v2) else begin
  let vis1 = (HT.create 256: (int, int) HT.t) in
  let vis2 = (HT.create 256: (int, int) HT.t) in
  let sub1 = getSubtreeForMul v1 vis1 in
  let sub2 = getSubtreeForMul v2 vis2 in
  let inter_of_subs = (HT.create 256: (int, int) HT.t) in
  HT.iter (fun key value -> if ((HT.mem sub2 key) = true) then (HT.replace inter_of_subs key 1)) sub1;
  let roots = HT.fold (fun key value result -> begin
    if ((List.length result) > 1) then begin
      result
    end else begin
      let tmp_vis = (HT.create 256: (int, int) HT.t) in
      let s = getSubtreeForMul key tmp_vis in
      if ((two_h_equal s inter_of_subs) = true) then key::result else result
      end
  end) inter_of_subs [] in
  if ((List.length roots) <> 1) then begin dieOnMul v1 v2 end else match roots with
  | [] -> dieOnMul v1 v2;
  | x::xs  -> HT.replace mul (v1, v2) x; x end
end;;

let rec initSum v1 v2 all = begin
  if (v1 > all) then begin () end else begin
    let _ = getPlus v1 v2 in
    if (v2 = all) then initSum (v1 + 1) 1 all else initSum v1 (v2 + 1) all
  end
end;;

let rec initMul v1 v2 all = begin
  if (v1 > all) then begin () end else begin
    let _ = getMul v1 v2 in
    if (v2 = all) then initMul (v1 + 1) 1 all else initMul v1 (v2 + 1) all
  end
end;;

let rec checkDistr v1 v2 v3 all = begin
  if (v1 > all) then begin () end else begin
    let ab = getMul v1 v2 in
    let ac = getMul v1 v3 in
    let have = getMul v1 (getPlus v2 v3) in
    let got = getPlus ab ac in
    if got <> have then begin
      dieOnDistr v1 v2 v3;
    end;
    if (v3 < all) then checkDistr v1 v2 (v3 + 1) all
    else if (v3 = all && v2 = all && v1 = all) then ()
    else if (v3 = all && v2 = all) then checkDistr (v1 + 1) 1 1 all
    else if (v3 = all) then checkDistr v1 (v2 + 1) 1 all
    else ()
  end
end

let getImpl v1 v2 = HT.find imp (v1, v2);;

let rec initImpl v1 v2 all = begin
  let rec helper vIndex = begin
    if (vIndex > all) then [] else begin
      let value = getMul vIndex v1 in
      let tmp_vis = (HT.create 256: (int, int) HT.t) in
      let sb = getSubtree value tmp_vis in
      if HT.mem sb v2 then vIndex::(helper (vIndex + 1)) else (helper (vIndex + 1))
    end
  end in
  let rec put_list_to_map l m = begin
    match l with
    | x::xs -> HT.replace m x 1; put_list_to_map xs m
    | [] -> ()
  end in
  let rec find_best l m = begin
    match l with
    | x::xs -> begin
    let tmp_vis = (HT.create 256: (int, int) HT.t) in
    let sb = getSubtree x tmp_vis in
    let rem_result = find_best xs m in
    let inter_of_subs = (HT.create 256: (int, int) HT.t) in
    HT.iter (fun key value -> if ((HT.mem sb key) = true) then (HT.replace inter_of_subs key 1)) m;
    if ((HT.length inter_of_subs) = 1) then x::rem_result else rem_result
    end
    | [] -> []
  end in
  if (v1 > all) then begin () end else begin
    let candidates = helper 1 in
    let map_them = (HT.create 256: (int, int) HT.t) in
    put_list_to_map candidates map_them;
    let best = find_best candidates map_them in
    if ((List.length best) <> 1) then begin
      dieOnImp v1 v2
    end else begin
      let vvv = match best with
      | x::xs -> x
      | _ -> -1 in
      HT.replace imp (v1, v2) vvv;
    end;
    if (v2 = all) then initImpl (v1 + 1) 1 all else initImpl v1 (v2 + 1) all
  end
end;;

let rec getZero curVer all = begin
  if (curVer > all) then [] else begin
  let tmp_vis = (HT.create 256: (int, int) HT.t) in
  let sb = getSubtree curVer tmp_vis in
  if ((HT.length sb) = all) then curVer::(getZero (curVer + 1) all) else getZero (curVer + 1) all
  end
end;;

let rec getOne curVer all = begin
  if (curVer > all) then [] else begin
    let tmp_vis = (HT.create 256: (int, int) HT.t) in
    let sb = getSubtreeForMul curVer tmp_vis in
    if ((HT.length sb) = all) then curVer::(getOne (curVer + 1) all) else getOne (curVer + 1) all
  end;
end;;

let vertexCount = int_of_string (input_line ic);;
buildGraph 1 vertexCount;;

initSum 1 1 vertexCount;;
initMul 1 1 vertexCount;;
checkDistr 1 1 1 vertexCount;;
initImpl 1 1 vertexCount;;

let p_zero = getZero 1 vertexCount;;
let p_one = getOne 1 vertexCount;;

if ((List.length p_zero) <> 1) then exit 100;;

if ((List.length p_one) <> 1) then exit 100;;

let get_first l = match l with
| x::xs -> x
| _ -> -1
;;

let zero = get_first p_zero;;
let one = get_first p_one;;

let rec final_check curVer all = begin
  if (curVer > all) then () else begin
    let neg = getImpl curVer zero in
    let s = getPlus curVer neg in
    if (s <> one) then begin
      dieOnAlgebra curVer;
    end else begin
      final_check (curVer + 1) all;
    end
  end
end;;

final_check 1 vertexCount;;

fprintf oc "Булева алгебра\n";

close_out oc;;
close_in ic;;
