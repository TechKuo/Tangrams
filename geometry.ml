
module Make(F : Numbers.OrderedField) = struct
 
open F

module OFU = Numbers.OrderedFieldUtils(F)

open OFU

module REG = Region.Make(F)

open REG

type point   = number * number
type polygon = point list
type region  = REG.region 


let minkowski_difference_convex obstacle poly =
   let rec get_poly_diff ob poly = 
    let rec gpd_helper (p1,p2) pl = match pl with 
      [] -> []
      |(num1,num2) :: t -> ((num1-p1),(num2-p2)) :: (gpd_helper (p1,p2) t) in
    match poly with 
      [] -> []
      | h :: t -> (gpd_helper h ob)@(get_poly_diff ob t) in
  let poly_diff = get_poly_diff obstacle poly in
  (* Computing Convex Hull using Andrew's monotone chain algorithm *)
  let compare_points (a1,a2) (b1,b2) = 
   if a1 === b1 then begin 
   if a2 < b2 then -1 else if a2 === b2 then 0 else 1 end
   else if a1 < b1 then -1 else 1 in
  let sorted_poly_diff = List.sort compare_points poly_diff in
  let rec delete_dups l = match l with 
    | [] -> [] 
    | (a1,a2) :: [] -> (a1,a2) :: [] 
    | (a1,a2) :: (b1,b2) :: rest -> begin 
      if (a1 === b1) && (a2 === b2) then delete_dups ((b1,b2) :: rest) 
      else (a1,a2) :: delete_dups ((b1,b2) :: rest) end in 
  let sorted_poly_diff_set = delete_dups sorted_poly_diff in
  if (Pervasives.(<=)(List.length sorted_poly_diff_set) 1) 
  then sorted_poly_diff_set else
  let cross (o1,o2) (c1,c2) (t1,t2) =
    ((c1 - o1) * (t2 - o2)) - ((c2 - o2)*(t1 - o1)) in
  let remove_last l = 
    let rl = List.rev l in
    match rl with 
    [] -> failwith "remove_last : empty list"
    | h :: t -> List.rev(t) in
  let rec build_lower lower points c =
    let open Pervasives in
    if c = List.length points then lower else
    let pc = List.nth points c in
    let rec bl_helper l p =
      let len = List.length l in 
      if len >= 2 then begin
      if OFU.(<=)(cross (List.nth l (len-2)) (List.nth l (len-1)) p) F.zero 
      then bl_helper (remove_last l) p else l end 
      else l in
      let fixed_lower = bl_helper lower pc in
      build_lower (fixed_lower @ [pc]) points (c+1) in
  let lower = build_lower [] sorted_poly_diff_set 0 in
  let upper = build_lower [] (List.rev sorted_poly_diff_set) 0 in
  (remove_last lower)@(remove_last upper) 

    
let rec minkowski_difference obstacles poly = match obstacles with
  [] -> REG.create([])
  | h :: t -> begin 
  REG.union (REG.create(minkowski_difference_convex h poly)) 
  (minkowski_difference t poly) end

end
