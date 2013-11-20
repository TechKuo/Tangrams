
#use "region.ml";;
module F  = Numbers.Rationals
module FU = Numbers.OrderedFieldUtils(F)
module R  = Make (F)

open F
open FU
open R

#install_printer format;;

let mtl map = PointMap.fold (fun k v acc -> (k,v)::acc) map []
let contain_to_str con =
  match con with
    | Boundary -> "Boundary"
    | Inside -> "Inside"
    | Outside -> "Outside"

let zed  = zero
let two  = one + one
let half = one / two

let p1 = zed, zed
let p2 = one, zed
let p3 = two, two
let p4 = zed, one

let q1 = one,  one
let q2 = zed, -one
let q3 = one, -one
let q4 = two,  one

let r1 =  half,  half
let r2 = -half,  half
let r3 = -half, -half
let r4 =  half, -half

(* p and q intersect at i1 and i2
 * q and r intersect at i1 and i3
 * p and r intersect at i1 and i4
 *)
let i1 = half, zero
let i2 = one  + half, one
let i3 = half * half, -half
let i4 = zero, half

(* the regions *)
let l1 = [p1; p2; p3; p4]
let l2 = [q1; q2; q3; q4]
let l3 = [r1; r2; r3; r4]
let p = create l1
let q = create l2
let r = create l3

(* these are the expected edges for the region p *)
let e21 = {target = p1; left_in = false; right_in = true}
let e32 = {target = p2; left_in = false; right_in = true}
let e34 = {target = p4; left_in = true;  right_in = false}
let e41 = {target = p1; left_in = true;  right_in = false}

(* these are for comparison testing *)
let edge p = {target = p; left_in = false; right_in = false}
let e'1 = edge (-one,zed)
let e'2 = edge (zero,half)



(* here is the expected output from p union q *)
let pqdata = [
  q2, [];
  p1, [];
  p4, [{target=p1; right_in=false; left_in=true}];
  i1, [{target=p1; right_in=true;  left_in=false};
       {target=q2; right_in=false; left_in=true}];
  q3, [{target=q2; right_in=true;  left_in=false}];
  i2, [];
  p3, [{target=p4; right_in=false; left_in=true};
       {target=i2; right_in=true;  left_in=false}];
  q4, [{target=i2; right_in=false; left_in=true};
       {target=q3; right_in=true;  left_in=false}];
]

(* here is the expected output from p union q union r *)
let pqrdata = [
  r3, [];
  r2, [{target=r3; right_in=false; left_in=true}];
  q2, [];
  i4, [{target=r2; right_in=false; left_in=true}];
  p4, [{target=i4; right_in=false; left_in=true}];
  i3, [{target=r3; right_in=true;  left_in=true};
       {target=q2; right_in=false; left_in=true}];
  i1, [];
  q3, [{target=q2; right_in=true;  left_in=false}];
  i2, [];
  p3, [{target=p4; right_in=false; left_in=true};
       {target=i2; right_in=true;  left_in=false}];
  q4, [{target=i2; right_in=false; left_in=true};
       {target=q3; right_in=true;  left_in=false}];
]

let pqregion = List.fold_left (fun acc (k,v) -> PointMap.add k v acc) PointMap.empty pqdata 
let pqrregion = List.fold_left (fun acc (k,v) -> PointMap.add k v acc) PointMap.empty pqrdata 

let pq = union p q;;

let pair_eq eq (x1,y1) (x2,y2) = eq x1 x2 && eq y1 y2


let test_adj_pairs = List.for_all2 (pair_eq (pair_eq (===)))
                                   (adjacent_pairs l1)
                                   [(p1, p2); (p2, p3); (p3, p4); (p4, p1)]

let test_compare_1 = compare_points p1 p2 = Lt
let test_compare_2 = compare_points p1 p1 = Eq
let test_compare_3 = compare_points p2 p1 = Gt
let test_compare_4 = compare_points p1 p4 = Lt
let test_compare_5 = compare_points p4 p1 = Gt


let test_locate_q_p1 = locate p1       q = Outside
let test_locate_q_p2 = locate p2       q = Inside
let test_locate_q_p3 = locate p3       q = Outside
let test_locate_q_p4 = locate p4       q = Outside
let test_locate_q_q1 = locate q1       q = Boundary
let test_locate_q_q2 = locate q2       q = Boundary
let test_locate_q_q3 = locate q3       q = Boundary
let test_locate_q_q4 = locate q4       q = Boundary
let test_locate_q_r1 = locate r1       q = Outside
let test_locate_q_r2 = locate r2       q = Outside
let test_locate_q_r3 = locate r3       q = Outside
let test_locate_q_r4 = locate r4       q = Inside

let test_locate_p_p1 = locate p1       p = Boundary
let test_locate_p_p2 = locate p2       p = Boundary
let test_locate_p_p3 = locate p3       p = Boundary
let test_locate_p_p4 = locate p4       p = Boundary
let test_locate_p_q1 = locate q1       p = Inside
let test_locate_p_q2 = locate q2       p = Outside
let test_locate_p_q3 = locate q3       p = Outside
let test_locate_p_q4 = locate q4       p = Outside
let test_locate_p_r1 = locate r1       p = Inside
let test_locate_p_r2 = locate r2       p = Outside
let test_locate_p_r3 = locate r3       p = Outside
let test_locate_p_r4 = locate r4       p = Outside

let test_locate_r_p1 = locate p1       r = Inside
let test_locate_r_p2 = locate p2       r = Outside
let test_locate_r_p3 = locate p3       r = Outside
let test_locate_r_p4 = locate p4       r = Outside
let test_locate_r_q1 = locate q1       r = Outside
let test_locate_r_q2 = locate q2       r = Outside
let test_locate_r_q3 = locate q3       r = Outside
let test_locate_r_q4 = locate q4       r = Outside
let test_locate_r_r1 = locate r1       r = Boundary
let test_locate_r_r2 = locate r2       r = Boundary
let test_locate_r_r3 = locate r3       r = Boundary
let test_locate_r_r4 = locate r4       r = Boundary

let test_locate_2 = locate (two, zed)  p = Outside
let test_locate_3 = locate (half, zed) p = Boundary

let test_compare_around_1 = compare_slopes_from p3 p2 p4 = Gt
let test_compare_around_2 = compare_slopes_from p3 p4 p2 = Lt
let test_compare_around_3 = compare_slopes_from p2 p1 (-one,zero) = Eq
let test_compare_around_4 = compare_slopes_from p4 p1 (zero,half) = Eq
let test_compare_around_5 = compare_slopes_from p4 p1 (-one,zero) = Gt
let test_compare_around_6 = compare_slopes_from r1 i4 i1 = Lt

let test_find_closest_pqr_1 = pair_eq ( === ) (find_closest pqrregion r3) r3 
let test_find_closest_pqr_2 = pair_eq ( === ) (find_closest pqrregion r2) r2
let test_find_closest_pqr_3 = pair_eq ( === ) (find_closest pqrregion q2) q2 
let test_find_closest_pqr_4 = pair_eq ( === ) (find_closest pqrregion i4) i4 
let test_find_closest_pqr_5 = pair_eq ( === ) (find_closest pqrregion i1) i1 
let test_find_closest_pqr_6 = pair_eq ( === ) (find_closest pqrregion p4) p4 
let test_find_closest_pqr_7 = pair_eq ( === ) (find_closest pqrregion i3) i3 
let test_find_closest_pqr_8 = pair_eq ( === ) (find_closest pqrregion q3) q3 
let test_find_closest_pqr_9 = pair_eq ( === ) (find_closest pqrregion p3) p3 
let test_find_closest_pqr_10 = pair_eq ( === ) (find_closest pqrregion i2) i2 
let test_find_closest_pqr_11 = pair_eq ( === ) (find_closest pqrregion q4) q4  

let test_find_closest_pq_1 = pair_eq ( === ) (find_closest pqregion p1) p1
let test_find_closest_pq_2 = pair_eq ( === ) (find_closest pqregion q2) q2 
let test_find_closest_pq_3 = pair_eq ( === ) (find_closest pqregion i1) i1 
let test_find_closest_pq_4 = pair_eq ( === ) (find_closest pqregion p4) p4 
let test_find_closest_pq_5 = pair_eq ( === ) (find_closest pqregion q3) q3 
let test_find_closest_pq_6 = pair_eq ( === ) (find_closest pqregion p3) p3 
let test_find_closest_pq_7 = pair_eq ( === ) (find_closest pqregion i2) i2 
let test_find_closest_pq_8 = pair_eq ( === ) (find_closest pqregion q4) q4  

let test_binary_search =
  let open Pervasives in
  binary_search (fun x -> if 2 < x then Lt else if 2 = x then Eq else Gt)
                [| 0; 1; 2; 2; 2; 3; 3; 4; 5 |]
  = (2,5)

let test_compare_edge_to_point_1 = compare_edge_to_point r4 (p2, edge p1) = Gt
let test_compare_edge_to_point_2 = compare_edge_to_point r1 (p2, edge p1) = Lt
let test_compare_edge_to_point_3 = compare_edge_to_point i1 (p2, edge p1) = Eq

let test_edges = binary_search (compare_edge_to_point i1)
                               [| (p3, edge p4);
                                  (r1, edge i1);
                                  (p2, edge p1);
                                  (q3, edge q2) |]
               = (1,3)


let test_segment_ix = segment_intersect (i1, edge q2) (r4, edge r3)

let dq = r2 -! r4
let dp = q2 -! i1
let d1 = i1 -! r4

(*
** vim: ts=2 sw=2 et ai
*)
