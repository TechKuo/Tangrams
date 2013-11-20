
module Make (F : Numbers.OrderedField) = struct
open F

module REG = Region.Make(F)
open REG

module OFU = Numbers.OrderedFieldUtils(F)
open OFU

module GEOM = Geometry.Make(F)
open GEOM

type point   = F.number * F.number
type polygon = point list

let shapes : polygon list ref = ref []
let clicked : polygon option ref = ref None
let orig_point : point ref = ref (F.zero,F.zero)
let md_region : region ref = ref (create [])

let create_shape p =
  shapes := p :: !shapes

let extract poly_op = match poly_op with
  None -> [] 
  | Some(poly) -> poly

let (@) xs ys = List.rev_append (List.rev xs) ys

let click p = 
  let shapes_old = !shapes in
  let pred poly = (REG.contains p (REG.create poly)) in
  let tup = List.partition pred shapes_old in
  let selected = List.flatten (fst tup) in
  let rec shift (p1,p2) poly = match poly with
    [] -> []
    | (x1,y1) :: t -> [(x1-p1,y1-p2)]@(shift (p1,p2) t) in
  let shifted_clicked = shift p selected in
  let md = GEOM.minkowski_difference !shapes shifted_clicked in
  md_region := md;
  clicked := Some(selected); 
  orig_point := p;
  shapes := snd tup

let move_to p  = 
  let poly = extract(!clicked) in
  let move orig dest = 
     let vector (x1,y1) (x2,y2) = (x2-x1,y2-y1) in
     let v = vector orig dest in
     List.rev(List.fold_left(fun a (x1,y1) -> begin
     (x1+(fst v),y1+(snd v)) :: a end) [] poly) in
  if (REG.contains p (!md_region)) then 
  let closest = find_closest (!md_region) p in
  clicked := Some(move (!orig_point) (closest));
  orig_point := closest
   
let unclick () = 
  let cpoly = !clicked in
  let new_shapes = (!shapes)@([(extract cpoly)]) in
  shapes := new_shapes;
  clicked := None
  
let obstacles () = !shapes

let selection () = !clicked

let extra_points () = []

let extra_lines ()  = REG.edges !md_region

end


