module Make (F : Numbers.OrderedField) : sig

  type point   = F.number * F.number
  type polygon = point list
  type region  = Region.Make(F).region

  val minkowski_difference_convex : polygon      -> polygon -> polygon
  val minkowski_difference        : polygon list -> polygon -> region
end

