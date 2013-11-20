
module Make (F : Numbers.OrderedField) : sig

  type point   = F.number * F.number
  type polygon = point list

  (* create_shape is used to initialize the game state.  It is
   * only called before any of the other functions are, and it should only be
   * called with non-overlapping polygons.
   *)
  val create_shape : polygon -> unit

  (* these functions should update the state of the game in
   * response to the corresponding events.  They will be called
   * by the ui
   *)
  val click   : point -> unit
  val move_to : point -> unit
  val unclick : unit  -> unit

  (* these functions are called by the ui to figure out what to draw.
   * the extra_points and extra_edges functions are for debugging: the ui will
   * draw any extra points or lines returned by these functions
   *)
  val obstacles    : unit -> polygon list
  val selection    : unit -> polygon option
  val extra_points : unit -> point list
  val extra_lines  : unit -> (point * point) list
end

