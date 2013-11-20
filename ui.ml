
module Make (F : Numbers.NiceField) = struct

module FU   = Numbers.OrderedFieldUtils(F)
module Game = Game.Make(F)

open F
open FU

(** coordinate transformations ************************************************)

let n_of_i = number_of_int
let f_of_n = float_of_number

(* origin and scaling factor *)
let _o_x   = ref (n_of_i 400)
let _o_y   = ref (n_of_i 300)
let _scale = ref (inv (n_of_i 75))

let p_of_ii x y =
  !_scale * ((n_of_i x) - !_o_x),
  !_scale * (!_o_y - (n_of_i y))

let ff_of_p (x,y) =
  float_of_number x,
  float_of_number y

(** Glut callbacks ************************************************************)

let init () =
  GlClear.color (1.0, 1.0, 1.0);
  Gl.enable `line_smooth;
  Gl.enable `blend;

  GlDraw.point_size 10.0;

  GlFunc.blend_func `src_alpha `one_minus_src_alpha;;


let reshape ~w ~h =
  let two   = n_of_i 2 in
  let eight = n_of_i 8 in
  let wn    = n_of_i w in
  let hn    = n_of_i h in

  _o_x   := wn / two;
  _o_y   := hn / two;
  _scale := eight / (min wn hn);

  let xsc = inv (!_o_x * !_scale) in
  let ysc = inv (!_o_y * !_scale) in

  GlMat.mode `projection;
  GlMat.load_identity ();
  GlMat.scale ~x:(f_of_n xsc) ~y:(f_of_n ysc) ();

  GlDraw.viewport 0 0 w h;
  ()

(*
draw the given polygon, filled with color (r,g,b) and outlined
with color (outline_r, outline_g, outline_b)
*)
let draw_shape ~r ~g ~b
	       ?(outline_r = 0.06) ?(outline_g = 0.0) ?(outline_b = 0.32)
	       shape =
  GlDraw.color (r,g,b) ~alpha:1.0;
  GlDraw.polygon_mode `both `fill;
  GlDraw.begins `polygon;
  List.iter GlDraw.vertex2 (List.map ff_of_p shape);
  GlDraw.ends ();

  GlDraw.color (outline_r, outline_g, outline_b) ~alpha:1.0;
  GlDraw.polygon_mode `both `line;
  GlDraw.line_width 2.0;
  GlDraw.begins `polygon;
  List.iter GlDraw.vertex2 (List.map ff_of_p shape);
  GlDraw.ends ();
  ()

let draw_shapes () =
  GlClear.clear [ `color ];

  (* draw obstacles *)
  List.iter (draw_shape ~r:0.13 ~g:0.00 ~b:0.66)
            (Game.obstacles ());

  (* draw selection *)
  begin match Game.selection () with
    | Some sel -> draw_shape ~r:0.26 ~g:0.00 ~b:1.00 sel
    | None     -> ()
  end;

  (* draw extra lines *)
  GlDraw.color (0.00,0.00,0.00) ~alpha:1.0;
  GlDraw.begins `lines;
  List.iter begin fun (p1,p2) ->
    GlDraw.vertex2 (ff_of_p p1);
    GlDraw.vertex2 (ff_of_p p2)
  end (Game.extra_lines ());
  GlDraw.ends ();

  (* draw extra points *)
  GlDraw.color (1.00,0.00,0.00) ~alpha:1.0;
  GlDraw.begins `points;
  List.iter GlDraw.vertex2
            (List.map ff_of_p (Game.extra_points ()));
  GlDraw.ends ();
  ()

let render () =
  draw_shapes ();
  Glut.swapBuffers ()

let mouse ~button ~state ~x ~y = match button, state with
  | Glut.LEFT_BUTTON, Glut.DOWN -> Game.click   (p_of_ii x y)
  | _,                Glut.UP   -> Game.unclick ()
  | _ -> ()

let motion ~x ~y =
  Game.move_to (p_of_ii x y);
  ()

let keyboard ~key ~x ~y =
  Format.eprintf "key: %i %i %i\n%!" key x y

(** initial tangrams **********************************************************)

let nn_of_ii (x,y) = n_of_i x, n_of_i y

let shapes = List.map (List.map nn_of_ii) [
  [0,2;0,1;0,0;1,0;2,0;1,1]; (* big triangle    *)
  [0,2;1,1;2,0;2,1;2,2;1,2]; (* big triangle    *)
  [0,2;0,1;0,0;1,1];         (* medium triangle *)
  [1,1;0,1;1,0];             (* small triangle  *)
  [0,0;1,0;2,1;1,1];         (* parallelogram   *)
  [1,1;0,0;1,0];             (* small triangle  *)
  [0,1;0,0;1,0;1,1];         (* square          *)
]

let offsets = [
  (n_of_i 1 ) / (n_of_i 2), (n_of_i 1) / (n_of_i 2);
  (n_of_i 1 ) / (n_of_i 2), (n_of_i 2) / (n_of_i 2);
  (n_of_i 11) / (n_of_i 4), (n_of_i 3) / (n_of_i 4);
  (n_of_i 3 ) / (n_of_i 1), (n_of_i 2) / (n_of_i 1);
  (n_of_i 13) / (n_of_i 4), (n_of_i 3) / (n_of_i 4);
  (n_of_i 9 ) / (n_of_i 2), (n_of_i 1) / (n_of_i 2);
  (n_of_i 17) / (n_of_i 4), (n_of_i 8) / (n_of_i 4);
];;

let vplus (x1,y1) (x2,y2) = (x1 + x2, y1 + y2)

let shapes = List.map2 (fun p o -> List.map (vplus o) p) (shapes) offsets
let shapes = List.map (List.map (fun (x,y) -> x - (n_of_i 3), y - (n_of_i 2))) shapes

let () = List.iter Game.create_shape shapes

(** main **********************************************************************)

let main () =
  ignore(Glut.init Sys.argv);
  Glut.initWindowSize ~w:800 ~h:600;
  Glut.initDisplayMode ~double_buffer:true ();
  ignore(Glut.createWindow ~title:"3110 Tangrams");

  Glut.displayFunc ~cb:render;
  Glut.reshapeFunc ~cb:reshape;
  Glut.idleFunc    ~cb:(Some Glut.postRedisplay);

  Glut.mouseFunc   ~cb:mouse;
  Glut.motionFunc  ~cb:motion;
  Glut.keyboardFunc ~cb:keyboard;

  init ();
  Glut.mainLoop ();;

end
