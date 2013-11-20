
let render () =
  GlClear.clear [`color];
  Glut.swapBuffers ();
  ()

let () =
  ignore(Glut.init Sys.argv);
  Glut.initWindowSize ~w:400 ~h:300;
  Glut.initDisplayMode ~double_buffer:true ();
  ignore(Glut.createWindow ~title:"3110 OpenGL Test");
  GlClear.color (1.0, 1.0, 1.0);
  Glut.displayFunc ~cb:render;
  Glut.mainLoop ();
  ()

