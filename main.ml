
(* Change NT to whatever number type you want to use. *)

module NT = Numbers.Rationals
module UI = Ui.Make(NT)

let () = UI.main ()

