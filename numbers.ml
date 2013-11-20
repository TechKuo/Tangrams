(** Some abstract algebra for you *********************************************)

module type Quotient = sig
  type number

  val ( === )  : number -> number -> bool
end

module QuotientProperties (Q : Quotient) = struct
  open Q
  let symmetric  a b   = if a === b then b === a else true;;
  let transitive a b c = if a === b &&   b === c then a === c else true;;
  let reflexive  a     = a === a;;
end

module type Group = sig
  include Quotient

  val zero   : number
  val ( +  ) : number -> number -> number
  val ( ~- ) : number -> number
end

module GroupProperties (G : Group) = struct
  open G

  include QuotientProperties (G)
  let commutative a b   = a + b === b + a
  let associative a b c = a + (b + c) === (a + b) + c
  let identity    a     = a + zero === a
  let inverses    a     = a + (~- a) === zero
end

module type Ring = sig
  include Group

  val one   : number
  val ( * ) : number -> number -> number
end

module RingProperties (R : Ring) = struct
  open R

  include GroupProperties (R)
  let times_associative  a b c = (a * b) * c === a * (b * c)
  let times_distributive a b c = a * (b + c) === a * b + a * c
  let times_identity     a     = a * one === a
  let times_commutative  a b   = a * b === b * a
end

module type Field = sig
  include Ring

  (* return the multiplicative inverse of the argument.  Behavior is undefined
   * if the argument is zero.
   *)
  val inv : number -> number
end

module FieldProperties (F : Field) = struct
  open F
  
  include RingProperties (F)
  let times_inverse a = if a === zero then true else a * inv a === one
end

module type OrderedRing = sig
  include Ring

  val is_non_neg : number -> bool
end

module OrderedRingProperties (R : OrderedRing) = struct
  open R

  let minus_one_negative     = not (is_non_neg ~-one)
  let squares_non_negative a = is_non_neg (a*a)

  let non_negative_times a b = if   is_non_neg a && is_non_neg b
                               then is_non_neg (a*b) else true

  let non_negative_plus  a b = if   is_non_neg a && is_non_neg b
                               then is_non_neg (a+b) else true
end

module type OrderedField = sig
  include Field
  include OrderedRing with type number := number
end

module OrderedFieldProperties (F : OrderedField) = struct
  include FieldProperties(F)
  include OrderedRingProperties(F)
end

(******************************************************************************)

module type NiceRing = sig
  include OrderedRing

  val float_of_number : number -> float
  val format          : Format.formatter -> number -> unit
end

module type NiceField = sig
  include OrderedField
  include (NiceRing with type number := number)
end

(** Exercise 1 ****************************************************************)

module type IntsType = NiceRing
  module Ints : IntsType = struct
  type number = int
  let ( === ) = fun x y -> x = y
  let zero = 0
  let ( + ) = fun x y -> x + y
  let ( ~- ) = fun x -> ~-x
  let one = 1
  let ( * ) = fun x y -> x * y
  let is_non_neg = fun x -> abs x === x
  let float_of_number = fun x -> float x
  let format = fun formatter x -> Format.pp_print_int formatter x
end

module type IntegersType = sig
  include NiceRing
  val to_big_int : number -> Big_int.big_int
  val to_number : Big_int.big_int -> number
end
  module Integers : IntegersType = struct
  open Big_int
  type number = Big_int.big_int
  let ( === ) = fun x y -> eq_big_int x y
  let zero = zero_big_int
  let ( + ) = fun x y -> add_big_int x y
  let ( ~- ) = fun x -> minus_big_int x
  let one = unit_big_int
  let ( * ) = fun x y -> mult_big_int x y 
  let is_non_neg = fun x -> (abs_big_int x) === x
  let float_of_number = fun x -> float_of_big_int x
  let format = fun formatter x -> begin
    Format.pp_print_string formatter (string_of_big_int x) end
  let to_big_int = fun x -> x
  let to_number = fun x -> x
  end

module type FloatsType = NiceField
  module Floats : FloatsType  = struct
  type number = float
  let ( === ) = fun x y -> (abs_float (x -. y)) < (10. ** (-6.))
  let zero = 0.
  let ( + ) = fun x y -> x +. y
  let ( ~- ) = fun x -> ~-. x
  let one = 1.
  let ( * ) = fun x y -> x *. y
  let inv = fun x -> 1. /. x
  let is_non_neg = fun x -> (abs_float x) === x
  let float_of_number = fun x -> x
  let format = fun formatter x -> Format.pp_print_float formatter x
end

module type Root23Type = sig
  include NiceRing
  val sqrt2 : number
  val sqrt3 : number
  val sqrt6 : number
end
  module Root23 : Root23Type = struct
  type number = (int * int * int * int)
  let sqrt2 = (0,1,0,0)
  let sqrt3 = (0,0,1,0)
  let sqrt6 = (0,0,0,1)
  let ( === ) = fun (x1,x2,x3,x4) (y1,y2,y3,y4) -> begin
    (x1 = y1) && (x2 = y2) && (x3 = y3) && (x4 = y4) end
  let zero = (0,0,0,0)
  let ( + ) = fun (x1,x2,x3,x4) (y1,y2,y3,y4) -> begin
    (x1+y1,x2+y2,x3+y3,x4+y4) end
  let ( ~- ) = fun (x1,x2,x3,x4) -> (~- x1, ~- x2, ~- x3, ~- x4)
  let one = (1,0,0,0)
  let ( * ) = fun (x1,x2,x3,x4) (y1,y2,y3,y4) -> begin
    let open Pervasives in 
    ( (x1*y1+2*x2*y2+3*x3*y3+6*x4*y4),(x1*y2+x2*y1+3*x3*y4+3*x4*y3),
     (x1*y3+2*x2*y4+x3*y1+2*x4*y2),(x1*y4+x2*y3+x3*y2+x4*y1) ) end
  let is_non_neg = fun (x1,x2,x3,x4) -> begin
    let open Pervasives in
    let inn_helper x1 x2 = 
      let diff = (x1 * x1) - (2 * x2 * x2)in
      if ((x1 >= 0) && (x2 >= 0)) then(true, diff) else
      if ((x1 < 0) && (x2 < 0)) then (false, diff) else
      if ((x1 >= 0) && (x2 < 0)) then (diff >= 0, diff) else
      (~-diff >= 0, diff) in
    let fsttup = inn_helper x1 x2 in
    let sndtup = inn_helper x3 x4 in
    let diff = (3 * snd(sndtup) * snd(sndtup)) - (snd(fsttup) * snd(fsttup))in
    if fst(fsttup) = true && fst(sndtup) = true then true else
    if fst(fsttup) = false && fst(sndtup) = false then false else
    if fst(fsttup) = true && fst(sndtup) = false then diff >= 0 else
     ~-diff >= 0 end
  let float_of_number = fun (x1,x2,x3,x4) -> begin
    float x1 +. (float x2 *. (sqrt 2.0)) +. (float x3 *. (sqrt 3.0)) +. 
    (float x4 *. (sqrt 6.0)) end
  let format = fun formatter (x1,x2,x3,x4) -> begin
    let root23string = string_of_int x1^" + _/2 "^string_of_int x2^
    " + _/3 "^string_of_int x3^" + _/6 "^string_of_int x4 in
    Format.pp_print_string formatter root23string end
end
 
module type FieldOfFractionsType = functor (R : NiceRing) -> sig
  include NiceField

  val from_numerator : R.number -> number

  (* refines NiceField.inv; raises an exception if the argument is zero. *)
  val inv : number -> number
  val to_number2 : (R.number * R.number) -> number
  val from_number : number -> (R.number * R.number)
end
module FieldOfFractions : FieldOfFractionsType = 
   functor (R : NiceRing) -> struct
   type number = (R.number * R.number)
   open R
   let ( === ) = fun (x1,x2) (y1,y2) -> begin
    (x1 * y2) === (x2 * y1)  end
   let zero = (R.zero, R.one)
   let ( + ) = fun (x1,x2) (y1,y2) -> begin
    ((x1 * y2) + (x2 * y1),(x2 * y2)) end
   let ( ~- ) = fun (x1,x2) -> ((~-x1),x2)
   let one = (R.one, R.one)
   let ( * ) = fun (x1,x2) (y1,y2) -> (( x1 * y1), (x2 * y2))
   let inv = fun (x1,x2) -> (x2,x1)
   let from_numerator = fun x -> (x,R.one)
   let is_non_neg = fun (x1,x2) -> (is_non_neg x1) && (is_non_neg x2)
   let float_of_number = fun (x1,x2) -> begin
     (float_of_number(x1) /. float_of_number(x2)) end
   let format = fun formatter (x1,x2) -> 
     format formatter x1;
     Format.pp_print_string formatter "/";
     format formatter x2 
   let to_number2 = fun x -> x
   let from_number = fun x -> x
end

module type RationalsType = NiceField
  module Rationals : RationalsType = struct
  include FieldOfFractions (Integers)
  open Integers
  (* Redefining + and * so they always return 
     canonicalized values *)
  let ( + ) = fun f1 f2 -> begin
    let new_f1 = from_number f1 in
    let new_f2 = from_number f2 in
    let x1 = fst(new_f1) in
    let x2 = snd(new_f1) in
    let y1 = fst(new_f2) in
    let y2 = snd(new_f2) in
    let num = to_big_int((x1 * y2) + (x2 * y1)) in
    let denom = to_big_int (x2 * y2) in
    let gcd = Big_int.gcd_big_int num denom in
    let can_num = to_number (Big_int.div_big_int num gcd) in
    let can_denom = to_number (Big_int.div_big_int denom gcd) in
    to_number2 (can_num , can_denom) end  
  let ( * ) = fun f1 f2 -> begin
    let new_f1 = from_number f1 in
    let new_f2 = from_number f2 in
    let x1 = fst(new_f1) in
    let x2 = snd(new_f1) in
    let y1 = fst(new_f2) in
    let y2 = snd(new_f2) in
    let num = to_big_int(x1 * y1) in
    let denom = to_big_int (x2 * y2) in
    let gcd = Big_int.gcd_big_int num denom in
    let can_num = to_number (Big_int.div_big_int num gcd) in
    let can_denom = to_number (Big_int.div_big_int denom gcd) in
    to_number2 (can_num , can_denom) end 
end

module type Rot15Type = sig
  include NiceField
  val cos45 : number
  val sin45 : number
  val cos30 : number
  val sin30 : number
end
  module Rot15 : Rot15Type = struct
   include FieldOfFractions (Root23)
   let cos45 = inv(from_numerator(Root23.sqrt2))
   let sin45 = cos45
   let cos30 = (from_numerator(Root23.sqrt3)) *
               (inv(from_numerator((Root23.( + ) Root23.one Root23.one))))
   let sin30 = (from_numerator(Root23.one)) *
               (inv(from_numerator((Root23.( + ) Root23.one Root23.one))))
end

(** Exercise 2 ****************************************************************)

module QuotientUtils (Q : Quotient) = struct
  let (<>) x y = not(Q.( === ) x y)
end

module GroupUtils (G : Group) = struct
  include QuotientUtils (G)
  let (-) x y = G.( + ) (x) (G.( ~- )(y))
end

module RingUtils (R : Ring) = struct
  include GroupUtils (R)
  let rec number_of_int n = 
    if n = 0 then R.zero else
    if n > 0 then 
    let open Pervasives in
    let new_n = pred n in
    R.( + ) (R.one) (number_of_int(new_n)) else
    let open Pervasives in 
    let new_n = succ n in
    R.( + ) (R.(~-)(R.one)) (number_of_int(new_n))
end

module FieldUtils (F : Field) = struct
  include RingUtils (F)
  let (/) x y = F.( * ) (x) (F.inv(y))
end

module OrderedRingUtils (R : OrderedRing) = struct
  include RingUtils (R)
  let (<)  x y = if R.( === ) x y then false else
                 if not(R.is_non_neg x) && R.is_non_neg y then true else
                 if R.is_non_neg x && not(R.is_non_neg y) then false else
                 R.is_non_neg( (-) y x )
                     
  let (>)  x y = if R.( === ) x y then false else  
                 if R.is_non_neg x && not(R.is_non_neg y) then true else
                 if not(R.is_non_neg x) && R.is_non_neg y then false else
                 R.is_non_neg( (-) x y )
                        
  let (<=) x y = R.( === ) x y || (<) x  y
  
  let (>=) x y = R.( === ) x y || (>) x  y

  (* return the smaller of x and y under the (<) ordering *)
  let min  x y = if (<=) x y then x else y

  (* return the larger of x and y under the (<) ordering *)
  let max  x y = if (>=) x y then x else y

  (* implement the Set.OrderedType.compare interface *)
  let compare x y = if R.( === ) x y then 0 else
                    if (>) x y then 1 else -1
             
end

module OrderedFieldUtils (F : OrderedField) = struct
  include FieldUtils (F)
  include OrderedRingUtils (F)
end

(** Exercise 3 ****************************************************************)
module type RealsType = sig
  include NiceField

  (* given a sequence f of rational approximations f(1) f(2) f(3) ... that
   * converges to a real number x, (create f) returns x.
   *
   * f is required to converge at a rate of 10^(-k).  That is, for all k,
   * |x - f(k)| < 10^(-k).  Behavior is completely unspecified if f does not
   * converge fast enough.
   *)
  val create      : (int -> Rationals.number) -> number

  (* approximate x k produces a rational approximations of x that is accurate
   * to within 10^(-k).  In other words, |x - (approximate x k)| < 10^(-k)
   *)
  val approximate : number -> int -> Rationals.number

  val pi : number
  val e  : number
end
  module Reals : RealsType = struct
  module OFU = OrderedFieldUtils(Rationals) 
  type number = int -> Rationals.number
  let create = fun x -> x
  let approximate = fun x k -> x k
  let ( === ) = fun x y -> begin 
    let tenk = Rationals.inv(OFU.number_of_int(10)) in
    let rec checkdiff x y k b =
      let xhat = approximate create(x) k in
      let yhat = approximate create(y) k in
      let open OFU in
      if ((max xhat yhat) - (min xhat yhat)) > b then false
      else let open Pervasives in 
      checkdiff x y (k+1) (Rationals.( * ) b tenk) in
    checkdiff x y 1 tenk end       
  let zero = create(fun k -> Rationals.zero)
  let ( + ) = fun x y -> begin
    let open Pervasives in 
    let plus x y k = Rationals.( + ) (x (k+1)) (y (k+1)) 
    in plus x y end
  let ( ~- ) = fun x -> let r k = Rationals.( ~- )(x k) in r
  let one = create(fun k -> Rationals.one)
  let rec power a n = begin
    if (Rationals.( === ) n Rationals.zero) then Rationals.one
    else 
      Rationals.( * ) (a) (power a (OFU.( - ) n Rationals.one)) end
  let ( * ) = fun x y -> begin
    let mul x y k = begin
      let rec mul_helper x k n = 
      let xhat = approximate (create x) k in 
      if (OFU.( < ) xhat (power (OFU.number_of_int(10)) (OFU.number_of_int(n))))
      then n
      else mul_helper x k (Pervasives.( + ) n 1) in
    let nx = mul_helper x k 0 in
    let ny = mul_helper y k 0 in
    let open Pervasives in
    Rationals.( * ) (x (1 + nx - k)) (y (1 + ny - k)) end in
    mul x y end   
  let inv = fun x -> let r k = Rationals.( ~- )(x k) in r
  let is_non_neg = fun x -> begin
    let tenk = Rationals.inv(OFU.number_of_int(10)) in
    let rec checkneg x k e = 
      let xhat = approximate create(x) k in
      if (Rationals.( + ) xhat e) < Rationals.zero then false
      else if (OFU.( - ) xhat e) > Rationals.zero then false
      else let open Pervasives in checkneg x (k+1) (Rationals.( * ) e tenk) in
    checkneg x 1 tenk end
  let float_of_number = fun x -> begin
    Rationals.float_of_number(approximate create(x) 10) end
  let format = fun formatter x -> begin
    Rationals.format formatter (approximate create(x) 10) end
  (* Uses the Baily-Borwein-Polouffe formula to calculate pi*)
  let pi = create(fun k -> begin
    let rec pi_helper k = 
      let open Rationals in
      let open OFU in
      if k = 0 then 
      ((number_of_int(47)) * (inv(number_of_int(15))))
      else (let rat_k = number_of_int(k) in
      let rat_eight = number_of_int(8) in
      ( inv (power (number_of_int(16)) rat_k) * 
      ((number_of_int(4))/(rat_eight * rat_k + one) -
       (number_of_int(2))/(rat_eight * rat_k + number_of_int(4)) - 
        one / (rat_eight * rat_k + number_of_int(5)) - 
        one / (rat_eight * rat_k + number_of_int(6)))) +
      (pi_helper (Pervasives.(-)k 1))) in
    let open Pervasives in
    pi_helper ((k+1)*(k+1)) end)
  (* Uses the Taylor series approximation to calculate e*) 
  let e = create(fun k -> begin
    let open Rationals in
    let open OFU in
    let rec fact n =  
      if (n === zero) then one
      else n * (fact (n - one)) in
    let rec e_helper k =
      let rat_k = number_of_int(k) in
      if (rat_k === zero) then one
      else (one / (fact rat_k)) + e_helper (Pervasives.(-)k 1) in
    let open Pervasives in 
    e_helper ((k+1)*(k+1)) end)
    
end




(******************************************************************************)

(*
** vim: ts=2 sw=2 ai et
*)
