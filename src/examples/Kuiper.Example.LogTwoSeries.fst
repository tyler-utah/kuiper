module Kuiper.Example.LogTwoSeries

open FStar.Real
module E = FStar.Math.Exp

let logarithm_bounds ()
  : Lemma (
      69314718055994530.0R /. 100000000000000000.0R <. E.log 2.0R /\
      E.log 2.0R <. 69314718055994532.0R /. 100000000000000000.0R) =
  E.log_two_decimal_bounds ()

let arbitrary_change_of_base (x:real)
  : Lemma (FStar.Math.Pow.exp2 x == E.exp (x *. E.log 2.0R)) =
  E.exp2_as_exp x
