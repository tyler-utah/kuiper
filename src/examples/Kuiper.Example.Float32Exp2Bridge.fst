module Kuiper.Example.Float32Exp2Bridge

open Kuiper
module F = Kuiper.Floating.Base
module F32 = Kuiper.Float32
module L = Kuiper.Float32.Literals
module E = FStar.Math.Exp
module P = FStar.Math.Pow
module S = FStar.Math.Sqrt

#set-options "--fuel 2 --ifuel 0 --z3rlimit 120"

inline_for_extraction noextract
let scale () : f32 = F.of_literal "0.12751743197441101074"

let ideal_scale () : real =
  E.log_two_positive ();
  S.rsqrt 128.0R /. E.log 2.0R

let ideal_scale_bounds ()
  : Lemma (
      1275174308245986.0R /. 10000000000000000.0R <. ideal_scale () /\
      ideal_scale () <. 1275174308245988.0R /. 10000000000000000.0R) =
  S.sqrt_positive 128.0R;
  S.sqrt_square 128.0R;
  E.log_two_decimal_bounds ();
  E.log_two_positive ();
  let root = S.sqrt 128.0R in
  let logarithm = E.log 2.0R in
  assert (11313708498984760.0R /. 1000000000000000.0R <. root);
  assert (root <. 11313708498984762.0R /. 1000000000000000.0R);
  assert (
    (11313708498984760.0R /. 1000000000000000.0R) *.
    (69314718055994530.0R /. 100000000000000000.0R) <. root *. logarithm);
  assert (
    root *. logarithm <.
    (11313708498984762.0R /. 1000000000000000.0R) *.
    (69314718055994532.0R /. 100000000000000000.0R))

let scale_certificate ()
  : Lemma (L.common_normal_cell "0.12751743197441101074"
      1275174308245986 10000000000000000
      1275174308245988 10000000000000000
      8557550 (-26)) =
  assert_norm (
    L.common_normal_cell "0.12751743197441101074"
      1275174308245986 10000000000000000
      1275174308245988 10000000000000000
      8557550 (-26))

let scale_represents_ideal ()
  : Lemma (v_approximates (scale ()) (ideal_scale ())) =
  ideal_scale_bounds ();
  scale_certificate ();
  F32.literal_interval_approx "0.12751743197441101074"
    1275174308245986 10000000000000000
    1275174308245988 10000000000000000
    8557550 (-26) (ideal_scale ())

let scaled_change_of_base (difference:real)
  : Lemma (
      P.exp2 (difference *. ideal_scale ()) ==
        E.exp (difference *. S.rsqrt 128.0R)) =
  E.log_two_positive ();
  E.exp2_as_exp (difference *. ideal_scale ())

let ideal_is_strictly_below_decoded_float ()
  : Lemma (ideal_scale () <. 4278775.0R /. 33554432.0R) =
  ideal_scale_bounds ()

[@@expect_failure [19]]
let cannot_equate_ideal_and_decoded_float ()
  : Lemma (ideal_scale () == 4278775.0R /. 33554432.0R) =
  ideal_scale_bounds ()

[@@expect_failure [19]]
let cannot_omit_lower_enclosure
  (r:real{r <=. 1275174308245988.0R /. 10000000000000000.0R})
  : Lemma (v_approximates (scale ()) r) =
  scale_certificate ();
  F32.literal_interval_approx "0.12751743197441101074"
    1275174308245986 10000000000000000
    1275174308245988 10000000000000000
    8557550 (-26) r

[@@expect_failure [19]]
let cannot_omit_upper_enclosure
  (r:real{1275174308245986.0R /. 10000000000000000.0R <=. r})
  : Lemma (v_approximates (scale ()) r) =
  scale_certificate ();
  F32.literal_interval_approx "0.12751743197441101074"
    1275174308245986 10000000000000000
    1275174308245988 10000000000000000
    8557550 (-26) r

[@@expect_failure [19]]
let cannot_use_neighboring_cell ()
  : Lemma (v_approximates (scale ()) (ideal_scale ())) =
  ideal_scale_bounds ();
  F32.literal_interval_approx "0.12751743197441101074"
    1275174308245986 10000000000000000
    1275174308245988 10000000000000000
    8557551 (-26) (ideal_scale ())
