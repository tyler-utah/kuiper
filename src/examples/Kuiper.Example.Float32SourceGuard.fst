module Kuiper.Example.Float32SourceGuard

#lang-pulse

open Kuiper
module F32 = Kuiper.Float32
module F = Kuiper.Floating.Base
module L = Kuiper.Float32.Literals
module SZ = Kuiper.SizeT

inline_for_extraction noextract
let scale () : f32 = F.of_literal "0.12751743197441101074"

let scale_bounds ()
  : Lemma (F32.positive_normal (scale ()) /\ F.lte (scale ()) F.one) =
  assert_norm (L.positive_normal_decimal "0.12751743197441101074");
  assert_norm (L.at_most_one_decimal "0.12751743197441101074");
  F32.positive_normal_of_literal "0.12751743197441101074";
  F32.positive_literal_at_most_one "0.12751743197441101074"

let bound_certificates ()
  : Lemma (
      L.at_most_one_decimal "1.0" /\
      not (L.at_most_one_decimal "1.0000000000000000000000000001") /\
      not (L.at_most_one_decimal "0.1e2"))
  = assert_norm (
      L.at_most_one_decimal "1.0" /\
      not (L.at_most_one_decimal "1.0000000000000000000000000001") /\
      not (L.at_most_one_decimal "0.1e2"))

let maximum_keeps_non_nan (left right : f32)
  : Lemma
      (requires not (NaN? (kind left)))
      (ensures not (NaN? (kind (F.fmax left right)))) =
  F32.fmax_special_values left right;
  if not (NaN? (kind right)) then (
    F.fmax_spec left right;
    F.eq_spec (F.fmax left right) (if F.lt left right then right else left)
  )

inline_for_extraction noextract
fn initial_rescale (maximum : f32)
  preserves gpu
  requires pure (not (NaN? (kind maximum)))
  returns result : f32
  ensures pure (
    (ieee_eq maximum (F.sub F.zero F.infinity) ==> result == F.one) /\
    (not (ieee_eq maximum (F.sub F.zero F.infinity)) ==>
      result == F.zero /\ v_approximates result 0.0R))
{
  scale_bounds ();
  F32.non_nan_classification maximum;
  F.neg_kind (F.infinity #f32);
  F.eq_spec maximum (F.sub F.zero F.infinity);
  let scaled = F32.mul_rn_ftz maximum (scale ());
  if ieee_eq maximum (F.sub F.zero F.infinity) {
    F.one
  } else {
    let shifted = F.sub F.zero scaled;
    F.neg_kind scaled;
    assert pure (Finite? (kind shifted) \/ shifted == F.sub F.zero F.infinity);
    let argument = F32.fma_rn_ftz (F.sub F.zero F.infinity) (scale ()) shifted;
    F32.exp2_approx_ftz argument
  }
}

[@@expect_failure [19]]
fn cannot_drop_scale_bound (x y : f32)
  preserves gpu
  requires pure (Finite? (kind x) /\ F32.positive_normal y)
  returns result : f32
  ensures pure (Finite? (kind result))
{
  F32.mul_rn_ftz x y
}

[@@expect_failure [19]]
let two_nans_are_not_finite (x y : f32)
  : Lemma
      (requires NaN? (kind x) /\ NaN? (kind y))
      (ensures Finite? (kind (F.fmax x y))) =
  F32.fmax_special_values x y

[@@expect_failure [19]]
fn cannot_drop_multiplier_condition (y : f32)
  preserves gpu
  returns result : f32
  ensures pure (result == F.infinity)
{
  F32.mul_rn_ftz F.infinity y
}

inline_for_extraction noextract
fn kernel
  (n : sz{SZ.v n <= 536870911})
  (inputs : larray f32 (2 * SZ.v n))
  (outputs : larray f32 (4 * SZ.v n))
  (#xs : erased (lseq f32 (2 * SZ.v n)))
  (#before : erased (seq f32))
  preserves gpu ** inputs |-> xs
  requires outputs |-> before
  ensures exists* after. outputs |-> after
{
  let mut i = 0sz;
  while (!i <^ n)
    invariant exists* (j : sz{j <= n}). i |-> j
    invariant exists* values. outputs |-> values
    decreases (n - !i)
  {
    let j = !i;
    let x = inputs.(2sz *^ j);
    let y = inputs.(2sz *^ j +^ 1sz);
    let maximum = F.fmax (F.sub F.zero F.infinity) x;
    F.neg_kind (F.infinity #f32);
    maximum_keeps_non_nan (F.sub F.zero F.infinity) x;
    let result = initial_rescale maximum;
    let product = F32.mul_rn_ftz x y;
    let scaled = F32.mul_rn_ftz x (scale ());
    pts_to_len outputs;
    outputs.(4sz *^ j) <- F.fmax x y;
    outputs.(4sz *^ j +^ 1sz) <- product;
    outputs.(4sz *^ j +^ 2sz) <- scaled;
    outputs.(4sz *^ j +^ 3sz) <- result;
    i := !i +^ 1sz;
  }
}

instance send_global_array_contents
  (#a : Type0)
  (arr : array a{is_global_array arr})
  (#f : perm)
  (contents : seq a)
  : is_send_across gpu_of (Pulse.Lib.Array.pts_to arr #f contents)
  = Kuiper.Array.Core.is_send_pts_to arr #f contents

fn run
  (n : sz{SZ.v n <= 536870911})
  (inputs : larray f32 (2 * SZ.v n){is_global_array inputs})
  (outputs : larray f32 (4 * SZ.v n){is_global_array outputs})
  (#xs : erased (lseq f32 (2 * SZ.v n)))
  preserves cpu ** on gpu_loc (inputs |-> xs)
  requires exists* before. on gpu_loc (outputs |-> before)
  ensures exists* after. on gpu_loc (outputs |-> after)
{
  with before. assert on gpu_loc (outputs |-> before);
  launch_kernel_1 (fun () -> kernel n inputs outputs #xs #before);
}
