module Kuiper.Example.Float32FtzSpecialValues

#lang-pulse

open Kuiper
module F32 = Kuiper.Float32
module F = Kuiper.Floating.Base
module Literals = Kuiper.Float32.Literals
module SZ = Kuiper.SizeT

let literal_certificates ()
  : Lemma (
      Literals.positive_normal_decimal "0.12751743197441101074" /\
      Literals.positive_normal_decimal "1.0" /\
      not (Literals.positive_normal_decimal "0.0") /\
      not (Literals.positive_normal_decimal "0.000000000000000000000000000000000000001") /\
      not (Literals.positive_normal_decimal "999999999999999999999999999999999999999.0") /\
      not (Literals.positive_normal_decimal "0.1e-100") /\
      not (Literals.positive_normal_decimal "0.1.2"))
  = assert_norm (
      Literals.positive_normal_decimal "0.12751743197441101074" /\
      Literals.positive_normal_decimal "1.0" /\
      not (Literals.positive_normal_decimal "0.0") /\
      not (Literals.positive_normal_decimal "0.000000000000000000000000000000000000001") /\
      not (Literals.positive_normal_decimal "999999999999999999999999999999999999999.0") /\
      not (Literals.positive_normal_decimal "0.1e-100") /\
      not (Literals.positive_normal_decimal "0.1.2"))

inline_for_extraction noextract
let attention_scale () : f32 = F.of_literal "0.12751743197441101074"

inline_for_extraction noextract
fn initial_rescale (shift : f32)
  preserves gpu
  returns result : f32
  ensures pure (
    (Finite? (kind shift) \/ shift == F.sub F.zero F.infinity ==>
      result == F.zero /\ v_approximates result 0.0R) /\
    (shift == F.infinity \/ NaN? (kind shift) ==> NaN? (kind result)))
{
  literal_certificates ();
  F32.positive_normal_of_literal "0.12751743197441101074";
  let argument = F32.fma_rn_ftz (F.sub F.zero F.infinity) (attention_scale ()) shift;
  F32.exp2_approx_ftz argument
}

inline_for_extraction noextract
fn initial_rescale_at_zero ()
  preserves gpu
  returns result : f32
  ensures pure (result == F.zero /\ v_approximates result 0.0R)
{
  initial_rescale F.zero
}

inline_for_extraction noextract
fn exp2_negative_infinity ()
  preserves gpu
  returns result : f32
  ensures pure (result == F.zero /\ v_approximates result 0.0R)
{
  F32.exp2_approx_ftz (F.sub F.zero F.infinity)
}

[@@expect_failure [19]]
fn cannot_drop_shift_condition (shift : f32)
  preserves gpu
  returns result : f32
  ensures pure (result == F.zero)
{
  initial_rescale shift
}

[@@expect_failure [19]]
fn infinite_cancellation_is_not_zero ()
  preserves gpu
  returns result : f32
  ensures pure (result == F.zero)
{
  initial_rescale F.infinity
}

[@@expect_failure [19]]
fn cannot_drop_multiplier_condition (multiplier : f32)
  preserves gpu
  returns result : f32
  ensures pure (result == F.sub F.zero F.infinity)
{
  F32.fma_rn_ftz (F.sub F.zero F.infinity) multiplier F.zero
}

[@@expect_failure [19]]
fn cannot_preserve_nan_payload (x : f32)
  preserves gpu
  requires pure (NaN? (kind x))
  returns result : f32
  ensures pure (result == x)
{
  F32.exp2_approx_ftz x
}

[@@expect_failure [228]]
fn cannot_compute_exp2_on_cpu (x : f32)
  preserves cpu
  returns f32
{
  F32.exp2_approx_ftz x
}

inline_for_extraction noextract
fn kernel
  (n : sz{SZ.v n <= 357913941})
  (inputs : larray f32 (3 * SZ.v n))
  (outputs : larray f32 (6 * SZ.v n))
  (#xs : erased (lseq f32 (3 * SZ.v n)))
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
    let x = inputs.(3sz *^ j);
    let y = inputs.(3sz *^ j +^ 1sz);
    let z = inputs.(3sz *^ j +^ 2sz);
    let exponential = F32.exp2_approx_ftz x;
    let fused = F32.fma_rn_ftz x y z;
    let argument = F32.fma_rn_ftz (F.sub F.zero F.infinity) y z;
    let rescale = F32.exp2_approx_ftz argument;
    let fixed_rescale = initial_rescale z;
    pts_to_len outputs;
    outputs.(6sz *^ j) <- exponential;
    outputs.(6sz *^ j +^ 1sz) <- fused;
    outputs.(6sz *^ j +^ 2sz) <- argument;
    outputs.(6sz *^ j +^ 3sz) <- rescale;
    outputs.(6sz *^ j +^ 4sz) <- fixed_rescale;
    outputs.(6sz *^ j +^ 5sz) <- attention_scale ();
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
  (n : sz{SZ.v n <= 357913941})
  (inputs : larray f32 (3 * SZ.v n){is_global_array inputs})
  (outputs : larray f32 (6 * SZ.v n){is_global_array outputs})
  (#xs : erased (lseq f32 (3 * SZ.v n)))
  preserves cpu ** on gpu_loc (inputs |-> xs)
  requires exists* before. on gpu_loc (outputs |-> before)
  ensures exists* after. on gpu_loc (outputs |-> after)
{
  with before. assert on gpu_loc (outputs |-> before);
  launch_kernel_1 (fun () -> kernel n inputs outputs #xs #before);
}
