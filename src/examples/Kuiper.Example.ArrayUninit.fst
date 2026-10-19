module Kuiper.Example.ArrayUninit

#lang-pulse

open Kuiper
module A = Pulse.Lib.Array
module GA = Kuiper.Array
module Seq = FStar.Seq

inline_for_extraction noextract
fn initialize_kernel
  (output:A.larray bf16 1024)
  preserves gpu
  requires A.pts_to_uninit output 1024
  ensures exists* (initialized:lseq bf16 1024). output |-> initialized
{
  unfold A.pts_to_uninit output 1024;
  let mut i = 0sz;
  while (!i <^ 1024sz)
    invariant exists* (j:sz{j <= 1024}) (masked:Seq.seq (option bf16)).
      i |-> j **
      A.pts_to_mask output masked (fun _ -> True) **
      pure (Seq.length masked == 1024 /\
        (forall (k:nat). k < j ==> Some? (Seq.index masked k)))
    decreases (1024 - !i)
  {
    let j = !i;
    A.mask_write output j (zero #bf16);
    i := j +^ 1sz;
  };
  A.from_mask output;
  with initialized. assert output |-> initialized;
  A.pts_to_len output;
}

instance send_initialized_global
  (#a:Type0)
  (pointer:A.array a{GA.is_global_array pointer})
  (#fraction:perm)
  (contents:Seq.seq a)
  : is_send_across gpu_of (A.pts_to pointer #fraction contents)
  = GA.is_send_pts_to pointer #fraction contents

fn initialize_output
  (output:A.larray bf16 1024{GA.is_global_array output})
  preserves cpu
  requires on gpu_loc (A.pts_to_uninit output 1024)
  ensures exists* (initialized:lseq bf16 1024). on gpu_loc (output |-> initialized)
{
  launch_kernel_1 (fun () -> initialize_kernel output);
}
