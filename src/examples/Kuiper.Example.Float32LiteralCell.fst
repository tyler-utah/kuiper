module Kuiper.Example.Float32LiteralCell

module L = Kuiper.Float32.Literals

let scale_cell ()
  : Lemma (
      L.common_normal_cell "0.12751743197441101074"
        1275174308245986 10000000000000000
        1275174308245988 10000000000000000
        8557550 (-26)) =
  assert_norm (
    L.common_normal_cell "0.12751743197441101074"
      1275174308245986 10000000000000000
      1275174308245988 10000000000000000
      8557550 (-26))

let neighboring_cells_rejected ()
  : Lemma (
      not (L.common_normal_cell "0.12751743197441101074"
        1275174308245986 10000000000000000
        1275174308245988 10000000000000000
        8557549 (-26)) /\
      not (L.common_normal_cell "0.12751743197441101074"
        1275174308245986 10000000000000000
        1275174308245988 10000000000000000
        8557551 (-26))) =
  assert_norm (
      not (L.common_normal_cell "0.12751743197441101074"
        1275174308245986 10000000000000000
        1275174308245988 10000000000000000
        8557549 (-26)) /\
      not (L.common_normal_cell "0.12751743197441101074"
        1275174308245986 10000000000000000
        1275174308245988 10000000000000000
        8557551 (-26)))

let invalid_certificates_rejected ()
  : Lemma (
      not (L.common_normal_cell "0.12751743197441101074" 1 10 2 10 8557550 (-26)) /\
      not (L.common_normal_cell "0.12751743197441101074" 2 10 1 10 8557550 (-26)) /\
      not (L.common_normal_cell "0.12751743197441101074e0" 1 10 2 10 8557550 (-26)) /\
      not (L.common_normal_cell "1.0" 1 1 1 1 8388608 (-23)) /\
      not (L.common_normal_cell "0.0" 0 1 0 1 8557550 (-26))) =
  assert_norm (
      not (L.common_normal_cell "0.12751743197441101074" 1 10 2 10 8557550 (-26)) /\
      not (L.common_normal_cell "0.12751743197441101074" 2 10 1 10 8557550 (-26)) /\
      not (L.common_normal_cell "0.12751743197441101074e0" 1 10 2 10 8557550 (-26)) /\
      not (L.common_normal_cell "1.0" 1 1 1 1 8388608 (-23)) /\
      not (L.common_normal_cell "0.0" 0 1 0 1 8557550 (-26)))
