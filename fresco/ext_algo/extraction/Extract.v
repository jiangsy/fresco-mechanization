From Coq Require Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt.

Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.subtyping.def_look_impl.
Require Import src.fresco.ext_algo.subtyping.def_solve_impl.
Require Import src.fresco.ext_algo.subtyping.def_extract_impl.
Require Import src.fresco.ext_algo.consistency.def_consis_impl.
Require Import src.fresco.ext_algo.subtyping.def_sub_impl.
Require Import src.fresco.ext_algo.typing.def_pat_impl.
Require Import src.fresco.ext_algo.typing.def_typing_impl.
Require Import src.fresco.ext_algo.extraction.PseudoMonadic.
Require Import src.fresco.ext_algo.prop_run_corollaries.

Extraction Language OCaml.

Extraction Inline proj1_sig.
Extraction Inline e_guess_mono_run.
Extraction Inline Sumbool.sumbool_of_bool.

Set Extraction Output Directory "fresco/ext_algo/extraction/extracted".

Extraction "fresco_guess.ml"
  e_guess_mono_run e_guess_run
  e_lookeq_run e_looksub_run
  e_solve_eq_run e_solve_sub_run e_solve_cstr_run
  e_extract_run
  e_consis_run
  e_sub_run
  e_pat_run
  e_typing_run
  fresco_infer.
