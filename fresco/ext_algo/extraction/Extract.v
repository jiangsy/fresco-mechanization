(** ⭐ THE TREE'S FIRST EXTRACTION — a real OCaml artifact, not a comment.

    The hand-off's §0 records that the tree contained ZERO [Extraction]
    commands, so the paper's shipped implementation
    ([paper/artifact/implementation/lib/type.ml]) was related to the
    mechanization only by our reading of it.  This file closes that for the
    part of the algorithm that has a runner.

    ⚙ WHAT IS EMITTED, and what is not.  Every judgement of [fresco/ext_algo]
    is a threaded RELATION bridged to [fresco/algo]'s (TODO (1), complete).
    A relation is [Prop] and extracts to nothing, so what can be emitted is
    exactly what has a Bove–Capretta runner — which since phase 4 (§8b) is
    EVERY judgement: the export list below reaches from [guess^TY] up to
    [e_typing_run], the algorithm's entry point.  ⚙ The output file keeps
    its M1.7 name [fresco_guess.ml]; it now holds the whole algorithm, and
    renaming it is deliberately deferred (the name is wired into the
    Makefile's acceptance step and this file's history).

    ⚠️ [ExtrOcamlNatInt] IS NOT A FOOTNOTE.  Without it metalib's atoms
    extract as UNARY [nat] — [supply_fresh] becomes [S (nat_list_max xs)] and
    the output is unusable for a differential test against [type.ml].  McTT
    imports it at its own entry point for the same reason
    (theories/Entrypoint.v).

    ⚙ OUTPUT.  [extracted/fresco_guess.ml] beside this file.  It is a BUILD
    PRODUCT — regenerated on every build, removed by [make clean], and
    git-ignored — so treat it as a snapshot to READ, never to edit.  ⚠️ The
    directory has to exist before [coqc] runs, because
    [Set Extraction Output Directory] does NOT create it; the Makefile's
    [coq] and [quick] targets [mkdir -p] it. *)

From Coq Require Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt.

Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_guess_impl.
Require Import src.fresco.ext_algo.def_guess_impl_sk.
Require Import src.fresco.ext_algo.def_dec.
Require Import src.fresco.ext_algo.def_look_impl.
Require Import src.fresco.ext_algo.def_solve_impl.
Require Import src.fresco.ext_algo.def_extract_impl.
Require Import src.fresco.ext_algo.def_consis_impl.
Require Import src.fresco.ext_algo.def_sub_impl.
Require Import src.fresco.ext_algo.def_pat_impl.
Require Import src.fresco.ext_algo.def_typing_impl.
Require Import src.fresco.ext_algo.extraction.PseudoMonadic.
Require Import src.fresco.ext_algo.prop_run_corollaries.  (* [fresco_infer], §7 *)

Extraction Language OCaml.

(** ⭐ THE STANDING BAR (hand-off §8): the extracted program must read as an
    ordinary OCaml program that can be diffed against [type.ml] — no
    [Acc_rect] / [Fix_sub] / [FixWf] wrappers, no [sumbool] / [sig]
    scaffolding, no [Obj.magic], no residue of the termination argument.
    Bove–Capretta gets us most of the way (the domain predicate is [Prop] and
    is ERASED); these two directives remove what is left. *)
Extraction Inline proj1_sig.
Extraction Inline e_guess_mono_run.
(* the phase-4 runners test their guards through [sumbool_of_bool]; inlined,
   each test extracts as a bare [if] — the same §8 bar the two inlines above
   serve *)
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
  (* ⭐ the CERTIFIED ENTRY POINT (prop_run_corollaries.v §7, McTT's
     [main_result] idiom): same data as [e_typing_run], but the
     constructor TAG carries the paper-level reading — [Inferred] is a
     declarative typing, [Untypable] a proof that none exists.  The wf
     hypothesis is [Prop] and vanishes: OCaml sees [exp -> infer_result]. *)
  fresco_infer.
