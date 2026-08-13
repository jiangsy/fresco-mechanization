(** ext_algo — [extract]'s supply invariants and its bridge.

    One rule, so no induction: every statement is the three clusters' own
    invariants composed.  ⭐ Which is the point — [e_extract_block]'s third
    conjunct is the three-way [uniq] that
    [frost/algo/def_rules.v:825-827] argues for in a comment. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.prop_guess.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.prop_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.prop_solve.
Require Import src.frost.ext_algo.def_extract.

Set Implicit Arguments.

Open Scope frost_e_scope.

Lemma e_extract_supply_grows : forall S0 Θ0 NM α m P P' S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e -> S0 [<=] S1.
Proof.
  intros * H; destruct H as [ S0 S1 S2 S3 Θ0 NM α m P P' Ξ Ξs Ξ' C Q Q'
                              Hl Hc Hg ].
  pose proof (e_looksub_supply_grows Hl).
  pose proof (e_solve_cstr_supply_grows Hc).
  pose proof (e_guess_supply_grows Hg).
  fsetdec.
Qed.

(** ⭐ THE THREE-WAY [uniq], AND THE REST OF THE BLOCK ACCOUNTING.  Each half
    is fresh for a supply that already contains the halves before it, so all
    three pairwise disjointnesses are one [fsetdec] each. *)
Lemma e_extract_block : forall S0 Θ0 NM α m P P' S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e ->
  dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
  /\ ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros * H; destruct H as [ S0 S1 S2 S3 Θ0 NM α m P P' Ξ Ξs Ξ' C Q Q'
                              Hl Hc Hg ].
  (* growth, so that a bound against an earlier supply travels forward *)
  pose proof (e_looksub_supply_grows Hl) as Hg1.
  pose proof (e_solve_cstr_supply_grows Hc) as Hg2.
  pose proof (e_guess_supply_grows Hg) as Hg3.
  (* the collection's block *)
  pose proof (e_looksub_generated_in_supply Hl) as Hin1.
  pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hl)
    as [_ [Hfr1 [Hu1 Hft1]]].
  (* the fold's block *)
  pose proof (e_solve_cstr_block Hc) as [Hin2 [Hfr2 [Hu2 Hft2]]].
  (* the guess's block *)
  pose proof (e_guess_block_in_supply Hg) as Hin3.
  pose proof (e_guess_block_fresh Hg) as Hfr3.
  pose proof (e_guess_uniq Hg) as Hu3.
  pose proof (e_guess_block_ftvar Hg) as Hft3.
  repeat rewrite dom_app in *; repeat rewrite ftvar_in_aenv_app in *.
  repeat split; try solve [ fsetdec ].
  apply uniq_app_4;
    [ assumption
    | apply uniq_app_4;
      [ assumption | assumption | unfold disjoint; repeat rewrite dom_app; fsetdec ]
    | unfold disjoint; repeat rewrite dom_app; fsetdec ].
Qed.

(** What the extracted skeleton can mention: the run's own names, plus the two
    subjects it was given. *)
Lemma e_extract_out_ftvar : forall S0 Θ0 NM α m P P' S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e ->
  ftvar_in_pskl Q [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P'.
Proof.
  intros * H; destruct H as [ S0 S1 S2 S3 Θ0 NM α m P P' Ξ Ξs Ξ' C Q Q'
                              Hl Hc Hg ].
  pose proof (e_looksub_supply_grows Hl) as Hg1.
  pose proof (e_solve_cstr_supply_grows Hc) as Hg2.
  pose proof (e_guess_supply_grows Hg) as Hg3.
  pose proof ((proj1 e_looksub_lookeq_cstr_ftvar) _ _ _ _ _ _ _ _ _ Hl) as Hcs.
  pose proof (e_solve_cstr_out_ftvar Hc) as Hq.
  pose proof (e_guess_ftv Hg) as Hq'.
  pose proof (e_guess_block_in_supply Hg) as Hin3.
  simpl in Hq. clear - Hg1 Hg2 Hg3 Hcs Hq Hq' Hin3. fsetdec.
Qed.

(* ===================================================================== *)
(*  The bridge                                                            *)
(*                                                                        *)
(*  ⚙ Each of the three premises needs its OWN coverage, at its OWN        *)
(*  supply — and every one of them is discharged from the clusters'        *)
(*  invariants rather than assumed.  That is the pipeline working: the     *)
(*  collection's block pays for the fold's context, the fold's block and   *)
(*  its output pay for the guess's.                                       *)
(* ===================================================================== *)

Lemma e_extract_sound : forall S0 Θ0 NM α m P P' S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e ->
  add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  {{ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}a.
Proof.
  intros * H Hcov;
    destruct H as [ S0 S1 S2 S3 Θ0 NM α m P P' Ξ Ξs Ξ' C Q Q' Hl Hc Hg ].
  pose proof (e_looksub_supply_grows Hl) as Hg1.
  pose proof (e_solve_cstr_supply_grows Hc) as Hg2.
  (* the collection's block pays for the fold's context *)
  pose proof (e_looksub_generated_in_supply Hl) as Hin1.
  pose proof (e_looksub_block_ftvar Hl) as Hft1.
  pose proof (e_looksub_cstr_ftvar Hl ltac:(clear - Hcov; fsetdec)) as Hcs.
  assert (HctxF : ftvar_in_aenv (Ξ ++ Θ0) [<=] S1)
    by (rewrite ftvar_in_aenv_app; clear - Hcov Hg1 Hin1 Hft1; fsetdec).
  (* the fold's block and output pay for the guess's context *)
  pose proof (e_solve_cstr_block Hc) as [Hin2 [_ [_ Hft2]]].
  pose proof (e_solve_cstr_out_ftvar Hc) as Hq. simpl in Hq.
  assert (HctxG : ftvar_in_aenv (Ξs ++ Ξ ++ Θ0) [<=] S2).
  { repeat rewrite ftvar_in_aenv_app.
    clear - Hcov Hg1 Hg2 Hin1 Hft1 Hin2 Hft2. fsetdec. }
  apply a_extract__solve with (Ξ := Ξ) (Ξs := Ξs) (C := C) (Q := Q).
  - eapply e_looksub_sound; [ exact Hl | exact Hcov ].
  - eapply e_solve_cstr_sound; [ exact Hc | ].
    simpl. clear - HctxF Hcs. fsetdec.
  - eapply e_guess_sound;
      [ exact Hg | exact HctxG | clear - Hq Hcs Hg2; fsetdec ].
Qed.
