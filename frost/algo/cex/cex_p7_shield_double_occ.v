(** ⚠️ THE POSITIONAL [sub_shield] IS *STILL* OVER-STRONG — THE
    DOUBLE-OCCURRENCE WITNESS.

    [cex_p7_shield_realizable.v] repaired TASK 0's premise by POSITIONAL
    indexing: the two guess-descending closures are demanded only where the
    looked-for [α] occurs in the walk position's subject ([the guard
    α ∈ ftv R']), and at its witness — subject [α → unit], the marker at ONE
    position — the repaired premise HOLDS ([p7_sub_shield_repaired_holds]).

    THIS FILE shows the guard is NOT ENOUGH.  Take the SAME [(Θ0, P0, ψa)]
    and put the marker at BOTH positions:

      P0 = (∀γ. γ→γ) → α̂          unchanged
      R  = ∀^t. (□₀ → □₀)          the subject: the binder occurs TWICE
      ψa = ∀^e β. β→β              unchanged — TAGGED, COMPOUND body
      κ  = α̂ ↦ unit→unit           (the codomain must offer an arrow)
      Q  = (∀ᵢ. β→β) → (unit→unit)

    The join is INHABITED — the tag [e] is still discharged at the arrow's
    DOMAIN, exactly as in the realizable witness, while the CODOMAIN copy of
    the guess is merely ForallL-INSTANTIATED (with [unit]) against the
    mono-ish counterpart the fill gives a raw flexible, which costs no tag
    at all ([join_w2]).  Every other hypothesis of P7b's ForallL row holds
    too ([p7_sub_shield_positional_over_strong]).  But now the shield's
    subject is [open (□₀ → □₀) α = α → α]: one [sss_arrow_r] step reaches
    [(α̂, α)], the guard [α ∈ ftv α] is MET, and the leaf is
    [cex_p7_shield_forall_flex.v]'s machine-checked stuck shape — a raw
    Θ0-flexible facing the whole tagged guess
    ([p7_sub_shield_double_fails]).

    ⭐ WHAT THIS ESTABLISHES.  No general supply of the CURRENT [sub_shield]
    exists for a [P0] with a ∀ below its head: the premise is FALSE at a
    reachable P7b ForallL node, so the residual [main_forall] hypothesis of
    [a_sub_complete_bundle_holds] cannot be discharged through
    [a_sub_complete_forall_l_tagged] as stated.  The positional guard
    localised the demand to the positions the guess REACHES; what it cannot
    see is WHAT THE DERIVATION DOES THERE.  With the marker at two
    positions the derivation treats the two copies of the guess
    DIFFERENTLY — the domain copy is MATCHED against the inherited ∀ of
    [Q] (where its tag is solved), the codomain copy is INSTANTIATED
    against the mono-ish counterpart of the raw flexible (solving no tag)
    — while [flex_shield] demands, at every guarded position, protection
    of the WHOLE guess including its tag.  The next repair therefore has
    to distinguish positions by what the join does at them (match vs
    instantiate — equivalently, by the counterpart the FILL pins there),
    not merely by where the marker sits.

    ⚠️ WHAT IT DOES **NOT** ESTABLISH.  Nothing for docs/PAPER-GAPS.md:
    [sub_shield] is a MECH-INVENTED repair premise (P6-Sv's), not a paper
    statement, and neither P6-Sv, P6-Ss nor thm:complete-subtyping is
    refuted — the ALGORITHM plainly succeeds at this configuration (the
    domain constraint pins the guess for the opened binder; the codomain
    solve instantiates [α̂]).  What is refuted is the third indexing of the
    repair premise, as the realizable file refuted the second. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.prop_basic.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_look_complete.
Require Import src.frost.algo.prop_sub_msubst_equiv.
Require Import src.frost.algo.prop_look_complete_sub_var.
Require Import src.frost.algo.prop_look_complete_sub_cstr.
Require Import src.frost.algo.cex.cex_p7_shield_forall_flex.

Set Implicit Arguments.

Section DoubleOccurrence.

Variables f e t : atom.
Hypothesis Het : e <> t.

Definition Θ0d : aenv := f ~ abind_flex_mono.

(* the guess — unchanged from the realizable witness *)
Definition ψd : uskl := cexψ e.

(* [P0 = (∀γ. γ→γ) → α̂] — unchanged *)
Definition P0d : pskl :=
  pskl_arrow (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
             (pskl_var_f f).

(* ⭐ the ONE change: the ∀-binder occurs at BOTH arrow positions *)
Definition Rjd : uskl := uskl_arrow (uskl_var_b 0) (uskl_var_b 0).
Definition Rd : uskl := uskl_all_etag t Rjd.
Definition Qd : bskl :=
  bskl_arrow (bskl_all_inh (bskl_arrow (bskl_var_b 0) (bskl_var_b 0)))
             (bskl_arrow bskl_unit bskl_unit).
(* …and correspondingly the codomain image is an arrow, so the instantiated
   codomain copy of the guess has something to face *)
Definition κd : metasubst := (f, ptyp_arrow ptyp_unit ptyp_unit) :: nil.

Lemma Θ0d_wf : a_wf_aenv Θ0d.
Proof. apply a_wf_aenv__flex; [ simpl; clear; fsetdec | apply a_wf_aenv__nil ]. Qed.

Lemma P0d_wf : Θ0d ⨟ empty ⊢ₚₛᵃ P0d.
Proof.
  apply a_wf_pskl__arrow.
  - apply a_wf_pskl__all with (L := empty). intros α _.
    unfold open_pskl_wrt_pskl; simpl.
    apply a_wf_pskl__arrow; apply a_wf_pskl__var; left; clear; fsetdec.
  - apply a_wf_pskl__var. right. right. left. unfold binds; simpl. auto.
Qed.

(* --------------------------------------------------------------------- *)
(*  (1) THE GUESS IS A LEGAL ForallL GUESS — verbatim from the realizable  *)
(*      witness                                                            *)
(* --------------------------------------------------------------------- *)

Lemma ψd_tags : a_tags_sort a_sub_mode_ty (singleton e) ψd.
Proof.
  unfold ψd, cexψ.
  apply a_tags_sort__ty.
  - apply is_tskl__all_etag with (L := empty). intros α _.
    unfold open_uskl_wrt_uskl; simpl.
    apply is_tskl__arrow; apply is_tskl__var.
  - apply d_tags_skl__all_etag with (L := empty) (Ψ0 := empty);
      [ intros α _; unfold open_uskl_wrt_uskl; simpl;
        apply d_tags_skl__arrow with (Ψ1 := empty) (Ψ2 := empty);
          [ apply d_tags_skl__var; clear; fsetdec
          | apply d_tags_skl__var; clear; fsetdec
          | clear; fsetdec | clear; fsetdec ]
      | clear; fsetdec
      | clear; fsetdec ].
  - apply uskl_ghost_free__all_etag with (L := empty). intros α _.
    unfold open_uskl_wrt_uskl; simpl.
    apply uskl_ghost_free__arrow; apply uskl_ghost_free__var.
Qed.

Lemma ψd_erase_wf : Θ0d ⨟ empty ⊢ₚₛᵃ ⌊ ψd ⌋ˢ.
Proof.
  unfold ψd, cexψ; simpl.
  apply a_wf_pskl__all with (L := empty). intros α _.
  unfold open_pskl_wrt_pskl; simpl.
  apply a_wf_pskl__arrow; apply a_wf_pskl__var; left; clear; fsetdec.
Qed.

(* --------------------------------------------------------------------- *)
(*  (2) THE JOIN.  The DOMAIN copy of the guess is MATCHED — the tag [e]  *)
(*      is discharged against the inherited ∀, verbatim as before.  The   *)
(*      CODOMAIN copy is ForallL-INSTANTIATED with [unit] against the     *)
(*      mono-ish counterpart — at NO tag cost.                            *)
(* --------------------------------------------------------------------- *)

Lemma consis_d :
  (singleton e) ⨟ Θ0d ⊢ₛᵃ ψd
    ∼ (bskl_all_inh (bskl_arrow (bskl_var_b 0) (bskl_var_b 0))).
Proof.
  unfold ψd, cexψ.
  apply ad_pat_consis__forall_inh_tagged with (L := empty) (Ψ0 := empty);
    [ | clear; fsetdec ].
  intros α _. unfold open_uskl_wrt_uskl, open_bskl_wrt_bskl; simpl.
  apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
    [ | | clear; fsetdec ];
    (apply ad_pat_consis__var;
     [ clear; fsetdec | left; unfold binds; simpl; auto ]).
Qed.

Lemma refine_dom_d :
  Θ0d ⨟ empty ⊢ᵣₚᵃ ⌊ ψd ⌋ˢ
    ⊳ (bskl_to_pskl (bskl_all_inh (bskl_arrow (bskl_var_b 0) (bskl_var_b 0)))).
Proof.
  unfold ψd, cexψ; simpl.
  apply ad_refine_pskl__all with (L := empty). intros α _.
  unfold open_pskl_wrt_pskl; simpl.
  apply ad_refine_pskl__arrow; apply ad_refine_pskl__var; left; clear; fsetdec.
Qed.

(** the CODOMAIN: the guess itself, instantiated with [unit] and checked
    against the arrow counterpart — index EMPTY, no tag solved *)
Lemma join_cod_d :
  ad_pat_sub_gv 1 a_sub_mode_ty mode_tc empty Θ0d ψd
    (bskl_arrow bskl_unit bskl_unit).
Proof.
  unfold ψd, cexψ.
  apply ad_pat_sub_gv__forall_l_tagged
    with (Ψ' := empty) (ψ := uskl_unit);
    [ discriminate
    | clear; fsetdec
    | clear; fsetdec
    | apply a_tags_sort__ty;
        [ apply is_tskl__unit
        | apply d_tags_skl__unit; clear; fsetdec
        | apply uskl_ghost_free__unit ]
    | simpl; apply a_wf_pskl__unit
    | ].
  unfold open_uskl_wrt_uskl; simpl.
  change (bskl_arrow bskl_unit bskl_unit)
    with (pskl_to_bskl_inh (pskl_arrow pskl_unit pskl_unit)).
  apply ad_pat_sub_gv__check;
    [ apply guarded_uskl__arrow; apply lc_uskl_unit
    | apply guarded_pskl__arrow; apply lc_pskl_unit
    | simpl; apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
        [ apply ad_pat_consis__unit; clear; fsetdec
        | apply ad_pat_consis__unit; clear; fsetdec
        | clear; fsetdec ]
    | simpl; apply ad_refine_pskl__arrow; apply ad_refine_pskl__unit ].
Qed.

Lemma join_d :
  ad_pat_sub_gv 3 a_sub_mode_ty (mode_fn mode_tc) empty Θ0d Rd Qd.
Proof.
  unfold Rd, Qd.
  apply ad_pat_sub_gv__forall_l_tagged
    with (Ψ' := singleton e) (ψ := ψd);
    [ discriminate
    | clear; fsetdec
    | unfold Rjd; simpl; clear - Het; fsetdec
    | apply ψd_tags
    | apply ψd_erase_wf
    | ].
  unfold Rjd, open_uskl_wrt_uskl; simpl.
  apply ad_pat_sub_gv__arrow
    with (Ψ1 := singleton e) (Ψ2 := empty);
    [ apply consis_d | apply refine_dom_d | apply join_cod_d
    | clear; fsetdec ].
Qed.

(** …and the join PREMISE in the row's own shape (the subject with the guess
    substituted at BOTH positions) *)
Lemma join_premise_d :
  ad_pat_sub_gv 2 a_sub_mode_ty (mode_fn mode_tc)
    (empty `union` singleton e) Θ0d (open_uskl_wrt_uskl Rjd ψd) Qd.
Proof.
  unfold Rjd, open_uskl_wrt_uskl, Qd; simpl.
  apply ad_pat_sub_gv__arrow with (Ψ1 := singleton e) (Ψ2 := empty);
    [ apply consis_d | apply refine_dom_d | apply join_cod_d
    | clear; fsetdec ].
Qed.

(* --------------------------------------------------------------------- *)
(*  (3) THE FILL, and the rest of the completeness configuration          *)
(* --------------------------------------------------------------------- *)

Definition Pd : pskl := ⌊ Rd ⌋ˢ.

Lemma msubst_P0d : pskl_to_bskl_inh (msubst_pskl κd P0d) = Qd.
Proof.
  unfold κd, P0d, Qd; simpl.
  match goal with
  | |- context [if ?c then _ else _] => destruct c as [_ | n0]
  end; [ reflexivity | exfalso; apply n0; reflexivity ].
Qed.

Lemma fill_d :
  ad_refine_syn_f empty Θ0d empty (pskl_to_bskl_inh (msubst_pskl κd P0d)) Qd.
Proof.
  rewrite msubst_P0d. unfold Qd.
  apply ad_refine_syn_f__arrow.
  - apply ad_refine_syn_f__all with (L := empty). intros α _.
    unfold open_bskl_wrt_bskl; simpl.
    apply ad_refine_syn_f__arrow;
      apply ad_refine_syn_f__var; left; clear; fsetdec.
  - apply ad_refine_syn_f__arrow; apply ad_refine_syn_f__unit.
Qed.

Lemma inc_d : κd ∷ Θ0d ⊑ Θ0d.
Proof.
  unfold κd, Θ0d.
  apply a_inc__flex;
    [ apply a_inc__empty;
        apply a_suffix__cons;
          [ apply a_suffix__nil | apply a_suffix_binding__flex_mono ]
    | apply a_wf_ptyp__arrow; apply a_wf_ptyp__unit
    | apply mono_ptyp__arrow; apply mono_ptyp__unit ].
Qed.

Lemma lc_Rd : lc_uskl Rd.
Proof.
  unfold Rd, Rjd.
  apply lc_uskl_all_etag_exists with (α1 := f).
  unfold open_uskl_wrt_uskl; simpl.
  apply lc_uskl_arrow; apply lc_uskl_var_f.
Qed.

Lemma slack_d : Θ0d ⊢ Rd ≡ᵘ (msubst_uskl_syn κd Rd).
Proof.
  replace (msubst_uskl_syn κd Rd) with Rd by reflexivity.
  apply a_uskl_tyequiv_refl. apply lc_Rd.
Qed.

Lemma Pd_wf : Θ0d ⨟ empty ⊢ₚₛᵃ Pd.
Proof.
  unfold Pd, Rd, Rjd; simpl.
  apply a_wf_pskl__all with (L := empty). intros α _.
  unfold open_pskl_wrt_pskl; simpl.
  apply a_wf_pskl__arrow; apply a_wf_pskl__var; left; clear; fsetdec.
Qed.

Lemma Qd_wf : Θ0d ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qd).
Proof.
  unfold Qd; simpl.
  apply a_wf_pskl__arrow.
  - apply a_wf_pskl__all with (L := empty). intros α _.
    unfold open_pskl_wrt_pskl; simpl.
    apply a_wf_pskl__arrow; apply a_wf_pskl__var; left; clear; fsetdec.
  - apply a_wf_pskl__arrow; apply a_wf_pskl__unit.
Qed.

Lemma P0d_mode : a_ty_mode_compat (mode_fn mode_tc) P0d.
Proof.
  unfold P0d.
  apply a_ty_mode_compat__fn.
  change (pskl_var_f f) with (ptyp_to_pskl (ptyp_var_f f)).
  apply a_ty_mode_compat__tc.
Qed.

Lemma P0d_guarded : guarded_pskl P0d.
Proof.
  unfold P0d. apply guarded_pskl__arrow; [ | apply lc_pskl_var_f ].
  apply lc_pskl_all_syn_exists with (α1 := f).
  unfold open_pskl_wrt_pskl; simpl.
  apply lc_pskl_arrow; apply lc_pskl_var_f.
Qed.

Lemma Rd_ghost_free : uskl_ghost_free Rd.
Proof.
  unfold Rd, Rjd.
  apply uskl_ghost_free__all_etag with (L := empty). intros α _.
  unfold open_uskl_wrt_uskl; simpl.
  apply uskl_ghost_free__arrow; apply uskl_ghost_free__var.
Qed.

(* --------------------------------------------------------------------- *)
(*  (4) THE DISPATCHER HAS NO OTHER RULE TO TAKE THERE                    *)
(* --------------------------------------------------------------------- *)

Lemma join_at_Rd_is_forall_l : forall n NM M Ψ,
  ad_pat_sub_gv n NM M Ψ Θ0d Rd Qd ->
  M <> mode_ti ->
  exists n0 Ψ' ψ,
    n = S n0 /\
    a_tags_sort NM Ψ' ψ /\
    ad_pat_sub_gv n0 NM M (Ψ `union` Ψ') Θ0d (open_uskl_wrt_uskl Rjd ψ) Qd.
Proof.
  intros n NM M Ψ H Hm; unfold Rd, Qd in H; inversion H; subst;
    try solve [ exfalso; apply Hm; reflexivity
              | match goal with Hg : guarded_uskl _ |- _ => inversion Hg end ].
  do 3 eexists; split; [ reflexivity | split; eassumption ].
Qed.

(* --------------------------------------------------------------------- *)
(*  (5) …AND THE SHIELD IS FALSE: the guard is MET at the raw flexible    *)
(* --------------------------------------------------------------------- *)

Lemma binds_f_d : binds f abind_flex_mono Θ0d.
Proof. unfold binds; simpl; auto. Qed.

Lemma e_in_d : e `in` (singleton e).
Proof. clear; fsetdec. Qed.

(** ⭐⭐ THE HEADLINE REFUTATION.  The shield, in exactly the form P7b's
    ForallL row demands it ([a_sub_complete_forall_l_tagged]'s premise at
    this node), is FALSE — for EVERY marker [α], in particular every fresh
    one: [open Rjd α = α → α], one [sss_arrow_r] step reaches [(α̂, α)],
    the guard [α ∈ ftv α] is met, and the leaf is the machine-checked
    stuck shape of cex_p7_shield_forall_flex.v. *)
(* ⭕⭕ RETRACTED AND REVERSED (2026-08-05) — [p7_sub_shield_double_fails].

   It refuted [sub_shield] here THROUGH THE GUARDED CONJUNCT: one
   [sss_arrow_r] step reaches [(α̂, α)], the guard [α ∈ ftv α] is met, and
   [flex_apart_walk] is then stuck at the raw flexible facing the opened
   tagged ∀.  That conjunct is GONE (prop_look_complete_sub_cstr.v): under
   the authors' repaired [SolE-FlexR], P6-Cv does not consume [flex_apart],
   so P6-Sv does not need [flex_apart_walk], so [sub_shield] keeps only its
   Δρ-constant P0-only half.

   ⭐⭐ AND THE SHIELD NOW *HOLDS* AT THIS VERY CONFIGURATION — see
   [p7_sub_shield_double_occ_holds] below.  Δρ is ∅ here, so every state the
   walk reaches is [fa_clean].  The double-occurrence obstacle to
   [main_forall]'s supply is therefore retired.

   ⚙ (2026-08-05, later) [sub_shield] itself is now DELETED — it had become a
   synonym for [flex_apart_p0], which is what P6-Ss and P6-L take.  The
   positive statement below is therefore phrased in that vocabulary.

   Coq text at commit `165746a`. *)

(** ⭐⭐ The positive statement, replacing the retraction above: the repair
    premise P6-Ss actually takes HOLDS at the double-occurrence
    configuration.  Δρ = ∅ here, so every state the P0-walk reaches is
    [fa_clean]. *)
Theorem p7_shield_double_occ_holds :
  flex_apart_p0 Θ0d empty P0d ψd.
Proof. apply flex_apart_p0_clean. clear; fsetdec. Qed.

(* ===================================================================== *)
(*  THE HEADLINE — every OTHER hypothesis of the ForallL row holds        *)
(* ===================================================================== *)

Theorem p7_double_occ_row_premises_all_hold :
  (* the completeness configuration … *)
  a_wf_aenv Θ0d /\
  Θ0d ⨟ empty ⊢ₚₛᵃ P0d /\
  Θ0d ⨟ empty ⊢ₚₛᵃ Pd /\
  a_ty_mode_compat (mode_fn mode_tc) P0d /\
  (guarded_pskl P0d \/ P0d = pskl_hole) /\
  uskl_ghost_free Rd /\
  ⌊ Rd ⌋ˢ = Pd /\
  κd ∷ Θ0d ⊑ Θ0d /\
  (Θ0d ⊢ Rd ≡ᵘ (msubst_uskl_syn κd Rd)) /\
  Θ0d ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qd) /\
  (* … the JOIN, reaching a ForallL node with the guess [ψd] … *)
  ad_pat_sub_gv 3 a_sub_mode_ty (mode_fn mode_tc) empty Θ0d Rd Qd /\
  a_tags_sort a_sub_mode_ty (singleton e) ψd /\
  (singleton e) ∩ empty [=] empty /\
  (singleton e) ∩ (ftag_in_uskl Rd) [=] empty /\
  Θ0d ⨟ empty ⊢ₚₛᵃ ⌊ ψd ⌋ˢ /\
  ad_pat_sub_gv 2 a_sub_mode_ty (mode_fn mode_tc)
    (empty `union` singleton e) Θ0d (open_uskl_wrt_uskl Rjd ψd) Qd /\
  (* … the FILL … *)
  ad_refine_syn_f empty Θ0d empty
    (pskl_to_bskl_inh (msubst_pskl κd P0d)) Qd /\
  (* … and the shield — the row's ONE remaining premise — HOLDS here
     (2026-08-05; it was FALSE before the guarded conjunct was retired, which
     is what this file used to record). *)
  flex_apart_p0 Θ0d empty P0d ψd.
Proof.
  repeat split;
    first [ apply Θ0d_wf | apply P0d_wf | apply Pd_wf | apply P0d_mode
          | left; apply P0d_guarded | apply Rd_ghost_free | apply inc_d
          | apply slack_d | apply Qd_wf | apply join_d | apply ψd_tags
          | apply ψd_erase_wf | apply join_premise_d | apply fill_d
          | exact p7_shield_double_occ_holds
          | unfold Rd, Rjd; simpl; clear - Het; fsetdec
          | clear; fsetdec ].
Qed.

End DoubleOccurrence.

Print Assumptions p7_shield_double_occ_holds.
Print Assumptions p7_double_occ_row_premises_all_hold.
Print Assumptions join_at_Rd_is_forall_l.
