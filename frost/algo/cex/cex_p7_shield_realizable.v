(** ⚠️ THE P7 SHIELD RESIDUAL IS REALIZABLE — [sub_shield] IS OVER-STRONG.

    [cex_p7_shield_forall_flex.v] settled the FALSITY half of TASK 0's
    residual: at a raw Θ0-flexible facing a TAGGED ∀ with a COMPOUND body,
    [flex_shield] — and hence [sub_shield] — is UNDERIVABLE.  What it left
    open (docs/DESIGN-completeness-subtyping.md §14) was REALIZABILITY:
    whether P7b's Sub-ForallL rows can actually be REACHED with such a
    [(P0, ψa)] pair and [ε ∈ Ψa].  **They can.**  This file exhibits the
    configuration and machine-checks every part of it.

    THE WITNESS.  [Θ0 = α̂], [κ = α̂ ↦ unit], [Θ = Θ0], and

      P0 = (∀γ. γ→γ) → α̂          a ∀ BELOW the head (the residual shape) AND
                                   a walk-reachable raw flexible
      R  = ∀^t. (□₀ → unit)        the subject: one tagged ∀
      ψa = ∀^e β. β→β              the guess — TAGGED, with a COMPOUND body
      Q  = (∀ᵢ. β→β) → unit        the counterpart

    WHY IT GOES THROUGH, and why the earlier ∀γ.γ probe did not.  The tag [e]
    has exactly one way to be discharged — [ad_pat_consis__forall_inh_tagged],
    a TAGGED ∀ in the subject facing an INHERITED ∀ in the counterpart — and
    the counterpart is fixed by the FILL, so [Q]'s inherited ∀ can only come
    from a ∀ in [P0].  Its BODY is therefore whatever [P0]'s ∀-body refines
    to.  With [P0 ⊇ ∀γ.γ] that body is a bare variable and the compound guess
    is stuck; with [P0 ⊇ ∀γ.γ→γ] it is an arrow and the guess goes through.
    So the residual is realized by the SAME shape that makes the shield false:
    a ∀ below the head, plus a walk-reachable raw flexible.

    WHAT THIS ESTABLISHES.  The P7c dispatcher cannot discharge [sub_shield]:
    at this node the join can ONLY have ended with [__forall_l_tagged]
    ([join_at_Rw_is_forall_l]), so the ForallL row must be applied, and its
    shield premise is FALSE ([shield_w_fails]).

    ⚠️ WHAT IT DOES **NOT** ESTABLISH.  It does NOT refute P6-Ss, P6-Sv or
    thm:complete-subtyping.  [sub_shield] is a MECH-INVENTED repair premise
    (P6-Sv's; prop_look_complete_sub_cstr.v), not a paper statement, so
    nothing goes to docs/PAPER-GAPS.md.  What is refuted is its INDEXING: it
    pairs EVERY walk-reachable [P0]-part with the WHOLE guess, while the
    derivation aligns [ψa] with ONE position — here the arrow's DOMAIN, facing
    the inherited ∀ of [Q], where the tag is legitimately discharged — and the
    shield is demanded at the CODOMAIN, a raw flexible that guess never meets.
    The repair is a POSITIONAL re-indexing, replayed through P6-Ss and P7b's
    two ForallL rows, which consume the current shape.  ⚠️ Trimming the
    [ss_walk] closure instead is not available: P6-Ss's Sub-Arrow row consumes
    it directly (prop_look_complete_sub_cstr.v:1546-1548). *)

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

(* ===================================================================== *)
(*  THE WITNESS                                                           *)
(* ===================================================================== *)

Section Realizable.

Variables f e t : atom.
Hypothesis Het : e <> t.

Definition Θ0w : aenv := f ~ abind_flex_mono.

(* the guess: a TAGGED ∀ with a COMPOUND body — the shape [flex_shield]
   cannot cover opposite a raw flexible *)
Definition ψw : uskl := cexψ e.

(* [P0 = (∀γ. γ→γ) → α̂] : a ∀ BELOW the head (TASK 0's residual shape) AND a
   walk-reachable raw flexible in the codomain *)
Definition P0w : pskl :=
  pskl_arrow (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
             (pskl_var_f f).

Definition Rjw : uskl := uskl_arrow (uskl_var_b 0) uskl_unit.
Definition Rw : uskl := uskl_all_etag t Rjw.
Definition Qw : bskl :=
  bskl_arrow (bskl_all_inh (bskl_arrow (bskl_var_b 0) (bskl_var_b 0)))
             bskl_unit.
Definition κw : metasubst := (f, ptyp_unit) :: nil.

Lemma Θ0w_wf : a_wf_aenv Θ0w.
Proof. apply a_wf_aenv__flex; [ simpl; clear; fsetdec | apply a_wf_aenv__nil ]. Qed.

Lemma P0w_wf : Θ0w ⨟ empty ⊢ₚₛᵃ P0w.
Proof.
  apply a_wf_pskl__arrow.
  - apply a_wf_pskl__all with (L := empty). intros α _.
    unfold open_pskl_wrt_pskl; simpl.
    apply a_wf_pskl__arrow; apply a_wf_pskl__var; left; clear; fsetdec.
  - apply a_wf_pskl__var. right. right. left. unfold binds; simpl. auto.
Qed.

(* --------------------------------------------------------------------- *)
(*  (1) THE GUESS IS A LEGAL ForallL GUESS                                *)
(* --------------------------------------------------------------------- *)

Lemma ψw_tags : a_tags_sort a_sub_mode_ty (singleton e) ψw.
Proof.
  unfold ψw, cexψ.
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

Lemma ψw_erase_wf : Θ0w ⨟ empty ⊢ₚₛᵃ ⌊ ψw ⌋ˢ.
Proof.
  unfold ψw, cexψ; simpl.
  apply a_wf_pskl__all with (L := empty). intros α _.
  unfold open_pskl_wrt_pskl; simpl.
  apply a_wf_pskl__arrow; apply a_wf_pskl__var; left; clear; fsetdec.
Qed.

(* --------------------------------------------------------------------- *)
(*  (2) THE JOIN — the ForallL node is REACHED, and the tag [e] is         *)
(*      DISCHARGED by the consistency leaf under the arrow's domain        *)
(* --------------------------------------------------------------------- *)

Lemma consis_w :
  (singleton e) ⨟ Θ0w ⊢ₛᵃ ψw
    ∼ (bskl_all_inh (bskl_arrow (bskl_var_b 0) (bskl_var_b 0))).
Proof.
  unfold ψw, cexψ.
  apply ad_pat_consis__forall_inh_tagged with (L := empty) (Ψ0 := empty);
    [ | clear; fsetdec ].
  intros α _. unfold open_uskl_wrt_uskl, open_bskl_wrt_bskl; simpl.
  apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
    [ | | clear; fsetdec ];
    (apply ad_pat_consis__var;
     [ clear; fsetdec | left; unfold binds; simpl; auto ]).
Qed.

Lemma refine_dom_w :
  Θ0w ⨟ empty ⊢ᵣₚᵃ ⌊ ψw ⌋ˢ
    ⊳ (bskl_to_pskl (bskl_all_inh (bskl_arrow (bskl_var_b 0) (bskl_var_b 0)))).
Proof.
  unfold ψw, cexψ; simpl.
  apply ad_refine_pskl__all with (L := empty). intros α _.
  unfold open_pskl_wrt_pskl; simpl.
  apply ad_refine_pskl__arrow; apply ad_refine_pskl__var; left; clear; fsetdec.
Qed.

Lemma join_cod_w :
  ad_pat_sub_gv 0 a_sub_mode_ty mode_tc empty Θ0w uskl_unit bskl_unit.
Proof.
  apply ad_pat_sub_gv__check with (B := pskl_unit);
    [ apply guarded_uskl__unit
    | apply guarded_pskl__unit
    | apply ad_pat_consis__unit; clear; fsetdec
    | simpl; apply ad_refine_pskl__unit ].
Qed.

Lemma join_w :
  ad_pat_sub_gv 2 a_sub_mode_ty (mode_fn mode_tc) empty Θ0w Rw Qw.
Proof.
  unfold Rw, Qw.
  apply ad_pat_sub_gv__forall_l_tagged
    with (Ψ' := singleton e) (ψ := ψw);
    [ discriminate
    | clear; fsetdec
    | unfold Rjw; simpl; clear - Het; fsetdec
    | apply ψw_tags
    | apply ψw_erase_wf
    | ].
  unfold Rjw, open_uskl_wrt_uskl; simpl.
  apply ad_pat_sub_gv__arrow
    with (Ψ1 := singleton e) (Ψ2 := empty);
    [ apply consis_w | apply refine_dom_w | apply join_cod_w
    | clear; fsetdec ].
Qed.

(* --------------------------------------------------------------------- *)
(*  (3) THE FILL, and the rest of the completeness configuration          *)
(* --------------------------------------------------------------------- *)

Definition Pw : pskl := ⌊ Rw ⌋ˢ.

Lemma msubst_P0w : pskl_to_bskl_inh (msubst_pskl κw P0w) = Qw.
Proof.
  unfold κw, P0w, Qw; simpl.
  match goal with
  | |- context [if ?c then _ else _] => destruct c as [_ | n0]
  end; [ reflexivity | exfalso; apply n0; reflexivity ].
Qed.

Lemma fill_w :
  ad_refine_syn_f empty Θ0w empty (pskl_to_bskl_inh (msubst_pskl κw P0w)) Qw.
Proof.
  rewrite msubst_P0w. unfold Qw.
  apply ad_refine_syn_f__arrow; [ | apply ad_refine_syn_f__unit ].
  apply ad_refine_syn_f__all with (L := empty). intros α _.
  unfold open_bskl_wrt_bskl; simpl.
  apply ad_refine_syn_f__arrow;
    apply ad_refine_syn_f__var; left; clear; fsetdec.
Qed.

Lemma inc_w : κw ∷ Θ0w ⊑ Θ0w.
Proof.
  unfold κw, Θ0w.
  apply a_inc__flex;
    [ apply a_inc__empty;
        apply a_suffix__cons;
          [ apply a_suffix__nil | apply a_suffix_binding__flex_mono ]
    | apply a_wf_ptyp__unit
    | apply mono_ptyp__unit ].
Qed.

Lemma lc_Rw : lc_uskl Rw.
Proof.
  unfold Rw, Rjw.
  apply lc_uskl_all_etag_exists with (α1 := f).
  unfold open_uskl_wrt_uskl; simpl.
  apply lc_uskl_arrow; [ apply lc_uskl_var_f | apply lc_uskl_unit ].
Qed.

Lemma slack_w : Θ0w ⊢ Rw ≡ᵘ (msubst_uskl_syn κw Rw).
Proof.
  replace (msubst_uskl_syn κw Rw) with Rw by reflexivity.
  apply a_uskl_tyequiv_refl. apply lc_Rw.
Qed.

Lemma Pw_wf : Θ0w ⨟ empty ⊢ₚₛᵃ Pw.
Proof.
  unfold Pw, Rw, Rjw; simpl.
  apply a_wf_pskl__all with (L := empty). intros α _.
  unfold open_pskl_wrt_pskl; simpl.
  apply a_wf_pskl__arrow;
    [ apply a_wf_pskl__var; left; clear; fsetdec | apply a_wf_pskl__unit ].
Qed.

Lemma Qw_wf : Θ0w ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qw).
Proof.
  unfold Qw; simpl.
  apply a_wf_pskl__arrow; [ | apply a_wf_pskl__unit ].
  apply a_wf_pskl__all with (L := empty). intros α _.
  unfold open_pskl_wrt_pskl; simpl.
  apply a_wf_pskl__arrow; apply a_wf_pskl__var; left; clear; fsetdec.
Qed.

Lemma P0w_mode : a_ty_mode_compat (mode_fn mode_tc) P0w.
Proof.
  unfold P0w.
  apply a_ty_mode_compat__fn.
  change (pskl_var_f f) with (ptyp_to_pskl (ptyp_var_f f)).
  apply a_ty_mode_compat__tc.
Qed.

Lemma P0w_guarded : guarded_pskl P0w.
Proof.
  unfold P0w. apply guarded_pskl__arrow; [ | apply lc_pskl_var_f ].
  apply lc_pskl_all_syn_exists with (α1 := f).
  unfold open_pskl_wrt_pskl; simpl.
  apply lc_pskl_arrow; apply lc_pskl_var_f.
Qed.

Lemma Rw_ghost_free : uskl_ghost_free Rw.
Proof.
  unfold Rw, Rjw.
  apply uskl_ghost_free__all_etag with (L := empty). intros α _.
  unfold open_uskl_wrt_uskl; simpl.
  apply uskl_ghost_free__arrow;
    [ apply uskl_ghost_free__var | apply uskl_ghost_free__unit ].
Qed.

(* --------------------------------------------------------------------- *)
(*  (4) …AND THE NON-POSITIONAL OBLIGATION IS FALSE THERE                 *)
(*                                                                        *)
(*  ⚠️ HISTORY.  Until 2026-08-03 [sub_shield] was indexed by [P0] ALONE   *)
(*  and demanded BOTH its closures at every walk-reachable P0-part against *)
(*  the WHOLE guess.  One [sss_arrow_r] step reaches [P0 = α̂] here, and    *)
(*  BOTH obligations are false at that leaf — which is what this file was  *)
(*  written to show.  The premise has since been re-indexed POSITIONALLY   *)
(*  (DESIGN §14.3), so the old statement can no longer even be written;    *)
(*  what survives verbatim, and is the whole of its content, is that the   *)
(*  two guess-DESCENDING closures fail at the codomain.                   *)
(* --------------------------------------------------------------------- *)

Lemma binds_f_w : binds f abind_flex_mono Θ0w.
Proof. unfold binds; simpl; auto. Qed.

Lemma e_in_w : e `in` (singleton e).
Proof. clear; fsetdec. Qed.

(** the [flex_shield] half, at the CODOMAIN the old indexing reached *)
Lemma shield_w_codomain_fails : forall Δρ,
  ~ flex_shield Θ0w (singleton e) Δρ (pskl_var_f f) ψw.
Proof.
  intros Δρ Hfsh.
  exact (flex_shield_raw_flex_tagged_arrow_stuck
           (Θ0 := Θ0w) (Ψ' := singleton e) (Δρ := Δρ) (f := f) (e := e)
           binds_f_w e_in_w Hfsh).
Qed.

(* the stuck [flex_apart] leaf: a raw flexible against an OPENED tagged
   guess whose body is compound *)
Lemma flex_apart_raw_flex_open_arrow_stuck : forall Δρ (β : atom),
  β `in` Δρ ->
  ~ flex_apart Θ0w Δρ (pskl_var_f f)
      (uskl_arrow (uskl_var_f β) (uskl_var_f β)).
Proof.
  intros Δρ β Hβ Hfa.
  assert (Hfl : a_flex_tvar Θ0w f) by (left; unfold binds; simpl; auto).
  inversion Hfa; subst.
  - (* fa_clean : β is in Δρ, and it is free in the guess *)
    match goal with H : _ ∩ _ [=] empty |- _ =>
      simpl in H; clear - H Hβ; fsetdec end.
  - (* fa_var_rigid : [f] is FLEXIBLE in Θ0w, not rigid *)
    match goal with H : binds _ abind_tvar _ |- _ =>
      unfold binds in H; simpl in H;
      destruct H as [Hc | Hc]; [ inversion Hc | contradiction ] end.
  - (* fa_flexfree : [f] is a raw flexible of Θ0w *)
    match goal with H : pskl_flex_free _ _ |- _ =>
      apply (H f ltac:(simpl; clear; fsetdec)); exact Hfl end.
Qed.

(** …and the [flex_apart_walk] half, at the same leaf: one [fastep_all_r]
    opens the guess into [β→β] at [β ∈ Δρ], where nothing applies. *)
Lemma apart_w_codomain_fails : forall Δρ,
  ~ flex_apart_walk Θ0w Δρ (pskl_var_f f) ψw.
Proof.
  intros Δρ Hfa.
  pick fresh β for (empty : atoms).
  assert (Hw : fa_walk (dom Θ0w) Δρ (pskl_var_f f) ψw
                 (add β Δρ) (pskl_var_f f)
                 (uskl_arrow (uskl_var_f β) (uskl_var_f β))).
  { unfold ψw, cexψ.
    eapply fw_step; [ apply fastep_all_r | ].
    unfold open_uskl_wrt_uskl; simpl. apply fw_refl. }
  pose proof (Hfa _ _ _ Hw) as Hleaf.
  (* ⚙ evar-free on purpose: [eapply] here would leave [Δρ] and [β] open and
     the [β ∈ Δρ] side goal would go to [fsetdec] WITH EVARS, which diverges *)
  assert (Hβin : β `in` add β Δρ) by (clear; fsetdec).
  exact (flex_apart_raw_flex_open_arrow_stuck Hβin Hleaf).
Qed.

(* --------------------------------------------------------------------- *)
(*  (5) …AND THE DISPATCHER HAS NO OTHER RULE TO TAKE THERE                *)
(* --------------------------------------------------------------------- *)

(** At this node the join can ONLY have ended with [__forall_l_tagged]:
    [__infer] wants [mode_ti], [__check] and [__univ_ghost_r] want a GUARDED
    subject (a ∀ is not), [__forall_r] and [__univ_ghost_r] want a ∀-inh /
    tophole counterpart (this one is an arrow), and every remaining row wants
    another subject shape.  So the completeness dispatcher must apply the
    ForallL row here — and that row's [sub_shield] premise is false. *)
Lemma join_at_Rw_is_forall_l : forall n NM M Ψ,
  ad_pat_sub_gv n NM M Ψ Θ0w Rw Qw ->
  M <> mode_ti ->
  exists n0 Ψ' ψ,
    n = S n0 /\
    a_tags_sort NM Ψ' ψ /\
    ad_pat_sub_gv n0 NM M (Ψ `union` Ψ') Θ0w (open_uskl_wrt_uskl Rjw ψ) Qw.
Proof.
  intros n NM M Ψ H Hm; unfold Rw, Qw in H; inversion H; subst;
    try solve [ (* infer : the mode *) exfalso; apply Hm; reflexivity
              | (* check / univ_ghost_r : the subject is a ∀ *)
                match goal with Hg : guarded_uskl _ |- _ => inversion Hg end ].
  (* forall_l_tagged : the survivor *)
  do 3 eexists; split; [ reflexivity | split; eassumption ].
Qed.

Lemma join_premise_w :
  ad_pat_sub_gv 1 a_sub_mode_ty (mode_fn mode_tc)
    (empty `union` singleton e) Θ0w (open_uskl_wrt_uskl Rjw ψw) Qw.
Proof.
  unfold Rjw, open_uskl_wrt_uskl, Qw; simpl.
  apply ad_pat_sub_gv__arrow with (Ψ1 := singleton e) (Ψ2 := empty);
    [ apply consis_w | apply refine_dom_w | apply join_cod_w
    | clear; fsetdec ].
Qed.

(* ===================================================================== *)
(*  THE HEADLINE — THE NON-POSITIONAL INDEXING IS OVER-STRONG             *)
(* ===================================================================== *)

(** Every input of P7b's completeness motive is inhabited here, the join ends
    at a ForallL node with this guess, no other rule can be taken there — and
    at the CODOMAIN the two guess-descending closures both fail.  The old,
    P0-only [sub_shield] demanded exactly those, one [sss_arrow_r] step away,
    so it could not be discharged by the P7c dispatcher.

    ⚠️ This does NOT refute P6-Ss or thm:complete-subtyping: [sub_shield] is a
    MECH-INVENTED repair premise (P6-Sv's), not a paper statement.  What it
    shows is that the premise was indexed NON-POSITIONALLY — it paired EVERY
    walk-reachable [P0]-part with the WHOLE guess, and here the derivation
    aligns [ψa] with the arrow's DOMAIN (facing the inherited ∀ of [Q], where
    its tag is legitimately discharged by [ad_pat_consis__forall_inh_tagged])
    while the shield was demanded at the CODOMAIN, a raw flexible that has
    nothing to do with that guess.  ⭐ The repair holds AT THIS VERY
    CONFIGURATION — [p7_sub_shield_repaired_holds] below. *)
Theorem p7_sub_shield_is_over_strong :
  (* the completeness configuration … *)
  a_wf_aenv Θ0w /\
  Θ0w ⨟ empty ⊢ₚₛᵃ P0w /\
  Θ0w ⨟ empty ⊢ₚₛᵃ Pw /\
  a_ty_mode_compat (mode_fn mode_tc) P0w /\
  (guarded_pskl P0w \/ P0w = pskl_hole) /\
  uskl_ghost_free Rw /\
  ⌊ Rw ⌋ˢ = Pw /\
  κw ∷ Θ0w ⊑ Θ0w /\
  (Θ0w ⊢ Rw ≡ᵘ (msubst_uskl_syn κw Rw)) /\
  Θ0w ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qw) /\
  (* … the JOIN, reaching a ForallL node with the guess [ψw] … *)
  ad_pat_sub_gv 2 a_sub_mode_ty (mode_fn mode_tc) empty Θ0w Rw Qw /\
  a_tags_sort a_sub_mode_ty (singleton e) ψw /\
  (singleton e) ∩ empty [=] empty /\
  (singleton e) ∩ (ftag_in_uskl Rw) [=] empty /\
  Θ0w ⨟ empty ⊢ₚₛᵃ ⌊ ψw ⌋ˢ /\
  ad_pat_sub_gv 1 a_sub_mode_ty (mode_fn mode_tc)
    (empty `union` singleton e) Θ0w (open_uskl_wrt_uskl Rjw ψw) Qw /\
  (* … the FILL … *)
  ad_refine_syn_f empty Θ0w empty
    (pskl_to_bskl_inh (msubst_pskl κw P0w)) Qw /\
  (* … and BOTH guess-descending closures fail at the CODOMAIN, which is
     one [ss_walk] step from the root and which the OLD indexing paired
     with this whole guess. *)
  (forall Δρ, ~ flex_shield Θ0w (singleton e) Δρ (pskl_var_f f) ψw) /\
  (forall Δρ, ~ flex_apart_walk Θ0w Δρ (pskl_var_f f) ψw).
Proof.
  repeat split;
    first [ apply Θ0w_wf | apply P0w_wf | apply Pw_wf | apply P0w_mode
          | left; apply P0w_guarded | apply Rw_ghost_free | apply inc_w
          | apply slack_w | apply Qw_wf | apply join_w | apply ψw_tags
          | apply ψw_erase_wf | apply join_premise_w | apply fill_w
          | apply shield_w_codomain_fails
          | apply apart_w_codomain_fails
          | unfold Rw, Rjw; simpl; clear - Het; fsetdec
          | clear; fsetdec ].
Qed.

(* ===================================================================== *)
(*  ⭐⭐ THE REPAIR, AT THIS VERY CONFIGURATION                             *)
(*                                                                        *)
(*  The POSITIONAL premise (DESIGN §14.3) holds where the old one fails.   *)
(*  Two independent things do the work, and the file checks BOTH:          *)
(*                                                                        *)
(*   · Part A — the walk steps [P0] and the SUBJECT in lockstep and the    *)
(*     guess-descending closures are demanded only where [α ∈ ftv R'].     *)
(*     P7b's ForallL row hands P6-L the subject [open Rjw α = α → unit],   *)
(*     so ONE [sss_arrow_r] step reaches the codomain — where the subject  *)
(*     is [unit], the guard FAILS, and the false obligation above is never *)
(*     raised.                                                            *)
(*   · Part B — [fa_step] no longer carries the guess-fixed P0 arrow       *)
(*     descents, so the ROOT obligation is satisfiable too.  With them the *)
(*     root fails as well (compose [fastep_p0_arrow_r] with               *)
(*     [fastep_all_r]), which is why the guard alone was not enough.       *)
(* ===================================================================== *)

(** Guesses reachable after the root's [fastep_all_r] carry no ε-tagged ∀:
    the only [uskl_all_etag] in play is [ψw], and every later guess is a
    SUBTERM of an opened one or a monotype PAINTING. *)
Fixpoint etag_free_w (R : uskl) : Prop :=
  match R with
  | uskl_arrow R1 R2 => etag_free_w R1 /\ etag_free_w R2
  | uskl_all_syn R0 => etag_free_w R0
  | uskl_all_etag _ _ => False
  | uskl_tophole R0 => etag_free_w R0
  | uskl_topholeg R0 => etag_free_w R0
  | _ => True
  end.

Lemma etag_free_w_painting : forall A, etag_free_w (ptyp_to_uskl_syn A).
Proof.
  intros A. unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  induction A; simpl in *; auto.
Qed.

(** The [fa_arrow] / [fa_rho_var] skeleton: every leaf of the guess is a
    Δρ-variable and its arrow spine matches P0's. *)
Inductive rho_shape_w (Δρ : atoms) : pskl -> uskl -> Prop :=
| rsw_var : forall P0 α, α `in` Δρ -> rho_shape_w Δρ P0 (uskl_var_f α)
| rsw_arrow : forall P1 P2 ψ1 ψ2,
    rho_shape_w Δρ P1 ψ1 -> rho_shape_w Δρ P2 ψ2 ->
    rho_shape_w Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2).

Definition INVw (Δρ : atoms) (P0 : pskl) (ψa : uskl) : Prop :=
  etag_free_w ψa /\
  ((ftvar_in_uskl ψa) ∩ Δρ [=] empty \/ rho_shape_w Δρ P0 ψa).

Lemma INVw_flex_apart : forall Θ0 Δρ P0 ψa,
  INVw Δρ P0 ψa -> flex_apart Θ0 Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa [_ [Hcl | Hrs]]; [ apply fa_clean; assumption | ].
  induction Hrs; [ apply fa_rho_var; assumption | apply fa_arrow; assumption ].
Qed.

Lemma INVw_step : forall A Δρ P0 ψa Δρ1 P1 ψ1,
  INVw Δρ P0 ψa -> fa_step A Δρ P0 ψa Δρ1 P1 ψ1 -> INVw Δρ1 P1 ψ1.
Proof.
  intros A Δρ P0 ψa Δρ1 P1 ψ1 [Hef Hd] Hs.
  destruct Hs.
  - (* arrow_l *)
    simpl in Hef. split; [ tauto | ]. destruct Hd as [Hcl | Hrs].
    + left. simpl in Hcl. clear - Hcl; fsetdec.
    + right. inversion Hrs; subst; assumption.
  - (* arrow_r *)
    simpl in Hef. split; [ tauto | ]. destruct Hd as [Hcl | Hrs].
    + left. simpl in Hcl. clear - Hcl; fsetdec.
    + right. inversion Hrs; subst; assumption.
  - (* all_l : the guess does not move *)
    split; [ exact Hef | ]. destruct Hd as [Hcl | Hrs].
    + left; exact Hcl.
    + right. inversion Hrs; subst. apply rsw_var; assumption.
  - (* all_r : VACUOUS — an ε-tagged ∀ is not [etag_free_w] *)
    simpl in Hef; contradiction.
  - (* tophole_l : the guess does not move *)
    split; [ exact Hef | ]. destruct Hd as [Hcl | Hrs].
    + left; exact Hcl.
    + right. inversion Hrs; subst. apply rsw_var; assumption.
  - (* topholeg_r *)
    simpl in Hef. split; [ exact Hef | ]. destruct Hd as [Hcl | Hrs].
    + left. simpl in Hcl. exact Hcl.
    + inversion Hrs.
  - (* flexdef_r : the new guess is a Δρ-clean PAINTING *)
    split; [ apply etag_free_w_painting | left; assumption ].
Qed.

Lemma INVw_walk : forall A Δρ P0 ψa Δρ' P0' ψa',
  fa_walk A Δρ P0 ψa Δρ' P0' ψa' -> INVw Δρ P0 ψa -> INVw Δρ' P0' ψa'.
Proof.
  intros A Δρ P0 ψa Δρ' P0' ψa' Hw; induction Hw; intros Hinv;
    [ exact Hinv | ].
  apply IHHw. eapply INVw_step; [ exact Hinv | exact H ].
Qed.

(** ⭐ PART B, machine-checked: the closure P6-Sv descends is SATISFIABLE at
    the root — at an ARBITRARY Δρ, which is what [sub_shield]'s own Δρ'
    quantifier hands it.  (With the guess-fixed P0 arrow descents this was
    FALSE: [fastep_p0_arrow_r] then [fastep_all_r] reach [(α̂, β→β)].) *)
Theorem apart_w_root_holds : forall Δρ, flex_apart_walk Θ0w Δρ P0w ψw.
Proof.
  intros Δρ Δρ' P0' ψa' Hw.
  inversion Hw as [ | Δρa P0a ψaa Δρ1 P1 ψ1 Δρ2 P2 ψ2 Hstep Hrest ]; subst.
  - (* the ROOT itself : the guess is CLOSED, so [fa_clean] at any Δρ *)
    apply fa_clean. unfold ψw, cexψ; simpl. clear; fsetdec.
  - (* the ONLY step from the root is [fastep_all_r] : [P0w] is an arrow and
       [ψw] an ε-tagged ∀, so no other constructor matches *)
    unfold P0w, ψw, cexψ in Hstep.
    inversion Hstep; subst.
    unfold open_uskl_wrt_uskl in Hrest; simpl in Hrest.
    eapply INVw_flex_apart.
    eapply INVw_walk; [ exact Hrest | ].
    split; [ simpl; tauto | ].
    right. apply rsw_arrow; apply rsw_var; clear; fsetdec.
Qed.

Theorem apart_p0_w_root_holds : forall Δρ, flex_apart_p0 Θ0w Δρ P0w ψw.
Proof.
  intros Δρ P0' _. apply fa_clean.
  unfold ψw, cexψ; simpl. clear; fsetdec.
Qed.

(** …and the shield half at the root, which §14.2 predicted: [fsh_all_r]
    opens the guess to [γ→γ] at [add γ Δρ], [fsh_arrow] splits it against
    [(∀γ.γ→γ) → α̂], and both sides close by [fsh_rho_var]. *)
Theorem shield_w_root_holds : forall Δρ,
  flex_shield Θ0w (singleton e) Δρ P0w ψw.
Proof.
  intros Δρ. unfold P0w, ψw, cexψ.
  apply fsh_all_r with (L := empty). intros γ _.
  unfold open_uskl_wrt_uskl; simpl.
  apply fsh_arrow; apply fsh_rho_var; clear; fsetdec.
Qed.

(* --------------------------------------------------------------------- *)
(*  …and PART A: the guard leaves EXACTLY the root.                        *)
(* --------------------------------------------------------------------- *)

Lemma ss_walk_w_stuck : forall α P0' R',
  ss_walk (dom Θ0w) α (pskl_var_f f) uskl_unit P0' R' ->
  P0' = pskl_var_f f /\ R' = uskl_unit.
Proof.
  intros α P0' R' Hw. inversion Hw; subst; [ auto | ].
  match goal with H : ss_step _ _ _ _ _ _ |- _ => inversion H end.
Qed.

Lemma ss_walk_w_inv : forall α P0' R',
  ss_walk (dom Θ0w) α P0w (open_uskl_wrt_uskl Rjw (uskl_var_f α)) P0' R' ->
  (P0' = P0w /\ R' = open_uskl_wrt_uskl Rjw (uskl_var_f α))
  \/ (P0' = pskl_var_f f /\ R' = uskl_unit).
Proof.
  intros α P0' R' Hw. unfold Rjw, open_uskl_wrt_uskl in Hw; simpl in Hw.
  inversion Hw as [ | Pa Ra P1 R1 P2 R2 Hstep Hrest ]; subst;
    [ left; unfold Rjw, open_uskl_wrt_uskl; simpl; auto | ].
  unfold P0w in Hstep. inversion Hstep; subst.
  right. eapply ss_walk_w_stuck; exact Hrest.
Qed.

(** ⭐⭐ THE DECISIVE CHECK.  With the positional index AND the split walk, the
    WHOLE repaired premise — in exactly the form P7b's ForallL rows now take
    ([a_sub_complete_forall_l_tagged]) — HOLDS at the configuration that
    refutes the old one. *)
Theorem p7_sub_shield_repaired_holds : forall α,
  sub_shield Θ0w (singleton e) empty α P0w
    (open_uskl_wrt_uskl Rjw (uskl_var_f α)) ψw.
Proof.
  intros α P0' R' Δρ' Hw Hle Hcl.
  destruct (ss_walk_w_inv Hw) as [[-> ->] | [-> ->]].
  - split; [ apply apart_p0_w_root_holds | intros _ ].
    apply apart_w_root_holds.
  - (* the CODOMAIN, where the OLD premise is false: the P0-only closure
       still holds (it never descends the guess), and the two that DO
       descend it are not demanded — the guard [α ∈ ftv unit] is unmet *)
    split.
    + intros P0'' _. apply fa_clean.
      unfold ψw, cexψ; simpl. clear; fsetdec.
    + simpl. intros Hα. clear - Hα; fsetdec.
Qed.

End Realizable.

Print Assumptions p7_sub_shield_is_over_strong.
Print Assumptions join_at_Rw_is_forall_l.
Print Assumptions p7_sub_shield_repaired_holds.
