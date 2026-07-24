(** COUNTEREXAMPLE (P6, 2026-07-24): the -var completeness lemmas of the
    constraint cluster —
    [lemma:complete-consistency-constraint-collection-solving-var]
    (consistency-proofs.tex:1181) and its subtyping twin
    [lemma:complete-constraint-collection-solving-var]
    (subtyping-proofs.tex:1696) — are FALSE AS STATED when the solve
    counterpart [P0] is a FLEXIBLE VARIABLE of [Θ0] (θ-pinned) whose image
    collides with a ρ-substituted (leaf) position of [ψa].

    THE CONFIGURATION.  Take
      Θ0 = X~tvar, α̂~flex        Θ = X~tvar        θ = [α̂ ↦ unit→unit]
      ψa = X → unit               ρ = [X ↦ unit]    (so ρ(ψa) = unit→unit)
      P_i = X → unit              P_0 = α̂           Q = unit → unit
    with Δ = Δρ = {X} and every tag set empty.  ALL premises of the -var
    lemma hold (machine-checked below): the wf premises, θ ∷ Θ0 ⊑ Θ, the
    tag-sort of ψa, the ρ-relation with its freshness pack (X rigid in Θ,
    absent from θ's images, Θ's definition images, P_i's ⊤◇-bodies, and
    ftv(P_0)), the precision premise θP_i ⊑ᵖ[·] ψa, the consistency premise
    for ρ(ψa) against Q, the refinement premise inh{θP_0} ⊳ Q — and the
    paper's positional side condition (P_i has the rigid X exactly at the
    ρ-substituted position).

    THE REFUTATION.  The only solve rule applicable to
    [solveeq{X→unit}{α̂}{·}] is FlexR, forcing P_a = α̂.  The conclusion
    demands  Θ ⨟ Δ ⊢ θa(α̂) ⊑ᵖ[Ψi,Ψa] ψa  with θ ≡ θa over Θ0, which pins
    θa(α̂) ≡ᵗ unit→unit; at Θ = X~tvar (definition-free) the equivalence is
    syntactic, so the required precision is
        (unit→unit) ⊑ᵖ (X → unit),
    underivable: its function-argument obligation is [unit ⊑ᵖ var X] with X
    RIGID, and no partial-precision rule matches (the var rule needs the
    occurrence, flex_r needs a defined flexible).  Machine-checked below for
    ARBITRARY θa, Δ and tag set.

    ROOT CAUSE.  The paper's case analyses recover P_0's shape by inversion
    on the refinement premise [Θ ⊢ inh{θP_0} ⊳ Q] — but that inversion also
    admits P_0 = flexible variable (whose θ-image supplies the matching
    constructor), a subcase no completeness proof case covers: the
    algorithm's own rule for flexible counterparts, LE-FlexR
    (fig:poly-info-extraction), is never invoked in the completeness
    appendices.  At the level of the non-var lemmas
    (consistency-proofs.tex:920 / subtyping-proofs.tex:2202) a flexible
    counterpart CAN be handled — LE-FlexR replaces the constraint payload by
    a FRESH γ̂ ∈ Ξc, and θa (which extends θ to Ξc there) is free to map γ̂
    to a ψa-refining monotype (when one exists; when ψa is not
    mono-paintable the premises are vacuous).  But the -var lemmas have
    Ξc = · and θa ≡ θ on ALL of Θ0, so a flexible P_0 with a θ-image that
    is "wrong" at a ρ-leaf position refutes the statement outright.

    STATUS: paper-level statement problem (a missing premise or a missing
    LE-FlexR-style repair), NOT a mech encoding slip — the mech solve rules
    are faithful on this configuration (the solve gets stuck / loses the
    rigid-variable information exactly as the paper's rules do).  Reported
    via docs/PAPER-GAPS.md; P6 is blocked on the resolution.

    Everything below is Qed and axiom-free. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_look_complete.

Set Implicit Arguments.

(* ===================================================================== *)
(*  ≡ᵗ over a definition-free context is syntactic identity.              *)
(* ===================================================================== *)

Lemma a_tyequiv_def_free_eq : forall Θ A B,
  Θ ⊢ A ≡ᵗ B ->
  (forall α τ, ~ binds α (abind_flex_mono_def τ) Θ) ->
  A = B.
Proof.
  intros Θ A B H; induction H; intros Hdf.
  - reflexivity.
  - symmetry; auto.
  - rewrite (IHa_tyequiv1 Hdf); auto.
  - exfalso; eapply Hdf; eassumption.
  - rewrite (IHa_tyequiv1 Hdf); rewrite (IHa_tyequiv2 Hdf); reflexivity.
  - f_equal.
    pick fresh Y for
      (L `union` ftvar_in_ptyp A `union` ftvar_in_ptyp B).
    apply (open_ptyp_wrt_ptyp_inj _ _ Y);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | ].
    apply H0; [ clear - Fr; fsetdec | exact Hdf ].
Qed.

(* ===================================================================== *)
(*  Equivalent increments have ≡ᵗ-equivalent images on every flexible.     *)
(* ===================================================================== *)

Lemma a_inc_equiv_flex_pin : forall Θ0 ρ1 ρ2 Θ',
  a_inc_equiv Θ0 ρ1 ρ2 Θ' ->
  forall α, binds α abind_flex_mono Θ0 ->
  Θ' ⊢ (msubst_lookup ρ1 α) ≡ᵗ (msubst_lookup ρ2 α).
Proof.
  intros Θ0 ρ1 ρ2 Θ' H; induction H; intros β Hb.
  - inversion Hb.
  - destruct (β == α) as [Heq | Hne0]; simpl.
    + destruct (β == α); [ assumption | contradiction ].
    + destruct (β == α); [ contradiction | ].
      apply IHa_inc_equiv.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq' _] | Hb'];
        [ exfalso; exact (Hne0 Heq') | exact Hb' ].
  - destruct (β == α) as [Heq | Hne0]; simpl.
    + destruct (β == α); [ assumption | contradiction ].
    + destruct (β == α); [ contradiction | ].
      apply IHa_inc_equiv.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq' _] | Hb'];
        [ exfalso; exact (Hne0 Heq') | exact Hb' ].
  - eapply a_tyequiv_weaken;
      [ intros y b Hby; apply binds_app_3; apply binds_app_3; exact Hby | ].
    apply IHa_inc_equiv.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
      [ discriminate Habs | exact Hb' ].
  - eapply a_tyequiv_weaken;
      [ intros y b Hby; apply binds_app_3; apply binds_app_3; exact Hby | ].
    apply IHa_inc_equiv.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
      [ discriminate Habs | exact Hb' ].
  - eapply a_tyequiv_weaken;
      [ intros y b Hby; apply binds_app_3; apply binds_app_3; exact Hby | ].
    apply IHa_inc_equiv.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
      [ discriminate Habs | exact Hb' ].
Qed.

Section CexP6FlexCounterpart.

Variables X alpha : atom.
Hypothesis Hne : X <> alpha.

(* The configuration. *)
Definition cexΘ0 : aenv :=
  (X ~ abind_tvar) ++ (alpha ~ abind_flex_mono) ++ nil.
Definition cexΘ : aenv := (X ~ abind_tvar) ++ nil.
Definition cexτ : ptyp := ptyp_arrow ptyp_unit ptyp_unit.
Definition cexθ : metasubst := (alpha, cexτ) :: nil.
Definition cexψa : uskl := uskl_arrow (uskl_var_f X) uskl_unit.
Definition cexψsub : uskl := uskl_arrow uskl_unit uskl_unit.
Definition cexPi : pskl := pskl_arrow (pskl_var_f X) pskl_unit.
Definition cexP0 : pskl := pskl_var_f alpha.
Definition cexQ : bskl := bskl_arrow bskl_unit bskl_unit.

(* ------------------------------------------------------------------ *)
(*  The premises of the -var lemma, each machine-checked.              *)
(* ------------------------------------------------------------------ *)

Lemma cex_wf_env0 : a_wf_aenv cexΘ0.
Proof.
  apply a_wf_aenv__tvar; simpl.
  - clear - Hne; fsetdec.
  - apply a_wf_aenv__flex; simpl; [ fsetdec | apply a_wf_aenv__nil ].
Qed.

Lemma cex_wf_env : a_wf_aenv cexΘ.
Proof.
  apply a_wf_aenv__tvar; simpl; [ fsetdec | apply a_wf_aenv__nil ].
Qed.

Lemma cex_inc : cexθ ∷ cexΘ0 ⊑ cexΘ.
Proof.
  apply (a_inc__tvar (Ξ := nil)); [ | apply a_suffix__nil ].
  apply a_inc__flex.
  - apply a_inc__empty; apply a_suffix__nil.
  - apply a_wf_ptyp__arrow; apply a_wf_ptyp__unit.
  - apply mono_ptyp__arrow; apply mono_ptyp__unit.
Qed.

Lemma cex_wf_Pi : cexΘ0 ⨟ empty ⊢ₚₛᵃ cexPi.
Proof.
  apply a_wf_pskl__arrow; [ | apply a_wf_pskl__unit ].
  apply a_wf_pskl__var; right; left.
  unfold cexΘ0, binds; simpl; left; reflexivity.
Qed.

Lemma cex_wf_P0 : cexΘ0 ⨟ empty ⊢ₚₛᵃ cexP0.
Proof.
  apply a_wf_pskl__var; right; right; left.
  unfold cexΘ0, binds; simpl; right; left; reflexivity.
Qed.

Lemma cex_tags : a_tags_sort a_sub_mode_sk empty cexψa.
Proof.
  apply a_tags_sort__sk.
  - apply is_tskl__arrow; [ apply is_tskl__var | apply is_tskl__unit ].
  - apply (d_tags_skl__arrow (Ψ1 := empty) (Ψ2 := empty));
      [ apply d_tags_skl__var; fsetdec
      | apply d_tags_skl__unit; fsetdec
      | fsetdec | fsetdec ].
Qed.

Lemma cex_wf_erase_psia : cexΘ ⨟ empty ⊢ₚₛᵃ ⌊ cexψa ⌋ˢ.
Proof.
  simpl.
  apply a_wf_pskl__arrow; [ | apply a_wf_pskl__unit ].
  apply a_wf_pskl__var; right; left.
  unfold cexΘ, binds; simpl; left; reflexivity.
Qed.

(** ρ = [X ↦ unit]: an arrow congruence with the leaf on the left and
    reflexivity on the right; Δρ = {X}, Ψρ = ∅. *)
Lemma cex_rho :
  uskl_rho a_sub_mode_sk cexΘ (singleton X) empty cexψsub cexψa.
Proof.
  apply (urho__arrow (Ψ1 := empty) (Ψ2 := empty)); [ | | fsetdec ].
  - apply urho__leaf with (Ψ'' := empty).
    + fsetdec.
    + apply a_tags_sort__sk;
        [ apply is_tskl__unit | apply d_tags_skl__unit; fsetdec ].
    + simpl. apply a_wf_pskl__unit.
    + fsetdec.
  - apply urho__refl; [ apply lc_uskl_unit | fsetdec ].
Qed.

(** The freshness pack: X is rigid in Θ, absent from θ's images, from Θ's
    (nonexistent) definition images, from P_i's ⊤◇-shielded variables, and
    from ftv(P_0). *)
Lemma cex_rho_fresh : rho_fresh (singleton X) cexΘ cexθ.
Proof.
  intros Y HY.
  assert (HYX : Y = X) by (clear - HY; fsetdec); subst Y.
  split; [ | split ].
  - unfold cexΘ, binds; simpl; left; reflexivity.
  - intros p Hp; simpl in Hp; destruct Hp as [Hp | []]; subst p.
    simpl. clear - Hne; fsetdec.
  - intros α τ Hb.
    unfold cexΘ, binds in Hb; simpl in Hb.
    destruct Hb as [Hb | []]; discriminate Hb.
Qed.

Lemma cex_pack_shielded : X `notin` pskl_shielded_ftv cexPi.
Proof. simpl. fsetdec. Qed.

Lemma cex_pack_ftv_P0 : X `notin` ftvar_in_pskl cexP0.
Proof. simpl. clear - Hne; fsetdec. Qed.

(** msubst computations. *)
Lemma cex_msubst_Pi : msubst_pskl cexθ cexPi = cexPi.
Proof.
  unfold cexPi, cexθ; simpl.
  destruct (X == alpha) as [Heq | _]; [ exact (False_ind _ (Hne Heq)) | ].
  reflexivity.
Qed.

Lemma cex_msubst_P0 :
  msubst_pskl cexθ cexP0 = pskl_arrow pskl_unit pskl_unit.
Proof.
  unfold cexP0, cexθ; simpl.
  destruct (alpha == alpha) as [_ | Habs];
    [ reflexivity | exact (False_ind _ (Habs eq_refl)) ].
Qed.

(** The precision premise  Θ ⨟ {X} ⊢ θP_i ⊑ᵖ[·] ψa  — note P_i has the
    rigid X exactly at the ρ-substituted position (the paper's positional
    side condition holds). *)
Lemma cex_precision :
  cexΘ ⨟ (singleton X) ⊢ (msubst_pskl cexθ cexPi) ⊑ᵖ[ empty ] cexψa.
Proof.
  rewrite cex_msubst_Pi.
  apply (ad_ppre__arrow (Ψ1 := empty) (Ψ2 := empty));
    [ | apply ad_ppre__unit; fsetdec | fsetdec ].
  apply ad_ppre__var; [ fsetdec | left; fsetdec ].
Qed.

(** The refinement premise  Θ ⊢ inh{θP_0} ⊳ Q. *)
Lemma cex_refinement :
  cexΘ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl cexθ cexP0)) ⊳ cexQ.
Proof.
  rewrite cex_msubst_P0. simpl.
  apply ad_refine_syn__arrow; apply ad_refine_syn__unit.
Qed.

(** The consistency premise  · ⨟ Θ ⊢ ρ(ψa) ∼ Q. *)
Lemma cex_consistency : empty ⨟ cexΘ ⊢ₛᵃ cexψsub ∼ cexQ.
Proof.
  apply (ad_pat_consis__arrow (Ψ1 := empty) (Ψ2 := empty));
    [ apply ad_pat_consis__unit; fsetdec
    | apply ad_pat_consis__unit; fsetdec
    | fsetdec ].
Qed.

(* ------------------------------------------------------------------ *)
(*  The refutation.                                                    *)
(* ------------------------------------------------------------------ *)

(** The only solve derivation forces P_a = α̂ (FlexR). *)
Lemma cex_solve_forces_flex : forall Pa,
  cexΘ0 ⊢ₑ cexPi ∼ cexP0 ⤳ Pa ->
  Pa = pskl_var_f alpha.
Proof.
  intros Pa H; inversion H; subst; reflexivity.
Qed.

(** No partial precision of the pinned image against ψa, at ANY Δ and ANY
    tag set: the function-argument obligation is [unit ⊑ᵖ var X] with X
    rigid. *)
Lemma cex_no_precision : forall Δ Ψ,
  cexΘ ⨟ Δ ⊢ (pskl_arrow pskl_unit pskl_unit) ⊑ᵖ[ Ψ ] cexψa ->
  False.
Proof.
  intros Δ Ψ H.
  inversion H; subst.
  match goal with
    Hu : cexΘ ⨟ Δ ⊢ pskl_unit ⊑ᵖ[ _ ] (uskl_var_f X) |- _ =>
      inversion Hu; subst
  end.
  match goal with
    Hb : binds X (abind_flex_mono_def _) cexΘ |- _ =>
      unfold cexΘ, binds in Hb; simpl in Hb;
      destruct Hb as [Hb | []]; discriminate Hb
  end.
Qed.

(** θa ≡ θ over Θ0 pins θa(α̂) to unit→unit (Θ is definition-free, so ≡ᵗ
    is syntactic identity). *)
Lemma cex_equiv_pins_image : forall θa,
  a_inc_equiv cexΘ0 cexθ θa cexΘ ->
  msubst_pskl θa cexP0 = pskl_arrow pskl_unit pskl_unit.
Proof.
  intros θa Hequiv.
  assert (Hb : binds alpha abind_flex_mono cexΘ0)
    by (unfold cexΘ0, binds; simpl; right; left; reflexivity).
  pose proof (a_inc_equiv_flex_pin Hequiv alpha Hb) as Hpin.
  assert (Hlook1 : msubst_lookup cexθ alpha = cexτ).
  { unfold cexθ; simpl.
    destruct (alpha == alpha) as [_ | Habs];
      [ reflexivity | exact (False_ind _ (Habs eq_refl)) ]. }
  rewrite Hlook1 in Hpin.
  assert (Heqt : cexτ = msubst_lookup θa alpha).
  { apply (a_tyequiv_def_free_eq Hpin).
    intros a t Hb'.
    unfold cexΘ, binds in Hb'; simpl in Hb'.
    destruct Hb' as [Hb' | []]; discriminate Hb'. }
  unfold cexP0; simpl.
  rewrite <- Heqt.
  reflexivity.
Qed.

(** MAIN THEOREM: the -var lemma's conclusion is unsatisfiable for this
    premise-satisfying configuration — for EVERY choice of P_a and θa
    (θa constrained exactly as the paper's conclusion does), and with the
    conclusion's precision refuted at EVERY Δ and tag set. *)
Theorem cex_p6_var_conclusion_refuted : forall Pa θa Δ Ψ,
  cexΘ0 ⊢ₑ cexPi ∼ cexP0 ⤳ Pa ->
  θa ∷ cexΘ0 ⊑ cexΘ ->
  a_inc_equiv cexΘ0 cexθ θa cexΘ ->
  cexΘ ⨟ Δ ⊢ (msubst_pskl θa Pa) ⊑ᵖ[ Ψ ] cexψa ->
  False.
Proof.
  intros Pa θa Δ Ψ Hsolve Hinc Hequiv Hpre.
  rewrite (cex_solve_forces_flex Hsolve) in Hpre.
  pose proof (cex_equiv_pins_image Hequiv) as Himg.
  unfold cexP0 in Himg. rewrite Himg in Hpre.
  exact (cex_no_precision Hpre).
Qed.

(** Corollary for the strengthened (θa := θ) reading. *)
Corollary cex_p6_var_conclusion_refuted_theta : forall Pa Δ Ψ,
  cexΘ0 ⊢ₑ cexPi ∼ cexP0 ⤳ Pa ->
  cexΘ ⨟ Δ ⊢ (msubst_pskl cexθ Pa) ⊑ᵖ[ Ψ ] cexψa ->
  False.
Proof.
  intros Pa Δ Ψ Hsolve Hpre.
  rewrite (cex_solve_forces_flex Hsolve) in Hpre.
  pose proof cex_msubst_P0 as Heq.
  unfold cexP0 in Heq. rewrite Heq in Hpre.
  exact (cex_no_precision Hpre).
Qed.

End CexP6FlexCounterpart.
