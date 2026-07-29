(** COUNTEREXAMPLE (P6, 2026-07-24): the -var completeness lemmas of the
    constraint cluster —
    [lemma:complete-consistency-constraint-collection-solving-var]
    (consistency-proofs.tex:1181) and its subtyping twin
    [lemma:complete-constraint-collection-solving-var]
    (subtyping-proofs.tex:1696) — are FALSE AS STATED when the solve
    counterpart [P0] is a FLEXIBLE VARIABLE of [Θ0] (κ-pinned) whose image
    collides with a ρ-substituted (leaf) position of [ψa].

    THE CONFIGURATION.  Take
      Θ0 = c~tvar, β̂~flex        Θ = c~tvar        κ = [β̂ ↦ unit→unit]
      ψa = c → unit               ρ = [c ↦ unit]    (so ρ(ψa) = unit→unit)
      P_i = c → unit              P_0 = β̂           Q = unit → unit
    with Δ = Δρ = {c} and every tag set empty.  ALL premises of the -var
    lemma hold (machine-checked below): the wf premises, κ ∷ Θ0 ⊑ Θ, the
    tag-sort of ψa, the ρ-relation with its freshness pack (c rigid in Θ,
    absent from κ's images, Θ's definition images, P_i's ⊤◇-bodies, and
    ftv(P_0)), the precision premise κP_i ⊑ᵖ[·] ψa, the consistency premise
    for ρ(ψa) against Q, the refinement premise inh{κP_0} ⊳ Q — and the
    paper's positional side condition (P_i has the rigid c exactly at the
    ρ-substituted position).

    THE REFUTATION.  The only solve rule applicable to
    [solveeq{c→unit}{β̂}{·}] is FlexR, forcing P_a = β̂.  The conclusion
    demands  Θ ⨟ Δ ⊢ κa(β̂) ⊑ᵖ[Ψi,Ψa] ψa  with κ ≡ κa over Θ0, which pins
    κa(β̂) ≡ᵗ unit→unit; at Θ = c~tvar (definition-free) the equivalence is
    syntactic, so the required precision is
        (unit→unit) ⊑ᵖ (c → unit),
    underivable: its function-argument obligation is [unit ⊑ᵖ var c] with c
    RIGID, and no partial-precision rule matches (the var rule needs the
    occurrence, flex_r needs a defined flexible).  Machine-checked below for
    ARBITRARY κa, Δ and tag set.

    ROOT CAUSE.  The paper's case analyses recover P_0's shape by inversion
    on the refinement premise [Θ ⊢ inh{κP_0} ⊳ Q] — but that inversion also
    admits P_0 = flexible variable (whose κ-image supplies the matching
    constructor), a subcase no completeness proof case covers: the
    algorithm's own rule for flexible counterparts, LE-FlexR
    (fig:poly-info-extraction), is never invoked in the completeness
    appendices.  At the level of the non-var lemmas
    (consistency-proofs.tex:920 / subtyping-proofs.tex:2202) a flexible
    counterpart CAN be handled — LE-FlexR replaces the constraint payload by
    a FRESH α1̂ ∈ Ξc, and κa (which extends κ to Ξc there) is free to map α1̂
    to a ψa-refining monotype (when one exists; when ψa is not
    mono-paintable the premises are vacuous).  But the -var lemmas have
    Ξc = · and κa ≡ κ on ALL of Θ0, so a flexible P_0 with a κ-image that
    is "wrong" at a ρ-leaf position refutes the statement outright.

    STATUS (updated 2026-07-25): the isolated -var statement is false, but
    this is NOT a completeness problem — the configuration is UNREACHABLE.
    See [cex_p6_flex_freshened.v] for the resolution and its two Qed lemmas.
    In brief:
      * The cex's κ is FORCED BY ρ, not free: ρ substitutes the rigid [c]
        away, so [ρ(ψa) = unit→unit ∼ Q] and [inh{κβ̂} ⊳ Q] (same Q) pin
        [κβ̂ = unit→unit] — c is stripped from everything κ can see, while
        ψa (used only for the final precision) still carries it.
      * A run never produces this: when a flexible counterpart faces a
        COMPOUND (arrow) subject, [a_lookeq__flex_r] (LE-FlexR) FRESHENS it
        to a new [α1 ∈ Ξ] — machine-checked in
        [a_lookeq_arrow_subject_flex_target_freshened].  The -var lemma
        never sees a raw Θ0-flex P_0 at an arrow node; it sees the fresh α1,
        handled by the NON-var lemma (κ extends over Ξ, assigns α1 the rigid
        c).  A raw flex payload only ever sits opposite a LEAF
        ([a_lookeq_flex_target_raw_subject_not_arrow]).
      * Only the Arrow case is even reachable for a flexible P_0: κ maps
        flexibles to MONOTYPES, so refinement can never expose a flexible
        P_0 as a ∀/⊤◇ (ForallInh/ForallSyn/ghost cases), and leaves are
        handled directly (SolE-Flex / the SolE-Var special case).
    There is no flex-SPLIT rule in constraint solving and none is needed:
    [SolE-FlexR] solves the flexible counterpart directly to β̂.

    SUPERSEDED (do not pursue): the earlier "redirected repair" (a P0-side
    positional condition [pskl_dominates_rho], DESIGN §6) — it patched an
    isolated statement that does not need patching, and its ForallL
    maintenance is not derivable from the local solve ([SolE-Check] bridges
    into [SolE-FlexR]).  Reverted 2026-07-25.

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

Lemma a_tyequiv_def_free_eq : forall Θ A A',
  Θ ⊢ A ≡ᵗ A' ->
  (forall α τ, ~ binds α (abind_flex_mono_def τ) Θ) ->
  A = A'.
Proof.
  intros Θ A A' H; induction H; intros Hdf.
  - reflexivity.
  - symmetry; auto.
  - rewrite (IHa_tyequiv1 Hdf); auto.
  - exfalso; eapply Hdf; eassumption.
  - rewrite (IHa_tyequiv1 Hdf); rewrite (IHa_tyequiv2 Hdf); reflexivity.
  - f_equal.
    pick fresh β for
      (L `union` ftvar_in_ptyp A `union` ftvar_in_ptyp B).
    apply (open_ptyp_wrt_ptyp_inj _ _ β);
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

Variables c beta : atom.
Hypothesis Hne : c <> beta.

(* The configuration. *)
Definition cexΘ0 : aenv :=
  (c ~ abind_tvar) ++ (beta ~ abind_flex_mono) ++ nil.
Definition cexΘ : aenv := (c ~ abind_tvar) ++ nil.
Definition cexτ : ptyp := ptyp_arrow ptyp_unit ptyp_unit.
Definition cexκ : metasubst := (beta, cexτ) :: nil.
Definition cexψa : uskl := uskl_arrow (uskl_var_f c) uskl_unit.
Definition cexψsub : uskl := uskl_arrow uskl_unit uskl_unit.
Definition cexPi : pskl := pskl_arrow (pskl_var_f c) pskl_unit.
Definition cexP0 : pskl := pskl_var_f beta.
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

Lemma cex_inc : cexκ ∷ cexΘ0 ⊑ cexΘ.
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

(** ρ = [c ↦ unit]: an arrow congruence with the leaf on the left and
    reflexivity on the right; Δρ = {c}, Ψρ = ∅. *)
Lemma cex_rho :
  uskl_rho a_sub_mode_sk cexΘ (singleton c) empty cexψsub cexψa.
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

(** The freshness pack: c is rigid in Θ, absent from κ's images, from Θ's
    (nonexistent) definition images, from P_i's ⊤◇-shielded variables, and
    from ftv(P_0). *)
Lemma cex_rho_fresh : rho_fresh (singleton c) cexΘ cexκ.
Proof.
  intros β Hβ.
  assert (HYX : β = c) by (clear - Hβ; fsetdec); subst β.
  split; [ | split ].
  - unfold cexΘ, binds; simpl; left; reflexivity.
  - intros p Hp; simpl in Hp; destruct Hp as [Hp | []]; subst p.
    simpl. clear - Hne; fsetdec.
  - intros α τ Hb.
    unfold cexΘ, binds in Hb; simpl in Hb.
    destruct Hb as [Hb | []]; discriminate Hb.
Qed.

Lemma cex_pack_shielded : c `notin` pskl_shielded_ftv cexPi.
Proof. simpl. fsetdec. Qed.

Lemma cex_pack_ftv_P0 : c `notin` ftvar_in_pskl cexP0.
Proof. simpl. clear - Hne; fsetdec. Qed.

(** msubst computations. *)
Lemma cex_msubst_Pi : msubst_pskl cexκ cexPi = cexPi.
Proof.
  unfold cexPi, cexκ; simpl.
  destruct (c == beta) as [Heq | _]; [ exact (False_ind _ (Hne Heq)) | ].
  reflexivity.
Qed.

Lemma cex_msubst_P0 :
  msubst_pskl cexκ cexP0 = pskl_arrow pskl_unit pskl_unit.
Proof.
  unfold cexP0, cexκ; simpl.
  destruct (beta == beta) as [_ | Habs];
    [ reflexivity | exact (False_ind _ (Habs eq_refl)) ].
Qed.

(** The precision premise  Θ ⨟ {c} ⊢ κP_i ⊑ᵖ[·] ψa  — note P_i has the
    rigid c exactly at the ρ-substituted position (the paper's positional
    side condition holds). *)
Lemma cex_precision :
  cexΘ ⨟ (singleton c) ⊢ (msubst_pskl cexκ cexPi) ⊑ᵖ[ empty ] cexψa.
Proof.
  rewrite cex_msubst_Pi.
  apply (ad_ppre__arrow (Ψ1 := empty) (Ψ2 := empty));
    [ | apply ad_ppre__unit; fsetdec | fsetdec ].
  apply ad_ppre__var; [ fsetdec | left; fsetdec ].
Qed.

(** The refinement premise  Θ ⊢ inh{κP_0} ⊳ Q. *)
Lemma cex_refinement :
  cexΘ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl cexκ cexP0)) ⊳ cexQ.
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

(** The only solve derivation forces P_a = β̂ (FlexR). *)
Lemma cex_solve_forces_flex : forall Pa,
  cexΘ0 ⊢ₑ cexPi ∼ cexP0 ⤳ Pa ->
  Pa = pskl_var_f beta.
Proof.
  intros Pa H; inversion H; subst; reflexivity.
Qed.

(** No partial precision of the pinned image against ψa, at ANY Δ and ANY
    tag set: the function-argument obligation is [unit ⊑ᵖ var c] with c
    rigid. *)
Lemma cex_no_precision : forall Δ Ψ,
  cexΘ ⨟ Δ ⊢ (pskl_arrow pskl_unit pskl_unit) ⊑ᵖ[ Ψ ] cexψa ->
  False.
Proof.
  intros Δ Ψ H.
  inversion H; subst.
  match goal with
    Hu : cexΘ ⨟ Δ ⊢ pskl_unit ⊑ᵖ[ _ ] (uskl_var_f c) |- _ =>
      inversion Hu; subst
  end.
  match goal with
    Hb : binds c (abind_flex_mono_def _) cexΘ |- _ =>
      unfold cexΘ, binds in Hb; simpl in Hb;
      destruct Hb as [Hb | []]; discriminate Hb
  end.
Qed.

(** κa ≡ κ over Θ0 pins κa(β̂) to unit→unit (Θ is definition-free, so ≡ᵗ
    is syntactic identity). *)
Lemma cex_equiv_pins_image : forall κa,
  a_inc_equiv cexΘ0 cexκ κa cexΘ ->
  msubst_pskl κa cexP0 = pskl_arrow pskl_unit pskl_unit.
Proof.
  intros κa Hequiv.
  assert (Hb : binds beta abind_flex_mono cexΘ0)
    by (unfold cexΘ0, binds; simpl; right; left; reflexivity).
  pose proof (a_inc_equiv_flex_pin Hequiv beta Hb) as Hpin.
  assert (Hlook1 : msubst_lookup cexκ beta = cexτ).
  { unfold cexκ; simpl.
    destruct (beta == beta) as [_ | Habs];
      [ reflexivity | exact (False_ind _ (Habs eq_refl)) ]. }
  rewrite Hlook1 in Hpin.
  assert (Heqt : cexτ = msubst_lookup κa beta).
  { apply (a_tyequiv_def_free_eq Hpin).
    intros a t Hb'.
    unfold cexΘ, binds in Hb'; simpl in Hb'.
    destruct Hb' as [Hb' | []]; discriminate Hb'. }
  unfold cexP0; simpl.
  rewrite <- Heqt.
  reflexivity.
Qed.

(** MAIN THEOREM: the -var lemma's conclusion is unsatisfiable for this
    premise-satisfying configuration — for EVERY choice of P_a and κa
    (κa constrained exactly as the paper's conclusion does), and with the
    conclusion's precision refuted at EVERY Δ and tag set. *)
Theorem cex_p6_var_conclusion_refuted : forall Pa κa Δ Ψ,
  cexΘ0 ⊢ₑ cexPi ∼ cexP0 ⤳ Pa ->
  κa ∷ cexΘ0 ⊑ cexΘ ->
  a_inc_equiv cexΘ0 cexκ κa cexΘ ->
  cexΘ ⨟ Δ ⊢ (msubst_pskl κa Pa) ⊑ᵖ[ Ψ ] cexψa ->
  False.
Proof.
  intros Pa κa Δ Ψ Hsolve Hinc Hequiv Hpre.
  rewrite (cex_solve_forces_flex Hsolve) in Hpre.
  pose proof (cex_equiv_pins_image Hequiv) as Himg.
  unfold cexP0 in Himg. rewrite Himg in Hpre.
  exact (cex_no_precision Hpre).
Qed.

(** Corollary for the strengthened (κa := κ) reading. *)
Corollary cex_p6_var_conclusion_refuted_theta : forall Pa Δ Ψ,
  cexΘ0 ⊢ₑ cexPi ∼ cexP0 ⤳ Pa ->
  cexΘ ⨟ Δ ⊢ (msubst_pskl cexκ Pa) ⊑ᵖ[ Ψ ] cexψa ->
  False.
Proof.
  intros Pa Δ Ψ Hsolve Hpre.
  rewrite (cex_solve_forces_flex Hsolve) in Hpre.
  pose proof cex_msubst_P0 as Heq.
  unfold cexP0 in Heq. rewrite Heq in Hpre.
  exact (cex_no_precision Hpre).
Qed.

(* ------------------------------------------------------------------ *)
(*  THE nonflex{P0} REPAIR IS INSUFFICIENT: the same refutation         *)
(*  reproduces one constructor down.  With                              *)
(*      ψa = 1 → (c → 1)      P_i = 1 → (c → 1)      P_0 = 1 → β̂       *)
(*  the counterpart P_0 is an arrow — nonflex{P_0} HOLDS — but the      *)
(*  arrow case of the -var lemma recurses on P_0's PIECES, and the      *)
(*  right piece is the old flexible β̂ opposite the ρ-leaf position:     *)
(*  solving forces P_a = 1 → β̂ (SE-Arrow, then SE-FlexR), and the       *)
(*  conclusion precision fails exactly as before.  So the repair must   *)
(*  exclude flexible variables from ALL (ρ-leaf-opposite) positions of  *)
(*  P_0, not just its head.                                             *)
(* ------------------------------------------------------------------ *)

Definition cexψa2 : uskl := uskl_arrow uskl_unit cexψa.
Definition cexψsub2 : uskl := uskl_arrow uskl_unit cexψsub.
Definition cexPi2 : pskl := pskl_arrow pskl_unit cexPi.
Definition cexP02 : pskl := pskl_arrow pskl_unit cexP0.
Definition cexQ2 : bskl := bskl_arrow bskl_unit cexQ.

(** The repair's premise holds: P_0 is not a flexible variable. *)
Lemma cex2_nonflex : a_non_flex cexΘ0 cexP02.
Proof.
  split.
  - apply lc_pskl_arrow; [ apply lc_pskl_unit | apply lc_pskl_var_f ].
  - intros Hf; inversion Hf.
Qed.

Lemma cex2_wf_Pi : cexΘ0 ⨟ empty ⊢ₚₛᵃ cexPi2.
Proof. apply a_wf_pskl__arrow; [ apply a_wf_pskl__unit | apply cex_wf_Pi ]. Qed.

Lemma cex2_wf_P0 : cexΘ0 ⨟ empty ⊢ₚₛᵃ cexP02.
Proof. apply a_wf_pskl__arrow; [ apply a_wf_pskl__unit | apply cex_wf_P0 ]. Qed.

Lemma cex2_tags : a_tags_sort a_sub_mode_sk empty cexψa2.
Proof.
  apply a_tags_sort__sk.
  - apply is_tskl__arrow;
      [ apply is_tskl__unit
      | apply is_tskl__arrow; [ apply is_tskl__var | apply is_tskl__unit ] ].
  - apply (d_tags_skl__arrow (Ψ1 := empty) (Ψ2 := empty));
      [ apply d_tags_skl__unit; fsetdec
      | apply (d_tags_skl__arrow (Ψ1 := empty) (Ψ2 := empty));
        [ apply d_tags_skl__var; fsetdec
        | apply d_tags_skl__unit; fsetdec
        | fsetdec | fsetdec ]
      | fsetdec | fsetdec ].
Qed.

Lemma cex2_wf_erase_psia : cexΘ ⨟ empty ⊢ₚₛᵃ ⌊ cexψa2 ⌋ˢ.
Proof.
  simpl.
  apply a_wf_pskl__arrow; [ apply a_wf_pskl__unit | ].
  apply a_wf_pskl__arrow; [ | apply a_wf_pskl__unit ].
  apply a_wf_pskl__var; right; left.
  unfold cexΘ, binds; simpl; left; reflexivity.
Qed.

Lemma cex2_rho :
  uskl_rho a_sub_mode_sk cexΘ (singleton c) empty cexψsub2 cexψa2.
Proof.
  apply (urho__arrow (Ψ1 := empty) (Ψ2 := empty)); [ | | fsetdec ].
  - apply urho__refl; [ apply lc_uskl_unit | fsetdec ].
  - apply cex_rho.
Qed.

Lemma cex2_pack_shielded : c `notin` pskl_shielded_ftv cexPi2.
Proof. simpl. fsetdec. Qed.

Lemma cex2_pack_ftv_P0 : c `notin` ftvar_in_pskl cexP02.
Proof. simpl. clear - Hne; fsetdec. Qed.

Lemma cex2_precision :
  cexΘ ⨟ (singleton c) ⊢ (msubst_pskl cexκ cexPi2) ⊑ᵖ[ empty ] cexψa2.
Proof.
  unfold cexPi2; cbn [msubst_pskl].
  rewrite cex_msubst_Pi.
  apply (ad_ppre__arrow (Ψ1 := empty) (Ψ2 := empty));
    [ apply ad_ppre__unit; fsetdec
    | pose proof cex_precision as Hp; rewrite cex_msubst_Pi in Hp; exact Hp
    | fsetdec ].
Qed.

Lemma cex2_refinement :
  cexΘ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl cexκ cexP02)) ⊳ cexQ2.
Proof.
  unfold cexP02; cbn [msubst_pskl].
  rewrite cex_msubst_P0. simpl.
  apply ad_refine_syn__arrow;
    [ apply ad_refine_syn__unit
    | apply ad_refine_syn__arrow; apply ad_refine_syn__unit ].
Qed.

Lemma cex2_consistency : empty ⨟ cexΘ ⊢ₛᵃ cexψsub2 ∼ cexQ2.
Proof.
  apply (ad_pat_consis__arrow (Ψ1 := empty) (Ψ2 := empty));
    [ apply ad_pat_consis__unit; fsetdec
    | apply cex_consistency
    | fsetdec ].
Qed.

(** The solve is forced through SE-Arrow and then SE-FlexR on the piece. *)
Lemma cex2_solve_forces_flex : forall Pa,
  cexΘ0 ⊢ₑ cexPi2 ∼ cexP02 ⤳ Pa ->
  Pa = pskl_arrow pskl_unit (pskl_var_f beta).
Proof.
  intros Pa H.
  inversion H; subst.
  match goal with
    H1 : cexΘ0 ⊢ₑ pskl_unit ∼ pskl_unit ⤳ ?P1 |- _ =>
      inversion H1; subst
  end.
  match goal with
    H2 : cexΘ0 ⊢ₑ cexPi ∼ cexP0 ⤳ ?P2 |- _ =>
      rewrite (cex_solve_forces_flex H2)
  end.
  reflexivity.
Qed.

Lemma cex2_no_precision : forall Δ Ψ,
  cexΘ ⨟ Δ ⊢ (pskl_arrow pskl_unit (pskl_arrow pskl_unit pskl_unit))
    ⊑ᵖ[ Ψ ] cexψa2 ->
  False.
Proof.
  intros Δ Ψ H.
  inversion H; subst.
  match goal with
    H2 : cexΘ ⨟ Δ ⊢ (pskl_arrow pskl_unit pskl_unit) ⊑ᵖ[ _ ] cexψa |- _ =>
      exact (cex_no_precision H2)
  end.
Qed.

(** MAIN THEOREM (deep variant): with nonflex{P_0} satisfied, the -var
    conclusion is still unsatisfiable — for every P_a, every κa pinned by
    the paper's equivalence, every Δ and tag set. *)
Theorem cex_p6_var_nonflex_insufficient : forall Pa κa Δ Ψ,
  cexΘ0 ⊢ₑ cexPi2 ∼ cexP02 ⤳ Pa ->
  κa ∷ cexΘ0 ⊑ cexΘ ->
  a_inc_equiv cexΘ0 cexκ κa cexΘ ->
  cexΘ ⨟ Δ ⊢ (msubst_pskl κa Pa) ⊑ᵖ[ Ψ ] cexψa2 ->
  False.
Proof.
  intros Pa κa Δ Ψ Hsolve Hinc Hequiv Hpre.
  rewrite (cex2_solve_forces_flex Hsolve) in Hpre.
  simpl in Hpre.
  pose proof (cex_equiv_pins_image Hequiv) as Himg.
  unfold cexP0 in Himg. simpl in Himg.
  rewrite Himg in Hpre.
  exact (cex2_no_precision Hpre).
Qed.

End CexP6FlexCounterpart.

