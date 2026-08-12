(** THE BRIDGE that the corrected [Flex-Flex-Assign] needs.

    With the rule's premise now CONSISTENCY, unification soundness must derive a
    type EQUIVALENCE  [{{ Θ ⊢ A ≡ᵗ B }}a]  from what consistency soundness gives it:
    a coloured JOIN [Qt] with

        syn{A} ∼ Qt      (declarative consistency of the SUBJECT with the join)
        inh{B} ⊳ Qt      (the INPUT refines to the join)

    On MONOTYPES this pins A and B together: monotypes carry no ghosts, so both
    judgments are structural (modulo flexible-variable lookups), and the join is
    forced.  Hence A ≡ B.

    This is the one genuinely NEW piece of mathematics the mutual-recursion fix
    needs; everything else is mechanical adaptation. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.

Set Implicit Arguments.

(** A monotype's skeleton painted [syn] and read back as an unresolved skeleton
    is just the monotype's [uskl] image. *)
Lemma ptyp_to_uskl_syn_eq : forall A,
  pskl_to_uskl (ptyp_to_pskl A) = ptyp_to_uskl_syn A.
Proof.
  unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  induction A; simpl; f_equal; auto.
Qed.

(** A definition is well-formed in its own (tail) context, hence in the whole. *)
Lemma a_wf_aenv_binds_def_wf_local : forall Θ α1 τ,
  {{ ⊢ Θ }}a ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ α1 τ Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
    try discriminate;
    try (eapply a_wf_ptyp_weaken;
         [ intros y b Hby; unfold binds; right; exact Hby | ];
         first [ apply IHHwf; exact Hb'
               | inversion Heqb; subst; assumption ]).
Qed.

(** On a MONOTYPE the inherited and synthesised paintings coincide — they only
    differ at quantifiers, and a monotype has none. *)
Lemma ptyp_to_bskl_inh_syn_eq : forall A,
  mono_ptyp A ->
  pskl_to_bskl_inh (ptyp_to_pskl A) = ptyp_to_bskl_syn A.
Proof.
  unfold ptyp_to_bskl_syn.
  intros A Hm; induction Hm; simpl; f_equal; auto.
Qed.

(** The syn painting of a monotype determines it. *)
Lemma ptyp_to_bskl_syn_inj : forall A A',
  mono_ptyp A -> mono_ptyp A' ->
  ptyp_to_bskl_syn A = ptyp_to_bskl_syn A' ->
  A = A'.
Proof.
  unfold ptyp_to_bskl_syn.
  intros A A' HmA; revert A'; induction HmA as [ | α | A1 A2 Hm1 IH1 Hm2 IH2 ];
    intros A' HmB Heq; destruct HmB; simpl in Heq; try discriminate.
  - reflexivity.
  - inversion Heq; reflexivity.
  - inversion Heq. f_equal; [ apply IH1 | apply IH2 ]; auto.
Qed.

(* ===================================================================== *)
(*  THE BRIDGE                                                            *)
(*                                                                        *)
(*  Consistency computes a JOIN [Qt].  On monotypes that join is itself   *)
(*  the painting of a monotype [C], and BOTH sides are equivalent to it:  *)
(*  the SUBJECT via consistency, the INPUT via refinement.  Hence the two  *)
(*  sides are equivalent to each other — which is what the corrected       *)
(*  [Flex-Flex-Assign] needs.                                             *)
(*                                                                        *)
(*  Both judgments are structural on monotypes (no ghosts, no             *)
(*  quantifiers); the only slack is flexible-variable LOOKUP, and          *)
(*  [a_tyequiv__flex_def] absorbs exactly that.                            *)
(* ===================================================================== *)

(** The SUBJECT side: consistency of a monotype with the join.

    Every rule but [flex_r] constrains the SUBJECT's shape, so a monotype subject
    admits only unit / var / arrow / flex_l.  [flex_r] leaves the subject alone
    (it unfolds the JOIN instead), so it must not be destructed along with the
    others. *)
Lemma consis_mono_join : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall A, R = ptyp_to_uskl_syn A -> mono_ptyp A ->
  exists C, mono_ptyp C /\ Qt = ptyp_to_bskl_syn C /\ {{ Θ ⊢ A ≡ᵗ C }}a.
Proof.
  intros Ψ Θ R Qt Hc Hwf; induction Hc; intros A0 HeqS HmA0;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct HmA0 as [ | α0 | A1 A2 Hm1 Hm2 ]; simpl in HeqS; try discriminate.
    exists ptyp_unit.
    split; [ apply mono_ptyp__unit | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_unit.
  - (* var *)
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    exists (ptyp_var_f α0).
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_var_f.
  - (* arrow *)
    destruct HmA0 as [ | | A1 A2 Hm1 Hm2 ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct (IHHc1 Hwf A1 eq_refl Hm1) as [C1 [HmC1 [HeqQ1 He1]]].
    destruct (IHHc2 Hwf A2 eq_refl Hm2) as [C2 [HmC2 [HeqQ2 He2]]].
    exists (ptyp_arrow C1 C2).
    split; [ apply mono_ptyp__arrow; auto | ].
    split; [ simpl; rewrite HeqQ1, HeqQ2; reflexivity | ].
    apply a_tyequiv__arrow; auto.
  - (* forall_inh_tagged *) destruct HmA0; simpl in HeqS; discriminate.
  - (* forall_inh_untagged *) destruct HmA0; simpl in HeqS; discriminate.
  - (* forall_syn_tagged *) destruct HmA0; simpl in HeqS; discriminate.
  - (* forall_syn *) destruct HmA0; simpl in HeqS; discriminate.
  - (* ghostg *) destruct HmA0; simpl in HeqS; discriminate.
  - (* topholeg *) destruct HmA0; simpl in HeqS; discriminate.
  - (* hole *) destruct HmA0; simpl in HeqS; discriminate.
  - (* tophole *) destruct HmA0; simpl in HeqS; discriminate.
  - (* tophole_inh *) destruct HmA0; simpl in HeqS; discriminate.
  - (* tophole_drop *) destruct HmA0; simpl in HeqS; discriminate.
  - (* flex_l : the SUBJECT is a defined flexible; unfold it *)
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHc Hwf τ eq_refl Hmτ) as [C [HmC [HeqQ He]]].
    exists C.
    split; [ exact HmC | ].
    split; [ exact HeqQ | ].
    eapply a_tyequiv__trans;
      [ apply a_tyequiv__flex_def; eassumption | exact He ].
  - (* flex_r : the JOIN is a defined flexible; unfold it.  The SUBJECT is
       untouched here, so do NOT destruct [HmA0]. *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHc Hwf A0 HeqS HmA0) as [C [HmC [HeqQ He]]].
    assert (Hτ : C = τ)
      by (apply ptyp_to_bskl_syn_inj; auto;
          unfold ptyp_to_bskl_syn; rewrite <- HeqQ; reflexivity).
    subst C.
    exists (ptyp_var_f α).
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    eapply a_tyequiv__trans;
      [ exact He
      | apply a_tyequiv__sym; apply a_tyequiv__flex_def; eassumption ].
Qed.

(** The INPUT side: the input monotype refines to the same join.

    Mirrors [consis_mono_join].  Every refinement rule but [flex_r] constrains the
    LEFT shape, so a monotype left-hand side admits only unit / var / arrow /
    flex_l. *)
Lemma refine_mono_join : forall Θ Δ Qb Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qb ⊳ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall A, Qb = ptyp_to_bskl_syn A -> mono_ptyp A ->
  exists C, mono_ptyp C /\ Qt = ptyp_to_bskl_syn C /\ {{ Θ ⊢ A ≡ᵗ C }}a.
Proof.
  intros Θ Δ Qb Qt Hr Hwf; induction Hr; intros B0 HeqB HmB0;
    unfold ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct HmB0 as [ | α0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
    exists ptyp_unit.
    split; [ apply mono_ptyp__unit | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_unit.
  - (* var *)
    destruct HmB0 as [ | α0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
    inversion HeqB; subst.
    exists (ptyp_var_f α0).
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_var_f.
  - (* arrow *)
    destruct HmB0 as [ | α0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
    inversion HeqB; subst.
    destruct (IHHr1 Hwf B1 eq_refl Hm1) as [C1 [HmC1 [HeqQ1 He1]]].
    destruct (IHHr2 Hwf B2 eq_refl Hm2) as [C2 [HmC2 [HeqQ2 He2]]].
    exists (ptyp_arrow C1 C2).
    split; [ apply mono_ptyp__arrow; auto | ].
    split; [ simpl; rewrite HeqQ1, HeqQ2; reflexivity | ].
    apply a_tyequiv__arrow; auto.
  - (* all *) destruct HmB0; simpl in HeqB; discriminate.
  - (* hole : a monotype has no ghosts *)
    destruct HmB0; simpl in HeqB; discriminate.
  - (* tophole_remove *) destruct HmB0; simpl in HeqB; discriminate.
  - (* tophole_fill *) destruct HmB0; simpl in HeqB; discriminate.
  - (* tophole_keep *) destruct HmB0; simpl in HeqB; discriminate.
  - (* flex_l : the LEFT side is a defined flexible; unfold it *)
    destruct HmB0 as [ | α0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
    inversion HeqB; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHr Hwf τ eq_refl Hmτ) as [C [HmC [HeqQ He]]].
    exists C.
    split; [ exact HmC | ].
    split; [ exact HeqQ | ].
    eapply a_tyequiv__trans;
      [ apply a_tyequiv__flex_def; eassumption | exact He ].
  - (* flex_r : the JOIN is a defined flexible.  The LEFT side is untouched, so
       do NOT destruct [HmB0]. *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHr Hwf B0 HeqB HmB0) as [C [HmC [HeqQ He]]].
    assert (Hτ : C = τ)
      by (apply ptyp_to_bskl_syn_inj; auto;
          unfold ptyp_to_bskl_syn; rewrite <- HeqQ; reflexivity).
    subst C.
    exists (ptyp_var_f α).
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    eapply a_tyequiv__trans;
      [ exact He
      | apply a_tyequiv__sym; apply a_tyequiv__flex_def; eassumption ].
Qed.

(** THE BRIDGE.  Both sides meet at the join, so they meet each other. *)
Theorem consis_refine_mono_tyequiv : forall Θ A A' Qt,
  {{ ⊢ Θ }}a ->
  mono_ptyp A ->
  mono_ptyp A' ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ Qt }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl A')) ⊳ Qt }}ad ->
  {{ Θ ⊢ A ≡ᵗ A' }}a.
Proof.
  intros Θ A A' Qt Hwf HmA HmB Hc Hr.
  rewrite (ptyp_to_bskl_inh_syn_eq HmB) in Hr.
  destruct (consis_mono_join Hc Hwf (A := A) eq_refl HmA) as [C  [HmC  [HeqC  HeA]]].
  destruct (refine_mono_join Hr Hwf (A := A') eq_refl HmB) as [C' [HmC' [HeqC' HeB]]].
  assert (HCC : C = C')
    by (apply ptyp_to_bskl_syn_inj; auto; rewrite <- HeqC, <- HeqC'; reflexivity).
  subst C'.
  eapply a_tyequiv__trans; [ exact HeA | apply a_tyequiv__sym; exact HeB ].
Qed.

(* ===================================================================== *)
(*  THE CONVERSE BRIDGE:  ≡  ⟹  consistency  (on monotypes)               *)
(*                                                                        *)
(*  Needed by [a_unify_sound_consis]: part 2's solution is stated as       *)
(*  declarative CONSISTENCY of the two subjects, while the mutual          *)
(*  induction naturally produces a type EQUIVALENCE.                       *)
(* ===================================================================== *)

(** Consistency is REFLEXIVE on monotype paintings. *)
Lemma consis_mono_refl : forall A Θ,
  mono_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (ptyp_to_bskl_syn A) }}ad.
Proof.
  intros A Θ Hm; unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  induction Hm; intros Hvis; simpl.
  - apply ad_pat_consis__unit. fsetdec.
  - apply ad_pat_consis__var; [ fsetdec | apply Hvis; simpl; fsetdec ].
  - apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHm1 | apply IHHm2 | fsetdec ];
      intros α Hα; apply Hvis; simpl; fsetdec.
Qed.

(** Consistency is SYMMETRIC on monotype paintings.  The lookup rules swap:
    a definition unfolded on the LEFT ([flex_l]) becomes one unfolded on the
    RIGHT ([flex_r]), and vice versa. *)
Lemma consis_mono_sym : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall A A', R = ptyp_to_uskl_syn A -> Qt = ptyp_to_bskl_syn A' ->
  mono_ptyp A -> mono_ptyp A' ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A') ∼ (ptyp_to_bskl_syn A) }}ad.
Proof.
  intros Ψ Θ R Qt Hc Hwf; induction Hc; intros A0 B0 HeqS HeqQ HmA0 HmB0;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct HmA0; simpl in HeqS; try discriminate.
    destruct HmB0; simpl in HeqQ; try discriminate.
    simpl. apply ad_pat_consis__unit. fsetdec.
  - (* var *)
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    destruct HmB0 as [ | β0 | ]; simpl in HeqQ; try discriminate.
    inversion HeqS; inversion HeqQ; subst.
    simpl. apply ad_pat_consis__var; [ fsetdec | assumption ].
  - (* arrow *)
    destruct HmA0 as [ | | A1 A2 Hm1 Hm2 ]; simpl in HeqS; try discriminate.
    destruct HmB0 as [ | | B1 B2 Hn1 Hn2 ]; simpl in HeqQ; try discriminate.
    inversion HeqS; inversion HeqQ; subst.
    simpl. apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ eapply IHHc1 | eapply IHHc2 | fsetdec ]; eauto.
  - (* forall_inh_tagged *) destruct HmA0; simpl in HeqS; discriminate.
  - (* forall_inh_untagged *) destruct HmA0; simpl in HeqS; discriminate.
  - (* forall_syn_tagged *) destruct HmA0; simpl in HeqS; discriminate.
  - (* forall_syn *) destruct HmA0; simpl in HeqS; discriminate.
  - (* ghostg *) destruct HmA0; simpl in HeqS; discriminate.
  - (* topholeg *) destruct HmA0; simpl in HeqS; discriminate.
  - (* hole *) destruct HmA0; simpl in HeqS; discriminate.
  - (* tophole *) destruct HmA0; simpl in HeqS; discriminate.
  - (* tophole_inh *) destruct HmA0; simpl in HeqS; discriminate.
  - (* tophole_drop *) destruct HmA0; simpl in HeqS; discriminate.
  - (* flex_l : a definition unfolded on the LEFT becomes one on the RIGHT *)
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
  - (* flex_r : ... and vice versa *)
    destruct HmB0 as [ | β0 | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_pat_consis__flex_l; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

(** [ad_pat_consis] is congruent in the tag context. *)
Lemma consis_psi_cong_local : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Ψ', Ψ [=] Ψ' ->
  {{ Ψ' ⨟ Θ ⊢ˢ R ∼ Q }}ad.
Proof.
  intros Ψ Θ R Q H; induction H; intros Ψ' Heq;
    econstructor; eauto; fsetdec.
Qed.

(** A monotype carries no TAGS, so a monotype-subject derivation has an empty
    tag context.  (Tags only ever enter through a tagged quantifier.) *)
Lemma consis_mono_psi_empty : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall A, R = ptyp_to_uskl_syn A -> mono_ptyp A ->
  Ψ [=] empty.
Proof.
  intros Ψ Θ R Qt Hc Hwf; induction Hc; intros A0 HeqS HmA0;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in HeqS;
    try (destruct HmA0; simpl in HeqS; discriminate).
  - (* unit *) fsetdec.
  - (* var *) fsetdec.
  - (* arrow *)
    destruct HmA0 as [ | | A1 A2 Hm1 Hm2 ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (He1 : Ψ1 [=] empty) by (apply (IHHc1 Hwf A1 eq_refl Hm1)).
    assert (He2 : Ψ2 [=] empty) by (apply (IHHc2 Hwf A2 eq_refl Hm2)).
    clear - H He1 He2. fsetdec.
  - (* flex_l : the subject unfolds to its DEFINITION, itself a monotype *)
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply (IHHc Hwf τ eq_refl Hmτ).
  - (* flex_r : the tag context is simply inherited; the SUBJECT is untouched *)
    apply (IHHc Hwf A0 HeqS HmA0).
Qed.

(* ===================================================================== *)
(*  THE CONVERSE BRIDGE                                                     *)
(*                                                                          *)
(*      tyequiv_mono_consis :  A ≡ᵗ B  ⟹  syn{A} ∼ syn{B}                   *)
(*                                                                          *)
(*  which the mutual soundness bundle needs (part 2's solution is stated    *)
(*  as declarative CONSISTENCY, while the mutual induction produces a type  *)
(*  EQUIVALENCE).                                                           *)
(*                                                                          *)
(*  Organisation: instead of proving transitivity of consistency by the     *)
(*  two-derivation nested induction (the shape of [ad_refine_syn_trans]),   *)
(*  we prove a BIDIRECTIONAL TRANSPORT along [≡ᵗ] — for [A ≡ᵗ B], a         *)
(*  consistency derivation whose subject is [syn{B}] can be re-subjected    *)
(*  to [syn{A}] and vice versa.  Its [trans] case is function composition,  *)
(*  and only two small single-side-equation inner inductions remain (the    *)
(*  subject-unfolding of a definition, and the arrow congruence).           *)
(*  [consis_mono_trans] then falls out as a corollary via the forward       *)
(*  bridge's [consis_mono_join].                                            *)
(* ===================================================================== *)

(** [≡ᵗ] preserves monotype-ness and ftv-visibility (both directions).
    Needed because [trans] passes through an arbitrary middle type. *)
Lemma a_tyequiv_mono_vis : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ ⊢ Θ }}a ->
  ((mono_ptyp A /\ (forall α0, α0 `in` ftvar_in_ptyp A -> a_binds_tvar α0 Θ)) ->
   (mono_ptyp A' /\ (forall α0, α0 `in` ftvar_in_ptyp A' -> a_binds_tvar α0 Θ))) /\
  ((mono_ptyp A' /\ (forall α0, α0 `in` ftvar_in_ptyp A' -> a_binds_tvar α0 Θ)) ->
   (mono_ptyp A /\ (forall α0, α0 `in` ftvar_in_ptyp A -> a_binds_tvar α0 Θ))).
Proof.
  intros * Heq Hwf; induction Heq; split; intros [Hm Hv];
    try solve [ split; assumption ]; try tauto.
  - (* flex_def, forward : α ↦ τ *)
    split.
    + eapply a_wf_aenv_binds_def_mono; eauto.
    + intros α0 Hα0.
      eapply a_wf_ptyp_ftv_tvarish;
        [ eapply a_wf_aenv_binds_def_wf_local; eauto | exact Hα0 ].
  - (* flex_def, backward : τ ↦ α *)
    split; [ apply mono_ptyp__var | ].
    intros α0 Hα0. simpl in Hα0.
    assert (α0 = α) by (clear - Hα0; fsetdec). subst.
    right; right; exists τ; assumption.
  - (* arrow, forward *)
    inversion Hm as [ | | ? ? Hm1 Hm2 ]; subst; simpl in Hv.
    destruct (IHHeq1 Hwf) as [IH1 _]. destruct (IHHeq2 Hwf) as [IH2 _].
    destruct (IH1 (conj Hm1
        (fun α0 Hα0 => Hv α0 (union_2 _ Hα0)))) as [HmB1 HvB1].
    destruct (IH2 (conj Hm2
        (fun α0 Hα0 => Hv α0 (union_3 _ Hα0)))) as [HmB2 HvB2].
    split; [ apply mono_ptyp__arrow; auto | ].
    intros α0 Hα0; simpl in Hα0.
    destruct (union_1 Hα0); auto.
  - (* arrow, backward *)
    inversion Hm as [ | | ? ? Hm1 Hm2 ]; subst; simpl in Hv.
    destruct (IHHeq1 Hwf) as [_ IH1]. destruct (IHHeq2 Hwf) as [_ IH2].
    destruct (IH1 (conj Hm1
        (fun α0 Hα0 => Hv α0 (union_2 _ Hα0)))) as [HmA1 HvA1].
    destruct (IH2 (conj Hm2
        (fun α0 Hα0 => Hv α0 (union_3 _ Hα0)))) as [HmA2 HvA2].
    split; [ apply mono_ptyp__arrow; auto | ].
    intros α0 Hα0; simpl in Hα0.
    destruct (union_1 Hα0); auto.
  - (* all, forward : a monotype is never a ∀ *)
    inversion Hm.
  - (* all, backward *)
    inversion Hm.
Qed.

(** Unfold a DEFINED subject variable inside a consistency derivation:
    only [var] / [flex_l] / [flex_r] can have subject [α1̂], and each is
    absorbed by a lookup rule on the other side. *)
Lemma consis_unfold_def_subject : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall α1 τ, R = uskl_var_f α1 ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn τ) ∼ Qt }}ad.
Proof.
  intros * Hc Hwf; induction Hc; intros α10 τ0 HeqS Hb;
    try discriminate HeqS.
  - (* var : the join is the same variable; fold it with [flex_r] *)
    inversion HeqS; subst.
    eapply ad_pat_consis__flex_r; [ exact Hb | ].
    eapply consis_psi_cong_local;
      [ apply consis_mono_refl | clear - H; fsetdec ].
    + eapply a_wf_aenv_binds_def_mono; eauto.
    + intros β Hβ.
      eapply a_wf_ptyp_ftv_tvarish;
        [ eapply a_wf_aenv_binds_def_wf_local; eauto | exact Hβ ].
  - (* flex_l : the same definition was already unfolded *)
    inversion HeqS; subst.
    assert (Huniq : uniq Θ) by (apply a_wf_aenv_uniq; auto).
    assert (Heqτ : abind_flex_mono_def τ = abind_flex_mono_def τ0)
      by (eapply binds_unique; eauto).
    inversion Heqτ; subst.
    exact Hc.
  - (* flex_r : the JOIN unfolds; the subject is untouched *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

(** Transport an arrow subject componentwise: only [arrow] / [flex_r] can
    have an arrow subject, and the transport is generic in the two
    component transports. *)
Lemma consis_arrow_subject_transport : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  forall R1 R2 R1' R2',
  R = uskl_arrow R1 R2 ->
  (forall Ψ' Q', {{ Ψ' ⨟ Θ ⊢ˢ R1 ∼ Q' }}ad -> {{ Ψ' ⨟ Θ ⊢ˢ R1' ∼ Q' }}ad) ->
  (forall Ψ' Q', {{ Ψ' ⨟ Θ ⊢ˢ R2 ∼ Q' }}ad -> {{ Ψ' ⨟ Θ ⊢ˢ R2' ∼ Q' }}ad) ->
  {{ Ψ ⨟ Θ ⊢ˢ (uskl_arrow R1' R2') ∼ Qt }}ad.
Proof.
  intros * Hc; induction Hc; intros S1' S2' R1' R2' HeqS Htr1 Htr2;
    try discriminate HeqS.
  - (* arrow *)
    inversion HeqS; subst.
    eapply ad_pat_consis__arrow; [ apply Htr1 | apply Htr2 | ]; eauto.
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

(** THE TRANSPORT.  For [A ≡ᵗ B] on monotypes, consistency derivations can
    be re-subjected between [syn{A}] and [syn{B}], in BOTH directions (the
    two directions are proved simultaneously so that [sym] just swaps and
    [trans] just composes). *)
Lemma tyequiv_mono_consis_transport : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ ⊢ Θ }}a ->
  mono_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  (forall Ψ Qt, {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A') ∼ Qt }}ad ->
     {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ Qt }}ad) /\
  (forall Ψ Qt, {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ Qt }}ad ->
     {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A') ∼ Qt }}ad).
Proof.
  intros Θ A A' Heq Hwf; induction Heq; intros Hm Hv.
  - (* refl *)
    split; intros Ψ Qt Hc; exact Hc.
  - (* sym : swap the IH's directions *)
    destruct (a_tyequiv_mono_vis Heq Hwf) as [_ Hback].
    destruct (Hback (conj Hm Hv)) as [HmA HvA].
    destruct (IHHeq Hwf HmA HvA) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - (* trans : compose *)
    destruct (a_tyequiv_mono_vis Heq1 Hwf) as [Hfwd _].
    destruct (Hfwd (conj Hm Hv)) as [HmB HvB].
    destruct (IHHeq1 Hwf Hm Hv) as [H1l H1r].
    destruct (IHHeq2 Hwf HmB HvB) as [H2l H2r].
    split; intros Ψ Qt Hc; [ apply H1l, H2l, Hc | apply H2r, H1r, Hc ].
  - (* flex_def : α̂ ≡ τ with α̂ := τ *)
    split; intros Ψ Qt Hc.
    + (* fold : one lookup rule *)
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl.
      eapply ad_pat_consis__flex_l; [ eassumption | exact Hc ].
    + (* unfold : peel the subject's lookup *)
      eapply consis_unfold_def_subject;
        [ exact Hc | exact Hwf | | eassumption ].
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl; reflexivity.
  - (* arrow : componentwise transport *)
    inversion Hm as [ | | ? ? Hm1 Hm2 ]; subst; simpl in Hv.
    assert (Hv1 : forall α, α `in` ftvar_in_ptyp A1 -> a_binds_tvar α Θ)
      by (intros α Hα; apply Hv; fsetdec).
    assert (Hv2 : forall α, α `in` ftvar_in_ptyp A2 -> a_binds_tvar α Θ)
      by (intros α Hα; apply Hv; fsetdec).
    destruct (IHHeq1 Hwf Hm1 Hv1) as [H1l H1r].
    destruct (IHHeq2 Hwf Hm2 Hv2) as [H2l H2r].
    split; intros Ψ Qt Hc.
    + eapply consis_arrow_subject_transport with (R1' := ptyp_to_uskl_syn A1);
        [ exact Hc | | exact H1l | exact H2l ].
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl; reflexivity.
    + eapply consis_arrow_subject_transport with (R1' := ptyp_to_uskl_syn B1);
        [ exact Hc | | exact H1r | exact H2r ].
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl; reflexivity.
  - (* all : a monotype is never a ∀ *)
    inversion Hm.
Qed.

(** THE CONVERSE BRIDGE.  [A ≡ᵗ B] on monotypes yields consistency of the
    two syn paintings: transport [B]'s reflexivity derivation. *)
Theorem tyequiv_mono_consis : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ ⊢ Θ }}a ->
  mono_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (ptyp_to_bskl_syn A') }}ad.
Proof.
  intros * Heq Hwf Hm Hv.
  destruct (a_tyequiv_mono_vis Heq Hwf) as [Hfwd _].
  destruct (Hfwd (conj Hm Hv)) as [HmB HvB].
  destruct (tyequiv_mono_consis_transport Heq Hwf Hm Hv) as [Hd1 _].
  apply Hd1.
  apply consis_mono_refl; auto.
Qed.

(** Transitivity of consistency on monotype paintings — recorded for the
    paper's account: the forward bridge extracts [A ≡ᵗ B] from the first
    derivation, and the transport re-subjects the second. *)
Corollary consis_mono_trans : forall Θ A A' A0,
  {{ ⊢ Θ }}a ->
  mono_ptyp A -> mono_ptyp A' ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (ptyp_to_bskl_syn A') }}ad ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A') ∼ (ptyp_to_bskl_syn A0) }}ad ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (ptyp_to_bskl_syn A0) }}ad.
Proof.
  intros * Hwf HmA HmB HvA Hc1 Hc2.
  destruct (consis_mono_join Hc1 Hwf (A := A) eq_refl HmA)
    as [B' [HmB' [HeqB' HeqAB']]].
  assert (HBB' : B' = A')
    by (apply ptyp_to_bskl_syn_inj; auto;
        unfold ptyp_to_bskl_syn; rewrite <- HeqB'; reflexivity).
  subst B'.
  destruct (tyequiv_mono_consis_transport HeqAB' Hwf HmA HvA) as [Hd1 _].
  apply Hd1. exact Hc2.
Qed.
