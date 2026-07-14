(** THE BRIDGE that the corrected [Flex-Flex-Assign] needs.

    With the rule's premise now CONSISTENCY, unification soundness must derive a
    type EQUIVALENCE  [Θ ⊢ A ≡ᵗ B]  from what consistency soundness gives it:
    a coloured JOIN [Qt] with

        syn{A} ≈ Qt      (declarative consistency of the SUBJECT with the join)
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
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
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

(** A definition is a monotype (it is stored that way). *)
Lemma a_wf_aenv_binds_def_mono : forall Θ γ τ,
  a_wf_aenv Θ ->
  binds γ (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ.
Proof.
  intros Θ γ τ Hwf; induction Hwf; intros Hb;
    try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
    try discriminate; try (inversion Heqb; subst; assumption); auto.
Qed.

Lemma a_wf_aenv_uniq_local : forall Θ, a_wf_aenv Θ -> uniq Θ.
Proof. intros Θ H; induction H; solve_uniq. Qed.

(** A definition is well-formed in its own (tail) context, hence in the whole. *)
Lemma a_wf_aenv_binds_def_wf_local : forall Θ γ τ,
  a_wf_aenv Θ ->
  binds γ (abind_flex_mono_def τ) Θ ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ γ τ Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
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
Lemma ptyp_to_bskl_syn_inj : forall A B,
  mono_ptyp A -> mono_ptyp B ->
  ptyp_to_bskl_syn A = ptyp_to_bskl_syn B ->
  A = B.
Proof.
  unfold ptyp_to_bskl_syn.
  intros A B HmA; revert B; induction HmA as [ | X | A1 A2 Hm1 IH1 Hm2 IH2 ];
    intros B HmB Heq; destruct HmB; simpl in Heq; try discriminate.
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
Lemma consis_mono_join : forall Ψ Θ S Qt,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  a_wf_aenv Θ ->
  forall A, S = ptyp_to_uskl_syn A -> mono_ptyp A ->
  exists C, mono_ptyp C /\ Qt = ptyp_to_bskl_syn C /\ Θ ⊢ A ≡ᵗ C.
Proof.
  intros Ψ Θ S Qt Hc Hwf; induction Hc; intros A0 HeqS HmA0;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct HmA0 as [ | X0 | A1 A2 Hm1 Hm2 ]; simpl in HeqS; try discriminate.
    exists ptyp_unit.
    split; [ apply mono_ptyp__unit | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_unit.
  - (* var *)
    destruct HmA0 as [ | X0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    exists (ptyp_var_f X0).
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
    destruct HmA0 as [ | X0 | ]; simpl in HeqS; try discriminate.
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
  Θ ⨟ Δ ⊢ᵣᵃ Qb ⊳ Qt ->
  a_wf_aenv Θ ->
  forall B, Qb = ptyp_to_bskl_syn B -> mono_ptyp B ->
  exists C, mono_ptyp C /\ Qt = ptyp_to_bskl_syn C /\ Θ ⊢ B ≡ᵗ C.
Proof.
  intros Θ Δ Qb Qt Hr Hwf; induction Hr; intros B0 HeqB HmB0;
    unfold ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct HmB0 as [ | X0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
    exists ptyp_unit.
    split; [ apply mono_ptyp__unit | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_unit.
  - (* var *)
    destruct HmB0 as [ | X0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
    inversion HeqB; subst.
    exists (ptyp_var_f X0).
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_var_f.
  - (* arrow *)
    destruct HmB0 as [ | X0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
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
    destruct HmB0 as [ | X0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
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
Theorem consis_refine_mono_tyequiv : forall Θ A B Qt,
  a_wf_aenv Θ ->
  mono_ptyp A ->
  mono_ptyp B ->
  empty ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl_syn A) ≈ Qt ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (ptyp_to_pskl B)) ⊳ Qt ->
  Θ ⊢ A ≡ᵗ B.
Proof.
  intros Θ A B Qt Hwf HmA HmB Hc Hr.
  rewrite (ptyp_to_bskl_inh_syn_eq HmB) in Hr.
  destruct (consis_mono_join Hc Hwf (A := A) eq_refl HmA) as [C  [HmC  [HeqC  HeA]]].
  destruct (refine_mono_join Hr Hwf (B := B) eq_refl HmB) as [C' [HmC' [HeqC' HeB]]].
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
  (forall X, X `in` ftvar_in_ptyp A -> a_binds_tvar X Θ) ->
  empty ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl_syn A) ≈ (ptyp_to_bskl_syn A).
Proof.
  intros A Θ Hm; unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  induction Hm; intros Hvis; simpl.
  - apply ad_pat_consis__unit. fsetdec.
  - apply ad_pat_consis__var; [ fsetdec | apply Hvis; simpl; fsetdec ].
  - apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHm1 | apply IHHm2 | fsetdec ];
      intros X HX; apply Hvis; simpl; fsetdec.
Qed.

(** Consistency is SYMMETRIC on monotype paintings.  The lookup rules swap:
    a definition unfolded on the LEFT ([flex_l]) becomes one unfolded on the
    RIGHT ([flex_r]), and vice versa. *)
Lemma consis_mono_sym : forall Ψ Θ S Qt,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  a_wf_aenv Θ ->
  forall A B, S = ptyp_to_uskl_syn A -> Qt = ptyp_to_bskl_syn B ->
  mono_ptyp A -> mono_ptyp B ->
  empty ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl_syn B) ≈ (ptyp_to_bskl_syn A).
Proof.
  intros Ψ Θ S Qt Hc Hwf; induction Hc; intros A0 B0 HeqS HeqQ HmA0 HmB0;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct HmA0; simpl in HeqS; try discriminate.
    destruct HmB0; simpl in HeqQ; try discriminate.
    simpl. apply ad_pat_consis__unit. fsetdec.
  - (* var *)
    destruct HmA0 as [ | X0 | ]; simpl in HeqS; try discriminate.
    destruct HmB0 as [ | Y0 | ]; simpl in HeqQ; try discriminate.
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
    destruct HmA0 as [ | X0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
  - (* flex_r : ... and vice versa *)
    destruct HmB0 as [ | Y0 | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_pat_consis__flex_l; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

(** [ad_pat_consis] is congruent in the tag context. *)
Lemma consis_psi_cong_local : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  forall Ψ', Ψ [=] Ψ' ->
  Ψ' ⨟ Θ ⊨ₛᵃ S ≈ Q.
Proof.
  intros Ψ Θ S Q H; induction H; intros Ψ' Heq;
    econstructor; eauto; fsetdec.
Qed.

(** A monotype carries no TAGS, so a monotype-subject derivation has an empty
    tag context.  (Tags only ever enter through a tagged quantifier.) *)
Lemma consis_mono_psi_empty : forall Ψ Θ S Qt,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  a_wf_aenv Θ ->
  forall A, S = ptyp_to_uskl_syn A -> mono_ptyp A ->
  Ψ [=] empty.
Proof.
  intros Ψ Θ S Qt Hc Hwf; induction Hc; intros A0 HeqS HmA0;
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
    destruct HmA0 as [ | X0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply (IHHc Hwf τ eq_refl Hmτ).
  - (* flex_r : the tag context is simply inherited; the SUBJECT is untouched *)
    apply (IHHc Hwf A0 HeqS HmA0).
Qed.

(* ===================================================================== *)
(*  REMAINING: [consis_mono_trans] — consistency is TRANSITIVE on monotype *)
(*  paintings — and then the CONVERSE bridge                                *)
(*                                                                          *)
(*      tyequiv_mono_consis :  A ≡ᵗ B  ⟹  syn{A} ≈ syn{B}                   *)
(*                                                                          *)
(*  which [a_unify_sound_consis] needs (part 2's solution is stated as       *)
(*  declarative CONSISTENCY, while the mutual induction produces a type      *)
(*  EQUIVALENCE).  Its ≡-induction needs refl / sym / trans of consistency:  *)
(*  refl and sym are proved above; TRANS is not.                             *)
(*                                                                          *)
(*  Shape (mapped, not landed — it is plumbing, not mathematics): OUTER      *)
(*  induction on the SECOND derivation; INNER induction on the FIRST to peel *)
(*  [flex_l] (which unfolds the SUBJECT while the right stands still);       *)
(*  [flex_r] unfolds the JOIN and falls to the outer IH.  Exactly the shape  *)
(*  of [ad_refine_syn_trans] in prop_precise.v.  The fiddly part is keeping  *)
(*  BOTH derivations''' indices as variables across the two inductions:          *)
(*  [syn{A}] is not a variable, so the subject must be carried as [Sa] with  *)
(*  [Sa = syn{A}] on the side, and the join [remember]ed.  Beware: a bare    *)
(*  [subst] silently eats that side equation.                                *)
(* ===================================================================== *)
