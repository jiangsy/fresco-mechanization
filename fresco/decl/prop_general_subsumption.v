(** Fresco declarative general subsumption (paper Lemma 3.1 / B.5), in the
    [utyp]/[btyp] split syntax.  Self-contained: the consistency-composition
    and tag-refinement machinery,
    Consistency-Subtyping Transitivity, the [FN^n] spine transitivity, and the
    headline [d_sd_typing_general_subsumption] ("Closed under the global
    context").  Since the base-term restriction on [d_typing__sub] was removed
    (the paper's "Removed base terms" rework), general subsumption is a RULE of
    [d_typing]; the proof obligation lives on the SYNTAX-DIRECTED side
    [d_sd_typing], which has no [Sub] rule. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
From Hammer Require Export Tactics.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_basic.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_weakening.
Require Import src.fresco.decl.prop_renaming.
Require Import src.fresco.decl.prop_tag_swap.

Set Implicit Arguments.

(* ======================================================================== *)
(*  Auxiliary facts: the compose_tags                                       *)
(*  witness + consistency composition (paper B.2), coercion / opening /      *)
(*  free-variable lemmas, and consistency basics.                            *)
(* ======================================================================== *)

(** [compose_tags C B] is the tag context produced by composing the two
    consistency derivations through a synthesised middle type.  Making it an
    explicit *function of (C,B)* (rather than an existential witness) is the
    crux of B.2: the witness is then manifestly independent of the variable
    used to open a quantifier body, so the cofinite case has a uniform Δc.

    The only rule that *grows* the context is the tagged→inh composition
    (paper [ForallInh] with β1=ε): a tagged-∀ that was dropped on the
    synthesised side ([ForallSyn], no tag) must be re-recorded when it meets
    an inherited ∀.  Hence the result is a strict superset of [Δa ∪ Δb]. *)
Fixpoint compose_tags (C : utyp) (B : btyp) {struct C} : atoms :=
  match C with
  | utyp_arrow C1 C2 =>
      match B with
      | btyp_arrow B1 B2 => compose_tags C1 B1 `union` compose_tags C2 B2
      | _ => empty
      end
  | utyp_all_tag ε C0 =>
      match B with
      | btyp_all_inh B0 => add ε (compose_tags C0 B0)
      | btyp_all_syn B0 => compose_tags C0 B0
      | _ => empty
      end
  | utyp_all_syn C0 =>
      match B with
      | btyp_all_inh B0 => compose_tags C0 B0
      | btyp_all_syn B0 => compose_tags C0 B0
      | _ => empty
      end
  | _ => empty
  end.

(** [compose_tags] inspects only the head constructors and tag names, never
    type variables, so it is invariant under opening with a variable. *)
Lemma compose_tags_open_rec : forall C B α' β k,
    compose_tags (open_utyp_wrt_utyp_rec k (utyp_var_f α') C)
                 (open_btyp_wrt_btyp_rec k (btyp_var_f β) B) = compose_tags C B.
Proof.
  induction C; intros B α' β k; destruct B; simpl;
    repeat match goal with
           | [ |- context[lt_eq_lt_dec ?a ?b] ] =>
               destruct (lt_eq_lt_dec a b) as [[|]|]
           end; simpl; try reflexivity;
    repeat match goal with
           | [ IH : forall _ _ _ _, compose_tags _ _ = compose_tags _ _ |- _ ] =>
               rewrite IH
           end; reflexivity.
Qed.

Lemma compose_tags_open : forall C B α β,
    compose_tags (open_utyp_wrt_utyp C (utyp_var_f α))
                 (open_btyp_wrt_btyp B (btyp_var_f β)) = compose_tags C B.
Proof.
  intros C B α β. unfold open_utyp_wrt_utyp, open_btyp_wrt_btyp.
  apply compose_tags_open_rec.
Qed.

(** A synthesised target carries no inh quantifier, so composing against it
    introduces no tag: [compose_tags C B = nil].  This is what lets the
    [mode_ti] infer base keeps its empty-tag output. *)
Lemma compose_tags_is_styp_nil : forall B C,
    is_styp B -> compose_tags C B [=] empty.
Proof.
  intros B C Hsyn. generalize dependent C.
  induction Hsyn; intros C0.
  - destruct C0; simpl; reflexivity.
  - destruct C0; simpl; reflexivity.
  - destruct C0; simpl; try reflexivity. rewrite IHHsyn1, IHHsyn2. fsetdec.
  - destruct C0; simpl; try reflexivity;
      (pick fresh α for L;
       rewrite <- (compose_tags_open _ B α α);
       apply (H0 α); fsetdec).
Qed.

(** Instantiate both opened sub-derivations at a variable [α], reshape their
    middle types back through the coercions, fire the size-induction IH, and
    fold [compose_tags] over the opening (it is invariant under [α]).  Leaves
    [Hincl] and [Hcons] for the body. *)
Ltac binder_ih IHn HszA HH HH0 AA α :=
  let HcX := fresh "HcX" in
  let HdX := fresh "HdX" in
  pose proof (HH α ltac:(solve_notin_auto)) as HcX;
  pose proof (HH0 α ltac:(solve_notin_auto)) as HdX;
  change (btyp_var_f α) with (ptyp_to_btyp_syn (ptyp_var_f α)) in HcX;
  rewrite <- ptyp_to_btyp_syn_open in HcX;
  change (utyp_var_f α) with (ptyp_to_utyp_syn (ptyp_var_f α)) in HdX;
  rewrite <- ptyp_to_utyp_syn_open in HdX;
  edestruct (IHn (open_ptyp_wrt_ptyp AA (ptyp_var_f α))
                 ltac:(rewrite size_ptyp_open_ptyp_wrt_ptyp_var; exact HszA)
                 _ _ _ _ _ HcX HdX) as [Hincl Hcons];
  rewrite compose_tags_open in Hincl;
  rewrite compose_tags_open in Hcons.

(** Paper B.2, native split form for a synthesized middle type.  Strengthened
    with the explicit witness [compose_tags C B] and proved by induction on the
    size of the middle type [A]. *)
Lemma d_consis_compose_strong : forall n A,
    size_ptyp A < n ->
    forall Δa Δb Γ C B,
    {{ Δa ⨟ Γ ⊢ C ∼ ptyp_to_btyp_syn A }}d ->
    {{ Δb ⨟ Γ ⊢ ptyp_to_utyp_syn A ∼ B }}d ->
    (Δa `union` Δb) [<=] (compose_tags C B) /\ {{ (compose_tags C B) ⨟ Γ ⊢ C ∼ B }}d.
Proof.
  induction n; intros A Hsz Δa Δb Γ C B H1 H2.
  - lia.
  - destruct A; simpl in H1, H2.
    + (* ptyp_unit *)
      dependent destruction H1. dependent destruction H2. simpl.
      split; [ fsetdec | apply d_consis__unit; reflexivity ].
    + (* ptyp_var_b — no consistency rule has a [btyp_var_b] RHS *)
      inversion H1.
    + (* ptyp_var_f *)
      dependent destruction H1. dependent destruction H2. simpl.
      split; [ fsetdec | apply d_consis__var; [ assumption | reflexivity ] ].
    + (* ptyp_arrow A1 A2 *)
      dependent destruction H1. dependent destruction H2. simpl.
      simpl in Hsz. pose proof (size_ptyp_min A1). pose proof (size_ptyp_min A2).
      assert (HszA1 : size_ptyp A1 < n) by lia.
      assert (HszA2 : size_ptyp A2 < n) by lia.
      edestruct (IHn A1 HszA1 _ _ _ _ _ H1_ H2_) as [Hincl1 Hcons1].
      edestruct (IHn A2 HszA2 _ _ _ _ _ H1_0 H2_0) as [Hincl2 Hcons2].
      split;
        [ fsetdec
        | eapply d_consis__arrow; [ exact Hcons1 | exact Hcons2 | reflexivity ] ].
    + (* ptyp_all A — A is the (body of the) middle type *)
      assert (HszA : size_ptyp A < n) by (simpl in Hsz; lia).
      dependent destruction H1; dependent destruction H2.
      { (* tagged → syn → inh : the only context-growing composition *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [α0 HX0].
          binder_ih IHn HszA H H0 A α0. simpl. fsetdec. }
        { simpl. eapply d_consis__forall_inh_tagged with (L := L `union` L0);
            [ | reflexivity ].
          intros α Hα. binder_ih IHn HszA H H0 A α. exact Hcons. } }
      { (* tagged → syn → syn *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [α0 HX0].
          binder_ih IHn HszA H H0 A α0. simpl. fsetdec. }
        { simpl. apply d_consis__forall_syn_tagged with (L := L `union` L0).
          intros α Hα. binder_ih IHn HszA H H0 A α. exact Hcons. } }
      { (* syn → syn → inh *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [α0 HX0].
          binder_ih IHn HszA H H0 A α0. simpl. fsetdec. }
        { simpl. apply d_consis__forall_inh_untagged with (L := L `union` L0).
          intros α Hα. binder_ih IHn HszA H H0 A α. exact Hcons. } }
      { (* syn → syn → syn *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [α0 HX0].
          binder_ih IHn HszA H H0 A α0. simpl. fsetdec. }
        { simpl. apply d_consis__forall_syn with (L := L `union` L0).
          intros α Hα. binder_ih IHn HszA H H0 A α. exact Hcons. } }
Qed.

Lemma d_consis_compose : forall Δa Δb Γ C A B,
    {{ Δa ⨟ Γ ⊢ C ∼ ptyp_to_btyp_syn A }}d ->
    {{ Δb ⨟ Γ ⊢ ptyp_to_utyp_syn A ∼ B }}d ->
    exists Δc, (Δa `union` Δb) [<=] Δc /\ {{ Δc ⨟ Γ ⊢ C ∼ B }}d.
Proof.
  intros Δa Δb Γ C A B H1 H2.
  exists (compose_tags C B).
  exact (@d_consis_compose_strong (S (size_ptyp A)) A ltac:(lia) Δa Δb Γ C B H1 H2).
Qed.

(** Coercions never introduce free type variables. *)
Lemma ftvar_btyp_to_utyp_syn : forall B,
    ftvar_in_utyp (btyp_to_utyp_syn B) [<=] ftvar_in_btyp B.
Proof. induction B; simpl; fsetdec. Qed.

(** A synthesised [btyp] is the syn-painting of its own forgetful image, so
    [d_consis_compose]'s [ptyp_to_btyp_syn A] middle can be fed an arbitrary
    [is_styp] btyp via [A := btyp_to_ptyp B]. *)
Lemma ptyp_to_utyp_syn_btyp_to_ptyp : forall B,
    ptyp_to_utyp_syn (btyp_to_ptyp B) = btyp_to_utyp_syn B.
Proof.
  induction B; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); rewrite IHB; reflexivity.
Qed.

Lemma ptyp_to_btyp_syn_btyp_to_ptyp : forall B,
    is_styp B ->
    ptyp_to_btyp_syn (btyp_to_ptyp B) = B.
Proof.
  intros B Hsyn. induction Hsyn; simpl; try reflexivity.
  - rewrite IHHsyn1, IHHsyn2; reflexivity.
  - f_equal.
    pick fresh α for (L `union` ftvar_in_btyp B).
    apply open_btyp_wrt_btyp_inj with (α1 := α).
    + rewrite ftvar_ptyp_to_btyp_syn, ftvar_btyp_to_ptyp. solve_notin_auto.
    + fsetdec.
    + specialize (H0 α ltac:(solve_notin_auto)).
      rewrite btyp_to_ptyp_open in H0.
      rewrite ptyp_to_btyp_syn_open in H0.
      exact H0.
Qed.

(** ===== [utyp_to_btyp] opening / erasure lemmas ===== *)

(** [utyp_to_btyp] commutes with opening. *)
Lemma utyp_to_btyp_open_rec : forall C1 C2 k,
    utyp_to_btyp (open_utyp_wrt_utyp_rec k C2 C1) =
    open_btyp_wrt_btyp_rec k (utyp_to_btyp C2) (utyp_to_btyp C1).
Proof.
  induction C1; intros C2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHC1_1, IHC1_2; reflexivity.
  - rewrite IHC1; reflexivity.
  - rewrite IHC1; reflexivity.
Qed.

Lemma utyp_to_btyp_open : forall C1 C2,
    utyp_to_btyp (open_utyp_wrt_utyp C1 C2) =
    open_btyp_wrt_btyp (utyp_to_btyp C1) (utyp_to_btyp C2).
Proof.
  intros. unfold open_utyp_wrt_utyp, open_btyp_wrt_btyp.
  apply utyp_to_btyp_open_rec.
Qed.

(** A [utyp]'s [btyp] erasure has only synthesised foralls, so it is [is_styp]
    once locally closed (lc rules out a dangling [var_b]). *)
Lemma is_styp_utyp_to_btyp : forall C,
    lc_utyp C -> is_styp (utyp_to_btyp C).
Proof.
  intros C Hlc. induction Hlc; simpl.
  - apply is_styp__unit.
  - apply is_styp__var.
  - apply is_styp__arrow; assumption.
  - apply is_styp__all with (L := empty). intros α Hα.
    replace (open_btyp_wrt_btyp (utyp_to_btyp C) (btyp_var_f α))
      with (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f α)))
      by (rewrite utyp_to_btyp_open; reflexivity).
    apply H0.
  - apply is_styp__all with (L := empty). intros α Hα.
    replace (open_btyp_wrt_btyp (utyp_to_btyp C) (btyp_var_f α))
      with (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f α)))
      by (rewrite utyp_to_btyp_open; reflexivity).
    apply H0.
Qed.

(** Empty-context composition: arbitrary input tag contexts, syn middle and
    target ⟹ empty output (the [mode_ti] infer base demands the empty set). *)
Lemma d_consis_compose_syn_nil_l : forall Δa Δb Γ C B2 B,
    is_styp B2 -> is_styp B ->
    {{ Δa ⨟ Γ ⊢ C ∼ B2 }}d ->
    {{ Δb ⨟ Γ ⊢ (btyp_to_utyp_syn B2) ∼ B }}d ->
    {{ empty ⨟ Γ ⊢ C ∼ B }}d.
Proof.
  intros Δa Δb Γ C B2 B Hsyn2 HsynB Hc Hd.
  rewrite <- (ptyp_to_btyp_syn_btyp_to_ptyp Hsyn2) in Hc.
  rewrite <- (ptyp_to_utyp_syn_btyp_to_ptyp B2) in Hd.
  pose proof (@d_consis_compose_strong (S (size_ptyp (btyp_to_ptyp B2)))
                (btyp_to_ptyp B2) ltac:(lia) Δa Δb Γ C B Hc Hd) as [_ Hcons].
  exact (d_consis_equiv (@compose_tags_is_styp_nil B C HsynB) Hcons).
Qed.

(** A consistency derivation's [utyp] side is locally closed. *)
Lemma d_consis_lc_utyp : forall Δ Γ C B,
    {{ Δ ⨟ Γ ⊢ C ∼ B }}d -> lc_utyp C.
Proof.
  intros Δ Γ C B H. induction H.
  - apply lc_utyp_unit.
  - apply lc_utyp_var_f.
  - pick fresh α. apply lc_utyp_all_tag_exists with (α1 := α). apply H0. fsetdec.
  - pick fresh α. apply lc_utyp_all_syn_exists with (α1 := α). apply H0. fsetdec.
  - pick fresh α. apply lc_utyp_all_tag_exists with (α1 := α). apply H0. fsetdec.
  - pick fresh α. apply lc_utyp_all_syn_exists with (α1 := α). apply H0. fsetdec.
  - apply lc_utyp_arrow; assumption.
Qed.

(** ⭐ …and so is its [btyp] side.  ⚙ The [lc] twin of [d_consis_wf] /
    [d_sub_wf]: those need the subject WELL-SCOPED and give well-scopedness
    back, which is more than a caller who only wants to build an
    [a_tyequiv__refl] can pay.  Kept GENERAL in Γ and Δ — the closed instance
    would hide exactly the side conditions a bridge has to surface. *)
Lemma d_consis_lc_btyp : forall Δ Γ C B,
    {{ Δ ⨟ Γ ⊢ C ∼ B }}d -> lc_utyp C -> lc_btyp B.
Proof.
  intros Δ Γ C B H. induction H; intros Hlc.
  - apply lc_btyp_unit.
  - apply lc_btyp_var_f.
  - inversion Hlc; subst. pick fresh α.
    apply lc_btyp_all_inh_exists with (α1 := α). apply H0; auto.
  - inversion Hlc; subst. pick fresh α.
    apply lc_btyp_all_inh_exists with (α1 := α). apply H0; auto.
  - inversion Hlc; subst. pick fresh α.
    apply lc_btyp_all_syn_exists with (α1 := α). apply H0; auto.
  - inversion Hlc; subst. pick fresh α.
    apply lc_btyp_all_syn_exists with (α1 := α). apply H0; auto.
  - inversion Hlc; subst. apply lc_btyp_arrow; auto.
Qed.

Lemma d_sub_lc_btyp : forall m Δ Γ C B,
    {{ Δ ⨟ Γ ⊢[ m ] C ⩽ B }}d -> lc_utyp C -> lc_btyp B.
Proof.
  intros m Δ Γ C B H. induction H; intros Hlc.
  - eapply d_consis_lc_btyp; eassumption.
  - eapply d_consis_lc_btyp; eassumption.
  - pick fresh α. apply lc_btyp_all_inh_exists with (α1 := α).
    apply H1; [ solve_notin_auto | exact Hlc ].
  - inversion Hlc; subst. apply lc_btyp_arrow;
      [ eapply d_consis_lc_btyp; eassumption | auto ].
  - (* forall_l: the premise's subject is the body opened by [ph] *)
    inversion Hlc; subst. apply IHd_sub.
    apply lc_body_utyp_wrt_utyp;
      [ intro α; auto | eapply d_wf_utyp_lc; eassumption ].
  - inversion Hlc; subst. apply IHd_sub.
    apply lc_body_utyp_wrt_utyp;
      [ intro α; auto | eapply d_wf_utyp_lc; eassumption ].
Qed.

(** A guarded middle forces a guarded source: consistency against a guarded
    ([unit]/[var]/[arrow]) erasure leaves no room for a forall on the LHS. *)
Lemma d_consis_guarded_lhs : forall Δ Γ Csrc C,
    guarded_utyp C ->
    {{ Δ ⨟ Γ ⊢ Csrc ∼ (utyp_to_btyp C) }}d ->
    guarded_utyp Csrc.
Proof.
  intros Δ Γ Csrc C Hg Hc.
  inversion Hg; subst; simpl in Hc.
  - inversion Hc; subst. apply guarded_utyp__unit.
  - inversion Hc; subst. apply guarded_utyp__var.
  - inversion Hc; subst. apply guarded_utyp__arrow.
    + eapply d_consis_lc_utyp; eauto.
    + eapply d_consis_lc_utyp; eauto.
Qed.

(** Mode arithmetic for the [FN^n] generalisation: replace the trailing
    [mode_ti] of an [FN^n TI] mode with [m_new]. *)
Fixpoint mode_fn_n_subst (m_orig m_new : mode) : mode :=
  match m_orig with
  | mode_ti => m_new
  | mode_tc => mode_tc
  | mode_fn m => mode_fn (mode_fn_n_subst m m_new)
  end.

(** * Paper-faithful general subsumption (2026-06 rework).

    The reworked paper (syntax-directed.tex) proves general subsumption
    over the ORDINARY subtyping/typing ([d_sub] / [d_typing]) using three
    auxiliary lemmas — Consistency-Subtyping Transitivity, Subtyping
    Transitivity, Function Subtyping — and a mode-indexed ([FN^n])
    generalisation that subtypes only the synthesised RESULT tail while
    keeping the function arguments fixed.

    Function Subtyping (syntax-directed.tex:256): if a function source is
    subtyped, the target is a polymorphic function shape
    [inh{∀ᾱ}.B1 → B2] with the argument matched by consistency (invariant)
    and the result subtyped at the decremented mode.  Here we prove the
    non-[TC] modes, where the inh-∀ prefix ᾱ is empty (the paper notes ᾱ
    is non-empty only when M = TC, via repeated [ForallR]). *)

(** Mono chain for the n=0 abstraction (tail) case.  [is_styp (inh A)]
    forces [A] monomorphic — the only way the *inherited* painting can be
    synthesised is to carry no ∀ (a ∀ paints to [btyp_all_inh], never
    [btyp_all_syn]). *)
Lemma is_styp_ptyp_to_btyp_inh_mono : forall A,
    is_styp (ptyp_to_btyp_inh A) -> mono_ptyp A.
Proof.
  induction A; simpl; intros Hst.
  - constructor.
  - inversion Hst.
  - constructor.
  - dependent destruction Hst. constructor; auto.
  - inversion Hst.
Qed.

(** Paint round-trip: erasing a syn-painted [btyp] to a [utyp] equals the
    direct utyp painting (structural). *)
Lemma btyp_to_utyp_syn_ptyp_to_btyp_syn : forall A,
    btyp_to_utyp_syn (ptyp_to_btyp_syn A) = ptyp_to_utyp_syn A.
Proof.
  induction A; simpl; try reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. reflexivity.
Qed.

(** Consistency rigidity for monomorphic sources: a [mono] syn-source pins
    the bidirectional RHS to its syn painting (no tags, no colour freedom).
    Holds at ANY tag context — a [mono] source carries no [tag], so the
    arrow recursion threads through whatever [Δ] the split produced. *)
Lemma d_consis_mono_determines : forall Δ Γ A B,
    {{ Δ ⨟ Γ ⊢ (ptyp_to_utyp_syn A) ∼ B }}d ->
    mono_ptyp A ->
    B = ptyp_to_btyp_syn A.
Proof.
  intros Δ Γ A B Hcons Hmono. generalize dependent B. generalize dependent Δ.
  induction Hmono; intros Δ B Hcons; simpl in *.
  - dependent destruction Hcons. reflexivity.
  - dependent destruction Hcons. reflexivity.
  - dependent destruction Hcons.
    f_equal; [ eapply IHHmono1 | eapply IHHmono2 ]; eassumption.
Qed.

Lemma is_styp_arrow_r : forall B1 B2, is_styp (btyp_arrow B1 B2) -> is_styp B2.
Proof. intros B1 B2 H. inversion H; subst; assumption. Qed.

Lemma is_styp_arrow_l : forall B1 B2, is_styp (btyp_arrow B1 B2) -> is_styp B1.
Proof. intros B1 B2 H. inversion H; subst; assumption. Qed.

(** A subtyping's source is locally closed (the standard lngen fact: the
    [forall_l] instantiation case goes through the degree-inversion lemma). *)
Lemma d_sub_lc_l : forall m Δ Γ C B, {{ Δ ⨟ Γ ⊢[ m ] C ⩽ B }}d -> lc_utyp C.
Proof.
  intros m Δ Γ C B H. induction H.
  - eapply d_consis_lc_utyp; eassumption.
  - eapply d_consis_lc_utyp; eassumption.
  - pick fresh α.
    match goal with H : forall _ : atom, _ -> lc_utyp _ |- _ => apply (H α); fsetdec end.
  - apply lc_utyp_arrow; [ eapply d_consis_lc_utyp; eassumption | assumption ].
  - apply lc_utyp_of_degree. constructor.
    eapply degree_utyp_wrt_utyp_open_utyp_wrt_utyp_inv.
    apply degree_utyp_wrt_utyp_of_lc_utyp. eassumption.
  - apply lc_utyp_of_degree. constructor.
    eapply degree_utyp_wrt_utyp_open_utyp_wrt_utyp_inv.
    apply degree_utyp_wrt_utyp_of_lc_utyp. eassumption.
Qed.

(** Reverse paint-lc: a locally-closed syn-painting comes from a
    locally-closed source.  Induction on the [lc_utyp] derivation. *)
Lemma lc_ptyp_of_lc_utyp_syn : forall A,
    lc_utyp (ptyp_to_utyp_syn A) -> lc_ptyp A.
Proof.
  intros A Hlc. remember (ptyp_to_utyp_syn A) as C eqn:HC. revert A HC.
  induction Hlc; intros A0 HC; destruct A0; simpl in HC; inversion HC; subst;
    try (constructor; eauto; fail).
  - pick fresh α. apply (lc_ptyp_all_exists α).
    eapply (H0 α (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))).
    rewrite ptyp_to_utyp_syn_open. reflexivity.
Qed.

(** The (mono) inherited argument of an abstraction is pinned by the arg
    consistency: the painted [inh A] is consistent only with [inh A]. *)
Lemma consis_mono_arg : forall Δ Γ A B,
    {{ Δ ⨟ Γ ⊢ (btyp_to_utyp_syn (ptyp_to_btyp_inh A)) ∼ B }}d ->
    mono_ptyp A ->
    B = ptyp_to_btyp_inh A.
Proof.
  intros Δ Γ A B Hc Hmono.
  rewrite (ptyp_to_btyp_inh_mono_syn Hmono) in Hc.
  rewrite btyp_to_utyp_syn_ptyp_to_btyp_syn in Hc.
  rewrite (ptyp_to_btyp_inh_mono_syn Hmono).
  eapply d_consis_mono_determines; eassumption.
Qed.

(** Consistency preserves erasure: the source and target erase to the same
    plain [ptyp] (the ∀ cases close via [open_ptyp_wrt_ptyp_inj]). *)
Lemma d_consis_btyp_erase : forall Δ Γ C B,
    {{ Δ ⨟ Γ ⊢ C ∼ B }}d -> btyp_to_ptyp (utyp_to_btyp C) = btyp_to_ptyp B.
Proof.
  intros Δ Γ C B H.
  induction H; simpl; try reflexivity; try (f_equal; assumption).
  all: f_equal;
    match goal with
    | |- btyp_to_ptyp (utyp_to_btyp ?c) = btyp_to_ptyp ?b =>
        pick fresh α for (L `union` ftvar_in_ptyp (btyp_to_ptyp (utyp_to_btyp c))
                          `union` ftvar_in_ptyp (btyp_to_ptyp b))
    end;
    apply open_ptyp_wrt_ptyp_inj with (α1 := α);
      [ fsetdec
      | fsetdec
      | match goal with
        | H0 : forall _ : atom, _ -> _ = _ |- _ =>
            specialize (H0 α ltac:(solve_notin_auto));
            rewrite utyp_to_btyp_open, !btyp_to_ptyp_open in H0; simpl in H0; exact H0
        end ].
Qed.

(** Syn round-trip: painting a synthesised [btyp] to a [utyp] and back is
    the identity.  Derived from the existing [ptyp] round-trips (the
    coercions are structural [Fixpoint]s, so the [ptyp]-level identity
    needs no binder reasoning). *)
(** ** Erasure ([utyp_to_btyp]) and tag-erasure facts. *)

Lemma utyp_to_btyp_ptyp_to_utyp_syn : forall A,
    utyp_to_btyp (ptyp_to_utyp_syn A) = ptyp_to_btyp_syn A.
Proof. induction A; simpl; congruence. Qed.

Lemma utyp_to_btyp_btyp_to_utyp_syn : forall B,
    is_styp B -> utyp_to_btyp (btyp_to_utyp_syn B) = B.
Proof.
  intros B Hsyn.
  rewrite <- (ptyp_to_utyp_syn_btyp_to_ptyp B).
  rewrite utyp_to_btyp_ptyp_to_utyp_syn.
  apply ptyp_to_btyp_syn_btyp_to_ptyp; assumption.
Qed.

(** Base fact for the [d_consis] substitution lemma: a tagged type [ph] is
    consistent (with NIL tags) with its bidirectional image [utyp_to_btyp ph]
    — every ε-tagged ∀ matches the syn-painted ∀ via [ForallSynTagged], which
    records no tag.  This is what makes the substitution [α ↦ ph] add no tags
    at variable occurrences. *)
Lemma d_consis_dtyp_refl : forall Γ C,
    {{ Γ ⊢ᵤ C }}d ->
    is_dtyp C ->
    {{ empty ⨟ Γ ⊢ C ∼ (utyp_to_btyp C) }}d.
Proof.
  intros Γ C Hwf. induction Hwf; intros Htt; simpl.
  - apply d_consis__unit. reflexivity.
  - apply d_consis__var; [ assumption | reflexivity ].
  - inversion Htt; subst.
    eapply d_consis__arrow; [ apply IHHwf1 | apply IHHwf2 | fsetdec ]; assumption.
  - inversion Htt.                          (* utyp_all_syn is not is_dtyp *)
  - inversion Htt; subst.
    apply d_consis__forall_syn_tagged with (L := L `union` L0).
    intros α Hα.
    change (btyp_var_f α) with (utyp_to_btyp (utyp_var_f α)).
    rewrite <- utyp_to_btyp_open.
    apply H0; [ fsetdec | ].
    match goal with
    | H : forall x, x `notin` _ -> is_dtyp _ |- _ => apply H; fsetdec
    end.
Qed.

(** [utyp_to_btyp] preserves local closure (needed for the btyp-side
    subst/open commute in the substitution lemma). *)
Lemma utyp_to_btyp_lc : forall C, lc_utyp C -> lc_btyp (utyp_to_btyp C).
Proof.
  intros C H. induction H; simpl.
  - apply lc_btyp_unit.
  - apply lc_btyp_var_f.
  - apply lc_btyp_arrow; assumption.
  - apply lc_btyp_all_syn. intros α.
    change (btyp_var_f α) with (utyp_to_btyp (utyp_var_f α)).
    rewrite <- utyp_to_btyp_open. apply H0.
  - apply lc_btyp_all_syn. intros α.
    change (btyp_var_f α) with (utyp_to_btyp (utyp_var_f α)).
    rewrite <- utyp_to_btyp_open. apply H0.
Qed.

(** [d_wf_utyp] head-weakening (prepend a context). *)
Lemma d_wf_utyp_weakening_head : forall Γ' Γ C,
    {{ Γ ⊢ᵤ C }}d ->
    {{ (Γ' ++ Γ) ⊢ᵤ C }}d.
Proof.
  intros Γ' Γ C H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_utyp_weakening. simpl. exact H.
Qed.

(** Tag-erasure of consistency: a consistency out of [Cmid] re-derives with
    [Cmid]'s ε-tags erased to syn ∀s ([btyp_to_utyp_syn (utyp_to_btyp Cmid)]),
    dropping the corresponding solved tags (hence the existential [Ψ']).
    Proof structure (induction on the consistency): unit/var/arrow are
    structural; each forall case replaces the tagged rule by its untagged
    counterpart ([ForallInhTagged → ForallInhUntagged], [ForallSynTagged →
    ForallSyn]) and recovers the cofinite-uniform witness by picking one
    fresh [α0] and renaming via [d_consis_rename_tvar].  Needs small commute/ftvar
    helpers ([btyp_to_utyp_syn_open], [utyp_to_btyp_open], an
    [ftvar_utyp_to_btyp] bound).  This is the last genuinely-new lemma the
    CST reformulation rests on. *)
Lemma ftvar_utyp_to_btyp : forall C,
    ftvar_in_btyp (utyp_to_btyp C) [<=] ftvar_in_utyp C.
Proof. induction C; simpl; fsetdec. Qed.

(** Erase ([btyp_to_utyp_syn ∘ utyp_to_btyp]) commutes with [open] on a
    variable. *)
Lemma erase_open : forall C α,
    btyp_to_utyp_syn (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f α)))
    = open_utyp_wrt_utyp (btyp_to_utyp_syn (utyp_to_btyp C)) (utyp_var_f α).
Proof.
  intros C α. rewrite utyp_to_btyp_open. simpl.
  rewrite btyp_to_utyp_syn_open. reflexivity.
Qed.

Lemma d_consis_erase_tags : forall Δ Γ C B,
    {{ Δ ⨟ Γ ⊢ C ∼ B }}d ->
    exists Ψ', {{ Ψ' ⨟ Γ ⊢ (btyp_to_utyp_syn (utyp_to_btyp C)) ∼ B }}d.
Proof.
  intros Δ Γ C B H. induction H.
  - (* unit *) exists empty. apply d_consis__unit. reflexivity.
  - (* var *) exists empty. simpl. apply d_consis__var; [ assumption | reflexivity ].
  - (* forall_inh_tagged: ε-tag erased, ForallInhTagged → ForallInhUntagged *)
    pick fresh α0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 α0 ltac:(solve_notin_auto)) as [Ψ'0 HΨ'0].
    rewrite erase_open in HΨ'0.
    exists Ψ'0. simpl.
    apply d_consis__forall_inh_untagged with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton α0).
    intros α Hα.
    rewrite (subst_utyp_in_utyp_intro α0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro α0) by fsetdec.
    apply (@d_consis_rename_tvar _ _ _ _ HΨ'0 nil Γ α0 α); [ reflexivity | simpl; fsetdec ].
  - (* forall_inh_untagged: ForallInhUntagged → ForallInhUntagged *)
    pick fresh α0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 α0 ltac:(solve_notin_auto)) as [Ψ'0 HΨ'0].
    rewrite erase_open in HΨ'0.
    exists Ψ'0. simpl.
    apply d_consis__forall_inh_untagged with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton α0).
    intros α Hα.
    rewrite (subst_utyp_in_utyp_intro α0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro α0) by fsetdec.
    apply (@d_consis_rename_tvar _ _ _ _ HΨ'0 nil Γ α0 α); [ reflexivity | simpl; fsetdec ].
  - (* forall_syn_tagged: ε-tag erased, ForallSynTagged → ForallSyn *)
    pick fresh α0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 α0 ltac:(solve_notin_auto)) as [Ψ'0 HΨ'0].
    rewrite erase_open in HΨ'0.
    exists Ψ'0. simpl.
    apply d_consis__forall_syn with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton α0).
    intros α Hα.
    rewrite (subst_utyp_in_utyp_intro α0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro α0) by fsetdec.
    apply (@d_consis_rename_tvar _ _ _ _ HΨ'0 nil Γ α0 α); [ reflexivity | simpl; fsetdec ].
  - (* forall_syn: ForallSyn → ForallSyn *)
    pick fresh α0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 α0 ltac:(solve_notin_auto)) as [Ψ'0 HΨ'0].
    rewrite erase_open in HΨ'0.
    exists Ψ'0. simpl.
    apply d_consis__forall_syn with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton α0).
    intros α Hα.
    rewrite (subst_utyp_in_utyp_intro α0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro α0) by fsetdec.
    apply (@d_consis_rename_tvar _ _ _ _ HΨ'0 nil Γ α0 α); [ reflexivity | simpl; fsetdec ].
  - (* arrow *)
    destruct IHd_consis1 as [Ψ1' H1']. destruct IHd_consis2 as [Ψ2' H2'].
    exists (Ψ1' `union` Ψ2'). simpl.
    eapply d_consis__arrow; [ eassumption | eassumption | reflexivity ].
Qed.

(** [nil]-context variant for the reformulated CST's [infer] case: when the
    target [B] is synthesised the composed tag context collapses to [nil]
    (via [d_consis_compose_syn_nil_l]), which is what [d_sub__infer] demands. *)
Lemma d_consis_trans_mid_nil : forall Ψ1 Ψ2 Γ C Cmid B,
    lc_utyp Cmid ->
    is_styp B ->
    {{ Ψ1 ⨟ Γ ⊢ C ∼ (utyp_to_btyp Cmid) }}d ->
    {{ Ψ2 ⨟ Γ ⊢ Cmid ∼ B }}d ->
    {{ empty ⨟ Γ ⊢ C ∼ B }}d.
Proof.
  intros Ψ1 Ψ2 Γ C Cmid B Hlc Hsyn HT HCmid.
  destruct (d_consis_erase_tags HCmid) as [Ψ2' Herase].
  eapply (d_consis_compose_syn_nil_l (B2 := utyp_to_btyp Cmid)).
  - apply is_styp_utyp_to_btyp; exact Hlc.
  - exact Hsyn.
  - exact HT.
  - exact Herase.
Qed.

(** The [d_consis] substitution lemma (the infrastructure the [forall_l]
    cases of both transitivity lemmas were blocked on).  Substituting a
    tvar [α0] by a tagged type [ph] on the unresolved side, and by its
    bidirectional image [utyp_to_btyp ph] on the bidirectional side,
    preserves consistency WITHOUT adding tags — the variable occurrences
    become [ph ∼ utyp_to_btyp ph], which is tag-free ([d_consis_dtyp_refl]).
    Structure mirrors [d_consis_rename_tvar] (var→var); the only changes are the
    [α0]-case (use the base fact) and the [lc]/wf side-conditions for [ph]. *)
Lemma d_consis_subst_tvar : forall Δ Γ C B,
    {{ Δ ⨟ Γ ⊢ C ∼ B }}d ->
    forall Γ1 Γ2 α0 C',
      Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
      {{ (Γ1 ++ Γ2) ⊢ᵤ C' }}d ->
      is_dtyp C' ->
      {{ Δ ⨟ (Γ1 ++ Γ2) ⊢ (subst_utyp_in_utyp C' α0 C)
                      ∼ (subst_btyp_in_btyp (utyp_to_btyp C') α0 B) }}d.
Proof.
  intros Δ Γ C B H. induction H; intros Γ1 Γ2 α0 C' Heq Hwf Htt; subst; simpl.
  - apply d_consis__unit. assumption.
  - (* var: [α = α0] uses the base fact; [α <> α0] stays a variable. *)
    destruct_if.
    + eapply d_consis_equiv; [ | apply d_consis_dtyp_refl; assumption ]. fsetdec.
    + apply d_consis__var; [ analyze_binds H; auto | assumption ].
  - eapply d_consis__forall_inh_tagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton α0).
    + intros α2 Hα2.
      erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
        by (solve [ fsetdec | apply is_dtyp_lc; assumption ]).
      erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
        by (solve [ fsetdec | apply utyp_to_btyp_lc; apply is_dtyp_lc; assumption ]).
      rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
      eapply (H0 α2);
        [ fsetdec | simpl; reflexivity
        | rewrite_env ((α2 ~ dbind_tvar) ++ (Γ1 ++ Γ2));
          apply d_wf_utyp_weakening_head; exact Hwf
        | assumption ].
    + assumption.
  - apply d_consis__forall_inh_untagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton α0).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply is_dtyp_lc; assumption ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply utyp_to_btyp_lc; apply is_dtyp_lc; assumption ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2);
      [ fsetdec | simpl; reflexivity
      | rewrite_env ((α2 ~ dbind_tvar) ++ (Γ1 ++ Γ2));
        apply d_wf_utyp_weakening_head; exact Hwf
      | assumption ].
  - apply d_consis__forall_syn_tagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton α0).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply is_dtyp_lc; assumption ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply utyp_to_btyp_lc; apply is_dtyp_lc; assumption ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2);
      [ fsetdec | simpl; reflexivity
      | rewrite_env ((α2 ~ dbind_tvar) ++ (Γ1 ++ Γ2));
        apply d_wf_utyp_weakening_head; exact Hwf
      | assumption ].
  - apply d_consis__forall_syn with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton α0).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply is_dtyp_lc; assumption ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply utyp_to_btyp_lc; apply is_dtyp_lc; assumption ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2);
      [ fsetdec | simpl; reflexivity
      | rewrite_env ((α2 ~ dbind_tvar) ++ (Γ1 ++ Γ2));
        apply d_wf_utyp_weakening_head; exact Hwf
      | assumption ].
  - eapply d_consis__arrow;
      [ eapply IHd_consis1; eauto | eapply IHd_consis2; eauto | assumption ].
Qed.

(** [utyp_tag_refines T Cmid]: [T] and [Cmid] have the same shape, and at
    every quantifier where [Cmid] is ε-tagged [T] carries the SAME tag, while
    [T] may carry EXTRA tags where [Cmid] is synthesised.  This captures the
    "T and A have the same shape modulo T may have extra tags" of the paper's
    CST (syntax-directed.tex), and — crucially — is closed under the shared-ph
    instantiation that [forall_l] performs (both sides gain the same ph).  It
    is the linearity-free replacement for the [d_tags] lower-bound chain. *)
(** ** Tag refinement and the [compose_tags] source-swap.

    [utyp_tag_refines T C]: [T] has [C]'s shape but may carry extra ε-tags.
    With the uniform [compose_tags] witness this swaps the source of a
    consistency without per-variable existentials — the linearity-free core
    of CST below. *)

Inductive utyp_tag_refines : utyp -> utyp -> Prop :=
| utr_unit  : utyp_tag_refines utyp_unit utyp_unit
| utr_var_b : forall n, utyp_tag_refines (utyp_var_b n) (utyp_var_b n)
| utr_var_f : forall α, utyp_tag_refines (utyp_var_f α) (utyp_var_f α)
| utr_arrow : forall T1 T2 C1 C2,
    utyp_tag_refines T1 C1 -> utyp_tag_refines T2 C2 ->
    utyp_tag_refines (utyp_arrow T1 T2) (utyp_arrow C1 C2)
| utr_tag_tag : forall ε T0 C0,
    utyp_tag_refines T0 C0 ->
    utyp_tag_refines (utyp_all_tag ε T0) (utyp_all_tag ε C0)
| utr_tag_syn : forall ε T0 C0,
    utyp_tag_refines T0 C0 ->
    utyp_tag_refines (utyp_all_tag ε T0) (utyp_all_syn C0)
| utr_syn_syn : forall T0 C0,
    utyp_tag_refines T0 C0 ->
    utyp_tag_refines (utyp_all_syn T0) (utyp_all_syn C0).

#[local] Hint Constructors utyp_tag_refines : core.

Lemma utyp_tag_refines_refl : forall T, utyp_tag_refines T T.
Proof. induction T; auto. Qed.

Lemma utyp_tag_refines_open_rec : forall C' C,
    utyp_tag_refines C' C ->
    forall k β,
      utyp_tag_refines (open_utyp_wrt_utyp_rec k (utyp_var_f β) C')
                       (open_utyp_wrt_utyp_rec k (utyp_var_f β) C).
Proof.
  induction 1; intros k β; simpl; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; auto.
Qed.

Lemma utyp_tag_refines_open : forall C' C α,
    utyp_tag_refines C' C ->
    utyp_tag_refines (open_utyp_wrt_utyp C' (utyp_var_f α))
                     (open_utyp_wrt_utyp C (utyp_var_f α)).
Proof.
  intros C' C α H. unfold open_utyp_wrt_utyp. apply utyp_tag_refines_open_rec; auto.
Qed.

(** Closing (de Bruijn abstraction) preserves refinement — the inverse
    direction of opening, used to recover structural refinement of ∀ bodies
    from the cofinite hypothesis. *)
Lemma utyp_tag_refines_close_rec_pres : forall C' C,
    utyp_tag_refines C' C ->
    forall k β,
      utyp_tag_refines (close_utyp_wrt_utyp_rec k β C')
                       (close_utyp_wrt_utyp_rec k β C).
Proof.
  induction 1; intros k β; simpl; auto using utyp_tag_refines_refl.
Qed.

Lemma utyp_tag_refines_close : forall C C' β k,
    β `notin` ftvar_in_utyp C ->
    β `notin` ftvar_in_utyp C' ->
    utyp_tag_refines (open_utyp_wrt_utyp_rec k (utyp_var_f β) C)
                     (open_utyp_wrt_utyp_rec k (utyp_var_f β) C') ->
    utyp_tag_refines C C'.
Proof.
  intros C C' β k HC HD H.
  pose proof (@utyp_tag_refines_close_rec_pres _ _ H k β) as H'.
  rewrite !close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec in H' by assumption.
  exact H'.
Qed.

(** ∀-body helper: recover structural refinement of [C] against [paint B]
    from the cofinite consistency body, via [close] + [paint]-opening. *)
Lemma consis_refines_paint_body : forall L C B,
    (forall α, α `notin` L ->
       utyp_tag_refines (open_utyp_wrt_utyp C (utyp_var_f α))
                        (btyp_to_utyp_syn (open_btyp_wrt_btyp B (btyp_var_f α)))) ->
    utyp_tag_refines C (btyp_to_utyp_syn B).
Proof.
  intros L C B H.
  pick fresh α for (L `union` ftvar_in_utyp C `union` ftvar_in_btyp B).
  apply (@utyp_tag_refines_close C (btyp_to_utyp_syn B) α 0).
  - fsetdec.
  - rewrite ftvar_btyp_to_utyp_syn; fsetdec.
  - change (open_utyp_wrt_utyp_rec 0 (utyp_var_f α) C)
      with (open_utyp_wrt_utyp C (utyp_var_f α)).
    change (open_utyp_wrt_utyp_rec 0 (utyp_var_f α) (btyp_to_utyp_syn B))
      with (open_utyp_wrt_utyp (btyp_to_utyp_syn B) (utyp_var_f α)).
    specialize (H α ltac:(solve_notin_auto)).
    rewrite btyp_to_utyp_syn_open in H. exact H.
Qed.

(** The unresolved source of a consistency refines the syn-painting of the
    bidirectional target: same shape, painting fully syn (tag-free), so [T]'s
    tags trivially dominate. *)
Lemma consis_refines_paint : forall Δ Γ C B_A,
    {{ Δ ⨟ Γ ⊢ C ∼ B_A }}d ->
    utyp_tag_refines C (btyp_to_utyp_syn B_A).
Proof.
  intros Δ Γ C B_A H. induction H; simpl.
  - apply utr_unit.
  - apply utr_var_f.
  - apply utr_tag_syn. eapply consis_refines_paint_body; eauto.
  - apply utr_syn_syn.  eapply consis_refines_paint_body; eauto.
  - apply utr_tag_syn. eapply consis_refines_paint_body; eauto.
  - apply utr_syn_syn.  eapply consis_refines_paint_body; eauto.
  - apply utr_arrow; assumption.
Qed.

(** [refines] makes [compose_tags] monotone: [Cmid]'s composed tags are a
    subset of [T]'s (extra tags only grow the result). *)
Lemma utyp_tag_refines_compose_mono : forall C' C,
    utyp_tag_refines C' C ->
    forall B, compose_tags C B [<=] compose_tags C' B.
Proof.
  induction 1; intros B0; destruct B0; simpl; try fsetdec;
    try (specialize (IHutyp_tag_refines1 B0_1); specialize (IHutyp_tag_refines2 B0_2); fsetdec);
    specialize (IHutyp_tag_refines B0); fsetdec.
Qed.

(** The consistency context is bounded above by [compose_tags] — the
    canonical (linearity-free) tag witness.  This is the lower link of the
    bound chain [Ψ2 ⊆ compose_tags Cmid B]. *)
Lemma d_consis_ctx_subset_compose : forall Δ Γ C B,
    {{ Δ ⨟ Γ ⊢ C ∼ B }}d ->
    Δ [<=] compose_tags C B.
Proof.
  intros Δ Γ C B H. induction H; simpl.
  - fsetdec.
  - fsetdec.
  - pick fresh α. match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
      specialize (IH α ltac:(solve_notin_auto)) end.
    rewrite compose_tags_open in *. fsetdec.
  - pick fresh α. match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
      specialize (IH α ltac:(solve_notin_auto)) end.
    rewrite compose_tags_open in *. fsetdec.
  - pick fresh α. match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
      specialize (IH α ltac:(solve_notin_auto)) end.
    rewrite compose_tags_open in *. fsetdec.
  - pick fresh α. match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
      specialize (IH α ltac:(solve_notin_auto)) end.
    rewrite compose_tags_open in *. fsetdec.
  - fsetdec.
Qed.

(** Source-swap with the [compose_tags] witness: if [T] refines [Cmid] (same
    shape, tags ⊇) and [Cmid ∼ B], then [T ∼ B] holds at the canonical
    context [compose_tags T B].  The witness is UNIFORM (opening-invariant via
    [compose_tags_open]), so the ∀ cases avoid the cofinite per-α existential.
    No [d_tags], no linearity. *)
Lemma refines_consis_swap : forall Δ Γ Cmid B,
    {{ Δ ⨟ Γ ⊢ Cmid ∼ B }}d ->
    (* C' , not C: [induction H] manufactures C from [d_consis]'s own binders. *)
    forall C', utyp_tag_refines C' Cmid ->
      {{ (compose_tags C' B) ⨟ Γ ⊢ C' ∼ B }}d.
Proof.
  intros Δ Γ Cmid B H. induction H; intros C' Href.
  - inversion Href; subst. simpl. apply d_consis__unit. reflexivity.
  - inversion Href; subst. simpl. apply d_consis__var; [ assumption | reflexivity ].
  - (* forall_inh_tagged: Cmid = utyp_all_tag ε C, B = btyp_all_inh; C = utyp_all_tag ε T0 *)
    inversion Href; subst. simpl.
    eapply d_consis__forall_inh_tagged with (L := L) (Ψ0 := compose_tags T0 B); [ | reflexivity ].
    intros α Hα.
    match goal with |- {{ compose_tags ?Tb ?Bb ⨟ _ ⊢ _ ∼ _ }}d =>
      rewrite <- (compose_tags_open Tb Bb α α) end.
    apply (H0 α Hα). apply utyp_tag_refines_open. assumption.
  - (* forall_inh_untagged: Cmid = utyp_all_syn C, B = btyp_all_inh; C tagged or syn *)
    inversion Href; subst; simpl.
    + (* C = utyp_all_tag ε T0 (extra tag) *)
      eapply d_consis__forall_inh_tagged with (L := L) (Ψ0 := compose_tags T0 B); [ | reflexivity ].
      intros α Hα.
      match goal with |- {{ compose_tags ?Tb ?Bb ⨟ _ ⊢ _ ∼ _ }}d =>
        rewrite <- (compose_tags_open Tb Bb α α) end.
      apply (H0 α Hα). apply utyp_tag_refines_open. assumption.
    + (* C = utyp_all_syn T0 *)
      apply d_consis__forall_inh_untagged with (L := L).
      intros α Hα.
      match goal with |- {{ compose_tags ?Tb ?Bb ⨟ _ ⊢ _ ∼ _ }}d =>
        rewrite <- (compose_tags_open Tb Bb α α) end.
      apply (H0 α Hα). apply utyp_tag_refines_open. assumption.
  - (* forall_syn_tagged: Cmid = utyp_all_tag ε C, B = btyp_all_syn; C = utyp_all_tag ε T0 *)
    inversion Href; subst. simpl.
    apply d_consis__forall_syn_tagged with (L := L).
    intros α Hα.
    match goal with |- {{ compose_tags ?Tb ?Bb ⨟ _ ⊢ _ ∼ _ }}d =>
      rewrite <- (compose_tags_open Tb Bb α α) end.
    apply (H0 α Hα). apply utyp_tag_refines_open. assumption.
  - (* forall_syn: Cmid = utyp_all_syn C, B = btyp_all_syn; C tagged or syn *)
    inversion Href; subst; simpl.
    + (* C = utyp_all_tag ε T0 *)
      apply d_consis__forall_syn_tagged with (L := L).
      intros α Hα.
      match goal with |- {{ compose_tags ?Tb ?Bb ⨟ _ ⊢ _ ∼ _ }}d =>
        rewrite <- (compose_tags_open Tb Bb α α) end.
      apply (H0 α Hα). apply utyp_tag_refines_open. assumption.
    + (* C = utyp_all_syn T0 *)
      apply d_consis__forall_syn with (L := L).
      intros α Hα.
      match goal with |- {{ compose_tags ?Tb ?Bb ⨟ _ ⊢ _ ∼ _ }}d =>
        rewrite <- (compose_tags_open Tb Bb α α) end.
      apply (H0 α Hα). apply utyp_tag_refines_open. assumption.
  - inversion Href; subst. simpl.
    eapply d_consis__arrow; [ apply IHd_consis1 | apply IHd_consis2 | reflexivity ]; assumption.
Qed.

(* ======================================================================== *)
(*  TAG-BOUNDED REFINEMENT — the invariant CST's ForallL case runs on.       *)
(* ======================================================================== *)

(** [utyp_tag_refines_in V C' C] is [utyp_tag_refines C' C] with the tags the
    refinement ADDS confined to [V].

    ⭐ WHY AN INDEXED RELATION, and not the set inclusion
    [ftag C' ⊆ ftag C ∪ V] that it implies.  CST rebuilds [ForallL] at the
    REFINED subject, so it owes [Ψ' ∩ ftag(C'_node) = ∅] while the derivation
    supplies only [Ψ' ∩ ftag(C_node) = ∅] — the gap is exactly the added tags,
    and [Ψ' ⊆ U] with [U ∩ V = ∅] closes it.  The inclusion alone does NOT
    survive the step, because [ForallL] then descends into the ∀'s BODY and
    [ftag (∀^ε T0)] has already absorbed ε: from
    [ftag (∀^ε T0) ⊆ ftag (∀^ε C0) ∪ V] one cannot recover
    [ftag T0 ⊆ ftag C0 ∪ V].  The relation carries the bound structurally, so
    it descends. *)
Inductive utyp_tag_refines_in : atoms -> utyp -> utyp -> Prop :=
| utri_unit  : forall V, utyp_tag_refines_in V utyp_unit utyp_unit
| utri_var_b : forall V n, utyp_tag_refines_in V (utyp_var_b n) (utyp_var_b n)
| utri_var_f : forall V α, utyp_tag_refines_in V (utyp_var_f α) (utyp_var_f α)
| utri_arrow : forall V T1 T2 C1 C2,
    utyp_tag_refines_in V T1 C1 -> utyp_tag_refines_in V T2 C2 ->
    utyp_tag_refines_in V (utyp_arrow T1 T2) (utyp_arrow C1 C2)
| utri_tag_tag : forall V ε T0 C0,
    utyp_tag_refines_in V T0 C0 ->
    utyp_tag_refines_in V (utyp_all_tag ε T0) (utyp_all_tag ε C0)
| utri_tag_syn : forall V ε T0 C0,
    (* the ONE place a tag is ADDED, and the only premise [V] constrains *)
    ε `in` V ->
    utyp_tag_refines_in V T0 C0 ->
    utyp_tag_refines_in V (utyp_all_tag ε T0) (utyp_all_syn C0)
| utri_syn_syn : forall V T0 C0,
    utyp_tag_refines_in V T0 C0 ->
    utyp_tag_refines_in V (utyp_all_syn T0) (utyp_all_syn C0).

#[local] Hint Constructors utyp_tag_refines_in : core.

Lemma utyp_tag_refines_in_of : forall V C' C,
    utyp_tag_refines_in V C' C -> utyp_tag_refines C' C.
Proof. induction 1; auto. Qed.

Lemma utyp_tag_refines_in_mono : forall V C' C,
    utyp_tag_refines_in V C' C ->
    forall V', V [<=] V' -> utyp_tag_refines_in V' C' C.
Proof.
  induction 1; intros V' Hle.
  - apply utri_unit.
  - apply utri_var_b.
  - apply utri_var_f.
  - apply utri_arrow;
      [ apply IHutyp_tag_refines_in1 | apply IHutyp_tag_refines_in2 ];
      exact Hle.
  - apply utri_tag_tag. apply IHutyp_tag_refines_in; exact Hle.
  - apply utri_tag_syn;
      [ clear - H Hle; fsetdec | apply IHutyp_tag_refines_in; exact Hle ].
  - apply utri_syn_syn. apply IHutyp_tag_refines_in; exact Hle.
Qed.

(** The canonical bound: a refinement's added tags are, trivially, tags of the
    refined term.  So the indexed relation costs a caller nothing. *)
Lemma utyp_tag_refines_to_in : forall C' C,
    utyp_tag_refines C' C -> utyp_tag_refines_in (ftag_in_utyp C') C' C.
Proof.
  induction 1; simpl.
  - apply utri_unit.
  - apply utri_var_b.
  - apply utri_var_f.
  - apply utri_arrow;
      [ apply (utyp_tag_refines_in_mono IHutyp_tag_refines1)
      | apply (utyp_tag_refines_in_mono IHutyp_tag_refines2) ];
      clear; fsetdec.
  - apply utri_tag_tag.
    apply (utyp_tag_refines_in_mono IHutyp_tag_refines); clear; fsetdec.
  - apply utri_tag_syn; [ clear; fsetdec | ].
    apply (utyp_tag_refines_in_mono IHutyp_tag_refines); clear; fsetdec.
  - apply utri_syn_syn.
    apply (utyp_tag_refines_in_mono IHutyp_tag_refines); clear; fsetdec.
Qed.

Lemma utyp_tag_refines_in_ftag : forall V C' C,
    utyp_tag_refines_in V C' C ->
    ftag_in_utyp C' [<=] (ftag_in_utyp C) `union` V.
Proof. induction 1; simpl; fsetdec. Qed.

(** A tag refinement does not touch TYPE variables — what CST's [forall_r]
    case needs to reuse the rule's own freshness side condition. *)
Lemma utyp_tag_refines_ftvar : forall C' C,
    utyp_tag_refines C' C -> ftvar_in_utyp C' [=] ftvar_in_utyp C.
Proof. induction 1; simpl; fsetdec. Qed.

Lemma utyp_tag_refines_in_refl : forall V C, utyp_tag_refines_in V C C.
Proof. intros V C. induction C; constructor; assumption. Qed.

Lemma utyp_tag_refines_in_open_rec_gen : forall V C' C,
    utyp_tag_refines_in V C' C ->
    forall k C0',
      utyp_tag_refines_in V (open_utyp_wrt_utyp_rec k C0' C')
                            (open_utyp_wrt_utyp_rec k C0' C).
Proof.
  induction 1; intros k C0'; simpl; try solve [ constructor; auto ].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?];
    solve [ apply utri_var_b | apply utyp_tag_refines_in_refl ].
Qed.

Lemma utyp_tag_refines_in_open_gen : forall V C' C C0,
    utyp_tag_refines_in V C' C ->
    utyp_tag_refines_in V (open_utyp_wrt_utyp C' C0) (open_utyp_wrt_utyp C C0).
Proof.
  intros V C' C C0 H. unfold open_utyp_wrt_utyp.
  apply utyp_tag_refines_in_open_rec_gen; exact H.
Qed.

(** Reformulated CST over a GENERAL middle [Cmid] (paper-faithful: the syn
    middle is not closed under tagged instantiation).  infer/check/arg close
    via the proven bridges; forall_l is the concrete attempt with the
    existing list-typed tag context. *)
(** ** Consistency-Subtyping Transitivity (paper B.3 / Lemma 3 dependency).

    [_mid] is the erase-form (middle carried as [T ∼ utyp_to_btyp Cmid]),
    which survives [forall_l] instantiation; [d_consis_sub_trans] is the
    paint-form corollary used downstream.

    ⭐ WHY THE TAGS-BOUND TWIN.  Since [ForallL] reads the paper's `fresh Ψ'`
    GLOBALLY — the instantiation's tags fresh from the SUBJECT too, not just
    from the tag context — rebuilding it at the REFINED source [C'] owes
    [Ψ' ∩ ftag C' = ∅], and the transported derivation supplies only
    [Ψ' ∩ ftag Cmid = ∅].  The gap is exactly the tags [utyp_tag_refines]
    ADDED ([utr_tag_syn] turns a [∀ˢ] into a [∀^ε]), and nothing local bounds
    them.  So the induction runs on [d_sub_tagsin U] instead: every [Ψ']
    inside the derivation is confined to one [U], the added tags are confined
    to one [V], and one global [U ∩ V = ∅] discharges every node at once.  The
    call sites establish it by moving [U] wholesale ([d_sub_freshen]). *)

Lemma d_consis_sub_trans_mid_tagsin : forall U M Ψ2 Γ Cmid B,
    d_sub_tagsin U M Ψ2 Γ Cmid B ->
    forall Ψ1 C' V,
      {{ Ψ1 ⨟ Γ ⊢ C' ∼ (utyp_to_btyp Cmid) }}d ->
      utyp_tag_refines_in V C' Cmid ->
      U ∩ V [=] empty ->
      exists Δ, Ψ2 [<=] Δ /\ {{ Δ ⨟ Γ ⊢[ M ] C' ⩽ B }}d.
Proof.
  intros U M Ψ2 Γ Cmid B Hsub.
  induction Hsub; intros Ψ0 C' V Hcons Href Hdisj.
  - (* infer (ti): Ψ2 [=] ∅. *)
    exists empty. split; [ fsetdec | ].
    apply d_sub__infer.
    + apply (d_consis_trans_mid_nil (Cmid := C) (Ψ1 := Ψ0) (Ψ2 := empty)).
      * exact (d_consis_lc_utyp H).
      * exact H0.
      * exact Hcons.
      * exact H.
    + exact H0.
    + reflexivity.
  - (* check (tc): output context is the canonical witness [compose_tags C' B];
       bound Ψ2 ⊆ it via the tag chain, output consistency via the source-swap. *)
    assert (HgT : guarded_utyp C') by (eapply d_consis_guarded_lhs; [ exact H | exact Hcons ]).
    exists (compose_tags C' B). split.
    + pose proof (d_consis_ctx_subset_compose H1) as Hc1.
      pose proof (utyp_tag_refines_compose_mono
                    (utyp_tag_refines_in_of Href) B) as Hc2. fsetdec.
    + apply d_sub__check;
        [ exact HgT | exact H0
        | apply (refines_consis_swap H1 (utyp_tag_refines_in_of Href))
        | exact H2 ].
  - (* forall_r (tc): the twin NAMES its binder, so the IH fires directly and
       [d_sub]'s cofinite family is regenerated by [d_sub_rename_tvar].  The
       rule's freshness is stated for [C]; it transfers to [C'] because a tag
       refinement does not move a TYPE variable. *)
    assert (Hftv : ftvar_in_utyp C' [=] ftvar_in_utyp C)
      by (apply utyp_tag_refines_ftvar; apply (utyp_tag_refines_in_of Href)).
    destruct (IHHsub Ψ0 C' V
                ltac:(apply d_consis_weakening_head; exact Hcons) Href Hdisj)
      as [Ψ' [Hbnd HΨ']].
    exists Ψ'. split; [ exact Hbnd | ].
    apply d_sub__forall_r with
      (L := dom Γ `union` ftvar_in_utyp C' `union` ftvar_in_btyp B
            `union` singleton α);
      [ assumption | ].
    intros α2 Hα2.
    rewrite (subst_btyp_in_btyp_intro α) by (clear - H0; fsetdec).
    rewrite <- (subst_utyp_in_utyp_fresh_eq C' (utyp_var_f α2) α)
      by (clear - H0 Hftv; fsetdec).
    apply (@d_sub_rename_tvar _ _ _ _ _ HΨ' nil Γ α α2);
      [ reflexivity | simpl; clear - H0 Hα2; fsetdec ].
  - (* arg (fn m): domain by source-swap, result by IH; bound by chain + IH. *)
    simpl in Hcons. dependent destruction Hcons.
    dependent destruction Href.
    destruct (IHHsub _ _ V ltac:(eassumption) ltac:(eassumption) Hdisj)
      as [Δc2 [Hbnd2 Hres]].
    match goal with Hr : utyp_tag_refines_in _ ?t C1 |- _ =>
      exists (compose_tags t B1 `union` Δc2) end. split.
    + pose proof (d_consis_ctx_subset_compose H) as Hc1.
      match goal with Hr : utyp_tag_refines_in _ _ C1 |- _ =>
        pose proof (utyp_tag_refines_compose_mono
                      (utyp_tag_refines_in_of Hr) B1) as Hc2 end.
      fsetdec.
    + eapply d_sub__arg;
        [ match goal with Hr : utyp_tag_refines_in _ _ C1 |- _ =>
            apply (refines_consis_swap H (utyp_tag_refines_in_of Hr)) end
        | exact Hres | reflexivity ].
  - (* forall_l_tagged: subtyping source is utyp_all_tag ε C; Href forces
       C' = utyp_all_tag ε T0 (utri_tag_tag); reconstruct via forall_l_tagged. *)
    dependent destruction Href.
    simpl in Hcons. dependent destruction Hcons.
    pick fresh α for (L `union` dom Γ `union` ftvar_in_utyp T0
                      `union` ftvar_in_utyp C `union` ftvar_in_btyp B
                      `union` Ψ `union` Ψ').
    pose proof (@d_consis_subst_tvar _ _ _ _ (H6 α ltac:(solve_notin_auto)) nil Γ α ph
                  eq_refl ltac:(simpl; exact H4) H5) as Hinst.
    rewrite <- (subst_utyp_in_utyp_intro α T0 ph) in Hinst by fsetdec.
    rewrite <- (subst_btyp_in_btyp_intro α (utyp_to_btyp C) (utyp_to_btyp ph)) in Hinst
      by (rewrite ftvar_utyp_to_btyp; fsetdec).
    rewrite <- utyp_to_btyp_open in Hinst.
    simpl in Hinst.
    pose proof (utyp_tag_refines_in_ftag Href) as Hft.
    destruct (IHHsub _ _ V Hinst
                (utyp_tag_refines_in_open_gen ph Href) Hdisj)
      as [Δ_IH [Hbnd HΔ_IH]].
    exists (Δ_IH ∖ Ψ'). split.
    + clear - Hbnd H0; fsetdec.
    + eapply d_sub__forall_l_tagged with (Ψ' := Ψ').
      * exact H.
      * clear - Hbnd H0; fsetdec.
      * (* ⭐ THE STEP THE TWIN EXISTS FOR: the node's own hygiene keeps Ψ'
           off the MIDDLE's tags, and Ψ' ⊆ U with U ∩ V = ∅ keeps it off the
           tags the refinement ADDED. *)
        simpl in H1 |- *. clear - H1 H2 Hdisj Hft; fsetdec.
      * exact H3.
      * exact H4.
      * exact H5.
      * eapply d_sub_equiv; [ | exact HΔ_IH ]. clear - Hbnd H0; fsetdec.
  - (* forall_l_untagged: with Ψ2 ⊆ Δ in the IH, the residual Ψ' ⊆ Δ_IH FOLLOWS
       from (Δ ∪ Ψ') ⊆ Δ_IH; refinement threaded by [open_gen]. *)
    simpl in Hcons.
    dependent destruction Hcons.
    + (* C' = utyp_all_tag ε C0 (matched syn): mirror, reconstruct via forall_l_tagged *)
      dependent destruction Href.
      pick fresh α for (L `union` dom Γ `union` ftvar_in_utyp C0
                        `union` ftvar_in_utyp C `union` ftvar_in_btyp B
                        `union` Ψ0 `union` Ψ `union` Ψ').
      pose proof (@d_consis_subst_tvar _ _ _ _ (H6 α ltac:(solve_notin_auto)) nil Γ α ph
                    eq_refl ltac:(simpl; exact H4) H5) as Hinst.
      rewrite <- (subst_utyp_in_utyp_intro α C0 ph) in Hinst by fsetdec.
      rewrite <- (subst_btyp_in_btyp_intro α (utyp_to_btyp C) (utyp_to_btyp ph)) in Hinst
        by (rewrite ftvar_utyp_to_btyp; fsetdec).
      rewrite <- utyp_to_btyp_open in Hinst.
      simpl in Hinst.
      pose proof (utyp_tag_refines_in_ftag Href) as Hft.
      destruct (IHHsub _ _ V Hinst
                  (utyp_tag_refines_in_open_gen ph Href) Hdisj)
        as [Δ_IH [Hbnd HΔ_IH]].
      exists (Δ_IH ∖ Ψ'). split.
      * clear - Hbnd H0; fsetdec.
      * eapply d_sub__forall_l_tagged with (Ψ' := Ψ').
        -- exact H.
        -- clear - Hbnd H0; fsetdec.
        -- (* here refinement ADDED ε itself ([utri_tag_syn]'s [H7 : ε ∈ V]),
              so even the head tag is bounded away from Ψ' by [U ∩ V = ∅]. *)
           simpl in H1 |- *. clear - H1 H2 Hdisj Hft H7; fsetdec.
        -- exact H3.
        -- exact H4.
        -- exact H5.
        -- eapply d_sub_equiv; [ | exact HΔ_IH ]. clear - Hbnd H0; fsetdec.
    + (* C' = utyp_all_syn C0 *)
      dependent destruction Href.
      pick fresh α for (L `union` dom Γ `union` ftvar_in_utyp C0
                        `union` ftvar_in_utyp C `union` ftvar_in_btyp B
                        `union` Ψ0 `union` Ψ `union` Ψ').
      pose proof (@d_consis_subst_tvar _ _ _ _ (H6 α ltac:(solve_notin_auto)) nil Γ α ph
                    eq_refl ltac:(simpl; exact H4) H5) as Hinst.
      rewrite <- (subst_utyp_in_utyp_intro α C0 ph) in Hinst by fsetdec.
      rewrite <- (subst_btyp_in_btyp_intro α (utyp_to_btyp C) (utyp_to_btyp ph)) in Hinst
        by (rewrite ftvar_utyp_to_btyp; fsetdec).
      rewrite <- utyp_to_btyp_open in Hinst.
      simpl in Hinst.
      pose proof (utyp_tag_refines_in_ftag Href) as Hft.
      destruct (IHHsub _ _ V Hinst
                  (utyp_tag_refines_in_open_gen ph Href) Hdisj)
        as [Δ_IH [Hbnd HΔ_IH]].
      exists (Δ_IH ∖ Ψ'). split.
      * clear - Hbnd H0; fsetdec.
      * eapply d_sub__forall_l_untagged with (Ψ' := Ψ').
        -- exact H.
        -- clear - Hbnd H0; fsetdec.
        -- simpl in H1 |- *. clear - H1 H2 Hdisj Hft; fsetdec.
        -- exact H3.
        -- exact H4.
        -- exact H5.
        -- eapply d_sub_equiv; [ | exact HΔ_IH ]. clear - Hbnd H0; fsetdec.
Qed.

(** ⭐ CST as its consumers state it.  Two conditions are new, and both hold
    wherever the tree invokes it: the middle is TAG-FREE (it is always a
    PAINTING [⌈B⌉ˢ]) and the tag context is empty (CST is invoked at the root
    of a spine).  Together they license moving the WHOLE transported
    derivation's instantiation tags off [C']'s tags ([d_sub_freshen],
    decl/prop_tag_swap.v §5) — a transposition of two inner tags leaves a
    tag-free conclusion fixed — which is exactly the [U ∩ V = ∅] the
    tags-bound form asks for. *)
Lemma d_consis_sub_trans_mid : forall M Ψ2 Γ Cmid B,
    {{ Ψ2 ⨟ Γ ⊢[ M ] Cmid ⩽ B }}d ->
    Ψ2 [=] empty ->
    ftag_in_utyp Cmid [=] empty ->
    forall Ψ1 C',
      {{ Ψ1 ⨟ Γ ⊢ C' ∼ (utyp_to_btyp Cmid) }}d ->
      utyp_tag_refines C' Cmid ->
      exists Δ, Ψ2 [<=] Δ /\ {{ Δ ⨟ Γ ⊢[ M ] C' ⩽ B }}d.
Proof.
  intros M Ψ2 Γ Cmid B Hsub HΨ HC Ψ1 C' Hcons Href.
  destruct (d_sub_freshen M Ψ2 Γ Cmid B (ftag_in_utyp C') Hsub
              ltac:(rewrite HΨ; clear; fsetdec)
              ltac:(rewrite HC; clear; fsetdec))
    as [ U [ Hfresh Htagsin ] ].
  eapply d_consis_sub_trans_mid_tagsin;
    [ exact Htagsin | exact Hcons | apply (utyp_tag_refines_to_in Href)
    | clear - Hfresh; fsetdec ].
Qed.

(** Consistency-Subtyping Transitivity (paper, syntax-directed.tex:152):
    a consistency into a synthesised type composes with a subtyping out of
    it.  The synthesised middle is carried as a [btyp] [B_A] with [is_styp],
    bridged to the subtyping LHS via [btyp_to_utyp_syn] (the same convention
    as [d_consis_compose_syn_nil]). *)
(** Paper CST (syntax-directed.tex:152), with the load-bearing [Ψ ⊆ Ψ']
    invariant the paper's "straightforward induction" silently needs: the
    subtyping context [Δb] is GENERAL (not [·]) — that is the inductive
    generalisation that lets the [forall_l] IH fire on its non-empty
    premise — and the conclusion context contains it ([Δb ⊆ Δ]).  The
    paper's [·]-statement is the [Δb = ∅] corollary.

    ⚙ [Δb [=] empty] is what [_mid]'s wholesale freshening needs of the
    conclusion; the paper's own statement is at [·], and so is the sole call
    site (decl/prop_stability.v). *)
Lemma d_consis_sub_trans : forall M Δb Γ C B,
    {{ Δb ⨟ Γ ⊢[ M ] C ⩽ B }}d ->
    Δb [=] empty ->
    forall B_A C' Δt,
      C = btyp_to_utyp_syn B_A ->
      is_styp B_A ->
      {{ Δt ⨟ Γ ⊢ C' ∼ B_A }}d ->
      exists Δ, Δb [<=] Δ /\ {{ Δ ⨟ Γ ⊢[ M ] C' ⩽ B }}d.
Proof.
  (* The [forall_l] case is the tag-encoding wall; it is dissolved by the
     erase-form generalisation [d_consis_sub_trans_mid], which threads tagged
     witnesses via [utyp_tag_refines].  Set [Cmid := btyp_to_utyp_syn B_A]:
     its erasure is [B_A] ([utyp_to_btyp_btyp_to_utyp_syn], [is_styp]), it is
     tag-free ([ftag_btyp_to_utyp_syn] — a painting invents no ε), and the
     source [C'] refines it ([consis_refines_paint]). *)
  intros M Δb Γ C B Hsub HΔ B_A C' Δt Heq Hsyn Hcons. subst C.
  eapply d_consis_sub_trans_mid;
    [ exact Hsub | exact HΔ | apply ftag_btyp_to_utyp_syn | | ].
  - rewrite utyp_to_btyp_btyp_to_utyp_syn by assumption. exact Hcons.
  - eapply consis_refines_paint; exact Hcons.
Qed.

(** * FN^n spine encoding (the design choice for the headline theorems).

    The paper writes the [FN^n TI] type as [Ā_i → syn{A}] — [n]
    bidirectional arguments then a synthesised tail — and general
    subsumption replaces *only the tail*.  We encode that "function spine
    with a replaceable synthesised tail" as a relation rather than an
    explicit telescope:

    [btyp_spine Bfull A Bnew Bres] means [Bfull = Ā → A] (with [A] the
    synthesised tail) and [Bres = Ā → Bnew] (same arguments [Ā], tail
    swapped).  This keeps the shared-arguments invariant structural and
    avoids list/length bookkeeping; the spine depth [n] stays implicit and
    is kept in sync with the mode by [is_fn_n_ti] in the lemmas. *)
(** Encoding (A): index both the mode (via [is_fn_n]) and the spine (via
    the [nat]) by the FN-depth [n], so the spine depth is forced to match
    the mode — this resolves the "is a synthesised arrow a tail or an
    argument?" ambiguity ([n = 0] forces [__tail]). *)
Inductive is_fn_n : nat -> mode -> Prop :=
| is_fn_n__ti : is_fn_n 0 mode_ti
| is_fn_n__fn : forall n m, is_fn_n n m -> is_fn_n (S n) (mode_fn m).

Inductive btyp_spine : nat -> btyp -> btyp -> btyp -> btyp -> Prop :=
| btyp_spine__tail : forall A Bnew,
    is_styp A ->
    btyp_spine 0 A A Bnew Bnew
| btyp_spine__arrow : forall n B1 B2 A Bnew B2',
    btyp_spine n B2 A Bnew B2' ->
    btyp_spine (S n) (btyp_arrow B1 B2) A Bnew (btyp_arrow B1 B2').

(** Subtyping Transitivity (paper, syntax-directed.tex:179): subtyping into
    an [FN^n TI] spine composes with a subtyping out of its synthesised
    tail, replacing the tail throughout the spine.  The conclusion carries
    the paper's [Ψ ⊆ Ψ'] invariant ([Δ [<=] Ψ']) — the output context only
    *grows*.  That invariant is what the [forall_l] cases need: the IH gives
    [(Δ ∪ Ψ') ⊆ Δr], so the instantiation tags [Ψ'] are inside [Δr] and the
    reconstruct picks the outer context [Δr ∖ Ψ'] — set difference makes the
    rule's freshness side condition ([Ψ' ∩ outer = ∅]) automatic and the
    premise context [=]-equal to [Δr] (the paper's "Ψ1 still disjoint from
    Ψ'" line, discharged here by [fsetdec]).  [check]/[forall_r] are
    excluded by [is_fn_n]. *)
Lemma d_sub_trans_spine : forall m1 Δ Γ C Bfull,
    {{ Δ ⨟ Γ ⊢[ m1 ] C ⩽ Bfull }}d ->
    forall n B' M B Bres,
      is_fn_n n m1 ->
      btyp_spine n Bfull B' B Bres ->
      {{ empty ⨟ Γ ⊢[ M ] (btyp_to_utyp_syn B') ⩽ B }}d ->
      exists Ψ', Δ [<=] Ψ' /\ {{ Ψ' ⨟ Γ ⊢[ mode_fn_n_subst m1 M ] C ⩽ Bres }}d.
Proof.
  intros m1 Δ Γ C Bfull Hsub.
  induction Hsub; intros n A0 M0 B0 Bres Hfn Hspine Htail.
  - (* d_sub__infer (ti): n = 0 forces the tail; compose by CST — now the
       fully-closed erase-form [d_consis_sub_trans_mid].  Middle is
       [btyp_to_utyp_syn A0]; its erasure is [A0] (is_styp), matching the infer
       consistency, and [C] refines it by [consis_refines_paint]. *)
    inversion Hfn; subst.
    dependent destruction Hspine.
    edestruct (d_consis_sub_trans_mid Htail) as [Ψ' [_ HΨ']].
    + (* the tail runs at the EMPTY tag context … *)
      clear; fsetdec.
    + (* … and its subject is a PAINTING, hence tag-free — the two conditions
         the wholesale freshening inside [_mid] needs. *)
      apply ftag_btyp_to_utyp_syn.
    + rewrite utyp_to_btyp_btyp_to_utyp_syn by eassumption.
      eassumption.
    + eapply consis_refines_paint; eassumption.
    + exists Ψ'. split; [ fsetdec | simpl; exact HΨ' ].
  - (* d_sub__check (tc): excluded, [is_fn_n n mode_tc] is uninhabited. *)
    inversion Hfn.
  - (* d_sub__forall_r (tc): excluded. *)
    inversion Hfn.
  - (* d_sub__arg (fn m'): peel one arrow, recurse on the result spine. *)
    inversion Hfn; subst.
    dependent destruction Hspine.
    edestruct IHHsub as [Ψ2' [Hb2 Hres]];
      [ eassumption | eassumption | eassumption | ].
    exists (Ψ1 `union` Ψ2'). split.
    + fsetdec.
    + simpl. eapply d_sub__arg; [ eassumption | exact Hres | reflexivity ].
  - (* d_sub__forall_l_tagged: subset invariant + set difference. *)
    edestruct IHHsub as [Δr [Hb Hr]];
      [ eassumption | eassumption | eassumption | ].
    exists (Δr ∖ Ψ'). split.
    + fsetdec.
    + eapply d_sub__forall_l_tagged with (Ψ' := Ψ').
      * destruct m as [ | | m']; simpl;
          [ exfalso; apply H; reflexivity | discriminate | discriminate ].
      * fsetdec.
      * eassumption.
      * eassumption.
      * eassumption.
      * eassumption.
      * eapply d_sub_equiv; [ | exact Hr ]. fsetdec.
  - (* d_sub__forall_l_untagged: as above. *)
    edestruct IHHsub as [Δr [Hb Hr]];
      [ eassumption | eassumption | eassumption | ].
    exists (Δr ∖ Ψ'). split.
    + fsetdec.
    + eapply d_sub__forall_l_untagged with (Ψ' := Ψ').
      * destruct m as [ | | m']; simpl;
          [ exfalso; apply H; reflexivity | discriminate | discriminate ].
      * fsetdec.
      * eassumption.
      * eassumption.
      * eassumption.
      * eassumption.
      * eapply d_sub_equiv; [ | exact Hr ]. fsetdec.
Qed.

(** A consistency whose RHS is guarded forces the (synthesised) LHS to be
    guarded too: every ∀-RHS consistency rule is ruled out by [guarded_btyp]
    (which excludes ∀). *)
(** * Consistency ⇒ checking-subtyping, and the [FN^0] abstraction helpers.

    [d_consis_syn_sub_tc] turns a consistency into a [tc] subtyping (the ∀
    target is instantiated by the bound variable — an untagged witness), and
    drives the [check] case of the abstraction tail helpers. *)

Lemma consis_guarded_btyp_lhs : forall Δ Γ C B,
    {{ Δ ⨟ Γ ⊢ C ∼ B }}d -> guarded_btyp B -> guarded_utyp C.
Proof.
  intros Δ Γ C B Hc Hg.
  inversion Hc; subst; try (inversion Hg; fail).
  - auto with fresco.
  - auto with fresco.
  - apply guarded_utyp__arrow; eapply d_consis_lc_utyp; eassumption.
Qed.

(** Direct consistency ⇒ checking-subtyping, for a SYNTHESISED LHS against an
    [is_ityp] target.  The guarded targets close by [d_sub__check] (which
    consumes the consistency directly); the ∀ target generalises by
    [forall_r] and then instantiates the synthesised ∀ with the bound
    variable — an untagged [is_dtyp] witness with [d_tags ∅] — so the IH
    fires without any tag-context bookkeeping (contrast CST transitivity,
    which must thread arbitrary tagged witnesses). *)
Lemma d_consis_syn_sub_tc : forall Bn, is_ityp Bn ->
    forall Δ Γ B',
      {{ Δ ⨟ Γ ⊢ (btyp_to_utyp_syn B') ∼ Bn }}d ->
      {{ Δ ⨟ Γ ⊢[ mode_tc ] (btyp_to_utyp_syn B') ⩽ Bn }}d.
Proof.
  intros Bn Hityp.
  induction Hityp; intros Δ Γ B' Hcons.
  - (* unit *)
    apply d_sub__check;
      [ eapply consis_guarded_btyp_lhs; [ exact Hcons | apply guarded_btyp__unit ]
      | apply guarded_btyp__unit | exact Hcons | apply is_ityp__unit ].
  - (* var α *)
    apply d_sub__check;
      [ eapply consis_guarded_btyp_lhs; [ exact Hcons | apply guarded_btyp__var ]
      | apply guarded_btyp__var | exact Hcons | apply is_ityp__var ].
  - (* arrow: lc from is_ityp of the components *)
    apply d_sub__check;
      [ eapply consis_guarded_btyp_lhs;
          [ exact Hcons | apply guarded_btyp__arrow; apply is_ityp_lc; assumption ]
      | apply guarded_btyp__arrow; apply is_ityp_lc; assumption
      | exact Hcons | apply is_ityp__arrow; assumption ].
  - (* all: Bn = btyp_all_inh A.  Only ∀-shaped sources survive. *)
    destruct B'; simpl in Hcons; try solve [ inversion Hcons ];
      dependent destruction Hcons;
      match goal with
      | Hc : forall α0, α0 `notin` ?L1 -> {{ _ ⨟ _ ⊢ _ ∼ _ }}d |- _ =>
          apply d_sub__forall_r with (L := L `union` L1 `union` dom Γ);
          [ apply is_ityp__all with (L := L); assumption | ];
          intros α Hα;
          apply d_sub__forall_l_untagged with (Ψ' := (@empty : atoms)) (ph := utyp_var_f α);
          [ intro Hco; discriminate
          | fsetdec
          | clear; fsetdec
          | apply d_tags__var; reflexivity
          | apply d_wf_utyp__var; simpl; auto
          | apply is_dtyp__var
          | specialize (Hc α ltac:(clear -Hα; solve_notin_auto));
            change (utyp_var_f α) with (btyp_to_utyp_syn (btyp_var_f α)) in Hc |- *;
            rewrite <- btyp_to_utyp_syn_open in Hc |- *;
            apply d_sub_equiv with (Δ := Ψ); [ clear; fsetdec | ];
            apply H0; [ clear -Hα; fsetdec | exact Hc ] ]
      end.
Qed.

(** The n=0 abstraction (tail) case, as a standalone induction on the tail
    subtyping.  [Bbody] is synthesised, [A] monomorphic (forced by [is_styp
    (inh A)]).  The body capability [Hbody] is quantified over [ctx_weaken]
    extensions so the [forall_r] (∀-target generalisation) recursion can use
    it at the tvar-extended context — the two-insertion case the single-slot
    formulation can't express.  Arrow targets (infer/check/arg) rebuild
    [d_typing__abs] with [consis_mono_arg] pinning the argument and [Hbody]
    subsuming the body; [forall_r] generalises via [d_typing__forall]. *)
(** [d_sub_skmod] (subtyping preserves the [skmod{TY}] colour/mode discipline)
    now lives in [prop_wellformed] alongside [d_typing_skmod]. *)

(** A [btyp_spine] preserves [mod_comp_ty]: if the tail [Bnew] is [M]-coloured then
    the whole spine result [Bres] is [(mode_fn_n_subst m M)]-coloured (each
    peeled arrow re-wraps with [mod_comp_ty__fn]).  Discharges the [skmod] premise
    of the abstraction reconstructed in [d_typing_general_subsumption_spine]. *)
Lemma btyp_spine_skmod : forall n Bfull B Bnew Bres m M,
    btyp_spine n Bfull B Bnew Bres ->
    is_fn_n n m ->
    mod_comp_ty Bnew M ->
    mod_comp_ty Bres (mode_fn_n_subst m M).
Proof.
  intros n Bfull B Bnew Bres m M Hsp. revert m M.
  induction Hsp; intros m M Hfn Hsk.
  - inversion Hfn; subst. simpl. exact Hsk.
  - inversion Hfn; subst. simpl. apply mod_comp_ty__fn. eapply IHHsp; eassumption.
Qed.

Lemma d_sd_typing_abs_tail_gen : forall L0 e A Bbody M Bnew Γ',
    mono_ptyp A ->
    is_styp Bbody ->
    d_wf_ptyp Γ' A ->
    (forall Γ'' x M' B'',
       ctx_weaken Γ' Γ'' ->
       x `notin` (L0 `union` dom Γ'') ->
       {{ empty ⨟ ((x ~ dbind_typ A) ++ Γ'') ⊢[ M' ] (btyp_to_utyp_syn Bbody) ⩽ B'' }}d ->
       {{ ((x ~ dbind_typ A) ++ Γ'') ⊢ˢᵈ[ M' ] open_exp_wrt_exp e (exp_var_f x) ⦂ B'' }}d) ->
    {{ empty ⨟ Γ' ⊢[ M ]
      (utyp_arrow (btyp_to_utyp_syn (ptyp_to_btyp_inh A)) (btyp_to_utyp_syn Bbody)) ⩽ Bnew }}d ->
    {{ Γ' ⊢ˢᵈ[ M ] exp_abs e ⦂ Bnew }}d.
Proof.
  intros L0 e A Bbody M Bnew Γ' Hmono Hstyp Hwf Hbody Hsub.
  remember (utyp_arrow (btyp_to_utyp_syn (ptyp_to_btyp_inh A))
              (btyp_to_utyp_syn Bbody)) as Clhs eqn:HC.
  remember (@empty) as Ψ0 eqn:HD.
  revert Hwf Hbody.
  induction Hsub; intros Hwf Hbody; try (exfalso; discriminate HC).
  - (* infer (M = ti): Bnew = arrow Bn1 Bn2 by arrow consistency. *)
    subst. dependent destruction H.
    rename B1 into Bn1. rename B2 into Bn2.
    pose proof (consis_mono_arg H Hmono) as HBn1. subst Bn1.
    apply d_sd_typing__abs with (L := L0 `union` dom Γ) (A := A).
    + discriminate.
    + assumption.
    + apply mod_comp_ty__ti. assumption.
    + intros xv Hxv.
      eapply (Hbody Γ xv mode_ti Bn2 (ctx_weaken_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      apply d_sub__infer; [ | exact (is_styp_arrow_r H2) | reflexivity ].
      eapply d_consis_equiv; [ | eassumption ]. fsetdec.
  - (* check (M = tc): the checked lambda is [__abs_check_base] (the ᾱ = ·
       arrow); the body's tc-subtyping comes from the body consistency via
       [d_consis_syn_sub_tc] (which handles the ∀-target internally by
       bound-variable instantiation). *)
    subst. dependent destruction H1.
    rename B1 into Bn1. rename B2 into Bn2.
    match goal with
    | Harg : {{ _ ⨟ _ ⊢ btyp_to_utyp_syn (ptyp_to_btyp_inh A) ∼ Bn1 }}d |- _ =>
        pose proof (consis_mono_arg Harg Hmono) as HBn1
    end. subst Bn1.
    match goal with Hit : is_ityp (btyp_arrow _ Bn2) |- _ => inversion Hit; subst end.
    apply d_sd_typing__abs_check_base with (L := L0 `union` dom Γ).
    + assumption.
    + assumption.
    + intros xv Hxv.
      eapply (Hbody Γ xv mode_tc Bn2 (ctx_weaken_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      eapply d_consis_syn_sub_tc;
        [ match goal with Hit : is_ityp Bn2 |- _ => exact Hit end
        | match goal with Hbc : {{ _ ⨟ _ ⊢ btyp_to_utyp_syn Bbody ∼ Bn2 }}d |- _ =>
            eapply d_consis_equiv; [ | exact Hbc ]; fsetdec end ].
  - (* forall_r (M = tc): the folded ∀-peel [__abs_check_step], recurse. *)
    subst.
    apply d_sd_typing__abs_check_step with (L := L `union` L0 `union` dom Γ).
    + assumption.
    + intros α Hα.
      eapply (H1 α ltac:(solve_notin_auto)); [ reflexivity | reflexivity | | ].
      * apply d_wf_ptyp_ctx_weaken with (Γ := Γ);
          [ apply ctx_weaken_app_front | assumption ].
      * intros Γ'' xv M' B'' Hcw Hfr Hsb.
        eapply (Hbody Γ'' xv M' B''); [ | exact Hfr | exact Hsb ].
        eapply ctx_weaken_trans; [ apply ctx_weaken_app_front | exact Hcw ].
  - (* arg (M = fn m'): the result is already a subtyping (at Ψ2 [=] empty). *)
    subst. injection HC; intros; subst.
    pose proof (consis_mono_arg H Hmono) as HBn1. subst B1.
    apply d_sd_typing__abs with (L := L0 `union` dom Γ) (A := A).
    + discriminate.
    + assumption.
    + apply mod_comp_ty__fn.
      match goal with Hs : {{ _ ⨟ _ ⊢[ _ ] btyp_to_utyp_syn Bbody ⩽ B2 }}d |- _ =>
        exact (d_sub_skmod Hs) end.
    + intros xv Hxv.
      eapply (Hbody Γ xv m B2 (ctx_weaken_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      match goal with Hs : {{ _ ⨟ _ ⊢[ _ ] btyp_to_utyp_syn Bbody ⩽ B2 }}d |- _ =>
        eapply d_sub_equiv; [ | exact Hs ] end.
      fsetdec.
Qed.

(** The [abs_anno] variant: the argument is an arbitrary bidirectional [Barg]
    ([is_styp], erasing to the annotation [A]) instead of the mono [inh A].
    The rebuilt argument [Bn1] (from the arg consistency) is a valid argument
    because consistency preserves erasure ([d_consis_btyp_erase]). *)
Lemma d_sd_typing_abs_anno_tail_gen : forall L0 e A Barg Bbody M Bnew Γ',
    is_styp Barg ->
    btyp_to_ptyp Barg = A ->
    is_styp Bbody ->
    d_wf_ptyp Γ' A ->
    (forall Γ'' x M' B'',
       ctx_weaken Γ' Γ'' ->
       x `notin` (L0 `union` dom Γ'') ->
       {{ empty ⨟ ((x ~ dbind_typ A) ++ Γ'') ⊢[ M' ] (btyp_to_utyp_syn Bbody) ⩽ B'' }}d ->
       {{ ((x ~ dbind_typ A) ++ Γ'') ⊢ˢᵈ[ M' ] open_exp_wrt_exp e (exp_var_f x) ⦂ B'' }}d) ->
    {{ empty ⨟ Γ' ⊢[ M ]
      (utyp_arrow (btyp_to_utyp_syn Barg) (btyp_to_utyp_syn Bbody)) ⩽ Bnew }}d ->
    {{ Γ' ⊢ˢᵈ[ M ] exp_abs_anno A e ⦂ Bnew }}d.
Proof.
  intros L0 e A Barg Bbody M Bnew Γ' HsBarg HBargA Hstyp Hwf Hbody Hsub. subst A.
  remember (utyp_arrow (btyp_to_utyp_syn Barg) (btyp_to_utyp_syn Bbody)) as Clhs eqn:HC.
  remember (@empty) as Ψ0 eqn:HD.
  revert Hwf Hbody.
  induction Hsub; intros Hwf Hbody; try (exfalso; discriminate HC).
  - (* infer (M = ti) *)
    subst. dependent destruction H. rename B1 into Bn1. rename B2 into Bn2.
    assert (Herase : btyp_to_ptyp Bn1 = btyp_to_ptyp Barg).
    { pose proof (d_consis_btyp_erase H) as He.
      rewrite (utyp_to_btyp_btyp_to_utyp_syn HsBarg) in He.
      symmetry. exact He. }
    apply d_sd_typing__abs_anno with (L := L0 `union` dom Γ) (B1 := Bn1).
    + discriminate.
    + assumption.
    + exact Herase.
    + apply mod_comp_ty__ti; assumption.
    + intros xv Hxv.
      eapply (Hbody Γ xv mode_ti Bn2 (ctx_weaken_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      apply d_sub__infer; [ | exact (is_styp_arrow_r H2) | reflexivity ].
      eapply d_consis_equiv; [ | eassumption ]. fsetdec.
  - (* check (M = tc): mirror infer; body tc-subtyping via d_consis_syn_sub_tc. *)
    subst. dependent destruction H1.
    rename B1 into Bn1. rename B2 into Bn2.
    assert (Herase : btyp_to_ptyp Bn1 = btyp_to_ptyp Barg).
    { match goal with Harg : {{ _ ⨟ _ ⊢ btyp_to_utyp_syn Barg ∼ Bn1 }}d |- _ =>
        pose proof (d_consis_btyp_erase Harg) as He end.
      rewrite (utyp_to_btyp_btyp_to_utyp_syn HsBarg) in He.
      symmetry. exact He. }
    match goal with Hit : is_ityp (btyp_arrow _ Bn2) |- _ => inversion Hit; subst end.
    assert (HBn1 : Bn1 = ptyp_to_btyp_inh (btyp_to_ptyp Barg)).
    { rewrite <- Herase. symmetry. apply ptyp_to_btyp_inh_btyp_to_ptyp. assumption. }
    rewrite HBn1.
    apply d_sd_typing__abs_anno_check_base with (L := L0 `union` dom Γ).
    + assumption.
    + assumption.
    + intros xv Hxv.
      eapply (Hbody Γ xv mode_tc Bn2 (ctx_weaken_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      eapply d_consis_syn_sub_tc;
        [ match goal with Hit : is_ityp Bn2 |- _ => exact Hit end
        | match goal with Hbc : {{ _ ⨟ _ ⊢ btyp_to_utyp_syn Bbody ∼ Bn2 }}d |- _ =>
            eapply d_consis_equiv; [ | exact Hbc ]; fsetdec end ].
  - (* forall_r (M = tc): the folded ∀-peel [__abs_anno_check_step]. *)
    subst.
    apply d_sd_typing__abs_anno_check_step with (L := L `union` L0 `union` dom Γ).
    + assumption.
    + intros α Hα.
      eapply (H1 α ltac:(solve_notin_auto)); [ reflexivity | reflexivity | | ].
      * apply d_wf_ptyp_ctx_weaken with (Γ := Γ);
          [ apply ctx_weaken_app_front | assumption ].
      * intros Γ'' xv M' B'' Hcw Hfr Hsb.
        eapply (Hbody Γ'' xv M' B''); [ | exact Hfr | exact Hsb ].
        eapply ctx_weaken_trans; [ apply ctx_weaken_app_front | exact Hcw ].
  - (* arg (M = fn m') *)
    subst. injection HC; intros; subst.
    assert (Herase : btyp_to_ptyp B1 = btyp_to_ptyp Barg).
    { pose proof (d_consis_btyp_erase H) as He.
      rewrite (utyp_to_btyp_btyp_to_utyp_syn HsBarg) in He.
      symmetry. exact He. }
    apply d_sd_typing__abs_anno with (L := L0 `union` dom Γ) (B1 := B1).
    + discriminate.
    + assumption.
    + exact Herase.
    + apply mod_comp_ty__fn.
      match goal with Hs : {{ _ ⨟ _ ⊢[ _ ] btyp_to_utyp_syn Bbody ⩽ B2 }}d |- _ =>
        exact (d_sub_skmod Hs) end.
    + intros xv Hxv.
      eapply (Hbody Γ xv m B2 (ctx_weaken_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      match goal with Hs : {{ _ ⨟ _ ⊢[ _ ] btyp_to_utyp_syn Bbody ⩽ B2 }}d |- _ =>
        eapply d_sub_equiv; [ | exact Hs ] end.
      fsetdec.
Qed.

(** The free ε-tags (tag binders) of a [utyp].  This is a purely syntactic
    upper bound on every tag context a subtyping/consistency can carry: a
    paint-image LHS has NONE, forcing its subtyping context to be empty. *)
(** * Paint-LHS forces the empty tag context.

    A subtyping's tag context is bounded by the LHS's own ε-tags
    ([d_sub_ctx_subset_tags]); a paint image has none, so any subtyping out
    of one is at the empty context — the fact the spine [sub] case needs. *)

Fixpoint utyp_tags (C : utyp) : atoms :=
  match C with
  | utyp_arrow C1 C2 => utyp_tags C1 `union` utyp_tags C2
  | utyp_all_tag ε C0 => add ε (utyp_tags C0)
  | utyp_all_syn C0 => utyp_tags C0
  | _ => empty
  end.

Lemma utyp_tags_paint : forall B, utyp_tags (btyp_to_utyp_syn B) [=] empty.
Proof.
  induction B; simpl; try reflexivity;
    [ rewrite IHB1, IHB2; fsetdec | exact IHB | exact IHB ].
Qed.

Lemma utyp_tags_open_rec_var : forall C α' k,
    utyp_tags (open_utyp_wrt_utyp_rec k (utyp_var_f α') C) [=] utyp_tags C.
Proof.
  induction C; intros α' k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - rewrite IHC1, IHC2; reflexivity.
  - rewrite IHC; reflexivity.
  - rewrite IHC; reflexivity.
Qed.

Lemma utyp_tags_open_var : forall C α,
    utyp_tags (open_utyp_wrt_utyp C (utyp_var_f α)) [=] utyp_tags C.
Proof. intros C α. apply utyp_tags_open_rec_var. Qed.

Lemma utyp_tags_open_rec_le : forall C C' k,
    utyp_tags (open_utyp_wrt_utyp_rec k C' C) [<=] utyp_tags C `union` utyp_tags C'.
Proof.
  induction C; intros C' k; simpl; try fsetdec.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; fsetdec.
  - specialize (IHC1 C' k); specialize (IHC2 C' k); fsetdec.
  - specialize (IHC C' (S k)); fsetdec.
  - specialize (IHC C' (S k)); fsetdec.
Qed.

Lemma utyp_tags_open_le : forall C C',
    utyp_tags (open_utyp_wrt_utyp C C') [<=] utyp_tags C `union` utyp_tags C'.
Proof. intros C C'. apply utyp_tags_open_rec_le. Qed.

(** [d_tags] records exactly the ε-tags of a tag-type. *)
Lemma d_tags_tags : forall Δ C, d_tags Δ C -> Δ [=] utyp_tags C.
Proof.
  intros Δ C H. induction H; simpl.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - pick fresh α for (L `union` ftvar_in_utyp C).
    match goal with IH : forall _, _ -> _ [=] _ |- _ =>
      specialize (IH α ltac:(solve_notin_auto)) end.
    rewrite utyp_tags_open_var in *. fsetdec.
Qed.

(** A consistency's tag context is bounded by the LHS's own ε-tags. *)
Lemma d_consis_ctx_subset_tags : forall Δ Γ C B,
    {{ Δ ⨟ Γ ⊢ C ∼ B }}d -> Δ [<=] utyp_tags C.
Proof.
  intros Δ Γ C B H. induction H; simpl;
    try (pick fresh α for (L `union` ftvar_in_utyp C);
         match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
           specialize (IH α ltac:(solve_notin_auto)) end;
         rewrite utyp_tags_open_var in *); fsetdec.
Qed.

(** A subtyping's tag context is bounded by the LHS's own ε-tags.  [forall_l]
    closes because the instantiation tags [Ψ'] sit inside [utyp_tags ph]
    (via [d_tags_tags] + [utyp_tags_open_le]) and are disjoint from the
    conclusion [Δ] (the rule's freshness side-condition). *)
Lemma d_sub_ctx_subset_tags : forall M Δ Γ C B,
    {{ Δ ⨟ Γ ⊢[ M ] C ⩽ B }}d -> Δ [<=] utyp_tags C.
Proof.
  intros M Δ Γ C B H. induction H; simpl.
  - (* infer *) fsetdec.
  - (* check *) eapply d_consis_ctx_subset_tags; eassumption.
  - (* forall_r: same LHS; IH is cofinite *)
    pick fresh α for L.
    match goal with IH : forall _, _ `notin` _ -> _ [<=] _ |- _ =>
      apply (IH α); fsetdec end.
  - (* arg *)
    match goal with Hc : {{ _ ⨟ _ ⊢ C1 ∼ _ }}d |- _ =>
      pose proof (d_consis_ctx_subset_tags Hc) as Htag end.
    fsetdec.
  - (* forall_l_tagged: Ψ' = utyp_tags ph (d_tags_tags), disjoint from Δ (H0). *)
    pose proof (d_tags_tags H2) as Hph.
    pose proof (utyp_tags_open_le C ph) as Hopen.
    fsetdec.
  - (* forall_l_untagged *)
    pose proof (d_tags_tags H2) as Hph.
    pose proof (utyp_tags_open_le C ph) as Hopen.
    fsetdec.
Qed.

(** A subtyping out of a paint-image LHS is forced to the EMPTY tag context:
    paint has no ε-tags, and [d_sub_ctx_subset_tags] bounds the context by
    them.  This is what lets [d_sub_trans_spine]'s grown output be re-based to
    [empty] for the subsumption rule. *)
Lemma d_sub_paint_lhs_empty : forall M Δ Γ B B',
    {{ Δ ⨟ Γ ⊢[ M ] (btyp_to_utyp_syn B) ⩽ B' }}d -> Δ [=] empty.
Proof.
  intros M Δ Γ B B' H.
  pose proof (d_sub_ctx_subset_tags H) as Hle.
  rewrite utyp_tags_paint in Hle. fsetdec.
Qed.

(** Generalised General Subsumption for the SYNTAX-DIRECTED system (the
    headline).  With the base-term restriction removed, [d_typing] has the
    unrestricted [Sub] RULE, so its general subsumption is trivial; the proof
    obligation moved here: [d_sd_typing] has no [Sub] rule, and the [FN^n]
    spine subsumption must be proved ADMISSIBLE.  Subtypes only the
    synthesised result of the [FN^n] spine, keeping the arguments fixed.
    Completeness of the syntax-directed system consumes this lemma. *)
Lemma d_sd_typing_general_subsumption_spine : forall m1 Γ e Bfull,
    {{ Γ ⊢ˢᵈ[ m1 ] e ⦂ Bfull }}d ->
    forall Γ',
      ctx_weaken Γ Γ' ->
      forall n B' M B Bres,
        is_fn_n n m1 ->
        btyp_spine n Bfull B' B Bres ->
        {{ empty ⨟ Γ' ⊢[ M ] (btyp_to_utyp_syn B') ⩽ B }}d ->
        {{ Γ' ⊢ˢᵈ[ mode_fn_n_subst m1 M ] e ⦂ Bres }}d.
Proof.
  intros m1 Γ e Bfull Hty.
  induction Hty; intros Γ' Hcw n A0 M0 B0 Bres Hfn Hspine Htail.
  - (* unit: the embedded subtyping composes with the [Bfull]-spine via
       [d_sub_trans_spine]; the tag context is forced EMPTY by
       [d_sub_paint_lhs_empty] (paint LHS has no ε-tags), so [__unit]
       re-emits directly. *)
    apply d_sd_typing__unit.
    pose proof (d_sub_ctx_weaken Hcw H) as Hs0'.
    edestruct (d_sub_trans_spine Hs0' Hfn Hspine Htail) as [Δ'' [_ HΔ'']].
    pose proof HΔ'' as HΔ''b.
    replace (ptyp_to_utyp_syn ptyp_unit)
      with (btyp_to_utyp_syn (ptyp_to_btyp_syn ptyp_unit)) in HΔ''b
      by (rewrite <- ptyp_to_utyp_syn_btyp_to_ptyp, btyp_to_ptyp_ptyp_to_btyp_syn; reflexivity).
    apply d_sub_equiv with (Δ := Δ'');
      [ eapply d_sub_paint_lhs_empty; exact HΔ''b | exact HΔ'' ].
  - (* var: as [unit]; [binds] survives [ctx_weaken]. *)
    apply d_sd_typing__var with (A := A).
    + eapply binds_ctx_weaken; eassumption.
    + pose proof (d_sub_ctx_weaken Hcw H0) as Hs0'.
      edestruct (d_sub_trans_spine Hs0' Hfn Hspine Htail) as [Δ'' [_ HΔ'']].
      pose proof HΔ'' as HΔ''b.
      replace (ptyp_to_utyp_syn A)
        with (btyp_to_utyp_syn (ptyp_to_btyp_syn A)) in HΔ''b
        by (rewrite <- ptyp_to_utyp_syn_btyp_to_ptyp, btyp_to_ptyp_ptyp_to_btyp_syn; reflexivity).
      apply d_sub_equiv with (Δ := Δ'');
        [ eapply d_sub_paint_lhs_empty; exact HΔ''b | exact HΔ'' ].
  - (* abs: split on the spine. *)
    assert (Hskm : mod_comp_ty Bres (mode_fn_n_subst m M0))
      by (eapply btyp_spine_skmod; [ exact Hspine | exact Hfn | exact (d_sub_skmod Htail) ]).
    dependent destruction Hspine.
    + (* __tail (n=0): generalisation helper. *)
      inversion Hfn; subst. simpl.
      eapply d_sd_typing_abs_tail_gen with (L0 := L) (Bbody := B).
      * apply is_styp_ptyp_to_btyp_inh_mono.
        match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_l Hs) end.
      * match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_r Hs) end.
      * eapply d_wf_ptyp_ctx_weaken; eassumption.
      * intros Γ'' x M' B'' Hcw'' Hfr Hsb.
        eapply (H3 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ'')).
        -- apply ctx_weaken_cons. eapply ctx_weaken_trans; [ exact Hcw | exact Hcw'' ].
        -- apply is_fn_n__ti.
        -- apply btyp_spine__tail.
           match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_r Hs) end.
        -- exact Hsb.
      * exact Htail.
    + (* __arrow (n>0): keep [inh A] fixed, recurse on the body via the
         context-general IH (insert under the binder [x:A]). *)
      dependent destruction Hfn. simpl.
      apply d_sd_typing__abs with (L := L `union` dom Γ') (A := A).
      * discriminate.
      * eapply d_wf_ptyp_ctx_weaken; eassumption.
      * exact Hskm.
      * intros x Hx.
        eapply (H3 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ')).
        -- apply ctx_weaken_cons. exact Hcw.
        -- eassumption.
        -- eassumption.
        -- apply d_sub_weakening_head with (Γ' := (x ~ dbind_typ A)). exact Htail.
  - (* abs_check_step (tc): excluded. *)
    inversion Hfn.
  - (* abs_check_base (tc): excluded. *)
    inversion Hfn.
  - (* anno: as [var]; the checked subderivation is weakened. *)
    eapply d_sd_typing__anno.
    + eapply d_sd_typing_ctx_weaken; eassumption.
    + match goal with Hs : {{ empty ⨟ _ ⊢[ _ ] ptyp_to_utyp_syn _ ⩽ _ }}d |- _ =>
        pose proof (d_sub_ctx_weaken Hcw Hs) as Hs0' end.
      edestruct (d_sub_trans_spine Hs0' Hfn Hspine Htail) as [Δ'' [_ HΔ'']].
      pose proof HΔ'' as HΔ''b.
      replace (ptyp_to_utyp_syn A)
        with (btyp_to_utyp_syn (ptyp_to_btyp_syn A)) in HΔ''b
        by (rewrite <- ptyp_to_utyp_syn_btyp_to_ptyp, btyp_to_ptyp_ptyp_to_btyp_syn; reflexivity).
      apply d_sub_equiv with (Δ := Δ'');
        [ eapply d_sub_paint_lhs_empty; exact HΔ''b | exact HΔ'' ].
  - (* abs_anno: split on the spine. *)
    assert (Hskm : mod_comp_ty Bres (mode_fn_n_subst m M0))
      by (eapply btyp_spine_skmod; [ exact Hspine | exact Hfn | exact (d_sub_skmod Htail) ]).
    dependent destruction Hspine.
    + (* __tail (n=0): abs_anno generalisation helper. *)
      inversion Hfn; subst. simpl.
      eapply d_sd_typing_abs_anno_tail_gen with (L0 := L) (Barg := B1) (Bbody := B2).
      * match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_l Hs) end.
      * reflexivity.
      * match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_r Hs) end.
      * eapply d_wf_ptyp_ctx_weaken; eassumption.
      * intros Γ'' x M' B'' Hcw'' Hfr Hsb.
        eapply (H4 x ltac:(solve_notin_auto) ((x ~ dbind_typ (btyp_to_ptyp B1)) ++ Γ'')).
        -- apply ctx_weaken_cons. eapply ctx_weaken_trans; [ exact Hcw | exact Hcw'' ].
        -- apply is_fn_n__ti.
        -- apply btyp_spine__tail.
           match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_r Hs) end.
        -- exact Hsb.
      * exact Htail.
    + (* __arrow (n>0). *)
      dependent destruction Hfn. simpl.
      apply d_sd_typing__abs_anno with (L := L `union` dom Γ') (A := A) (B1 := B1).
      * discriminate.
      * eapply d_wf_ptyp_ctx_weaken; eassumption.
      * eassumption.
      * exact Hskm.
      * intros x Hx.
        eapply (H4 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ')).
        -- apply ctx_weaken_cons. exact Hcw.
        -- eassumption.
        -- eassumption.
        -- apply d_sub_weakening_head with (Γ' := (x ~ dbind_typ A)). exact Htail.
  - (* abs_anno_check_step (tc): excluded. *)
    inversion Hfn.
  - (* abs_anno_check_base (tc): excluded. *)
    inversion Hfn.
  - (* freeze (tc): excluded. *)
    inversion Hfn.
  - (* app: thread the spine through [e1] via the IH; weaken the side
       premises ([d_pat], [d_refine_syn], [e2]) by [ctx_weaken]. *)
    eapply d_sd_typing__app.
    + eapply d_pat_ctx_weaken; eassumption.
    + eapply d_refine_syn_ctx_weaken; eassumption.
    + eapply IHHty1.
      * exact Hcw.
      * apply is_fn_n__fn. exact Hfn.
      * apply btyp_spine__arrow. exact Hspine.
      * exact Htail.
    + eapply d_sd_typing_ctx_weaken; eassumption.
Qed.

(** General subsumption for the syntax-directed system (paper Lemma
    "general subsumption"; on [d_typing] this is now just the [Sub] rule).
    The paper's premise is a synthesized painting [syn{A}], so the native
    statement quantifies the plain type [A] and uses both paintings
    explicitly. *)
Theorem d_sd_typing_general_subsumption : forall Γ e A B m,
    d_wf_denv Γ ->
    {{ Γ ⊢ˢᵈ[ mode_ti ] e ⦂ ptyp_to_btyp_syn A }}d ->
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
    {{ Γ ⊢ˢᵈ[ m ] e ⦂ B }}d.
Proof.
  (* The n=0 corollary of the spine lemma: the [FN^0] spine is the tail, so
     [e : syn{A}] subsumes to [B] through [empty ⊢[m] syn{A} ⩽ B] directly. *)
  intros Γ e A B m Hwf Hty Hsub.
  assert (Hst : is_styp (ptyp_to_btyp_syn A)).
  { (* [syn{A}] is [is_styp]: it is [lc] because the subtyping [Hsub] forces
       its source [ptyp_to_utyp_syn A] locally closed. *)
    apply is_styp_ptyp_to_btyp_syn, lc_ptyp_of_lc_utyp_syn.
    eapply d_sub_lc_l. exact Hsub. }
  eapply (d_sd_typing_general_subsumption_spine Hty (ctx_weaken_refl Γ)
            (n := 0) (B' := ptyp_to_btyp_syn A) (M := m) (B := B) (Bres := B)).
  - apply is_fn_n__ti.
  - apply btyp_spine__tail. exact Hst.
  - rewrite btyp_to_utyp_syn_ptyp_to_btyp_syn. exact Hsub.
Qed.
