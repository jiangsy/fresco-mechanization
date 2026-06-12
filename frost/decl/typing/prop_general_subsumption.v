(** Frost declarative typing metatheory: D12 and D1 in native split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.typing.prop_weakening.
Require Import src.frost.decl.typing.def_gen.
Require Import src.frost.decl.typing.prop_subsumption_aux.

Set Implicit Arguments.

(** * Paper-faithful general subsumption (2026-06 rework).

    The reworked paper (syntax-directed.tex) proves general subsumption
    over the ORDINARY subtyping/typing ([d_sub] / [d_typing]) using three
    auxiliary lemmas — Consistency-Subtyping Transitivity, Subtyping
    Transitivity, Function Subtyping — and a mode-indexed ([FN^n])
    generalisation that subtypes only the synthesised RESULT tail while
    keeping the function arguments fixed.  This supersedes the [gutyp] /
    [d_sub_gen] route below.

    Function Subtyping (syntax-directed.tex:256): if a function source is
    subtyped, the target is a polymorphic function shape
    [inh{∀ᾱ}.B1 → B2] with the argument matched by consistency (invariant)
    and the result subtyped at the decremented mode.  Here we prove the
    non-[TC] modes, where the inh-∀ prefix ᾱ is empty (the paper notes ᾱ
    is non-empty only when M = TC, via repeated [ForallR]). *)
Lemma d_sub_function_nontc : forall m Δ Γ C1 C2 B,
    m <> mode_tc ->
    Δ ⨟ Γ ⊢[ m ] (utyp_arrow C1 C2) ⊑ B ->
    exists B1 B2 Δ1 Δ2,
      B = btyp_arrow B1 B2 /\
      Δ1 ⨟ Γ ⊨ C1 ≈ B1 /\
      Δ2 ⨟ Γ ⊢[ decr_mode m ] C2 ⊑ B2.
Proof.
  intros m Δ Γ C1 C2 B Hm Hsub.
  dependent destruction Hsub.
  - (* d_sub__infer (m = ti): the whole arrow is matched by consistency *)
    dependent destruction H.                 (* d_consis__arrow *)
    match goal with
    | H : _ ++ _ = nil |- _ => apply app_eq_nil in H as [-> ->]
    | H : nil = _ ++ _ |- _ => symmetry in H; apply app_eq_nil in H as [-> ->]
    end.
    match goal with                          (* is_styp (btyp_arrow _ _), any name *)
    | H : is_styp (btyp_arrow _ _) |- _ => dependent destruction H
    end.
    do 2 eexists; exists (@nil atom), (@nil atom).
    split; [ reflexivity | split ].
    + eassumption.
    + simpl. eauto using d_sub__infer.
  - (* d_sub__check (m = tc): excluded *) contradiction.
  - (* d_sub__forall_r (m = tc): excluded *) contradiction.
  - (* d_sub__arg (m = fn m'): argument by consistency, result subtyped *)
    do 4 eexists. split.
    + reflexivity.
    + split.
      * eassumption.
      * simpl. eassumption.
Qed.

(** Syn round-trip: painting a synthesised [btyp] to a [utyp] and back is
    the identity.  Derived from the existing [ptyp] round-trips (the
    coercions are structural [Fixpoint]s, so the [ptyp]-level identity
    needs no binder reasoning). *)
Lemma utyp_to_btyp_ptyp_to_utyp_syn : forall A,
    utyp_to_btyp (ptyp_to_utyp_syn A) = ptyp_to_btyp_syn A.
Proof. induction A; simpl; congruence. Qed.

Lemma utyp_to_btyp_btyp_to_utyp_syn : forall B,
    is_syn B -> utyp_to_btyp (btyp_to_utyp_syn B) = B.
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
Lemma d_consis_ttyp_refl : forall Γ ph,
    Γ ⊢ᵤ ph ->
    is_ttyp ph ->
    nil ⨟ Γ ⊨ ph ≈ (utyp_to_btyp ph).
Proof.
  intros Γ ph Hwf. induction Hwf; intros Htt; simpl.
  - apply d_consis__unit.
  - apply d_consis__var. assumption.
  - inversion Htt; subst.
    replace (@nil atom) with (@nil atom ++ @nil atom) by reflexivity.
    apply d_consis__arrow; [ apply IHHwf1 | apply IHHwf2 ]; assumption.
  - inversion Htt.                          (* utyp_all_syn is not is_ttyp *)
  - inversion Htt; subst.
    apply d_consis__forall_syn_tagged with (L := L `union` L0).
    intros X HX.
    change (btyp_var_f X) with (utyp_to_btyp (utyp_var_f X)).
    rewrite <- utyp_to_btyp_open.
    apply H0; [ fsetdec | ].
    match goal with
    | H : forall x, x `notin` _ -> is_ttyp _ |- _ => apply H; fsetdec
    end.
Qed.

(** Every well-formed [utyp] is consistent (nil tags) with its bidirectional
    image — generalises [d_consis_ttyp_refl] from [is_ttyp] to all [utyp]
    (the extra [utyp_all_syn] case goes via [ForallSyn]).  This is the
    "middle reflexivity" the general-middle CST reformulation needs. *)
Lemma d_consis_utyp_refl : forall Γ C,
    Γ ⊢ᵤ C ->
    nil ⨟ Γ ⊨ C ≈ (utyp_to_btyp C).
Proof.
  intros Γ C Hwf. induction Hwf; simpl.
  - apply d_consis__unit.
  - apply d_consis__var. assumption.
  - replace (@nil atom) with (@nil atom ++ @nil atom) by reflexivity.
    apply d_consis__arrow; assumption.
  - apply d_consis__forall_syn with (L := L).
    intros X HX. change (btyp_var_f X) with (utyp_to_btyp (utyp_var_f X)).
    rewrite <- utyp_to_btyp_open. apply H0; auto.
  - apply d_consis__forall_syn_tagged with (L := L).
    intros X HX. change (btyp_var_f X) with (utyp_to_btyp (utyp_var_f X)).
    rewrite <- utyp_to_btyp_open. apply H0; auto.
Qed.

(** [utyp_to_btyp] preserves local closure (needed for the btyp-side
    subst/open commute in the substitution lemma). *)
Lemma utyp_to_btyp_lc : forall C, lc_utyp C -> lc_btyp (utyp_to_btyp C).
Proof.
  intros C H. induction H; simpl.
  - apply lc_btyp_unit.
  - apply lc_btyp_var_f.
  - apply lc_btyp_arrow; assumption.
  - apply lc_btyp_all_syn. intros X.
    change (btyp_var_f X) with (utyp_to_btyp (utyp_var_f X)).
    rewrite <- utyp_to_btyp_open. apply H0.
  - apply lc_btyp_all_syn. intros X.
    change (btyp_var_f X) with (utyp_to_btyp (utyp_var_f X)).
    rewrite <- utyp_to_btyp_open. apply H0.
Qed.

(** [d_wf_utyp] head-weakening (prepend a context). *)
Lemma d_wf_utyp_weakening_head : forall Γ' Γ C,
    Γ ⊢ᵤ C ->
    (Γ' ++ Γ) ⊢ᵤ C.
Proof.
  intros Γ' Γ C H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_utyp_weakening. simpl. exact H.
Qed.

(** Tag-erasure of consistency: a consistency out of [Cmid] re-derives with
    [Cmid]'s ε-tags erased to syn ∀s ([btyp_to_utyp_syn (utyp_to_btyp Cmid)]),
    dropping the corresponding solved tags (hence the existential [Δ']).
    Proof structure (induction on the consistency): unit/var/arrow are
    structural; each forall case replaces the tagged rule by its untagged
    counterpart ([ForallInhTagged → ForallInhUntagged], [ForallSynTagged →
    ForallSyn]) and recovers the cofinite-uniform witness by picking one
    fresh [X0] and renaming via [d_consis_rename].  Needs small commute/ftvar
    helpers ([btyp_to_utyp_syn_open], [utyp_to_btyp_open], an
    [ftvar_utyp_to_btyp] bound).  This is the last genuinely-new lemma the
    CST reformulation rests on. *)
Lemma ftvar_utyp_to_btyp : forall C,
    ftvar_in_btyp (utyp_to_btyp C) [<=] ftvar_in_utyp C.
Proof. induction C; simpl; fsetdec. Qed.

(** Erase ([btyp_to_utyp_syn ∘ utyp_to_btyp]) commutes with [open] on a
    variable. *)
Lemma erase_open : forall C X,
    btyp_to_utyp_syn (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f X)))
    = open_utyp_wrt_utyp (btyp_to_utyp_syn (utyp_to_btyp C)) (utyp_var_f X).
Proof.
  intros C X. rewrite utyp_to_btyp_open. simpl.
  rewrite btyp_to_utyp_syn_open. reflexivity.
Qed.

Lemma d_consis_erase_tags : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    exists Δ', Δ' ⨟ Γ ⊨ (btyp_to_utyp_syn (utyp_to_btyp C)) ≈ B.
Proof.
  intros Δ Γ C B H. induction H.
  - (* unit *) exists (@nil atom). apply d_consis__unit.
  - (* var *) exists (@nil atom). simpl. apply d_consis__var; assumption.
  - (* arrow *)
    destruct IHd_consis1 as [Δ1' H1']. destruct IHd_consis2 as [Δ2' H2'].
    exists (Δ1' ++ Δ2'). simpl. apply d_consis__arrow; assumption.
  - (* forall_inh_tagged: ε-tag erased, ForallInhTagged → ForallInhUntagged *)
    pick fresh X0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 X0 ltac:(fsetdec)) as [Δ'0 HΔ'0].
    rewrite erase_open in HΔ'0.
    exists Δ'0. simpl.
    apply d_consis__forall_inh_untagged with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton X0).
    intros X HX.
    rewrite (subst_utyp_in_utyp_intro X0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro X0) by fsetdec.
    apply (@d_consis_rename _ _ _ _ HΔ'0 nil Γ X0 X); [ reflexivity | simpl; fsetdec ].
  - (* forall_inh_untagged: ForallInhUntagged → ForallInhUntagged *)
    pick fresh X0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 X0 ltac:(fsetdec)) as [Δ'0 HΔ'0].
    rewrite erase_open in HΔ'0.
    exists Δ'0. simpl.
    apply d_consis__forall_inh_untagged with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton X0).
    intros X HX.
    rewrite (subst_utyp_in_utyp_intro X0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro X0) by fsetdec.
    apply (@d_consis_rename _ _ _ _ HΔ'0 nil Γ X0 X); [ reflexivity | simpl; fsetdec ].
  - (* forall_syn_tagged: ε-tag erased, ForallSynTagged → ForallSyn *)
    pick fresh X0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 X0 ltac:(fsetdec)) as [Δ'0 HΔ'0].
    rewrite erase_open in HΔ'0.
    exists Δ'0. simpl.
    apply d_consis__forall_syn with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton X0).
    intros X HX.
    rewrite (subst_utyp_in_utyp_intro X0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro X0) by fsetdec.
    apply (@d_consis_rename _ _ _ _ HΔ'0 nil Γ X0 X); [ reflexivity | simpl; fsetdec ].
  - (* forall_syn: ForallSyn → ForallSyn *)
    pick fresh X0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 X0 ltac:(fsetdec)) as [Δ'0 HΔ'0].
    rewrite erase_open in HΔ'0.
    exists Δ'0. simpl.
    apply d_consis__forall_syn with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton X0).
    intros X HX.
    rewrite (subst_utyp_in_utyp_intro X0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro X0) by fsetdec.
    apply (@d_consis_rename _ _ _ _ HΔ'0 nil Γ X0 X); [ reflexivity | simpl; fsetdec ].
Qed.

(** Composition through a general (possibly tagged) middle [Cmid] — the
    reusable bridge for the reformulated CST's infer/check/arg cases:
    [T ≈ ⌈Cmid⌉] composed with [Cmid ≈ B] gives [T ≈ B].  [utyp_to_btyp Cmid]
    is synthesised, so [d_consis_compose_syn] applies once the second
    premise's tags are erased ([d_consis_erase_tags]). *)
Lemma d_consis_trans_mid : forall Δ1 Δ2 Γ T Cmid B,
    lc_utyp Cmid ->
    Δ1 ⨟ Γ ⊨ T ≈ (utyp_to_btyp Cmid) ->
    Δ2 ⨟ Γ ⊨ Cmid ≈ B ->
    exists Δ, Δ ⨟ Γ ⊨ T ≈ B.
Proof.
  intros Δ1 Δ2 Γ T Cmid B Hlc HT HCmid.
  destruct (d_consis_erase_tags HCmid) as [Δ2' Herase].
  destruct (d_consis_compose_syn (is_syn_utyp_to_btyp Hlc) HT Herase)
    as [Δ [Hincl Hc]].
  exists Δ. exact Hc.
Qed.

(** [nil]-context variant for the reformulated CST's [infer] case: when the
    target [B] is synthesised the composed tag context collapses to [nil]
    (via [d_consis_compose_syn_nil_l]), which is what [d_sub__infer] demands. *)
Lemma d_consis_trans_mid_nil : forall Δ1 Δ2 Γ T Cmid B,
    lc_utyp Cmid ->
    is_syn B ->
    Δ1 ⨟ Γ ⊨ T ≈ (utyp_to_btyp Cmid) ->
    Δ2 ⨟ Γ ⊨ Cmid ≈ B ->
    nil ⨟ Γ ⊨ T ≈ B.
Proof.
  intros Δ1 Δ2 Γ T Cmid B Hlc Hsyn HT HCmid.
  destruct (d_consis_erase_tags HCmid) as [Δ2' Herase].
  eapply (d_consis_compose_syn_nil_l (B2 := utyp_to_btyp Cmid)).
  - apply is_syn_utyp_to_btyp; exact Hlc.
  - exact Hsyn.
  - exact HT.
  - exact Herase.
Qed.

(** The [d_consis] substitution lemma (the infrastructure the [forall_l]
    cases of both transitivity lemmas were blocked on).  Substituting a
    tvar [X0] by a tagged type [ph] on the unresolved side, and by its
    bidirectional image [utyp_to_btyp ph] on the bidirectional side,
    preserves consistency WITHOUT adding tags — the variable occurrences
    become [ph ≈ utyp_to_btyp ph], which is tag-free ([d_consis_ttyp_refl]).
    Structure mirrors [d_consis_rename] (var→var); the only changes are the
    [X0]-case (use the base fact) and the [lc]/wf side-conditions for [ph]. *)
Lemma d_consis_subst_tvar : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    forall Γ1 Γ2 X0 ph,
      Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
      (Γ1 ++ Γ2) ⊢ᵤ ph ->
      is_ttyp ph ->
      Δ ⨟ (Γ1 ++ Γ2) ⊨ (subst_utyp_in_utyp ph X0 C)
                      ≈ (subst_btyp_in_btyp (utyp_to_btyp ph) X0 B).
Proof.
  intros Δ Γ C B H. induction H; intros Γ1 Γ2 X0 ph Heq Hwf Htt; subst; simpl.
  - apply d_consis__unit.
  - (* var: [X = X0] uses the base fact; [X <> X0] stays a variable. *)
    match goal with |- context [ if ?d then _ else _ ] => destruct d end.
    + apply d_consis_ttyp_refl; assumption.
    + apply d_consis__var. analyze_binds H; auto.
  - apply d_consis__arrow; [ eapply IHd_consis1 | eapply IHd_consis2 ]; eauto.
  - apply d_consis__forall_inh_tagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton X0).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply is_ttyp_lc; assumption ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply utyp_to_btyp_lc; apply is_ttyp_lc; assumption ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z);
      [ fsetdec | simpl; reflexivity
      | rewrite_env ((Z ~ dbind_tvar) ++ (Γ1 ++ Γ2));
        apply d_wf_utyp_weakening_head; exact Hwf
      | assumption ].
  - apply d_consis__forall_inh_untagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton X0).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply is_ttyp_lc; assumption ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply utyp_to_btyp_lc; apply is_ttyp_lc; assumption ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z);
      [ fsetdec | simpl; reflexivity
      | rewrite_env ((Z ~ dbind_tvar) ++ (Γ1 ++ Γ2));
        apply d_wf_utyp_weakening_head; exact Hwf
      | assumption ].
  - apply d_consis__forall_syn_tagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton X0).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply is_ttyp_lc; assumption ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply utyp_to_btyp_lc; apply is_ttyp_lc; assumption ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z);
      [ fsetdec | simpl; reflexivity
      | rewrite_env ((Z ~ dbind_tvar) ++ (Γ1 ++ Γ2));
        apply d_wf_utyp_weakening_head; exact Hwf
      | assumption ].
  - apply d_consis__forall_syn with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton X0).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply is_ttyp_lc; assumption ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply utyp_to_btyp_lc; apply is_ttyp_lc; assumption ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z);
      [ fsetdec | simpl; reflexivity
      | rewrite_env ((Z ~ dbind_tvar) ++ (Γ1 ++ Γ2));
        apply d_wf_utyp_weakening_head; exact Hwf
      | assumption ].
Qed.

(** Consistency-Subtyping Transitivity (paper, syntax-directed.tex:152):
    a consistency into a synthesised type composes with a subtyping out of
    it.  The synthesised middle is carried as a [btyp] [B_A] with [is_syn],
    bridged to the subtyping LHS via [btyp_to_utyp_syn] (the same convention
    as [d_consis_compose_syn_nil]).  [is_syn] = [is_styp] up to
    [is_styp_is_syn]. *)
Lemma d_consis_sub_trans : forall M Δb Γ C B,
    Δb ⨟ Γ ⊢[ M ] C ⊑ B ->
    forall B_A T Δt,
      C = btyp_to_utyp_syn B_A ->
      is_syn B_A ->
      Δt ⨟ Γ ⊨ T ≈ B_A ->
      exists Δ, Δ ⨟ Γ ⊢[ M ] T ⊑ B.
Proof.
  intros M Δb Γ C B Hsub.
  induction Hsub; intros B_A T Δt Heq Hsyn Hcons.
  - (* d_sub__infer (ti): compose the two consistencies.  Since the RHS [B]
       is synthesised, no inh quantifier is reached, so the composed context
       collapses to [nil] (d_consis_compose_syn_nil_l). *)
    subst C. exists (@nil atom). apply d_sub__infer.
    + eapply d_consis_compose_syn_nil_l.
      * exact Hsyn.
      * apply is_styp_is_syn. eassumption.
      * exact Hcons.
      * eassumption.
    + assumption.
  - (* d_sub__check (tc): [T] is guarded (from [B_A] guarded + the
       consistency, via [d_consis_guarded_lhs] and the syn round-trip),
       and the consistency composes through to the inh target [B]. *)
    subst C.
    assert (HgT : guarded_utyp T).
    { eapply d_consis_guarded_lhs.
      - eassumption.
      - rewrite utyp_to_btyp_btyp_to_utyp_syn by assumption. exact Hcons. }
    destruct (@d_consis_compose_syn _ _ _ _ B_A _
                ltac:(eassumption) ltac:(exact Hcons) ltac:(eassumption))
      as [Δc [Hincl Hc]].
    exists Δc. apply d_sub__check; assumption.
  - (* d_sub__forall_r (tc): IH under a fresh [α] (consistency weakened via
       d_consis_weakening_head), then re-[ForallR].  Blocked on the
       cofinite-uniform witness: the IH gives a per-[α] context [Δ], so we
       need an ordinary [d_sub_rename] (only [d_sub_gen_rename] exists) to
       transport one fresh instance to all [α].  Deferred. *)
    admit.
  - (* d_sub__arg (fn m'): the source is an arrow, so [B_A] is an arrow;
       compose on the (consistency) argument, recurse (IH) on the result. *)
    destruct B_A as [ | n | X | B_A1 B_A2 | B_A0 | B_A0 ];
      simpl in Heq; try discriminate.
    injection Heq as HeqC1 HeqC2. subst.
    dependent destruction Hsyn.                 (* is_syn B_A1, is_syn B_A2 *)
    dependent destruction Hcons.                (* T = utyp_arrow T1 T2 *)
    destruct (@d_consis_compose_syn _ _ _ _ B_A1 _
                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption))
      as [Δc1 [Hincl1 Hc1]].
    destruct (IHHsub B_A2 _ _ eq_refl ltac:(eassumption) ltac:(eassumption))
      as [Δc2 Hres].
    exists (Δc1 ++ Δc2). apply d_sub__arg; eassumption.
  - (* d_sub__forall_l_tagged: LHS [utyp_all_etag] cannot be a
       [btyp_to_utyp_syn] image (no etag in a synthesised type). *)
    destruct B_A as [ | n | X | B_A1 B_A2 | B_A0 | B_A0 ];
      simpl in Heq; discriminate.
  - (* d_sub__forall_l_untagged: LHS is [utyp_all_syn] (so [B_A] is
       [btyp_all_syn]); the rule instantiates with [ph].  Blocked on a
       [d_consis] substitution lemma (does not exist) to push [T]'s
       consistency under [α ↦ ph] — the same hard sub-problem the old
       [d_sub_gen_trans_ti_lhs_aux] forall_l case flagged.  Deferred. *)
    admit.
Admitted.

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
    tail, replacing the tail throughout the spine.  Proved by induction on
    the subtyping: [infer] is [CST], [arg] is the recursion, [check] /
    [forall_r] are excluded by [is_fn_n], and the [forall_l] cases share
    CST's tag-context bookkeeping gap. *)
Lemma d_sub_trans_spine : forall m1 Δ Γ T Bfull,
    Δ ⨟ Γ ⊢[ m1 ] T ⊑ Bfull ->
    forall n A M B Bres,
      is_fn_n n m1 ->
      btyp_spine n Bfull A B Bres ->
      nil ⨟ Γ ⊢[ M ] (btyp_to_utyp_syn A) ⊑ B ->
      exists Δ', Δ' ⨟ Γ ⊢[ mode_fn_n_subst m1 M ] T ⊑ Bres.
Proof.
  intros m1 Δ Γ T Bfull Hsub.
  induction Hsub; intros n A0 M0 B0 Bres Hfn Hspine Htail.
  - (* d_sub__infer (ti): n = 0 forces the tail; compose by CST. *)
    inversion Hfn; subst.
    dependent destruction Hspine.
    edestruct (d_consis_sub_trans Htail) as [Δ' HΔ'];
      [ reflexivity
      | apply is_styp_is_syn; eassumption
      | eassumption
      | exists Δ'; simpl; exact HΔ' ].
  - (* d_sub__check (tc): excluded, [is_fn_n n mode_tc] is uninhabited. *)
    inversion Hfn.
  - (* d_sub__forall_r (tc): excluded. *)
    inversion Hfn.
  - (* d_sub__arg (fn m'): peel one arrow, recurse on the result spine. *)
    inversion Hfn; subst.
    dependent destruction Hspine.
    edestruct IHHsub as [Δ2' Hres];
      [ eassumption | eassumption | eassumption | ].
    eexists. simpl. apply d_sub__arg; eassumption.
  - (* d_sub__forall_l_tagged: needs the tag-context bookkeeping (the
       instantiation tags [Δ'] must be split back out of the IH's context),
       the same gap as CST's forall_l.  Deferred. *)
    admit.
  - (* d_sub__forall_l_untagged: as above. *)
    admit.
Admitted.

(** Generalised General Subsumption (paper, syntax-directed.tex:287): the
    headline.  Over PLAIN typing; subtypes only the synthesised result of
    the [FN^n] spine, keeping the arguments fixed.  D1 (general subsumption)
    is the [n = 0] corollary. *)
Lemma d_typing_general_subsumption_spine : forall m1 Γ e Bfull,
    Γ ⊢[ m1 ] e ⦂ Bfull ->
    forall n A M B Bres,
      is_fn_n n m1 ->
      btyp_spine n Bfull A B Bres ->
      nil ⨟ Γ ⊢[ M ] (btyp_to_utyp_syn A) ⊑ B ->
      Γ ⊢[ mode_fn_n_subst m1 M ] e ⦂ Bres.
Proof.
  intros m1 Γ e Bfull Hty.
  induction Hty; intros n A0 M0 B0 Bres Hfn Hspine Htail.
  - (* unit: n = 0 (tail); subsume the synthesised result via d_typing__sub
       fed by the tail subtyping [Htail]. *)
    inversion Hfn; subst. dependent destruction Hspine. simpl.
    apply d_typing__sub with (B1 := btyp_unit).
    + apply is_base_term__unit.
    + apply d_typing__unit.
    + rewrite ptyp_to_utyp_syn_btyp_to_ptyp. exact Htail.
  - (* var *)
    inversion Hfn; subst. dependent destruction Hspine. simpl.
    apply d_typing__sub with (B1 := ptyp_to_btyp_syn A).
    + apply is_base_term__var.
    + apply d_typing__var; assumption.
    + rewrite ptyp_to_utyp_syn_btyp_to_ptyp. exact Htail.
  - (* anno *)
    inversion Hfn; subst. dependent destruction Hspine. simpl.
    apply d_typing__sub with (B1 := ptyp_to_btyp_syn A).
    + apply is_base_term__anno.
    + apply d_typing__anno; assumption.
    + rewrite ptyp_to_utyp_syn_btyp_to_ptyp. exact Htail.
  - (* sub: compose via Subtyping Transitivity, then re-apply d_typing__sub.
       Needs the "tag-free (syn) LHS ⇒ nil tag context" fact so the composed
       subtyping fits d_typing__sub's nil-context premise.  Deferred. *)
    admit.
  - (* freeze (tc): [is_fn_n n mode_tc] is uninhabited. *)
    inversion Hfn.
  - (* forall (tc): excluded. *)
    inversion Hfn.
  - (* abs: split on the spine.
       - [__arrow] (n>0): the abs's inherited argument [inh A] is the first
         spine ARGUMENT [B1] (no [is_styp] needed there); recurse via the IH
         on the body and rebuild [d_typing__abs].  (Mode arithmetic:
         [decr (mode_fn_n_subst m M) = mode_fn_n_subst (decr m) M].)
       - [__tail] (n=0): requires [is_styp (btyp_arrow (inh A) B)], i.e.
         [is_styp (inh A)] — FALSE for polymorphic [A] (vacuous), but
         REACHABLE for monomorphic [A] (where [inh A = syn A]); that
         sub-case needs Function Subtyping (the paper's n=0 abs).
       Deferred. *)
    admit.
  - (* abs_anno: as abs, with the bidirectional [Barg].  Deferred. *)
    admit.
  - (* app: Function Subtyping on [e1]'s arrow type.  Deferred. *)
    admit.
Admitted.

(** D12, paper Lemma B.5: generalised general subsumption.  The source
    mode is restricted to [FN^n TI], and the target mode replaces the
    terminal [TI] by [m_new].  The subtyping premise consumes the
    generalized-unresolved embedding of the synthesized type. *)
Theorem d_typing_general_subsumption_gen : forall m_orig Γ e B1,
    Γ ⊢ᵍ[ m_orig ] e ⦂ B1 ->
    is_fn_n_ti m_orig ->
    d_wf_denv Γ ->
    forall m_new B2,
      nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m_orig m_new ] (btyp_to_gutyp B1) ⊑ B2 ->
      Γ ⊢ᵍ[ mode_fn_n_subst m_orig m_new ] e ⦂ B2.
Proof.
  intros m_orig Γ e B1 Hty.
  induction Hty; intros Hfn Hwf m_new B_tgt Hsub.
  - (* __embed: H : d_typing m Γ e B *)
    destruct m.
    + (* mode_ti *)
      simpl in Hsub |- *.
      apply d_typing_gen__sub with (B1 := B).
      * apply d_typing_gen__embed. exact H.
      * exact Hsub.
    + (* mode_tc: not in is_fn_n_ti *)
      inversion Hfn.
    + (* mode_fn m: function-side subsumption *)
      admit.
  - (* __sub: e synthesises B1 (mode_ti), then two gen-subtypings
       B1 ⊑ B0 (at m) and B0 ⊑ B_tgt (at the substituted mode) compose
       via B.3 transitivity into one B1 ⊑ B_tgt. *)
    eapply d_typing_gen__sub.
    + exact Hty.
    + eapply d_sub_gen_trans_btyp_nil; [ exact H | exact Hsub ].
Admitted.

(** D1, paper Lemma 3.1: ordinary general subsumption.  The paper's
    premise is a synthesized painting [syn{A}], so the native statement
    quantifies the plain type [A] and uses both paintings explicitly. *)
Theorem d_typing_general_subsumption : forall Γ e A B m,
    d_wf_denv Γ ->
    Γ ⊢[ mode_ti ] e ⦂ ptyp_to_btyp_syn A ->
    nil ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⊑ B ->
    Γ ⊢[ m ] e ⦂ B.
Proof.
Admitted.

Theorem d_typing_general_subsumption_via_gen : forall Γ e A B m,
    d_wf_denv Γ ->
    Γ ⊢[ mode_ti ] e ⦂ ptyp_to_btyp_syn A ->
    nil ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⊑ B ->
    Γ ⊢[ m ] e ⦂ B.
Proof.
  apply d_typing_general_subsumption.
Qed.
