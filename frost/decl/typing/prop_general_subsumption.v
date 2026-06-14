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
Require Import src.frost.decl.typing.prop_subsumption_aux.

Set Implicit Arguments.

(** Mode arithmetic for the [FN^n] generalisation: replace the trailing
    [mode_ti] of an [FN^n TI] mode with [m_new] (formerly in [def_gen.v],
    the only survivor of the deleted [gutyp]/[d_sub_gen] route). *)
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
  - (* d_sub__infer (m = ti): the whole arrow is matched by consistency.
       The arrow-consistency now carries [empty [=] Δ1 ∪ Δ2], so both halves
       sit at the empty tag context (recovered by [fsetdec]). *)
    dependent destruction H.                 (* d_consis__arrow *)
    match goal with                          (* is_styp (btyp_arrow _ _), any name *)
    | H : is_styp (btyp_arrow _ _) |- _ => dependent destruction H
    end.
    do 2 eexists; exists empty, empty.
    split; [ reflexivity | split ].
    + eapply d_consis_equiv; [ | eassumption ]. fsetdec.
    + simpl. apply d_sub__infer.
      * eapply d_consis_equiv; [ | eassumption ]. fsetdec.
      * assumption.
      * reflexivity.
  - (* d_sub__check (m = tc): excluded *) contradiction.
  - (* d_sub__forall_r (m = tc): excluded *) contradiction.
  - (* d_sub__arg (m = fn m'): argument by consistency, result subtyped *)
    do 4 eexists. split.
    + reflexivity.
    + split.
      * eassumption.
      * simpl. eassumption.
Qed.

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

(** For monomorphic [A] the two paintings coincide (no ∀ to colour). *)
Lemma mono_ptyp_inh_eq_syn : forall A,
    mono_ptyp A -> ptyp_to_btyp_inh A = ptyp_to_btyp_syn A.
Proof.
  induction 1; simpl; [ reflexivity | reflexivity | ].
  rewrite IHmono_ptyp1, IHmono_ptyp2. reflexivity.
Qed.

(** Consistency rigidity for monomorphic sources: a [mono] syn-source pins
    the bidirectional RHS to its syn painting (no tags, no colour freedom).
    Holds at ANY tag context — a [mono] source carries no [etag], so the
    arrow recursion threads through whatever [Δ] the split produced. *)
Lemma d_consis_mono_determines : forall Δ Γ A B,
    Δ ⨟ Γ ⊨ (ptyp_to_utyp_syn A) ≈ B ->
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
    empty ⨟ Γ ⊨ ph ≈ (utyp_to_btyp ph).
Proof.
  intros Γ ph Hwf. induction Hwf; intros Htt; simpl.
  - apply d_consis__unit. reflexivity.
  - apply d_consis__var; [ assumption | reflexivity ].
  - inversion Htt; subst.
    eapply d_consis__arrow; [ apply IHHwf1 | apply IHHwf2 | fsetdec ]; assumption.
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
    empty ⨟ Γ ⊨ C ≈ (utyp_to_btyp C).
Proof.
  intros Γ C Hwf. induction Hwf; simpl.
  - apply d_consis__unit. reflexivity.
  - apply d_consis__var; [ assumption | reflexivity ].
  - eapply d_consis__arrow; [ eassumption | eassumption | fsetdec ].
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
  - (* unit *) exists empty. apply d_consis__unit. reflexivity.
  - (* var *) exists empty. simpl. apply d_consis__var; [ assumption | reflexivity ].
  - (* arrow *)
    destruct IHd_consis1 as [Δ1' H1']. destruct IHd_consis2 as [Δ2' H2'].
    exists (Δ1' `union` Δ2'). simpl.
    eapply d_consis__arrow; [ eassumption | eassumption | reflexivity ].
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
    empty ⨟ Γ ⊨ T ≈ B.
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
  - apply d_consis__unit. assumption.
  - (* var: [X = X0] uses the base fact; [X <> X0] stays a variable. *)
    match goal with |- context [ if ?d then _ else _ ] => destruct d end.
    + eapply d_consis_equiv; [ | apply d_consis_ttyp_refl; assumption ]. fsetdec.
    + apply d_consis__var; [ analyze_binds H; auto | assumption ].
  - eapply d_consis__arrow;
      [ eapply IHd_consis1; eauto | eapply IHd_consis2; eauto | assumption ].
  - eapply d_consis__forall_inh_tagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton X0).
    + intros Z HZ.
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
    + assumption.
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

(** Against an INHERITED ([is_ityp]) RHS, every ε-tag of the source is solved
    ([ForallInh]), so the source's full tag set sits inside the consistency
    context.  This is the lower bound the [forall_l] reconstruct needs: the
    instantiation tags [Δ'] of [ph] survive into the output *because* [ph]
    occurs in the subject and the RHS is inherited.  ([forall_syn*] cases are
    vacuous: their RHS [btyp_all_syn] is not [is_ityp]; [forall_inh_untagged]
    is vacuous: its source [utyp_all_syn] has no [d_tags].) *)
Lemma d_consis_tags_subset_ityp : forall Δ Γ C B Δc,
    Δ ⨟ Γ ⊨ C ≈ B ->
    is_ityp B ->
    d_tags Δc C ->
    Δc [<=] Δ.
Proof.
  intros Δ Γ C B Δc Hcons. revert Δc. induction Hcons; intros Δc Hity Htags.
  - dependent destruction Htags. fsetdec.
  - dependent destruction Htags. fsetdec.
  - dependent destruction Hity. dependent destruction Htags.
    match goal with
    | IH1 : forall _, is_ityp ?B1 -> _, IH2 : forall _, is_ityp ?B2 -> _ |- _ =>
        specialize (IH1 _ ltac:(assumption) ltac:(eassumption));
        specialize (IH2 _ ltac:(assumption) ltac:(eassumption))
    end. fsetdec.
  - (* forall_inh_tagged: source etag, RHS inh — the tag-solving case. *)
    dependent destruction Htags.
    dependent destruction Hity.
    pick fresh X.
    match goal with
    | IH : forall _, _ `notin` _ -> _ |- _ =>
        assert (Hsub0 : _ [<=] _) by
          (eapply (IH X); [ fsetdec
                          | match goal with H : forall _, _ -> is_ityp _ |- _ => apply H; fsetdec end
                          | match goal with H : forall _, _ -> d_tags _ _ |- _ => apply H; fsetdec end ])
    end.
    clear - H1 H5 Hsub0; fsetdec.
  - dependent destruction Htags.   (* forall_inh_untagged: utyp_all_syn has no d_tags *)
  - dependent destruction Hity.    (* forall_syn_tagged: btyp_all_syn not is_ityp *)
  - dependent destruction Hity.    (* forall_syn: btyp_all_syn not is_ityp *)
Qed.


(** Consistency-Subtyping Transitivity (paper, syntax-directed.tex:152):
    a consistency into a synthesised type composes with a subtyping out of
    it.  The synthesised middle is carried as a [btyp] [B_A] with [is_syn],
    bridged to the subtyping LHS via [btyp_to_utyp_syn] (the same convention
    as [d_consis_compose_syn_nil]).  [is_syn] = [is_styp] up to
    [is_styp_is_syn]. *)
(** Paper CST (syntax-directed.tex:152), with the load-bearing [Ψ ⊆ Ψ']
    invariant the paper's "straightforward induction" silently needs: the
    subtyping context [Δb] is GENERAL (not [·]) — that is the inductive
    generalisation that lets the [forall_l] IH fire on its non-empty
    premise — and the conclusion context contains it ([Δb ⊆ Δ]).  The
    paper's [·]-statement is the [Δb = ∅] corollary. *)
Lemma d_consis_sub_trans : forall M Δb Γ C B,
    Δb ⨟ Γ ⊢[ M ] C ⊑ B ->
    forall B_A T Δt,
      C = btyp_to_utyp_syn B_A ->
      is_syn B_A ->
      Δt ⨟ Γ ⊨ T ≈ B_A ->
      exists Δ, Δb [<=] Δ /\ Δ ⨟ Γ ⊢[ M ] T ⊑ B.
Proof.
  intros M Δb Γ C B Hsub.
  induction Hsub; intros B_A T Δt Heq Hsyn Hcons.
  - (* d_sub__infer (ti): Δb [=] ∅; compose collapses to ∅. *)
    subst C. exists empty. split; [ fsetdec | ].
    apply d_sub__infer.
    + eapply d_consis_compose_syn_nil_l.
      * exact Hsyn.
      * apply is_styp_is_syn. eassumption.
      * exact Hcons.
      * eassumption.
    + assumption.
    + reflexivity.
  - (* d_sub__check (tc): the composed context [Δc] ⊇ [Δt ∪ Δb] ⊇ [Δb]. *)
    subst C.
    assert (HgT : guarded_utyp T).
    { eapply d_consis_guarded_lhs.
      - eassumption.
      - rewrite utyp_to_btyp_btyp_to_utyp_syn by assumption. exact Hcons. }
    destruct (@d_consis_compose_syn _ _ _ _ B_A _
                ltac:(eassumption) ltac:(exact Hcons) ltac:(eassumption))
      as [Δc [Hincl Hc]].
    exists Δc. split; [ fsetdec | apply d_sub__check; assumption ].
  - (* d_sub__forall_r (tc): context unchanged; IH carries the bound. *)
    subst C.
    pick fresh X0 for (L `union` dom Γ `union` ftvar_in_utyp T
                       `union` ftvar_in_btyp B `union` ftvar_in_btyp B_A).
    destruct (H0 X0 ltac:(fsetdec) B_A T Δt eq_refl Hsyn
                ltac:(apply d_consis_weakening_head; exact Hcons)) as [Δ0 [HΔbound HΔ0]].
    exists Δ0. split; [ exact HΔbound | ].
    apply d_sub__forall_r with
      (L := L `union` dom Γ `union` ftvar_in_utyp T `union` ftvar_in_btyp B
            `union` singleton X0).
    intros X HX.
    rewrite (subst_btyp_in_btyp_intro X0) by fsetdec.
    rewrite <- (subst_utyp_in_utyp_fresh_eq T (utyp_var_f X) X0) by fsetdec.
    apply (@d_sub_rename _ _ _ _ _ HΔ0 nil Γ X0 X); [ reflexivity | simpl; fsetdec ].
  - (* d_sub__arg (fn m'): arg [Δc1 ⊇ Δ1], result [Δc2 ⊇ Δ2], so
       [Δc1 ∪ Δc2 ⊇ Δ1 ∪ Δ2 = Δb]. *)
    destruct B_A as [ | n | X | B_A1 B_A2 | B_A0 | B_A0 ];
      simpl in Heq; try discriminate.
    injection Heq as HeqC1 HeqC2. subst.
    dependent destruction Hsyn.                 (* is_syn B_A1, is_syn B_A2 *)
    dependent destruction Hcons.                (* T = utyp_arrow T1 T2 *)
    destruct (@d_consis_compose_syn _ _ _ _ B_A1 _
                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption))
      as [Δc1 [Hincl1 Hc1]].
    destruct (IHHsub B_A2 _ _ eq_refl ltac:(eassumption) ltac:(eassumption))
      as [Δc2 [HΔbound2 Hres]].
    exists (Δc1 `union` Δc2). split; [ fsetdec | ].
    eapply d_sub__arg; [ eassumption | eassumption | reflexivity ].
  - (* d_sub__forall_l_tagged: LHS [utyp_all_etag] cannot be a
       [btyp_to_utyp_syn] image (no etag in a synthesised type). *)
    destruct B_A as [ | n | X | B_A1 B_A2 | B_A0 | B_A0 ];
      simpl in Heq; discriminate.
  - (* d_sub__forall_l_untagged: the syn-form IH demands the subject be a
       [btyp_to_utyp_syn] image, which [open (paint B_A0) ph] is not for
       tagged [ph] (confirmed by inverting Hcons: everything on the
       consistency side is supplied, the equation [open C ph =
       btyp_to_utyp_syn B_A'] is the lone wall, forcing [ph = paint(erase
       ph)]).  The erase-form generalisation (this lemma's [_mid] variant)
       fixes the IH shape; tracked there. *)
    admit.
Admitted.

(** [utyp_tag_refines T Cmid]: [T] and [Cmid] have the same shape, and at
    every quantifier where [Cmid] is ε-tagged [T] carries the SAME tag, while
    [T] may carry EXTRA tags where [Cmid] is synthesised.  This captures the
    "T and A have the same shape modulo T may have extra tags" of the paper's
    CST (syntax-directed.tex), and — crucially — is closed under the shared-ph
    instantiation that [forall_l] performs (both sides gain the same ph).  It
    is the linearity-free replacement for the [d_tags] lower-bound chain. *)
Inductive utyp_tag_refines : utyp -> utyp -> Prop :=
| utr_unit  : utyp_tag_refines utyp_unit utyp_unit
| utr_var_b : forall n, utyp_tag_refines (utyp_var_b n) (utyp_var_b n)
| utr_var_f : forall X, utyp_tag_refines (utyp_var_f X) (utyp_var_f X)
| utr_arrow : forall T1 T2 C1 C2,
    utyp_tag_refines T1 C1 -> utyp_tag_refines T2 C2 ->
    utyp_tag_refines (utyp_arrow T1 T2) (utyp_arrow C1 C2)
| utr_etag_etag : forall ε T0 C0,
    utyp_tag_refines T0 C0 ->
    utyp_tag_refines (utyp_all_etag ε T0) (utyp_all_etag ε C0)
| utr_etag_syn : forall ε T0 C0,
    utyp_tag_refines T0 C0 ->
    utyp_tag_refines (utyp_all_etag ε T0) (utyp_all_syn C0)
| utr_syn_syn : forall T0 C0,
    utyp_tag_refines T0 C0 ->
    utyp_tag_refines (utyp_all_syn T0) (utyp_all_syn C0).

#[local] Hint Constructors utyp_tag_refines : core.

Lemma utyp_tag_refines_refl : forall T, utyp_tag_refines T T.
Proof. induction T; auto. Qed.

Lemma utyp_tag_refines_open_rec : forall T C,
    utyp_tag_refines T C ->
    forall k Y,
      utyp_tag_refines (open_utyp_wrt_utyp_rec k (utyp_var_f Y) T)
                       (open_utyp_wrt_utyp_rec k (utyp_var_f Y) C).
Proof.
  induction 1; intros k Y; simpl; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; auto.
Qed.

Lemma utyp_tag_refines_open : forall T C X,
    utyp_tag_refines T C ->
    utyp_tag_refines (open_utyp_wrt_utyp T (utyp_var_f X))
                     (open_utyp_wrt_utyp C (utyp_var_f X)).
Proof.
  intros T C X H. unfold open_utyp_wrt_utyp. apply utyp_tag_refines_open_rec; auto.
Qed.

(** Opening with a GENERAL [U] (the [ph] instantiation): both sides gain the
    SAME [U], so refinement is preserved (the bound variable becomes [U] on
    both, [refl]). *)
Lemma utyp_tag_refines_open_rec_gen : forall T C,
    utyp_tag_refines T C ->
    forall k U,
      utyp_tag_refines (open_utyp_wrt_utyp_rec k U T) (open_utyp_wrt_utyp_rec k U C).
Proof.
  induction 1; intros k U; simpl; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; auto using utyp_tag_refines_refl.
Qed.

Lemma utyp_tag_refines_open_gen : forall T C U,
    utyp_tag_refines T C ->
    utyp_tag_refines (open_utyp_wrt_utyp T U) (open_utyp_wrt_utyp C U).
Proof.
  intros T C U H. unfold open_utyp_wrt_utyp. apply utyp_tag_refines_open_rec_gen; auto.
Qed.

(** Closing (de Bruijn abstraction) preserves refinement — the inverse
    direction of opening, used to recover structural refinement of ∀ bodies
    from the cofinite hypothesis. *)
Lemma utyp_tag_refines_close_rec_pres : forall T C,
    utyp_tag_refines T C ->
    forall k Y,
      utyp_tag_refines (close_utyp_wrt_utyp_rec k Y T)
                       (close_utyp_wrt_utyp_rec k Y C).
Proof.
  induction 1; intros k Y; simpl; auto using utyp_tag_refines_refl.
Qed.

Lemma utyp_tag_refines_close : forall C D Y k,
    Y `notin` ftvar_in_utyp C ->
    Y `notin` ftvar_in_utyp D ->
    utyp_tag_refines (open_utyp_wrt_utyp_rec k (utyp_var_f Y) C)
                     (open_utyp_wrt_utyp_rec k (utyp_var_f Y) D) ->
    utyp_tag_refines C D.
Proof.
  intros C D Y k HC HD H.
  pose proof (@utyp_tag_refines_close_rec_pres _ _ H k Y) as H'.
  rewrite !close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec in H' by assumption.
  exact H'.
Qed.

(** ∀-body helper: recover structural refinement of [C] against [paint B]
    from the cofinite consistency body, via [close] + [paint]-opening. *)
Lemma consis_refines_paint_body : forall L C B,
    (forall X, X `notin` L ->
       utyp_tag_refines (open_utyp_wrt_utyp C (utyp_var_f X))
                        (btyp_to_utyp_syn (open_btyp_wrt_btyp B (btyp_var_f X)))) ->
    utyp_tag_refines C (btyp_to_utyp_syn B).
Proof.
  intros L C B H.
  pick fresh X for (L `union` ftvar_in_utyp C `union` ftvar_in_btyp B).
  apply (@utyp_tag_refines_close C (btyp_to_utyp_syn B) X 0).
  - fsetdec.
  - rewrite ftvar_btyp_to_utyp_syn; fsetdec.
  - change (open_utyp_wrt_utyp_rec 0 (utyp_var_f X) C)
      with (open_utyp_wrt_utyp C (utyp_var_f X)).
    change (open_utyp_wrt_utyp_rec 0 (utyp_var_f X) (btyp_to_utyp_syn B))
      with (open_utyp_wrt_utyp (btyp_to_utyp_syn B) (utyp_var_f X)).
    specialize (H X ltac:(fsetdec)).
    rewrite btyp_to_utyp_syn_open in H. exact H.
Qed.

(** The unresolved source of a consistency refines the syn-painting of the
    bidirectional target: same shape, painting fully syn (tag-free), so [T]'s
    tags trivially dominate. *)
Lemma consis_refines_paint : forall Δ Γ T B_A,
    Δ ⨟ Γ ⊨ T ≈ B_A ->
    utyp_tag_refines T (btyp_to_utyp_syn B_A).
Proof.
  intros Δ Γ T B_A H. induction H; simpl.
  - apply utr_unit.
  - apply utr_var_f.
  - apply utr_arrow; assumption.
  - apply utr_etag_syn. eapply consis_refines_paint_body; eauto.
  - apply utr_syn_syn.  eapply consis_refines_paint_body; eauto.
  - apply utr_etag_syn. eapply consis_refines_paint_body; eauto.
  - apply utr_syn_syn.  eapply consis_refines_paint_body; eauto.
Qed.

(** [refines] makes [compose_tags] monotone: [Cmid]'s composed tags are a
    subset of [T]'s (extra tags only grow the result). *)
Lemma utyp_tag_refines_compose_mono : forall T C,
    utyp_tag_refines T C ->
    forall B, compose_tags C B [<=] compose_tags T B.
Proof.
  induction 1; intros B0; destruct B0; simpl; try fsetdec;
    try (specialize (IHutyp_tag_refines1 B0_1); specialize (IHutyp_tag_refines2 B0_2); fsetdec);
    specialize (IHutyp_tag_refines B0); fsetdec.
Qed.

(** The consistency context is bounded above by [compose_tags] — the
    canonical (linearity-free) tag witness.  This is the lower link of the
    bound chain [Δ2 ⊆ compose_tags Cmid B]. *)
Lemma d_consis_ctx_subset_compose : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    Δ [<=] compose_tags C B.
Proof.
  intros Δ Γ C B H. induction H; simpl.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - pick fresh X. match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
      specialize (IH X ltac:(fsetdec)) end.
    rewrite compose_tags_open in *. fsetdec.
  - pick fresh X. match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
      specialize (IH X ltac:(fsetdec)) end.
    rewrite compose_tags_open in *. fsetdec.
  - pick fresh X. match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
      specialize (IH X ltac:(fsetdec)) end.
    rewrite compose_tags_open in *. fsetdec.
  - pick fresh X. match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
      specialize (IH X ltac:(fsetdec)) end.
    rewrite compose_tags_open in *. fsetdec.
Qed.

(** Source-swap with the [compose_tags] witness: if [T] refines [Cmid] (same
    shape, tags ⊇) and [Cmid ≈ B], then [T ≈ B] holds at the canonical
    context [compose_tags T B].  The witness is UNIFORM (opening-invariant via
    [compose_tags_open]), so the ∀ cases avoid the cofinite per-X existential.
    No [d_tags], no linearity. *)
Lemma refines_consis_swap : forall Δ Γ Cmid B,
    Δ ⨟ Γ ⊨ Cmid ≈ B ->
    forall T, utyp_tag_refines T Cmid ->
      (compose_tags T B) ⨟ Γ ⊨ T ≈ B.
Proof.
  intros Δ Γ Cmid B H. induction H; intros T Href.
  - inversion Href; subst. simpl. apply d_consis__unit. reflexivity.
  - inversion Href; subst. simpl. apply d_consis__var; [ assumption | reflexivity ].
  - inversion Href; subst. simpl.
    eapply d_consis__arrow; [ apply IHd_consis1 | apply IHd_consis2 | reflexivity ]; assumption.
  - (* forall_inh_tagged: Cmid = utyp_all_etag ε C, B = btyp_all_inh; T = utyp_all_etag ε T0 *)
    inversion Href; subst. simpl.
    eapply d_consis__forall_inh_tagged with (L := L) (Δ0 := compose_tags T0 B); [ | reflexivity ].
    intros X HX.
    match goal with |- compose_tags ?Tb ?Bb ⨟ _ ⊨ _ ≈ _ =>
      rewrite <- (compose_tags_open Tb Bb X X) end.
    apply (H0 X HX). apply utyp_tag_refines_open. assumption.
  - (* forall_inh_untagged: Cmid = utyp_all_syn C, B = btyp_all_inh; T tagged or syn *)
    inversion Href; subst; simpl.
    + (* T = utyp_all_etag ε T0 (extra tag) *)
      eapply d_consis__forall_inh_tagged with (L := L) (Δ0 := compose_tags T0 B); [ | reflexivity ].
      intros X HX.
      match goal with |- compose_tags ?Tb ?Bb ⨟ _ ⊨ _ ≈ _ =>
        rewrite <- (compose_tags_open Tb Bb X X) end.
      apply (H0 X HX). apply utyp_tag_refines_open. assumption.
    + (* T = utyp_all_syn T0 *)
      apply d_consis__forall_inh_untagged with (L := L).
      intros X HX.
      match goal with |- compose_tags ?Tb ?Bb ⨟ _ ⊨ _ ≈ _ =>
        rewrite <- (compose_tags_open Tb Bb X X) end.
      apply (H0 X HX). apply utyp_tag_refines_open. assumption.
  - (* forall_syn_tagged: Cmid = utyp_all_etag ε C, B = btyp_all_syn; T = utyp_all_etag ε T0 *)
    inversion Href; subst. simpl.
    apply d_consis__forall_syn_tagged with (L := L).
    intros X HX.
    match goal with |- compose_tags ?Tb ?Bb ⨟ _ ⊨ _ ≈ _ =>
      rewrite <- (compose_tags_open Tb Bb X X) end.
    apply (H0 X HX). apply utyp_tag_refines_open. assumption.
  - (* forall_syn: Cmid = utyp_all_syn C, B = btyp_all_syn; T tagged or syn *)
    inversion Href; subst; simpl.
    + (* T = utyp_all_etag ε T0 *)
      apply d_consis__forall_syn_tagged with (L := L).
      intros X HX.
      match goal with |- compose_tags ?Tb ?Bb ⨟ _ ⊨ _ ≈ _ =>
        rewrite <- (compose_tags_open Tb Bb X X) end.
      apply (H0 X HX). apply utyp_tag_refines_open. assumption.
    + (* T = utyp_all_syn T0 *)
      apply d_consis__forall_syn with (L := L).
      intros X HX.
      match goal with |- compose_tags ?Tb ?Bb ⨟ _ ⊨ _ ≈ _ =>
        rewrite <- (compose_tags_open Tb Bb X X) end.
      apply (H0 X HX). apply utyp_tag_refines_open. assumption.
Qed.

(** Reformulated CST over a GENERAL middle [Cmid] (paper-faithful: the syn
    middle is not closed under tagged instantiation).  infer/check/arg close
    via the proven bridges; forall_l is the concrete attempt with the
    existing list-typed tag context. *)
Lemma d_consis_sub_trans_mid : forall M Δ2 Γ Cmid B,
    Δ2 ⨟ Γ ⊢[ M ] Cmid ⊑ B ->
    forall Δ1 T,
      Δ1 ⨟ Γ ⊨ T ≈ (utyp_to_btyp Cmid) ->
      utyp_tag_refines T Cmid ->
      exists Δ, Δ2 [<=] Δ /\ Δ ⨟ Γ ⊢[ M ] T ⊑ B.
Proof.
  intros M Δ2 Γ Cmid B Hsub.
  induction Hsub; intros Δ0 T Hcons Href.
  - (* infer (ti): Δ2 [=] ∅. *)
    exists empty. split; [ fsetdec | ].
    apply d_sub__infer.
    + apply (d_consis_trans_mid_nil (Cmid := C) (Δ1 := Δ0) (Δ2 := empty)).
      * exact (d_consis_lc_utyp H).
      * apply is_styp_is_syn; exact H0.
      * exact Hcons.
      * exact H.
    + exact H0.
    + reflexivity.
  - (* check (tc): output context is the canonical witness [compose_tags T B];
       bound Δ2 ⊆ it via the tag chain, output consistency via the source-swap. *)
    assert (HgT : guarded_utyp T) by (eapply d_consis_guarded_lhs; [ exact H | exact Hcons ]).
    exists (compose_tags T B). split.
    + pose proof (d_consis_ctx_subset_compose H1) as Hc1.
      pose proof (utyp_tag_refines_compose_mono Href B) as Hc2. fsetdec.
    + apply d_sub__check;
        [ exact HgT | exact H0 | apply (refines_consis_swap H1 Href) | exact H2 ].
  - (* forall_r (tc): IH carries the bound; refinement unchanged. *)
    pick fresh X0 for (L `union` dom Γ `union` ftvar_in_utyp T
                       `union` ftvar_in_btyp B).
    destruct (H0 X0 ltac:(fsetdec) Δ0 T
                ltac:(apply d_consis_weakening_head; exact Hcons) Href) as [Δ' [Hbnd HΔ']].
    exists Δ'. split; [ exact Hbnd | ].
    apply d_sub__forall_r with
      (L := L `union` dom Γ `union` ftvar_in_utyp T `union` ftvar_in_btyp B
            `union` singleton X0).
    intros X HX.
    rewrite (subst_btyp_in_btyp_intro X0) by fsetdec.
    rewrite <- (subst_utyp_in_utyp_fresh_eq T (utyp_var_f X) X0) by fsetdec.
    apply (@d_sub_rename _ _ _ _ _ HΔ' nil Γ X0 X); [ reflexivity | simpl; fsetdec ].
  - (* arg (fn m): domain by source-swap, result by IH; bound by chain + IH. *)
    simpl in Hcons. dependent destruction Hcons.
    dependent destruction Href.
    destruct (IHHsub _ _ ltac:(eassumption) ltac:(eassumption)) as [Δc2 [Hbnd2 Hres]].
    match goal with Hr : utyp_tag_refines ?t C1 |- _ =>
      exists (compose_tags t B1 `union` Δc2) end. split.
    + pose proof (d_consis_ctx_subset_compose H) as Hc1.
      match goal with Hr : utyp_tag_refines _ C1 |- _ =>
        pose proof (utyp_tag_refines_compose_mono Hr B1) as Hc2 end.
      fsetdec.
    + eapply d_sub__arg;
        [ match goal with Hr : utyp_tag_refines _ C1 |- _ =>
            apply (refines_consis_swap H Hr) end
        | exact Hres | reflexivity ].
  - (* forall_l_tagged: subtyping source is utyp_all_etag ε C; Href forces
       T = utyp_all_etag ε C0 (utr_etag_etag); reconstruct via forall_l_tagged. *)
    dependent destruction Href.
    simpl in Hcons. dependent destruction Hcons.
    pick fresh X for (L `union` dom Γ `union` ftvar_in_utyp T0
                      `union` ftvar_in_utyp C `union` ftvar_in_btyp B
                      `union` Δ `union` Δ').
    pose proof (@d_consis_subst_tvar _ _ _ _ (H4 X ltac:(fsetdec)) nil Γ X ph
                  eq_refl ltac:(simpl; exact H2) H3) as Hinst.
    rewrite <- (subst_utyp_in_utyp_intro X T0 ph) in Hinst by fsetdec.
    rewrite <- (subst_btyp_in_btyp_intro X (utyp_to_btyp C) (utyp_to_btyp ph)) in Hinst
      by (rewrite ftvar_utyp_to_btyp; fsetdec).
    rewrite <- utyp_to_btyp_open in Hinst.
    simpl in Hinst.
    destruct (IHHsub _ _ Hinst
                (@utyp_tag_refines_open_gen _ _ ph ltac:(eassumption)))
      as [Δ_IH [Hbnd HΔ_IH]].
    exists (AtomSetImpl.diff Δ_IH Δ'). split.
    + fsetdec.
    + eapply d_sub__forall_l_tagged with (Δ' := Δ').
      * exact H.
      * fsetdec.
      * exact H1.
      * exact H2.
      * exact H3.
      * eapply d_sub_equiv; [ | exact HΔ_IH ]. fsetdec.
  - (* forall_l_untagged: with Δ2 ⊆ Δ in the IH, the residual Δ' ⊆ Δ_IH FOLLOWS
       from (Δ ∪ Δ') ⊆ Δ_IH; refinement threaded by [open_gen]. *)
    simpl in Hcons.
    dependent destruction Hcons.
    + (* T = utyp_all_etag ε C0 (matched syn): mirror, reconstruct via forall_l_tagged *)
      dependent destruction Href.
      pick fresh X for (L `union` dom Γ `union` ftvar_in_utyp C0
                        `union` ftvar_in_utyp C `union` ftvar_in_btyp B
                        `union` Δ0 `union` Δ `union` Δ').
      pose proof (@d_consis_subst_tvar _ _ _ _ (H4 X ltac:(fsetdec)) nil Γ X ph
                    eq_refl ltac:(simpl; exact H2) H3) as Hinst.
      rewrite <- (subst_utyp_in_utyp_intro X C0 ph) in Hinst by fsetdec.
      rewrite <- (subst_btyp_in_btyp_intro X (utyp_to_btyp C) (utyp_to_btyp ph)) in Hinst
        by (rewrite ftvar_utyp_to_btyp; fsetdec).
      rewrite <- utyp_to_btyp_open in Hinst.
      simpl in Hinst.
      destruct (IHHsub _ _ Hinst
                  (@utyp_tag_refines_open_gen _ _ ph ltac:(eassumption)))
        as [Δ_IH [Hbnd HΔ_IH]].
      exists (AtomSetImpl.diff Δ_IH Δ'). split.
      * fsetdec.
      * eapply d_sub__forall_l_tagged with (Δ' := Δ').
        -- exact H.
        -- fsetdec.
        -- exact H1.
        -- exact H2.
        -- exact H3.
        -- eapply d_sub_equiv; [ | exact HΔ_IH ]. fsetdec.
    + (* T = utyp_all_syn C0 *)
      dependent destruction Href.
      pick fresh X for (L `union` dom Γ `union` ftvar_in_utyp C0
                        `union` ftvar_in_utyp C `union` ftvar_in_btyp B
                        `union` Δ0 `union` Δ `union` Δ').
      pose proof (@d_consis_subst_tvar _ _ _ _ (H4 X ltac:(fsetdec)) nil Γ X ph
                    eq_refl ltac:(simpl; exact H2) H3) as Hinst.
      rewrite <- (subst_utyp_in_utyp_intro X C0 ph) in Hinst by fsetdec.
      rewrite <- (subst_btyp_in_btyp_intro X (utyp_to_btyp C) (utyp_to_btyp ph)) in Hinst
        by (rewrite ftvar_utyp_to_btyp; fsetdec).
      rewrite <- utyp_to_btyp_open in Hinst.
      simpl in Hinst.
      destruct (IHHsub _ _ Hinst
                  (@utyp_tag_refines_open_gen _ _ ph ltac:(eassumption)))
        as [Δ_IH [Hbnd HΔ_IH]].
      exists (AtomSetImpl.diff Δ_IH Δ'). split.
      * fsetdec.
      * eapply d_sub__forall_l_untagged with (Δ' := Δ').
        -- exact H.
        -- fsetdec.
        -- exact H1.
        -- exact H2.
        -- exact H3.
        -- eapply d_sub_equiv; [ | exact HΔ_IH ]. fsetdec.
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
    the paper's [Ψ ⊆ Ψ'] invariant ([Δ [<=] Δ']) — the output context only
    *grows*.  That invariant is what the [forall_l] cases need: the IH gives
    [(Δ ∪ Δ') ⊆ Δr], so the instantiation tags [Δ'] are inside [Δr] and the
    reconstruct picks the outer context [Δr ∖ Δ'] — set difference makes the
    rule's freshness side condition ([Δ' ∩ outer = ∅]) automatic and the
    premise context [=]-equal to [Δr] (the paper's "Ψ1 still disjoint from
    Ψ'" line, discharged here by [fsetdec]).  [check]/[forall_r] are
    excluded by [is_fn_n]. *)
Lemma d_sub_trans_spine : forall m1 Δ Γ T Bfull,
    Δ ⨟ Γ ⊢[ m1 ] T ⊑ Bfull ->
    forall n A M B Bres,
      is_fn_n n m1 ->
      btyp_spine n Bfull A B Bres ->
      empty ⨟ Γ ⊢[ M ] (btyp_to_utyp_syn A) ⊑ B ->
      exists Δ', Δ [<=] Δ' /\ Δ' ⨟ Γ ⊢[ mode_fn_n_subst m1 M ] T ⊑ Bres.
Proof.
  intros m1 Δ Γ T Bfull Hsub.
  induction Hsub; intros n A0 M0 B0 Bres Hfn Hspine Htail.
  - (* d_sub__infer (ti): n = 0 forces the tail; compose by CST — now the
       fully-closed erase-form [d_consis_sub_trans_mid].  Middle is
       [btyp_to_utyp_syn A0]; its erasure is [A0] (is_syn), matching the infer
       consistency, and [T] refines it by [consis_refines_paint]. *)
    inversion Hfn; subst.
    dependent destruction Hspine.
    edestruct (d_consis_sub_trans_mid Htail) as [Δ' [_ HΔ']].
    + rewrite utyp_to_btyp_btyp_to_utyp_syn by (apply is_styp_is_syn; eassumption).
      eassumption.
    + eapply consis_refines_paint; eassumption.
    + exists Δ'. split; [ fsetdec | simpl; exact HΔ' ].
  - (* d_sub__check (tc): excluded, [is_fn_n n mode_tc] is uninhabited. *)
    inversion Hfn.
  - (* d_sub__forall_r (tc): excluded. *)
    inversion Hfn.
  - (* d_sub__arg (fn m'): peel one arrow, recurse on the result spine. *)
    inversion Hfn; subst.
    dependent destruction Hspine.
    edestruct IHHsub as [Δ2' [Hb2 Hres]];
      [ eassumption | eassumption | eassumption | ].
    exists (Δ1 `union` Δ2'). split.
    + fsetdec.
    + simpl. eapply d_sub__arg; [ eassumption | exact Hres | reflexivity ].
  - (* d_sub__forall_l_tagged: subset invariant + set difference. *)
    edestruct IHHsub as [Δr [Hb Hr]];
      [ eassumption | eassumption | eassumption | ].
    exists (AtomSetImpl.diff Δr Δ'). split.
    + fsetdec.
    + eapply d_sub__forall_l_tagged with (Δ' := Δ').
      * destruct m as [ | | m']; simpl;
          [ exfalso; apply H; reflexivity | discriminate | discriminate ].
      * fsetdec.
      * eassumption.
      * eassumption.
      * eassumption.
      * eapply d_sub_equiv; [ | exact Hr ]. fsetdec.
  - (* d_sub__forall_l_untagged: as above. *)
    edestruct IHHsub as [Δr [Hb Hr]];
      [ eassumption | eassumption | eassumption | ].
    exists (AtomSetImpl.diff Δr Δ'). split.
    + fsetdec.
    + eapply d_sub__forall_l_untagged with (Δ' := Δ').
      * destruct m as [ | | m']; simpl;
          [ exfalso; apply H; reflexivity | discriminate | discriminate ].
      * fsetdec.
      * eassumption.
      * eassumption.
      * eassumption.
      * eapply d_sub_equiv; [ | exact Hr ]. fsetdec.
Qed.

(** Generalised General Subsumption (paper, syntax-directed.tex:287): the
    headline.  Over PLAIN typing; subtypes only the synthesised result of
    the [FN^n] spine, keeping the arguments fixed.  D1 (general subsumption)
    is the [n = 0] corollary. *)
Lemma d_typing_general_subsumption_spine : forall m1 Γ e Bfull,
    Γ ⊢[ m1 ] e ⦂ Bfull ->
    forall Γl Γw Γb,
      Γ = Γl ++ Γb ->
      forall n A M B Bres,
        is_fn_n n m1 ->
        btyp_spine n Bfull A B Bres ->
        empty ⨟ (Γl ++ Γw ++ Γb) ⊢[ M ] (btyp_to_utyp_syn A) ⊑ B ->
        (Γl ++ Γw ++ Γb) ⊢[ mode_fn_n_subst m1 M ] e ⦂ Bres.
Proof.
  intros m1 Γ e Bfull Hty.
  induction Hty; intros Γl Γw Γb Heq n A0 M0 B0 Bres Hfn Hspine Htail.
  - (* unit *)
    inversion Hfn; subst. dependent destruction Hspine. simpl.
    apply d_typing__sub with (B1 := btyp_unit).
    + apply is_base_term__unit.
    + apply d_typing__unit.
    + rewrite ptyp_to_utyp_syn_btyp_to_ptyp. exact Htail.
  - (* var: binds preserved under the inserted [Γw]. *)
    inversion Hfn; subst. dependent destruction Hspine. simpl. subst.
    apply d_typing__sub with (B1 := ptyp_to_btyp_syn A).
    + apply is_base_term__var.
    + apply d_typing__var. analyze_binds H.
    + rewrite ptyp_to_utyp_syn_btyp_to_ptyp. exact Htail.
  - (* anno: the checked subderivation is weakened. *)
    inversion Hfn; subst. dependent destruction Hspine. simpl. subst.
    apply d_typing__sub with (B1 := ptyp_to_btyp_syn A).
    + apply is_base_term__anno.
    + apply d_typing__anno.
      apply d_typing_weakening with (Γ1 := Γl) (Γ2 := Γw) (Γ3 := Γb). eassumption.
    + rewrite ptyp_to_utyp_syn_btyp_to_ptyp. exact Htail.
  - (* sub: needs the syn-LHS ⇒ empty-context fact.  Deferred. *)
    admit.
  - (* freeze (tc): excluded. *)
    inversion Hfn.
  - (* forall (tc): excluded. *)
    inversion Hfn.
  - (* abs: split on the spine. *)
    dependent destruction Hspine.
    + (* __tail (n=0): Function-Subtyping + generalisation.  Deferred. *)
      admit.
    + (* __arrow (n>0): keep [inh A] fixed, recurse on the body via the
         context-general IH (insert [Γw] after the binder [x:A]). *)
      dependent destruction Hfn. simpl. subst.
      apply d_typing__abs with (L := L `union` dom (Γl ++ Γb)) (A := A).
      * apply d_wf_ptyp_weakening. assumption.
      * intros x Hx.
        eapply (H1 x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γl) Γw Γb eq_refl).
        -- eassumption.
        -- eassumption.
        -- apply d_sub_weakening_head with (Γ' := (x ~ dbind_typ A)). exact Htail.
  - (* abs_anno: as abs, with the bidirectional [Barg] kept fixed. *)
    dependent destruction Hspine.
    + (* __tail (n=0): Function-Subtyping + generalisation.  Deferred. *)
      admit.
    + (* __arrow (n>0). *)
      dependent destruction Hfn. simpl. subst Γ.
      apply d_typing__abs_anno with (L := L `union` dom (Γl ++ Γb)) (A := A) (Barg := Barg).
      * apply d_wf_ptyp_weakening. assumption.
      * exact H0.
      * intros x Hx.
        eapply (H2 x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γl) Γw Γb eq_refl).
        -- eassumption.
        -- eassumption.
        -- apply d_sub_weakening_head with (Γ' := (x ~ dbind_typ A)). exact Htail.
  - (* app: thread the spine through [e1] via the IH; weaken the side
       premises ([d_pat], [d_refine_syn], [e2]) by the inserted [Γw]. *)
    subst Γ.
    eapply d_typing__app.
    + exact H.
    + apply d_pat_weakening with (Γ1 := Γl) (Γ2 := Γw) (Γ3 := Γb). exact H0.
    + apply d_refine_syn_weakening with (Γ1 := Γl) (Γ2 := Γw) (Γ3 := Γb). exact H1.
    + eapply IHHty1 with (Γl := Γl) (Γw := Γw) (Γb := Γb).
      * reflexivity.
      * apply is_fn_n__fn. exact Hfn.
      * apply btyp_spine__arrow. exact Hspine.
      * exact Htail.
    + apply d_typing_weakening with (Γ1 := Γl) (Γ2 := Γw) (Γ3 := Γb). exact Hty2.
Admitted.

(** D1, paper Lemma 3.1: ordinary general subsumption.  The paper's
    premise is a synthesized painting [syn{A}], so the native statement
    quantifies the plain type [A] and uses both paintings explicitly. *)
Theorem d_typing_general_subsumption : forall Γ e A B m,
    d_wf_denv Γ ->
    Γ ⊢[ mode_ti ] e ⦂ ptyp_to_btyp_syn A ->
    empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⊑ B ->
    Γ ⊢[ m ] e ⦂ B.
Proof.
Admitted.

Theorem d_typing_general_subsumption_via_gen : forall Γ e A B m,
    d_wf_denv Γ ->
    Γ ⊢[ mode_ti ] e ⦂ ptyp_to_btyp_syn A ->
    empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⊑ B ->
    Γ ⊢[ m ] e ⦂ B.
Proof.
  apply d_typing_general_subsumption.
Qed.
