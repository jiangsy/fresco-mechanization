(** The TOTAL-UNFOLDING NORMAL FORM  [⇓[Θ] ·]  (docs/DESIGN-completeness-measure.md §4).

    The completeness proof for consistency (thm:complete-consistency) needs an
    induction measure

        V  =  size (⇓[Θ] (κ α))  +  size (⇓[Θ] (κ β))

    — "the size of the skeletons AS THE SOLUTION SEES THEM".  For that to be a
    well-defined natural number, the size must be stable under the two moves the
    proof constantly makes:

      (M1)  κ ≡ κ₁ on Θ₀   ([a_inc_equiv]; used at Arrow's second premise);
      (M2)  κα1̂ ≡ᵗ κτ       (used at both back-edges, [Flex-Flex-Assign] and
                            [Assign-Assign], to rewrite [α[τ/α1̂]] into [α]).

    Both are stated up to [a_tyequiv] ([≡ᵗ]), which is NOT size-preserving: its
    rule [a_tyequiv__flex_def] equates a defined flexible variable [α̂] with an
    ARBITRARY monotype [τ].  So [size (msubst_pskl κ P)] is not an invariant.

    The fix is to normalize by the TARGET context's own definitions.  A
    well-formed [Θ] is ordered and acyclic ([a_wf_aenv__flex_def] carries
    [a_wf_ptyp Θ τ] on the TAIL — a definition's body only mentions variables to
    its LEFT, i.e. deeper in the list), so it induces a total unfolding
    metasubstitution [aenv_msubst Θ], definable as a plain structural [Fixpoint].
    Writing [⇓[Θ]A := msubst_ptyp (aenv_msubst Θ) A], the crux is

        L1   {{ ⊢ Θ }}a -> {{ Θ ⊢ A ≡ᵗ B }}a -> ⇓[Θ]A = ⇓[Θ]B

    which makes [size (⇓[Θ] (κ α))] invariant under (M1) and (M2) — proved below
    as [a_tyequiv_downarrow], with the two moves themselves as
    [a_inc_equiv_downarrow_*] (M1) and [downarrow_subst_*] (M2). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_compose.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  The total-unfolding metasubstitution  [⇓[Θ]]                       *)
(* ===================================================================== *)

(** [aenv_msubst Θ]: unfold EVERY definition of [Θ], recursively.

    The list HEAD is the paper's RIGHTMOST (innermost, most recent) entry, and a
    definition's body is well-formed in the TAIL — so the tail is normalized
    first and the head's body is normalized BY the tail's normal form.  The
    result is therefore fully unfolded: no image of [aenv_msubst Θ] mentions a
    DEFINED variable of [Θ].

    Undefined flexible variables map to themselves (they are what a solution is
    still free to choose); rigid variables and term variables are not in the map
    at all, which is what makes the rigid extension [Θ → Θ,α] of
    [ForallInh]/[ForallSyn]/[UnivGhost1] invisible to [⇓] ([aenv_msubst_tvar]). *)
Fixpoint aenv_msubst (Θ : aenv) : metasubst :=
  match Θ with
  | nil => nil
  | (α, abind_flex_mono_def τ) :: Θ' =>
      (α, msubst_ptyp (aenv_msubst Θ') τ) :: aenv_msubst Θ'
  | (α, abind_flex_mono) :: Θ' =>
      (α, ptyp_var_f α) :: aenv_msubst Θ'
  | _ :: Θ' => aenv_msubst Θ'
  end.

Notation "⇓ᵗ[ Θ ] A" := (msubst_ptyp (aenv_msubst Θ) A)
  (at level 5, Θ at level 0, A at level 0, no associativity) : type_scope.
Notation "⇓ˢ[ Θ ] P" := (msubst_pskl (aenv_msubst Θ) P)
  (at level 5, Θ at level 0, P at level 0, no associativity) : type_scope.

(* --------------------------------------------------------------------- *)
(*  L2 / L4 : [⇓] ignores rigid and term-variable entries                  *)
(* --------------------------------------------------------------------- *)

Lemma aenv_msubst_tvar : forall α Θ,
  aenv_msubst ((α ~ abind_tvar) ++ Θ) = aenv_msubst Θ.
Proof. reflexivity. Qed.

Lemma aenv_msubst_var_typ : forall x A Θ,
  aenv_msubst ((x ~ abind_var_typ A) ++ Θ) = aenv_msubst Θ.
Proof. reflexivity. Qed.

Lemma aenv_msubst_var_skl : forall x P Θ,
  aenv_msubst ((x ~ abind_var_skl P) ++ Θ) = aenv_msubst Θ.
Proof. reflexivity. Qed.

(** The map lives inside the context's domain. *)
Lemma dom_aenv_msubst : forall Θ,
  dom (aenv_msubst Θ) [<=] dom Θ.
Proof.
  induction Θ as [ | [α b] Θ' IH ]; simpl; [ fsetdec | ].
  destruct b; simpl; clear - IH; fsetdec.
Qed.

Lemma aenv_msubst_notin : forall Θ α,
  α `notin` dom Θ ->
  msubst_lookup (aenv_msubst Θ) α = ptyp_var_f α.
Proof.
  intros Θ α Hα. apply msubst_lookup_notin.
  pose proof (dom_aenv_msubst Θ). clear - Hα H. fsetdec.
Qed.

(* --------------------------------------------------------------------- *)
(*  L2 (the workhorse) : entries ABOVE a suffix do not affect it           *)
(* --------------------------------------------------------------------- *)

Lemma aenv_msubst_lookup_app : forall Θp Θs α,
  uniq (Θp ++ Θs) ->
  α `in` dom Θs ->
  msubst_lookup (aenv_msubst (Θp ++ Θs)) α = msubst_lookup (aenv_msubst Θs) α.
Proof.
  intros Θp; induction Θp as [ | [β b] Θp' IH ];
    intros Θs α Huniq Hα; simpl; [ reflexivity | ].
  simpl in Huniq.
  assert (HnotinY : β `notin` dom (Θp' ++ Θs))
    by (inversion Huniq; subst; assumption).
  assert (Huniq' : uniq (Θp' ++ Θs)) by (inversion Huniq; subst; assumption).
  assert (HYne : α <> β).
  { intros Heq. subst β. apply HnotinY.
    rewrite dom_app. clear - Hα. fsetdec. }
  destruct b; simpl;
    try (apply IH; assumption);
    (destruct (α == β) as [Heq | Hne];
     [ exfalso; apply HYne; exact Heq | apply IH; assumption ]).
Qed.

(* --------------------------------------------------------------------- *)
(*  Local closure of the images                                            *)
(* --------------------------------------------------------------------- *)

(** All of a metasubstitution's images are locally closed.  [prop_compose.v] gets
    this from an [a_inc] witness; [aenv_msubst Θ] has no such witness (its target
    is [Θ] itself, which is not a suffix), so we take the property directly. *)
Definition msubst_lc (κ : metasubst) : Prop :=
  forall α, lc_ptyp (msubst_lookup κ α).

Lemma msubst_ptyp_open_rec_lc : forall κ,
  msubst_lc κ ->
  forall A A' k,
  msubst_ptyp κ (open_ptyp_wrt_ptyp_rec k A' A)
  = open_ptyp_wrt_ptyp_rec k (msubst_ptyp κ A') (msubst_ptyp κ A).
Proof.
  intros κ Hlc A; induction A; intros A' k; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - symmetry.
    apply open_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp.
    apply degree_ptyp_wrt_ptyp_O.
    apply degree_ptyp_wrt_ptyp_of_lc_ptyp.
    apply Hlc.
Qed.

Lemma msubst_ptyp_open_lc : forall κ A α,
  msubst_lc κ ->
  α `notin` dom κ ->
  msubst_ptyp κ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
  = open_ptyp_wrt_ptyp (msubst_ptyp κ A) (ptyp_var_f α).
Proof.
  intros κ A α Hlc Hα. unfold open_ptyp_wrt_ptyp.
  rewrite (msubst_ptyp_open_rec_lc Hlc A (ptyp_var_f α) 0).
  simpl. rewrite msubst_lookup_notin by exact Hα. reflexivity.
Qed.

Lemma msubst_ptyp_lc_lc : forall κ A,
  msubst_lc κ ->
  lc_ptyp A ->
  lc_ptyp (msubst_ptyp κ A).
Proof.
  intros κ A Hlc HA; induction HA; simpl.
  - constructor.
  - apply Hlc.
  - constructor; auto.
  - pick fresh α for (dom κ).
    apply lc_ptyp_all_exists with (α1 := α).
    erewrite <- msubst_ptyp_open_lc; [ apply H0 | exact Hlc | clear - Fr; fsetdec ].
Qed.

Lemma aenv_msubst_lc : forall Θ,
  {{ ⊢ Θ }}a ->
  msubst_lc (aenv_msubst Θ).
Proof.
  intros Θ Hwf; induction Hwf; intros α0; simpl.
  - constructor.
  - destruct (α0 == α) as [-> | Hne];
      [ constructor | apply IHHwf ].
  - destruct (α0 == α) as [-> | Hne];
      [ apply msubst_ptyp_lc_lc; [ exact IHHwf | apply mono_ptyp_lc; exact H1 ]
      | apply IHHwf ].
  - apply IHHwf.
  - apply IHHwf.
  - apply IHHwf.
Qed.

(* --------------------------------------------------------------------- *)
(*  A defined variable and its definition have the SAME normal form        *)
(* --------------------------------------------------------------------- *)

Lemma aenv_msubst_lookup_def : forall Θ α τ,
  {{ ⊢ Θ }}a ->
  binds α (abind_flex_mono_def τ) Θ ->
  msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[Θ] τ.
Proof.
  intros Θ α τ Hwf; revert α τ.
  induction Hwf as
    [ | β Θ' Hnd Hwf IH
      | β σ Θ' Hnd Hwpσ Hmσ Hwf IH
      | x P Θ' Hnd Hwp Hwf IH
      | x A Θ' Hnd Hwp Hwf IH
      | β Θ' Hnd Hwf IH ];
    intros α τ Hb; simpl in *.
  - inversion Hb.
  - (* head = undefined flexible β *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb']; [ discriminate | ].
    assert (Hfr : β `notin` ftvar_in_ptyp τ)
      by (eapply a_wf_aenv_head_notin_def_ftv;
          [ apply a_wf_aenv__flex; eassumption | exact Hb' ]).
    rewrite msubst_ptyp_cons_notin by exact Hfr.
    destruct (α == β) as [Heqα | Hne].
    { exfalso. subst β. apply binds_In in Hb'. clear - Hb' Hnd. fsetdec. }
    apply IH; exact Hb'.
  - (* head = definition β := σ *)
    destruct (α == β) as [Heqα | Hne].
    + subst β.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'].
      * assert (Heqτ : τ = σ) by (inversion Heqb; reflexivity). subst σ.
        assert (Hfr : α `notin` ftvar_in_ptyp τ)
          by (eapply a_wf_aenv_def_head_fresh;
              apply a_wf_aenv__flex_def; eassumption).
        rewrite msubst_ptyp_cons_notin by exact Hfr.
        reflexivity.
      * exfalso. apply binds_In in Hb'. clear - Hb' Hnd. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqα ?] | Hb'];
        [ exfalso; apply Hne; exact Heqα | ].
      assert (Hfr : β `notin` ftvar_in_ptyp τ)
        by (eapply a_wf_aenv_head_notin_def_ftv;
            [ apply a_wf_aenv__flex_def; eassumption | exact Hb' ]).
      rewrite msubst_ptyp_cons_notin by exact Hfr.
      apply IH; exact Hb'.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb']; [ discriminate | ].
    apply IH; exact Hb'.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb']; [ discriminate | ].
    apply IH; exact Hb'.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb']; [ discriminate | ].
    apply IH; exact Hb'.
Qed.

(* ===================================================================== *)
(*  §2  L1 — [⇓] IS [≡ᵗ]-SOUND                                            *)
(* ===================================================================== *)

(** THE CRUX.  [≡ᵗ] is not size-preserving, but it IS [⇓]-preserving: every one
    of its rules is either a congruence, an equivalence closure step, or the
    definition lookup — and the lookup is exactly [aenv_msubst_lookup_def]. *)
Lemma a_tyequiv_downarrow : forall Θ A A',
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  ⇓ᵗ[Θ] A = ⇓ᵗ[Θ] A'.
Proof.
  intros Θ A A' Hwf Heq; induction Heq.
  - reflexivity.
  - symmetry; auto.
  - transitivity (⇓ᵗ[Θ] B); auto.
  - simpl. apply aenv_msubst_lookup_def; assumption.
  - simpl. f_equal; auto.
  - simpl. f_equal.
    pose proof (aenv_msubst_lc Hwf) as Hlc.
    pick fresh α for (L `union` dom (aenv_msubst Θ)
                        `union` ftvar_in_ptyp (⇓ᵗ[Θ] A)
                        `union` ftvar_in_ptyp (⇓ᵗ[Θ] B)).
    apply open_ptyp_wrt_ptyp_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | ].
    rewrite <- msubst_ptyp_open_lc by (first [ exact Hlc | clear - Fr; fsetdec ]).
    rewrite <- msubst_ptyp_open_lc by (first [ exact Hlc | clear - Fr; fsetdec ]).
    apply H0; [ clear - Fr; fsetdec | exact Hwf ].
Qed.

(* ===================================================================== *)
(*  §3  Transporting [⇓]-equalities through an outer metasubstitution      *)
(* ===================================================================== *)

(** Two metasubstitutions whose images are [ζ]-equal on a type's free variables
    are indistinguishable after [ζ].  NB the [∀] case needs NO opening: [msubst]
    goes under the binder syntactically, and [ftvar_in_ptyp (ptyp_all A) =
    ftvar_in_ptyp A]. *)
Lemma msubst_ptyp_outer_ext : forall ζ κ κ' A,
  (forall α, α `in` ftvar_in_ptyp A ->
     msubst_ptyp ζ (msubst_lookup κ α) = msubst_ptyp ζ (msubst_lookup κ' α)) ->
  msubst_ptyp ζ (msubst_ptyp κ A) = msubst_ptyp ζ (msubst_ptyp κ' A).
Proof.
  intros ζ κ κ' A; induction A; intros Hag; simpl.
  - reflexivity.
  - reflexivity.
  - apply Hag. simpl. fsetdec.
  - f_equal; [ apply IHA1 | apply IHA2 ];
      intros α Hα; apply Hag; simpl; fsetdec.
  - f_equal. apply IHA. intros α Hα; apply Hag; simpl; fsetdec.
Qed.

Lemma msubst_pskl_outer_ext : forall ζ κ κ' P,
  (forall α, α `in` ftvar_in_pskl P ->
     msubst_ptyp ζ (msubst_lookup κ α) = msubst_ptyp ζ (msubst_lookup κ' α)) ->
  msubst_pskl ζ (msubst_pskl κ P) = msubst_pskl ζ (msubst_pskl κ' P).
Proof.
  intros ζ κ κ' P;
    induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hag; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite !msubst_pskl_embed_ptyp. f_equal. apply Hag. simpl. fsetdec.
  - f_equal; [ apply IHa | apply IHb ];
      intros α Hα; apply Hag; simpl; fsetdec.
  - f_equal. apply IHall. intros α Hα; apply Hag; simpl; fsetdec.
  - reflexivity.
  - f_equal. apply IHt. intros α Hα; apply Hag; simpl; fsetdec.
Qed.

(* ===================================================================== *)
(*  §4  (M2) — the BACK-EDGE move  [α[τ/α1̂] ↦ α]                           *)
(* ===================================================================== *)

(** Lookup in an extended metasubstitution.  Stated as rewrite rules so that
    proofs never have to [destruct] an [if] that [simpl] has left inside another
    substitution's argument. *)
Lemma msubst_lookup_cons_eq : forall (α1 : atom) τ0 κ,
  msubst_lookup ((α1, τ0) :: κ) α1 = τ0.
Proof.
  intros α1 τ0 κ. simpl.
  destruct (α1 == α1) as [_ | Hc]; [ reflexivity | congruence ].
Qed.

Lemma msubst_lookup_cons_neq : forall (α α1 : atom) τ0 κ,
  α <> α1 ->
  msubst_lookup ((α1, τ0) :: κ) α = msubst_lookup κ α.
Proof.
  intros α α1 τ0 κ Hne. simpl.
  destruct (α == α1) as [Hc | _]; [ congruence | reflexivity ].
Qed.

(** Substituting a definition and then applying the tail metasubstitution is the
    same as applying the full metasubstitution with [α1̂ ↦ ⟦τ⟧]. *)
Lemma msubst_ptyp_subst : forall κ τ α1 A,
  msubst_ptyp κ (subst_ptyp_in_ptyp τ α1 A)
  = msubst_ptyp ((α1, msubst_ptyp κ τ) :: κ) A.
Proof.
  intros κ τ α1 A;
    induction A as [ | n | β | A1 IH1 A2 IH2 | A0 IH0 ].
  - reflexivity.
  - reflexivity.
  - destruct (β == α1) as [Heq | Hne].
    + subst β. cbn [subst_ptyp_in_ptyp msubst_ptyp].
      destruct (α1 == α1) as [_ | Hc]; [ | congruence ].
      rewrite msubst_lookup_cons_eq. reflexivity.
    + cbn [subst_ptyp_in_ptyp msubst_ptyp].
      destruct (β == α1) as [Hc | _]; [ congruence | ].
      cbn [msubst_ptyp].
      rewrite msubst_lookup_cons_neq by exact Hne. reflexivity.
  - cbn [subst_ptyp_in_ptyp msubst_ptyp]. f_equal; auto.
  - cbn [subst_ptyp_in_ptyp msubst_ptyp]. f_equal; auto.
Qed.

Lemma msubst_pskl_subst : forall κ τ α1 P,
  msubst_pskl κ (subst_pskl_in_pskl (ptyp_to_pskl τ) α1 P)
  = msubst_pskl ((α1, msubst_ptyp κ τ) :: κ) P.
Proof.
  intros κ τ α1 P;
    induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ].
  - reflexivity.
  - reflexivity.
  - destruct (β == α1) as [Heq | Hne].
    + subst β. cbn [subst_pskl_in_pskl msubst_pskl].
      destruct (α1 == α1) as [_ | Hc]; [ | congruence ].
      rewrite msubst_lookup_cons_eq.
      apply msubst_pskl_embed_ptyp.
    + cbn [subst_pskl_in_pskl msubst_pskl].
      destruct (β == α1) as [Hc | _]; [ congruence | ].
      cbn [msubst_pskl].
      rewrite msubst_lookup_cons_neq by exact Hne. reflexivity.
  - cbn [subst_pskl_in_pskl msubst_pskl]. f_equal; auto.
  - cbn [subst_pskl_in_pskl msubst_pskl]. f_equal; auto.
  - reflexivity.
  - cbn [subst_pskl_in_pskl msubst_pskl]. f_equal; auto.
Qed.

(** (M2), the type version.  [κ = (α1,τ') :: κ₀] is the metasubstitution at the
    context [Θ₀,α1̂:=τ]; [κ₀] is the one the back-edge's premise runs at.  The
    hypothesis is exactly [a_inc__flex_def]'s premise. *)
Lemma downarrow_subst_ptyp : forall Θ κ0 α1 τ τ' A,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) }}a ->
  ⇓ᵗ[Θ] (msubst_ptyp κ0 (subst_ptyp_in_ptyp τ α1 A))
  = ⇓ᵗ[Θ] (msubst_ptyp ((α1, τ') :: κ0) A).
Proof.
  intros Θ κ0 α1 τ τ' A Hwf Heq.
  rewrite msubst_ptyp_subst.
  apply msubst_ptyp_outer_ext.
  intros α Hα. simpl.
  destruct (α == α1) as [-> | Hne]; [ | reflexivity ].
  symmetry. apply a_tyequiv_downarrow; assumption.
Qed.

(** (M2), the skeleton version — this is the shape [a_unify__flex_assign] and
    [a_assign__assign] actually use. *)
Lemma downarrow_subst_pskl : forall Θ κ0 α1 τ τ' P,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) }}a ->
  ⇓ˢ[Θ] (msubst_pskl κ0 (subst_pskl_in_pskl (ptyp_to_pskl τ) α1 P))
  = ⇓ˢ[Θ] (msubst_pskl ((α1, τ') :: κ0) P).
Proof.
  intros Θ κ0 α1 τ τ' P Hwf Heq.
  rewrite msubst_pskl_subst.
  apply msubst_pskl_outer_ext.
  intros α Hα. simpl.
  destruct (α == α1) as [-> | Hne]; [ | reflexivity ].
  symmetry. apply a_tyequiv_downarrow; assumption.
Qed.

(** The size corollaries (M2) hands to the measure. *)
Corollary downarrow_subst_ptyp_size : forall Θ κ0 α1 τ τ' A,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) }}a ->
  size_ptyp (⇓ᵗ[Θ] (msubst_ptyp κ0 (subst_ptyp_in_ptyp τ α1 A)))
  = size_ptyp (⇓ᵗ[Θ] (msubst_ptyp ((α1, τ') :: κ0) A)).
Proof.
  intros. erewrite downarrow_subst_ptyp by eauto. reflexivity.
Qed.

Corollary downarrow_subst_pskl_size : forall Θ κ0 α1 τ τ' P,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) }}a ->
  size_pskl (⇓ˢ[Θ] (msubst_pskl κ0 (subst_pskl_in_pskl (ptyp_to_pskl τ) α1 P)))
  = size_pskl (⇓ˢ[Θ] (msubst_pskl ((α1, τ') :: κ0) P)).
Proof.
  intros. erewrite downarrow_subst_pskl by eauto. reflexivity.
Qed.

(* ===================================================================== *)
(*  §5  (M1) — metasubstitution EQUIVALENCE is invisible to [⇓]            *)
(* ===================================================================== *)

Lemma a_inc_equiv_dom : forall Θ0 κ1 κ2 Θ,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  dom κ1 [<=] dom Θ0 /\ dom κ2 [<=] dom Θ0.
Proof.
  intros Θ0 κ1 κ2 Θ Hie; induction Hie; simpl in *;
    try (destruct IHHie as [H1 H2]);
    split; try fsetdec.
Qed.

(** Two equivalent metasubstitutions send every type-variable of the source to
    [≡ᵗ]-equivalent images. *)
Lemma a_inc_equiv_lookup_tvar : forall Θ0 κ1 κ2 Θ,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  {{ ⊢ Θ0 }}a ->
  forall α', a_binds_tvar α' Θ0 ->
  {{ Θ ⊢ (msubst_lookup κ1 α') ≡ᵗ (msubst_lookup κ2 α') }}a.
Proof.
  intros Θ0 κ1 κ2 Θ Hie; induction Hie; intros Hwf α' Hbt.
  - (* empty *)
    destruct Hbt as [Hb | [Hb | [τ Hb]]]; inversion Hb.
  - (* flex α *)
    assert (Hwf' : {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    simpl. destruct (α' == α) as [-> | Hne];
      [ assumption | ].
    apply IHHie; [ exact Hwf' | ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq ?] | Hb'];
      try (exfalso; apply Hne; exact Heq);
      [ left | right; left | right; right; exists τ ]; exact Hb'.
  - (* flex_def α := τ *)
    assert (Hwf' : {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    simpl. destruct (α' == α) as [-> | Hne];
      [ assumption | ].
    apply IHHie; [ exact Hwf' | ].
    destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq ?] | Hb'];
      try (exfalso; apply Hne; exact Heq);
      [ left | right; left | right; right; exists τ0 ]; exact Hb'.
  - (* term variable, type binding : κ unchanged, target grows *)
    assert (Hwf' : {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    assert (Hbt' : a_binds_tvar α' Θ).
    { destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        try discriminate;
        [ left | right; left | right; right; exists τ0 ]; exact Hb'. }
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds in *;
        apply in_or_app; right; simpl; right; exact Hby
      | apply IHHie; assumption ].
  - (* term variable, skeleton binding *)
    assert (Hwf' : {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    assert (Hbt' : a_binds_tvar α' Θ).
    { destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        try discriminate;
        [ left | right; left | right; right; exists τ0 ]; exact Hb'. }
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds in *;
        apply in_or_app; right; simpl; right; exact Hby
      | apply IHHie; assumption ].
  - (* rigid α : κ does not touch it, so both lookups are α itself *)
    assert (Hnd : α `notin` dom Θ /\ {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    destruct Hnd as [Hnd Hwf'].
    destruct (a_inc_equiv_dom Hie) as [Hd1 Hd2].
    destruct (α' == α) as [-> | Hne].
    + rewrite !msubst_lookup_notin
        by (first [ clear - Hnd Hd1; fsetdec | clear - Hnd Hd2; fsetdec ]).
      apply a_tyequiv__refl. constructor.
    + assert (Hbt' : a_binds_tvar α' Θ).
      { destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq ?] | Hb'];
          try (exfalso; apply Hne; exact Heq);
          [ left | right; left | right; right; exists τ0 ]; exact Hb'. }
      eapply a_tyequiv_weaken;
        [ intros y b Hby; unfold binds in *;
          apply in_or_app; right; simpl; right; exact Hby
        | apply IHHie; assumption ].
Qed.

(** (M1), the skeleton version — this is what Arrow's second premise needs. *)
Lemma a_inc_equiv_downarrow_pskl : forall Θ0 κ1 κ2 Θ P,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θ }}a ->
  a_scope_pskl Θ0 P ->
  ⇓ˢ[Θ] (msubst_pskl κ1 P) = ⇓ˢ[Θ] (msubst_pskl κ2 P).
Proof.
  intros Θ0 κ1 κ2 Θ P Hie Hwf0 Hwf HP.
  apply msubst_pskl_outer_ext. intros α Hα.
  apply a_tyequiv_downarrow; [ exact Hwf | ].
  eapply a_inc_equiv_lookup_tvar;
    [ exact Hie | exact Hwf0 | eapply a_scope_pskl_ftv_tvarish; eauto ].
Qed.

Corollary a_inc_equiv_downarrow_pskl_size : forall Θ0 κ1 κ2 Θ P,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θ }}a ->
  a_scope_pskl Θ0 P ->
  size_pskl (⇓ˢ[Θ] (msubst_pskl κ1 P)) = size_pskl (⇓ˢ[Θ] (msubst_pskl κ2 P)).
Proof.
  intros. erewrite a_inc_equiv_downarrow_pskl by eauto. reflexivity.
Qed.
