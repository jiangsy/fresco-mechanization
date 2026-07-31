(** TAGGED SUBJECT EQUIVALENCE [Θ ⊢ R ≡ᵘ R'] and its msubst generation.

    P7b's Sub-Arrow (and later ForallR / P7a) re-enter the induction after a
    consistency/subtyping run has advanced the context Θ0 to Θ1: the paper
    silently swaps the solution's metasubstitution θ for the package's θ1
    ("I used type equivalence a bit informally" — the author's own margin
    note at completeSubtyping).  The two subjects [msubst κ R] and
    [msubst σ R] are then only EQUIVALENT — same skeleton, ≡ᵗ-monotype
    paintings at the flexible leaves — never equal.

    The motive absorbs this by carrying the join at an arbitrary subject [T]
    with [Θ ⊢ T ≡ᵘ msubst κ R] (see prop_sub_complete_thm.v): the IH then
    takes the ORIGINAL join derivation unchanged, and only the consistency
    LEAVES ever transport — via the erasure of ≡ᵘ into ≡ˢ and the EXISTING
    pskl-level transports (skl_tyequiv_{consis,refine_syn_f,refine_pskl_f}_
    transport, prop_consis_complete.v).

    Design notes:
    - STRUCTURAL rows only (no sym/trans/refl closure): inversion at a known
      subject shape must stay trivial.  Reflexivity/symmetry are lemmas.
    - The one non-congruence row is [__mono]: paintings of ≡ᵗ monotypes.
      It carries wf AT THE RELATION'S OWN Θ so that a later substitution
      lemma (ForallL) can keep the leaves clear of the substituted variable.
    - Binder rows keep the SAME Θ (mirroring ≡ˢ's [__all]); transports pass
      a binds-monotone context parameter instead. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_tags.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.prop_inc.            (* a_tyequiv_pskl *)
Require Import src.frost.algo.prop_flex.           (* a_tyequiv_weaken_cons *)
Require Import src.frost.algo.prop_compose.        (* a_inc_lookup_{wf,mono}, msubst_lookup_notin *)
Require Import src.frost.algo.prop_normal.         (* a_inc_equiv_lookup *)
Require Import src.frost.algo.prop_pat_sub.        (* uskl_to_pskl_ptyp_to_uskl_syn *)
Require Import src.frost.algo.prop_consis_sound.   (* uskl_to_pskl_open *)
Require Import src.frost.algo.prop_look_complete_cstr. (* msubst_uskl_syn_open *)
Require Import src.frost.algo.prop_consis_precise.  (* ftag_in_uskl_{open_var,ptyp_syn} *)

Set Implicit Arguments.

Reserved Notation "Θ ⊢ R1 ≡ᵘ R2"
  (at level 75, R1 at level 74, R2 at level 74, no associativity).

Inductive a_uskl_tyequiv (Θ : aenv) : uskl -> uskl -> Prop :=
| a_uskl_tyequiv__mono : forall τ1 τ2,
    mono_ptyp τ1 -> mono_ptyp τ2 ->
    a_wf_ptyp Θ τ1 -> a_wf_ptyp Θ τ2 ->
    Θ ⊢ τ1 ≡ᵗ τ2 ->
    Θ ⊢ (ptyp_to_uskl_syn τ1) ≡ᵘ (ptyp_to_uskl_syn τ2)
| a_uskl_tyequiv__unit :
    Θ ⊢ uskl_unit ≡ᵘ uskl_unit
| a_uskl_tyequiv__var : forall α,
    Θ ⊢ (uskl_var_f α) ≡ᵘ (uskl_var_f α)
| a_uskl_tyequiv__arrow : forall R1 R2 R1' R2',
    Θ ⊢ R1 ≡ᵘ R1' ->
    Θ ⊢ R2 ≡ᵘ R2' ->
    Θ ⊢ (uskl_arrow R1 R2) ≡ᵘ (uskl_arrow R1' R2')
| a_uskl_tyequiv__all_syn : forall L R R',
    (forall α, α `notin` L ->
       Θ ⊢ (open_uskl_wrt_uskl R (uskl_var_f α)) ≡ᵘ
           (open_uskl_wrt_uskl R' (uskl_var_f α))) ->
    Θ ⊢ (uskl_all_syn R) ≡ᵘ (uskl_all_syn R')
| a_uskl_tyequiv__all_etag : forall L ε R R',
    (forall α, α `notin` L ->
       Θ ⊢ (open_uskl_wrt_uskl R (uskl_var_f α)) ≡ᵘ
           (open_uskl_wrt_uskl R' (uskl_var_f α))) ->
    Θ ⊢ (uskl_all_etag ε R) ≡ᵘ (uskl_all_etag ε R')
| a_uskl_tyequiv__hole :
    Θ ⊢ uskl_hole ≡ᵘ uskl_hole
| a_uskl_tyequiv__holeg :
    Θ ⊢ uskl_holeg ≡ᵘ uskl_holeg
| a_uskl_tyequiv__tophole : forall R R',
    Θ ⊢ R ≡ᵘ R' ->
    Θ ⊢ (uskl_tophole R) ≡ᵘ (uskl_tophole R')
| a_uskl_tyequiv__topholeg : forall R R',
    Θ ⊢ R ≡ᵘ R' ->
    Θ ⊢ (uskl_topholeg R) ≡ᵘ (uskl_topholeg R')
where "Θ ⊢ R1 ≡ᵘ R2" := (a_uskl_tyequiv Θ R1 R2) : type_scope.

(* ===================================================================== *)
(*  Reflexivity (from local closure) and symmetry                          *)
(* ===================================================================== *)

Lemma a_uskl_tyequiv_refl : forall Θ R,
  lc_uskl R ->
  Θ ⊢ R ≡ᵘ R.
Proof.
  intros Θ R Hlc; induction Hlc;
    try (apply a_uskl_tyequiv__all_syn with (L := empty); intros α _; auto);
    try (apply a_uskl_tyequiv__all_etag with (L := empty); intros α _; auto);
    eauto using a_uskl_tyequiv.
Qed.

Lemma a_uskl_tyequiv_sym : forall Θ R R',
  Θ ⊢ R ≡ᵘ R' ->
  Θ ⊢ R' ≡ᵘ R.
Proof.
  intros Θ R R' H; induction H;
    try (apply a_uskl_tyequiv__all_syn with (L := L); intros α Hα; auto);
    try (apply a_uskl_tyequiv__all_etag with (L := L); intros α Hα; auto);
    eauto using a_uskl_tyequiv, a_tyequiv__sym.
Qed.

(* ===================================================================== *)
(*  Erasure: ≡ᵘ projects onto ≡ˢ                                          *)
(* ===================================================================== *)

Lemma a_uskl_tyequiv_erase : forall Θ R R',
  Θ ⊢ R ≡ᵘ R' ->
  Θ ⊢ ⌊ R ⌋ˢ ≡ˢ ⌊ R' ⌋ˢ.
Proof.
  intros Θ R R' H; induction H; cbn.
  - (* mono paintings erase to the type's own skeleton *)
    rewrite !uskl_to_pskl_ptyp_to_uskl_syn.
    apply a_tyequiv_pskl; assumption.
  - apply a_pskl_tyequiv__refl; apply lc_pskl_unit.
  - apply a_pskl_tyequiv__refl; apply lc_pskl_var_f.
  - apply a_pskl_tyequiv__arrow; assumption.
  - apply a_pskl_tyequiv__all with (L := L); intros α Hα.
    rewrite <- !uskl_to_pskl_open. auto.
  - apply a_pskl_tyequiv__all with (L := L); intros α Hα.
    rewrite <- !uskl_to_pskl_open. auto.
  - apply a_pskl_tyequiv__refl; apply lc_pskl_hole.
  - apply a_pskl_tyequiv__refl; apply lc_pskl_hole.
  - apply a_pskl_tyequiv__tophole; assumption.
  - apply a_pskl_tyequiv__tophole; assumption.
Qed.

(* ===================================================================== *)
(*  Generation: equivalent metasubstitutions give ≡ᵘ images                *)
(* ===================================================================== *)

(** The workhorse.  [R] is the unresolved subject; every free variable is
    either Θ0-bound (where the a_inc kit supplies the leaf facts) or seen by
    NEITHER metasubstitution (the fresh binder-openers).  Stated with BOTH
    increases so wf / mono / ≡ᵗ of the images read off the kit. *)
Lemma a_inc_equiv_msubst_uskl : forall Θ0 κ σ Θ R,
  lc_uskl R ->
  (forall α, α `in` ftvar_in_uskl R ->
     a_binds_tvar α Θ0 \/ (α `notin` dom κ /\ α `notin` dom σ)) ->
  a_inc_equiv Θ0 κ σ Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  σ ∷ Θ0 ⊑ Θ ->
  a_wf_aenv Θ0 ->
  Θ ⊢ (msubst_uskl_syn κ R) ≡ᵘ (msubst_uskl_syn σ R).
Proof.
  intros Θ0 κ σ Θ R Hlc; revert Θ0 κ σ Θ.
  induction Hlc; intros Θ0 κ σ Θ Hftv Hie Hincκ Hincσ Hwf0; cbn.
  - (* unit *) apply a_uskl_tyequiv__unit.
  - (* var_f α *)
    destruct (Hftv α ltac:(cbn; fsetdec)) as [Hbt | [Hκ Hσ]].
    + apply a_uskl_tyequiv__mono;
        [ eapply a_inc_lookup_mono; exact Hincκ
        | eapply a_inc_lookup_mono; exact Hincσ
        | eapply a_inc_lookup_wf; eassumption
        | eapply a_inc_lookup_wf; eassumption
        | eapply a_inc_equiv_lookup; eassumption ].
    + rewrite (msubst_lookup_notin κ Hκ), (msubst_lookup_notin σ Hσ).
      cbn. apply a_uskl_tyequiv__var.
  - (* arrow *)
    apply a_uskl_tyequiv__arrow;
      [ eapply IHHlc1 | eapply IHHlc2 ]; try eassumption;
      intros α Hα; apply Hftv; cbn; clear - Hα; fsetdec.
  - (* all_syn *)
    apply a_uskl_tyequiv__all_syn with (L := dom κ `union` dom σ).
    intros α Hα.
    assert (Hoκ : msubst_uskl_syn κ (open_uskl_wrt_uskl R (uskl_var_f α))
                  = open_uskl_wrt_uskl (msubst_uskl_syn κ R) (uskl_var_f α))
      by (eapply msubst_uskl_syn_open;
          [ exact Hincκ | clear - Hα; fsetdec ]).
    assert (Hoσ : msubst_uskl_syn σ (open_uskl_wrt_uskl R (uskl_var_f α))
                  = open_uskl_wrt_uskl (msubst_uskl_syn σ R) (uskl_var_f α))
      by (eapply msubst_uskl_syn_open;
          [ exact Hincσ | clear - Hα; fsetdec ]).
    rewrite <- Hoκ, <- Hoσ.
    eapply H0; try eassumption.
    intros β Hβ.
    destruct (β == α) as [-> | Hne].
    + right. split; clear - Hα; fsetdec.
    + apply Hftv.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                    R (uskl_var_f α)) as Hup.
      cbn in Hup. clear - Hβ Hne Hup.
      assert (Hd : β `in` (singleton α `union` ftvar_in_uskl R)) by fsetdec.
      apply union_1 in Hd; destruct Hd as [Hd | Hd];
        [ exfalso; apply Hne; apply singleton_1 in Hd; auto | exact Hd ].
  - (* all_etag *)
    apply a_uskl_tyequiv__all_etag with (L := dom κ `union` dom σ).
    intros α Hα.
    assert (Hoκ : msubst_uskl_syn κ (open_uskl_wrt_uskl R (uskl_var_f α))
                  = open_uskl_wrt_uskl (msubst_uskl_syn κ R) (uskl_var_f α))
      by (eapply msubst_uskl_syn_open;
          [ exact Hincκ | clear - Hα; fsetdec ]).
    assert (Hoσ : msubst_uskl_syn σ (open_uskl_wrt_uskl R (uskl_var_f α))
                  = open_uskl_wrt_uskl (msubst_uskl_syn σ R) (uskl_var_f α))
      by (eapply msubst_uskl_syn_open;
          [ exact Hincσ | clear - Hα; fsetdec ]).
    rewrite <- Hoκ, <- Hoσ.
    eapply H0; try eassumption.
    intros β Hβ.
    destruct (β == α) as [-> | Hne].
    + right. split; clear - Hα; fsetdec.
    + apply Hftv.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                    R (uskl_var_f α)) as Hup.
      cbn in Hup. clear - Hβ Hne Hup.
      assert (Hd : β `in` (singleton α `union` ftvar_in_uskl R)) by fsetdec.
      apply union_1 in Hd; destruct Hd as [Hd | Hd];
        [ exfalso; apply Hne; apply singleton_1 in Hd; auto | exact Hd ].
  - (* hole *) apply a_uskl_tyequiv__hole.
  - (* tophole *) apply a_uskl_tyequiv__tophole; eauto.
  - (* holeg *) apply a_uskl_tyequiv__holeg.
  - (* topholeg *) apply a_uskl_tyequiv__topholeg; eauto.
Qed.

(* ===================================================================== *)
(*  Small inversions and transports the motive's rows read off             *)
(* ===================================================================== *)

(** A ghost is ≡ᵘ-inert: mono paintings are never ghosts. *)
Lemma a_uskl_tyequiv_hole_l_inv : forall Θ R',
  Θ ⊢ uskl_hole ≡ᵘ R' ->
  R' = uskl_hole.
Proof.
  intros Θ R' H; inversion H; subst; try reflexivity.
  destruct τ1; cbn in *; discriminate.
Qed.

Lemma a_uskl_tyequiv_holeg_l_inv : forall Θ R',
  Θ ⊢ uskl_holeg ≡ᵘ R' ->
  R' = uskl_holeg.
Proof.
  intros Θ R' H; inversion H; subst; try reflexivity.
  destruct τ1; cbn in *; discriminate.
Qed.

(** Both sides of ≡ᵘ are locally closed. *)
Lemma a_uskl_tyequiv_lc : forall Θ R R',
  Θ ⊢ R ≡ᵘ R' ->
  lc_uskl R /\ lc_uskl R'.
Proof.
  intros Θ R R' H; induction H.
  - split; apply mono_ptyp_to_uskl_syn_lc; assumption.
  - split; apply lc_uskl_unit.
  - split; apply lc_uskl_var_f.
  - destruct IHa_uskl_tyequiv1, IHa_uskl_tyequiv2.
    split; apply lc_uskl_arrow; assumption.
  - pick fresh α. destruct (H0 α ltac:(clear - Fr; fsetdec)) as [Hl Hr].
    split; [ eapply lc_uskl_all_syn_exists; exact Hl
           | eapply lc_uskl_all_syn_exists; exact Hr ].
  - pick fresh α. destruct (H0 α ltac:(clear - Fr; fsetdec)) as [Hl Hr].
    split; [ eapply lc_uskl_all_etag_exists; exact Hl
           | eapply lc_uskl_all_etag_exists; exact Hr ].
  - split; apply lc_uskl_hole.
  - split; apply lc_uskl_holeg.
  - destruct IHa_uskl_tyequiv. split; apply lc_uskl_tophole; assumption.
  - destruct IHa_uskl_tyequiv. split; apply lc_uskl_topholeg; assumption.
Qed.

(** A monotype's painting is guarded (its head is unit / var / arrow). *)
Lemma guarded_ptyp_to_uskl_syn : forall τ,
  mono_ptyp τ ->
  guarded_uskl (ptyp_to_uskl_syn τ).
Proof.
  intros τ Hm; destruct Hm; cbn.
  - apply guarded_uskl__unit.
  - apply guarded_uskl__var.
  - apply guarded_uskl__arrow;
      apply mono_ptyp_to_uskl_syn_lc; assumption.
Qed.

(** Guardedness transports along ≡ᵘ (only the head matters, and a guarded
    head is congruent or a mono painting on both sides). *)
Lemma a_uskl_tyequiv_guarded : forall Θ R R',
  Θ ⊢ R ≡ᵘ R' ->
  guarded_uskl R ->
  guarded_uskl R'.
Proof.
  intros Θ R R' H Hg; inversion H; subst.
  - (* mono row: any monotype painting is guarded *)
    apply guarded_ptyp_to_uskl_syn; assumption.
  - apply guarded_uskl__unit.
  - apply guarded_uskl__var.
  - (* arrow congruence: the components' lc comes from the relation *)
    match goal with
    | H1 : _ ⊢ _ ≡ᵘ ?A, H2 : _ ⊢ _ ≡ᵘ ?B
      |- guarded_uskl (uskl_arrow ?A ?B) =>
        apply guarded_uskl__arrow;
        [ exact (proj2 (a_uskl_tyequiv_lc H1))
        | exact (proj2 (a_uskl_tyequiv_lc H2)) ]
    end.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
Qed.

(* ===================================================================== *)
(*  ⇓ REFLECTION — Θ ⊢ A ≡ᵗ ⇓ᵗ[Θ]A                                        *)
(*                                                                        *)
(*  Obligation (1) of the Sub-Arrow scoping (PROGRESS 2026-07-31):        *)
(*  prop_normal.v proves the FORWARD direction (≡ᵗ sources collapse to    *)
(*  equal normal forms); the ≡ᵘ inversions need the converse — a type is  *)
(*  equivalent to its own total unfolding, because every unfolding step   *)
(*  is a [__flex_def] step.  Natural home is prop_normal.v; parked here   *)
(*  to keep the rebuild local (moving it forces the full algo chain).     *)
(* ===================================================================== *)

Lemma msubst_ptyp_nil : forall A, msubst_ptyp nil A = A.
Proof. induction A; cbn; f_equal; auto. Qed.

(** Pointwise congruence: a metasubstitution each of whose lookups is
    ≡ᵗ-related to the variable itself relates every type to its image. *)
Lemma msubst_ptyp_tyequiv_pointwise : forall Θ κ A,
  lc_ptyp A ->
  msubst_lc κ ->
  (forall β, Θ ⊢ (ptyp_var_f β) ≡ᵗ (msubst_lookup κ β)) ->
  Θ ⊢ A ≡ᵗ (msubst_ptyp κ A).
Proof.
  intros Θ κ A Hlc; revert Θ κ; induction Hlc; intros Θ κ Hκlc Hpt; cbn.
  - apply a_tyequiv__refl; apply lc_ptyp_unit.
  - apply Hpt.
  - apply a_tyequiv__arrow; auto.
  - apply a_tyequiv__all with (L := dom κ).
    intros α Hα.
    rewrite <- msubst_ptyp_open_lc
      by (first [ exact Hκlc | clear - Hα; fsetdec ]).
    apply H0; [ exact Hκlc | exact Hpt ].
Qed.

(** [a_tyequiv_weaken_cons] at a single cons entry (the [++]-form does not
    unify against a cons). *)
Lemma a_tyequiv_weaken_cons1 : forall Θ (x : atom) (b : abind) A A',
  Θ ⊢ A ≡ᵗ A' ->
  ((x, b) :: Θ) ⊢ A ≡ᵗ A'.
Proof.
  intros Θ x b A A' H.
  change ((x, b) :: Θ) with ((x ~ b) ++ Θ).
  apply a_tyequiv_weaken_cons; exact H.
Qed.

Lemma a_tyequiv_downarrow_refl : forall Θ,
  a_wf_aenv Θ ->
  forall A, lc_ptyp A ->
  Θ ⊢ A ≡ᵗ ⇓ᵗ[Θ] A.
Proof.
  (* [A0]: the [__var_typ] case's rule binder is [A] *)
  intros Θ Hwf; induction Hwf; intros A0 HlcA.
  - (* nil : the empty metasubstitution is the identity *)
    cbn. rewrite msubst_ptyp_nil.
    apply a_tyequiv__refl; exact HlcA.
  - (* flex α : the entry maps α to itself *)
    apply msubst_ptyp_tyequiv_pointwise;
      [ exact HlcA
      | apply aenv_msubst_lc; apply a_wf_aenv__flex; assumption
      | ].
    intros β. cbn.
    lazymatch goal with
    | |- context [ if ?c then _ else _ ] => destruct c as [Heq | Hne]
    end.
    + subst β. apply a_tyequiv__refl; apply lc_ptyp_var_f.
    + apply a_tyequiv_weaken_cons1.
      pose proof (IHHwf (ptyp_var_f β) (lc_ptyp_var_f β)) as Hβ.
      cbn in Hβ. exact Hβ.
  - (* flex_def α ≔ τ : one [__flex_def] step, then the tail's reflection *)
    apply msubst_ptyp_tyequiv_pointwise;
      [ exact HlcA
      | apply aenv_msubst_lc; apply a_wf_aenv__flex_def; assumption
      | ].
    intros β. cbn.
    lazymatch goal with
    | |- context [ if ?c then _ else _ ] => destruct c as [Heq | Hne]
    end.
    + subst β.
      eapply a_tyequiv__trans.
      * apply a_tyequiv__flex_def with (τ := τ).
        unfold binds; left; reflexivity.
      * apply a_tyequiv_weaken_cons1.
        apply IHHwf. apply mono_ptyp_lc; assumption.
    + apply a_tyequiv_weaken_cons1.
      pose proof (IHHwf (ptyp_var_f β) (lc_ptyp_var_f β)) as Hβ.
      cbn in Hβ. exact Hβ.
  - (* var_skl : invisible to ⇓ *)
    apply msubst_ptyp_tyequiv_pointwise;
      [ exact HlcA
      | apply aenv_msubst_lc; apply a_wf_aenv__var; assumption
      | ].
    intros β. cbn.
    apply a_tyequiv_weaken_cons1.
    pose proof (IHHwf (ptyp_var_f β) (lc_ptyp_var_f β)) as Hβ.
    cbn in Hβ. exact Hβ.
  - (* var_typ : invisible to ⇓ *)
    apply msubst_ptyp_tyequiv_pointwise;
      [ exact HlcA
      | apply aenv_msubst_lc; apply a_wf_aenv__var_typ; assumption
      | ].
    intros β. cbn.
    apply a_tyequiv_weaken_cons1.
    pose proof (IHHwf (ptyp_var_f β) (lc_ptyp_var_f β)) as Hβ.
    cbn in Hβ. exact Hβ.
  - (* tvar : invisible to ⇓ *)
    apply msubst_ptyp_tyequiv_pointwise;
      [ exact HlcA
      | apply aenv_msubst_lc; apply a_wf_aenv__tvar; assumption
      | ].
    intros β. cbn.
    apply a_tyequiv_weaken_cons1.
    pose proof (IHHwf (ptyp_var_f β) (lc_ptyp_var_f β)) as Hβ.
    cbn in Hβ. exact Hβ.
Qed.

(** Obligation (2): ≡ᵗ between arrows decomposes — both normal forms are
    the same arrow, and each side is equivalent to its own normal form. *)
Lemma a_tyequiv_arrow_inv : forall Θ A1 A2 B1 B2,
  a_wf_aenv Θ ->
  lc_ptyp A1 -> lc_ptyp A2 -> lc_ptyp B1 -> lc_ptyp B2 ->
  Θ ⊢ (ptyp_arrow A1 A2) ≡ᵗ (ptyp_arrow B1 B2) ->
  (Θ ⊢ A1 ≡ᵗ B1) /\ (Θ ⊢ A2 ≡ᵗ B2).
Proof.
  intros Θ A1 A2 B1 B2 Hwf Hlc1 Hlc2 Hlc1' Hlc2' Heq.
  pose proof (a_tyequiv_downarrow Hwf Heq) as Hdn.
  cbn in Hdn. injection Hdn as Hd1 Hd2.
  split.
  - eapply a_tyequiv__trans;
      [ apply a_tyequiv_downarrow_refl; assumption | ].
    rewrite Hd1. apply a_tyequiv__sym.
    apply a_tyequiv_downarrow_refl; assumption.
  - eapply a_tyequiv__trans;
      [ apply a_tyequiv_downarrow_refl; assumption | ].
    rewrite Hd2. apply a_tyequiv__sym.
    apply a_tyequiv_downarrow_refl; assumption.
Qed.

(* ===================================================================== *)
(*  Obligations (3)+(4): painting injectivity, and the MONO-PAINTING       *)
(*  inversion — anything ≡ᵘ-related to a monotype painting IS one          *)
(*  (paintings are structural, so [arrow (painting τa) (painting τb)]      *)
(*  IS [painting (τa→τb)]; the apparent arrow-vs-defined-var               *)
(*  counterexamples dissolve into the [__mono] row).                       *)
(* ===================================================================== *)

Lemma ptyp_to_uskl_syn_inj : forall τ1 τ2,
  ptyp_to_uskl_syn τ1 = ptyp_to_uskl_syn τ2 ->
  τ1 = τ2.
Proof.
  induction τ1; destruct τ2; cbn; intros Heq;
    try discriminate; try reflexivity;
    injection Heq as Heq1; f_equal; auto.
Qed.

Lemma a_uskl_tyequiv_mono_r_inv : forall Θ X Y,
  Θ ⊢ X ≡ᵘ Y ->
  forall τ, Y = ptyp_to_uskl_syn τ ->
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  exists τ', X = ptyp_to_uskl_syn τ' /\ mono_ptyp τ' /\
             a_wf_ptyp Θ τ' /\ Θ ⊢ τ' ≡ᵗ τ.
Proof.
  intros Θ X Y H; induction H; intros τ0 HeqY Hm Hwf.
  - (* __mono *)
    apply ptyp_to_uskl_syn_inj in HeqY. subst τ0.
    exists τ1; repeat split; assumption.
  - (* __unit *)
    destruct τ0; cbn in HeqY; try discriminate.
    exists ptyp_unit; repeat split;
      [ apply mono_ptyp__unit | apply a_wf_ptyp__unit
      | apply a_tyequiv__refl; apply lc_ptyp_unit ].
  - (* __var *)
    destruct τ0; cbn in HeqY; try discriminate.
    injection HeqY as <-.
    exists (ptyp_var_f α); repeat split;
      [ apply mono_ptyp__var | exact Hwf
      | apply a_tyequiv__refl; apply lc_ptyp_var_f ].
  - (* __arrow *)
    destruct τ0; cbn in HeqY; try discriminate.
    injection HeqY as Heq1 Heq2.   (* variable LHSs: substituted in place *)
    inversion Hm; subst.
    inversion Hwf; subst.
    destruct (IHa_uskl_tyequiv1 τ0_1 eq_refl ltac:(assumption) ltac:(assumption))
      as [τa [HXa [Hma [Hwfa Heqa]]]].
    destruct (IHa_uskl_tyequiv2 τ0_2 eq_refl ltac:(assumption) ltac:(assumption))
      as [τb [HXb [Hmb [Hwfb Heqb]]]].
    exists (ptyp_arrow τa τb); repeat split;
      [ cbn; rewrite HXa, HXb; reflexivity
      | apply mono_ptyp__arrow; assumption
      | apply a_wf_ptyp__arrow; assumption
      | apply a_tyequiv__arrow; assumption ].
  - (* __all_syn : painting of a MONO is never a ∀ *)
    destruct τ0; cbn in HeqY; try discriminate.
    inversion Hm.
  - (* __all_etag *)
    destruct τ0; cbn in HeqY; discriminate.
  - (* __hole *)
    destruct τ0; cbn in HeqY; discriminate.
  - (* __holeg *)
    destruct τ0; cbn in HeqY; discriminate.
  - (* __tophole *)
    destruct τ0; cbn in HeqY; discriminate.
  - (* __topholeg *)
    destruct τ0; cbn in HeqY; discriminate.
Qed.

(* ===================================================================== *)
(*  Obligation (5): TRANSITIVITY.  Not a row (rows stay inversion-        *)
(*  friendly); the only non-congruent composition is a structural arrow    *)
(*  against a mono-painting middle, and (4) collapses it: the whole        *)
(*  arrow-side IS a painting, so the composite is one [__mono] row.        *)
(* ===================================================================== *)

Lemma a_uskl_tyequiv_trans : forall Θ X Y,
  Θ ⊢ X ≡ᵘ Y ->
  forall Z, Θ ⊢ Y ≡ᵘ Z ->
  Θ ⊢ X ≡ᵘ Z.
Proof.
  intros Θ X Y H1; induction H1; intros Z HYZ.
  - (* __mono : both ends of the composite are paintings *)
    destruct (a_uskl_tyequiv_mono_r_inv (a_uskl_tyequiv_sym HYZ) eq_refl
                ltac:(assumption) ltac:(assumption))
      as [τ3 [HZ [Hm3 [Hwf3 Heq3]]]].
    subst Z.
    apply a_uskl_tyequiv__mono; try assumption.
    eapply a_tyequiv__trans; [ eassumption | ].
    apply a_tyequiv__sym; exact Heq3.
  - (* __unit *) exact HYZ.
  - (* __var *) exact HYZ.
  - (* __arrow *)
    inversion HYZ; subst.
    + (* the middle is a mono painting — so is the whole left arrow *)
      lazymatch goal with
      | He : ptyp_to_uskl_syn ?t = uskl_arrow _ _ |- _ =>
          assert (Hfull : Θ ⊢ (uskl_arrow R1 R2) ≡ᵘ (ptyp_to_uskl_syn t))
            by (rewrite He; apply a_uskl_tyequiv__arrow; assumption)
      end.
      lazymatch goal with
      | Hm1 : mono_ptyp ?t1, Hw1 : a_wf_ptyp _ ?t1,
        Ht : Θ ⊢ ?t1 ≡ᵗ ?t2,
        Hfull : Θ ⊢ (uskl_arrow R1 R2) ≡ᵘ (ptyp_to_uskl_syn ?t1) |- _ =>
          destruct (a_uskl_tyequiv_mono_r_inv Hfull eq_refl Hm1 Hw1)
            as [τx [HX [Hmx [Hwfx Heqx]]]]
      end.
      rewrite HX.
      apply a_uskl_tyequiv__mono; try assumption.
      eapply a_tyequiv__trans; eassumption.
    + apply a_uskl_tyequiv__arrow; auto.
  - (* __all_syn *)
    inversion HYZ; subst.
    + lazymatch goal with
      | Hm0 : mono_ptyp ?t, He : ptyp_to_uskl_syn ?t = uskl_all_syn _ |- _ =>
          destruct Hm0; cbn in He; discriminate He
      end.
    + lazymatch goal with
      | Hz : forall α : atom, α `notin` ?L2 -> Θ ⊢ _ ≡ᵘ _ |- _ =>
          apply a_uskl_tyequiv__all_syn with (L := L `union` L2);
          intros α Hα;
          apply H0; [ clear - Hα; fsetdec | apply Hz; clear - Hα; fsetdec ]
      end.
  - (* __all_etag *)
    inversion HYZ; subst.
    + lazymatch goal with
      | Hm0 : mono_ptyp ?t, He : ptyp_to_uskl_syn ?t = uskl_all_etag _ _ |- _ =>
          destruct Hm0; cbn in He; discriminate He
      end.
    + lazymatch goal with
      | Hz : forall α : atom, α `notin` ?L2 -> Θ ⊢ _ ≡ᵘ _ |- _ =>
          apply a_uskl_tyequiv__all_etag with (L := L `union` L2);
          intros α Hα;
          apply H0; [ clear - Hα; fsetdec | apply Hz; clear - Hα; fsetdec ]
      end.
  - (* __hole *) exact HYZ.
  - (* __holeg *) exact HYZ.
  - (* __tophole *)
    inversion HYZ; subst.
    + lazymatch goal with
      | Hm0 : mono_ptyp ?t, He : ptyp_to_uskl_syn ?t = uskl_tophole _ |- _ =>
          destruct Hm0; cbn in He; discriminate He
      end.
    + apply a_uskl_tyequiv__tophole; auto.
  - (* __topholeg *)
    inversion HYZ; subst.
    + lazymatch goal with
      | Hm0 : mono_ptyp ?t, He : ptyp_to_uskl_syn ?t = uskl_topholeg _ |- _ =>
          destruct Hm0; cbn in He; discriminate He
      end.
    + apply a_uskl_tyequiv__topholeg; auto.
Qed.

(* ===================================================================== *)
(*  Obligation (6): ARROW-ARROW inversion — the motive's relation at an    *)
(*  Arrow row splits into component relations.  [__arrow] is direct; a     *)
(*  [__mono] instance decomposes by (2), since a mono painting of an       *)
(*  arrow IS the arrow of the component paintings.                         *)
(* ===================================================================== *)

Lemma a_uskl_tyequiv_arrow_arrow_inv : forall Θ A B A' B',
  a_wf_aenv Θ ->
  Θ ⊢ (uskl_arrow A B) ≡ᵘ (uskl_arrow A' B') ->
  (Θ ⊢ A ≡ᵘ A') /\ (Θ ⊢ B ≡ᵘ B').
Proof.
  intros Θ A B A' B' Hwf H; inversion H; subst.
  - (* __mono *)
    lazymatch goal with
    | Hm1 : mono_ptyp ?t1, He1 : ptyp_to_uskl_syn ?t1 = uskl_arrow A B |- _ =>
        destruct Hm1; cbn in He1; try discriminate He1
    end.
    lazymatch goal with
    | Hm2 : mono_ptyp ?t2, He2 : ptyp_to_uskl_syn ?t2 = uskl_arrow A' B' |- _ =>
        destruct Hm2; cbn in He2; try discriminate He2
    end.
    lazymatch goal with
    | He1 : uskl_arrow _ _ = uskl_arrow A B |- _ => injection He1 as <- <-
    end.
    lazymatch goal with
    | He2 : uskl_arrow _ _ = uskl_arrow A' B' |- _ => injection He2 as <- <-
    end.
    inversion H4; subst. inversion H5; subst.
    destruct (a_tyequiv_arrow_inv Hwf
                (mono_ptyp_lc H2_) (mono_ptyp_lc H2_0)
                (mono_ptyp_lc H3_) (mono_ptyp_lc H3_0) H6) as [Hta Htb].
    split; apply a_uskl_tyequiv__mono; assumption.
  - (* __arrow *)
    split; assumption.
Qed.

(* ===================================================================== *)
(*  Obligation (7), generic half: images agree when the lookups do.        *)
(*  (The Arrow row instantiates this with [msubst_compose ζ w] vs [ζ] on   *)
(*  an id [w] to collapse the composite on Θ0-scoped subjects.)            *)
(* ===================================================================== *)

Lemma msubst_uskl_syn_agree : forall R κ σ,
  (forall α, α `in` ftvar_in_uskl R ->
     msubst_lookup κ α = msubst_lookup σ α) ->
  msubst_uskl_syn κ R = msubst_uskl_syn σ R.
Proof.
  induction R; intros κ σ Hag; cbn.
  - reflexivity.
  - reflexivity.
  - f_equal. apply Hag. cbn. clear; fsetdec.
  - f_equal;
      [ apply IHR1 | apply IHR2 ]; intros α Hα; apply Hag; cbn;
      clear - Hα; fsetdec.
  - f_equal. apply IHR. intros α Hα; apply Hag; cbn; clear - Hα; fsetdec.
  - f_equal. apply IHR. intros α Hα; apply Hag; cbn; clear - Hα; fsetdec.
  - reflexivity.
  - f_equal. apply IHR. intros α Hα; apply Hag; cbn; clear - Hα; fsetdec.
  - reflexivity.
  - f_equal. apply IHR. intros α Hα; apply Hag; cbn; clear - Hα; fsetdec.
Qed.

(* ===================================================================== *)
(*  Weakening ≡ᵘ by a context extension (binds-monotone: only the [__mono] *)
(*  row reads Θ — wf of the two paintings and their ≡ᵗ)                   *)
(* ===================================================================== *)

Lemma a_uskl_tyequiv_weaken_cons : forall Θ R R' (x : atom) (b : abind),
  Θ ⊢ R ≡ᵘ R' ->
  ((x ~ b) ++ Θ) ⊢ R ≡ᵘ R'.
Proof.
  intros Θ R R' x b H; induction H.
  - apply a_uskl_tyequiv__mono; try assumption;
      [ eapply a_wf_ptyp_weaken;
          [ intros y c Hb; unfold binds in *; simpl; right; exact Hb
          | assumption ]
      | eapply a_wf_ptyp_weaken;
          [ intros y c Hb; unfold binds in *; simpl; right; exact Hb
          | assumption ]
      | apply a_tyequiv_weaken_cons1; assumption ].
  - apply a_uskl_tyequiv__unit.
  - apply a_uskl_tyequiv__var.
  - apply a_uskl_tyequiv__arrow; assumption.
  - apply a_uskl_tyequiv__all_syn with (L := L); auto.
  - apply a_uskl_tyequiv__all_etag with (L := L); auto.
  - apply a_uskl_tyequiv__hole.
  - apply a_uskl_tyequiv__holeg.
  - apply a_uskl_tyequiv__tophole; assumption.
  - apply a_uskl_tyequiv__topholeg; assumption.
Qed.

Print Assumptions a_uskl_tyequiv_weaken_cons.

(* ===================================================================== *)
(*  Sub-ForallL row enablers: ∀-head inversions and the substitution      *)
(*  congruence.  ≡ᵘ is shape-rigid at quantifier heads (the [__mono] row  *)
(*  cannot produce one — monotypes have no ∀), so the inversions are      *)
(*  clean; the [__mono] row's Θ-wf leaves make substitution at a          *)
(*  Θ-fresh variable a no-op there (the design note anticipated exactly   *)
(*  this consumer).                                                       *)
(* ===================================================================== *)

Lemma a_uskl_tyequiv_all_syn_inv : forall Θ R R',
  Θ ⊢ (uskl_all_syn R) ≡ᵘ (uskl_all_syn R') ->
  exists L, forall α, α `notin` L ->
    Θ ⊢ (open_uskl_wrt_uskl R (uskl_var_f α)) ≡ᵘ
        (open_uskl_wrt_uskl R' (uskl_var_f α)).
Proof.
  intros Θ R R' H; inversion H; subst.
  - (* __mono : a monotype painting is never ∀-headed *)
    lazymatch goal with
    | Hm1 : mono_ptyp ?t1, He1 : ptyp_to_uskl_syn ?t1 = uskl_all_syn R |- _ =>
        destruct Hm1; cbn in He1; discriminate He1
    end.
  - (* __all_syn *) eauto.
Qed.

Lemma a_uskl_tyequiv_all_etag_inv : forall Θ ε R R',
  Θ ⊢ (uskl_all_etag ε R) ≡ᵘ (uskl_all_etag ε R') ->
  exists L, forall α, α `notin` L ->
    Θ ⊢ (open_uskl_wrt_uskl R (uskl_var_f α)) ≡ᵘ
        (open_uskl_wrt_uskl R' (uskl_var_f α)).
Proof.
  intros Θ ε R R' H; inversion H; subst.
  - lazymatch goal with
    | Hm1 : mono_ptyp ?t1, He1 : ptyp_to_uskl_syn ?t1 = uskl_all_etag ε R |- _ =>
        destruct Hm1; cbn in He1; discriminate He1
    end.
  - eauto.
Qed.

(** A Θ-wf monotype's painting avoids any Θ-fresh variable. *)
Lemma a_wf_ptyp_paint_notin : forall Θ τ β,
  a_wf_ptyp Θ τ ->
  β `notin` dom Θ ->
  β `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ).
Proof.
  intros Θ τ β Hwf Hβ.
  rewrite ftvar_in_uskl_ptyp_syn.
  intro Hc.
  pose proof (a_wf_ptyp_ftv_tvarish Hwf Hc) as Hbt.
  destruct Hbt as [Hb | [Hb | [τ0 Hb]]]; apply binds_In in Hb;
    clear - Hb Hβ; fsetdec.
Qed.

(** ≡ᵘ is closed under substituting a common (locally closed) skeleton for
    a Θ-fresh variable: the [__mono] leaves are Θ-scoped, hence untouched;
    every other row is a congruence. *)
Lemma a_uskl_tyequiv_subst : forall Θ X Y,
  Θ ⊢ X ≡ᵘ Y ->
  forall β ψ,
  lc_uskl ψ ->
  β `notin` dom Θ ->
  Θ ⊢ (subst_bskl_in_uskl ψ β X) ≡ᵘ (subst_bskl_in_uskl ψ β Y).
Proof.
  intros Θ X Y H; induction H; intros β ψ Hlcψ HβΘ.
  - (* __mono : both paintings are β-free *)
    rewrite (subst_bskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τ1) ψ β
               (a_wf_ptyp_paint_notin H1 HβΘ)).
    rewrite (subst_bskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τ2) ψ β
               (a_wf_ptyp_paint_notin H2 HβΘ)).
    apply a_uskl_tyequiv__mono; assumption.
  - (* __unit *) cbn. apply a_uskl_tyequiv__unit.
  - (* __var *)
    cbn. destruct (eq_var α β) as [-> | Hne].
    + apply a_uskl_tyequiv_refl. exact Hlcψ.
    + apply a_uskl_tyequiv__var.
  - (* __arrow *)
    cbn. apply a_uskl_tyequiv__arrow; auto.
  - (* __all_syn *)
    cbn. apply a_uskl_tyequiv__all_syn with (L := L `union` singleton β).
    intros γ Hγ.
    assert (Hne : β <> γ) by (clear - Hγ; fsetdec).
    rewrite (subst_bskl_in_uskl_open_uskl_wrt_uskl_var R ψ β γ Hne Hlcψ).
    rewrite (subst_bskl_in_uskl_open_uskl_wrt_uskl_var R' ψ β γ Hne Hlcψ).
    apply H0; [ clear - Hγ; fsetdec | exact Hlcψ | exact HβΘ ].
  - (* __all_etag *)
    cbn. apply a_uskl_tyequiv__all_etag with (L := L `union` singleton β).
    intros γ Hγ.
    assert (Hne : β <> γ) by (clear - Hγ; fsetdec).
    rewrite (subst_bskl_in_uskl_open_uskl_wrt_uskl_var R ψ β γ Hne Hlcψ).
    rewrite (subst_bskl_in_uskl_open_uskl_wrt_uskl_var R' ψ β γ Hne Hlcψ).
    apply H0; [ clear - Hγ; fsetdec | exact Hlcψ | exact HβΘ ].
  - (* __hole *) cbn. apply a_uskl_tyequiv__hole.
  - (* __holeg *) cbn. apply a_uskl_tyequiv__holeg.
  - (* __tophole *) cbn. apply a_uskl_tyequiv__tophole; auto.
  - (* __topholeg *) cbn. apply a_uskl_tyequiv__topholeg; auto.
Qed.

(** The opening form: instantiate two ≡ᵘ ∀-bodies at a common (locally
    closed) argument. *)
Lemma a_uskl_tyequiv_open : forall Θ R R' ψ L,
  (forall α, α `notin` L ->
     Θ ⊢ (open_uskl_wrt_uskl R (uskl_var_f α)) ≡ᵘ
         (open_uskl_wrt_uskl R' (uskl_var_f α))) ->
  lc_uskl ψ ->
  Θ ⊢ (open_uskl_wrt_uskl R ψ) ≡ᵘ (open_uskl_wrt_uskl R' ψ).
Proof.
  intros Θ R R' ψ L Hfam Hlcψ.
  destruct (atom_fresh
    (L `union` dom Θ `union` ftvar_in_uskl R `union` ftvar_in_uskl R'))
    as [β Fr].
  rewrite (subst_bskl_in_uskl_intro β R ψ ltac:(clear - Fr; fsetdec)).
  rewrite (subst_bskl_in_uskl_intro β R' ψ ltac:(clear - Fr; fsetdec)).
  apply a_uskl_tyequiv_subst;
    [ apply Hfam; clear - Fr; fsetdec | exact Hlcψ | clear - Fr; fsetdec ].
Qed.

(** ≡ᵘ preserves the syntactic tag reading: every row is tag-homomorphic,
    and the [__mono] row's paintings are tag-free on both sides.  (Lets
    the ≡ᵘ-subject transports carry `ftag`-conditioned premises across.) *)
Lemma a_uskl_tyequiv_ftag : forall Θ R R',
  Θ ⊢ R ≡ᵘ R' ->
  ftag_in_uskl R [=] ftag_in_uskl R'.
Proof.
  intros Θ R R' H; induction H; simpl; try (clear - IHa_uskl_tyequiv; fsetdec).
  - (* __mono *)
    rewrite (ftag_in_uskl_ptyp_syn τ1). rewrite (ftag_in_uskl_ptyp_syn τ2).
    clear; fsetdec.
  - (* __unit *) clear; fsetdec.
  - (* __var *) clear; fsetdec.
  - (* __arrow *)
    clear - IHa_uskl_tyequiv1 IHa_uskl_tyequiv2; fsetdec.
  - (* __all_syn *)
    pick fresh α for L.
    pose proof (H0 α ltac:(clear - Fr; fsetdec)) as Hb.
    pose proof (ftag_in_uskl_open_var R α) as Ho1.
    pose proof (ftag_in_uskl_open_var R' α) as Ho2.
    clear - Hb Ho1 Ho2; fsetdec.
  - (* __all_etag *)
    pick fresh α for L.
    pose proof (H0 α ltac:(clear - Fr; fsetdec)) as Hb.
    pose proof (ftag_in_uskl_open_var R α) as Ho1.
    pose proof (ftag_in_uskl_open_var R' α) as Ho2.
    clear - Hb Ho1 Ho2; fsetdec.
  - (* __hole *) clear; fsetdec.
  - (* __holeg *) clear; fsetdec.
Qed.
