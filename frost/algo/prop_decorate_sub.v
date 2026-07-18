(** DECORATION OF ALGORITHMIC SUBTYPING (lemma:decorating-algorithmic-
    subtyping, subtyping-proofs.tex:32-58) — the R-B enabler of
    thm:sound-subtyping (docs/DESIGN-subtyping.md §2.2, phase P4).

    An algorithmic subtyping run [Θ0 ⊢ₐ[N|M|P0] P ⊑ Q ⊣ Θ1] can be
    replayed as a DECORATED run [Θ0 ⊢ᵗ[N|M|P0|∅] ⌊P⌋ᵘ ⊑ Q ⊣ Θ1] whose
    ForallL instantiations use decorated skeletons whose tags the run
    solves.  This file builds the auxiliary lemmas bottom-up. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_pat_sub.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Erasure commutes with close                                       *)
(* ===================================================================== *)

Lemma uskl_to_pskl_close_rec : forall ψ X k,
  uskl_to_pskl (close_uskl_wrt_uskl_rec k X ψ)
  = close_pskl_wrt_pskl_rec k X (uskl_to_pskl ψ).
Proof.
  induction ψ; intros X k; simpl; try (f_equal; auto; fail).
  - destruct (lt_ge_dec n k); reflexivity.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      reflexivity.
Qed.

Lemma uskl_to_pskl_close : forall ψ X,
  ⌊ close_uskl_wrt_uskl X ψ ⌋ˢ = close_pskl_wrt_pskl X ⌊ ψ ⌋ˢ.
Proof.
  intros. unfold close_uskl_wrt_uskl, close_pskl_wrt_pskl.
  apply uskl_to_pskl_close_rec.
Qed.

(* ===================================================================== *)
(*  §2  Look decoration (lemma:look-decoration)                           *)
(*                                                                        *)
(*  Every locally-closed skeleton [Q] admits a decoration [ψ]: a fresh    *)
(*  tag on every quantifier, ghosts turned dotted.  Stated with an        *)
(*  avoid-set [L] so sibling subtrees get disjoint tags (the arrow rule   *)
(*  of [d_tags_skl] needs [Ψ1 ∩ Ψ2 = ∅]).                                 *)
(* ===================================================================== *)

Lemma pskl_decorate_exists : forall Q,
  lc_pskl Q ->
  forall L, exists Ψ ψ,
    AtomSetImpl.inter Ψ L [=] empty /\
    is_tskl ψ /\
    d_tags_skl Ψ ψ /\
    ⌊ ψ ⌋ˢ = Q /\
    (pskl_ghost_free Q -> uskl_ghost_free ψ).
Proof.
  intros Q Hlc; induction Hlc; intros L.
  - (* unit *)
    exists empty, uskl_unit. repeat apply conj;
      [ fsetdec | apply is_tskl__unit | apply d_tags_skl__unit; fsetdec
      | reflexivity | intros _; apply uskl_ghost_free__unit ].
  - (* var *)
    exists empty, (uskl_var_f Xps). repeat apply conj;
      [ fsetdec | apply is_tskl__var | apply d_tags_skl__var; fsetdec
      | reflexivity | intros _; apply uskl_ghost_free__var ].
  - (* arrow *)
    destruct (IHHlc1 L) as [Ψ1 [ψ1 [Hd1 [Ht1 [Hg1 [He1 Hgf1]]]]]].
    destruct (IHHlc2 (L `union` Ψ1))
      as [Ψ2 [ψ2 [Hd2 [Ht2 [Hg2 [He2 Hgf2]]]]]].
    exists (Ψ1 `union` Ψ2), (uskl_arrow ψ1 ψ2). repeat apply conj.
    + clear - Hd1 Hd2. fsetdec.
    + apply is_tskl__arrow; assumption.
    + apply d_tags_skl__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
        [ assumption | assumption | clear - Hd2; fsetdec | fsetdec ].
    + simpl. rewrite He1, He2. reflexivity.
    + intros Hg. simpl in Hg. destruct Hg as [Hga Hgb].
      apply uskl_ghost_free__arrow; [ apply Hgf1; auto | apply Hgf2; auto ].
  - (* all_syn → all_etag ε *)
    destruct (atom_fresh (L `union` ftvar_in_pskl P1)) as [X0 FrX].
    destruct (H0 X0 (L `union` singleton X0))
      as [Ψ0 [ψ0 [Hd0 [Ht0 [Hg0 [He0 Hgf0]]]]]].
    destruct (atom_fresh (L `union` Ψ0)) as [ε Frε].
    exists (add ε Ψ0), (uskl_all_etag ε (close_uskl_wrt_uskl X0 ψ0)).
    repeat apply conj.
    + clear - Hd0 Frε. fsetdec.
    + apply is_tskl__all_etag with (L := singleton X0).
      intros Y HY.
      rewrite <- subst_bskl_in_uskl_spec.
      change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply is_tskl_subst_mono; [ exact Ht0 | apply mono_ptyp__var ].
    + apply d_tags_skl__all_etag with (L := singleton X0) (Ψ0 := Ψ0);
        [ | clear - Frε; fsetdec | fsetdec ].
      intros Y HY.
      rewrite <- subst_bskl_in_uskl_spec.
      change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply d_tags_skl_subst_mono; [ exact Hg0 | apply mono_ptyp__var ].
    + simpl. rewrite uskl_to_pskl_close. rewrite He0.
      rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        [ reflexivity | clear - FrX; fsetdec ].
    + intros Hg. simpl in Hg.
      apply uskl_ghost_free__all_etag with (L := singleton X0).
      intros Y HY.
      rewrite <- subst_bskl_in_uskl_spec.
      change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply uskl_ghost_free_subst_mono; [ | apply mono_ptyp__var ].
      apply Hgf0. unfold open_pskl_wrt_pskl. apply pskl_ghost_free_open_rec.
      exact Hg.
  - (* hole → holeg *)
    exists empty, uskl_holeg. repeat apply conj;
      [ fsetdec | apply is_tskl__holeg | apply d_tags_skl__holeg; fsetdec
      | reflexivity | intros Hg; simpl in Hg; contradiction ].
  - (* tophole → topholeg *)
    destruct (IHHlc L) as [Ψ0 [ψ0 [Hd0 [Ht0 [Hg0 [He0 Hgf0]]]]]].
    exists Ψ0, (uskl_topholeg ψ0). repeat apply conj.
    + exact Hd0.
    + apply is_tskl__topholeg; assumption.
    + apply d_tags_skl__topholeg; assumption.
    + simpl. rewrite He0. reflexivity.
    + intros Hg. simpl in Hg. contradiction.
Qed.

(* ===================================================================== *)
(*  §3  Constraint-solving concatenation (lemma:solvetag-concat)          *)
(*                                                                        *)
(*  Solvable constraint lists are eq-prefixed with at most a single sub   *)
(*  at the tail; splitting/joining a solve at a list append splits/joins  *)
(*  the solved tag set.                                                   *)
(* ===================================================================== *)

Lemma a_solvetag_split : forall C1 C2 ψ Ψ,
  (C1 ++ C2) ⊩ᵗ ψ ⤳ Ψ ->
  exists Ψ1 Ψ2,
    C1 ⊩ᵗ ψ ⤳ Ψ1 /\ C2 ⊩ᵗ ψ ⤳ Ψ2 /\ Ψ [=] Ψ1 `union` Ψ2.
Proof.
  induction C1 as [ | c C1' IH ]; intros C2 ψ Ψ Hs; simpl in Hs.
  - exists empty, Ψ. repeat apply conj;
      [ apply a_solvetag__empty; fsetdec | exact Hs | fsetdec ].
  - destruct c as [ M Q | Q ].
    + (* sub head : inversion unifies C1' ++ C2 = nil *)
      inversion Hs as [ | M0 Q0 ψ0 Ψ0 Hsub Hnil | ]; subst.
      symmetry in H0. apply app_eq_nil in H0. destruct H0 as [-> ->].
      exists Ψ, empty. repeat apply conj;
        [ apply a_solvetag__sub; exact Hsub
        | apply a_solvetag__empty; fsetdec | fsetdec ].
    + (* eq head *)
      inversion Hs as [ | | Q0 C0 ψ0 Ψall Ψa Ψb Heqp Hrest HΨ ]; subst.
      destruct (IH C2 ψ Ψb Hrest) as [Ψ1 [Ψ2 [Hs1 [Hs2 HΨe]]]].
      exists (Ψa `union` Ψ1), Ψ2. repeat apply conj.
      * eapply a_solvetag__eq; [ exact Heqp | exact Hs1 | fsetdec ].
      * exact Hs2.
      * clear - HΨ HΨe. fsetdec.
Qed.

Scheme a_solvetag_sub_mut := Induction for a_solvetag_sub Sort Prop
  with a_solvetag_eq_mut := Induction for a_solvetag_eq Sort Prop.
Combined Scheme a_solvetag_sub_eq_mutind
  from a_solvetag_sub_mut, a_solvetag_eq_mut.

Lemma a_solvetag_sub_eq_psi_cong :
  (forall ψ M Q Ψ, ψ ≼ᵗ[ M ] Q ⤳ Ψ ->
     forall Ψ', Ψ [=] Ψ' -> ψ ≼ᵗ[ M ] Q ⤳ Ψ') /\
  (forall ψ Q Ψ, ψ ∼ᵗ Q ⤳ Ψ ->
     forall Ψ', Ψ [=] Ψ' -> ψ ∼ᵗ Q ⤳ Ψ').
Proof.
  apply (a_solvetag_sub_eq_mutind
           (fun ψ M Q Ψ _ => forall Ψ', Ψ [=] Ψ' -> ψ ≼ᵗ[ M ] Q ⤳ Ψ')
           (fun ψ Q Ψ _ => forall Ψ', Ψ [=] Ψ' -> ψ ∼ᵗ Q ⤳ Ψ'));
    intros; try (econstructor; eauto; fsetdec).
Qed.

Lemma a_solvetag_sub_psi_cong : forall ψ M Q Ψ Ψ',
  ψ ≼ᵗ[ M ] Q ⤳ Ψ -> Ψ [=] Ψ' -> ψ ≼ᵗ[ M ] Q ⤳ Ψ'.
Proof. intros; eapply (proj1 a_solvetag_sub_eq_psi_cong); eauto. Qed.

Lemma a_solvetag_eq_psi_cong : forall ψ Q Ψ Ψ',
  ψ ∼ᵗ Q ⤳ Ψ -> Ψ [=] Ψ' -> ψ ∼ᵗ Q ⤳ Ψ'.
Proof. intros; eapply (proj2 a_solvetag_sub_eq_psi_cong); eauto. Qed.

Lemma a_solvetag_psi_cong : forall C ψ Ψ Ψ',
  C ⊩ᵗ ψ ⤳ Ψ -> Ψ [=] Ψ' -> C ⊩ᵗ ψ ⤳ Ψ'.
Proof.
  intros C ψ Ψ Ψ' Hs; revert Ψ'; induction Hs; intros Ψ' Heq.
  - apply a_solvetag__empty. fsetdec.
  - apply a_solvetag__sub. eapply a_solvetag_sub_psi_cong; eauto.
  - eapply a_solvetag__eq; [ exact H | exact Hs | clear - Heq H0; fsetdec ].
Qed.

(* NB: the paper's converse (join) direction is only sound when the
   left list is eq-only — a sub constraint solves only as a singleton
   list.  The forward split above is what the main decoration proof
   consumes; the join is deferred until a call site fixes its shape. *)


(* ===================================================================== *)
(*  §4  Erasure commutes with decorated substitution                     *)
(* ===================================================================== *)

Lemma uskl_to_pskl_subst : forall ψ ψg β,
  ⌊ subst_bskl_in_uskl ψg β ψ ⌋ˢ
  = subst_pskl_in_pskl ⌊ ψg ⌋ˢ β ⌊ ψ ⌋ˢ.
Proof.
  induction ψ; intros ψg β; simpl; try (f_equal; auto; fail).
  match goal with |- context [ if ?e then _ else _ ] => destruct e end;
    reflexivity.
Qed.

(* ===================================================================== *)
(*  §5  The ρ metasubstitution (rigid vars → decorated skeletons)         *)
(*                                                                        *)
(*  The paper's ρ, applied to a decorated skeleton, and its erased        *)
(*  counterpart applied to the plain erasure.  Represented as iterated    *)
(*  single substitutions; freshness of the domain against the range is    *)
(*  maintained at every use so iterated = simultaneous.                   *)
(* ===================================================================== *)

Fixpoint msubst_uskl (ρ : list (atom * uskl)) (T : uskl) : uskl :=
  match ρ with
  | nil => T
  | (β, ψg) :: ρ' => subst_bskl_in_uskl ψg β (msubst_uskl ρ' T)
  end.

Fixpoint msubst_pskl_named (ρ : list (atom * pskl)) (P : pskl) : pskl :=
  match ρ with
  | nil => P
  | (β, Pg) :: ρ' => subst_pskl_in_pskl Pg β (msubst_pskl_named ρ' P)
  end.

Definition erase_msubst (ρ : list (atom * uskl)) : list (atom * pskl) :=
  map (fun ψg => uskl_to_pskl ψg) ρ.

(** Erasure commutes with the metasubstitution. *)
Lemma uskl_to_pskl_msubst : forall ρ T,
  ⌊ msubst_uskl ρ T ⌋ˢ = msubst_pskl_named (erase_msubst ρ) ⌊ T ⌋ˢ.
Proof.
  induction ρ as [ | [β ψg] ρ' IH ]; intros T; simpl; [ reflexivity | ].
  rewrite uskl_to_pskl_subst. rewrite IH. reflexivity.
Qed.

(** A variable outside the domain is untouched. *)
Lemma msubst_uskl_var_notin : forall ρ β,
  β `notin` dom ρ ->
  msubst_uskl ρ (uskl_var_f β) = uskl_var_f β.
Proof.
  induction ρ as [ | [γ ψg] ρ' IH ]; intros β Hβ; simpl; [ reflexivity | ].
  rewrite IH; [ | simpl in Hβ; clear - Hβ; fsetdec ].
  simpl.
  match goal with |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne] end;
    [ simpl in Hβ; exfalso; clear - Hβ; fsetdec | reflexivity ].
Qed.

(** Local closure of every range skeleton lets ρ commute with opening. *)
Definition msubst_lc (ρ : list (atom * uskl)) : Prop :=
  forall β ψg, binds β ψg ρ -> lc_uskl ψg.

Lemma msubst_uskl_open_comm : forall ρ T X,
  msubst_lc ρ ->
  X `notin` dom ρ ->
  (forall β ψg, binds β ψg ρ -> X `notin` ftvar_in_uskl ψg) ->
  msubst_uskl ρ (open_uskl_wrt_uskl T (uskl_var_f X))
  = open_uskl_wrt_uskl (msubst_uskl ρ T) (uskl_var_f X).
Proof.
  induction ρ as [ | [γ ψg] ρ' IH ]; intros T X Hlc Hdom Hftv;
    simpl; [ reflexivity | ].
  assert (Hlcγ : lc_uskl ψg)
    by (eapply Hlc; unfold binds; simpl; left; reflexivity).
  assert (Hlc' : msubst_lc ρ')
    by (intros b p Hb; eapply Hlc; unfold binds; simpl; right; exact Hb).
  assert (Hdom' : X `notin` dom ρ')
    by (simpl in Hdom; clear - Hdom; fsetdec).
  assert (Hftv' : forall b p, binds b p ρ' -> X `notin` ftvar_in_uskl p)
    by (intros b p Hb; eapply Hftv; unfold binds; simpl; right; exact Hb).
  rewrite (IH T X Hlc' Hdom' Hftv').
  rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcγ ].
  f_equal.
  assert (HXγ : X <> γ) by (simpl in Hdom; clear - Hdom; fsetdec).
  assert (HXf : X `notin` ftvar_in_uskl ψg)
    by (eapply Hftv; unfold binds; simpl; left; reflexivity).
  simpl.
  match goal with |- context [ if ?e then _ else _ ] => destruct e as [-> | _] end;
    [ contradiction | reflexivity ].
Qed.
