(* ===================================================================== *)
(*  COMPLETENESS of consistency / unification / assignment                *)
(*  (thm:complete-consistency; paper proof: consistency-proofs.tex        *)
(*  :2225-3167 "Completeness of Consistency", all three parts).           *)
(*                                                                        *)
(*  The paper proceeds "by mutual induction for the three parts":         *)
(*    part 1 (consistency)  — case analysis on the last rule of the       *)
(*      declarative join derivation, with the special cases peeled first  *)
(*      (:2566-2580): P₀ = ◇ → GhostR; P₀ = ∀◇.P₀' with P guarded →       *)
(*      UnivGhostR; P or P₀ flexible → parts 2/3.                          *)
(*    part 2 (unification)  — walk of the context Θ₀.                      *)
(*    part 3 (assignment)   — walk of the context pair Θ₀ ∣ Ξ.             *)
(*                                                                        *)
(*  [paper-gap] The paper's three stated induction subjects do NOT        *)
(*  combine into a well-founded order (docs/DESIGN-completeness-          *)
(*  measure.md §3): the back-edges Flex-Flex-Assign / Assign-Assign hand  *)
(*  part 1 a declarative derivation that can be strictly LARGER than the  *)
(*  caller's, and UnivGhostR recurses with the SAME one.  The repaired    *)
(*  measure (design doc §4, infrastructure green in prop_completeness_consis.v (PART A))  *)
(*                                                                        *)
(*      μ = (V, n, t, k)   lexicographic on ℕ⁴                            *)
(*                                                                        *)
(*  runs on V = the size of the node's two skeletons AS THE SOLUTION      *)
(*  SEES THEM (⇓ˢ[Θ] ∘ κ): V strictly decreases on every consistency-      *)
(*  internal edge, is exactly constant on every cross/back-edge — where   *)
(*  n = |Θ₀| (resp. |Ξ|+|Θ₀|) then strictly decreases; t breaks the       *)
(*  consis→unify/assign tie; k breaks Assign-Depend.  All 21 edges are    *)
(*  verified in the design doc §5.                                        *)
(*                                                                        *)
(*  The statement is the paper's FUSED one (:2246-2255): existence of the *)
(*  algorithmic derivation TOGETHER WITH the factoring (ζ, a_inc_equiv)   *)
(*  and — for consistency — the PRECISION of the output (⊑ against the    *)
(*  competing solution's join target), on the AUGMENTED problem           *)
(*  (Δ₁;Δ₂;Ψ;Θ₀;P₀;R) of :2230-2242.  COMPLETE — no admits; the whole      *)
(*  bundle (and [a_consis_complete_thm]) is axiom-free.                   *)
(* ===================================================================== *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.decorated_algo.prop_decorate.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_soundness_consis.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_precise_recover.
Require Import src.frost.algo.prop_consis_rename.

Set Implicit Arguments.

(* ##################################################################### *)
(*  PART A — THE μ-MEASURE (formerly algo/prop_consis_exist.v, merged     *)
(*  2026-07-18; that file and the deprecated OPT-bundle file               *)
(*  prop_completeness_consis.v (PART B) were folded into this one).                     *)
(* ##################################################################### *)

(** EXISTENCE for [thm:complete-consistency] — the well-founded-measure half.

    If a consistency / unification / assignment problem HAS a solution, the
    algorithm PRODUCES a derivation.  The hypothesis is a declarative
    (solution-side) derivation, and the paper's "mutual induction for the three
    parts" inducts on it in part 1.  A mutual IH is only usable BELOW the
    current point, so every appeal needs a witness derivation that is a
    subderivation of the hypothesis (structural induction) or strictly smaller
    (size induction).

    WHERE THE DIRECT SUBDERIVATION IS LOST — on three edges the witness handed
    to the callee is not carved out of the caller's derivation at all:

      - Assign-Assign (assign → consis): the algorithm substitutes the head
        definition β̂ ≔ τ into the subject and re-runs consistency on the
        SUBSTITUTED problem.  No premise of the caller's derivation is about
        that judgment; its witness must be SYNTHESIZED FROM THE SOLUTION
        (reflexivity at the solved κ(α̂[τ/β̂])).
      - UnivGhostR (consis → consis): the premise reuses the caller's
        derivation IDENTICALLY (the ∀◇ is peeled from the problem, not from
        the derivation).
      - Flex-Flex-Assign (unify → assign): the witness is only transported
        across ≡ᵗ, i.e. rebuilt, not extracted.

    WHY THE PAPER'S MEASURE ALSO FAILS — a synthesized witness could still be
    fine if it were smaller, but it is not: in Assign-Assign the caller's Ghost
    node absorbs an arbitrary Q in ONE node, which the solved type spells back
    out, so the new witness is strictly LARGER (§3.2 witness: 3 nodes → 5); and
    ≡ᵗ-transport is not size-preserving.  Falling back to context size fails on
    a DISJOINT edge: Arrow's second premise runs in a context GROWN by guess
    (§3.1).  Hence no lexicographic combination of |derivation| and context
    size is well-founded (design doc §3), and the proof instead runs on the
    WELL-FOUNDED MEASURE

        μ = (V, n, t, k)   lexicographic on ℕ⁴

    of docs/DESIGN-completeness-measure.md §4:

      V = size of the SOLVED skeletons  size (⇓ˢ[Θ] (κ α)) + size (⇓ˢ[Θ] (κ β))
      n = |Θ0|  (consis, unify) | |Ξ|+|Θ0| (assign)
      t = 1 (consis) | 0 (unify/assign)   — breaks the consis↔unify/assign tie
      k = |Θ0| (assign) | 0 (consis/unify) — breaks Assign-Depend

    The V-invariance machinery (⇓ˢ, a_tyequiv_downarrow, and the size corollaries)
    is built and green in algo/prop_normal.v; this file supplies (1) the ℕ⁴
    lexicographic order and its well-foundedness, (2) the measure components,
    (3) the per-edge decrease facts, and (4) the STUCK-CHECK (the §9.2 paper gap). *)

(* ===================================================================== *)
(*  §1  The lexicographic order on ℕ⁴ and its well-foundedness            *)
(* ===================================================================== *)

Section Lex.
  Context {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop).

  Definition lex (x y : A * B) : Prop :=
    RA (fst x) (fst y) \/ (fst x = fst y /\ RB (snd x) (snd y)).

  Lemma lex_wf : well_founded RA -> well_founded RB -> well_founded lex.
  Proof.
    intros wfA wfB [a b]. revert b.
    generalize (wfA a); intros Ha.
    induction Ha as [a Ha IHa]. intros b.
    generalize (wfB b); intros Hb.
    induction Hb as [b Hb IHb].
    constructor. intros [a' b'] Hlex.
    destruct Hlex as [Hlt | [Heq Hlt]]; simpl in *.
    - apply IHa. exact Hlt.
    - subst a'. apply IHb. exact Hlt.
  Qed.
End Lex.

(** The measure is a 4-tuple [(V, n, t, k)] of naturals, associated to the
    right: [nat * (nat * (nat * nat))].  Its order is [lex lt (lex lt (lex lt
    lt))], which is well-founded because [lt] on [nat] is. *)
Definition mu_ty : Type := nat * (nat * (nat * nat)).

Definition mu_lt : mu_ty -> mu_ty -> Prop :=
  lex lt (lex lt (lex lt lt)).

Lemma mu_lt_wf : well_founded mu_lt.
Proof.
  unfold mu_lt.
  apply lex_wf; [ exact lt_wf | ].
  apply lex_wf; [ exact lt_wf | ].
  apply lex_wf; exact lt_wf.
Qed.

(* ===================================================================== *)
(*  §2  The measure components  V, n, t, k                                *)
(* ===================================================================== *)

(** [V] is the size of a skeleton "as the solution sees it": push it through the
    solution's metasubstitution [κ], then through the target context [Θ]'s own
    definitions ([⇓ˢ]).  For a variable subject we use its metasubstitution image
    ([msubst_lookup κ α], a [ptyp]) and the type-level normal form [⇓ᵗ]. *)
Definition Vpskl (Θ : aenv) (κ : metasubst) (P : pskl) : nat :=
  size_pskl (⇓ˢ[Θ] (msubst_pskl κ P)).

Definition Vptyp (Θ : aenv) (κ : metasubst) (A : ptyp) : nat :=
  size_ptyp (⇓ᵗ[Θ] (msubst_ptyp κ A)).

Definition Vvar (Θ : aenv) (κ : metasubst) (α : atom) : nat :=
  size_ptyp (⇓ᵗ[Θ] (msubst_lookup κ α)).

(** The [V] component of the three node kinds (the "pair of skeletons" of the
    design doc §1: consis → [(P,P0)], unify → [(α̂,β̂)], assign → [(P,α̂)]). *)
Definition V_consis (Θ : aenv) (κ : metasubst) (P0 P : pskl) : nat :=
  Vpskl Θ κ P + Vpskl Θ κ P0.
Definition V_unify (Θ : aenv) (κ : metasubst) (α β : atom) : nat :=
  Vvar Θ κ α + Vvar Θ κ β.
Definition V_assign (Θ : aenv) (κ : metasubst) (α : atom) (P : pskl) : nat :=
  Vpskl Θ κ P + Vvar Θ κ α.

(** [Vvar] is [Vptyp] on the variable seen as a type. *)
Lemma Vvar_ptyp : forall Θ κ α,
  Vvar Θ κ α = Vptyp Θ κ (ptyp_var_f α).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  §3a  Homomorphism of [Vpskl] — the consistency-internal V-decreases    *)
(* ===================================================================== *)

(** [⇓ˢ ∘ κ] commutes with every skeleton former, because both [msubst_pskl]s
    do; hence [size_pskl] adds exactly the shape's own node.  These are the
    strict V-decrease facts of design doc §5.1 (Arrow / Forall / UnivGhost /
    Tophole edges). *)
Lemma Vpskl_arrow : forall Θ κ P1 P2,
  Vpskl Θ κ (pskl_arrow P1 P2) = 1 + Vpskl Θ κ P1 + Vpskl Θ κ P2.
Proof. reflexivity. Qed.

Lemma Vpskl_all_syn : forall Θ κ P,
  Vpskl Θ κ (pskl_all_syn P) = 1 + Vpskl Θ κ P.
Proof. reflexivity. Qed.

Lemma Vpskl_tophole : forall Θ κ P,
  Vpskl Θ κ (pskl_tophole P) = 1 + Vpskl Θ κ P.
Proof. reflexivity. Qed.

(** Every skeleton has positive [Vpskl] (its normal form is a non-empty
    skeleton), so a former's component is STRICTLY smaller than the whole. *)
Lemma Vpskl_pos : forall Θ κ P, 1 <= Vpskl Θ κ P.
Proof. intros. unfold Vpskl. apply size_pskl_min. Qed.

Lemma Vpskl_arrow_lt1 : forall Θ κ P1 P2,
  Vpskl Θ κ P1 < Vpskl Θ κ (pskl_arrow P1 P2).
Proof. intros. rewrite Vpskl_arrow. pose proof (Vpskl_pos Θ κ P2). lia. Qed.

Lemma Vpskl_arrow_lt2 : forall Θ κ P1 P2,
  Vpskl Θ κ P2 < Vpskl Θ κ (pskl_arrow P1 P2).
Proof. intros. rewrite Vpskl_arrow. pose proof (Vpskl_pos Θ κ P1). lia. Qed.

Lemma Vpskl_all_syn_lt : forall Θ κ P,
  Vpskl Θ κ P < Vpskl Θ κ (pskl_all_syn P).
Proof. intros. rewrite Vpskl_all_syn. lia. Qed.

Lemma Vpskl_tophole_lt : forall Θ κ P,
  Vpskl Θ κ P < Vpskl Θ κ (pskl_tophole P).
Proof. intros. rewrite Vpskl_tophole. lia. Qed.

(* ===================================================================== *)
(*  §3b  The variable/skeleton bridge — for the cross-edges                *)
(* ===================================================================== *)

(** [ptyp_to_pskl] preserves size (it never adds a node). *)
Lemma size_ptyp_to_pskl : forall A,
  size_pskl (ptyp_to_pskl A) = size_ptyp A.
Proof. induction A; simpl; auto. Qed.

(** A flexible-variable subject is measured identically as a skeleton and as a
    type: this is exactly the pairing that makes [V] constant on the cross-edges
    [Flex]/[FlexL]/[FlexR] (design doc §5.3). *)
Lemma Vpskl_var : forall Θ κ α,
  Vpskl Θ κ (pskl_var_f α) = Vvar Θ κ α.
Proof.
  intros. unfold Vpskl, Vvar. cbn [msubst_pskl].
  rewrite msubst_pskl_ptyp_to_pskl. apply size_ptyp_to_pskl.
Qed.

(** [FlexL]: [consis(Θ0; P0; α̂)] -> [assign(Θ0; ·; α̂; P0)].  [V] is exactly
    preserved (the two skeletons swap roles). *)
Lemma V_flexL : forall Θ κ α P0,
  V_consis Θ κ P0 (pskl_var_f α) = V_assign Θ κ α P0.
Proof. intros. unfold V_consis, V_assign. rewrite Vpskl_var. lia. Qed.

(** [FlexR]: [consis(Θ0; α̂; P)] -> [assign(Θ0; ·; α̂; P)]. *)
Lemma V_flexR : forall Θ κ α P,
  V_consis Θ κ (pskl_var_f α) P = V_assign Θ κ α P.
Proof. intros. unfold V_consis, V_assign. rewrite Vpskl_var. lia. Qed.

(** [Flex]: [consis(Θ0; β̂; α̂)] -> [unify(Θ0; α̂; β̂)]. *)
Lemma V_flex : forall Θ κ α β,
  V_consis Θ κ (pskl_var_f β) (pskl_var_f α) = V_unify Θ κ α β.
Proof. intros. unfold V_consis, V_unify. rewrite !Vpskl_var. lia. Qed.

(* ===================================================================== *)
(*  §3c  V-CONSTANCY under (M1) and (M2) — the back-edges and Arrow's 2nd  *)
(* ===================================================================== *)

(** (M1) [Vpskl] is invariant under passing an [a_inc_equiv]alent
    metasubstitution — this is what makes [Arrow]'s SECOND premise (which runs
    at the extended [Θ1] with [κ1 ≡ κ] on [Θ0]) leave [V] untouched, so the
    context-blow-up of design doc §3.1 is simply not measured. *)
Lemma Vpskl_inc_equiv : forall Θ0 κ1 κ2 Θ P,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  a_wf_aenv Θ0 -> a_wf_aenv Θ -> a_scope_pskl Θ0 P ->
  Vpskl Θ κ1 P = Vpskl Θ κ2 P.
Proof.
  intros. unfold Vpskl. eapply a_inc_equiv_downarrow_pskl_size; eauto.
Qed.

Lemma Vptyp_inc_equiv : forall Θ0 κ1 κ2 Θ A,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  a_wf_aenv Θ0 -> a_wf_aenv Θ -> a_wf_ptyp Θ0 A ->
  Vptyp Θ κ1 A = Vptyp Θ κ2 A.
Proof.
  intros. unfold Vptyp. eapply a_inc_equiv_downarrow_ptyp_size; eauto.
Qed.

(** (M2) The BACK-EDGE move [α[τ/α1̂] ↦ α], with the outer metasubstitution
    dropping its head [α1̂ ↦ τ'].  [V] is exactly preserved — the back-edge merely
    unfolds a definition the solution had already unfolded ([Flex-Flex-Assign],
    [Assign-Assign], design doc §5.4).  The [≡ᵗ] premise is [a_inc__flex_def]'s. *)
Lemma Vpskl_backedge : forall Θ κ0 α1 τ τ' P,
  a_wf_aenv Θ ->
  Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) ->
  Vpskl Θ κ0 (subst_pskl_in_pskl (ptyp_to_pskl τ) α1 P)
  = Vpskl Θ ((α1, τ') :: κ0) P.
Proof.
  intros. unfold Vpskl. eapply downarrow_subst_pskl_size; eauto.
Qed.

Lemma Vvar_backedge : forall Θ κ0 α1 τ τ' α,
  a_wf_aenv Θ ->
  Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) ->
  Vptyp Θ κ0 (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))
  = Vptyp Θ ((α1, τ') :: κ0) (ptyp_var_f α).
Proof.
  intros. unfold Vptyp. eapply downarrow_subst_ptyp_size; eauto.
Qed.

(* ===================================================================== *)
(*  §3d  Opening by a rigid variable is invisible to V — the Forall edges  *)
(* ===================================================================== *)

(** [ptyp_to_pskl] carries local closure. *)
Lemma ptyp_to_pskl_lc : forall A, lc_ptyp A -> lc_pskl (ptyp_to_pskl A).
Proof.
  induction 1; simpl.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh α.
    apply lc_pskl_all_syn_exists with (α1 := α).
    rewrite <- ptyp_to_pskl_open. auto.
Qed.

(** [msubst_pskl] commutes with recursive opening when the map's images are
    locally closed (they have no bound variable to be captured). *)
Lemma msubst_pskl_open_rec_lc : forall κ,
  msubst_lc κ ->
  forall P P' k,
  msubst_pskl κ (open_pskl_wrt_pskl_rec k P' P)
  = open_pskl_wrt_pskl_rec k (msubst_pskl κ P') (msubst_pskl κ P).
Proof.
  intros κ Hlc P;
    induction P as [ | n | α | P1 IH1 P2 IH2 | P0 IH0 | | P0 IH0 ];
    intros P' k; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - symmetry.
    apply open_pskl_wrt_pskl_rec_degree_pskl_wrt_pskl.
    apply degree_pskl_wrt_pskl_O.
    apply degree_pskl_wrt_pskl_of_lc_pskl.
    apply ptyp_to_pskl_lc. apply Hlc.
Qed.

Lemma msubst_pskl_open_lc : forall κ P α,
  msubst_lc κ ->
  α `notin` dom κ ->
  msubst_pskl κ (open_pskl_wrt_pskl P (pskl_var_f α))
  = open_pskl_wrt_pskl (msubst_pskl κ P) (pskl_var_f α).
Proof.
  intros κ P α Hlc Hα. unfold open_pskl_wrt_pskl.
  rewrite (msubst_pskl_open_rec_lc Hlc P (pskl_var_f α) 0).
  cbn [msubst_pskl]. rewrite msubst_lookup_notin by exact Hα.
  reflexivity.
Qed.

(** [ForallInh]/[ForallSyn]/[UnivGhost1] open the body by a FRESH RIGID [α]
    added to the context.  [⇓] ignores the rigid entry ([aenv_msubst_tvar]) and
    [κ] does not touch [α] ([α ∉ dom κ]), so opening changes neither [⇓ˢ ∘ κ] nor
    the size — [V] is unchanged (design doc §4.3).  Hence the body's [V] is
    STRICTLY below the [all_syn]/[tophole]-headed parent's. *)
Lemma Vpskl_open : forall Θ κ P α,
  a_wf_aenv Θ ->
  msubst_lc κ ->
  α `notin` dom κ ->
  α `notin` dom Θ ->
  Vpskl Θ κ (open_pskl_wrt_pskl P (pskl_var_f α)) = Vpskl Θ κ P.
Proof.
  intros Θ κ P α Hwf Hlcκ Hακ HαΘ. unfold Vpskl.
  assert (HαΘ' : α `notin` dom (aenv_msubst Θ))
    by (pose proof (dom_aenv_msubst Θ); clear - HαΘ H; fsetdec).
  rewrite msubst_pskl_open_lc by assumption.
  rewrite (msubst_pskl_open_lc (κ := aenv_msubst Θ));
    [ apply size_pskl_open_pskl_wrt_pskl_var
    | apply aenv_msubst_lc; exact Hwf
    | exact HαΘ' ].
Qed.

(* ===================================================================== *)
(*  §4  The STUCK-CHECK (design doc §9.2 — the paper gap)                 *)
(* ===================================================================== *)

(** A metasubstitution never ERASES a free variable outside its domain: if
    [α ∉ dom κ] and [α ∈ ftv(P)] then [α ∈ ftv(κP)].  ([κ] can only REPLACE the
    variables it is defined on; everything else survives verbatim.) *)
Lemma msubst_pskl_ftv_notin_dom : forall κ P α',
  α' `notin` dom κ ->
  α' `in` ftvar_in_pskl P ->
  α' `in` ftvar_in_pskl (msubst_pskl κ P).
Proof.
  intros κ P;
    induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros α' Hα Hin; simpl in *.
  - clear - Hin; fsetdec.
  - clear - Hin; fsetdec.
  - (* pskl_var_f β : Hin forces α' = β, and β ∉ dom κ so κ leaves it alone *)
    assert (α' = β) by (clear - Hin; fsetdec); subst β.
    rewrite msubst_lookup_notin by exact Hα. simpl. clear; fsetdec.
  - apply union_1 in Hin. destruct Hin as [Hin | Hin].
    + assert (Hs : α' `in` ftvar_in_pskl (msubst_pskl κ Pa)) by (apply IHa; auto).
      clear - Hs; fsetdec.
    + assert (Hs : α' `in` ftvar_in_pskl (msubst_pskl κ Pb)) by (apply IHb; auto).
      clear - Hs; fsetdec.
  - apply IHall; assumption.
  - clear - Hin; fsetdec.
  - apply IHt; assumption.
Qed.

(** THE STUCK-CHECK, provable half (design doc §9.2, the [Assign-SkipRigid] /
    [Assign-SolveM] "occurs" obligation): a RIGID variable [β] that occurs in the
    walked skeleton [P] is preserved by ANY solution's metasubstitution [κ] into
    [Θ] — [β ∈ ftv(κP)].

    This is the "[β] is not erased" ingredient.  [a_inc] keeps a rigid variable
    rigid, so it never enters [κ]'s domain ([a_inc_tvar_notin_dom]); a variable
    [κ] does not act on survives verbatim ([msubst_pskl_ftv_notin_dom]).

    [paper-gap] The FULL not-stuck argument (that the assignment walk never
    reaches a rigid head [β ∈ ftv(P)], for which there is NO rule) closes the
    contradiction from here as follows — the two remaining ingredients are NOT
    supplied in this file (see the report / docs/PAPER-GAPS.md §9.2):

      (i)  [β ∉ ftv(κα̂)]: at the stuck head [β] is ABOVE [α̂] in the walked
           context, so [a_inc] peels [β] (via [a_inc__tvar]) before reaching
           [α̂]; hence [κα̂] is well-formed in a target BELOW [β] and cannot
           mention it.  Needs an [a_inc]-position / target-wf lemma.
      (ii) [β ∈ ftv(κα̂)]: the assignment solution's JOIN
           [empty ⨟ Θ ⊢ₛᵃ ⌊κP⌋ ∼ syn(κα̂)] against the MONOTYPE [κα̂]
           ([a_inc_lookup_mono]) transports (via [consis_refine_mono_tyequiv],
           prop_mono_bridge.v) to [κP ≡ᵗ κα̂]; combined with [β ∈ ftv(κP)]
           (this lemma) it should force [β ∈ ftv(κα̂)].  The subtlety flagged in
           the report: [≡ᵗ]'s [flex_def] rule is NOT rigid-ftv-preserving in
           general, so (ii) needs a dedicated "rigid ftv survives [≡ᵗ] into a
           definition-free-below-[β] target" lemma, not a bare [≡ᵗ] rewrite.

    (i) and (ii) contradict, so the stuck head is unreachable.  The clean,
    self-contained half — that the solution does not erase [β] — is [Qed]'d here. *)
Lemma rigid_survives_solution : forall Θ1 κ Θ β P,
  κ ∷ Θ1 ⊑ Θ ->
  a_wf_aenv Θ1 ->
  binds β abind_tvar Θ1 ->
  β `in` ftvar_in_pskl P ->
  β `in` ftvar_in_pskl (msubst_pskl κ P).
Proof.
  intros Θ1 κ Θ β P Hinc Hwf Hb Hin.
  apply msubst_pskl_ftv_notin_dom; [ | exact Hin ].
  eapply a_inc_tvar_notin_dom; eauto.
Qed.

(* ##################################################################### *)
(*  PART B — HELPER LEMMAS (formerly algo/prop_consis_complete.v).         *)
(* ##################################################################### *)

(** HELPER LEMMAS for the consistency completeness development.

    HISTORY.  This file originally hosted the standalone 28-case mutual
    OPTIMALITY bundle ([a_assign_unify_consis_optimal], Admitted) together
    with the problem/solution/optimality definitions it was stated against.
    That development is SUPERSEDED: completeness AND optimality are proved
    together by the μ-measure bundle in algo/prop_consis_complete.v
    ([complete_mu], [a_consis_complete_thm] — all Qed, axiom-free), whose
    fused statement is the paper's (full-algo-spec.tex:1476-1519).  The
    Admitted bundle, its corollaries, the problem/solution definitions, and
    the OPT-only helpers ([skip_tm_var_case], [consis_tophole_solution_inv],
    [consis_refine_mono_tyequiv_gen], the [*_optimal_post] motives) were
    removed 2026-07-18; see git history.  The machine-checked falsity of
    optimality under SYNTACTIC binder middles (and its resolution by the
    GundryMM10 §3.1 semantic entries adopted in def_meta.v) is recorded in
    docs/PAPER-GAPS.md and sections/appendices/optimality-cex.tex.

    What remains are the Qed helpers the μ-bundle imports. *)

(* ---- downarrow SCOPING + the join-grounding crux (GMM Lemma 2.6, step 2) ---- *)
(*  ⇓ᵗ[Θ] of a type stays inside any def-closed set containing its ftv; and    *)
(*  (THE CRUX) a mono-join uskl(R) ∼ syn(mono C) forces ⇓ˢ[Θ]R scoped to any    *)
(*  def-closed D that scopes C — so the walked payload downarrows into the      *)
(*  sub-target.  Holes contribute no ftv; the ∀/inh cases cannot fire (C mono). *)


Lemma join_pskl_downarrow_mono_scoped : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  a_wf_aenv Θ ->
  forall P0 A D,
    R = pskl_to_uskl P0 ->
    Q = ptyp_to_bskl_syn A -> mono_ptyp A ->
    (forall α τ, binds α (abind_flex_mono_def τ) Θ -> α `in` D -> ftvar_in_ptyp τ [<=] D) ->
    ftvar_in_ptyp A [<=] D ->
    ftvar_in_pskl (⇓ˢ[ Θ ] P0) [<=] D.
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc;
    intros P0 C0 D HeqS HeqC HmC0 Hcl HCD;
    unfold ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct P0; simpl in HeqS; try discriminate.
    simpl. clear; fsetdec.
  - (* var *)
    destruct P0; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    simpl. rewrite ftvar_in_ptyp_to_pskl.
    match goal with
    | |- context[msubst_lookup ?r ?α] =>
        replace (msubst_lookup r α) with (⇓ᵗ[ Θ ] (ptyp_var_f α)) by reflexivity
    end.
    apply downarrow_ftv_closed;
      [ exact Hwf | simpl; clear - HCD; simpl in HCD; fsetdec | exact Hcl ].
  - (* arrow *)
    destruct P0 as [ | n | α | S01 S02 | S0a | | S0b ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    inversion HmC0 as [ | | ? ? HmC1 HmC2 ]; subst.
    simpl. intros α2 Hα2.
    apply union_1 in Hα2. destruct Hα2 as [HZl | HZr].
    + apply (IHHc1 Hwf S01 C1 D eq_refl eq_refl HmC1 Hcl
               ltac:(clear - HCD; simpl in HCD; fsetdec) α2 HZl).
    + apply (IHHc2 Hwf S02 C2 D eq_refl eq_refl HmC2 Hcl
               ltac:(clear - HCD; simpl in HCD; fsetdec) α2 HZr).
  - (* forall_inh_tagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_inh_untagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_syn_tagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_syn *) destruct HmC0; simpl in HeqC; discriminate.
  - (* ghostg *) destruct HmC0; simpl in HeqC; discriminate.
  - (* topholeg *) destruct HmC0; simpl in HeqC; discriminate.
  - (* hole : subject is a ghost hole, ⇓ contributes no ftv *)
    destruct P0; simpl in HeqS; try discriminate.
    simpl. clear; fsetdec.
  - (* tophole *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_inh *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_drop *)
    destruct P0 as [ | | | | | | S0t ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl. apply (IHHc Hwf S0t C0 D eq_refl eq_refl HmC0 Hcl HCD).
  - (* flex_l : subject is a defined flexible *)
    destruct P0 as [ | | αv | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) αv = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk.
    rewrite <- msubst_pskl_ptyp_to_pskl.
    apply (IHHc Hwf (ptyp_to_pskl τ) C0 D
             (eq_sym (ptyp_to_uskl_syn_eq τ)) eq_refl HmC0 Hcl HCD).
  - (* flex_r : join is a defined flexible *)
    destruct C0; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hτcl : ftvar_in_ptyp τ [<=] D).
    { eapply Hcl; [ exact H | ].
      clear - HCD; simpl in HCD; fsetdec. }
    apply (IHHc Hwf P0 τ D eq_refl eq_refl Hmτ Hcl Hτcl).
Qed.


(* ===================================================================== *)
(*  CONTEXT-STRENGTHENING for the join (ad_pat_consis) and skeleton-wf     *)
(*  (a_wf_pskl) judgments — the SkipRigid / SkipTmVar walk cases move    *)
(*  the competing join from the grown target down to the sub-target.       *)
(* ===================================================================== *)


Lemma a_wf_pskl_strengthen : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall Θ', uniq Θ ->
  (forall x, x `in` Δ -> x `notin` dom Θ) ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall α, α `in` ftvar_in_pskl P -> α `in` Δ \/ α `in` dom Θ') ->
  Θ' ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H; induction H; intros Θ' Hu Hdisj Hsub Hsc.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    assert (HXin : α `in` ftvar_in_pskl (pskl_var_f α)) by (simpl; fsetdec).
    destruct (Hsc α HXin) as [HΔ | Hd]; [ left; exact HΔ | ].
    destruct H as [HΔ | Htv]; [ left; exact HΔ | ].
    right. eapply a_binds_tvar_strengthen; eauto.
  - apply a_wf_pskl__arrow.
    + apply IHa_wf_pskl1; auto. intros α Hα. apply Hsc. simpl. fsetdec.
    + apply IHa_wf_pskl2; auto. intros α Hα. apply Hsc. simpl. fsetdec.
  - apply a_wf_pskl__all with (L := L `union` dom Θ `union` dom Θ' `union` Δ).
    intros α Hα. apply H0.
    + clear - Hα; fsetdec.
    + exact Hu.
    + assert (HxnΘ : α `notin` dom Θ) by (clear - Hα; fsetdec).
      intros y Hy. destruct (y == α) as [-> | Hyne];
        [ exact HxnΘ | apply Hdisj; clear - Hy Hyne; fsetdec ].
    + exact Hsub.
    + intros β Hβ.
      destruct (β == α) as [-> | Hne]; [ left; clear; fsetdec | ].
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hup.
      assert (HYP : β `in` ftvar_in_pskl P) by (simpl in Hup; clear - Hβ Hup Hne; fsetdec).
      destruct (Hsc β HYP) as [HΔ | Hd]; [ left; clear - HΔ; fsetdec | right; exact Hd ].
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; [ exact H | ].
    apply IHa_wf_pskl; auto.
    + intros y Hy; clear - Hy; fsetdec.
    + intros α Hα. right.
      pose proof (a_wf_pskl_ftv_tvarish H0 Hα) as Htv.
      assert (HxΘ : α `in` dom Θ).
      { destruct Htv as [He | Ht]; [ clear - He; fsetdec | ].
        destruct Ht as [Hb|[Hb|[τ Hb]]]; apply binds_In in Hb; exact Hb. }
      assert (HXtop : α `in` ftvar_in_pskl (pskl_tophole P)) by (simpl; exact Hα).
      destruct (Hsc α HXtop) as [HΔ | Hd]; [ | exact Hd ].
      exfalso. apply (Hdisj α HΔ). exact HxΘ.
Qed.


Ltac str_forall H0 Hu Hwf' Hsub HscS HscQ Rr Qq α Hα openU openB :=
  apply H0;
  [ clear - Hα; fsetdec
  | simpl_env; apply uniq_push; [ exact Hu | clear - Hα; fsetdec ]
  | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]
  | apply binds_sub_cons with (e := (α ~ abind_tvar)); exact Hsub
  | intros β Hβ;
    pose proof (openU Rr (uskl_var_f α)) as HupU; simpl in HupU;
    destruct (β == α) as [-> | Hne]; [ simpl; clear; fsetdec | ];
    simpl; apply add_2; apply HscS; clear - Hβ HupU Hne; fsetdec
  | intros β Hβ;
    pose proof (openB Qq (bskl_var_f α)) as HupB; simpl in HupB;
    destruct (β == α) as [-> | Hne]; [ simpl; clear; fsetdec | ];
    simpl; apply add_2; apply HscQ; clear - Hβ HupB Hne; fsetdec ].

Lemma ad_pat_consis_strengthen : forall Ψ Θ R' Q,
  Ψ ⨟ Θ ⊢ₛᵃ R' ∼ Q ->
  forall Θ', uniq Θ -> a_wf_aenv Θ' ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall α0, α0 `in` ftvar_in_uskl R' -> α0 `in` dom Θ') ->
  (forall α0, α0 `in` ftvar_in_bskl Q -> α0 `in` dom Θ') ->
  Ψ ⨟ Θ' ⊢ₛᵃ R' ∼ Q.
Proof.
  intros Ψ Θ R' Q H; induction H;
    intros Θ' Hu Hwf' Hsub HscS HscQ; simpl in *.
  - apply ad_pat_consis__unit; auto.
  - apply ad_pat_consis__var; [ assumption | ].
    eapply a_binds_tvar_strengthen;
      [ eassumption | exact Hu | exact Hsub | apply HscS; fsetdec ].
  - eapply ad_pat_consis__arrow; [ | | exact H1 ].
    + apply IHad_pat_consis1; auto; intros α0 Hα0;
        solve [ apply HscS; fsetdec | apply HscQ; fsetdec ].
    + apply IHad_pat_consis2; auto; intros α0 Hα0;
        solve [ apply HscS; fsetdec | apply HscQ; fsetdec ].
  - eapply ad_pat_consis__forall_inh_tagged
      with (L := L `union` dom Θ `union` dom Θ'); [ | exact H1 ].
    intros α0 Hα0.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q α0 Hα0
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_inh_untagged
      with (L := L `union` dom Θ `union` dom Θ').
    intros α0 Hα0.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q α0 Hα0
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_syn_tagged
      with (L := L `union` dom Θ `union` dom Θ').
    intros α0 Hα0.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q α0 Hα0
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_syn
      with (L := L `union` dom Θ `union` dom Θ').
    intros α0 Hα0.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q α0 Hα0
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - apply ad_pat_consis__ghostg; auto.
  - apply ad_pat_consis__topholeg. apply IHad_pat_consis; auto.
  - apply ad_pat_consis__hole; auto.
    eapply a_wf_pskl_strengthen; [ exact H0 | exact Hu | intros y Hy; clear - Hy; fsetdec | exact Hsub | ].
    intros α0 Hα0. right. apply HscQ.
    pose proof (ftvar_in_bskl_inh P) as Hb. clear - Hα0 Hb. fsetdec.
  - apply ad_pat_consis__tophole. apply IHad_pat_consis; auto.
  - eapply ad_pat_consis__tophole_inh
      with (L := L `union` dom Θ `union` dom Θ').
    intros α0 Hα0.
    apply H0.
    + clear - Hα0; fsetdec.
    + simpl_env; apply uniq_push; [ exact Hu | clear - Hα0; fsetdec ].
    + apply a_wf_aenv__tvar; [ clear - Hα0; fsetdec | exact Hwf' ].
    + apply binds_sub_cons with (e := (α0 ~ abind_tvar)); exact Hsub.
    + intros β Hβ. simpl in Hβ. simpl.
      apply add_2. apply HscS; exact Hβ.
    + intros β Hβ.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f α0)) as HupB;
        simpl in HupB.
      destruct (β == α0) as [-> | Hne]; [ simpl; clear; fsetdec | ].
      simpl. apply add_2. apply HscQ; clear - Hβ HupB Hne; fsetdec.
  - apply ad_pat_consis__tophole_drop. apply IHad_pat_consis; auto.
  - eapply ad_pat_consis__flex_l.
    + eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscS; fsetdec ].
    + apply IHad_pat_consis; auto.
      intros α0 Hα0.
      assert (Hbd' : binds α (abind_flex_mono_def τ) Θ')
        by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscS; fsetdec ]).
      assert (Hwfτ : a_wf_ptyp Θ' τ) by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hbd' ]).
      pose proof (a_wf_ptyp_ftv_dom' Hwfτ) as Hftv.
      pose proof (ftvar_in_uskl_ptyp_syn τ) as Hco.
      clear - Hα0 Hftv Hco. fsetdec.
  - eapply ad_pat_consis__flex_r.
    + eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscQ; fsetdec ].
    + apply IHad_pat_consis; auto.
      intros α0 Hα0.
      assert (Hbd' : binds α (abind_flex_mono_def τ) Θ')
        by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscQ; fsetdec ]).
      assert (Hwfτ : a_wf_ptyp Θ' τ) by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hbd' ]).
      pose proof (a_wf_ptyp_ftv_dom' Hwfτ) as Hftv.
      pose proof (ftvar_in_bskl_ptyp_syn τ) as Hco.
      clear - Hα0 Hftv Hco. fsetdec.
Qed.


(* ===================================================================== *)
(*  The composed factoring, assembled from CONGRUENCE + TRANSITIVITY.      *)
(* ===================================================================== *)

(** Monotype precision recovery, for the AXIOM nodes (Unit/Rigid) whose
    algorithmic output is a CONCRETE monotype painting rather than a flexible
    [α̂].  Same [consis_mono_join] core as [consis_precise_core], but the subject
    is the raw painting [ptyp_to_pskl A] instead of [msubst_bskl ζ α̂]. *)
Lemma consis_precise_mono_join : forall Θ Δ A Qb,
  a_wf_aenv Θ ->
  mono_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  empty ⨟ Θ ⊢ₛᵃ (ptyp_to_uskl_syn A) ∼ Qb ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (ptyp_to_pskl A) ⊑ (bskl_to_pskl Qb).
Proof.
  intros Θ Δ A Qb Hwf HmA Hvis Hjoin.
  destruct (consis_mono_join Hjoin Hwf (A := A) eq_refl HmA) as [C [HmC [HQb Heq]]].
  unfold ad_precise.
  rewrite (ptyp_to_bskl_inh_syn_eq HmA).
  subst Qb.
  replace (bskl_to_pskl (ptyp_to_bskl_syn C)) with (ptyp_to_pskl C).
  2:{ unfold ptyp_to_bskl_syn. rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity. }
  rewrite (ptyp_to_bskl_inh_syn_eq HmC).
  apply tyequiv_mono_refine_syn; auto.
Qed.

(** Colour erasure commutes with metasubstitution. *)
Lemma bskl_to_pskl_msubst_bskl : forall κ Q,
  bskl_to_pskl (msubst_bskl κ Q) = msubst_pskl κ (bskl_to_pskl Q).
Proof.
  intros κ Q; induction Q; simpl; try reflexivity.
  - rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity.
  - rewrite IHQ1, IHQ2. reflexivity.
  - rewrite IHQ. reflexivity.
  - rewrite IHQ. reflexivity.
  - rewrite IHQ. reflexivity.
Qed.

(** A join whose SUBJECT is the ghost hole forces the target painting to be
    fully INHERITED: it is invariant under erase-then-reinherit.  (The only
    two rules that can conclude [uskl_hole ∼ Qb] are [__hole], whose target is
    an [inh] painting, and [__flex_r], whose target is a defined-flex variable
    — both fixed points of [inh ∘ erase].) *)
Lemma consis_hole_target_inh : forall Ψ Θ Qb,
  Ψ ⨟ Θ ⊢ₛᵃ uskl_hole ∼ Qb ->
  pskl_to_bskl_inh (bskl_to_pskl Qb) = Qb.
Proof.
  intros Ψ Θ Qb H.
  remember uskl_hole as R eqn:HR.
  induction H; try discriminate HR.
  - rewrite bskl_to_pskl_pskl_to_bskl_inh. reflexivity.
  - reflexivity.
Qed.


(** A guarded consistency subject has a guarded target.  Stated with an
    explicit local-closure premise on the target so the Arrow case needs no
    separate regularity development.  A left-side defined-flex lookup recurs
    on its definition; a right-side lookup lands at a guarded variable. *)
Lemma ad_pat_consis_guarded_r : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  a_wf_aenv Θ ->
  forall P,
    R = pskl_to_uskl P ->
    guarded_pskl P ->
    lc_bskl Q ->
    guarded_bskl Q.
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc; intros P0 HeqS Hg Hlc;
    try solve [ destruct P0; simpl in HeqS; try discriminate;
                inversion Hg ].
  - destruct P0; simpl in HeqS; try discriminate.
    auto with frost.
  - destruct P0; simpl in HeqS; try discriminate.
    auto with frost.
  - destruct P0; simpl in HeqS; try discriminate.
    inversion Hlc; subst. apply guarded_bskl__arrow; assumption.
  - (* flex_l *)
    destruct P0; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    apply IHHc with (P := ptyp_to_pskl τ); auto.
    + symmetry. apply ptyp_to_uskl_syn_eq.
    + apply mono_ptyp_to_pskl_guarded.
      eapply a_wf_aenv_binds_def_mono; eauto.
  - (* flex_r *) apply guarded_bskl__var.
Qed.

(** If a tophole subject is refined to a guarded target, the tophole must have
    been removed.  Target-side flexible aliases are peeled recursively and
    folded back after the removal. *)
Lemma ad_refine_syn_f_tophole_guarded_inv : forall F Θ Δ Q Q',
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ (bskl_tophole Q) Q' ->
  guarded_bskl Q' ->
  ad_refine_syn_f F Θ Δ Q Q'.
Proof.
  intros F Θ Δ Q Q' Hwf Hr.
  remember (bskl_tophole Q) as Qt eqn:HeqQt.
  induction Hr; intros Hg; try discriminate HeqQt.
  - inversion HeqQt; subst. exact Hr.
  - inversion Hg.
  - inversion Hg.
  - inversion HeqQt; subst.
    eapply ad_refine_syn_f__flex_r; [ exact H | ].
    apply IHHr; [ exact Hwf | reflexivity | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_refine_pskl_f_tophole_guarded_inv : forall F Θ Δ P P',
  a_wf_aenv Θ ->
  ad_refine_pskl_f F Θ Δ (pskl_tophole P) P' ->
  guarded_pskl P' ->
  ad_refine_pskl_f F Θ Δ P P'.
Proof.
  intros F Θ Δ P P' Hwf Hr.
  remember (pskl_tophole P) as Pt eqn:HeqPt.
  induction Hr; intros Hg; try discriminate HeqPt.
  - inversion HeqPt; subst. exact Hr.
  - inversion Hg.
  - inversion Hg.
  - inversion HeqPt; subst.
    eapply ad_refine_pskl_f__flex_r; [ exact H | ].
    apply IHHr; [ exact Hwf | reflexivity | ].
    apply mono_ptyp_to_pskl_guarded.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** A consistency derivation from a tophole to a guarded target must use the
    tophole-dropping path.  As above, a target-side defined-flex alias is
    unfolded recursively and folded back afterwards. *)
Lemma ad_pat_consis_tophole_guarded_inv : forall Ψ Θ P Q,
  a_wf_aenv Θ ->
  Ψ ⨟ Θ ⊢ₛᵃ (uskl_tophole (pskl_to_uskl P)) ∼ Q ->
  guarded_pskl P ->
  guarded_bskl Q ->
  Ψ ⨟ Θ ⊢ₛᵃ (pskl_to_uskl P) ∼ Q.
Proof.
  intros Ψ Θ P Q Hwf Hc.
  remember (uskl_tophole (pskl_to_uskl P)) as R eqn:HeqS.
  induction Hc; intros HgP HgQ; try discriminate HeqS.
  - inversion HgQ.
  - inversion HgQ.
  - inversion HeqS; subst. exact Hc.
  - inversion HeqS; subst.
    eapply ad_pat_consis__flex_r; [ exact H | ].
    apply IHHc; [ exact Hwf | reflexivity | exact HgP | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_refine_syn_f_tophole_keep_inv : forall F Θ Δ Q' Q,
  a_wf_aenv Θ ->
  guarded_bskl Q' ->
  ad_refine_syn_f F Θ Δ (bskl_tophole Q') (bskl_tophole Q) ->
  ad_refine_syn_f F Θ Δ Q' Q.
Proof.
  intros F Θ Δ Q' Q Hwf Hg Hr.
  inversion Hr; subst; try discriminate.
  - match goal with
    | Hsub : ad_refine_syn_f _ _ _ Q' (bskl_tophole Q) |- _ =>
        pose proof (ad_refine_syn_f_guarded_r Hwf Hsub Hg) as Hbad;
        inversion Hbad
    end.
  - assumption.
Qed.

Lemma ad_refine_pskl_f_tophole_keep_inv : forall F Θ Δ P P',
  a_wf_aenv Θ ->
  guarded_pskl P ->
  ad_refine_pskl_f F Θ Δ (pskl_tophole P) (pskl_tophole P') ->
  ad_refine_pskl_f F Θ Δ P P'.
Proof.
  intros F Θ Δ P P' Hwf Hg Hr.
  inversion Hr; subst; try discriminate.
  - match goal with
    | Hsub : ad_refine_pskl_f _ _ _ P (pskl_tophole P') |- _ =>
        pose proof (ad_refine_pskl_f_guarded_r Hwf Hsub Hg) as Hbad;
        inversion Hbad
    end.
  - assumption.
Qed.

(* The join is invariant under ⇓-normalizing the SUBJECT, when the RHS is a
   monotype (mono C prunes every ∀/tophole_inh case, exactly as in
   join_pskl_downarrow_mono_scoped).  This transfers the assign-node join
   (subject msubst κ P, RHS syn(mono κα)) onto the ⇓-normalized subject,
   which [join_pskl_downarrow_mono_scoped] shows is scoped to the
   sub-target Θ'.  (Consumed by the ⇓-truncation walk cases of the
   μ-bundle in prop_completeness_consis.v (PART B).) *)
Lemma consis_downarrow_subject : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q ->
  a_wf_aenv Θ ->
  forall P0 A,
    R = pskl_to_uskl P0 ->
    Q = ptyp_to_bskl_syn A -> mono_ptyp A ->
    ad_pat_consis Ψ Θ (pskl_to_uskl (⇓ˢ[ Θ ] P0)) Q.
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc;
    intros P0 C0 HeqS HeqC HmC0;
    unfold ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct P0; simpl in HeqS; try discriminate.
    simpl. apply ad_pat_consis__unit; assumption.
  - (* var α : uniform ⇓(var α) ≡ var α route (covers tvar/flex_mono/flex_def) *)
    destruct P0 as [ | | αp | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | αc | | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    simpl.
    replace (ptyp_to_pskl (msubst_lookup (aenv_msubst Θ) αc))
       with (ptyp_to_pskl (⇓ᵗ[ Θ ] (ptyp_var_f αc))) by reflexivity.
    assert (Hwfx : a_wf_ptyp Θ (ptyp_var_f αc)) by (apply a_wf_ptyp__var; exact H0).
    assert (Hmono_x : mono_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f αc)))
      by (apply mono_downarrow; [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]).
    assert (Hwf_x : a_wf_ptyp Θ (⇓ᵗ[ Θ ] (ptyp_var_f αc)))
      by (apply a_wf_ptyp_downarrow_mono; [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]).
    assert (Hvis : forall β, β `in` ftvar_in_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f αc)) ->
                   a_binds_tvar β Θ)
      by (intros β Hβ; eapply a_wf_ptyp_ftv_tvarish; [ exact Hwf_x | exact Hβ ]).
    assert (Heqd : Θ ⊢ (⇓ᵗ[ Θ ] (ptyp_var_f αc)) ≡ᵗ (ptyp_var_f αc)).
    { apply a_tyequiv__sym.
      apply a_tyequiv_to_downarrow_mono;
        [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]. }
    destruct (tyequiv_mono_consis_transport_q Heqd Hwf Hmono_x Hvis) as [_ Hfwd].
    rewrite ptyp_to_uskl_syn_eq.
    change (bskl_var_f αc) with (ptyp_to_bskl_syn (ptyp_var_f αc)).
    apply Hfwd.
    eapply ad_pat_consis_psi_cong;
      [ apply consis_mono_refl; [ exact Hmono_x | exact Hvis ]
      | fsetdec ].
  - (* arrow *)
    destruct P0 as [ | | | S01 S02 | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    inversion HmC0 as [ | | ? ? HmC1 HmC2 ]; subst.
    simpl.
    apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ apply (IHHc1 Hwf S01 C1 eq_refl eq_refl HmC1)
      | apply (IHHc2 Hwf S02 C2 eq_refl eq_refl HmC2)
      | exact H ].
  - (* forall_inh_tagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_inh_untagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_syn_tagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_syn *) destruct HmC0; simpl in HeqC; discriminate.
  - (* ghostg *) destruct HmC0; simpl in HeqC; discriminate.
  - (* topholeg *) destruct HmC0; simpl in HeqC; discriminate.
  - (* hole *)
    destruct P0; simpl in HeqS; try discriminate.
    simpl. apply ad_pat_consis__hole; [ exact H | exact H0 ].
  - (* tophole *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_inh *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_drop *)
    destruct P0 as [ | | | | | | S0t ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl. apply ad_pat_consis__tophole_drop.
    apply (IHHc Hwf S0t C0 eq_refl eq_refl HmC0).
  - (* flex_l : subject is a defined flexible *)
    destruct P0 as [ | | αv | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) αv = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk.
    rewrite <- msubst_pskl_ptyp_to_pskl.
    apply (IHHc Hwf (ptyp_to_pskl τ) C0
             (eq_sym (ptyp_to_uskl_syn_eq τ)) eq_refl HmC0).
  - (* flex_r : join is a defined flexible *)
    destruct C0; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_pat_consis__flex_r with (τ := τ); [ exact H | ].
    apply (IHHc Hwf P0 τ eq_refl eq_refl Hmτ).
Qed.


(* ===================================================================== *)
(*  §1  The three node measures                                           *)
(* ===================================================================== *)

Definition mu_consis (Θ : aenv) (κ : metasubst) (P0 P : pskl)
    (Θ0 : aenv) : mu_ty :=
  (V_consis Θ κ P0 P, (length Θ0, (1, 0))).

Definition mu_unify (Θ : aenv) (κ : metasubst) (α β : atom)
    (Θ0 : aenv) : mu_ty :=
  (V_unify Θ κ α β, (length Θ0, (0, 0))).

Definition mu_assign (Θ : aenv) (κ : metasubst) (α : atom) (P : pskl)
    (Ξ Θ0 : aenv) : mu_ty :=
  (V_assign Θ κ α P, (length Ξ + length Θ0, (0, length Θ0))).

(* ===================================================================== *)
(*  §1b  HYGIENIC PRECISION                                               *)
(*                                                                        *)
(*  The paper's precision [⊑] carries an implicit hole-fill discipline:   *)
(*  fills never mention the ∀-variables in scope (the same EXTERNAL       *)
(*  side-condition family as wf; without it the C-ForallInh cofinite      *)
(*  precision reassembly is unprovable — the [__hole] rule demands the    *)
(*  fill wf at [⨟ ∅], so a fill mentioning the freshly bound variable     *)
(*  kills every renamed instance).  We therefore state the completeness   *)
(*  precision in the hygiene-carrying [_f] form at [F := Δ1 ∪ Δ2] —       *)
(*  exactly the sets the GIVEN refinements [Hrs]/[Hrp] already police —   *)
(*  and recover the paper's plain form by [ad_refine_syn_f_forget].       *)
(* ===================================================================== *)

Definition ad_precise_f (F : atoms) (Θ : aenv) (Δ : atoms)
    (P Q : pskl) : Prop :=
  ad_refine_syn_f F Θ Δ (pskl_to_bskl_inh P) (pskl_to_bskl_inh Q).

Lemma ad_precise_f_forget : forall F Θ Δ P P',
  ad_precise_f F Θ Δ P P' -> Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ P'.
Proof.
  intros * H. apply ad_refine_syn_f_forget in H. exact H.
Qed.

(** Hole-free skeletons: the [__hole] rule can never fire on them, so a
    plain refinement lifts to the [_f] form at ANY [F]. *)
Fixpoint bskl_no_hole (Q : bskl) : Prop :=
  match Q with
  | bskl_unit => True
  | bskl_var_b _ => True
  | bskl_var_f _ => True
  | bskl_arrow Q1 Q2 => bskl_no_hole Q1 /\ bskl_no_hole Q2
  | bskl_all_syn Q0 => bskl_no_hole Q0
  | bskl_all_inh Q0 => bskl_no_hole Q0
  | bskl_hole => False
  | bskl_tophole Q0 => bskl_no_hole Q0
  end.

Fixpoint pskl_no_hole (P : pskl) : Prop :=
  match P with
  | pskl_unit => True
  | pskl_var_b _ => True
  | pskl_var_f _ => True
  | pskl_arrow P1 P2 => pskl_no_hole P1 /\ pskl_no_hole P2
  | pskl_all_syn P0 => pskl_no_hole P0
  | pskl_hole => False
  | pskl_tophole P0 => pskl_no_hole P0
  end.

Lemma bskl_no_hole_open_rec : forall Q α' k,
  bskl_no_hole Q ->
  bskl_no_hole (open_bskl_wrt_bskl_rec k (bskl_var_f α') Q).
Proof.
  induction Q; simpl; intros α' k Hnh; try contradiction; try exact I;
    try solve [ apply IHQ; assumption ];
    try solve [ destruct Hnh; split;
                [ apply IHQ1 | apply IHQ2 ]; assumption ].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; exact I.
Qed.

Lemma bskl_no_hole_open : forall Q α,
  bskl_no_hole Q ->
  bskl_no_hole (open_bskl_wrt_bskl Q (bskl_var_f α)).
Proof. intros. apply bskl_no_hole_open_rec. assumption. Qed.

Lemma ptyp_to_pskl_no_hole : forall A, pskl_no_hole (ptyp_to_pskl A).
Proof. induction A; simpl; tauto. Qed.

Lemma pskl_to_bskl_syn_no_hole : forall P,
  pskl_no_hole P -> bskl_no_hole (pskl_to_bskl_syn P).
Proof. induction P; simpl; tauto. Qed.

Lemma pskl_to_bskl_inh_no_hole : forall P,
  pskl_no_hole P -> bskl_no_hole (pskl_to_bskl_inh P).
Proof. induction P; simpl; tauto. Qed.

Lemma bskl_to_pskl_no_hole : forall Q,
  bskl_no_hole Q -> pskl_no_hole (bskl_to_pskl Q).
Proof. induction Q; simpl; tauto. Qed.

Lemma ptyp_to_bskl_syn_no_hole : forall A,
  bskl_no_hole (ptyp_to_bskl_syn A).
Proof.
  intros. unfold ptyp_to_bskl_syn.
  apply pskl_to_bskl_syn_no_hole, ptyp_to_pskl_no_hole.
Qed.

Lemma msubst_bskl_no_hole : forall ζ Q,
  bskl_no_hole Q -> bskl_no_hole (msubst_bskl ζ Q).
Proof.
  intros ζ Q; induction Q; simpl; intros Hnh; try tauto.
  apply ptyp_to_bskl_syn_no_hole.
Qed.

Lemma ad_refine_syn_f_of_plain_no_hole : forall Θ Δ Q Q',
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ Q' ->
  bskl_no_hole Q ->
  forall F, ad_refine_syn_f F Θ Δ Q Q'.
Proof.
  intros * H; induction H; intros Hnh F; simpl in Hnh.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - destruct Hnh. apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply bskl_no_hole_open; assumption ].
  - destruct Hnh.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L). intros α Hα.
    apply H0; [ exact Hα | exact Hnh ].
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; [ eassumption | ].
    apply IHad_refine_syn. apply ptyp_to_bskl_syn_no_hole.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    apply IHad_refine_syn. exact Hnh.
Qed.

Lemma ftvar_in_pskl_bskl_to_pskl : forall Q,
  ftvar_in_pskl (bskl_to_pskl Q) [=] ftvar_in_bskl Q.
Proof. induction Q; simpl; fsetdec. Qed.

(** F-extension along ftv-avoidance of the TARGET: every hole fill is a
    target subterm, so new [F]-atoms that avoid the target's free names —
    and every definition of the context (the [flex_r] unfolding can route
    the target through a definition) — cannot show up in a fill. *)
Lemma ad_refine_syn_f_fextend_ftv : forall F Θ Δ Q Q',
  ad_refine_syn_f F Θ Δ Q Q' ->
  forall F',
  (forall α1, α1 `in` F' -> α1 `in` F \/
     (α1 `notin` ftvar_in_bskl Q' /\
      (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
         α1 `notin` ftvar_in_ptyp τ))) ->
  ad_refine_syn_f F' Θ Δ Q Q'.
Proof.
  intros * H; induction H; intros F' Hcond; simpl in *.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - apply ad_refine_syn_f__arrow.
    + apply IHad_refine_syn_f1. intros α1 Hα1.
      destruct (Hcond α1 Hα1) as [HinF | [Hf Hd]];
        [ left; exact HinF | right; split; [ | exact Hd ] ].
      clear - Hf. fsetdec.
    + apply IHad_refine_syn_f2. intros α1 Hα1.
      destruct (Hcond α1 Hα1) as [HinF | [Hf Hd]];
        [ left; exact HinF | right; split; [ | exact Hd ] ].
      clear - Hf. fsetdec.
  - apply ad_refine_syn_f__all with (L := L `union` F').
    intros α Hα.
    apply H0; [ clear - Hα; fsetdec | ].
    intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinF | [Hf Hd]];
      [ left; exact HinF | right; split; [ | exact Hd ] ].
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                  P (bskl_var_f α)) as Hup.
    simpl in Hup.
    assert (α1 <> α) by (clear - Hα Hα1; fsetdec).
    clear - Hf Hup H1. fsetdec.
  - apply ad_refine_syn_f__hole; [ | assumption ].
    apply inter_empty_pointwise. intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinF | [Hf Hd]].
    + intro Hc.
      assert (Hin : α1 `in` F ∩ ftvar_in_pskl P)
        by (apply inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec.
    + rewrite ftvar_in_bskl_syn in Hf. exact Hf.
  - apply ad_refine_syn_f__tophole_remove. apply IHad_refine_syn_f.
    exact Hcond.
  - apply ad_refine_syn_f__tophole_fill with (L := L `union` F').
    intros α Hα.
    apply H0; [ clear - Hα; fsetdec | ].
    intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinF | [Hf Hd]];
      [ left; exact HinF | right ].
    split.
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                    P (bskl_var_f α)) as Hup.
      simpl in Hup.
      assert (α1 <> α) by (clear - Hα Hα1; fsetdec).
      clear - Hf Hup H1. fsetdec.
    + intros β τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | exact (Hd β τ Hb') ].
  - apply ad_refine_syn_f__tophole_keep; [ assumption | ].
    apply IHad_refine_syn_f.
    intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinF | [Hf Hd]];
      [ left; exact HinF | right; split; [ | exact Hd ] ].
    clear - Hf. fsetdec.
  - eapply ad_refine_syn_f__flex_l; [ eassumption | ].
    apply IHad_refine_syn_f. exact Hcond.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    apply IHad_refine_syn_f.
    intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinF | [Hf Hd]];
      [ left; exact HinF | right; split; [ | exact Hd ] ].
    rewrite ftvar_in_bskl_ptyp_syn. exact (Hd _ _ H).
Qed.

(** A hole-source Δ2-refinement polices its WHOLE target against rigid
    [F]-atoms: the [__hole] rule checks the fill (= the target) directly,
    and the only other applicable rule, [__flex_r], routes the target
    through a DEFINED (hence non-rigid) variable. *)
Lemma ad_refine_pskl_f_hole_src_target_ftv : forall F Θ Δ Pt,
  ad_refine_pskl_f F Θ Δ pskl_hole Pt ->
  a_wf_aenv Θ ->
  forall α1, α1 `in` F -> binds α1 abind_tvar Θ ->
  α1 `notin` ftvar_in_pskl Pt.
Proof.
  intros * H.
  remember pskl_hole as R eqn:HeqS.
  induction H; intros Hwf α1 HγF Hbγ; try discriminate HeqS.
  - (* __hole : the fill is the target *)
    intro Hc.
    assert (Hin : α1 `in` F ∩ ftvar_in_pskl Q)
      by (apply inter_3; assumption).
    rewrite H in Hin. clear - Hin. fsetdec.
  - (* __flex_r : target is a defined flexible, not the rigid α1 *)
    simpl. intro Hc.
    assert (Heqγ : α1 = α) by (clear - Hc; fsetdec). subst α.
    pose proof (binds_unique _ _ _ _ _ H Hbγ (a_wf_aenv_uniq Hwf)) as Hcon.
    discriminate.
Qed.

(** The syn-side twin: a hole-source Δ1-refinement polices its whole
    target against rigid [F]-atoms. *)
Lemma ad_refine_syn_f_hole_src_target_ftv : forall F Θ Δ Qt,
  ad_refine_syn_f F Θ Δ bskl_hole Qt ->
  a_wf_aenv Θ ->
  forall α1, α1 `in` F -> binds α1 abind_tvar Θ ->
  α1 `notin` ftvar_in_bskl Qt.
Proof.
  intros * H.
  remember bskl_hole as R eqn:HeqS.
  induction H; intros Hwf α1 HγF Hbγ; try discriminate HeqS.
  - (* __hole : the fill is the target *)
    rewrite ftvar_in_bskl_syn.
    intro Hc.
    assert (Hin : α1 `in` F ∩ ftvar_in_pskl P)
      by (apply inter_3; assumption).
    rewrite H in Hin. clear - Hin. fsetdec.
  - (* __flex_r : target is a defined flexible, not the rigid α1 *)
    simpl. intro Hc.
    assert (Heqγ : α1 = α) by (clear - Hc; fsetdec). subst α.
    pose proof (binds_unique _ _ _ _ _ H Hbγ (a_wf_aenv_uniq Hwf)) as Hcon.
    discriminate.
Qed.

(* ===================================================================== *)
(*  §1c  ∀-case transports: weakening / F-extension / Δ↔context moves     *)
(* ===================================================================== *)

(** Free variables of a wf skeleton are scoped by its Δ and context. *)

(** Renaming a Δ-BOUND variable of skeleton well-formedness — the wf twin of
    [ad_precise_rename_delta].  The ∀◇ case is where freshness earns its
    keep: its premise is CLOSED ([Θ ⨟ empty ⊢ₚₛᵃ P]), so β ∉ dom Θ makes β
    fresh for the body and the substitution is a no-op there.

    (Lives here, beside [a_wf_pskl_ftv_dom] which its ∀◇ case needs, so that
    BOTH completeness_look/prop_kit.v and completeness_look/prop_extract.v can see it —
    the two files are independent of each other.) *)

(** ∀-INTRODUCTION FROM ONE INSTANCE — the exists-fresh idiom of DESIGN §4.3
    on the wf judgment.  The algorithmic solve rules now hand their consumers
    ONE instance at their own binder; [a_wf_pskl__all] wants the whole
    cofinite family, and the rename above is what manufactures it. *)
Lemma a_wf_pskl_all_of_one : forall Θ Δ P β,
  Θ ⨟ (add β Δ) ⊢ₚₛᵃ (open_pskl_wrt_pskl P (pskl_var_f β)) ->
  β `notin` dom Θ ->
  β `notin` ftvar_in_pskl P ->
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_all_syn P).
Proof.
  intros Θ Δ P β H HβΘ HβP.
  apply a_wf_pskl__all
    with (L := add β (dom Θ `union` ftvar_in_pskl P `union` Δ)).
  intros α Hα.
  pose proof (@a_wf_pskl_rename_delta Θ (add β Δ)
                (open_pskl_wrt_pskl P (pskl_var_f β)) β α H HβΘ) as Hr.
  rewrite <- (subst_pskl_in_pskl_intro β P (pskl_var_f α) HβP) in Hr.
  eapply a_wf_pskl_delta_mono; [ exact Hr | clear; fsetdec ].
Qed.

(** ∀-ELIMINATION AT A CHOSEN BINDER — the converse move: a consumer that
    must open at ITS OWN β (an exists-fresh rule's binder) gets the instance
    by renaming the family's witness onto β.  No condition on β beyond
    body-freshness: a β already in Δ or in dom Θ is harmless because the
    conclusion's Δ only grows. *)

(** Context weakening (binds-monotone) for the hygienic refinements. *)
Lemma ad_refine_syn_f_weaken_ctx : forall F Θ Δ Q Q',
  ad_refine_syn_f F Θ Δ Q Q' ->
  forall Θ', (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  ad_refine_syn_f F Θ' Δ Q Q'.
Proof.
  intros * H; induction H; intros Θ' Hmon.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Hbt]; [ left; exact HΔ | right ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros α Hα. auto.
  - apply ad_refine_syn_f__hole; [ exact H | ].
    eapply a_wf_pskl_weaken; eassumption.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L). intros α Hα.
    apply H0; [ exact Hα | ].
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
      [ subst; unfold binds; left; reflexivity
      | apply binds_cons_3; apply Hmon; exact Hb' ].
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; [ apply Hmon; eassumption | auto ].
  - eapply ad_refine_syn_f__flex_r; [ apply Hmon; eassumption | auto ].
Qed.

Lemma ad_refine_pskl_f_weaken_ctx : forall F Θ Δ P P',
  ad_refine_pskl_f F Θ Δ P P' ->
  forall Θ', (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  ad_refine_pskl_f F Θ' Δ P P'.
Proof.
  intros * H; induction H; intros Θ' Hmon.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var.
    destruct H as [HΔ | Hbt]; [ left; exact HΔ | right ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
  - apply ad_refine_pskl_f__arrow; auto.
  - apply ad_refine_pskl_f__all with (L := L). intros α Hα. auto.
  - apply ad_refine_pskl_f__hole; [ exact H | ].
    eapply a_wf_pskl_weaken; eassumption.
  - apply ad_refine_pskl_f__tophole_remove; auto.
  - apply ad_refine_pskl_f__tophole_fill with (L := L). intros α Hα.
    apply H0; [ exact Hα | ].
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
      [ subst; unfold binds; left; reflexivity
      | apply binds_cons_3; apply Hmon; exact Hb' ].
  - apply ad_refine_pskl_f__tophole_keep; auto.
  - eapply ad_refine_pskl_f__flex_l; [ apply Hmon; eassumption | auto ].
  - eapply ad_refine_pskl_f__flex_r; [ apply Hmon; eassumption | auto ].
Qed.

(** F-extension by names outside the context: hole fills are wf at their
    local context, so new [F]-atoms outside every reachable context's
    domain never collide with a fill. *)
Lemma ad_refine_syn_f_fextend_dom : forall F Θ Δ Q Q',
  ad_refine_syn_f F Θ Δ Q Q' ->
  forall F', (forall α1, α1 `in` F' -> α1 `in` F \/ α1 `notin` dom Θ) ->
  ad_refine_syn_f F' Θ Δ Q Q'.
Proof.
  intros * H; induction H; intros F' Hcond.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros α Hα. auto.
  - apply ad_refine_syn_f__hole; [ | exact H0 ].
    apply inter_empty_pointwise. intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinF | Hnd].
    + intro Hc.
      assert (Hin : α1 `in` F ∩ ftvar_in_pskl P)
        by (apply inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec.
    + pose proof (a_wf_pskl_ftv_dom H0) as Hsc.
      clear - Hnd Hsc. fsetdec.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L `union` F').
    intros α Hα.
    apply H0; [ clear - Hα; fsetdec | ].
    intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinF | Hnd]; [ left; exact HinF | right ].
    simpl dom.
    assert (α1 <> α) by (clear - Hα Hα1; fsetdec).
    clear - Hnd H1. fsetdec.
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; [ eassumption | auto ].
  - eapply ad_refine_syn_f__flex_r; [ eassumption | auto ].
Qed.

Lemma ad_refine_pskl_f_fextend_dom : forall F Θ Δ P P',
  ad_refine_pskl_f F Θ Δ P P' ->
  forall F', (forall α1, α1 `in` F' -> α1 `in` F \/ α1 `notin` dom Θ) ->
  ad_refine_pskl_f F' Θ Δ P P'.
Proof.
  intros * H; induction H; intros F' Hcond.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var; assumption.
  - apply ad_refine_pskl_f__arrow; auto.
  - apply ad_refine_pskl_f__all with (L := L). intros α Hα. auto.
  - apply ad_refine_pskl_f__hole; [ | exact H0 ].
    apply inter_empty_pointwise. intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinF | Hnd].
    + intro Hc.
      assert (Hin : α1 `in` F ∩ ftvar_in_pskl Q)
        by (apply inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec.
    + pose proof (a_wf_pskl_ftv_dom H0) as Hsc.
      clear - Hnd Hsc. fsetdec.
  - apply ad_refine_pskl_f__tophole_remove; auto.
  - apply ad_refine_pskl_f__tophole_fill with (L := L `union` F').
    intros α Hα.
    apply H0; [ clear - Hα; fsetdec | ].
    intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinF | Hnd]; [ left; exact HinF | right ].
    simpl dom.
    assert (α1 <> α) by (clear - Hα Hα1; fsetdec).
    clear - Hnd H1. fsetdec.
  - apply ad_refine_pskl_f__tophole_keep; auto.
  - eapply ad_refine_pskl_f__flex_l; [ eassumption | auto ].
  - eapply ad_refine_pskl_f__flex_r; [ eassumption | auto ].
Qed.

(** Moving a Δ-variable of a wf skeleton into the context as a rigid. *)
Lemma a_wf_pskl_delta_to_tvar : forall Θ Δ0 P,
  Θ ⨟ Δ0 ⊢ₚₛᵃ P ->
  forall α Δ, Δ0 [<=] add α Δ ->
  ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros * H; induction H; intros β Δ' Hsub.
  - apply a_wf_pskl__unit.
  - destruct H as [HΔ | Hbt].
    + destruct (α == β) as [-> | Hne].
      * apply a_wf_pskl__var. right. left.
        unfold binds. left. reflexivity.
      * apply a_wf_pskl__var. left. clear - HΔ Hsub Hne. fsetdec.
    + apply a_wf_pskl__var. right.
      apply a_binds_tvar_weaken_cons. exact Hbt.
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L `union` singleton β).
    intros α2 Hα2.
    apply H0; [ clear - Hα2; fsetdec | clear - Hsub Hα2; fsetdec ].
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; [ exact H | ].
    apply IHa_wf_pskl. clear. fsetdec.
Qed.

(** A guarded source never refines to an inherited quantifier (the mirror
    of [ad_refine_syn_f_all_inh_guarded_absurd]): the rules with an
    [all_inh] target need an [all_inh] source or a defined-flexible whose
    monotype unfolding is guarded again. *)
Lemma ad_refine_syn_f_guarded_src_all_inh_absurd : forall F Θ Δ Q Q',
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ Q (bskl_all_inh Q') ->
  guarded_bskl Q ->
  False.
Proof.
  intros * Hwf Hr.
  remember (bskl_all_inh Q') as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT.
  - (* __all : the source is an inherited quantifier, not guarded *)
    inversion Hg.
  - (* __hole : a syn painting is never an inherited quantifier *)
    destruct P; simpl in HeqT; discriminate.
  - (* __tophole_remove : a ∀◇ source is not guarded *)
    inversion Hg.
  - (* __flex_l : unfold to the (guarded) monotype *)
    apply IHHr; [ exact Hwf | exact HeqT | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** Mirror: a guarded source never refines to a ∀-syn target either
    (that target only arises by [tophole_fill], whose source is a ∀◇). *)
Lemma ad_refine_syn_f_guarded_src_all_syn_absurd : forall F Θ Δ Q Q',
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ Q (bskl_all_syn Q') ->
  guarded_bskl Q ->
  False.
Proof.
  intros * Hwf Hr.
  remember (bskl_all_syn Q') as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT;
    try solve [ inversion Hg ].
  apply IHHr; [ exact Hwf | exact HeqT | ].
  apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
  eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** The pskl-side mirror. *)
Lemma ad_refine_pskl_f_guarded_src_all_syn_absurd : forall F Θ Δ P P',
  a_wf_aenv Θ ->
  ad_refine_pskl_f F Θ Δ P (pskl_all_syn P') ->
  guarded_pskl P ->
  False.
Proof.
  intros * Hwf Hr.
  remember (pskl_all_syn P') as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT;
    try solve [ inversion Hg ].
  apply IHHr; [ exact Hwf | exact HeqT | ].
  apply mono_ptyp_to_pskl_guarded.
  eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** Moving the rigid mid entry into the Δ-slot of a HYGIENIC refinement
    ([α ∈ F] guarantees no fill mentions it, which is exactly what lets
    the fills' wf strengthen past the removed entry). *)
Lemma ad_refine_syn_f_ctx_to_delta : forall F Θfull Δ Q Q',
  ad_refine_syn_f F Θfull Δ Q Q' ->
  forall Θ1 α Θ0, Θfull = Θ1 ++ (α ~ abind_tvar) ++ Θ0 ->
  α `in` F ->
  uniq Θfull ->
  ad_refine_syn_f F (Θ1 ++ Θ0) (add α Δ) Q Q'.
Proof.
  intros F Θfull Δ Q Q' H; induction H;
    intros Θ1 α0 Θt HeqΘ HαF Hu; subst Θ.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Hbt]; [ left; clear - HΔ; fsetdec | ].
    destruct (α == α0) as [-> | Hne];
      [ left; clear; fsetdec | right ].
    eapply a_binds_tvar_strip_mid;
      [ exact Hbt
      | intro Hc; inversion Hc; congruence
      | intro Hc; inversion Hc
      | intros τ0 Hc; inversion Hc ].
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros α Hα.
    eapply ad_refine_syn_f_delta_mono;
      [ apply (H0 α Hα Θ1 α0 Θt eq_refl HαF Hu) | clear; fsetdec ].
  - apply ad_refine_syn_f__hole; [ exact H | ].
    assert (HαP : α0 `notin` ftvar_in_pskl P).
    { intro Hc.
      assert (Hin : α0 `in` F ∩ ftvar_in_pskl P)
        by (apply inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec. }
    pose proof (a_wf_pskl_ftv_dom H0) as Hsc.
    eapply a_wf_pskl_strengthen;
      [ exact H0 | exact Hu
      | intros x Hx; exfalso; clear - Hx; fsetdec
      | intros x b Hb; apply binds_weaken; exact Hb
      | ].
    intros α Hα. right.
    assert (Hd : α `in` dom (Θ1 ++ (α0 ~ abind_tvar) ++ Θt))
      by (clear - Hsc Hα; fsetdec).
    assert (Hne : α <> α0) by (intro; subst; contradiction).
    repeat rewrite dom_app in *. simpl dom in Hd.
    clear - Hd Hne. fsetdec.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with
      (L := L `union` dom (Θ1 ++ (α0 ~ abind_tvar) ++ Θt)).
    intros α Hα.
    apply (H0 α ltac:(clear - Hα; fsetdec)
             ((α ~ abind_tvar) ++ Θ1) α0 Θt eq_refl HαF).
    apply uniq_push; [ exact Hu | clear - Hα; fsetdec ].
  - apply ad_refine_syn_f__tophole_keep; auto.
  - assert (Hne : α <> α0).
    { intros ->.
      assert (Hbα0 : binds α0 abind_tvar
                       (Θ1 ++ (α0 ~ abind_tvar) ++ Θt))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      pose proof (binds_unique _ _ _ _ _ H Hbα0 Hu) as Hcon.
      discriminate. }
    eapply ad_refine_syn_f__flex_l;
      [ eapply binds_remove_mid; [ exact H | exact Hne ] | auto ].
  - assert (Hne : α <> α0).
    { intros ->.
      assert (Hbα0 : binds α0 abind_tvar
                       (Θ1 ++ (α0 ~ abind_tvar) ++ Θt))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      pose proof (binds_unique _ _ _ _ _ H Hbα0 Hu) as Hcon.
      discriminate. }
    eapply ad_refine_syn_f__flex_r;
      [ eapply binds_remove_mid; [ exact H | exact Hne ] | auto ].
Qed.

(* ===================================================================== *)
(*  §1d  Rename-vs-embedding/metasubstitution commutations               *)
(* ===================================================================== *)

Lemma pskl_to_bskl_inh_subst_var : forall α' α P,
  subst_bskl_in_bskl (bskl_var_f α') α (pskl_to_bskl_inh P)
  = pskl_to_bskl_inh (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  intros α' α P; induction P; simpl;
    try solve [ reflexivity
              | rewrite IHP; reflexivity
              | rewrite IHP1, IHP2; reflexivity ].
  destruct_if;
    reflexivity.
Qed.

Lemma bskl_to_pskl_subst_var : forall α' α Q,
  subst_pskl_in_pskl (pskl_var_f α') α (bskl_to_pskl Q)
  = bskl_to_pskl (subst_bskl_in_bskl (bskl_var_f α') α Q).
Proof.
  intros α' α Q; induction Q; simpl;
    try solve [ reflexivity
              | rewrite IHQ; reflexivity
              | rewrite IHQ1, IHQ2; reflexivity ].
  destruct_if;
    reflexivity.
Qed.

Lemma msubst_lookup_in_or : forall (ζ : metasubst) (β : atom),
  In (β, msubst_lookup ζ β) ζ \/
  (β `notin` dom ζ /\ msubst_lookup ζ β = ptyp_var_f β).
Proof.
  induction ζ as [ | [α1 τ] ζ' IH ]; intros β; simpl.
  - right. split; [ fsetdec | reflexivity ].
  - destruct (β == α1) as [-> | Hne].
    + left. left. reflexivity.
    + destruct (IH β) as [Hin | [Hni Heq]];
        [ left; right; exact Hin
        | right; split; [ clear - Hni Hne; fsetdec | exact Heq ] ].
Qed.

(** Renaming a rigid [α ↦ α] commutes with a metasubstitution that does
    not touch either name (its images avoid [α]; both are off its
    domain). *)
Lemma msubst_pskl_subst_var : forall ζ α α' P,
  α `notin` dom ζ ->
  α' `notin` dom ζ ->
  (forall α1 τ, In (α1, τ) ζ -> α `notin` ftvar_in_ptyp τ) ->
  subst_pskl_in_pskl (pskl_var_f α') α (msubst_pskl ζ P)
  = msubst_pskl ζ (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  intros ζ α α' P Hαd HXd Him;
    induction P as [ | n | β | Pa IHa Pb IHb | Pb IHb | | Pt IHt ]; simpl;
    try solve [ reflexivity
              | rewrite IHb; reflexivity
              | rewrite IHt; reflexivity
              | rewrite IHa, IHb; reflexivity ].
  (* var *)
  destruct_if as [-> | Hne].
  - (* the renamed variable: off the domain on both sides *)
    rewrite (msubst_lookup_notin ζ Hαd). simpl.
    destruct_if as [_ | Hc]; [ | congruence ].
    cbn [msubst_pskl].
    rewrite (msubst_lookup_notin ζ HXd). reflexivity.
  - (* any other variable: the image is α-free *)
    cbn [msubst_pskl].
    destruct (msubst_lookup_in_or ζ β) as [Hin | [Hni Heq]].
    + apply subst_pskl_in_pskl_fresh_eq.
      pose proof (Him _ _ Hin) as Hfr.
      pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup ζ β)) as Hfe.
      clear - Hfr Hfe. fsetdec.
    + rewrite Heq. simpl.
      destruct_if as [Hc | _]; [ congruence | reflexivity ].
Qed.

(** Images of an information increase are scoped by the target. *)
Lemma a_inc_images_ftv_dom : forall Θ0 ζ Θ,
  ζ ∷ Θ0 ⊑ Θ ->
  forall α1 τ, In (α1, τ) ζ -> ftvar_in_ptyp τ [<=] dom Θ.
Proof.
  intros Θ0 ζ Θ H; induction H; intros α10 τ0 Hin.
  - inversion Hin.
  - destruct Hin as [Heq | Hin];
      [ inversion Heq; subst; apply a_wf_ptyp_ftv_dom; assumption
      | eapply IHa_inc; exact Hin ].
  - destruct Hin as [Heq | Hin];
      [ inversion Heq; subst; apply a_wf_ptyp_ftv_dom; assumption
      | eapply IHa_inc; exact Hin ].
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros α2 Hα2. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub α2 Hα2). clear - H2. fsetdec.
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros α2 Hα2. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub α2 Hα2). clear - H2. fsetdec.
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros α2 Hα2. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub α2 Hα2). clear - H1. fsetdec.
Qed.

(* ===================================================================== *)
(*  §1e  ⇓-idempotence: a normalized term is invariant under any          *)
(*       sub-context's normalization (V-constancy for the walk's          *)
(*       target-truncating recursions)                                    *)
(* ===================================================================== *)

Lemma msubst_pskl_ftv_ex : forall ζ P α',
  α' `in` ftvar_in_pskl (msubst_pskl ζ P) ->
  exists β, β `in` ftvar_in_pskl P /\
            α' `in` ftvar_in_ptyp (msubst_lookup ζ β).
Proof.
  intros ζ P; induction P as [ | n | α2 | Pa IHa Pb IHb | Pb IHb | | Pt IHt ];
    intros α' Hα; simpl in *.
  - clear - Hα; fsetdec.
  - clear - Hα; fsetdec.
  - exists α2. split; [ fsetdec | ].
    rewrite ftvar_in_ptyp_to_pskl in Hα. exact Hα.
  - apply union_1 in Hα. destruct Hα as [H1 | H2].
    + destruct (IHa α' H1) as [β [HY1 HY2]].
      exists β; split; [ fsetdec | exact HY2 ].
    + destruct (IHb α' H2) as [β [HY1 HY2]].
      exists β; split; [ fsetdec | exact HY2 ].
  - destruct (IHb α' Hα) as [β [HY1 HY2]].
    exists β; split; [ fsetdec | exact HY2 ].
  - clear - Hα; fsetdec.
  - destruct (IHt α' Hα) as [β [HY1 HY2]].
    exists β; split; [ fsetdec | exact HY2 ].
Qed.

Lemma aenv_msubst_cons_flex : forall α Θ,
  aenv_msubst ((α ~ abind_flex_mono) ++ Θ)
  = (α, ptyp_var_f α) :: aenv_msubst Θ.
Proof. reflexivity. Qed.

Lemma aenv_msubst_cons_def : forall α τ Θ,
  aenv_msubst ((α ~ abind_flex_mono_def τ) ++ Θ)
  = (α, msubst_ptyp (aenv_msubst Θ) τ) :: aenv_msubst Θ.
Proof. reflexivity. Qed.

(** Images of [⇓[Θ]] are scoped by the queried name and the context. *)
Lemma aenv_msubst_image_ftv : forall Θ,
  a_wf_aenv Θ ->
  forall β,
  ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) β) [<=] add β (dom Θ).
Proof.
  intros Θ Hwf; induction Hwf; intros β;
    try rewrite aenv_msubst_cons_flex;
    try rewrite aenv_msubst_cons_def;
    try rewrite aenv_msubst_tvar;
    try rewrite aenv_msubst_var_typ;
    try rewrite aenv_msubst_var_skl.
  - (* nil *) simpl. clear; fsetdec.
  - (* flex_mono *)
    destruct (β == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq. simpl. simpl_env.
      clear; fsetdec.
    + rewrite msubst_lookup_cons_neq by exact Hne. simpl_env.
      pose proof (IHHwf β) as Him. clear - Him. fsetdec.
  - (* flex_mono_def *)
    destruct (β == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq.
      intros α0 Hα0.
      destruct (msubst_ptyp_ftv _ _ Hα0) as [α2 [HZ1 HZ2]].
      assert (HZd : α2 `in` dom Θ)
        by (pose proof (a_wf_ptyp_ftv_dom H0) as Hsc;
            clear - Hsc HZ1; fsetdec).
      pose proof (IHHwf α2) as Him.
      simpl_env. clear - HZ2 Him HZd. fsetdec.
    + rewrite msubst_lookup_cons_neq by exact Hne. simpl_env.
      pose proof (IHHwf β) as Him. clear - Him. fsetdec.
  - (* var_skl *) simpl_env.
    pose proof (IHHwf β) as Him. clear - Him. fsetdec.
  - (* var_typ *) simpl_env.
    pose proof (IHHwf β) as Him. clear - Him. fsetdec.
  - (* tvar *) simpl_env.
    pose proof (IHHwf β) as Him. clear - Him. fsetdec.
Qed.

(** No image of [⇓[Θ]] mentions a DEFINED variable of [Θ]. *)
Lemma aenv_msubst_image_no_def : forall Θ,
  a_wf_aenv Θ ->
  forall β α', α' `in` ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) β) ->
  forall τ, ~ binds α' (abind_flex_mono_def τ) Θ.
Proof.
  intros Θ Hwf; induction Hwf; intros β α' Hα τq Hb;
    try rewrite aenv_msubst_cons_flex in Hα;
    try rewrite aenv_msubst_cons_def in Hα;
    try rewrite aenv_msubst_tvar in Hα;
    try rewrite aenv_msubst_var_typ in Hα;
    try rewrite aenv_msubst_var_skl in Hα.
  - (* nil *) inversion Hb.
  - (* flex_mono α *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | ].
    destruct (β == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq in Hα. simpl in Hα.
      assert (α' = α) by (clear - Hα; fsetdec). subst α'.
      apply binds_In in Hb'. contradiction.
    + rewrite msubst_lookup_cons_neq in Hα by exact Hne.
      exact (IHHwf β α' Hα τq Hb').
  - (* flex_mono_def α τ0 *)
    destruct (β == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq in Hα.
      destruct (msubst_ptyp_ftv _ _ Hα) as [α2 [HZ1 HZ2]].
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'].
      * subst α'. exfalso.
        assert (HZd : α2 `in` dom Θ)
          by (pose proof (a_wf_ptyp_ftv_dom H0) as Hsc;
              clear - Hsc HZ1; fsetdec).
        pose proof (aenv_msubst_image_ftv Hwf α2) as Him.
        assert (Hin1 : α `in` add α2 (dom Θ))
          by (clear - HZ2 Him; fsetdec).
        assert (Hne1 : α <> α2) by (intro; subst; contradiction).
        clear - Hin1 Hne1 H. fsetdec.
      * exact (IHHwf α2 α' HZ2 τq Hb').
    + rewrite msubst_lookup_cons_neq in Hα by exact Hne.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'].
      * subst α'. exfalso.
        pose proof (aenv_msubst_image_ftv Hwf β) as Him.
        assert (Hin1 : α `in` add β (dom Θ))
          by (clear - Hα Him; fsetdec).
        assert (Hne1 : α <> β) by (intro; subst; contradiction).
        clear - Hin1 Hne1 H. fsetdec.
      * exact (IHHwf β α' Hα τq Hb').
  - (* var_skl *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | exact (IHHwf β α' Hα τq Hb') ].
  - (* var_typ *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | exact (IHHwf β α' Hα τq Hb') ].
  - (* tvar *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | exact (IHHwf β α' Hα τq Hb') ].
Qed.

(** Look-up under a context none of whose definitions can be hit. *)
Lemma aenv_msubst_lookup_no_def : forall Θ α,
  (forall τ, ~ binds α (abind_flex_mono_def τ) Θ) ->
  msubst_lookup (aenv_msubst Θ) α = ptyp_var_f α.
Proof.
  induction Θ as [ | [α1 b] Θ' IH ]; intros α Hnd.
  - reflexivity.
  - destruct b as [ | A | Q | | τ0 ]; simpl aenv_msubst.
    + apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + destruct (α == α1) as [-> | Hne].
      * rewrite msubst_lookup_cons_eq. reflexivity.
      * rewrite msubst_lookup_cons_neq by exact Hne.
        apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + destruct (α == α1) as [-> | Hne].
      * exfalso. apply (Hnd τ0). unfold binds. left. reflexivity.
      * rewrite msubst_lookup_cons_neq by exact Hne.
        apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
Qed.

Lemma msubst_ptyp_lookup_refl : forall κ A,
  (forall α, α `in` ftvar_in_ptyp A -> msubst_lookup κ α = ptyp_var_f α) ->
  msubst_ptyp κ A = A.
Proof.
  intros κ A; induction A as [ | n | α2 | A1 IH1 A2 IH2 | A0 IH0 ];
    intros Hlk; simpl in *.
  - reflexivity.
  - reflexivity.
  - apply Hlk. fsetdec.
  - rewrite IH1, IH2;
      [ reflexivity
      | intros α Hα; apply Hlk; fsetdec
      | intros α Hα; apply Hlk; fsetdec ].
  - rewrite IH0; [ reflexivity | intros α Hα; apply Hlk; fsetdec ].
Qed.

Lemma msubst_pskl_lookup_refl : forall κ P,
  (forall α, α `in` ftvar_in_pskl P -> msubst_lookup κ α = ptyp_var_f α) ->
  msubst_pskl κ P = P.
Proof.
  intros κ P;
    induction P as [ | n | α2 | Pa IHa Pb IHb | Pb IHb | | Pt IHt ];
    intros Hlk; simpl in *.
  - reflexivity.
  - reflexivity.
  - rewrite Hlk; [ reflexivity | fsetdec ].
  - rewrite IHa, IHb;
      [ reflexivity
      | intros α Hα; apply Hlk; fsetdec
      | intros α Hα; apply Hlk; fsetdec ].
  - rewrite IHb; [ reflexivity | intros α Hα; apply Hlk; fsetdec ].
  - reflexivity.
  - rewrite IHt; [ reflexivity | intros α Hα; apply Hlk; fsetdec ].
Qed.

(** ⇓-idempotence along a context restriction. *)
Lemma downarrow_idem_sub_ptyp : forall Θ Θs A,
  a_wf_aenv Θ ->
  (forall x (b : abind), binds x b Θs -> binds x b Θ) ->
  ⇓ᵗ[ Θs ] (⇓ᵗ[ Θ ] A) = ⇓ᵗ[ Θ ] A.
Proof.
  intros * Hwf Hsub.
  apply msubst_ptyp_lookup_refl. intros α Hα.
  apply aenv_msubst_lookup_no_def. intros τ Hb.
  destruct (msubst_ptyp_ftv _ _ Hα) as [β [HY1 HY2]].
  assert (Hno : forall τ0, ~ binds α (abind_flex_mono_def τ0) Θ)
    by (intros τ0; eapply aenv_msubst_image_no_def;
        [ exact Hwf | exact HY2 ]).
  exact (Hno τ (Hsub _ _ Hb)).
Qed.

Lemma downarrow_idem_sub_pskl : forall Θ Θs P,
  a_wf_aenv Θ ->
  (forall x (b : abind), binds x b Θs -> binds x b Θ) ->
  ⇓ˢ[ Θs ] (⇓ˢ[ Θ ] P) = ⇓ˢ[ Θ ] P.
Proof.
  intros * Hwf Hsub.
  apply msubst_pskl_lookup_refl. intros α Hα.
  apply aenv_msubst_lookup_no_def. intros τ Hb.
  destruct (msubst_pskl_ftv_ex _ _ Hα) as [β [HY1 HY2]].
  assert (Hno : forall τ0, ~ binds α (abind_flex_mono_def τ0) Θ)
    by (intros τ0; eapply aenv_msubst_image_no_def;
        [ exact Hwf | exact HY2 ]).
  exact (Hno τ (Hsub _ _ Hb)).
Qed.

(* ===================================================================== *)
(*  §1f  var_skl / tvar middle twins of the walk-case a_inc tooling       *)
(* ===================================================================== *)

Lemma a_pskl_tyequiv_weaken : forall Θ Θ' P P',
  (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  Θ ⊢ P ≡ˢ P' ->
  Θ' ⊢ P ≡ˢ P'.
Proof.
  intros * Hmon Heq; revert Θ' Hmon; induction Heq; intros Θ' Hmon;
    eauto using a_pskl_tyequiv.
Qed.

Lemma a_scope_pskl_weaken : forall Θ Θ' P,
  (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  a_scope_pskl Θ P ->
  a_scope_pskl Θ' P.
Proof.
  intros * Hmon Hwf; revert Θ' Hmon; induction Hwf; intros Θ' Hmon.
  - apply a_scope_pskl__unit.
  - apply a_scope_pskl__var.
    destruct H as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
  - apply a_scope_pskl__arrow; auto.
  - apply a_scope_pskl__all with (L := L). intros α Hα.
    apply H0; [ exact Hα | ].
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
      [ subst; unfold binds; left; reflexivity
      | apply binds_cons_3; apply Hmon; exact Hb' ].
  - apply a_scope_pskl__hole.
  - apply a_scope_pskl__tophole; auto.
Qed.

Lemma a_inc_var_skl_mid_strip_id : forall Ξ x P Θ0 κ Θ1,
  a_decls Ξ ->
  is_id_msubst κ ->
  κ ∷ (Ξ ++ (x ~ abind_var_skl P) ++ Θ0) ⊑ ((x ~ abind_var_skl P) ++ Θ1) ->
  κ ∷ (Ξ ++ Θ0) ⊑ Θ1.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros x P Θ0 κ Θ1 Hdec Hid Hinc.
  - simpl in Hinc.
    destruct (a_inc_var_skl_inv Hinc)
      as [Ξv [P' [Θ2 [Heqt [Heqv [Hsuf Hinc']]]]]].
    destruct Ξv as [ | [z bz] Ξv' ].
    + simpl in Heqt. inversion Heqt; subst. exact Hinc'.
    + exfalso. simpl in Heqt. inversion Heqt; subst.
      inversion Hsuf as [ | z0 b0 Ξ0 Hsuf0 Hsb ]; subst.
      inversion Hsb.
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θts aa τ Hinc' Hwfτ Hmτ | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    apply a_inc__flex; [ | | apply mono_ptyp__var ].
    2:{ apply a_wf_ptyp__var.
        inversion Hwfτ as [ | Θw Xw Hbt | | ]; subst.
        eapply a_binds_tvar_strip_mid with
          (c := x) (b := abind_var_skl P) (Ξ := (@nil (atom * abind)));
          [ simpl; exact Hbt
          | intro Hc; inversion Hc
          | intro Hc; inversion Hc
          | intros ? Hc; inversion Hc ]. }
    eapply IH; [ exact Hdec' | exact Hid' | exact Hinc' ].
Qed.

Lemma a_inc_equiv_mid_insert_var_skl :
  forall Ξ x Θ0 Θ' Ξv κ1 κ2 σ1 σ2 Pm Pm',
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom κ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  Θ' ⊢ Pm' ≡ˢ (msubst_pskl κ2 Pm) ->
  a_suffix Ξv ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ' ->
  a_inc_equiv (Ξ ++ (x ~ abind_var_skl Pm) ++ Θ0)
              (κ1 ++ κ2) (σ1 ++ σ2)
              (Ξv ++ (x ~ abind_var_skl Pm') ++ Θ').
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros x Θ0 Θ' Ξv κ1 κ2 σ1 σ2 Pm Pm' Hdec Huq Hdκ Hdσ Heqm Hsuf Hie.
  - rewrite dom_nil in Hdκ, Hdσ.
    apply metasubst_dom_empty in Hdκ; apply metasubst_dom_empty in Hdσ;
      subst.
    simpl in Hie |- *.
    apply a_inc_equiv__var_skl; [ exact Hie | exact Heqm | exact Hsuf ].
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Huκ : uniq (κ1 ++ κ2))
      by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
    assert (Huσ : uniq (σ1 ++ σ2))
      by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
    assert (HaΞ : a `notin` dom Ξ')
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    destruct κ1 as [ | [ar tr] κ1' ];
      [ exfalso; rewrite dom_nil in Hdκ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdκ in Hin; clear - Hin; fsetdec | ].
    destruct σ1 as [ | [asg ts] σ1' ];
      [ exfalso; rewrite dom_nil in Hdσ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
    assert (Harκ : ar `notin` dom κ1')
      by (clear - Huκ; simpl_env in Huκ; solve_uniq).
    assert (Hasσ : asg `notin` dom σ1')
      by (clear - Huσ; simpl_env in Huσ; solve_uniq).
    simpl in Hie.
    inversion Hie as [ | R q1 q2 T aa u1 u2 Hie' Hequ | | | | ]; subst.
    simpl_env in Hdκ; simpl_env in Hdσ.
    simpl. apply a_inc_equiv__flex.
    2:{ apply a_tyequiv_weaken with (Θ := Θ');
        [ intros y b Hb; simpl_env; auto | exact Hequ ]. }
    apply IH; auto.
    + clear - Hdκ Harκ HaΞ. simpl_env in *. fsetdec.
    + clear - Hdσ Hasσ HaΞ. simpl_env in *. fsetdec.
Qed.

Lemma a_inc_equiv_mid_insert_tvar :
  forall Ξ c Θ0 Θ' Ξv κ1 κ2 σ1 σ2,
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom κ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  a_suffix Ξv ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ' ->
  a_inc_equiv (Ξ ++ (c ~ abind_tvar) ++ Θ0)
              (κ1 ++ κ2) (σ1 ++ σ2)
              (Ξv ++ (c ~ abind_tvar) ++ Θ').
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros c Θ0 Θ' Ξv κ1 κ2 σ1 σ2 Hdec Huq Hdκ Hdσ Hsuf Hie.
  - rewrite dom_nil in Hdκ, Hdσ.
    apply metasubst_dom_empty in Hdκ; apply metasubst_dom_empty in Hdσ;
      subst.
    simpl in Hie |- *.
    apply a_inc_equiv__tvar; [ exact Hie | exact Hsuf ].
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Huκ : uniq (κ1 ++ κ2))
      by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
    assert (Huσ : uniq (σ1 ++ σ2))
      by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
    assert (HaΞ : a `notin` dom Ξ')
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    destruct κ1 as [ | [ar tr] κ1' ];
      [ exfalso; rewrite dom_nil in Hdκ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdκ in Hin; clear - Hin; fsetdec | ].
    destruct σ1 as [ | [asg ts] σ1' ];
      [ exfalso; rewrite dom_nil in Hdσ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
    assert (Harκ : ar `notin` dom κ1')
      by (clear - Huκ; simpl_env in Huκ; solve_uniq).
    assert (Hasσ : asg `notin` dom σ1')
      by (clear - Huσ; simpl_env in Huσ; solve_uniq).
    simpl in Hie.
    inversion Hie as [ | R q1 q2 T aa u1 u2 Hie' Hequ | | | | ]; subst.
    simpl_env in Hdκ; simpl_env in Hdσ.
    simpl. apply a_inc_equiv__flex.
    2:{ apply a_tyequiv_weaken with (Θ := Θ');
        [ intros y b Hb; simpl_env; auto | exact Hequ ]. }
    apply IH; auto.
    + clear - Hdκ Harκ HaΞ. simpl_env in *. fsetdec.
    + clear - Hdσ Hasσ HaΞ. simpl_env in *. fsetdec.
Qed.

(** Strip a DEFINED flexible mid off a competing increment (the
    [flex_def] twin of [a_inc_mid_strip_flex]): additionally returns the
    dropped image's wf/mono data and its ≡ᵗ-tie to the definition. *)
Lemma a_inc_mid_strip_flex_def : forall Ξ β τd Θ0 κ Θ,
  a_decls Ξ ->
  κ ∷ (Ξ ++ (β ~ abind_flex_mono_def τd) ++ Θ0) ⊑ Θ ->
  exists κ1 τ κ2,
    κ = κ1 ++ (β, τ) :: κ2 /\
    dom κ1 [=] dom Ξ /\
    κ2 ∷ Θ0 ⊑ Θ /\
    κ1 ++ κ2 ∷ (Ξ ++ Θ0) ⊑ Θ /\
    a_wf_ptyp Θ τ /\ mono_ptyp τ /\
    Θ ⊢ τ ≡ᵗ (msubst_ptyp κ2 τd).
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros β τd Θ0 κ Θ Hdec Hinc.
  - (* Ξ = nil : head is the defined mid β itself *)
    simpl in Hinc.
    inversion Hinc as [ | | Θs κs Θt βs τ0 τ' Hinc' Hwfτ Hmτ Heqv
                          [Heqβ Heqκ] Heqt | | | ]; subst.
    exists (@nil (atom * ptyp)), τ', κs. simpl.
    split; [ reflexivity | ].
    split; [ clear; fsetdec | ].
    split; [ exact Hinc' | ].
    split; [ exact Hinc' | ].
    split; [ exact Hwfτ | ].
    split; [ exact Hmτ | exact Heqv ].
  - (* Ξ = (a ~ flex) ++ Ξ' : peel the head flex a, recurse *)
    inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θt as' τ Hinc' Hwfτ Hmτ [Heqa Heqκ] Heqt
                      | | | | ]; subst.
    destruct (IH β τd Θ0 κs Θ Hdec' Hinc')
      as [κ1 [τ2 [κ2 [Heqκ [Hdom [Hinc2 [Hrec [Hwf2 [Hm2 Heqv2]]]]]]]]].
    exists ((a, τ) :: κ1), τ2, κ2. simpl.
    split; [ rewrite Heqκ; reflexivity | ].
    split; [ clear - Hdom; simpl_env; fsetdec | ].
    split; [ exact Hinc2 | ].
    split; [ apply a_inc__flex; auto | ].
    split; [ exact Hwf2 | ].
    split; [ exact Hm2 | exact Heqv2 ].
Qed.

(** Mid-insertion of a DEFINED flexible pair into a factoring (the
    [flex_def] twin of [a_inc_equiv_mid_insert_flex]). *)
Lemma a_inc_equiv_mid_insert_flex_def :
  forall Ξ β τd Θ0 Θ κ1 κ2 σ1 σ2 τ1 τ2,
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom κ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  Θ ⊢ τ1 ≡ᵗ τ2 ->
  Θ ⊢ τ1 ≡ᵗ (msubst_ptyp κ2 τd) ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ ->
  a_inc_equiv (Ξ ++ (β ~ abind_flex_mono_def τd) ++ Θ0)
              (κ1 ++ (β, τ1) :: κ2) (σ1 ++ (β, τ2) :: σ2) Θ.
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros β τd Θ0 Θ κ1 κ2 σ1 σ2 τ1 τ2 Hdec Huq Hdκ Hdσ Heqτ Heqd Hie.
  - rewrite dom_nil in Hdκ, Hdσ.
    apply metasubst_dom_empty in Hdκ; apply metasubst_dom_empty in Hdσ;
      subst.
    simpl in Hie |- *.
    apply a_inc_equiv__flex_def;
      [ exact Hie | exact Heqτ | exact Heqd ].
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Huκ : uniq (κ1 ++ κ2))
      by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
    assert (Huσ : uniq (σ1 ++ σ2))
      by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
    assert (HaΞ : a `notin` dom Ξ')
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    destruct κ1 as [ | [ar tr] κ1' ];
      [ exfalso; rewrite dom_nil in Hdκ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdκ in Hin; clear - Hin; fsetdec | ].
    destruct σ1 as [ | [asg ts] σ1' ];
      [ exfalso; rewrite dom_nil in Hdσ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
    assert (Harκ : ar `notin` dom κ1')
      by (clear - Huκ; simpl_env in Huκ; solve_uniq).
    assert (Hasσ : asg `notin` dom σ1')
      by (clear - Huσ; simpl_env in Huσ; solve_uniq).
    simpl in Hie.
    inversion Hie as [ | R q1 q2 T aa u1 u2 Hie' Hequ | | | | ]; subst.
    simpl_env in Hdκ; simpl_env in Hdσ.
    simpl. apply a_inc_equiv__flex; [ | exact Hequ ].
    apply IH; auto.
    + clear - Hdκ Harκ HaΞ. simpl_env in *. fsetdec.
    + clear - Hdσ Hasσ HaΞ. simpl_env in *. fsetdec.
Qed.

Lemma a_inc_tvar_mid_strip_id : forall Ξ c Θ0 κ Θ1,
  a_decls Ξ ->
  uniq (Ξ ++ (c ~ abind_tvar) ++ Θ0) ->
  is_id_msubst κ ->
  κ ∷ (Ξ ++ (c ~ abind_tvar) ++ Θ0) ⊑ ((c ~ abind_tvar) ++ Θ1) ->
  κ ∷ (Ξ ++ Θ0) ⊑ Θ1.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros c Θ0 κ Θ1 Hdec Huq Hid Hinc.
  - simpl in Hinc.
    destruct (a_inc_tvar_inv Hinc) as [Ξv [Θ2 [Heqt [Hsuf Hinc']]]].
    destruct Ξv as [ | [z bz] Ξv' ].
    + simpl in Heqt. inversion Heqt; subst. exact Hinc'.
    + exfalso. simpl in Heqt. inversion Heqt; subst.
      inversion Hsuf as [ | z0 b0 Ξ0 Hsuf0 Hsb ]; subst.
      inversion Hsb.
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Hac : a <> c)
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ (c ~ abind_tvar) ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θts aa τ Hinc' Hwfτ Hmτ | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    apply a_inc__flex; [ | | apply mono_ptyp__var ].
    2:{ apply a_wf_ptyp__var.
        inversion Hwfτ as [ | Θw Xw Hbt | | ]; subst.
        eapply a_binds_tvar_strip_mid with
          (c := c) (b := abind_tvar) (Ξ := (@nil (atom * abind)));
          [ simpl; exact Hbt
          | intro Hc; inversion Hc; subst; exact (Hac eq_refl)
          | intro Hc; inversion Hc
          | intros ? Hc; inversion Hc ]. }
    eapply IH; [ exact Hdec' | exact Huq' | exact Hid' | exact Hinc' ].
Qed.

(* ===================================================================== *)
(*  §2  The three completeness statements AT A MEASURE                    *)
(*                                                                        *)
(*  Hypotheses mirror the AUGMENTED problem/solution of consistency-      *)
(*  proofs.tex:2230-2242 exactly as [consis_optimal_post] does (the       *)
(*  competing-solution shape of the green soundness bundle); the          *)
(*  conclusion is the fused existence+optimality of :2246-2255, with the  *)
(*  algorithm's own id-witness quantified as in [a_consis_optimal].       *)
(*                                                                        *)
(*  THE AVOID SET [N] (DESIGN.md §4.3).  The walk's re-attaching rules    *)
(*  carry the paper's Barendregt output premise: the popped head does     *)
(*  not reappear in the output.  Discharging it needs to know that a      *)
(*  sub-run generates only FRESH names, which used to be the 4th conjunct *)
(*  of the soundness bundle, indexed by the judgment's own used-name set  *)
(*  [F].  [F] is gone; the obligation lives here instead, as the middle   *)
(*  conjunct of each conclusion:                                          *)
(*                                                                        *)
(*      forall γ, γ ∈ dom Θ1 -> γ ∈ dom Θ0 \/ γ ∉ N                       *)
(*                                                                        *)
(*  This is the SAME statement, moved from the judgment to the            *)
(*  completeness theorem — where it is free rather than a constraint,     *)
(*  because completeness is the direction that CHOOSES the guessed        *)
(*  names.  An avoid set restricts a judgment and liberates a             *)
(*  completeness proof; [F] was on the wrong side.  The walk rows relay   *)
(*  [N := add α1 N] exactly where they used to relay [add α1 F].          *)
(* ===================================================================== *)

Definition consis_complete_at (m : mu_ty) : Prop :=
  forall (N : atoms) Δ1 Δ2 Θ0 P0 P κ Θ Ψ Qb,
    m = mu_consis Θ κ P0 P Θ0 ->
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    κ ∷ Θ0 ⊑ Θ ->
    a_wf_aenv Θ ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    Ψ ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P)) ∼ Qb ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl κ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl κ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall γ, γ `in` dom Θ1 -> γ `in` dom Θ0 \/ γ `notin` N) /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           ad_precise_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb)).

Definition unify_complete_at (m : mu_ty) : Prop :=
  forall (N : atoms) Θ0 α β κ Θ,
    m = mu_unify Θ κ α β Θ0 ->
    a_wf_aenv Θ0 ->
    a_flex_tvar Θ0 α ->
    a_flex_tvar Θ0 β ->
    κ ∷ Θ0 ⊑ Θ ->
    a_wf_aenv Θ ->
    Θ ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup κ β) ->
    exists Θ1,
      Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 /\
      (forall γ, γ `in` dom Θ1 -> γ `in` dom Θ0 \/ γ `notin` N) /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ).

Definition assign_complete_at (m : mu_ty) : Prop :=
  forall (N : atoms) Θ0 Ξ α P κ Θ,
    m = mu_assign Θ κ α P Ξ Θ0 ->
    a_decls Ξ ->
    a_wf_aenv (Ξ ++ Θ0) ->
    a_flex_tvar Θ0 α ->
    (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
    a_non_flex (Ξ ++ Θ0) P ->
    dom Ξ [<=] ftvar_in_pskl P ->
    κ ∷ (Ξ ++ Θ0) ⊑ Θ ->
    a_wf_aenv Θ ->
    empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P))
                 ∼ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α))) ->
    exists Θ1,
      Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 /\
      (forall γ, γ `in` dom Θ1 -> γ `in` dom (Ξ ++ Θ0) \/ γ `notin` N) /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ (Ξ ++ Θ0) ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv (Ξ ++ Θ0) κ (msubst_compose ζ κ1) Θ).

Definition complete_at (m : mu_ty) : Prop :=
  consis_complete_at m /\ unify_complete_at m /\ assign_complete_at m.

(* ===================================================================== *)
(*  §2b  Small shared helpers (measure intro, head-stripping, embeddings) *)
(* ===================================================================== *)

(** Componentwise introduction of the lexicographic order. *)
Lemma mu_lt_intro : forall (V' V n' n t' t k' k : nat),
  (V' < V \/
   (V' = V /\ (n' < n \/ (n' = n /\ (t' < t \/ (t' = t /\ k' < k)))))) ->
  mu_lt (V', (n', (t', k'))) (V, (n, (t, k))).
Proof.
  intros. unfold mu_lt, lex; simpl.
  destruct H as [HV | [-> [Hn | [-> [Ht | [-> Hk]]]]]].
  - left; exact HV.
  - right; split; [ reflexivity | left; exact Hn ].
  - right; split; [ reflexivity | right; split;
      [ reflexivity | left; exact Ht ] ].
  - right; split; [ reflexivity | right; split;
      [ reflexivity | right; split; [ reflexivity | exact Hk ] ] ].
Qed.

(* --------------------------------------------------------------------- *)
(*  The four moves of the avoid set [N] (see §2's header).  Every one is   *)
(*  a fact about atom SETS: nothing about the judgments is involved, which *)
(*  is the point — the obligation the used-name index used to carry is     *)
(*  bookkeeping, and completeness is where the bookkeeping is free.        *)
(* --------------------------------------------------------------------- *)

(** RELAY.  A walk step pops the head [α1], recurses with [add α1 N], and
    re-attaches [α1].  [D0']/[D1'] are the sub-run's input/output domains,
    [D0]/[D1] the outer run's; [α1] is in the outer input. *)
Lemma avoid_relay : forall (α1 : atom) N (D0' D1' D0 D1 : atoms),
  (forall γ, γ `in` D1' -> γ `in` D0' \/ γ `notin` (add α1 N)) ->
  D0' [<=] D0 ->
  α1 `in` D0 ->
  D1 [<=] (add α1 D1') ->
  forall γ, γ `in` D1 -> γ `in` D0 \/ γ `notin` N.
Proof.
  intros α1 N D0' D1' D0 D1 Hnew Hsub Hα1 HD1 γ Hγ.
  destruct (γ == α1) as [-> | Hne]; [ left; exact Hα1 | ].
  assert (Hγ' : γ `in` D1') by (clear - Hγ HD1 Hne; fsetdec).
  destruct (Hnew γ Hγ') as [Hin | Hni];
    [ left; clear - Hin Hsub; fsetdec | right; clear - Hni; fsetdec ].
Qed.

(** DISCHARGE.  The relayed set is exactly what proves the walk's Barendregt
    output premise: the popped head is in [add α1 N] and fresh for the
    sub-run's input, so the sub-run cannot have produced it. *)
Lemma avoid_head_miss : forall (α1 : atom) N (D0' D1' : atoms),
  (forall γ, γ `in` D1' -> γ `in` D0' \/ γ `notin` (add α1 N)) ->
  α1 `notin` D0' ->
  α1 `notin` D1'.
Proof.
  intros α1 N D0' D1' Hnew Hnd Hin.
  destruct (Hnew α1 Hin) as [Hd | HN]; [ auto | clear - HN; fsetdec ].
Qed.

(** COMPOSE.  Two runs in sequence (the Arrow node) share one [N]. *)
Lemma avoid_compose : forall N (D0 D1 D2 : atoms),
  (forall γ, γ `in` D1 -> γ `in` D0 \/ γ `notin` N) ->
  (forall γ, γ `in` D2 -> γ `in` D1 \/ γ `notin` N) ->
  forall γ, γ `in` D2 -> γ `in` D0 \/ γ `notin` N.
Proof.
  intros N D0 D1 D2 H1 H2 γ Hγ.
  destruct (H2 γ Hγ) as [Hin | Hni]; [ apply H1; exact Hin | right; exact Hni ].
Qed.

(** TRUNCATE.  The ∀ rows run under their own rigid binder [α] and hand back
    the truncated output; [α] is fresh, so it is not in the tail. *)
Lemma avoid_truncate : forall (α : atom) N (D0 D1 : atoms),
  (forall γ, γ `in` (add α D1) -> γ `in` (add α D0) \/ γ `notin` N) ->
  α `notin` D1 ->
  forall γ, γ `in` D1 -> γ `in` D0 \/ γ `notin` N.
Proof.
  intros α N D0 D1 Hnew HαD1 γ Hγ.
  assert (Hne : γ <> α) by (intros ->; auto).
  destruct (Hnew γ ltac:(clear - Hγ; fsetdec)) as [Hin | Hni];
    [ left; clear - Hin Hne; fsetdec | right; exact Hni ].
Qed.

(** [avoid_relay] at the shape the UNIFICATION walk has: the head is consed
    straight back onto the sub-run's output (possibly re-bound). *)
Lemma avoid_relay_cons : forall (α1 : atom) (b1 b0 : abind) (N : atoms)
    (Θ0' Θ1' : aenv),
  (forall γ, γ `in` dom Θ1' -> γ `in` dom Θ0' \/ γ `notin` (add α1 N)) ->
  forall γ, γ `in` dom ((α1 ~ b1) ++ Θ1') ->
    γ `in` dom ((α1 ~ b0) ++ Θ0') \/ γ `notin` N.
Proof.
  intros α1 b1 b0 N Θ0' Θ1' Hnew.
  eapply avoid_relay with (D0' := dom Θ0') (D1' := dom Θ1');
    [ exact Hnew | simpl_env | simpl_env | simpl_env ]; fsetdec.
Qed.

(** [avoid_relay] at the shape the ASSIGNMENT walk has: the popped head sits
    UNDER the declaration prefix [Ξ], which both runs carry. *)
Lemma avoid_relay_cons_mid : forall (α1 : atom) (b1 b0 : abind) (N : atoms)
    (Ξ Θ0' Θ1' : aenv),
  (forall γ, γ `in` dom Θ1' -> γ `in` dom (Ξ ++ Θ0') \/ γ `notin` (add α1 N)) ->
  forall γ, γ `in` dom ((α1 ~ b1) ++ Θ1') ->
    γ `in` dom (Ξ ++ (α1 ~ b0) ++ Θ0') \/ γ `notin` N.
Proof.
  intros α1 b1 b0 N Ξ Θ0' Θ1' Hnew.
  eapply avoid_relay with (D0' := dom (Ξ ++ Θ0')) (D1' := dom Θ1');
    [ exact Hnew | simpl_env | simpl_env | simpl_env ]; fsetdec.
Qed.

(** [avoid_truncate] at the ∀ rows' shape. *)
Lemma avoid_truncate_cons : forall (α : atom) (b : abind) (N : atoms)
    (Θ0 Θ1 : aenv),
  (forall γ, γ `in` dom ((α ~ b) ++ Θ1) ->
     γ `in` dom ((α ~ b) ++ Θ0) \/ γ `notin` N) ->
  α `notin` dom Θ1 ->
  forall γ, γ `in` dom Θ1 -> γ `in` dom Θ0 \/ γ `notin` N.
Proof.
  intros α b N Θ0 Θ1 Hnew Hα.
  eapply avoid_truncate with (α := α); [ | exact Hα ].
  intros γ Hγ.
  destruct (Hnew γ ltac:(simpl_env; clear - Hγ; fsetdec)) as [Hin | Hni];
    [ left; simpl_env in Hin; clear - Hin; fsetdec | right; exact Hni ].
Qed.

(** The axiom rows re-bind the head without moving any other entry. *)
Lemma avoid_same_dom : forall (α1 : atom) (b1 b0 : abind) (N : atoms)
    (Θ0' : aenv),
  forall γ, γ `in` dom ((α1 ~ b1) ++ Θ0') ->
    γ `in` dom ((α1 ~ b0) ++ Θ0') \/ γ `notin` N.
Proof. intros. left. simpl_env in *. fsetdec. Qed.

(** The rows whose output domain merely contains the input's. *)
Lemma avoid_mono : forall N (D0 D0' : atoms),
  D0' [<=] D0 -> forall γ, γ `in` D0' -> γ `in` D0 \/ γ `notin` N.
Proof. intros N D0 D0' Hs γ Hγ. left. clear - Hs Hγ. fsetdec. Qed.

(** A hatted variable other than the head is hatted in the tail. *)
Lemma a_flex_tvar_strip_head : forall (α1 : atom) b Θ0 β1,
  β1 <> α1 ->
  a_flex_tvar ((α1 ~ b) ++ Θ0) β1 ->
  a_flex_tvar Θ0 β1.
Proof.
  intros α1 b Θ0 β1 Hne [Hb | [τ Hb]];
    apply binds_cons_1 in Hb as [[Heq _] | Hb];
    solve [ exfalso; auto | left; exact Hb | right; exists τ; exact Hb ].
Qed.

(** The [V]-measure of an embedded monotype is its type-level measure. *)
Lemma Vpskl_ptyp_to_pskl : forall Θ κ A,
  Vpskl Θ κ (ptyp_to_pskl A) = Vptyp Θ κ A.
Proof.
  intros. unfold Vpskl, Vptyp.
  rewrite msubst_pskl_ptyp_to_pskl. rewrite msubst_pskl_ptyp_to_pskl.
  apply size_ptyp_to_pskl.
Qed.

(** [Vvar] ignores a target prefix the image cannot mention (the walk cases
    for rigid / term-variable heads truncate the solution target). *)
Lemma Vvar_strengthen_mid : forall Ξ (c : atom) b Θt κ α,
  uniq (Ξ ++ (c ~ b) ++ Θt) ->
  a_wf_ptyp Θt (msubst_lookup κ α) ->
  Vvar (Ξ ++ (c ~ b) ++ Θt) κ α = Vvar Θt κ α.
Proof.
  intros Ξ c b Θt κ α Huniq Hwf. unfold Vvar.
  rewrite <- app_assoc in Huniq |- *.
  rewrite (downarrow_app_agree_ptyp _ _ _ Huniq
             (a_wf_ptyp_ftv_dom Hwf)).
  reflexivity.
Qed.

(** A variable outside the metasubstitution's domain keeps its free
    occurrences under it (substitution only adds or preserves them). *)
Lemma msubst_pskl_ftv_keep : forall κ P α',
  α' `notin` dom κ ->
  α' `in` ftvar_in_pskl P ->
  α' `in` ftvar_in_pskl (msubst_pskl κ P).
Proof.
  intros κ P α' Hnd;
    induction P as [ | n | x | P1 IH1 P2 IH2 | Pb IHb | | Pt IHt ];
    simpl; intros Hin; try solve [ fsetdec ].
  (* var_f : the occurrence IS α', whose lookup is itself *)
  assert (Heq : α' = x) by (clear - Hin; fsetdec). subst x.
  rewrite (msubst_lookup_notin κ Hnd). simpl. fsetdec.
Qed.

(** Extending Θ with a fresh rigid entry preserves the three fixed
    hypotheses of the ftv-survival inductions below. *)
Local Ltac ftv_rev_extend α Fr β Θ Hwf HbX Hdefs HwfY HbXY HdefsY :=
  assert (HwfY : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
    by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]);
  assert (HbXY : binds α abind_tvar ((β ~ abind_tvar) ++ Θ))
    by (apply binds_cons_3; exact HbX);
  (* β0, not β: β is this tactic's FORMAL PARAMETER (the caller's fresh
     rigid), so a quantifier named β here would capture it. *)
  assert (HdefsY : forall β0 τ,
            binds β0 (abind_flex_mono_def τ) ((β ~ abind_tvar) ++ Θ) ->
            α `notin` ftvar_in_ptyp τ)
    by (intros β0 τ Hb;
        apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | exact (Hdefs _ _ Hb) ]).

(** Rigid free variables survive fill-hygienic refinement RIGHT-TO-LEFT:
    a rigid [α] (never mentioned by a Θ-definition) absent from the target
    is absent from the source.  This is the ftv-chase behind Ghost's
    [Δ2 ∩ ftv(P0) = ∅] side condition (and GhostR's mirror). *)
Lemma ad_refine_syn_f_rigid_ftv_rev : forall F Θ Δ Qs Qt α',
  a_wf_aenv Θ ->
  binds α' abind_tvar Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
               α' `notin` ftvar_in_ptyp τ) ->
  ad_refine_syn_f F Θ Δ Qs Qt ->
  α' `notin` ftvar_in_bskl Qt ->
  α' `notin` ftvar_in_bskl Qs.
Proof.
  intros F Θ Δ Qs Qt α' Hwf HbX Hdefs Hr.
  induction Hr; intros Hout; simpl in *.
  - (* unit *) clear; fsetdec.
  - (* var *) clear - Hout; fsetdec.
  - (* arrow *)
    assert (Hn1 : α' `notin` ftvar_in_bskl Q1)
      by (apply IHHr1;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    assert (Hn2 : α' `notin` ftvar_in_bskl Q2)
      by (apply IHHr2;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    clear - Hn1 Hn2; fsetdec.
  - (* all (cofinite; Θ unchanged) *)
    pick fresh β for (L `union` singleton α' `union` ftvar_in_bskl P
                        `union` ftvar_in_bskl Q).
    assert (HnT : α' `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl P (bskl_var_f β))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 β ltac:(clear - Fr; fsetdec) Hwf HbX Hdefs HnT) as HnS.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f β))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* hole *) clear; fsetdec.
  - (* tophole_remove *) exact (IHHr Hwf HbX Hdefs Hout).
  - (* tophole_fill (cofinite; Θ grows by the fresh rigid β) *)
    pick fresh β for (L `union` dom Θ `union` singleton α'
                        `union` ftvar_in_bskl P `union` ftvar_in_bskl Q).
    ftv_rev_extend α' Fr β Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : α' `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl P (bskl_var_f β))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    simpl in HnS. clear - HnS. fsetdec.
  - (* tophole_keep *) exact (IHHr Hwf HbX Hdefs Hout).
  - (* flex_l : the source is a defined flexible, never the rigid α' *)
    assert (Hne : α' <> α).
    { intro Heq; subst α.
      pose proof (binds_unique _ _ _ _ _ HbX H (a_wf_aenv_uniq Hwf)) as Hc;
        discriminate. }
    clear - Hne; fsetdec.
  - (* flex_r : unfold the target definition; its ftv avoids α' *)
    apply IHHr; [ assumption | assumption | assumption | ].
    rewrite ftvar_in_bskl_ptyp_syn.
    apply (Hdefs _ _ H).
Qed.

(** The mirror on the JOIN: a rigid [α] absent from the join target is
    absent from the (painted) subject.  Drives GhostR's side condition. *)
Lemma ad_pat_consis_rigid_ftv_rev : forall Ψ Θ R' Qt α',
  a_wf_aenv Θ ->
  binds α' abind_tvar Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
               α' `notin` ftvar_in_ptyp τ) ->
  Ψ ⨟ Θ ⊢ₛᵃ R' ∼ Qt ->
  α' `notin` ftvar_in_bskl Qt ->
  α' `notin` ftvar_in_uskl R'.
Proof.
  intros Ψ Θ R' Qt α' Hwf HbX Hdefs Hc.
  induction Hc; intros Hout; simpl in *.
  - (* unit *) clear; fsetdec.
  - (* var *) clear - Hout; fsetdec.
  - (* arrow *)
    assert (Hn1 : α' `notin` ftvar_in_uskl R1)
      by (apply IHHc1;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    assert (Hn2 : α' `notin` ftvar_in_uskl R2)
      by (apply IHHc2;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    clear - Hn1 Hn2; fsetdec.
  - (* forall_inh_tagged (cofinite; Θ grows) *)
    pick fresh β for (L `union` dom Θ `union` singleton α'
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend α' Fr β Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : α' `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f β))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_inh_untagged (cofinite; Θ grows) *)
    pick fresh β for (L `union` dom Θ `union` singleton α'
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend α' Fr β Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : α' `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f β))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn_tagged (cofinite; Θ grows) *)
    pick fresh β for (L `union` dom Θ `union` singleton α'
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend α' Fr β Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : α' `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f β))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn (cofinite; Θ grows) *)
    pick fresh β for (L `union` dom Θ `union` singleton α'
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend α' Fr β Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : α' `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f β))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* ghostg *) clear; fsetdec.
  - (* topholeg *) exact (IHHc Hwf HbX Hdefs Hout).
  - (* hole : the subject is the ghost hole, no free variables *)
    clear; fsetdec.
  - (* tophole *) exact (IHHc Hwf HbX Hdefs Hout).
  - (* tophole_inh (cofinite target; Θ grows; subject fixed) *)
    pick fresh β for (L `union` dom Θ `union` singleton α'
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend α' Fr β Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : α' `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f β))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    simpl in HnS. clear - HnS. fsetdec.
  - (* tophole_drop *) exact (IHHc Hwf HbX Hdefs Hout).
  - (* flex_l : the subject is a defined flexible, never the rigid α' *)
    assert (Hne : α' <> α).
    { intro Heq; subst α.
      pose proof (binds_unique _ _ _ _ _ HbX H (a_wf_aenv_uniq Hwf)) as Hc';
        discriminate. }
    clear - Hne; fsetdec.
  - (* flex_r : unfold the join definition; its ftv avoids α' *)
    apply IHHc; [ assumption | assumption | assumption | ].
    rewrite ftvar_in_bskl_ptyp_syn.
    apply (Hdefs _ _ H).
Qed.

(** SCOPED variant of the join ftv-survival: the definition side condition
    only holds for definitions REACHABLE from the target's scope [D] (the
    truncated context of the SkipRigid stuck-check).  A rigid [α] outside
    [D] absent from a [D]-scoped target is absent from the subject. *)
Lemma ad_pat_consis_rigid_ftv_rev_scoped : forall Ψ Θ R' Qt α' D,
  a_wf_aenv Θ ->
  binds α' abind_tvar Θ ->
  α' `notin` D ->
  (forall α1 τ, binds α1 (abind_flex_mono_def τ) Θ -> α1 `in` D ->
               ftvar_in_ptyp τ [<=] D) ->
  Ψ ⨟ Θ ⊢ₛᵃ R' ∼ Qt ->
  ftvar_in_bskl Qt [<=] D ->
  α' `notin` ftvar_in_uskl R'.
Proof.
  intros Ψ Θ R' Qt α' D Hwf HbX HXD Hdefs Hc.
  revert D HXD Hdefs.
  induction Hc; intros D HXD Hdefs Hout; simpl in *.
  - (* unit *) clear; fsetdec.
  - (* var *) clear - Hout HXD; fsetdec.
  - (* arrow *)
    assert (Hn1 : α' `notin` ftvar_in_uskl R1)
      by (apply (IHHc1 Hwf HbX D HXD Hdefs); clear - Hout; fsetdec).
    assert (Hn2 : α' `notin` ftvar_in_uskl R2)
      by (apply (IHHc2 Hwf HbX D HXD Hdefs); clear - Hout; fsetdec).
    clear - Hn1 Hn2; fsetdec.
  - (* forall_inh_tagged (cofinite; Θ and D grow by the fresh β) *)
    pick fresh β for (L `union` dom Θ `union` singleton α' `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds α' abind_tvar ((β ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall α1 τ,
              binds α1 (abind_flex_mono_def τ) ((β ~ abind_tvar) ++ Θ) ->
              α1 `in` (add β D) -> ftvar_in_ptyp τ [<=] (add β D)).
    { intros α1 τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : α1 <> β).
      { intro Heq; subst α1. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : α1 `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : α' `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β))).
    { apply (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY (add β D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_inh_untagged *)
    pick fresh β for (L `union` dom Θ `union` singleton α' `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds α' abind_tvar ((β ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall α1 τ,
              binds α1 (abind_flex_mono_def τ) ((β ~ abind_tvar) ++ Θ) ->
              α1 `in` (add β D) -> ftvar_in_ptyp τ [<=] (add β D)).
    { intros α1 τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : α1 <> β).
      { intro Heq; subst α1. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : α1 `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : α' `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β))).
    { apply (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY (add β D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn_tagged *)
    pick fresh β for (L `union` dom Θ `union` singleton α' `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds α' abind_tvar ((β ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall α1 τ,
              binds α1 (abind_flex_mono_def τ) ((β ~ abind_tvar) ++ Θ) ->
              α1 `in` (add β D) -> ftvar_in_ptyp τ [<=] (add β D)).
    { intros α1 τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : α1 <> β).
      { intro Heq; subst α1. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : α1 `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : α' `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β))).
    { apply (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY (add β D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn *)
    pick fresh β for (L `union` dom Θ `union` singleton α' `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds α' abind_tvar ((β ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall α1 τ,
              binds α1 (abind_flex_mono_def τ) ((β ~ abind_tvar) ++ Θ) ->
              α1 `in` (add β D) -> ftvar_in_ptyp τ [<=] (add β D)).
    { intros α1 τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : α1 <> β).
      { intro Heq; subst α1. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : α1 `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : α' `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β))).
    { apply (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY (add β D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* ghostg *) clear; fsetdec.
  - (* topholeg *) apply (IHHc Hwf HbX D HXD Hdefs Hout).
  - (* hole *) clear; fsetdec.
  - (* tophole *) apply (IHHc Hwf HbX D HXD Hdefs Hout).
  - (* tophole_inh *)
    pick fresh β for (L `union` dom Θ `union` singleton α' `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds α' abind_tvar ((β ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall α1 τ,
              binds α1 (abind_flex_mono_def τ) ((β ~ abind_tvar) ++ Θ) ->
              α1 `in` (add β D) -> ftvar_in_ptyp τ [<=] (add β D)).
    { intros α1 τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : α1 <> β).
      { intro Heq; subst α1. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : α1 `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : α' `notin` ftvar_in_uskl (uskl_tophole R)).
    { apply (H0 β ltac:(clear - Fr; fsetdec) HwfY HbXY (add β D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    simpl in HnS. clear - HnS. fsetdec.
  - (* tophole_drop *) apply (IHHc Hwf HbX D HXD Hdefs Hout).
  - (* flex_l : the subject is a defined flexible, never the rigid α' *)
    assert (Hne : α' <> α).
    { intro Heq; subst α.
      pose proof (binds_unique _ _ _ _ _ HbX H (a_wf_aenv_uniq Hwf)) as Hc';
        discriminate. }
    clear - Hne; fsetdec.
  - (* flex_r : the defined join is IN [D], so its definition is too *)
    apply (IHHc Hwf HbX D HXD Hdefs).
    rewrite ftvar_in_bskl_ptyp_syn.
    apply (Hdefs _ _ H). clear - Hout. fsetdec.
Qed.

(** Well-formedness of a metasubstitution image: the solution's images are
    wf in the target, rigid occurrences stay put.  Δ-variables must avoid
    the substitution's domain (locally-opened binders are chosen fresh). *)
Lemma a_wf_pskl_msubst_inc : forall Θ0 κ Θ Δ P,
  κ ∷ Θ0 ⊑ Θ ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ Δ ⊢ₚₛᵃ P ->
  (forall α, α `in` Δ -> α `notin` dom κ) ->
  Θ ⨟ Δ ⊢ₚₛᵃ (msubst_pskl κ P).
Proof.
  intros Θ0 κ Θ Δ P Hinc Hwf0 Hwf; induction Hwf; intros HΔ; simpl.
  - apply a_wf_pskl__unit.
  - (* var : rigid occurrences stay; flexibles map to wf target types *)
    destruct H as [HαΔ | Hbt].
    + rewrite (msubst_lookup_notin κ (HΔ _ HαΔ)). simpl.
      apply a_wf_pskl__var; left; exact HαΔ.
    + apply a_wf_ptyp_to_wf_pskl.
      eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf0 | exact Hbt ].
  - apply a_wf_pskl__arrow;
      [ apply IHHwf1 | apply IHHwf2 ]; try assumption.
  - (* all : open with a binder fresh from the substitution *)
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; eauto).
    apply a_wf_pskl__all with (L := L `union` dom κ).
    intros α Hα.
    rewrite <- msubst_pskl_open_lc_local;
      [ | exact Hlcκ | clear - Hα; fsetdec ].
    apply H0; [ clear - Hα; fsetdec | exact Hinc | exact Hwf0 | ].
    intros β Hβ.
    destruct (β == α) as [-> | Hne].
    + clear - Hα; fsetdec.
    + apply HΔ. clear - Hβ Hne; fsetdec.
  - apply a_wf_pskl__hole.
  - (* tophole : the body is guarded and closed under Δ = ∅ *)
    apply a_wf_pskl__tophole.
    + eapply guarded_pskl_msubst_inc; eauto.
    + apply IHHwf; [ exact Hinc | exact Hwf0 | ].
      intros β Hβ. exfalso. clear - Hβ. fsetdec.
Qed.

(** The non-mono RE-INHERIT bridge (the OPT C-GhostR plan,
    prop_completeness_consis.v (PART B):1752): an uncoloured refinement [A ⊳ B] whose two
    sides are JOINED at the syn painting re-inherits to the coloured
    refinement of the inh paintings.  [Θr] is the refinement context; [Θj]
    the join context, which extends [Θr] by rigid opens only (at the top
    level Θj = Θr).  The wf of [A] supplies guardedness of ∀◇-bodies, which
    is what forces the join to strip/keep wrappers in lockstep with the
    refinement. *)
Lemma refine_join_reinherit : forall F Θr Δ P' P0,
  ad_refine_pskl_f F Θr Δ P' P0 ->
  forall Θj,
  a_wf_aenv Θr ->
  a_wf_aenv Θj ->
  (forall x b, binds x b Θr -> binds x b Θj) ->
  Θr ⨟ Δ ⊢ₚₛᵃ P' ->
  empty ⨟ Θj ⊢ₛᵃ (pskl_to_uskl P') ∼ (pskl_to_bskl_syn P0) ->
  ad_refine_syn_f F Θr Δ (pskl_to_bskl_inh P') (pskl_to_bskl_inh P0).
Proof.
  intros F Θr Δ P' P0 Hr.
  induction Hr; intros Θj Hwfr Hwf Hincl HwfA Hj; simpl in Hj |- *.
  - (* unit *) apply ad_refine_syn_f__unit.
  - (* var *) apply ad_refine_syn_f__var; exact H.
  - (* arrow *)
    inversion HwfA; subst.
    inversion Hj; subst.
    apply ad_refine_syn_f__arrow;
      [ eapply IHHr1 | eapply IHHr2 ]; try eassumption;
      (eapply ad_pat_consis_psi_cong; [ eassumption | fsetdec ]).
  - (* all (forall_syn) *)
    inversion HwfA; subst.
    inversion Hj; subst.
    match goal with
    | Hn : forall _, _ -> ad_pat_consis _ _ _ _ |- _ => rename Hn into Hsub
    end.
    match goal with
    | Hn : forall _, _ -> a_wf_pskl _ _ _ |- _ => rename Hn into Hwfb
    end.
    simpl.
    match type of Hsub with
    | forall _, _ `notin` ?LL -> _ =>
        match type of Hwfb with
        | forall _, _ `notin` ?LW -> _ =>
            apply ad_refine_syn_f__all with
              (L := L `union` LL `union` LW `union` dom Θ `union` dom Θj
                    `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)
        end
    end.
    intros α Hα.
    rewrite <- pskl_to_bskl_inh_open, <- pskl_to_bskl_inh_open.
    apply (H0 α ltac:(clear - Hα; fsetdec) ((α ~ abind_tvar) ++ Θj) Hwfr).
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ].
    + intros x b Hb. apply binds_cons_3. apply Hincl; exact Hb.
    + apply Hwfb. clear - Hα; fsetdec.
    + rewrite pskl_to_uskl_open_var, pskl_to_bskl_syn_open.
      apply Hsub. clear - Hα; fsetdec.
  - (* hole : the join forces the fill to be inh-invariant *)
    pose proof (consis_hole_target_inh Hj) as Hqi.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hqi.
    rewrite Hqi. apply ad_refine_syn_f__hole; [ exact H | exact H0 ].
  - (* tophole_remove : the join strips its subject ∀◇ in lockstep *)
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    assert (HwfP : Θ ⨟ empty ⊢ₚₛᵃ P) by (inversion HwfA; assumption).
    assert (HwfPΔ : Θ ⨟ Δ ⊢ₚₛᵃ P)
      by (eapply a_wf_pskl_delta_mono; [ exact HwfP | clear; fsetdec ]).
    apply ad_refine_syn_f__tophole_remove.
    apply (IHHr Θj Hwfr Hwf Hincl HwfPΔ).
    (* the join: ∀◇⌊P⌋ ∼ syn Q must strip the subject wrapper *)
    inversion Hj; subst.
    + (* __tophole : the target would be a ∀◇ — but the guarded [P]
         refines to it, contradiction *)
      exfalso.
      match goal with
      | HeqQ : pskl_to_bskl_syn Q = bskl_tophole _ |- _ =>
          destruct Q; simpl in HeqQ; try discriminate
      | HeqQ : bskl_tophole _ = pskl_to_bskl_syn Q |- _ =>
          destruct Q; simpl in HeqQ; try discriminate
      end.
      pose proof (ad_refine_pskl_f_guarded_r Hwfr Hr HgP) as Hbad.
      inversion Hbad.
    + (* __tophole_inh : a syn painting is never an inherited ∀ *)
      exfalso.
      match goal with
      | HeqQ : pskl_to_bskl_syn Q = bskl_all_inh _ |- _ =>
          destruct Q; simpl in HeqQ; discriminate
      | HeqQ : bskl_all_inh _ = pskl_to_bskl_syn Q |- _ =>
          destruct Q; simpl in HeqQ; discriminate
      end.
    + (* __tophole_drop : exactly the stripped join *)
      assumption.
    + (* __flex_r : a defined-flex target is guarded; strip via the
         guarded inversion *)
      match goal with
      | HeqQ : pskl_to_bskl_syn Q = bskl_var_f _ |- _ =>
          destruct Q; simpl in HeqQ; try discriminate;
          inversion HeqQ; subst
      | HeqQ : bskl_var_f _ = pskl_to_bskl_syn Q |- _ =>
          destruct Q; simpl in HeqQ; try discriminate;
          inversion HeqQ; subst
      end.
      eapply ad_pat_consis_tophole_guarded_inv;
        [ exact Hwf | | exact HgP | apply guarded_bskl__var ].
      eapply ad_pat_consis__flex_r; eassumption.
  - (* tophole_fill : VACUOUS — no join matches a ∀◇ subject against a
       ∀-syn target *)
    exfalso.
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    pick fresh α for (L `union` dom Θ).
    assert (HlcQX : lc_pskl (open_pskl_wrt_pskl Q (pskl_var_f α)))
      by (eapply ad_refine_pskl_f_lc_r; apply H; clear - Fr; fsetdec).
    assert (HlcQ : lc_bskl (pskl_to_bskl_syn (pskl_all_syn Q))).
    { apply pskl_to_bskl_syn_lc.
      apply (lc_pskl_all_syn_exists α). exact HlcQX. }
    inversion Hj; subst.
    (* only __tophole_drop survives the target shape; its stripped subject
       is guarded against a ∀-syn target *)
    match goal with
    | Hdrop : _ ⨟ _ ⊢ₛᵃ (pskl_to_uskl P) ∼ _ |- _ =>
        pose proof (ad_pat_consis_guarded_r Hdrop Hwf eq_refl HgP HlcQ)
          as Hbad
    end.
    inversion Hbad.
  - (* tophole_keep : the join keeps (or cannot drop) the wrapper *)
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    assert (HwfP : Θ ⨟ empty ⊢ₚₛᵃ P) by (inversion HwfA; assumption).
    assert (HwfPΔ : Θ ⨟ Δ ⊢ₚₛᵃ P)
      by (eapply a_wf_pskl_delta_mono; [ exact HwfP | clear; fsetdec ]).
    apply ad_refine_syn_f__tophole_keep;
      [ apply guarded_pskl_to_bskl_inh; exact H | ].
    apply (IHHr Θj Hwfr Hwf Hincl HwfPΔ).
    inversion Hj; subst.
    + (* __tophole : both wrappers strip *) assumption.
    + (* __tophole_drop : the guarded stripped subject cannot join a ∀◇ *)
      exfalso.
      assert (HlcQt : lc_bskl (bskl_tophole (pskl_to_bskl_syn Q))).
      { apply lc_bskl_tophole. apply pskl_to_bskl_syn_lc.
        eapply ad_refine_pskl_f_lc_r; exact Hr. }
      match goal with
      | Hdrop : _ ⨟ _ ⊢ₛᵃ (pskl_to_uskl P) ∼ _ |- _ =>
          pose proof (ad_pat_consis_guarded_r Hdrop Hwf eq_refl HgP HlcQt)
            as Hbad
      end.
      inversion Hbad.
  - (* flex_l : unfold α̂ in the output and in the join SUBJECT *)
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfr | exact H ]).
    apply ad_refine_syn_f__flex_l with (τ := τ); [ exact H | ].
    rewrite <- (mono_inh_eq_syn Hmτ).
    eapply IHHr; try eassumption.
    + apply a_wf_ptyp_to_wf_pskl.
      eapply a_wf_aenv_binds_def_wf; [ exact Hwfr | exact H ].
    + rewrite pskl_to_uskl_ptyp.
      eapply consis_unfold_def_subject;
        [ exact Hj | exact Hwf | reflexivity | apply Hincl; exact H ].
  - (* flex_r : unfold α̂ in the output and in the join TARGET *)
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfr | exact H ]).
    apply ad_refine_syn_f__flex_r with (τ := τ); [ exact H | ].
    rewrite <- (mono_inh_eq_syn Hmτ).
    eapply IHHr; try eassumption.
    unfold ptyp_to_bskl_syn.
    eapply consis_unfold_def_join;
      [ exact Hj | exact Hwf | reflexivity | apply Hincl; exact H ].
Qed.

(* --------------------------------------------------------------------- *)
(*  The ≡ˢ-SUBJECT TRANSPORT of the join (general skeletons).             *)
(*                                                                        *)
(*  This is the step the paper's C-Arrow glosses as `the right-component  *)
(*  premises can be rewritten with κ₁` (:2744) and Assign-Assign's        *)
(*  soundness needed as the ≡ˢ-subject transport: a join is invariant     *)
(*  under replacing its subject by an ≡ˢ-equivalent skeleton (the         *)
(*  equational theory only unfolds flexible definitions and is a          *)
(*  congruence elsewhere).  Mirrors [tyequiv_mono_consis_transport],      *)
(*  which covers only monotype subjects.                                  *)
(* --------------------------------------------------------------------- *)

(** Transport a ∀-syn subject componentwise: only [forall_inh_untagged] /
    [forall_syn] / [flex_r] can have an [all_syn] subject. *)
Lemma consis_forall_subject_transport : forall Ψ Θ R Qt,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Qt ->
  forall R0 R0' L0,
  R = uskl_all_syn R0 ->
  (forall α, α `notin` L0 -> forall Ψ' Q',
     Ψ' ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ₛᵃ
       (open_uskl_wrt_uskl R0 (uskl_var_f α)) ∼ Q' ->
     Ψ' ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ₛᵃ
       (open_uskl_wrt_uskl R0' (uskl_var_f α)) ∼ Q') ->
  Ψ ⨟ Θ ⊢ₛᵃ (uskl_all_syn R0') ∼ Qt.
Proof.
  intros Ψ Θ R Qt Hc; induction Hc; intros R0 R0' L0 HeqS Htr;
    try discriminate HeqS.
  - (* forall_inh_untagged *)
    inversion HeqS; subst.
    apply ad_pat_consis__forall_inh_untagged with (L := L `union` L0).
    intros α Hα.
    apply Htr; [ clear - Hα; fsetdec | ].
    apply H; clear - Hα; fsetdec.
  - (* forall_syn *)
    inversion HeqS; subst.
    apply ad_pat_consis__forall_syn with (L := L `union` L0).
    intros α Hα.
    apply Htr; [ clear - Hα; fsetdec | ].
    apply H; clear - Hα; fsetdec.
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

(** Transport a ∀◇ subject componentwise.  The component transport is
    context-generalized because [tophole_inh] keeps the SAME subject under
    an extended context. *)
Lemma consis_tophole_subject_transport : forall Ψ Θ R Qt,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Qt ->
  a_wf_aenv Θ ->
  forall R0 R0',
  R = uskl_tophole R0 ->
  (forall Θ' Ψ' Q',
     a_wf_aenv Θ' ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     Ψ' ⨟ Θ' ⊢ₛᵃ R0 ∼ Q' -> Ψ' ⨟ Θ' ⊢ₛᵃ R0' ∼ Q') ->
  Ψ ⨟ Θ ⊢ₛᵃ (uskl_tophole R0') ∼ Qt.
Proof.
  intros Ψ Θ R Qt Hc; induction Hc; intros HwfΘ R0 R0' HeqS Htr;
    try discriminate HeqS.
  - (* tophole *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc ].
  - (* tophole_inh : same subject, extended context *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole_inh with (L := L `union` dom Θ).
    intros α Hα.
    assert (HwfX : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    apply (H0 α ltac:(clear - Hα; fsetdec) HwfX R0 R0' eq_refl).
    intros Θ' Ψ' Q' Hwf' Hincl' Hc'.
    apply (Htr Θ' Ψ' Q' Hwf'); [ | exact Hc' ].
    intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  - (* tophole_drop *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole_drop.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc ].
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

(** THE TRANSPORT: for [Θ ⊢ A ≡ˢ B], joins re-subject between [⌊A⌋] and
    [⌊B⌋] in BOTH directions, in any conservative extension [Θ'] of the
    equivalence's context (the generality the ∀/∀◇ congruences need). *)
Lemma skl_tyequiv_consis_transport : forall Θ P P',
  Θ ⊢ P ≡ˢ P' ->
  forall Θ',
  a_wf_aenv Θ' ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall Ψ Qt, Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl P) ∼ Qt ->
                Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl P') ∼ Qt) /\
  (forall Ψ Qt, Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl P') ∼ Qt ->
                Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl P) ∼ Qt).
Proof.
  intros Θ P P' Heq; induction Heq; intros Θ' Hwf' Hincl.
  - (* refl *) split; intros Ψ Qt Hc; exact Hc.
  - (* sym : swap *)
    destruct (IHHeq Θ' Hwf' Hincl) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - (* trans : compose *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros Ψ Qt Hc; [ apply H2l, H1l, Hc | apply H1r, H2r, Hc ].
  - (* flex_def : α̂ ≡ˢ ⌊τ⌋ with α̂ ≔ τ *)
    split; intros Ψ Qt Hc.
    + (* unfold the subject definition *)
      rewrite pskl_to_uskl_ptyp.
      eapply consis_unfold_def_subject;
        [ exact Hc | exact Hwf' | reflexivity | apply Hincl; exact H ].
    + (* fold : one lookup rule *)
      simpl.
      eapply ad_pat_consis__flex_l; [ apply Hincl; exact H | ].
      rewrite pskl_to_uskl_ptyp in Hc. exact Hc.
  - (* arrow : componentwise *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros Ψ Qt Hc; simpl in Hc |- *.
    + eapply consis_arrow_subject_transport;
        [ exact Hc | reflexivity | exact H1l | exact H2l ].
    + eapply consis_arrow_subject_transport;
        [ exact Hc | reflexivity | exact H1r | exact H2r ].
  - (* all : componentwise, under a fresh rigid open *)
    split; intros Ψ Qt Hc; simpl in Hc |- *.
    + eapply consis_forall_subject_transport with (L0 := L `union` dom Θ');
        [ exact Hc | reflexivity | ].
      intros α Hα Ψ' Q' Hc'.
      assert (HwfX : a_wf_aenv ((α ~ abind_tvar) ++ Θ'))
        by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]).
      assert (HinclX : forall x b, binds x b Θ ->
                binds x b ((α ~ abind_tvar) ++ Θ'))
        by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb).
      destruct (H0 α ltac:(clear - Hα; fsetdec)
                  ((α ~ abind_tvar) ++ Θ') HwfX HinclX) as [Hl _].
      rewrite <- pskl_to_uskl_open_var in Hc'.
      rewrite <- pskl_to_uskl_open_var.
      apply Hl. exact Hc'.
    + eapply consis_forall_subject_transport with (L0 := L `union` dom Θ');
        [ exact Hc | reflexivity | ].
      intros α Hα Ψ' Q' Hc'.
      assert (HwfX : a_wf_aenv ((α ~ abind_tvar) ++ Θ'))
        by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]).
      assert (HinclX : forall x b, binds x b Θ ->
                binds x b ((α ~ abind_tvar) ++ Θ'))
        by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb).
      destruct (H0 α ltac:(clear - Hα; fsetdec)
                  ((α ~ abind_tvar) ++ Θ') HwfX HinclX) as [_ Hr].
      rewrite <- pskl_to_uskl_open_var in Hc'.
      rewrite <- pskl_to_uskl_open_var.
      apply Hr. exact Hc'.
  - (* tophole : componentwise, context-generalized *)
    split; intros Ψ Qt Hc; simpl in Hc |- *.
    + eapply consis_tophole_subject_transport;
        [ exact Hc | exact Hwf' | reflexivity | ].
      intros Θ'' Ψ' Q' Hwf'' Hincl' Hc'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [Hl _].
      apply Hl. exact Hc'.
    + eapply consis_tophole_subject_transport;
        [ exact Hc | exact Hwf' | reflexivity | ].
      intros Θ'' Ψ' Q' Hwf'' Hincl' Hc'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [_ Hr].
      apply Hr. exact Hc'.
Qed.

(** Reflexivity of fill-hygienic refinement on a monotype's syn painting. *)
Lemma ad_refine_syn_f_mono_refl : forall F Θ Δ τ,
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  ad_refine_syn_f F Θ Δ (ptyp_to_bskl_syn τ) (ptyp_to_bskl_syn τ).
Proof.
  intros F Θ Δ τ Hm Hwf.
  rewrite <- (mono_inh_eq_syn Hm).
  apply ad_refine_syn_f_refl_inh.
  apply a_wf_pskl_mono_ptyp; assumption.
Qed.

(** Reflexivity of the uncoloured fill-hygienic refinement on a monotype. *)
Lemma ad_refine_pskl_f_mono_refl : forall F Θ Δ τ,
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  ad_refine_pskl_f F Θ Δ (ptyp_to_pskl τ) (ptyp_to_pskl τ).
Proof.
  intros F Θ Δ τ Hm Hwf.
  apply ad_refine_pskl_f_refl.
  apply a_wf_pskl_mono_ptyp; assumption.
Qed.

(* --------------------------------------------------------------------- *)
(*  The ≡ˢ-SOURCE TRANSPORTS of the two refinement judgments — the        *)
(*  companions of [skl_tyequiv_consis_transport] for C-Arrow's (g)/(i)    *)
(*  premises and Assign-Assign.  Same architecture: per-source-shape      *)
(*  helpers (each chasing the [flex_r] target chains), then the main      *)
(*  induction on [≡ˢ].                                                    *)
(* --------------------------------------------------------------------- *)

(** Unfold a DEFINED source variable inside a Δ1-refinement: only [var] /
    [flex_l] / [flex_r] can have source [α1̂]. *)
Lemma ad_refine_syn_f_unfold_def_source : forall F Θ Δ Q Qt,
  ad_refine_syn_f F Θ Δ Q Qt ->
  a_wf_aenv Θ ->
  forall α1 τ, Q = bskl_var_f α1 ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  ad_refine_syn_f F Θ Δ (ptyp_to_bskl_syn τ) Qt.
Proof.
  intros F Θ Δ Q Qt Hr Hwf; induction Hr; intros α10 τ0 HeqS Hb;
    try discriminate HeqS.
  - (* var : the target is the same variable; fold it with [flex_r] *)
    inversion HeqS; subst.
    eapply ad_refine_syn_f__flex_r; [ exact Hb | ].
    apply ad_refine_syn_f_mono_refl;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
  - (* flex_l : the unfolding is the derivation's own *)
    inversion HeqS; subst.
    pose proof (binds_unique _ _ _ _ _ H Hb (a_wf_aenv_uniq Hwf)) as Heqd.
    inversion Heqd; subst.
    exact Hr.
  - (* flex_r : the target unfolds; recurse and re-wrap *)
    eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport an arrow source componentwise. *)
Lemma ad_refine_syn_f_arrow_source_transport : forall F Θ Δ Q Qt,
  ad_refine_syn_f F Θ Δ Q Qt ->
  forall Q1 Q2 Q1' Q2',
  Q = bskl_arrow Q1 Q2 ->
  (forall Qt', ad_refine_syn_f F Θ Δ Q1 Qt' ->
               ad_refine_syn_f F Θ Δ Q1' Qt') ->
  (forall Qt', ad_refine_syn_f F Θ Δ Q2 Qt' ->
               ad_refine_syn_f F Θ Δ Q2' Qt') ->
  ad_refine_syn_f F Θ Δ (bskl_arrow Q1' Q2') Qt.
Proof.
  intros F Θ Δ Q Qt Hr; induction Hr; intros S1' S2' Q1' Q2' HeqS Htr1 Htr2;
    try discriminate HeqS.
  - (* arrow *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__arrow; [ apply Htr1 | apply Htr2 ]; assumption.
  - (* flex_r *)
    eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport an inherited-∀ source componentwise (the [__all] premise
    grows Δ, so the component transport is Δ-generalized). *)
Lemma ad_refine_syn_f_forall_source_transport : forall F Θ Δ Q Qt,
  ad_refine_syn_f F Θ Δ Q Qt ->
  forall Q0 Q0' L0,
  Q = bskl_all_inh Q0 ->
  (forall α, α `notin` L0 -> forall Δ' Qt',
     ad_refine_syn_f F Θ Δ'
       (open_bskl_wrt_bskl Q0 (bskl_var_f α)) Qt' ->
     ad_refine_syn_f F Θ Δ'
       (open_bskl_wrt_bskl Q0' (bskl_var_f α)) Qt') ->
  ad_refine_syn_f F Θ Δ (bskl_all_inh Q0') Qt.
Proof.
  intros F Θ Δ Q Qt Hr; induction Hr; intros Q0 Q0' L0 HeqS Htr;
    try discriminate HeqS.
  - (* all *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__all with (L := L `union` L0).
    intros α Hα.
    apply Htr; [ clear - Hα; fsetdec | ].
    apply H; clear - Hα; fsetdec.
  - (* flex_r *)
    eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport a ∀◇ source componentwise.  Context-generalized: the
    [tophole_fill] premise keeps the SAME source under an extended Θ. *)
Lemma ad_refine_syn_f_tophole_source_transport : forall F Θ Δ Q Qt,
  ad_refine_syn_f F Θ Δ Q Qt ->
  a_wf_aenv Θ ->
  forall Q0 Q0',
  Q = bskl_tophole Q0 ->
  (forall Θ' Qt',
     a_wf_aenv Θ' ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     ad_refine_syn_f F Θ' Δ Q0 Qt' ->
     ad_refine_syn_f F Θ' Δ Q0' Qt') ->
  ad_refine_syn_f F Θ Δ (bskl_tophole Q0') Qt.
Proof.
  intros F Θ Δ Q Qt Hr; induction Hr; intros HwfΘ Q0 Q0' HeqS Htr;
    try discriminate HeqS.
  - (* tophole_remove *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__tophole_remove.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  - (* tophole_fill : same source, extended context *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__tophole_fill with (L := L `union` dom Θ).
    intros α Hα.
    assert (HwfX : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    apply (H0 α ltac:(clear - Hα; fsetdec) HwfX Q0 Q0' eq_refl).
    intros Θ' Qt' Hwf' Hincl' Hr'.
    apply (Htr Θ' Qt' Hwf'); [ | exact Hr' ].
    intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  - (* tophole_keep *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__tophole_keep; [ exact H | ].
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  - (* flex_r *)
    eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** THE SYN TRANSPORT: for [Θ ⊢ A ≡ˢ B], Δ1-refinements re-source between
    [inh A] and [inh B], in both directions, in any conservative
    extension. *)
Lemma skl_tyequiv_refine_syn_f_transport : forall Θ P P',
  Θ ⊢ P ≡ˢ P' ->
  forall Θ',
  a_wf_aenv Θ' ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall F Δ Qt,
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh P) Qt ->
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh P') Qt) /\
  (forall F Δ Qt,
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh P') Qt ->
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh P) Qt).
Proof.
  intros Θ P P' Heq; induction Heq; intros Θ' Hwf' Hincl.
  - (* refl *) split; intros F Δ Qt Hr; exact Hr.
  - (* sym *)
    destruct (IHHeq Θ' Hwf' Hincl) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - (* trans *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros F Δ Qt Hr;
      [ apply H2l, H1l, Hr | apply H1r, H2r, Hr ].
  - (* flex_def *)
    assert (HbΘ' : binds α (abind_flex_mono_def τ) Θ')
      by (apply Hincl; exact H).
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf' | exact HbΘ' ]).
    split; intros F Δ Qt Hr.
    + (* unfold : the source's own definition *)
      rewrite (mono_inh_eq_syn Hmτ).
      eapply ad_refine_syn_f_unfold_def_source;
        [ exact Hr | exact Hwf' | reflexivity | exact HbΘ' ].
    + (* fold : one lookup rule *)
      simpl.
      eapply ad_refine_syn_f__flex_l; [ exact HbΘ' | ].
      rewrite (mono_inh_eq_syn Hmτ) in Hr. exact Hr.
  - (* arrow *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros F Δ Qt Hr; simpl in Hr |- *.
    + eapply ad_refine_syn_f_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1l | apply H2l ].
    + eapply ad_refine_syn_f_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1r | apply H2r ].
  - (* all *)
    split; intros F Δ Qt Hr; simpl in Hr |- *.
    + eapply ad_refine_syn_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros α Hα Δ' Qt' Hr'.
      destruct (H0 α ltac:(clear - Hα; fsetdec) Θ' Hwf' Hincl) as [Hl _].
      rewrite <- pskl_to_bskl_inh_open in Hr'.
      rewrite <- pskl_to_bskl_inh_open.
      apply Hl. exact Hr'.
    + eapply ad_refine_syn_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros α Hα Δ' Qt' Hr'.
      destruct (H0 α ltac:(clear - Hα; fsetdec) Θ' Hwf' Hincl) as [_ Hrr].
      rewrite <- pskl_to_bskl_inh_open in Hr'.
      rewrite <- pskl_to_bskl_inh_open.
      apply Hrr. exact Hr'.
  - (* tophole *)
    split; intros F Δ Qt Hr; simpl in Hr |- *.
    + eapply ad_refine_syn_f_tophole_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [Hl _].
      apply Hl. exact Hr'.
    + eapply ad_refine_syn_f_tophole_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [_ Hrr].
      apply Hrr. exact Hr'.
Qed.

(** Unfold a DEFINED source variable inside a Δ2-refinement. *)
Lemma ad_refine_pskl_f_unfold_def_source : forall F Θ Δ P Pt,
  ad_refine_pskl_f F Θ Δ P Pt ->
  a_wf_aenv Θ ->
  forall α1 τ, P = pskl_var_f α1 ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  ad_refine_pskl_f F Θ Δ (ptyp_to_pskl τ) Pt.
Proof.
  intros F Θ Δ P Pt Hr Hwf; induction Hr; intros α10 τ0 HeqS Hb;
    try discriminate HeqS.
  - (* var *)
    inversion HeqS; subst.
    eapply ad_refine_pskl_f__flex_r; [ exact Hb | ].
    apply ad_refine_pskl_f_mono_refl;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
  - (* flex_l *)
    inversion HeqS; subst.
    pose proof (binds_unique _ _ _ _ _ H Hb (a_wf_aenv_uniq Hwf)) as Heqd.
    inversion Heqd; subst.
    exact Hr.
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport an arrow source componentwise (uncoloured). *)
Lemma ad_refine_pskl_f_arrow_source_transport : forall F Θ Δ P Pt,
  ad_refine_pskl_f F Θ Δ P Pt ->
  forall P1 P2 P1' P2',
  P = pskl_arrow P1 P2 ->
  (forall Qt', ad_refine_pskl_f F Θ Δ P1 Qt' ->
               ad_refine_pskl_f F Θ Δ P1' Qt') ->
  (forall Qt', ad_refine_pskl_f F Θ Δ P2 Qt' ->
               ad_refine_pskl_f F Θ Δ P2' Qt') ->
  ad_refine_pskl_f F Θ Δ (pskl_arrow P1' P2') Pt.
Proof.
  intros F Θ Δ P Pt Hr; induction Hr; intros S1' S2' P1' P2' HeqS Htr1 Htr2;
    try discriminate HeqS.
  - (* arrow *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__arrow; [ apply Htr1 | apply Htr2 ]; assumption.
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport a ∀-syn source componentwise (uncoloured; Δ grows). *)
Lemma ad_refine_pskl_f_forall_source_transport : forall F Θ Δ P Pt,
  ad_refine_pskl_f F Θ Δ P Pt ->
  forall P0 P0' L0,
  P = pskl_all_syn P0 ->
  (forall α, α `notin` L0 -> forall Δ' Pt',
     ad_refine_pskl_f F Θ Δ'
       (open_pskl_wrt_pskl P0 (pskl_var_f α)) Pt' ->
     ad_refine_pskl_f F Θ Δ'
       (open_pskl_wrt_pskl P0' (pskl_var_f α)) Pt') ->
  ad_refine_pskl_f F Θ Δ (pskl_all_syn P0') Pt.
Proof.
  intros F Θ Δ P Pt Hr; induction Hr; intros P0 P0' L0 HeqS Htr;
    try discriminate HeqS.
  - (* all *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__all with (L := L `union` L0).
    intros α Hα.
    apply Htr; [ clear - Hα; fsetdec | ].
    apply H; clear - Hα; fsetdec.
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport a ∀◇ source componentwise (uncoloured; context-generalized
    for [tophole_fill]). *)
Lemma ad_refine_pskl_f_tophole_source_transport : forall F Θ Δ P Pt,
  ad_refine_pskl_f F Θ Δ P Pt ->
  a_wf_aenv Θ ->
  forall P0 P0',
  P = pskl_tophole P0 ->
  (forall Θ' Pt',
     a_wf_aenv Θ' ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     ad_refine_pskl_f F Θ' Δ P0 Pt' ->
     ad_refine_pskl_f F Θ' Δ P0' Pt') ->
  ad_refine_pskl_f F Θ Δ (pskl_tophole P0') Pt.
Proof.
  intros F Θ Δ P Pt Hr; induction Hr; intros HwfΘ P0 P0' HeqS Htr;
    try discriminate HeqS.
  - (* tophole_remove *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__tophole_remove.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  - (* tophole_fill *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__tophole_fill with (L := L `union` dom Θ).
    intros α Hα.
    assert (HwfX : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    apply (H0 α ltac:(clear - Hα; fsetdec) HwfX P0 P0' eq_refl).
    intros Θ' Pt' Hwf' Hincl' Hr'.
    apply (Htr Θ' Pt' Hwf'); [ | exact Hr' ].
    intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  - (* tophole_keep *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__tophole_keep; [ exact H | ].
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** THE PSKL TRANSPORT: for [Θ ⊢ A ≡ˢ B], Δ2-refinements re-source between
    [A] and [B], in both directions, in any conservative extension. *)
Lemma skl_tyequiv_refine_pskl_f_transport : forall Θ P P',
  Θ ⊢ P ≡ˢ P' ->
  forall Θ',
  a_wf_aenv Θ' ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall F Δ Pt,
     ad_refine_pskl_f F Θ' Δ P Pt ->
     ad_refine_pskl_f F Θ' Δ P' Pt) /\
  (forall F Δ Pt,
     ad_refine_pskl_f F Θ' Δ P' Pt ->
     ad_refine_pskl_f F Θ' Δ P Pt).
Proof.
  intros Θ P P' Heq; induction Heq; intros Θ' Hwf' Hincl.
  - (* refl *) split; intros F Δ Pt Hr; exact Hr.
  - (* sym *)
    destruct (IHHeq Θ' Hwf' Hincl) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - (* trans *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros F Δ Pt Hr;
      [ apply H2l, H1l, Hr | apply H1r, H2r, Hr ].
  - (* flex_def *)
    assert (HbΘ' : binds α (abind_flex_mono_def τ) Θ')
      by (apply Hincl; exact H).
    split; intros F Δ Pt Hr.
    + eapply ad_refine_pskl_f_unfold_def_source;
        [ exact Hr | exact Hwf' | reflexivity | exact HbΘ' ].
    + eapply ad_refine_pskl_f__flex_l; [ exact HbΘ' | exact Hr ].
  - (* arrow *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros F Δ Pt Hr.
    + eapply ad_refine_pskl_f_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1l | apply H2l ].
    + eapply ad_refine_pskl_f_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1r | apply H2r ].
  - (* all *)
    split; intros F Δ Pt Hr.
    + eapply ad_refine_pskl_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros α Hα Δ' Qt' Hr'.
      destruct (H0 α ltac:(clear - Hα; fsetdec) Θ' Hwf' Hincl) as [Hl _].
      apply Hl. exact Hr'.
    + eapply ad_refine_pskl_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros α Hα Δ' Qt' Hr'.
      destruct (H0 α ltac:(clear - Hα; fsetdec) Θ' Hwf' Hincl) as [_ Hrr].
      apply Hrr. exact Hr'.
  - (* tophole *)
    split; intros F Δ Pt Hr.
    + eapply ad_refine_pskl_f_tophole_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [Hl _].
      apply Hl. exact Hr'.
    + eapply ad_refine_pskl_f_tophole_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [_ Hrr].
      apply Hrr. exact Hr'.
Qed.

(** Bridge to the Δ-free skeleton wf (the form the ≡ˢ/V lemmas take):
    Δ-variables must be tvar-ish in the receiving context. *)
Lemma a_wf_pskl_to_a_scope_pskl : forall Θ Δ P,
  a_wf_pskl Θ Δ P ->
  forall Θa,
  (forall x b, binds x b Θ -> binds x b Θa) ->
  (forall α, α `in` Δ -> a_binds_tvar α Θa) ->
  a_scope_pskl Θa P.
Proof.
  intros Θ Δ P Hwfd; induction Hwfd; intros Θa Hincl HΔ.
  - apply a_scope_pskl__unit.
  - apply a_scope_pskl__var.
    destruct H as [HαΔ | Hbt]; [ apply HΔ; exact HαΔ | ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ];
      apply Hincl; exact Hb.
  - apply a_scope_pskl__arrow;
      [ apply IHHwfd1 | apply IHHwfd2 ]; assumption.
  - apply a_scope_pskl__all with (L := L).
    intros α Hα.
    apply H0; [ exact Hα | | ].
    + intros x b Hb. apply binds_cons_3. apply Hincl; exact Hb.
    + intros β Hβ. destruct (β == α) as [-> | Hne].
      * left. unfold binds. left. reflexivity.
      * destruct (HΔ β ltac:(clear - Hβ Hne; fsetdec))
          as [Hb | [Hb | [τ Hb]]];
          [ left | right; left | right; right; exists τ ];
          apply binds_cons_3; exact Hb.
  - apply a_scope_pskl__hole.
  - apply a_scope_pskl__tophole.
    apply IHHwfd; [ exact Hincl | ].
    intros β Hβ. exfalso. clear - Hβ. fsetdec.
Qed.

(** The join's target erases to a well-formed (Δ-free) skeleton — the
    output-regularity C-Arrow's precision transport needs. *)
Lemma ad_pat_consis_target_wf : forall Ψ Θ R Qt,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Qt ->
  a_scope_pskl Θ (bskl_to_pskl Qt).
Proof.
  intros Ψ Θ R Qt Hc; induction Hc; simpl.
  - apply a_scope_pskl__unit.
  - apply a_scope_pskl__var; exact H0.
  - apply a_scope_pskl__arrow; assumption.
  - (* forall_inh_tagged *)
    apply a_scope_pskl__all with (L := L).
    intros α Hα. rewrite <- bskl_to_pskl_open. apply H0; exact Hα.
  - (* forall_inh_untagged *)
    apply a_scope_pskl__all with (L := L).
    intros α Hα. rewrite <- bskl_to_pskl_open. apply H0; exact Hα.
  - (* forall_syn_tagged *)
    apply a_scope_pskl__all with (L := L).
    intros α Hα. rewrite <- bskl_to_pskl_open. apply H0; exact Hα.
  - (* forall_syn *)
    apply a_scope_pskl__all with (L := L).
    intros α Hα. rewrite <- bskl_to_pskl_open. apply H0; exact Hα.
  - apply a_scope_pskl__hole.
  - apply a_scope_pskl__tophole; assumption.
  - (* hole : the fill is wf by the rule's own premise *)
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    eapply a_wf_pskl_to_a_scope_pskl;
      [ exact H0 | intros x b Hb; exact Hb
      | intros β Hβ; exfalso; clear - Hβ; fsetdec ].
  - apply a_scope_pskl__tophole; assumption.
  - (* tophole_inh *)
    apply a_scope_pskl__all with (L := L).
    intros α Hα. rewrite <- bskl_to_pskl_open. apply H0; exact Hα.
  - (* tophole_drop *) assumption.
  - (* flex_l *) assumption.
  - (* flex_r *)
    apply a_scope_pskl__var. right; right; exists τ; exact H.
Qed.

(** The empty hygiene set is free: the plain refinement IS the
    fill-hygienic one at [F = ∅] (the hole rule's ∅-disjointness is
    trivial).  Lets the precision goal reuse the [_f] transports. *)
Lemma ad_refine_syn_f_of_plain : forall Θ Δ Q Q',
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ Q' ->
  ad_refine_syn_f empty Θ Δ Q Q'.
Proof.
  intros Θ Δ Q Q' H; induction H;
    try solve [ eauto using ad_refine_syn_f ].
  apply ad_refine_syn_f__hole; [ clear; fsetdec | exact H ].
Qed.

(** An inherited quantifier never refines to a guarded skeleton (the target
    of every rule applicable to an [all_inh] source is an [all_inh] or a
    defined flexible whose unfolding is a monotype painting — itself guarded,
    recursing).  Kills the [P0 = ∀.P0'] sub-case of C-UnivGhost2. *)
Lemma ad_refine_syn_f_all_inh_guarded_absurd : forall F Θ Δ Q Q',
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ (bskl_all_inh Q) Q' ->
  guarded_bskl Q' ->
  False.
Proof.
  intros F Θ Δ Q Q' Hwf Hr.
  remember (bskl_all_inh Q) as R eqn:HeqS.
  induction Hr; intros Hg; try discriminate HeqS.
  - (* __all : target is an inherited quantifier, not guarded *)
    inversion Hg.
  - (* __flex_r : unfold the target definition (a monotype, guarded) *)
    apply IHHr; [ exact Hwf | exact HeqS | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** Target-side definition unfolding for the fill-hygienic Δ1-refinement:
    a refinement into a DEFINED flexible target is a refinement into its
    definition's painting (the C-FlexR transport of the core's [flex_r]
    join case).  The [F]-disjointness premise is the [no_flex_dep]
    invariant instantiated at the definition. *)
Lemma ad_refine_syn_f_flex_target_unfold : forall F Θ Δ Q α τ,
  a_wf_aenv Θ ->
  binds α (abind_flex_mono_def τ) Θ ->
  (forall α0, α0 `in` Δ -> binds α0 abind_tvar Θ) ->
  F ∩ ftvar_in_ptyp τ [=] empty ->
  ad_refine_syn_f F Θ Δ Q (bskl_var_f α) ->
  ad_refine_syn_f F Θ Δ Q (ptyp_to_bskl_syn τ).
Proof.
  intros F Θ Δ Q α τ Hwf Hbα HΔ Hdisj Hr.
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
  assert (Hwfτ : a_wf_ptyp Θ τ) by (eapply a_wf_aenv_binds_def_wf; eauto).
  remember (bskl_var_f α) as T eqn:HeqT.
  induction Hr; try discriminate HeqT.
  - (* __var : the source IS the defined flexible; unfold it on the left *)
    inversion HeqT; subst α0.
    assert (Hbtα : binds α abind_tvar Θ \/ binds α abind_flex_mono Θ \/
                   (exists τ', binds α (abind_flex_mono_def τ') Θ)).
    { destruct H as [HinΔ | Hbt]; [ left; apply HΔ; exact HinΔ | exact Hbt ]. }
    destruct Hbtα as [Hb | [Hb | [τ' Hb]]];
      try solve [ pose proof (binds_unique _ _ _ _ _ Hb Hbα
                                (a_wf_aenv_uniq Hwf)) as Hcon; discriminate ].
    eapply ad_refine_syn_f__flex_l; [ exact Hbα | ].
    apply ad_refine_syn_f_mono_refl; assumption.
  - (* __hole : the fill is the defined flexible; refill with its definition *)
    destruct P as [ | n | β1 | | | | ]; simpl in HeqT; try discriminate.
    inversion HeqT; subst β1.
    replace (ptyp_to_bskl_syn τ)
      with (pskl_to_bskl_syn (ptyp_to_pskl τ)) by reflexivity.
    apply ad_refine_syn_f__hole.
    + rewrite ftvar_in_ptyp_to_pskl. exact Hdisj.
    + apply a_wf_ptyp_to_wf_pskl. exact Hwfτ.
  - (* __tophole_remove : arbitrary target; recurse under the source strip *)
    apply ad_refine_syn_f__tophole_remove.
    apply IHHr; assumption.
  - (* __flex_l : source-side unfolding; recurse and re-wrap *)
    eapply ad_refine_syn_f__flex_l; [ exact H | ].
    apply IHHr; assumption.
  - (* __flex_r : the target unfolding itself; definitions agree by uniq *)
    inversion HeqT; subst α0.
    pose proof (binds_unique _ _ _ _ _ H Hbα (a_wf_aenv_uniq Hwf)) as Heq.
    inversion Heq; subst τ0.
    exact Hr.
Qed.

(** Uncoloured version of the target-side definition unfolding. *)
Lemma ad_refine_pskl_f_flex_target_unfold : forall F Θ Δ P α τ,
  a_wf_aenv Θ ->
  binds α (abind_flex_mono_def τ) Θ ->
  (forall α0, α0 `in` Δ -> binds α0 abind_tvar Θ) ->
  F ∩ ftvar_in_ptyp τ [=] empty ->
  ad_refine_pskl_f F Θ Δ P (pskl_var_f α) ->
  ad_refine_pskl_f F Θ Δ P (ptyp_to_pskl τ).
Proof.
  intros F Θ Δ P α τ Hwf Hbα HΔ Hdisj Hr.
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
  assert (Hwfτ : a_wf_ptyp Θ τ) by (eapply a_wf_aenv_binds_def_wf; eauto).
  remember (pskl_var_f α) as T eqn:HeqT.
  induction Hr; try discriminate HeqT.
  - (* __var *)
    inversion HeqT; subst α0.
    assert (Hbtα : binds α abind_tvar Θ \/ binds α abind_flex_mono Θ \/
                   (exists τ', binds α (abind_flex_mono_def τ') Θ)).
    { destruct H as [HinΔ | Hbt]; [ left; apply HΔ; exact HinΔ | exact Hbt ]. }
    destruct Hbtα as [Hb | [Hb | [τ' Hb]]];
      try solve [ pose proof (binds_unique _ _ _ _ _ Hb Hbα
                                (a_wf_aenv_uniq Hwf)) as Hcon; discriminate ].
    eapply ad_refine_pskl_f__flex_l; [ exact Hbα | ].
    apply ad_refine_pskl_f_mono_refl; assumption.
  - (* __hole *)
    inversion HeqT; subst Q.
    apply ad_refine_pskl_f__hole.
    + rewrite ftvar_in_ptyp_to_pskl. exact Hdisj.
    + apply a_wf_ptyp_to_wf_pskl. exact Hwfτ.
  - (* __tophole_remove *)
    apply ad_refine_pskl_f__tophole_remove.
    apply IHHr; assumption.
  - (* __flex_l *)
    eapply ad_refine_pskl_f__flex_l; [ exact H | ].
    apply IHHr; assumption.
  - (* __flex_r *)
    inversion HeqT; subst α0.
    pose proof (binds_unique _ _ _ _ _ H Hbα (a_wf_aenv_uniq Hwf)) as Heq.
    inversion Heq; subst τ0.
    exact Hr.
Qed.

(* ===================================================================== *)
(*  §3  The three induction steps (one per part of the paper's proof)     *)
(* ===================================================================== *)

(** Part 2 of the paper's proof (:2260-2401): unification of flexible
    variables, by a walk of the context [Θ0] (n strictly decreases on the
    walk edges; the Flex-Flex-Assign back-edge re-enters part 1 with [V]
    exactly constant and [n] one smaller). *)
Lemma unify_complete_step : forall m,
  (forall m', mu_lt m' m -> complete_at m') ->
  unify_complete_at m.
Proof.
  intros m IH. unfold unify_complete_at.
  intros N Θ0 α β κ Θ Hm Hwf Hfα Hfβ Hinc Hwfth Heq. subst m.
  destruct (α == β) as [-> | Hne].
  { (* Flex-Flex-Id : axiom, Θ1 = Θ0; ζ := κ. *)
    exists Θ0. split; [ apply a_unify__flex_id; exact Hfα | ].
    split; [ intros γ Hγ; left; exact Hγ | ].
    intros κ1 Hid Hinc1. exists κ.
    exact (opt_axiom_factor Hwf Hid Hinc1 Hinc). }
  assert (Hβα : β <> α) by auto.
  destruct Θ0 as [ | [α1 b] Θ0' ].
  { exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb. }
  destruct b as [ | A | Q | | τdef ].
  - (* head [α1 ~ tvar] : Flex-Flex-Skip' (rigid). *)
    inversion Hwf as [ | | | | | γh Θh Hnd Hwf0 ]; subst.
    assert (Hα1α : α <> α1)
      by (intros ->; destruct Hfα as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hα1β : β <> α1)
      by (intros ->; destruct Hfβ as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hfα0 : a_flex_tvar Θ0' α)
      by (eapply a_flex_tvar_strip_head; [ exact Hα1α | exact Hfα ]).
    assert (Hfβ0 : a_flex_tvar Θ0' β)
      by (eapply a_flex_tvar_strip_head; [ exact Hα1β | exact Hfβ ]).
    assert (Hbtα : a_binds_tvar α Θ0') by (right; exact Hfα0).
    assert (Hbtβ : a_binds_tvar β Θ0') by (right; exact Hfβ0).
    apply a_inc_tvar_inv in Hinc as [Ξ [Θ2 [-> [HΞ Hinc']]]].
    assert (Hwfth2 : a_wf_aenv Θ2)
      by (rewrite <- app_assoc in Hwfth;
          apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
    assert (Hwflα : a_wf_ptyp Θ2 (msubst_lookup κ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]).
    assert (Hwflβ : a_wf_ptyp Θ2 (msubst_lookup κ β))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]).
    assert (Heq2 : Θ2 ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup κ β)).
    { eapply a_tyequiv_strengthen_mono_mid;
        [ exact Hwfth | exact Hwflα
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Hwflβ
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Heq ]. }
    assert (Huniq : uniq (Ξ ++ (α1 ~ abind_tvar) ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hlt : mu_lt (mu_unify Θ2 κ α β Θ0')
                        (mu_unify (Ξ ++ (α1 ~ abind_tvar) ++ Θ2) κ α β
                                  ((α1 ~ abind_tvar) ++ Θ0'))).
    { unfold mu_unify. apply mu_lt_intro. right. split.
      - unfold V_unify.
        rewrite (@Vvar_strengthen_mid Ξ α1 abind_tvar Θ2 κ α Huniq Hwflα).
        rewrite (@Vvar_strengthen_mid Ξ α1 abind_tvar Θ2 κ β Huniq Hwflβ).
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add α1 N) Θ0' α β κ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu [Hnew Hopt']]].
    exists ((α1 ~ abind_tvar) ++ Θ1'). split.
    { apply a_unify__skip_other;
        [ left; reflexivity | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss; [ exact Hnew | exact Hnd ] | exact Hu ]. }
    split; [ eapply avoid_relay_cons; exact Hnew | ].
    intros κ1 Hid Hinc1.
    assert (Hinc1' : κ1 ∷ Θ0' ⊑ Θ1')
      by (eapply a_inc_id_mid_strip; [ left; reflexivity | exact Hinc1 ]).
    destruct (Hopt' κ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
    exists ζ'. split.
    + apply a_inc__tvar; [ exact Hζ' | exact HΞ ].
    + apply a_inc_equiv__tvar; [ exact Hie' | exact HΞ ].
  - (* head [x ~ var_typ A] : Flex-Flex-Skip' (semantic type middle). *)
    destruct (a_wf_aenv_var_typ_inv Hwf) as [Hnd [HwfA Hwf0]].
    assert (Hα1α : α <> α1)
      by (intros ->; destruct Hfα as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hα1β : β <> α1)
      by (intros ->; destruct Hfβ as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hfα0 : a_flex_tvar Θ0' α)
      by (eapply a_flex_tvar_strip_head; [ exact Hα1α | exact Hfα ]).
    assert (Hfβ0 : a_flex_tvar Θ0' β)
      by (eapply a_flex_tvar_strip_head; [ exact Hα1β | exact Hfβ ]).
    assert (Hbtα : a_binds_tvar α Θ0') by (right; exact Hfα0).
    assert (Hbtβ : a_binds_tvar β Θ0') by (right; exact Hfβ0).
    apply a_inc_var_inv in Hinc as [Ξ [A' [Θ2 [-> [HA'eq [HΞ Hinc']]]]]].
    assert (Hwfth2 : a_wf_aenv Θ2)
      by (rewrite <- app_assoc in Hwfth;
          apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
    assert (Hwflα : a_wf_ptyp Θ2 (msubst_lookup κ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]).
    assert (Hwflβ : a_wf_ptyp Θ2 (msubst_lookup κ β))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]).
    assert (Heq2 : Θ2 ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup κ β)).
    { eapply a_tyequiv_strengthen_mono_mid;
        [ exact Hwfth | exact Hwflα
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Hwflβ
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Heq ]. }
    assert (Huniq : uniq (Ξ ++ (α1 ~ abind_var_typ A') ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hlt : mu_lt (mu_unify Θ2 κ α β Θ0')
                        (mu_unify (Ξ ++ (α1 ~ abind_var_typ A') ++ Θ2) κ α β
                                  ((α1 ~ abind_var_typ A) ++ Θ0'))).
    { unfold mu_unify. apply mu_lt_intro. right. split.
      - unfold V_unify.
        rewrite (@Vvar_strengthen_mid Ξ α1 (abind_var_typ A') Θ2 κ α Huniq Hwflα).
        rewrite (@Vvar_strengthen_mid Ξ α1 (abind_var_typ A') Θ2 κ β Huniq Hwflβ).
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add α1 N) Θ0' α β κ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu [Hnew Hopt']]].
    exists ((α1 ~ abind_var_typ A) ++ Θ1'). split.
    { apply a_unify__skip_other;
        [ right; left; exists A; reflexivity | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss; [ exact Hnew | exact Hnd ] | exact Hu ]. }
    split; [ eapply avoid_relay_cons; exact Hnew | ].
    intros κ1 Hid Hinc1.
    assert (Hinc1' : κ1 ∷ Θ0' ⊑ Θ1')
      by (eapply a_inc_id_mid_strip;
          [ right; left; exists A; reflexivity | exact Hinc1 ]).
    destruct (Hopt' κ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
    destruct (a_unify_sound Hu Hwf0)
      as [[[w [Hidw Hincw]] _] [Hwf1' _]].
    assert (Hbridge : Θ2 ⊢ A' ≡ᵗ (msubst_ptyp ζ' A)).
    { eapply a_tyequiv__trans; [ exact HA'eq | ].
      rewrite <- (msubst_compose_id_ptyp Hwf0 Hwf1' Hid Hinc1' Hζ' HwfA).
      eapply a_inc_equiv_msubst_ptyp;
        [ exact HwfA | exact Hie' | exact Hwf0
        | eapply a_inc_msubst_lc; exact Hinc'
        | eapply msubst_lc_compose;
            [ eapply a_inc_msubst_lc; exact Hζ'
            | eapply is_id_msubst_values_lc; exact Hid ] ]. }
    exists ζ'. split.
    + apply a_inc__var; [ exact Hζ' | exact Hbridge | exact HΞ ].
    + apply a_inc_equiv__var; [ exact Hie' | exact HA'eq | exact HΞ ].
  - (* head [x ~ var_skl Q] : Flex-Flex-Skip' (semantic skeleton middle). *)
    destruct (a_wf_aenv_var_skl_inv Hwf) as [Hnd [HwfQ Hwf0]].
    assert (Hα1α : α <> α1)
      by (intros ->; destruct Hfα as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hα1β : β <> α1)
      by (intros ->; destruct Hfβ as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hfα0 : a_flex_tvar Θ0' α)
      by (eapply a_flex_tvar_strip_head; [ exact Hα1α | exact Hfα ]).
    assert (Hfβ0 : a_flex_tvar Θ0' β)
      by (eapply a_flex_tvar_strip_head; [ exact Hα1β | exact Hfβ ]).
    assert (Hbtα : a_binds_tvar α Θ0') by (right; exact Hfα0).
    assert (Hbtβ : a_binds_tvar β Θ0') by (right; exact Hfβ0).
    apply a_inc_var_skl_inv in Hinc as [Ξ [P' [Θ2 [-> [HP'eq [HΞ Hinc']]]]]].
    assert (Hwfth2 : a_wf_aenv Θ2)
      by (rewrite <- app_assoc in Hwfth;
          apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
    assert (Hwflα : a_wf_ptyp Θ2 (msubst_lookup κ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]).
    assert (Hwflβ : a_wf_ptyp Θ2 (msubst_lookup κ β))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]).
    assert (Heq2 : Θ2 ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup κ β)).
    { eapply a_tyequiv_strengthen_mono_mid;
        [ exact Hwfth | exact Hwflα
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Hwflβ
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Heq ]. }
    assert (Huniq : uniq (Ξ ++ (α1 ~ abind_var_skl P') ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hlt : mu_lt (mu_unify Θ2 κ α β Θ0')
                        (mu_unify (Ξ ++ (α1 ~ abind_var_skl P') ++ Θ2) κ α β
                                  ((α1 ~ abind_var_skl Q) ++ Θ0'))).
    { unfold mu_unify. apply mu_lt_intro. right. split.
      - unfold V_unify.
        rewrite (@Vvar_strengthen_mid Ξ α1 (abind_var_skl P') Θ2 κ α Huniq Hwflα).
        rewrite (@Vvar_strengthen_mid Ξ α1 (abind_var_skl P') Θ2 κ β Huniq Hwflβ).
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add α1 N) Θ0' α β κ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu [Hnew Hopt']]].
    exists ((α1 ~ abind_var_skl Q) ++ Θ1'). split.
    { apply a_unify__skip_other;
        [ right; right; exists Q; reflexivity | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss; [ exact Hnew | exact Hnd ] | exact Hu ]. }
    split; [ eapply avoid_relay_cons; exact Hnew | ].
    intros κ1 Hid Hinc1.
    assert (Hinc1' : κ1 ∷ Θ0' ⊑ Θ1')
      by (eapply a_inc_id_mid_strip;
          [ right; right; exists Q; reflexivity | exact Hinc1 ]).
    destruct (Hopt' κ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
    destruct (a_unify_sound Hu Hwf0)
      as [[[w [Hidw Hincw]] _] [Hwf1' _]].
    assert (Hbridge : Θ2 ⊢ P' ≡ˢ (msubst_pskl ζ' Q)).
    { eapply a_pskl_tyequiv__trans; [ exact HP'eq | ].
      rewrite <- (msubst_compose_id_pskl Hwf0 Hwf1' Hid Hinc1' Hζ' HwfQ).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HwfQ | exact Hie' | exact Hwf0
        | eapply a_inc_msubst_lc; exact Hinc'
        | eapply msubst_lc_compose;
            [ eapply a_inc_msubst_lc; exact Hζ'
            | eapply is_id_msubst_values_lc; exact Hid ] ]. }
    exists ζ'. split.
    + apply a_inc__var_skl; [ exact Hζ' | exact Hbridge | exact HΞ ].
    + apply a_inc_equiv__var_skl; [ exact Hie' | exact HP'eq | exact HΞ ].
  - (* head [α1̂] undefined flexible : Flex-Flex-L / Flex-Flex-R / Skip. *)
    inversion Hwf as [ | γh Θh Hnd Hwf0 | | | | ]; subst.
    destruct (α1 == α) as [-> | Hα1α].
    + (* Flex-Flex-L : α̂ ≔ β̂; axiom, ζ := κ. *)
      inversion Hinc as [ | Θs κs Θt αs τ Hinc' Hwfτ Hmτ [Heqα Heqκ] Heqt
                        | | | | ]; subst.
      assert (Hfβ0 : a_flex_tvar Θ0' β)
        by (eapply a_flex_tvar_strip_head; [ exact Hβα | exact Hfβ ]).
      exists ((α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0'). split.
      { apply a_unify__flex_l; [ exact Hne | exact Hfβ0 ]. }
      split; [ apply avoid_same_dom | ].
      intros κ1 Hid Hinc1. exists ((α, τ) :: κs). split.
      * apply a_inc__flex_def; auto.
        rewrite msubst_lookup_cons_eq in Heq.
        rewrite (msubst_lookup_cons_neq τ κs Hβα) in Heq.
        exact Heq.
      * rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
        apply a_inc_equiv_refl; exact Hinc.
    + destruct (α1 == β) as [-> | Hα1β].
      * (* Flex-Flex-R : β̂ ≔ α̂; axiom, ζ := κ. *)
        inversion Hinc as [ | Θs κs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqκ] Heqt
                          | | | | ]; subst.
        assert (Hα1α' : α <> β) by exact Hne.
        assert (Hfα0 : a_flex_tvar Θ0' α)
          by (eapply a_flex_tvar_strip_head; [ exact Hne | exact Hfα ]).
        exists ((β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0'). split.
        { apply a_unify__flex_r; [ exact Hne | exact Hfα0 ]. }
        split; [ apply avoid_same_dom | ].
        intros κ1 Hid Hinc1. exists ((β, τ) :: κs). split.
        -- apply a_inc__flex_def; auto.
           rewrite msubst_lookup_cons_eq in Heq.
           rewrite (msubst_lookup_cons_neq τ κs Hα1α') in Heq.
           apply a_tyequiv__sym; exact Heq.
        -- rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
           apply a_inc_equiv_refl; exact Hinc.
      * (* Flex-Flex-Skip : α1̂ ∉ {α̂, β̂} walked past. *)
        inversion Hinc as [ | Θs κs Θt α1s τα1 Hincs Hwfτ Hmτ [Heqγ Heqκ] Heqt
                          | | | | ]; subst.
        assert (Hαα1 : α <> α1) by auto.
        assert (Hβα1 : β <> α1) by auto.
        assert (Hfα0 : a_flex_tvar Θ0' α)
          by (eapply a_flex_tvar_strip_head; [ exact Hαα1 | exact Hfα ]).
        assert (Hfβ0 : a_flex_tvar Θ0' β)
          by (eapply a_flex_tvar_strip_head; [ exact Hβα1 | exact Hfβ ]).
        rewrite (msubst_lookup_cons_neq τα1 κs Hαα1) in Heq.
        rewrite (msubst_lookup_cons_neq τα1 κs Hβα1) in Heq.
        assert (Hlt : mu_lt (mu_unify Θ κs α β Θ0')
                            (mu_unify Θ ((α1, τα1) :: κs) α β
                                      ((α1 ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_unify. apply mu_lt_intro. right. split.
          - unfold V_unify, Vvar.
            rewrite (msubst_lookup_cons_neq τα1 κs Hαα1).
            rewrite (msubst_lookup_cons_neq τα1 κs Hβα1).
            reflexivity.
          - left. simpl. lia. }
        destruct (IH _ Hlt) as [_ [HuIH _]].
        destruct (HuIH (add α1 N) Θ0' α β κs Θ eq_refl Hwf0 Hfα0 Hfβ0
                       Hincs Hwfth Heq) as [Θ1' [Hu [Hnew Hopt']]].
        exists ((α1 ~ abind_flex_mono) ++ Θ1'). split.
        { apply a_unify__flex_skip;
            [ auto | auto | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss; [ exact Hnew | exact Hnd ] | exact Hu ]. }
        split; [ eapply avoid_relay_cons; exact Hnew | ].
        intros κ1 Hid Hinc1.
        inversion Hinc1 as [ | Θp κp Θq α1p τp Hincp Hwfp Hmp [Heqγ1 Heqκ1] Heqt1
                           | | | | ]; subst.
        apply is_id_msubst_inv in Hid as [Heqτp Hid']; subst τp.
        destruct (a_unify_sound Hu Hwf0)
          as [[[w [Hidw Hincw]] _] _].
        assert (Hw : κp = w)
          by (eapply is_id_inc_unique; eauto).
        subst w.
        assert (Hγw : α1 `notin` dom κp)
          by (pose proof (a_inc_dom_sub Hincw) as Hs; clear - Hs Hnd; fsetdec).
        destruct (Hopt' κp Hid' Hincw) as [ζ' [Hζ' Hie']].
        exists ((α1, τα1) :: ζ'). split.
        -- apply a_inc__flex; auto.
        -- assert (Heqc : msubst_compose ((α1, τα1) :: ζ') ((α1, ptyp_var_f α1) :: κp)
                         = (α1, τα1) :: msubst_compose ζ' κp).
           { change (msubst_compose ((α1, τα1) :: ζ') ((α1, ptyp_var_f α1) :: κp))
               with ((α1, msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
                     :: msubst_compose ((α1, τα1) :: ζ') κp).
             rewrite (msubst_compose_cons_l_id τα1 ζ' Hid' Hγw).
             change (msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
               with (msubst_lookup ((α1, τα1) :: ζ') α1).
             rewrite msubst_lookup_cons_eq. reflexivity. }
           rewrite Heqc.
           apply a_inc_equiv__flex; [ exact Hie' | ].
           apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτ.
  - (* head [α1̂ ≔ τdef] : Flex-Flex-Assign, the back-edge into part 1. *)
    inversion Hwf as [ | | γh τh Θh Hnd Hwfτd Hmτd Hwf0 | | | ]; subst.
    inversion Hinc as [ | | Θs κs Θt α1s τd τα1 Hinc' Hwfτα1 Hmτα1 Heqd
                          [Heqγ Heqκ] Heqt | | | ]; subst.
    (* the substituted subjects and their facts, uniformly in the variable *)
    assert (Hgen : forall β1,
        a_flex_tvar ((α1 ~ abind_flex_mono_def τdef) ++ Θ0') β1 ->
        a_wf_ptyp Θ0' (subst_ptyp_in_ptyp τdef α1 (ptyp_var_f β1)) /\
        mono_ptyp (subst_ptyp_in_ptyp τdef α1 (ptyp_var_f β1)) /\
        Θ ⊢ (msubst_ptyp κs (subst_ptyp_in_ptyp τdef α1 (ptyp_var_f β1)))
          ≡ᵗ (msubst_lookup ((α1, τα1) :: κs) β1)).
    { intros β1 Hfδ. cbn [subst_ptyp_in_ptyp].
      destruct_if as [-> | Hβ1α1].
      - repeat split;
          [ exact Hwfτd | exact Hmτd
          | rewrite msubst_lookup_cons_eq;
            apply a_tyequiv__sym; exact Heqd ].
      - assert (Hfδ' : a_flex_tvar Θ0' β1)
          by (eapply a_flex_tvar_strip_head; [ exact Hβ1α1 | exact Hfδ ]).
        repeat split.
        + apply a_wf_ptyp__var. right. exact Hfδ'.
        + apply mono_ptyp__var.
        + rewrite (msubst_lookup_cons_neq τα1 κs Hβ1α1).
          cbn [msubst_ptyp].
          apply a_tyequiv__refl. apply mono_ptyp_lc.
          eapply a_inc_lookup_mono; exact Hinc'. }
    destruct (Hgen α Hfα) as [HwfAσ [HmAσ HeqAκ]].
    destruct (Hgen β Hfβ) as [HwfBσ [HmBσ HeqBκ]].
    clear Hgen.
    set (Aσ := subst_ptyp_in_ptyp τdef α1 (ptyp_var_f α)) in *.
    set (Bσ := subst_ptyp_in_ptyp τdef α1 (ptyp_var_f β)) in *.
    (* the sub-node's solution facts *)
    assert (HmA' : mono_ptyp (msubst_ptyp κs Aσ))
      by (eapply mono_ptyp_msubst; [ exact Hinc' | exact HmAσ ]).
    assert (HmB' : mono_ptyp (msubst_ptyp κs Bσ))
      by (eapply mono_ptyp_msubst; [ exact Hinc' | exact HmBσ ]).
    assert (HwfA' : a_wf_ptyp Θ (msubst_ptyp κs Aσ))
      by (eapply a_wf_ptyp_msubst; [ exact HwfAσ | exact Hwf0 | exact Hinc' ]).
    assert (HwfB' : a_wf_ptyp Θ (msubst_ptyp κs Bσ))
      by (eapply a_wf_ptyp_msubst; [ exact HwfBσ | exact Hwf0 | exact Hinc' ]).
    assert (HeqAB : Θ ⊢ (msubst_ptyp κs Aσ) ≡ᵗ (msubst_ptyp κs Bσ)).
    { eapply a_tyequiv__trans; [ exact HeqAκ | ].
      eapply a_tyequiv__trans; [ exact Heq | ].
      apply a_tyequiv__sym; exact HeqBκ. }
    assert (Hjoin0 : empty ⨟ Θ ⊢ₛᵃ (ptyp_to_uskl_syn (msubst_ptyp κs Aσ))
                       ∼ (ptyp_to_bskl_syn (msubst_ptyp κs Bσ))).
    { apply tyequiv_mono_consis;
        [ exact HeqAB | exact Hwfth | exact HmA'
        | intros α0 Hα0; eapply a_wf_ptyp_ftv_tvarish;
            [ exact HwfA' | exact Hα0 ] ]. }
    assert (Hjoin' : empty ⨟ Θ ⊢ₛᵃ
              (pskl_to_uskl (msubst_pskl κs (ptyp_to_pskl Aσ)))
              ∼ (ptyp_to_bskl_syn (msubst_ptyp κs Bσ)))
      by (rewrite msubst_pskl_ptyp_to_pskl, pskl_to_uskl_ptyp; exact Hjoin0).
    assert (Hrs' : ad_refine_syn_f empty Θ empty
              (pskl_to_bskl_inh (msubst_pskl κs (ptyp_to_pskl Bσ)))
              (ptyp_to_bskl_syn (msubst_ptyp κs Bσ))).
    { rewrite msubst_pskl_ptyp_to_pskl.
      replace (pskl_to_bskl_inh (ptyp_to_pskl (msubst_ptyp κs Bσ)))
        with (pskl_to_bskl_inh (uskl_to_pskl (ptyp_to_uskl_syn (msubst_ptyp κs Bσ))))
        by (rewrite uskl_to_pskl_ptyp; reflexivity).
      eapply ad_pat_consis_refine_syn_f_mono;
        [ apply consis_mono_refl;
            [ exact HmB'
            | intros α0 Hα0; eapply a_wf_ptyp_ftv_tvarish;
                [ exact HwfB' | exact Hα0 ] ]
        | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmB'
        | clear; fsetdec
        | intros β0 τ0 Hb0; clear; fsetdec ]. }
    assert (Hrp' : ad_refine_pskl_f empty Θ empty
              (msubst_pskl κs (ptyp_to_pskl Aσ))
              (bskl_to_pskl (ptyp_to_bskl_syn (msubst_ptyp κs Bσ)))).
    { rewrite msubst_pskl_ptyp_to_pskl.
      replace (ptyp_to_pskl (msubst_ptyp κs Aσ))
        with (uskl_to_pskl (ptyp_to_uskl_syn (msubst_ptyp κs Aσ)))
        by (apply uskl_to_pskl_ptyp).
      eapply ad_pat_consis_refine_pskl_f_mono;
        [ exact Hjoin0 | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmB'
        | clear; fsetdec
        | intros β0 τ0 Hb0; clear; fsetdec ]. }
    assert (Hpsi : (empty : atoms) [=] empty) by fsetdec.
    assert (HwfPA : Θ0' ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl Aσ))
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfAσ).
    assert (HwfPB : Θ0' ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl Bσ))
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfBσ).
    (* the measure: V constant (the back-edge unfolds a definition the
       solution had already unfolded), n one smaller. *)
    assert (Hlt : mu_lt
        (mu_consis Θ κs (ptyp_to_pskl Bσ) (ptyp_to_pskl Aσ) Θ0')
        (mu_unify Θ ((α1, τα1) :: κs) α β
                  ((α1 ~ abind_flex_mono_def τdef) ++ Θ0'))).
    { unfold mu_consis, mu_unify. apply mu_lt_intro. right. split.
      - unfold V_consis, V_unify.
        rewrite (Vpskl_ptyp_to_pskl Θ κs Aσ).
        rewrite (Vpskl_ptyp_to_pskl Θ κs Bσ).
        unfold Aσ, Bσ.
        rewrite (@Vvar_backedge Θ κs α1 τdef τα1 α Hwfth Heqd).
        rewrite (@Vvar_backedge Θ κs α1 τdef τα1 β Hwfth Heqd).
        unfold Vvar, Vptyp; cbn [msubst_ptyp]; reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH (add α1 N) empty empty Θ0' (ptyp_to_pskl Bσ)
                   (ptyp_to_pskl Aσ) κs Θ empty
                   (ptyp_to_bskl_syn (msubst_ptyp κs Bσ))
                   eq_refl Hwf0 HwfPB HwfPA
                   ltac:(intros α0 Hα0; exfalso; clear - Hα0; fsetdec)
                   ltac:(repeat intro; fsetdec)
                   ltac:(repeat intro; fsetdec)
                   Hinc' Hwfth
                   ltac:(repeat intro; fsetdec)
                   Hpsi Hjoin' Hrs' Hrp')
      as [P1 [Θ1' [Hcons [Hnew Hopt']]]].
    exists ((α1 ~ abind_flex_mono_def τdef) ++ Θ1'). split.
    { eapply a_unify__flex_assign;
        [ exact Hfα | exact Hfβ | | exact Hcons ].
      (* the walked definition is in the relayed avoid set [add α1 N] and
         fresh for the input, so it misses the output *)
      eapply avoid_head_miss; [ exact Hnew | exact Hnd ]. }
    split; [ eapply avoid_relay_cons; exact Hnew | ].
    intros κ1 Hid Hinc1.
    inversion Hinc1 as [ | | Θp κp Θq α1p τd1 τ1 Hincp Hwf1p Hm1p Heq1p
                           [Heqγ1 Heqκ1] Heqt1 | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ1 Hid']; subst τ1.
    (* the sub-derivation's own soundness: id-witness + target wf *)
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ Hcons
                Hwf0 HwfPB HwfPA
                ltac:(intros α0 Hα0; exfalso; clear - Hα0; fsetdec)
                ltac:(repeat intro; fsetdec)
                ltac:(repeat intro; fsetdec))
      as [[[w [Hidw Hincw]] _] [Hwf1' _]].
    assert (Hw : κp = w) by (eapply is_id_inc_unique; eauto).
    subst w.
    assert (Hγw : α1 `notin` dom κp)
      by (pose proof (a_inc_dom_sub Hincw) as Hs; clear - Hs Hnd; fsetdec).
    destruct (Hopt' κp Hid' Hincw) as [ζ' [Hζ' [Hie' _]]].
    exists ((α1, τα1) :: ζ'). split.
    + apply a_inc__flex_def; [ exact Hζ' | exact Hwfτα1 | exact Hmτα1 | ].
      (* the definition's image transports across the equivalent increments *)
      eapply a_tyequiv__trans; [ exact Heqd | ].
      rewrite <- (msubst_compose_id_ptyp Hwf0 Hwf1' Hid' Hincw Hζ' Hwfτd).
      eapply a_inc_equiv_msubst_ptyp;
        [ exact Hwfτd | exact Hie' | exact Hwf0
        | eapply a_inc_msubst_lc; exact Hinc'
        | eapply msubst_lc_compose;
            [ eapply a_inc_msubst_lc; exact Hζ'
            | eapply is_id_msubst_values_lc; exact Hidw ] ].
    + assert (Heqc : msubst_compose ((α1, τα1) :: ζ') ((α1, ptyp_var_f α1) :: κp)
                     = (α1, τα1) :: msubst_compose ζ' κp).
      { change (msubst_compose ((α1, τα1) :: ζ') ((α1, ptyp_var_f α1) :: κp))
          with ((α1, msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
                :: msubst_compose ((α1, τα1) :: ζ') κp).
        rewrite (msubst_compose_cons_l_id τα1 ζ' Hid' Hγw).
        change (msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
          with (msubst_lookup ((α1, τα1) :: ζ') α1).
        rewrite msubst_lookup_cons_eq. reflexivity. }
      rewrite Heqc.
      apply a_inc_equiv__flex_def;
        [ exact Hie'
        | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτα1
        | exact Heqd ].
Qed.

(** Part 3 of the paper's proof (:2403-2559): assignment, by a walk of the
    context pair [Θ0 ∣ Ξ] ([n = |Ξ|+|Θ0|] on the skips, [k = |Θ0|] on
    Assign-Depend; the Assign-Assign back-edge re-enters part 1 with [V]
    constant and [n] one smaller). *)
(** Decidable equality of skeletons (for the UnivGhost-Id shape test). *)
Lemma pskl_eq_dec : forall (P Q : pskl), sumbool (P = Q) (P <> Q).
Proof.
  decide equality; solve [ apply Nat.eq_dec | apply eq_var ].
Qed.

(* ===================================================================== *)
(*  §2f  Assign-SolveM enablers: metasubstitution helpers                                    *)
(* ===================================================================== *)

(** Deciding whether a skeleton is a free variable. *)
Lemma pskl_var_dec : forall P,
  (exists α, P = pskl_var_f α) \/ (forall α, P <> pskl_var_f α).
Proof.
  destruct P;
    first [ left; eexists; reflexivity
          | right; intros ? Hcx; discriminate Hcx ].
Qed.

(** An identity metasubstitution's mid entry is the identity on its key. *)
Lemma is_id_msubst_mid : forall κa β τ κb,
  is_id_msubst (κa ++ (β, τ) :: κb) ->
  τ = ptyp_var_f β /\ is_id_msubst (κa ++ κb).
Proof.
  induction κa as [ | [a t] κa' IH ]; intros β τ κb Hid; simpl in *.
  - apply is_id_msubst_inv in Hid as [Heq Hid']; auto.
  - inversion Hid as [ | e es He Hes ]; subst.
    destruct (IH _ _ _ Hes) as [Heq Hid']; subst.
    split; [ reflexivity | constructor; assumption ].
Qed.

(** Composition with an identity multiplicand only reads the left factor's
    lookups on the identity's keys. *)
Lemma msubst_compose_agree_id : forall ζ ζ' κ1,
  is_id_msubst κ1 ->
  (forall α, α `in` dom κ1 -> msubst_lookup ζ α = msubst_lookup ζ' α) ->
  msubst_compose ζ κ1 = msubst_compose ζ' κ1.
Proof.
  intros ζ ζ' κ1; induction κ1 as [ | [a t] κ1' IH ]; intros Hid Hag;
    [ reflexivity | ].
  apply is_id_msubst_inv in Hid as [Heq Hid']; subst.
  unfold msubst_compose in *; simpl.
  rewrite (Hag a) by (simpl; fsetdec).
  rewrite IH; [ reflexivity | exact Hid' | ].
  intros α Hα. apply Hag. simpl. fsetdec.
Qed.

(** [msubst_compose_is_id_r] with a source-disjoint prefix on the left
    factor: the prefix is never consulted on the identity's keys. *)
Lemma msubst_compose_is_id_r_ext : forall Θ0 κ1 Θ1 κ Θ ζpre,
  a_wf_aenv Θ0 ->
  is_id_msubst κ1 ->
  κ1 ∷ Θ0 ⊑ Θ1 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` dom ζpre -> α `notin` dom Θ0) ->
  msubst_compose (ζpre ++ κ) κ1 = κ.
Proof.
  intros Θ0 κ1 Θ1 κ Θ ζpre Hwf Hid Hinc1 Hinc Hdisj.
  assert (Hag : forall α, α `in` dom κ1 ->
            msubst_lookup (ζpre ++ κ) α = msubst_lookup κ α).
  { intros α Hα.
    pose proof (a_inc_dom_sub Hinc1) as Hsub.
    apply msubst_lookup_app_notin.
    assert (HαΘ0 : α `in` dom Θ0) by (clear - Hα Hsub; fsetdec).
    destruct (AtomSetProperties.In_dec α (dom ζpre)) as [Hin | Hni];
      [ exfalso; exact (Hdisj α Hin HαΘ0) | exact Hni ]. }
  rewrite (@msubst_compose_agree_id (ζpre ++ κ) κ κ1 Hid Hag).
  eapply msubst_compose_is_id_r; eauto.
Qed.

(* ===================================================================== *)
(*  §2g  Assign-SolveM: the var-base mono bridge                          *)
(* ===================================================================== *)

Lemma join_var_tyequiv : forall Ψ Θ A A',
  Ψ ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (ptyp_to_pskl A)) ∼ (ptyp_to_bskl_syn A') ->
  a_wf_aenv Θ ->
  mono_ptyp A ->
  mono_ptyp A' ->
  Θ ⊢ A ≡ᵗ A'.
Proof.
  intros Ψ Θ A A' Hc Hwf HmA HmC.
  rewrite ptyp_to_uskl_syn_eq in Hc.
  destruct (consis_mono_join Hc Hwf (A := A) eq_refl HmA)
    as [C' [HmC' [HeqQ Heqv]]].
  assert (HeqC : C' = A')
    by (apply ptyp_to_bskl_syn_inj; auto).
  subst C'. exact Heqv.
Qed.

(* ===================================================================== *)
(*  §2h  Assign-SolveM: OCCURS — the α-occurrence size walk                               *)
(* ===================================================================== *)

Lemma occurs_join_size_aux : forall Ψ Θ R' Q,
  Ψ ⨟ Θ ⊢ₛᵃ R' ∼ Q ->
  a_wf_aenv Θ ->
  forall κm,
  (forall α', mono_ptyp (msubst_lookup κm α')) ->
  forall α P A Θw Δw,
    (forall α', P <> pskl_var_f α') ->
    R' = pskl_to_uskl (msubst_pskl κm P) ->
    Q = ptyp_to_bskl_syn A ->
    mono_ptyp A ->
    Θw ⨟ Δw ⊢ₚₛᵃ P ->
    α `in` ftvar_in_pskl P ->
    size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α)) <= size_ptyp (⇓ᵗ[Θ] A) /\
    (P = pskl_tophole (pskl_var_f α) \/
     size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α)) < size_ptyp (⇓ᵗ[Θ] A)).
Proof.
  intros Ψ Θ R' Q Hc Hwf κm Hmlk.
  induction Hc; intros α0 P0 C0 Θw Δw Hnv HeqS HeqQ HmC0 HwfP0 Hocc.
  - (* unit *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    simpl in Hocc. exfalso. clear - Hocc. fsetdec.
  - (* var *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* arrow *)
    destruct P0 as [ | | α' | P1 P2 | | | ]; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    inversion HeqS; subst R1 R2.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst Q1 Q2.
    inversion HmC0; subst.
    match goal with H : mono_ptyp C1 |- _ => rename H into HmC1 end.
    match goal with H : mono_ptyp C2 |- _ => rename H into HmC2 end.
    inversion HwfP0; subst.
    match goal with H : Θw ⨟ Δw ⊢ₚₛᵃ P1 |- _ => rename H into HwfP1 end.
    match goal with H : Θw ⨟ Δw ⊢ₚₛᵃ P2 |- _ => rename H into HwfP2 end.
    simpl in Hocc. apply union_1 in Hocc.
    destruct Hocc as [Hocc | Hocc].
    + (* α ∈ ftv P1 *)
      assert (Hle : size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α0))
                      <= size_ptyp (⇓ᵗ[Θ] C1)).
      { destruct (pskl_var_dec P1) as [[α'1 HeqP1] | Hnv1].
        - subst P1. simpl in Hocc.
          assert (HeqX : α'1 = α0) by (clear - Hocc; fsetdec). subst α'1.
          simpl in Hc1.
          rewrite (a_tyequiv_downarrow Hwf
                     (join_var_tyequiv Hc1 Hwf (Hmlk α0) HmC1)).
          lia.
        - destruct (IHHc1 Hwf α0 P1 C1 Θw Δw Hnv1 eq_refl eq_refl
                      HmC1 HwfP1 Hocc) as [Hle1 _].
          exact Hle1. }
      split; [ | right ];
        simpl; pose proof (size_ptyp_min (⇓ᵗ[Θ] C2)); lia.
    + (* α ∈ ftv P2 *)
      assert (Hle : size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α0))
                      <= size_ptyp (⇓ᵗ[Θ] C2)).
      { destruct (pskl_var_dec P2) as [[α'2 HeqP2] | Hnv2].
        - subst P2. simpl in Hocc.
          assert (HeqX : α'2 = α0) by (clear - Hocc; fsetdec). subst α'2.
          simpl in Hc2.
          rewrite (a_tyequiv_downarrow Hwf
                     (join_var_tyequiv Hc2 Hwf (Hmlk α0) HmC2)).
          lia.
        - destruct (IHHc2 Hwf α0 P2 C2 Θw Δw Hnv2 eq_refl eq_refl
                      HmC2 HwfP2 Hocc) as [Hle2 _].
          exact Hle2. }
      split; [ | right ];
        simpl; pose proof (size_ptyp_min (⇓ᵗ[Θ] C1)); lia.
  - (* forall_inh_tagged : R' = uskl_all_etag, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_inh_untagged : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* forall_syn_tagged : R' = uskl_all_etag, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_syn : Q = bskl_all_syn, mono A refutes *)
    destruct C0; simpl in HeqQ; try discriminate. inversion HmC0.
  - (* ghostg : R' = uskl_holeg, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* topholeg : R' = uskl_topholeg, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* hole : P = hole, no free variables *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    simpl in Hocc. exfalso. clear - Hocc. fsetdec.
  - (* tophole : Q = bskl_tophole, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* tophole_inh : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* tophole_drop : P = ∀◇P', same A *)
    destruct P0 as [ | | | | | | P' ]; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    inversion HeqS; subst R.
    inversion HwfP0; subst.
    match goal with H : guarded_pskl P' |- _ => rename H into Hgu end.
    match goal with H : _ ⨟ empty ⊢ₚₛᵃ P' |- _ => rename H into HwfP' end.
    simpl in Hocc.
    destruct (pskl_var_dec P') as [[α'' HeqP'] | Hnv'].
    + (* P = ∀◇α'' : the drop-to-var base *)
      subst P'. simpl in Hocc.
      assert (HeqX : α'' = α0) by (clear - Hocc; fsetdec). subst α''.
      simpl in Hc.
      rewrite (a_tyequiv_downarrow Hwf
                 (join_var_tyequiv Hc Hwf (Hmlk α0) HmC0)).
      split; [ lia | left; reflexivity ].
    + (* body not a var : recurse; P' = ∀◇α̂ is killed by guardedness *)
      destruct (IHHc Hwf α0 P' C0 Θw empty Hnv' eq_refl eq_refl
                  HmC0 HwfP' Hocc) as [Hle Hdisj].
      split; [ exact Hle | right ].
      destruct Hdisj as [HeqP' | Hlt]; [ | exact Hlt ].
      subst P'. inversion Hgu.
  - (* flex_l : R' = uskl_var, P must be a var — excluded *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* flex_r : unfold the RHS definition, same P *)
    destruct C0 as [ | | α'0 | | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst α'0.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHc Hwf α0 P0 τ Θw Δw Hnv HeqS eq_refl Hmτ HwfP0 Hocc)
      as [Hle Hdisj].
    assert (Heqd : ⇓ᵗ[Θ] (ptyp_var_f α) = ⇓ᵗ[Θ] τ)
      by (apply a_tyequiv_downarrow;
          [ exact Hwf | apply a_tyequiv__flex_def; exact H ]).
    rewrite Heqd. split; [ exact Hle | exact Hdisj ].
Qed.

(** The wrapper: full occurs-size fact, var case included. *)
Lemma occurs_join_size : forall Ψ Θ κm α P A Θw Δw,
  Ψ ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κm P)) ∼ (ptyp_to_bskl_syn A) ->
  a_wf_aenv Θ ->
  (forall α0, mono_ptyp (msubst_lookup κm α0)) ->
  mono_ptyp A ->
  Θw ⨟ Δw ⊢ₚₛᵃ P ->
  α `in` ftvar_in_pskl P ->
  size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α)) <= size_ptyp (⇓ᵗ[Θ] A) /\
  (P = pskl_var_f α \/ P = pskl_tophole (pskl_var_f α) \/
   size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α)) < size_ptyp (⇓ᵗ[Θ] A)).
Proof.
  intros Ψ Θ κm α P A Θw Δw Hc Hwf Hmlk HmC HwfP Hocc.
  destruct (pskl_var_dec P) as [[α0 HeqP] | Hnv].
  - (* P = var α0 *)
    subst P. simpl in Hocc.
    assert (HeqX : α0 = α) by (clear - Hocc; fsetdec). subst α0.
    simpl in Hc.
    rewrite (a_tyequiv_downarrow Hwf
               (join_var_tyequiv Hc Hwf (Hmlk α) HmC)).
    split; [ lia | left; reflexivity ].
  - destruct (occurs_join_size_aux Hc Hwf κm Hmlk Hnv eq_refl eq_refl
                HmC HwfP Hocc) as [Hle Hdisj].
    split; [ exact Hle | destruct Hdisj; auto ].
Qed.

(* ===================================================================== *)
(*  §2i  Assign-SolveM: GUESS — existence + the ζ-images from the join                   *)
(* ===================================================================== *)

(** The trivial tuple at a variable: guess keeps the variable, no fresh
    names, and the equation is the base bridge. *)
Lemma guess_witness_var_tuple : forall Θ κm α A L,
  Θ ⊢ (msubst_lookup κm α) ≡ᵗ A ->
  exists βs τg ζβ,
    (forall Θg,
       (forall α0, α0 `in` dom βs -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg (pskl_var_f α) βs τg) /\
    mono_ptyp τg /\
    uniq βs /\
    (forall α10, α10 `in` dom βs -> α10 `notin` L) /\
    dom ζβ [=] dom βs /\
    (forall E κE, κE ∷ E ⊑ Θ -> ζβ ++ κE ∷ (βs ++ E) ⊑ Θ) /\
    Θ ⊢ (msubst_ptyp (ζβ ++ κm) τg) ≡ᵗ A.
Proof.
  intros Θ κm α A L Heqv.
  exists nil, (ptyp_var_f α), (@nil (atom * ptyp)).
  split; [ intros Θg _; apply a_guess_mono__var | ].
  split; [ apply mono_ptyp__var | ].
  split; [ constructor | ].
  split; [ intros α10 Hγ0; simpl in Hγ0; exfalso; clear - Hγ0; fsetdec | ].
  split; [ simpl; reflexivity | ].
  split; [ intros E κE HE; simpl; exact HE | ].
  simpl. exact Heqv.
Qed.

Lemma guess_join_witness_aux : forall Ψ Θ R' Q,
  Ψ ⨟ Θ ⊢ₛᵃ R' ∼ Q ->
  a_wf_aenv Θ ->
  forall κm,
  (forall α, mono_ptyp (msubst_lookup κm α)) ->
  forall P A,
    (forall α, P <> pskl_var_f α) ->
    R' = pskl_to_uskl (msubst_pskl κm P) ->
    Q = ptyp_to_bskl_syn A ->
    mono_ptyp A ->
    a_wf_ptyp Θ A ->
    forall L, exists βs τg ζβ,
      (forall Θg,
       (forall α0, α0 `in` dom βs -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg P βs τg) /\
      mono_ptyp τg /\
      uniq βs /\
      (forall α10, α10 `in` dom βs -> α10 `notin` L) /\
      dom ζβ [=] dom βs /\
      (forall E κE, κE ∷ E ⊑ Θ -> ζβ ++ κE ∷ (βs ++ E) ⊑ Θ) /\
      Θ ⊢ (msubst_ptyp (ζβ ++ κm) τg) ≡ᵗ A.
Proof.
  intros Ψ Θ R' Q Hc Hwf κm Hmlk.
  induction Hc; intros P0 C0 Hnv HeqS HeqQ HmC0 HwfC0 Lav.
  - (* unit *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    destruct C0; simpl in HeqQ; try discriminate.
    exists nil, ptyp_unit, (@nil (atom * ptyp)).
    split; [ intros Θg _; apply a_guess_mono__unit | ].
    split; [ apply mono_ptyp__unit | ].
    split; [ constructor | ].
    split; [ intros α10 Hγ0; simpl in Hγ0; exfalso; clear - Hγ0; fsetdec | ].
    split; [ simpl; reflexivity | ].
    split; [ intros E κE HE; simpl; exact HE | ].
    simpl. apply a_tyequiv__refl. apply lc_ptyp_unit.
  - (* var : P must be a var — excluded *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* arrow *)
    destruct P0 as [ | | α | P1 P2 | | | ]; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    inversion HeqS; subst R1 R2.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst Q1 Q2.
    inversion HmC0; subst.
    match goal with H : mono_ptyp C1 |- _ => rename H into HmC1 end.
    match goal with H : mono_ptyp C2 |- _ => rename H into HmC2 end.
    inversion HwfC0; subst.
    match goal with H : a_wf_ptyp Θ C1 |- _ => rename H into HwfC1 end.
    match goal with H : a_wf_ptyp Θ C2 |- _ => rename H into HwfC2 end.
    (* component 1, avoiding Lav ∪ ftv (P1→P2) *)
    set (L1 := Lav `union` ftvar_in_pskl (pskl_arrow P1 P2)).
    assert (Hcomp1 : exists βs1 τ1 ζ1,
        (forall Θg,
       (forall α0, α0 `in` dom βs1 -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg P1 βs1 τ1) /\
        mono_ptyp τ1 /\ uniq βs1 /\
        (forall α10, α10 `in` dom βs1 -> α10 `notin` L1) /\
        dom ζ1 [=] dom βs1 /\
        (forall E κE, κE ∷ E ⊑ Θ -> ζ1 ++ κE ∷ (βs1 ++ E) ⊑ Θ) /\
        Θ ⊢ (msubst_ptyp (ζ1 ++ κm) τ1) ≡ᵗ C1).
    { destruct (pskl_var_dec P1) as [[α1 HeqP1] | Hnv1].
      - subst P1. simpl in Hc1.
        apply guess_witness_var_tuple.
        apply (join_var_tyequiv Hc1 Hwf (Hmlk α1) HmC1).
      - apply (IHHc1 Hwf P1 C1 Hnv1 eq_refl eq_refl HmC1 HwfC1 L1). }
    destruct Hcomp1 as [βs1 [τ1 [ζ1 [Hg1 [Hm1 [Hu1 [Hf1 [Hd1 [Ht1 He1]]]]]]]]].
    set (L2 := L1 `union` dom βs1).
    assert (Hcomp2 : exists βs2 τ2 ζ2,
        (forall Θg,
       (forall α0, α0 `in` dom βs2 -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg P2 βs2 τ2) /\
        mono_ptyp τ2 /\ uniq βs2 /\
        (forall α10, α10 `in` dom βs2 -> α10 `notin` L2) /\
        dom ζ2 [=] dom βs2 /\
        (forall E κE, κE ∷ E ⊑ Θ -> ζ2 ++ κE ∷ (βs2 ++ E) ⊑ Θ) /\
        Θ ⊢ (msubst_ptyp (ζ2 ++ κm) τ2) ≡ᵗ C2).
    { destruct (pskl_var_dec P2) as [[α2 HeqP2] | Hnv2].
      - subst P2. simpl in Hc2.
        apply guess_witness_var_tuple.
        apply (join_var_tyequiv Hc2 Hwf (Hmlk α2) HmC2).
      - apply (IHHc2 Hwf P2 C2 Hnv2 eq_refl eq_refl HmC2 HwfC2 L2). }
    destruct Hcomp2 as [βs2 [τ2 [ζ2 [Hg2 [Hm2 [Hu2 [Hf2 [Hd2 [Ht2 He2]]]]]]]]].
    exists (βs1 ++ βs2), (ptyp_arrow τ1 τ2), (ζ1 ++ ζ2).
    assert (Hdisj12 : forall α10, α10 `in` dom βs2 -> α10 `notin` dom βs1).
    { intros α10 Hγ0. specialize (Hf2 α10 Hγ0).
      clear - Hf2. unfold L2 in Hf2. fsetdec. }
    (* the two msubst-agree transports *)
    (* the ftv bound is context-free; read it off at [nil], where the
       generated-name guard is vacuous *)
    pose proof (a_guess_mono_ftv (Hg1 nil ltac:(intros; simpl; fsetdec)))
      as Hftv1.
    pose proof (a_guess_mono_ftv (Hg2 nil ltac:(intros; simpl; fsetdec)))
      as Hftv2.
    assert (Hag1 : msubst_ptyp ((ζ1 ++ ζ2) ++ κm) τ1
                 = msubst_ptyp (ζ1 ++ κm) τ1).
    { apply msubst_ptyp_agree. intros α0 HX0.
      assert (HX0' : α0 `in` ftvar_in_pskl P1 `union` dom βs1)
        by (clear - Hftv1 HX0; fsetdec).
      rewrite app_assoc.
      destruct (AtomSetProperties.In_dec α0 (dom ζ1)) as [Hin | Hni].
      - rewrite (msubst_lookup_app_in ζ1 (ζ2 ++ κm) Hin).
        rewrite (msubst_lookup_app_in ζ1 κm Hin). reflexivity.
      - rewrite (msubst_lookup_app_notin _ _ Hni).
        rewrite (msubst_lookup_app_notin _ _ Hni).
        assert (HX0P1 : α0 `in` ftvar_in_pskl P1)
          by (rewrite Hd1 in Hni; clear - HX0' Hni; fsetdec).
        assert (Hniζ2 : α0 `notin` dom ζ2).
        { rewrite Hd2. intros Hin2.
          specialize (Hf2 α0 Hin2). clear - Hf2 HX0P1.
          unfold L2, L1 in Hf2. simpl in Hf2. fsetdec. }
        rewrite (msubst_lookup_app_notin _ _ Hniζ2). reflexivity. }
    assert (Hag2 : msubst_ptyp ((ζ1 ++ ζ2) ++ κm) τ2
                 = msubst_ptyp (ζ2 ++ κm) τ2).
    { apply msubst_ptyp_agree. intros α0 HX0.
      assert (HX0' : α0 `in` ftvar_in_pskl P2 `union` dom βs2)
        by (clear - Hftv2 HX0; fsetdec).
      rewrite app_assoc.
      assert (Hniζ1 : α0 `notin` dom ζ1).
      { rewrite Hd1.
        destruct (AtomSetProperties.In_dec α0 (dom βs2)) as [Hin2 | Hni2].
        - exact (Hdisj12 α0 Hin2).
        - assert (HX0P2 : α0 `in` ftvar_in_pskl P2)
            by (clear - HX0' Hni2; fsetdec).
          intros Hin1. specialize (Hf1 α0 Hin1).
          clear - Hf1 HX0P2. unfold L1 in Hf1. simpl in Hf1. fsetdec. }
      rewrite (msubst_lookup_app_notin _ _ Hniζ1). reflexivity. }
    split; [ intros Θg Hfrg; apply a_guess_mono__arrow;
             [ apply Hg1 | apply Hg2 ];
             intros α0 Hα0; apply Hfrg; rewrite dom_app;
             clear - Hα0; fsetdec | ].
    split; [ apply mono_ptyp__arrow; assumption | ].
    split.
    { apply uniq_app_4; auto.
      unfold disjoint. intros x Hx.
      assert (Hx1 : x `in` dom βs1) by (clear - Hx; fsetdec).
      assert (Hx2 : x `in` dom βs2) by (clear - Hx; fsetdec).
      exfalso. exact (Hdisj12 x Hx2 Hx1). }
    split.
    { intros α10 Hγ0. rewrite dom_app in Hγ0.
      apply union_1 in Hγ0. destruct Hγ0 as [Hγ0 | Hγ0].
      - specialize (Hf1 α10 Hγ0). clear - Hf1. unfold L1 in Hf1. fsetdec.
      - specialize (Hf2 α10 Hγ0). clear - Hf2. unfold L2, L1 in Hf2. fsetdec. }
    split.
    { repeat rewrite dom_app. rewrite Hd1. rewrite Hd2. reflexivity. }
    split.
    { intros E κE HE.
      rewrite app_assoc. rewrite app_assoc.
      apply Ht1. apply Ht2. exact HE. }
    simpl. apply a_tyequiv__arrow;
      [ rewrite Hag1; exact He1 | rewrite Hag2; exact He2 ].
  - (* forall_inh_tagged : R' = uskl_all_etag, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_inh_untagged : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* forall_syn_tagged *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_syn : Q = bskl_all_syn, mono A refutes *)
    destruct C0; simpl in HeqQ; try discriminate. inversion HmC0.
  - (* ghostg *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* topholeg *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* hole : the crux — a fresh β̂ whose ζ-image is A *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    destruct (atom_fresh Lav) as [β Hβ].
    exists (β ~ abind_flex_mono), (ptyp_var_f β), ((β, C0) :: nil).
    split; [ intros Θg Hfrg; apply a_guess_mono__hole;
               apply Hfrg; simpl; fsetdec | ].
    split; [ apply mono_ptyp__var | ].
    split; [ solve_uniq | ].
    split.
    { intros α10 Hγ0. simpl in Hγ0.
      assert (Heqγ : α10 = β) by (clear - Hγ0; fsetdec).
      subst α10. exact Hβ. }
    split; [ simpl; fsetdec | ].
    split.
    { intros E κE HE. simpl.
      apply a_inc__flex; [ exact HE | exact HwfC0 | exact HmC0 ]. }
    simpl. destruct (β == β) as [_ | Hne]; [ | exfalso; auto ].
    apply a_tyequiv__refl. apply mono_ptyp_lc. exact HmC0.
  - (* tophole : Q = bskl_tophole, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* tophole_inh : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* tophole_drop : P = ∀◇P', recurse on the body *)
    destruct P0 as [ | | | | | | P' ]; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    inversion HeqS; subst R.
    assert (Hbody : exists βs τg ζβ,
        (forall Θg,
       (forall α0, α0 `in` dom βs -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg P' βs τg) /\
        mono_ptyp τg /\ uniq βs /\
        (forall α10, α10 `in` dom βs -> α10 `notin` Lav) /\
        dom ζβ [=] dom βs /\
        (forall E κE, κE ∷ E ⊑ Θ -> ζβ ++ κE ∷ (βs ++ E) ⊑ Θ) /\
        Θ ⊢ (msubst_ptyp (ζβ ++ κm) τg) ≡ᵗ C0).
    { destruct (pskl_var_dec P') as [[α' HeqP'] | Hnv'].
      - subst P'. simpl in Hc. rewrite HeqQ in Hc.
        apply guess_witness_var_tuple.
        apply (join_var_tyequiv Hc Hwf (Hmlk α') HmC0).
      - apply (IHHc Hwf P' C0 Hnv' eq_refl HeqQ HmC0 HwfC0 Lav). }
    destruct Hbody as [βs [τg [ζβ [Hg [Hm [Hu [Hf [Hd [Ht He]]]]]]]]].
    exists βs, τg, ζβ.
    split; [ intros Θg Hfrg; apply a_guess_mono__tophole;
               apply Hg; exact Hfrg | ].
    split; [ exact Hm | ].
    split; [ exact Hu | ].
    split; [ exact Hf | ].
    split; [ exact Hd | ].
    split; [ exact Ht | ].
    exact He.
  - (* flex_l : P must be a var — excluded *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* flex_r : unfold the RHS definition *)
    destruct C0 as [ | | α0 | | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst α0.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hwτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf_local; eauto).
    destruct (IHHc Hwf P0 τ Hnv HeqS eq_refl Hmτ Hwτ Lav)
      as [βs [τg [ζβ [Hg [Hm [Hu [Hf [Hd [Ht He]]]]]]]]].
    exists βs, τg, ζβ.
    split; [ exact Hg | ].
    split; [ exact Hm | ].
    split; [ exact Hu | ].
    split; [ exact Hf | ].
    split; [ exact Hd | ].
    split; [ exact Ht | ].
    eapply a_tyequiv__trans; [ exact He | ].
    apply a_tyequiv__sym. apply a_tyequiv__flex_def. exact H.
Qed.

(** The wrapper: var case included. *)
Lemma guess_join_witness : forall Ψ Θ κm P A,
  Ψ ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κm P)) ∼ (ptyp_to_bskl_syn A) ->
  a_wf_aenv Θ ->
  (forall α, mono_ptyp (msubst_lookup κm α)) ->
  mono_ptyp A ->
  a_wf_ptyp Θ A ->
  forall L, exists βs τg ζβ,
    (forall Θg,
       (forall α0, α0 `in` dom βs -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg P βs τg) /\
    mono_ptyp τg /\
    uniq βs /\
    (forall α10, α10 `in` dom βs -> α10 `notin` L) /\
    dom ζβ [=] dom βs /\
    (forall E κE, κE ∷ E ⊑ Θ -> ζβ ++ κE ∷ (βs ++ E) ⊑ Θ) /\
    Θ ⊢ (msubst_ptyp (ζβ ++ κm) τg) ≡ᵗ A.
Proof.
  intros Ψ Θ κm P A Hc Hwf Hmlk HmC HwfC L.
  destruct (pskl_var_dec P) as [[α HeqP] | Hnv].
  - subst P. simpl in Hc.
    apply guess_witness_var_tuple.
    apply (join_var_tyequiv Hc Hwf (Hmlk α) HmC).
  - eapply (guess_join_witness_aux Hc Hwf κm Hmlk Hnv eq_refl eq_refl
              HmC HwfC).
Qed.

(* ===================================================================== *)
(*  §2j  The Assign-SolveM completeness case, assembled                   *)
(* ===================================================================== *)

Lemma assign_solve_m_complete : forall (N : atoms) Θ0' Ξ α P κ Θ,
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ->
  (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ⨟ empty ⊢ₚₛᵃ P ->
  a_non_flex (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') P ->
  P <> pskl_tophole (pskl_var_f α) ->
  κ ∷ (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ⊑ Θ ->
  a_wf_aenv Θ ->
  empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P))
             ∼ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α))) ->
  exists Θ1,
    ((α ~ abind_flex_mono) ++ Θ0') ⊲[ Ξ ] α ≔ P ⊣ Θ1 /\
    (forall γ, γ `in` dom Θ1 ->
       γ `in` dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') \/ γ `notin` N) /\
    (forall κ1, is_id_msubst κ1 ->
       κ1 ∷ (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ⊑ Θ1 ->
       exists ζ, ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') κ
                     (msubst_compose ζ κ1) Θ).
Proof.
  intros N Θ0' Ξ α P κ Θ Hdecl Hwf HwfP Hnf HneP Hinc Hwfth Hjoin.
  set (τα := msubst_lookup κ α) in *.
  assert (Huq : uniq (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Hbα : binds α abind_flex_mono (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
    by (apply binds_app_3; left; reflexivity).
  assert (Hbtα : a_binds_tvar α (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
    by (right; left; exact Hbα).
  assert (Hmτα : mono_ptyp τα) by (eapply a_inc_lookup_mono; exact Hinc).
  assert (Hwτα : a_wf_ptyp Θ τα)
    by (eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact Hbtα ]).
  assert (Hmlk : forall α0, mono_ptyp (msubst_lookup κ α0))
    by (intros α0; eapply a_inc_lookup_mono; exact Hinc).
  (* ---- occurs check ---- *)
  assert (Hocc : α `notin` ftvar_in_pskl P).
  { destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P))
      as [Hin | Hni]; [ exfalso | exact Hni ].
    destruct (occurs_join_size κ Hjoin Hwfth Hmlk Hmτα HwfP Hin)
      as [Hle Hdisj].
    destruct Hdisj as [HeqP | [HeqP | Hlt]].
    - subst P. destruct Hnf as [_ Hnfl].
      apply Hnfl. apply a_flex__var. exact Hbα.
    - exact (HneP HeqP).
    - exact (Nat.lt_irrefl _ Hlt). }
  (* ---- the guess witness ---- *)
  (* [ftvar_in_aenv], not [dom]: since the freshness campaign the guessed
     names must dodge everything the context MENTIONS (payloads included),
     which is what [a_guess_mono__hole] now polices. *)
  set (L := N `union` add α (ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
              `union` ftvar_in_pskl P `union` dom Θ).
  destruct (guess_join_witness κ P Hjoin Hwfth Hmlk Hmτα Hwτα L)
    as [βs [τg [ζβ [Hg [Hmτg [Huβ [Hfβ [Hdζ [Htr Heqn]]]]]]]]].
  (* ---- the algorithmic step ---- *)
  exists ((α ~ abind_flex_mono_def τg) ++ βs ++ Ξ ++ Θ0').
  split.
  { apply a_assign__solve_m.
    - exact Hocc.
    - apply Hg.
      intros α10 Hγ0. specialize (Hfβ α10 Hγ0).
      clear - Hfβ. unfold L in Hfβ.
      rewrite ftvar_in_aenv_app in Hfβ. rewrite ftvar_in_aenv_app in Hfβ.
      fsetdec.
    - exact Hmτg.
    - exact Huβ.
    - intros α10 Hγ0. specialize (Hfβ α10 Hγ0).
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
        as Hds.
      clear - Hfβ Hds. unfold L in Hfβ. simpl_env in *. fsetdec. }
  (* ---- the avoid set: everything the node deposits is a GUESSED name,
         and the guess dodged [L], which contains [N] ---- *)
  split.
  { intros γ Hγ. simpl_env in Hγ.
    destruct (AtomSetProperties.In_dec γ (dom βs)) as [Hin | Hni].
    - right. specialize (Hfβ γ Hin). clear - Hfβ. unfold L in Hfβ. fsetdec.
    - left. simpl_env. clear - Hγ Hni. fsetdec. }
  (* ---- optimality ---- *)
  intros κ1 Hid Hinc1.
  (* strip the competing solution at the α entry *)
  destruct (@a_inc_mid_strip_flex Ξ α Θ0' κ Θ Hdecl Hinc)
    as [κa [τα' [κ0 [Heqκ [Hdκa [Hinc0 Hincs]]]]]].
  assert (Hακa : α `notin` dom κa).
  { rewrite Hdκa. clear - Huq. simpl_env in Huq. solve_uniq. }
  assert (Heqτα : τα = τα').
  { unfold τα. rewrite Heqκ.
    rewrite (msubst_lookup_app_notin _ _ Hακa). simpl.
    destruct (α == α) as [_ | Hne]; [ reflexivity | exfalso; auto ]. }
  subst τα'.
  (* the factoring ζ *)
  exists ((α, τα) :: ζβ ++ κa ++ κ0).
  assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
    by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact Hwf ]).
  assert (Hαftvτg : α `notin` ftvar_in_ptyp τg).
  { pose proof (a_guess_mono_ftv (Hg nil ltac:(intros; simpl; fsetdec)))
      as Hftv.
    intros Hinτ. apply Hftv in Hinτ.
    apply union_1 in Hinτ. destruct Hinτ as [HinP | Hinβ].
    - clear - HinP Hocc. fsetdec.
    - specialize (Hfβ α Hinβ). clear - Hfβ. unfold L in Hfβ. fsetdec. }
  (* the deposited definition is ζ-consistent *)
  assert (Heqdef : Θ ⊢ τα ≡ᵗ (msubst_ptyp (ζβ ++ κa ++ κ0) τg)).
  { apply a_tyequiv__sym.
    assert (Hagd : msubst_ptyp (ζβ ++ κa ++ κ0) τg
                 = msubst_ptyp (ζβ ++ κ) τg).
    { apply msubst_ptyp_agree. intros α00 HX0.
      rewrite Heqκ.
      rewrite <- app_assoc. rewrite <- (app_assoc _ ζβ κa ((α, τα) :: κ0)).
      assert (HneX : α00 <> α)
        by (intros ->; exact (Hαftvτg HX0)).
      rewrite (msubst_lookup_mid_drop _ _ _ HneX). reflexivity. }
    rewrite Hagd. exact Heqn. }
  split.
  { (* ζ ∷ Θ1 ⊑ Θ *)
    simpl_env.
    apply a_inc__flex_def.
    - simpl_env. apply Htr. exact Hincs.
    - exact Hwτα.
    - exact Hmτα.
    - simpl_env. exact Heqdef. }
  (* ---- the metasubstitution equivalence ---- *)
  destruct (@a_inc_mid_strip_flex Ξ α Θ0' κ1
              ((α ~ abind_flex_mono_def τg) ++ βs ++ Ξ ++ Θ0') Hdecl Hinc1)
    as [κ1a [τid [κ1b [Heqκ1 [Hdκ1a [Hinc10 Hinc1s]]]]]].
  assert (Hidm : τid = ptyp_var_f α /\ is_id_msubst (κ1a ++ κ1b))
    by (rewrite Heqκ1 in Hid; apply is_id_msubst_mid; exact Hid).
  destruct Hidm as [Heqτid Hid'].
  subst τid.
  rewrite Heqκ1. rewrite Heqκ.
  rewrite msubst_compose_app.
  replace (msubst_compose ((α, τα) :: ζβ ++ κa ++ κ0)
             ((α, ptyp_var_f α) :: κ1b))
    with ((α, τα) :: msubst_compose ((α, τα) :: ζβ ++ κa ++ κ0) κ1b)
    by (unfold msubst_compose; simpl;
        destruct (α == α); [ reflexivity | exfalso; auto ]).
  apply a_inc_equiv_mid_insert_flex.
  - exact Hdecl.
  - clear - Huq. simpl_env in *. solve_uniq.
  - exact Hdκa.
  - rewrite dom_msubst_compose. exact Hdκ1a.
  - apply a_tyequiv__refl. apply mono_ptyp_lc. exact Hmτα.
  - (* collapse ζ ∘ (κ1a ++ κ1b) to κa ++ κ0, then reflexivity *)
    rewrite <- msubst_compose_app.
    change ((α, τα) :: ζβ ++ κa ++ κ0)
      with (((α, τα) :: ζβ) ++ κa ++ κ0).
    rewrite (msubst_compose_is_id_r_ext ((α, τα) :: ζβ) Hwf' Hid' Hinc1s Hincs).
    + apply a_inc_equiv_refl. exact Hincs.
    + intros α00 HX0. simpl in HX0.
      destruct (AtomSetProperties.In_dec α00 (dom ζβ)) as [Hinζ | Hniζ].
      * rewrite Hdζ in Hinζ. specialize (Hfβ α00 Hinζ).
        pose proof (dom_subset_ftvar_in_aenv
                      (Ξ ++ (α ~ abind_flex_mono) ++ Θ0')) as Hds.
        clear - Hfβ Hds. unfold L in Hfβ. simpl_env in *. fsetdec.
      * assert (HeqX : α00 = α) by (clear - HX0 Hniζ; fsetdec).
        subst α00. clear - Huq. simpl_env in Huq. solve_uniq.
Qed.

Lemma assign_complete_step : forall m,
  (forall m', mu_lt m' m -> complete_at m') ->
  assign_complete_at m.
Proof.
  intros m IH. unfold assign_complete_at.
  intros N Θ0 Ξ α P κ Θ Hm Hdecl Hwf Hfα HwfP Hnf Hdomξ Hinc Hwfth Hjoin.
  subst m.
  destruct Θ0 as [ | [α1 b] Θ0' ].
  { exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb. }
  destruct b as [ | A | Q | | τdef ].
  - (* head [α1 ~ tvar] RIGID. *)
    destruct (AtomSetProperties.In_dec α1 (ftvar_in_pskl P)) as [Hγin | Hγni].
    + (* α1 ∈ ftv(P) : NO RULE fires — the STUCK-CHECK (design doc §9.2,
         [paper-gap]: the paper never proves the walk cannot reach this
         head) refutes the solution.  [a_inc] peels α1 before reaching α̂
         ([a_inc_tvar_inv]), so κα̂ is wf BELOW α1; α1 survives the solution
         into κP ([rigid_survives_solution]) while the join confines the
         subject's rigid ftv to κα̂'s scope
         ([ad_pat_consis_rigid_ftv_rev_scoped]) — contradiction. *)
      exfalso.
      (* decompose the competing increment at the rigid head *)
      destruct (@a_inc_strip_decls_prefix Ξ ((α1, abind_tvar) :: Θ0') κ Θ
                  Hdecl Hinc)
        as [κa [κb [Heqκ [Hdκa Hincb]]]].
      destruct (a_inc_tvar_inv Hincb)
        as [Ξv [Θt [HeqΘ [HsufΞv Hincb']]]].
      assert (Huq : uniq (Ξ ++ (α1, abind_tvar) :: Θ0'))
        by (apply a_wf_aenv_uniq; exact Hwf).
      assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
      assert (Hbγ : binds α1 abind_tvar (Ξ ++ (α1, abind_tvar) :: Θ0')).
      { apply binds_app_3. left. reflexivity. }
      assert (HbγΘ : binds α1 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; [ exact Hinc | exact Hbγ ]).
      assert (Hα1Θt : α1 `notin` dom Θt).
      { rewrite HeqΘ in HuqΘ. clear - HuqΘ.
        simpl_env in HuqΘ. solve_uniq. }
      (* κα̂ is well-formed in the truncated target Θt, below α1 *)
      assert (Hfα0 : a_flex_tvar Θ0' α).
      { destruct Hfα as [Hb | [τ0 Hb]].
        - apply binds_cons_1 in Hb as [[_ Heq2] | Hb];
            [ discriminate Heq2 | left; exact Hb ].
        - apply binds_cons_1 in Hb as [[_ Heq2] | Hb];
            [ discriminate Heq2 | right; exists τ0; exact Hb ]. }
      assert (Hbtα0 : a_binds_tvar α Θ0')
        by (destruct Hfα0 as [Hb | [τ0 Hb]];
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]).
      assert (HαΘ0' : α `in` dom Θ0')
        by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
      assert (Hακa : α `notin` dom κa).
      { rewrite Hdκa. clear - Huq HαΘ0'.
        simpl_env in Huq. solve_uniq. }
      assert (Hwf2 : a_wf_aenv ((Ξ ++ (α1 ~ abind_tvar)) ++ Θ0'))
        by (simpl_env; exact Hwf).
      assert (Hwf0' : a_wf_aenv Θ0')
        by (eapply a_wf_aenv_app_r; exact Hwf2).
      assert (Hwfα : a_wf_ptyp Θt (msubst_lookup κ α)).
      { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb Hακa).
        eapply a_inc_lookup_wf;
          [ exact Hincb' | exact Hwf0' | exact Hbtα0 ]. }
      assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θt)
        by (apply a_wf_ptyp_ftv_dom; exact Hwfα).
      (* definitions visible in dom Θt are Θt's own, scoped to Θt *)
      assert (HwfΘt : a_wf_aenv Θt).
      { rewrite HeqΘ in Hwfth.
        assert (Hwtmp : a_wf_aenv ((Ξv ++ (α1 ~ abind_tvar)) ++ Θt))
          by (simpl_env; simpl_env in Hwfth; exact Hwfth).
        eapply a_wf_aenv_app_r; exact Hwtmp. }
      assert (Hdefs : forall β1 τ, binds β1 (abind_flex_mono_def τ) Θ ->
                β1 `in` dom Θt -> ftvar_in_ptyp τ [<=] dom Θt).
      { intros β1 τ Hb HδD.
        assert (Hbt : binds β1 (abind_flex_mono_def τ) Θt).
        { rewrite HeqΘ in Hb.
          assert (Hb2 : binds β1 (abind_flex_mono_def τ)
                    ((Ξv ++ (α1 ~ abind_tvar)) ++ Θt))
            by (simpl_env; simpl_env in Hb; exact Hb).
          apply binds_app_iff in Hb2.
          destruct Hb2 as [Hb2 | Hb2]; [ exfalso | exact Hb2 ].
          apply binds_In in Hb2.
          rewrite HeqΘ in HuqΘ.
          assert (Hu2 : uniq ((Ξv ++ (α1 ~ abind_tvar)) ++ Θt))
            by (simpl_env; simpl_env in HuqΘ; exact HuqΘ).
          apply uniq_app_iff in Hu2. destruct Hu2 as [_ [_ Hdisj]].
          clear - Hdisj Hb2 HδD. unfold disjoint in Hdisj. fsetdec. }
        apply a_wf_ptyp_ftv_dom.
        eapply a_wf_aenv_binds_def_wf_local; [ exact HwfΘt | exact Hbt ]. }
      (* α1 survives the solution into κP … *)
      assert (Hα1κP : α1 `in` ftvar_in_pskl (msubst_pskl κ P))
        by (eapply rigid_survives_solution;
            [ exact Hinc | exact Hwf | exact Hbγ | exact Hγin ]).
      (* … but the join confines the subject's rigid ftv to dom Θt *)
      assert (HγnS : α1 `notin`
                ftvar_in_uskl (pskl_to_uskl (msubst_pskl κ P))).
      { eapply ad_pat_consis_rigid_ftv_rev_scoped with (D := dom Θt);
          [ exact Hwfth | exact HbγΘ | exact Hα1Θt | exact Hdefs
          | exact Hjoin | ].
        pose proof (ftvar_in_bskl_syn
                      (ptyp_to_pskl (msubst_lookup κ α))) as Hf1.
        pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup κ α)) as Hf2.
        clear - Hf1 Hf2 Hftvα. fsetdec. }
      pose proof (ftvar_in_uskl_pskl (msubst_pskl κ P)) as Hf3.
      clear - HγnS Hα1κP Hf3. fsetdec.
    + (* Assign-SkipRigid proper (α1 ∉ ftv P): the same ⇓-truncation as
           SkipTmVar, with the rigid middle re-attached verbatim (no
           semantic-middle obligation). *)
      assert (Huqf : uniq (Ξ ++ (α1 ~ abind_tvar) ++ Θ0'))
        by (apply a_wf_aenv_uniq; exact Hwf).
      assert (HwfM : a_wf_aenv (Ξ ++ (α1 ~ abind_tvar) ++ Θ0'))
        by (exact Hwf).
      assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
        by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
      assert (Huq' : uniq (Ξ ++ Θ0')) by (apply a_wf_aenv_uniq; exact Hwf').
      assert (Hwf0 : a_wf_aenv Θ0') by (eapply a_wf_aenv_app_r; exact Hwf').
      assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
      pose proof Hγni as Hγfr.
      assert (HwfP' : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
        by (eapply a_wf_pskl_strip_mid; [ exact HwfP | exact Hγfr ]).
      assert (Hfα0 : a_flex_tvar Θ0' α).
      { destruct Hfα as [Hb | [τ0 Hb]];
          [ destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
            [ discriminate | left; exact Hb' ]
          | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
            [ discriminate | right; exists τ0; exact Hb' ] ]. }
      assert (Hbw : forall (β1 : atom) (bb : abind),
                binds β1 bb (Ξ ++ Θ0') ->
                binds β1 bb (Ξ ++ (α1 ~ abind_tvar) ++ Θ0')).
      { intros β1 bb Hb. unfold binds in *.
        apply in_app_or in Hb. apply in_or_app.
        destruct Hb as [Hb | Hb];
          [ left; exact Hb | right; simpl; right; exact Hb ]. }
      assert (Hnf' : a_non_flex (Ξ ++ Θ0') P).
      { destruct Hnf as [Hlc Hnfl]. split; [ exact Hlc | ].
        intro Hfl. apply Hnfl.
        inversion Hfl as [Θf β1 Hb | Θf β1 τ0 Hb]; subst;
          [ apply a_flex__var; apply Hbw; exact Hb
          | eapply a_flex__var_def; apply Hbw; exact Hb ]. }
      (* competing: strip Ξ, invert the α1-var middle *)
      destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_tvar) ++ Θ0')
                  κ Θ Hdecl Hinc) as [κa [κb' [Heqκ [Hdκa Hincxb]]]].
      destruct (a_inc_tvar_inv Hincxb)
        as [Ξv [Θ' [HeqΘ [HsufΞv Hincb]]]].
      assert (HwfΘ' : a_wf_aenv Θ').
      { rewrite HeqΘ in Hwfth.
        eapply a_wf_aenv_app_r with (Θp := Ξv ++ (α1 ~ abind_tvar)).
        simpl_env. simpl_env in Hwfth. exact Hwfth. }
      assert (HeqW : (Ξv ++ (α1 ~ abind_tvar)) ++ Θ' = Θ)
        by (rewrite HeqΘ; simpl_env; reflexivity).
      assert (Hincb_n : msubst_compose (aenv_msubst Θ) κb' ∷ Θ0' ⊑ Θ').
      { pose proof (a_inc_self_downarrow Hincb
                      (Ξv ++ (α1 ~ abind_tvar))) as Hs.
        rewrite HeqW in Hs. apply Hs; [ exact Hwfth | exact HuqΘ | exact Hwf0 ]. }
      assert (Hside : forall β, β `in` ftvar_in_pskl P ->
                β `in` dom κ \/ β `notin` dom (aenv_msubst Θ)).
      { intros β Hβ.
        destruct (AtomSetProperties.In_dec β (dom κ)) as [Hin | Hni];
          [ left; exact Hin | right ].
        intro Hin2. apply aenv_msubst_dom_inv in Hin2.
        destruct (a_wf_pskl_ftv_tvarish HwfP Hβ) as [Hemp | Hbt];
          [ clear - Hemp; fsetdec | ].
        destruct Hbt as [Htv | [Hfm | [τ0 Hfd]]].
        - assert (HtvΘ : binds β abind_tvar Θ)
            by (eapply a_inc_binds_tvar; [ exact Hinc | exact Htv ]).
          destruct Hin2 as [Hb | [τ1 Hb]];
            (pose proof (binds_unique _ _ _ _ _ HtvΘ Hb
                           (a_wf_aenv_uniq Hwfth)) as Heqb;
             discriminate Heqb).
        - assert (Hyd : β `in` dom κ)
            by (eapply a_inc_flex_dom;
                [ exact Hinc | exact Hwf | left; exact Hfm ]).
          contradiction.
        - assert (Hyd : β `in` dom κ)
            by (eapply a_inc_flex_dom;
                [ exact Hinc | exact Hwf | right; exists τ0; exact Hfd ]).
          contradiction. }
      assert (Hmona : mono_ptyp (msubst_lookup κ α))
        by (eapply a_inc_lookup_mono; exact Hinc).
      assert (HO2 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P)) [<=] dom Θ').
      { eapply join_pskl_downarrow_mono_scoped;
          [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
          | exact Hmona | | ].
        - intros β τ Hbβ Hβd.
          assert (Hβpre : β `notin` dom (Ξv ++ (α1 ~ abind_tvar))).
          { pose proof HuqΘ as Hu2. rewrite HeqΘ in Hu2.
            rewrite <- app_assoc in Hu2.
            apply uniq_app_iff in Hu2. destruct Hu2 as [_ [_ Hdisj]].
            clear - Hdisj Hβd. unfold disjoint in Hdisj. fsetdec. }
          assert (Hbβ' : binds β (abind_flex_mono_def τ) Θ').
          { rewrite HeqΘ in Hbβ. rewrite <- app_assoc in Hbβ.
            apply binds_app_iff in Hbβ. destruct Hbβ as [Hb | Hb];
              [ | exact Hb ].
            exfalso. apply binds_In in Hb. clear - Hb Hβpre. fsetdec. }
          apply a_wf_ptyp_ftv_dom.
          eapply a_wf_aenv_binds_def_wf_local; [ exact HwfΘ' | exact Hbβ' ].
        - assert (HαΘ0 : α `in` dom Θ0')
            by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb;
                exact Hb).
          assert (Hακa : α `notin` dom κa).
          { rewrite Hdκa. clear - Huqf HαΘ0. simpl_env in Huqf. solve_uniq. }
          assert (Hwfα : a_wf_ptyp Θ' (msubst_lookup κ α)).
          { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb' Hακa).
            eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ].
            destruct Hfα0 as [Hb | [τ0 Hb]];
              [ right; left; exact Hb | right; right; exists τ0; exact Hb ]. }
          apply a_wf_ptyp_ftv_dom. exact Hwfα. }
      assert (Hgr : forall α0, α0 `in` dom κa ->
                 ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup κa α0)) [<=] dom Θ').
      { intros α0 Hα0.
        assert (HXP : α0 `in` ftvar_in_pskl P)
          by (apply Hdomξ; rewrite <- Hdκa; exact Hα0).
        assert (Hα0κ : α0 `in` dom κ)
          by (rewrite Heqκ; rewrite dom_app; clear - Hα0; fsetdec).
        assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup κa α0)
                       = msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α0).
        { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hα0κ)).
          f_equal. rewrite Heqκ. symmetry.
          apply msubst_lookup_app_in; exact Hα0. }
        rewrite Heqlk.
        eapply AtomSetProperties.subset_trans;
          [ apply (msubst_pskl_ftv_lower
                     (msubst_compose (aenv_msubst Θ) κ) P HXP) | ].
        rewrite msubst_pskl_compose; [ exact HO2 | exact Hside ]. }
      assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
      { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
        exact Hb. }
      assert (Hinc_sub0 : (msubst_compose (aenv_msubst Θ) κa)
                              ++ (msubst_compose (aenv_msubst Θ) κb') ∷ (Ξ ++ Θ0') ⊑ Θ').
      { assert (HincR : κa ++ κb' ∷ (Ξ ++ (α1 ~ abind_tvar) ++ Θ0') ⊑ Θ)
          by (rewrite <- Heqκ; exact Hinc).
        eapply a_inc_downarrow_prefix;
          [ exact Hdecl | exact HincR | exact Huqf | exact Hdκa
          | exact Hincb_n | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
      assert (Hinc_sub : msubst_compose (aenv_msubst Θ) κ ∷ (Ξ ++ Θ0') ⊑ Θ').
      { rewrite Heqκ. rewrite msubst_compose_app. exact Hinc_sub0. }
      (* the join over Θ' at ⇓κ *)
      assert (HαΘ0 : α `in` dom Θ0')
        by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
      assert (Hακa : α `notin` dom κa)
        by (rewrite Hdκa; clear - Huqf HαΘ0; simpl_env in Huqf; solve_uniq).
      assert (Hbtα0 : a_binds_tvar α Θ0')
        by (destruct Hfα0 as [Hb | [τ0 Hb]];
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]).
      assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup κ α)).
      { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb' Hακa).
        eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | exact Hbtα0 ]. }
      assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ')
        by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
      assert (Hvisα : forall β, β `in` ftvar_in_ptyp (msubst_lookup κ α) ->
                a_binds_tvar β Θ).
      { intros β Hβ.
        assert (HbtY' : a_binds_tvar β Θ')
          by (eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfα' | exact Hβ ]).
        destruct HbtY' as [Hb | [Hb | [τ0 Hb]]];
          [ left | right; left | right; right; exists τ0 ];
          apply Hsub'; exact Hb. }
      assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup κ α)
                   = ⇓ᵗ[ Θ' ] (msubst_lookup κ α)).
      { rewrite <- HeqW.
        apply downarrow_app_agree_ptyp;
          [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
      assert (Hj1 : ad_pat_consis empty Θ
                (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl κ P)))
                (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))).
      { eapply consis_downarrow_subject;
          [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
          | exact Hmona ]. }
      assert (Heqκα : Θ ⊢ (msubst_lookup κ α)
                        ≡ᵗ (⇓ᵗ[ Θ ] (msubst_lookup κ α))).
      { apply a_tyequiv_to_downarrow_mono;
          [ exact Hwfth
          | eapply a_wf_ptyp_weaken; [ exact Hsub' | exact Hwfα' ]
          | exact Hmona ]. }
      destruct (tyequiv_mono_consis_transport_q Heqκα Hwfth Hmona Hvisα)
        as [_ Hfwd].
      pose proof (Hfwd empty _ Hj1) as Hj2.
      assert (Hjstr : ad_pat_consis empty Θ'
                (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl κ P)))
                (pskl_to_bskl_syn (ptyp_to_pskl
                   (⇓ᵗ[ Θ ] (msubst_lookup κ α))))).
      { eapply ad_pat_consis_strengthen;
          [ exact Hj2 | exact HuqΘ | exact HwfΘ' | exact Hsub' | | ].
        - intros α2 Hα2. rewrite ftvar_in_uskl_pskl in Hα2.
          clear - HO2 Hα2. fsetdec.
        - intros α2 Hα2. rewrite ftvar_in_bskl_syn in Hα2.
          rewrite ftvar_in_ptyp_to_pskl in Hα2.
          rewrite Hddα in Hα2.
          assert (Hwfd : a_wf_ptyp Θ' (⇓ᵗ[ Θ' ] (msubst_lookup κ α)))
            by (apply a_wf_ptyp_downarrow_mono;
                [ exact HwfΘ' | exact Hwfα' | exact Hmona ]).
          apply a_wf_ptyp_ftv_dom in Hwfd. clear - Hwfd Hα2. fsetdec. }
      assert (Hακdom : α `in` dom κ).
      { rewrite Heqκ. rewrite dom_app.
        assert (Hαb : α `in` dom κb')
          by (eapply a_inc_flex_dom;
              [ exact Hincb | exact Hwf0 | exact Hfα0 ]).
        clear - Hαb. fsetdec. }
      assert (Hjoin_sub : empty ⨟ Θ' ⊢ₛᵃ
                (pskl_to_uskl (msubst_pskl
                   (msubst_compose (aenv_msubst Θ) κ) P))
              ∼ (pskl_to_bskl_syn (ptyp_to_pskl
                  (msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α)))).
      { rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P Hside).
        rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hακdom)).
        exact Hjstr. }
      (* ---- the μ-IH at the truncated problem : V is exactly constant ---- *)
      assert (Hlt : mu_lt
          (mu_assign Θ' (msubst_compose (aenv_msubst Θ) κ) α P Ξ Θ0')
          (mu_assign Θ κ α P Ξ ((α1, abind_tvar) :: Θ0'))).
      { unfold mu_assign. apply mu_lt_intro. right. split.
        - unfold V_assign, Vpskl, Vvar.
          rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P Hside).
          rewrite (msubst_lookup_compose (aenv_msubst Θ) κ
                     (or_introl Hακdom)).
          rewrite downarrow_idem_sub_pskl;
            [ | exact Hwfth | exact Hsub' ].
          rewrite downarrow_idem_sub_ptyp;
            [ | exact Hwfth | exact Hsub' ].
          reflexivity.
        - left. simpl. lia. }
      destruct (IH _ Hlt) as [_ [_ HaIH]].
      destruct (HaIH (add α1 N) Θ0' Ξ α P
                     (msubst_compose (aenv_msubst Θ) κ) Θ' eq_refl
                     Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hinc_sub HwfΘ'
                     Hjoin_sub)
        as [Θ1 [Ha' [Hnew Hopt'']]].
      exists ((α1 ~ abind_tvar) ++ Θ1). split.
      { apply a_assign__skip_rigid;
          [ exact Hγni | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss;
            [ exact Hnew
            | pose proof (a_wf_aenv_uniq Hwf) as Huq0; clear - Huq0;
              simpl_env in Huq0; solve_uniq ] | exact Ha' ]. }
      split; [ eapply avoid_relay_cons_mid; exact Hnew | ].
      (* ---- optimality : the OPT twin's two conjuncts ---- *)
      intros κ1 Hid Hinc1.
      assert (Hinc1_s : κ1 ∷ (Ξ ++ Θ0') ⊑ Θ1)
        by (eapply a_inc_tvar_mid_strip_id;
            [ exact Hdecl | exact Huqf | exact Hid | exact Hinc1 ]).
      destruct (Hopt'' κ1 Hid Hinc1_s) as [ζ' [Hζ' Hie']].
      exists ζ'. split.
      * (* ζ' ∷ ((α1~tvar)++Θ1) ⊑ Θ  via a_inc__tvar *)
        rewrite HeqΘ. apply a_inc__tvar; [ exact Hζ' | exact HsufΞv ].
      * (* factoring: mid_insert_tvar over ⇓κ, then ⇓κ→κ *)
        destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_tvar) ++ Θ0')
                    κ1 ((α1 ~ abind_tvar) ++ Θ1) Hdecl Hinc1)
          as [κ1a [κ1b' [Heqκ1' [Hdκ1a Hinc1x]]]].
        assert (Hmi : a_inc_equiv (Ξ ++ (α1 ~ abind_tvar) ++ Θ0')
                        (msubst_compose (aenv_msubst Θ) κ)
                        (msubst_compose ζ' κ1)
                        (Ξv ++ (α1 ~ abind_tvar) ++ Θ')).
        { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb').
          rewrite Heqκ1'. rewrite (msubst_compose_app ζ' κ1a κ1b').
          apply a_inc_equiv_mid_insert_tvar;
            [ exact Hdecl | exact Huq'
            | rewrite dom_msubst_compose; exact Hdκa
            | rewrite dom_msubst_compose; exact Hdκ1a
            | exact HsufΞv | ].
          rewrite Heqκ in Hie'.
          rewrite (msubst_compose_app (aenv_msubst Θ) κa κb') in Hie'.
          rewrite Heqκ1' in Hie'.
          rewrite (msubst_compose_app ζ' κ1a κ1b') in Hie'.
          exact Hie'. }
        rewrite <- HeqΘ in Hmi.
        eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
        pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
          as Hself.
        simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ].
  - (* head [α1 ~ var_typ A] : Assign-SkipTmVar — the EX+OPT fusion of the
       CLOSED OPT twin [skip_tm_var_case] (prop_completeness_consis.v (PART B):990):
       ⇓-normalize the competing increment below the middle, strengthen
       the join to the truncated target, recurse through the μ-IH (V is
       exactly constant by ⇓-idempotence, §1e), rebuild with the semantic
       middle. *)
    assert (Huqf : uniq (Ξ ++ (α1 ~ abind_var_typ A) ++ Θ0'))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfM : a_wf_aenv (Ξ ++ (α1 ~ abind_var_typ A) ++ Θ0'))
      by (exact Hwf).
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
      by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
    assert (Huq' : uniq (Ξ ++ Θ0')) by (apply a_wf_aenv_uniq; exact Hwf').
    assert (Hwf0 : a_wf_aenv Θ0') by (eapply a_wf_aenv_app_r; exact Hwf').
    assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hγfr : α1 `notin` ftvar_in_pskl P).
    { intro Hx. destruct (a_wf_pskl_ftv_tvarish HwfP Hx) as [Hemp | Hbt].
      - clear - Hemp. fsetdec.
      - assert (Hbx : binds α1 (abind_var_typ A)
                  (Ξ ++ (α1 ~ abind_var_typ A) ++ Θ0'))
          by (apply binds_app_3; left; reflexivity).
        destruct Hbt as [Hb | [Hb | [τ Hb]]];
          (pose proof (binds_unique _ _ _ _ _ Hb Hbx
                         (a_wf_aenv_uniq Hwf)) as Heq;
           discriminate Heq). }
    assert (HwfP' : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
      by (eapply a_wf_pskl_strip_mid; [ exact HwfP | exact Hγfr ]).
    assert (Hfα0 : a_flex_tvar Θ0' α).
    { destruct Hfα as [Hb | [τ0 Hb]];
        [ destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
          [ discriminate | left; exact Hb' ]
        | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
          [ discriminate | right; exists τ0; exact Hb' ] ]. }
    assert (Hbw : forall (β1 : atom) (bb : abind),
              binds β1 bb (Ξ ++ Θ0') ->
              binds β1 bb (Ξ ++ (α1 ~ abind_var_typ A) ++ Θ0')).
    { intros β1 bb Hb. unfold binds in *.
      apply in_app_or in Hb. apply in_or_app.
      destruct Hb as [Hb | Hb];
        [ left; exact Hb | right; simpl; right; exact Hb ]. }
    assert (Hnf' : a_non_flex (Ξ ++ Θ0') P).
    { destruct Hnf as [Hlc Hnfl]. split; [ exact Hlc | ].
      intro Hfl. apply Hnfl.
      inversion Hfl as [Θf β1 Hb | Θf β1 τ0 Hb]; subst;
        [ apply a_flex__var; apply Hbw; exact Hb
        | eapply a_flex__var_def; apply Hbw; exact Hb ]. }
    (* competing: strip Ξ, invert the α1-var middle *)
    destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_var_typ A) ++ Θ0')
                κ Θ Hdecl Hinc) as [κa [κb' [Heqκ [Hdκa Hincxb]]]].
    destruct (a_inc_var_inv Hincxb)
      as [Ξv [A' [Θ' [HeqΘ [HeqA' [HsufΞv Hincb]]]]]].
    assert (HwfΘ' : a_wf_aenv Θ').
    { rewrite HeqΘ in Hwfth.
      eapply a_wf_aenv_app_r with (Θp := Ξv ++ (α1 ~ abind_var_typ A')).
      simpl_env. simpl_env in Hwfth. exact Hwfth. }
    assert (HeqW : (Ξv ++ (α1 ~ abind_var_typ A')) ++ Θ' = Θ)
      by (rewrite HeqΘ; simpl_env; reflexivity).
    assert (Hincb_n : msubst_compose (aenv_msubst Θ) κb' ∷ Θ0' ⊑ Θ').
    { pose proof (a_inc_self_downarrow Hincb
                    (Ξv ++ (α1 ~ abind_var_typ A'))) as Hs.
      rewrite HeqW in Hs. apply Hs; [ exact Hwfth | exact HuqΘ | exact Hwf0 ]. }
    assert (Hside : forall β, β `in` ftvar_in_pskl P ->
              β `in` dom κ \/ β `notin` dom (aenv_msubst Θ)).
    { intros β Hβ.
      destruct (AtomSetProperties.In_dec β (dom κ)) as [Hin | Hni];
        [ left; exact Hin | right ].
      intro Hin2. apply aenv_msubst_dom_inv in Hin2.
      destruct (a_wf_pskl_ftv_tvarish HwfP Hβ) as [Hemp | Hbt];
        [ clear - Hemp; fsetdec | ].
      destruct Hbt as [Htv | [Hfm | [τ0 Hfd]]].
      - assert (HtvΘ : binds β abind_tvar Θ)
          by (eapply a_inc_binds_tvar; [ exact Hinc | exact Htv ]).
        destruct Hin2 as [Hb | [τ1 Hb]];
          (pose proof (binds_unique _ _ _ _ _ HtvΘ Hb
                         (a_wf_aenv_uniq Hwfth)) as Heqb;
           discriminate Heqb).
      - assert (Hyd : β `in` dom κ)
          by (eapply a_inc_flex_dom;
              [ exact Hinc | exact Hwf | left; exact Hfm ]).
        contradiction.
      - assert (Hyd : β `in` dom κ)
          by (eapply a_inc_flex_dom;
              [ exact Hinc | exact Hwf | right; exists τ0; exact Hfd ]).
        contradiction. }
    assert (Hmona : mono_ptyp (msubst_lookup κ α))
      by (eapply a_inc_lookup_mono; exact Hinc).
    assert (HO2 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P)) [<=] dom Θ').
    { eapply join_pskl_downarrow_mono_scoped;
        [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
        | exact Hmona | | ].
      - intros β τ Hbβ Hβd.
        assert (Hβpre : β `notin` dom (Ξv ++ (α1 ~ abind_var_typ A'))).
        { pose proof HuqΘ as Hu2. rewrite HeqΘ in Hu2.
          rewrite <- app_assoc in Hu2.
          apply uniq_app_iff in Hu2. destruct Hu2 as [_ [_ Hdisj]].
          clear - Hdisj Hβd. unfold disjoint in Hdisj. fsetdec. }
        assert (Hbβ' : binds β (abind_flex_mono_def τ) Θ').
        { rewrite HeqΘ in Hbβ. rewrite <- app_assoc in Hbβ.
          apply binds_app_iff in Hbβ. destruct Hbβ as [Hb | Hb];
            [ | exact Hb ].
          exfalso. apply binds_In in Hb. clear - Hb Hβpre. fsetdec. }
        apply a_wf_ptyp_ftv_dom.
        eapply a_wf_aenv_binds_def_wf_local; [ exact HwfΘ' | exact Hbβ' ].
      - assert (HαΘ0 : α `in` dom Θ0')
          by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb;
              exact Hb).
        assert (Hακa : α `notin` dom κa).
        { rewrite Hdκa. clear - Huqf HαΘ0. simpl_env in Huqf. solve_uniq. }
        assert (Hwfα : a_wf_ptyp Θ' (msubst_lookup κ α)).
        { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb' Hακa).
          eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ].
          destruct Hfα0 as [Hb | [τ0 Hb]];
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]. }
        apply a_wf_ptyp_ftv_dom. exact Hwfα. }
    assert (Hgr : forall α0, α0 `in` dom κa ->
               ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup κa α0)) [<=] dom Θ').
    { intros α0 Hα0.
      assert (HXP : α0 `in` ftvar_in_pskl P)
        by (apply Hdomξ; rewrite <- Hdκa; exact Hα0).
      assert (Hα0κ : α0 `in` dom κ)
        by (rewrite Heqκ; rewrite dom_app; clear - Hα0; fsetdec).
      assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup κa α0)
                     = msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α0).
      { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hα0κ)).
        f_equal. rewrite Heqκ. symmetry.
        apply msubst_lookup_app_in; exact Hα0. }
      rewrite Heqlk.
      eapply AtomSetProperties.subset_trans;
        [ apply (msubst_pskl_ftv_lower
                   (msubst_compose (aenv_msubst Θ) κ) P HXP) | ].
      rewrite msubst_pskl_compose; [ exact HO2 | exact Hside ]. }
    assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
    { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
      exact Hb. }
    assert (Hinc_sub0 : (msubst_compose (aenv_msubst Θ) κa)
                            ++ (msubst_compose (aenv_msubst Θ) κb') ∷ (Ξ ++ Θ0') ⊑ Θ').
    { assert (HincR : κa ++ κb' ∷ (Ξ ++ (α1 ~ abind_var_typ A) ++ Θ0') ⊑ Θ)
        by (rewrite <- Heqκ; exact Hinc).
      eapply a_inc_downarrow_prefix;
        [ exact Hdecl | exact HincR | exact Huqf | exact Hdκa
        | exact Hincb_n | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
    assert (Hinc_sub : msubst_compose (aenv_msubst Θ) κ ∷ (Ξ ++ Θ0') ⊑ Θ').
    { rewrite Heqκ. rewrite msubst_compose_app. exact Hinc_sub0. }
    (* the join over Θ' at ⇓κ *)
    assert (HαΘ0 : α `in` dom Θ0')
      by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
    assert (Hακa : α `notin` dom κa)
      by (rewrite Hdκa; clear - Huqf HαΘ0; simpl_env in Huqf; solve_uniq).
    assert (Hbtα0 : a_binds_tvar α Θ0')
      by (destruct Hfα0 as [Hb | [τ0 Hb]];
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]).
    assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup κ α)).
    { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb' Hακa).
      eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | exact Hbtα0 ]. }
    assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ')
      by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
    assert (Hvisα : forall β, β `in` ftvar_in_ptyp (msubst_lookup κ α) ->
              a_binds_tvar β Θ).
    { intros β Hβ.
      assert (HbtY' : a_binds_tvar β Θ')
        by (eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfα' | exact Hβ ]).
      destruct HbtY' as [Hb | [Hb | [τ0 Hb]]];
        [ left | right; left | right; right; exists τ0 ];
        apply Hsub'; exact Hb. }
    assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup κ α)
                 = ⇓ᵗ[ Θ' ] (msubst_lookup κ α)).
    { rewrite <- HeqW.
      apply downarrow_app_agree_ptyp;
        [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
    assert (Hj1 : ad_pat_consis empty Θ
              (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl κ P)))
              (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))).
    { eapply consis_downarrow_subject;
        [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
        | exact Hmona ]. }
    assert (Heqκα : Θ ⊢ (msubst_lookup κ α)
                      ≡ᵗ (⇓ᵗ[ Θ ] (msubst_lookup κ α))).
    { apply a_tyequiv_to_downarrow_mono;
        [ exact Hwfth
        | eapply a_wf_ptyp_weaken; [ exact Hsub' | exact Hwfα' ]
        | exact Hmona ]. }
    destruct (tyequiv_mono_consis_transport_q Heqκα Hwfth Hmona Hvisα)
      as [_ Hfwd].
    pose proof (Hfwd empty _ Hj1) as Hj2.
    assert (Hjstr : ad_pat_consis empty Θ'
              (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl κ P)))
              (pskl_to_bskl_syn (ptyp_to_pskl
                 (⇓ᵗ[ Θ ] (msubst_lookup κ α))))).
    { eapply ad_pat_consis_strengthen;
        [ exact Hj2 | exact HuqΘ | exact HwfΘ' | exact Hsub' | | ].
      - intros α2 Hα2. rewrite ftvar_in_uskl_pskl in Hα2.
        clear - HO2 Hα2. fsetdec.
      - intros α2 Hα2. rewrite ftvar_in_bskl_syn in Hα2.
        rewrite ftvar_in_ptyp_to_pskl in Hα2.
        rewrite Hddα in Hα2.
        assert (Hwfd : a_wf_ptyp Θ' (⇓ᵗ[ Θ' ] (msubst_lookup κ α)))
          by (apply a_wf_ptyp_downarrow_mono;
              [ exact HwfΘ' | exact Hwfα' | exact Hmona ]).
        apply a_wf_ptyp_ftv_dom in Hwfd. clear - Hwfd Hα2. fsetdec. }
    assert (Hακdom : α `in` dom κ).
    { rewrite Heqκ. rewrite dom_app.
      assert (Hαb : α `in` dom κb')
        by (eapply a_inc_flex_dom;
            [ exact Hincb | exact Hwf0 | exact Hfα0 ]).
      clear - Hαb. fsetdec. }
    assert (Hjoin_sub : empty ⨟ Θ' ⊢ₛᵃ
              (pskl_to_uskl (msubst_pskl
                 (msubst_compose (aenv_msubst Θ) κ) P))
            ∼ (pskl_to_bskl_syn (ptyp_to_pskl
                (msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α)))).
    { rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P Hside).
      rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hακdom)).
      exact Hjstr. }
    (* ---- the μ-IH at the truncated problem : V is exactly constant ---- *)
    assert (Hlt : mu_lt
        (mu_assign Θ' (msubst_compose (aenv_msubst Θ) κ) α P Ξ Θ0')
        (mu_assign Θ κ α P Ξ ((α1, abind_var_typ A) :: Θ0'))).
    { unfold mu_assign. apply mu_lt_intro. right. split.
      - unfold V_assign, Vpskl, Vvar.
        rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P Hside).
        rewrite (msubst_lookup_compose (aenv_msubst Θ) κ
                   (or_introl Hακdom)).
        rewrite downarrow_idem_sub_pskl;
          [ | exact Hwfth | exact Hsub' ].
        rewrite downarrow_idem_sub_ptyp;
          [ | exact Hwfth | exact Hsub' ].
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [_ HaIH]].
    destruct (HaIH (add α1 N) Θ0' Ξ α P
                   (msubst_compose (aenv_msubst Θ) κ) Θ' eq_refl
                   Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hinc_sub HwfΘ'
                   Hjoin_sub)
      as [Θ1 [Ha' [Hnew Hopt'']]].
    exists ((α1 ~ abind_var_typ A) ++ Θ1). split.
    { apply a_assign__skip_tm_var; [ (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss;
            [ exact Hnew
            | pose proof (a_wf_aenv_uniq Hwf) as Huq0; clear - Huq0;
              simpl_env in Huq0; solve_uniq ] | exact Ha' ]. }
    split; [ eapply avoid_relay_cons_mid; exact Hnew | ].
    (* ---- optimality : the OPT twin's two conjuncts ---- *)
    intros κ1 Hid Hinc1.
    assert (Hinc1_s : κ1 ∷ (Ξ ++ Θ0') ⊑ Θ1)
      by (eapply a_inc_var_mid_strip_id;
          [ exact Hdecl | exact Hid | exact Hinc1 ]).
    destruct (Hopt'' κ1 Hid Hinc1_s) as [ζ' [Hζ' Hie']].
    exists ζ'. split.
    + (* ζ' ∷ ((α1:A)++Θ1) ⊑ Θ  via a_inc__var *)
      rewrite HeqΘ. apply a_inc__var; [ exact Hζ' | | exact HsufΞv ].
      assert (HwfaΘ0x : a_wf_aenv ((α1 ~ abind_var_typ A) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      destruct (a_wf_aenv_var_typ_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HwfQ : a_wf_ptyp (Ξ ++ Θ0') A)
        by (eapply a_wf_ptyp_weaken;
            [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
      assert (HlcQ : lc_ptyp A) by (eapply a_wf_ptyp_lc; exact HwfQ0).
      assert (HwfΘ1 : a_wf_aenv Θ1)
        by (eapply a_assign_preserves_wf;
            [ exact Ha' | exact Hdecl | exact Hwf' | exact HwfP' ]).
      assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) κ))
        by (eapply a_inc_msubst_lc; exact Hinc_sub).
      assert (Hlc2 : msubst_lc (msubst_compose ζ' κ1)).
      { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ' | ].
        intros a t Hin. eapply is_id_msubst_values_lc;
          [ exact Hid | exact Hin ]. }
      pose proof (a_inc_equiv_msubst_ptyp HwfQ Hie' Hwf' Hlc1 Hlc2)
        as Hmid.
      rewrite (msubst_compose_id_ptyp Hwf' HwfΘ1 Hid Hinc1_s Hζ' HwfQ)
        in Hmid.
      assert (Hag : msubst_ptyp (msubst_compose (aenv_msubst Θ) κ) A
                  = msubst_ptyp (msubst_compose (aenv_msubst Θ) κb') A).
      { apply msubst_ptyp_agree. intros α0 HXQ.
        rewrite Heqκ. rewrite msubst_compose_app.
        apply msubst_lookup_app_notin.
        rewrite dom_msubst_compose. rewrite Hdκa.
        assert (Hα0Θ0 : α0 `in` dom Θ0')
          by (apply a_wf_ptyp_ftv_dom in HwfQ0;
              clear - HwfQ0 HXQ; fsetdec).
        clear - Huqf Hα0Θ0. simpl_env in Huqf. solve_uniq. }
      rewrite Hag in Hmid.
      eapply a_tyequiv__trans; [ exact HeqA' | ].
      eapply a_tyequiv__trans; [ | exact Hmid ].
      apply a_tyequiv__sym.
      eapply msubst_compose_downarrow_tyequiv
        with (Θpre := Ξv ++ (α1 ~ abind_var_typ A'));
        [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth
        | exact HwfΘ' | eapply a_inc_msubst_lc; exact Hincb
        | intros α0 HXd;
          destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
          (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
        | exact HlcQ ].
    + (* factoring: mid_insert_var over ⇓κ, then ⇓κ→κ via self_downarrow *)
      assert (HwfaΘ0x : a_wf_aenv ((α1 ~ abind_var_typ A) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      destruct (a_wf_aenv_var_typ_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HlcQ : lc_ptyp A) by (eapply a_wf_ptyp_lc; exact HwfQ0).
      destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_var_typ A) ++ Θ0')
                  κ1 ((α1 ~ abind_var_typ A) ++ Θ1) Hdecl Hinc1)
        as [κ1a [κ1b' [Heqκ1' [Hdκ1a Hinc1x]]]].
      assert (Hmiddle : Θ' ⊢ A' ≡ᵗ
                msubst_ptyp (msubst_compose (aenv_msubst Θ) κb') A).
      { eapply a_tyequiv__trans; [ exact HeqA' | ].
        apply a_tyequiv__sym.
        eapply msubst_compose_downarrow_tyequiv
          with (Θpre := Ξv ++ (α1 ~ abind_var_typ A'));
          [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
          | eapply a_inc_msubst_lc; exact Hincb
          | intros α0 HXd;
            destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
            (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
          | exact HlcQ ]. }
      assert (Hmi : a_inc_equiv (Ξ ++ (α1 ~ abind_var_typ A) ++ Θ0')
                      (msubst_compose (aenv_msubst Θ) κ)
                      (msubst_compose ζ' κ1)
                      (Ξv ++ (α1 ~ abind_var_typ A') ++ Θ')).
      { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb').
        rewrite Heqκ1'. rewrite (msubst_compose_app ζ' κ1a κ1b').
        apply a_inc_equiv_mid_insert_var;
          [ exact Hdecl | exact Huq'
          | rewrite dom_msubst_compose; exact Hdκa
          | rewrite dom_msubst_compose; exact Hdκ1a
          | exact Hmiddle | exact HsufΞv | ].
        rewrite Heqκ in Hie'.
        rewrite (msubst_compose_app (aenv_msubst Θ) κa κb') in Hie'.
        rewrite Heqκ1' in Hie'.
        rewrite (msubst_compose_app ζ' κ1a κ1b') in Hie'.
        exact Hie'. }
      rewrite <- HeqΘ in Hmi.
      eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
      pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
        as Hself.
      simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ].
  - (* head [α1 ~ var_skl Q] : Assign-SkipTmSkl — as SkipTmVar with the
       ≡ˢ semantic middle throughout. *)
    assert (Huqf : uniq (Ξ ++ (α1 ~ abind_var_skl Q) ++ Θ0'))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfM : a_wf_aenv (Ξ ++ (α1 ~ abind_var_skl Q) ++ Θ0'))
      by (exact Hwf).
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
      by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
    assert (Huq' : uniq (Ξ ++ Θ0')) by (apply a_wf_aenv_uniq; exact Hwf').
    assert (Hwf0 : a_wf_aenv Θ0') by (eapply a_wf_aenv_app_r; exact Hwf').
    assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hγfr : α1 `notin` ftvar_in_pskl P).
    { intro Hx. destruct (a_wf_pskl_ftv_tvarish HwfP Hx) as [Hemp | Hbt].
      - clear - Hemp. fsetdec.
      - assert (Hbx : binds α1 (abind_var_skl Q)
                  (Ξ ++ (α1 ~ abind_var_skl Q) ++ Θ0'))
          by (apply binds_app_3; left; reflexivity).
        destruct Hbt as [Hb | [Hb | [τ Hb]]];
          (pose proof (binds_unique _ _ _ _ _ Hb Hbx
                         (a_wf_aenv_uniq Hwf)) as Heq;
           discriminate Heq). }
    assert (HwfP' : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
      by (eapply a_wf_pskl_strip_mid; [ exact HwfP | exact Hγfr ]).
    assert (Hfα0 : a_flex_tvar Θ0' α).
    { destruct Hfα as [Hb | [τ0 Hb]];
        [ destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
          [ discriminate | left; exact Hb' ]
        | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
          [ discriminate | right; exists τ0; exact Hb' ] ]. }
    assert (Hbw : forall (β1 : atom) (bb : abind),
              binds β1 bb (Ξ ++ Θ0') ->
              binds β1 bb (Ξ ++ (α1 ~ abind_var_skl Q) ++ Θ0')).
    { intros β1 bb Hb. unfold binds in *.
      apply in_app_or in Hb. apply in_or_app.
      destruct Hb as [Hb | Hb];
        [ left; exact Hb | right; simpl; right; exact Hb ]. }
    assert (Hnf' : a_non_flex (Ξ ++ Θ0') P).
    { destruct Hnf as [Hlc Hnfl]. split; [ exact Hlc | ].
      intro Hfl. apply Hnfl.
      inversion Hfl as [Θf β1 Hb | Θf β1 τ0 Hb]; subst;
        [ apply a_flex__var; apply Hbw; exact Hb
        | eapply a_flex__var_def; apply Hbw; exact Hb ]. }
    (* competing: strip Ξ, invert the α1-var middle *)
    destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_var_skl Q) ++ Θ0')
                κ Θ Hdecl Hinc) as [κa [κb' [Heqκ [Hdκa Hincxb]]]].
    destruct (a_inc_var_skl_inv Hincxb)
      as [Ξv [Q' [Θ' [HeqΘ [HeqQ' [HsufΞv Hincb]]]]]].
    assert (HwfΘ' : a_wf_aenv Θ').
    { rewrite HeqΘ in Hwfth.
      eapply a_wf_aenv_app_r with (Θp := Ξv ++ (α1 ~ abind_var_skl Q')).
      simpl_env. simpl_env in Hwfth. exact Hwfth. }
    assert (HeqW : (Ξv ++ (α1 ~ abind_var_skl Q')) ++ Θ' = Θ)
      by (rewrite HeqΘ; simpl_env; reflexivity).
    assert (Hincb_n : msubst_compose (aenv_msubst Θ) κb' ∷ Θ0' ⊑ Θ').
    { pose proof (a_inc_self_downarrow Hincb
                    (Ξv ++ (α1 ~ abind_var_skl Q'))) as Hs.
      rewrite HeqW in Hs. apply Hs; [ exact Hwfth | exact HuqΘ | exact Hwf0 ]. }
    assert (Hside : forall β, β `in` ftvar_in_pskl P ->
              β `in` dom κ \/ β `notin` dom (aenv_msubst Θ)).
    { intros β Hβ.
      destruct (AtomSetProperties.In_dec β (dom κ)) as [Hin | Hni];
        [ left; exact Hin | right ].
      intro Hin2. apply aenv_msubst_dom_inv in Hin2.
      destruct (a_wf_pskl_ftv_tvarish HwfP Hβ) as [Hemp | Hbt];
        [ clear - Hemp; fsetdec | ].
      destruct Hbt as [Htv | [Hfm | [τ0 Hfd]]].
      - assert (HtvΘ : binds β abind_tvar Θ)
          by (eapply a_inc_binds_tvar; [ exact Hinc | exact Htv ]).
        destruct Hin2 as [Hb | [τ1 Hb]];
          (pose proof (binds_unique _ _ _ _ _ HtvΘ Hb
                         (a_wf_aenv_uniq Hwfth)) as Heqb;
           discriminate Heqb).
      - assert (Hyd : β `in` dom κ)
          by (eapply a_inc_flex_dom;
              [ exact Hinc | exact Hwf | left; exact Hfm ]).
        contradiction.
      - assert (Hyd : β `in` dom κ)
          by (eapply a_inc_flex_dom;
              [ exact Hinc | exact Hwf | right; exists τ0; exact Hfd ]).
        contradiction. }
    assert (Hmona : mono_ptyp (msubst_lookup κ α))
      by (eapply a_inc_lookup_mono; exact Hinc).
    assert (HO2 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P)) [<=] dom Θ').
    { eapply join_pskl_downarrow_mono_scoped;
        [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
        | exact Hmona | | ].
      - intros β τ Hbβ Hβd.
        assert (Hβpre : β `notin` dom (Ξv ++ (α1 ~ abind_var_skl Q'))).
        { pose proof HuqΘ as Hu2. rewrite HeqΘ in Hu2.
          rewrite <- app_assoc in Hu2.
          apply uniq_app_iff in Hu2. destruct Hu2 as [_ [_ Hdisj]].
          clear - Hdisj Hβd. unfold disjoint in Hdisj. fsetdec. }
        assert (Hbβ' : binds β (abind_flex_mono_def τ) Θ').
        { rewrite HeqΘ in Hbβ. rewrite <- app_assoc in Hbβ.
          apply binds_app_iff in Hbβ. destruct Hbβ as [Hb | Hb];
            [ | exact Hb ].
          exfalso. apply binds_In in Hb. clear - Hb Hβpre. fsetdec. }
        apply a_wf_ptyp_ftv_dom.
        eapply a_wf_aenv_binds_def_wf_local; [ exact HwfΘ' | exact Hbβ' ].
      - assert (HαΘ0 : α `in` dom Θ0')
          by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb;
              exact Hb).
        assert (Hακa : α `notin` dom κa).
        { rewrite Hdκa. clear - Huqf HαΘ0. simpl_env in Huqf. solve_uniq. }
        assert (Hwfα : a_wf_ptyp Θ' (msubst_lookup κ α)).
        { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb' Hακa).
          eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ].
          destruct Hfα0 as [Hb | [τ0 Hb]];
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]. }
        apply a_wf_ptyp_ftv_dom. exact Hwfα. }
    assert (Hgr : forall α0, α0 `in` dom κa ->
               ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup κa α0)) [<=] dom Θ').
    { intros α0 Hα0.
      assert (HXP : α0 `in` ftvar_in_pskl P)
        by (apply Hdomξ; rewrite <- Hdκa; exact Hα0).
      assert (Hα0κ : α0 `in` dom κ)
        by (rewrite Heqκ; rewrite dom_app; clear - Hα0; fsetdec).
      assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup κa α0)
                     = msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α0).
      { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hα0κ)).
        f_equal. rewrite Heqκ. symmetry.
        apply msubst_lookup_app_in; exact Hα0. }
      rewrite Heqlk.
      eapply AtomSetProperties.subset_trans;
        [ apply (msubst_pskl_ftv_lower
                   (msubst_compose (aenv_msubst Θ) κ) P HXP) | ].
      rewrite msubst_pskl_compose; [ exact HO2 | exact Hside ]. }
    assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
    { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
      exact Hb. }
    assert (Hinc_sub0 : (msubst_compose (aenv_msubst Θ) κa)
                            ++ (msubst_compose (aenv_msubst Θ) κb') ∷ (Ξ ++ Θ0') ⊑ Θ').
    { assert (HincR : κa ++ κb' ∷ (Ξ ++ (α1 ~ abind_var_skl Q) ++ Θ0') ⊑ Θ)
        by (rewrite <- Heqκ; exact Hinc).
      eapply a_inc_downarrow_prefix;
        [ exact Hdecl | exact HincR | exact Huqf | exact Hdκa
        | exact Hincb_n | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
    assert (Hinc_sub : msubst_compose (aenv_msubst Θ) κ ∷ (Ξ ++ Θ0') ⊑ Θ').
    { rewrite Heqκ. rewrite msubst_compose_app. exact Hinc_sub0. }
    (* the join over Θ' at ⇓κ *)
    assert (HαΘ0 : α `in` dom Θ0')
      by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
    assert (Hακa : α `notin` dom κa)
      by (rewrite Hdκa; clear - Huqf HαΘ0; simpl_env in Huqf; solve_uniq).
    assert (Hbtα0 : a_binds_tvar α Θ0')
      by (destruct Hfα0 as [Hb | [τ0 Hb]];
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]).
    assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup κ α)).
    { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb' Hακa).
      eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | exact Hbtα0 ]. }
    assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ')
      by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
    assert (Hvisα : forall β, β `in` ftvar_in_ptyp (msubst_lookup κ α) ->
              a_binds_tvar β Θ).
    { intros β Hβ.
      assert (HbtY' : a_binds_tvar β Θ')
        by (eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfα' | exact Hβ ]).
      destruct HbtY' as [Hb | [Hb | [τ0 Hb]]];
        [ left | right; left | right; right; exists τ0 ];
        apply Hsub'; exact Hb. }
    assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup κ α)
                 = ⇓ᵗ[ Θ' ] (msubst_lookup κ α)).
    { rewrite <- HeqW.
      apply downarrow_app_agree_ptyp;
        [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
    assert (Hj1 : ad_pat_consis empty Θ
              (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl κ P)))
              (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))).
    { eapply consis_downarrow_subject;
        [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
        | exact Hmona ]. }
    assert (Heqκα : Θ ⊢ (msubst_lookup κ α)
                      ≡ᵗ (⇓ᵗ[ Θ ] (msubst_lookup κ α))).
    { apply a_tyequiv_to_downarrow_mono;
        [ exact Hwfth
        | eapply a_wf_ptyp_weaken; [ exact Hsub' | exact Hwfα' ]
        | exact Hmona ]. }
    destruct (tyequiv_mono_consis_transport_q Heqκα Hwfth Hmona Hvisα)
      as [_ Hfwd].
    pose proof (Hfwd empty _ Hj1) as Hj2.
    assert (Hjstr : ad_pat_consis empty Θ'
              (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl κ P)))
              (pskl_to_bskl_syn (ptyp_to_pskl
                 (⇓ᵗ[ Θ ] (msubst_lookup κ α))))).
    { eapply ad_pat_consis_strengthen;
        [ exact Hj2 | exact HuqΘ | exact HwfΘ' | exact Hsub' | | ].
      - intros α2 Hα2. rewrite ftvar_in_uskl_pskl in Hα2.
        clear - HO2 Hα2. fsetdec.
      - intros α2 Hα2. rewrite ftvar_in_bskl_syn in Hα2.
        rewrite ftvar_in_ptyp_to_pskl in Hα2.
        rewrite Hddα in Hα2.
        assert (Hwfd : a_wf_ptyp Θ' (⇓ᵗ[ Θ' ] (msubst_lookup κ α)))
          by (apply a_wf_ptyp_downarrow_mono;
              [ exact HwfΘ' | exact Hwfα' | exact Hmona ]).
        apply a_wf_ptyp_ftv_dom in Hwfd. clear - Hwfd Hα2. fsetdec. }
    assert (Hακdom : α `in` dom κ).
    { rewrite Heqκ. rewrite dom_app.
      assert (Hαb : α `in` dom κb')
        by (eapply a_inc_flex_dom;
            [ exact Hincb | exact Hwf0 | exact Hfα0 ]).
      clear - Hαb. fsetdec. }
    assert (Hjoin_sub : empty ⨟ Θ' ⊢ₛᵃ
              (pskl_to_uskl (msubst_pskl
                 (msubst_compose (aenv_msubst Θ) κ) P))
            ∼ (pskl_to_bskl_syn (ptyp_to_pskl
                (msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α)))).
    { rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P Hside).
      rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hακdom)).
      exact Hjstr. }
    (* ---- the μ-IH at the truncated problem : V is exactly constant ---- *)
    assert (Hlt : mu_lt
        (mu_assign Θ' (msubst_compose (aenv_msubst Θ) κ) α P Ξ Θ0')
        (mu_assign Θ κ α P Ξ ((α1, abind_var_skl Q) :: Θ0'))).
    { unfold mu_assign. apply mu_lt_intro. right. split.
      - unfold V_assign, Vpskl, Vvar.
        rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P Hside).
        rewrite (msubst_lookup_compose (aenv_msubst Θ) κ
                   (or_introl Hακdom)).
        rewrite downarrow_idem_sub_pskl;
          [ | exact Hwfth | exact Hsub' ].
        rewrite downarrow_idem_sub_ptyp;
          [ | exact Hwfth | exact Hsub' ].
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [_ HaIH]].
    destruct (HaIH (add α1 N) Θ0' Ξ α P
                   (msubst_compose (aenv_msubst Θ) κ) Θ' eq_refl
                   Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hinc_sub HwfΘ'
                   Hjoin_sub)
      as [Θ1 [Ha' [Hnew Hopt'']]].
    exists ((α1 ~ abind_var_skl Q) ++ Θ1). split.
    { apply a_assign__skip_tm_skl; [ (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss;
            [ exact Hnew
            | pose proof (a_wf_aenv_uniq Hwf) as Huq0; clear - Huq0;
              simpl_env in Huq0; solve_uniq ] | exact Ha' ]. }
    split; [ eapply avoid_relay_cons_mid; exact Hnew | ].
    (* ---- optimality : the OPT twin's two conjuncts ---- *)
    intros κ1 Hid Hinc1.
    assert (Hinc1_s : κ1 ∷ (Ξ ++ Θ0') ⊑ Θ1)
      by (eapply a_inc_var_skl_mid_strip_id;
          [ exact Hdecl | exact Hid | exact Hinc1 ]).
    destruct (Hopt'' κ1 Hid Hinc1_s) as [ζ' [Hζ' Hie']].
    exists ζ'. split.
    + (* ζ' ∷ ((α1:A)++Θ1) ⊑ Θ  via a_inc__var *)
      rewrite HeqΘ. apply a_inc__var_skl; [ exact Hζ' | | exact HsufΞv ].
      assert (HwfaΘ0x : a_wf_aenv ((α1 ~ abind_var_skl Q) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      destruct (a_wf_aenv_var_skl_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HwfQ : a_scope_pskl (Ξ ++ Θ0') Q)
        by (eapply a_scope_pskl_weaken;
            [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
      assert (HlcQ : lc_pskl Q) by (eapply a_scope_pskl_lc; exact HwfQ0).
      assert (HwfΘ1 : a_wf_aenv Θ1)
        by (eapply a_assign_preserves_wf;
            [ exact Ha' | exact Hdecl | exact Hwf' | exact HwfP' ]).
      assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) κ))
        by (eapply a_inc_msubst_lc; exact Hinc_sub).
      assert (Hlc2 : msubst_lc (msubst_compose ζ' κ1)).
      { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ' | ].
        intros a t Hin. eapply is_id_msubst_values_lc;
          [ exact Hid | exact Hin ]. }
      pose proof (a_inc_equiv_msubst_pskl HwfQ Hie' Hwf' Hlc1 Hlc2)
        as Hmid.
      rewrite (msubst_compose_id_pskl Hwf' HwfΘ1 Hid Hinc1_s Hζ' HwfQ)
        in Hmid.
      assert (Hag : msubst_pskl (msubst_compose (aenv_msubst Θ) κ) Q
                  = msubst_pskl (msubst_compose (aenv_msubst Θ) κb') Q).
      { apply msubst_pskl_agree. intros α0 HXQ.
        rewrite Heqκ. rewrite msubst_compose_app.
        apply msubst_lookup_app_notin.
        rewrite dom_msubst_compose. rewrite Hdκa.
        assert (Hα0Θ0 : α0 `in` dom Θ0')
          by (apply a_scope_pskl_ftv_dom' in HwfQ0;
              clear - HwfQ0 HXQ; fsetdec).
        clear - Huqf Hα0Θ0. simpl_env in Huqf. solve_uniq. }
      rewrite Hag in Hmid.
      eapply a_pskl_tyequiv__trans; [ exact HeqQ' | ].
      eapply a_pskl_tyequiv__trans; [ | exact Hmid ].
      apply a_pskl_tyequiv__sym.
      eapply msubst_pskl_compose_downarrow_tyequiv
        with (Θpre := Ξv ++ (α1 ~ abind_var_skl Q'));
        [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth
        | exact HwfΘ' | eapply a_inc_msubst_lc; exact Hincb
        | intros α0 HXd;
          destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
          (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
        | exact HlcQ ].
    + (* factoring: mid_insert_var over ⇓κ, then ⇓κ→κ via self_downarrow *)
      assert (HwfaΘ0x : a_wf_aenv ((α1 ~ abind_var_skl Q) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      destruct (a_wf_aenv_var_skl_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HlcQ : lc_pskl Q) by (eapply a_scope_pskl_lc; exact HwfQ0).
      destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_var_skl Q) ++ Θ0')
                  κ1 ((α1 ~ abind_var_skl Q) ++ Θ1) Hdecl Hinc1)
        as [κ1a [κ1b' [Heqκ1' [Hdκ1a Hinc1x]]]].
      assert (Hmiddle : Θ' ⊢ Q' ≡ˢ
                msubst_pskl (msubst_compose (aenv_msubst Θ) κb') Q).
      { eapply a_pskl_tyequiv__trans; [ exact HeqQ' | ].
        apply a_pskl_tyequiv__sym.
        eapply msubst_pskl_compose_downarrow_tyequiv
          with (Θpre := Ξv ++ (α1 ~ abind_var_skl Q'));
          [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
          | eapply a_inc_msubst_lc; exact Hincb
          | intros α0 HXd;
            destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
            (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
          | exact HlcQ ]. }
      assert (Hmi : a_inc_equiv (Ξ ++ (α1 ~ abind_var_skl Q) ++ Θ0')
                      (msubst_compose (aenv_msubst Θ) κ)
                      (msubst_compose ζ' κ1)
                      (Ξv ++ (α1 ~ abind_var_skl Q') ++ Θ')).
      { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb').
        rewrite Heqκ1'. rewrite (msubst_compose_app ζ' κ1a κ1b').
        apply a_inc_equiv_mid_insert_var_skl;
          [ exact Hdecl | exact Huq'
          | rewrite dom_msubst_compose; exact Hdκa
          | rewrite dom_msubst_compose; exact Hdκ1a
          | exact Hmiddle | exact HsufΞv | ].
        rewrite Heqκ in Hie'.
        rewrite (msubst_compose_app (aenv_msubst Θ) κa κb') in Hie'.
        rewrite Heqκ1' in Hie'.
        rewrite (msubst_compose_app ζ' κ1a κ1b') in Hie'.
        exact Hie'. }
      rewrite <- HeqΘ in Hmi.
      eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
      pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
        as Hself.
      simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ].
  - (* head [α1̂] undefined flexible *)
    destruct (α1 == α) as [-> | Hα1α].
    + (* the head IS the subject α̂ *)
      destruct (pskl_eq_dec P (pskl_tophole (pskl_var_f α))) as [-> | HneP].
      * (* Assign-UnivGhost-Id : axiom, Θ1 = Θ0, Ξ forced nil. *)
        assert (HΞnil : Ξ = nil).
        { destruct Ξ as [ | [ξ bξ] Ξ' ]; [ reflexivity | exfalso ].
          assert (Hξ : ξ `in` ftvar_in_pskl (pskl_tophole (pskl_var_f α)))
            by (apply Hdomξ; simpl; fsetdec).
          simpl in Hξ.
          assert (Heqξ : ξ = α) by (clear - Hξ; fsetdec). subst ξ.
          pose proof (a_wf_aenv_uniq Hwf) as Hu.
          clear - Hu. simpl_env in Hu. solve_uniq. }
        subst Ξ. simpl_env in *.
        exists ((α ~ abind_flex_mono) ++ Θ0'). split.
        { apply a_assign__univ_ghost_id. }
        split; [ intros γ Hγ; left; simpl_env in *; exact Hγ | ].
        intros κ1 Hid Hinc1. exists κ.
        exact (opt_axiom_factor Hwf Hid Hinc1 Hinc).
      * (* Assign-SolveM : the standalone lemma above supplies the two
           premises the paper leaves implicit (design doc §9.2) — the
           occurs check and the mono guess witness — plus the ζ-factoring. *)
        apply (assign_solve_m_complete N Θ0' Hdecl Hwf HwfP Hnf HneP Hinc
                 Hwfth Hjoin).
    + (* α1̂ ≠ α̂ : Assign-Depend (α1 ∈ ftv P) / Assign-Skip (α1 ∉ ftv P) *)
      assert (Hαα1 : α <> α1) by auto.
      assert (Hwfmid : a_wf_aenv ((α1 ~ abind_flex_mono) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      inversion Hwfmid as [ | γh Θh Hnd Hwf0 | | | | ]; subst.
      assert (Hfα0 : a_flex_tvar Θ0' α)
        by (eapply a_flex_tvar_strip_head; [ exact Hαα1 | exact Hfα ]).
      destruct (AtomSetProperties.In_dec α1 (ftvar_in_pskl P)) as [Hγin | Hγni].
      * (* Assign-Depend : α1̂ moves to the tail of Ξ; pure re-association. *)
        assert (Hdecl' : a_decls (Ξ ++ (α1 ~ abind_flex_mono)))
          by (apply a_decls_app;
              [ exact Hdecl | apply (a_decls__cons α1); apply a_decls__nil ]).
        assert (Hdomξ' : dom (Ξ ++ (α1 ~ abind_flex_mono)) [<=] ftvar_in_pskl P)
          by (rewrite dom_app; simpl; clear - Hdomξ Hγin; fsetdec).
        assert (Hwf2 : a_wf_aenv ((Ξ ++ (α1 ~ abind_flex_mono)) ++ Θ0'))
          by (simpl_env; exact Hwf).
        assert (HwfP2 : ((Ξ ++ (α1 ~ abind_flex_mono)) ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
          by (simpl_env; exact HwfP).
        assert (Hnf2 : a_non_flex ((Ξ ++ (α1 ~ abind_flex_mono)) ++ Θ0') P)
          by (simpl_env; exact Hnf).
        assert (Hinc2 : κ ∷ ((Ξ ++ (α1 ~ abind_flex_mono)) ++ Θ0') ⊑ Θ)
          by (simpl_env; exact Hinc).
        assert (Hlt : mu_lt (mu_assign Θ κ α P (Ξ ++ (α1 ~ abind_flex_mono)) Θ0')
                            (mu_assign Θ κ α P Ξ ((α1 ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_assign. apply mu_lt_intro. right. split; [ reflexivity | ].
          right. split.
          - rewrite length_app. simpl. lia.
          - right. split; [ reflexivity | simpl; lia ]. }
        destruct (IH _ Hlt) as [_ [_ HaIH]].
        destruct (HaIH N Θ0' (Ξ ++ (α1 ~ abind_flex_mono)) α P κ Θ eq_refl
                       Hdecl' Hwf2 Hfα0 HwfP2 Hnf2 Hdomξ' Hinc2 Hwfth Hjoin)
          as [Θ1 [Ha' [Hnew Hopt']]].
        exists Θ1. split.
        { apply a_assign__depend; [ exact Hαα1 | exact Hγin | exact Ha' ]. }
        split;
          [ intros γ Hγ; destruct (Hnew γ Hγ) as [Hin | Hni];
            [ left; simpl_env in *; exact Hin | right; exact Hni ] | ].
        intros κ1 Hid Hinc1.
        assert (Hinc1' : κ1 ∷ ((Ξ ++ (α1 ~ abind_flex_mono)) ++ Θ0') ⊑ Θ1)
          by (simpl_env; exact Hinc1).
        destruct (Hopt' κ1 Hid Hinc1') as [ζ [Hζ Hie]].
        exists ζ. split; [ exact Hζ | ].
        simpl_env in Hie. exact Hie.
      * (* Assign-Skip : α1̂ dropped from the walked context (mid-strip). *)
        destruct (a_inc_mid_strip_flex α1 Θ0' Hdecl Hinc)
          as [κa [τα1 [κb [Heqκ [Hdκa [Hincb Hincab]]]]]].
        assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
          by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact Hwf ]).
        assert (HwfP' : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
          by (eapply a_wf_pskl_strip_mid; [ exact HwfP | exact Hγni ]).
        assert (Hbw : forall (β1 : atom) (bb : abind),
                  binds β1 bb (Ξ ++ Θ0') ->
                  binds β1 bb (Ξ ++ (α1 ~ abind_flex_mono) ++ Θ0')).
        { intros β1 bb Hb. unfold binds in *.
          apply in_app_or in Hb. apply in_or_app.
          destruct Hb as [Hb | Hb];
            [ left; exact Hb | right; simpl; right; exact Hb ]. }
        assert (Hnf' : a_non_flex (Ξ ++ Θ0') P).
        { destruct Hnf as [Hlc Hnfl]. split; [ exact Hlc | ].
          intro Hfl. apply Hnfl.
          inversion Hfl as [Θf β1 Hb | Θf β1 τ0 Hb]; subst;
            [ apply a_flex__var; apply Hbw; exact Hb
            | eapply a_flex__var_def; apply Hbw; exact Hb ]. }
        assert (HeqP : msubst_pskl (κa ++ κb) P = msubst_pskl κ P).
        { rewrite Heqκ. apply msubst_pskl_agree. intros α0 Hα0.
          symmetry. apply msubst_lookup_mid_drop.
          clear - Hα0 Hγni. intro; subst α0; contradiction. }
        assert (Hlkα : msubst_lookup (κa ++ κb) α = msubst_lookup κ α)
          by (rewrite Heqκ; symmetry; apply msubst_lookup_mid_drop; exact Hαα1).
        assert (Hjoin' : empty ⨟ Θ ⊢ₛᵃ
                  (pskl_to_uskl (msubst_pskl (κa ++ κb) P))
                ∼ (pskl_to_bskl_syn (ptyp_to_pskl
                     (msubst_lookup (κa ++ κb) α))))
          by (rewrite HeqP, Hlkα; exact Hjoin).
        assert (Hlt : mu_lt (mu_assign Θ (κa ++ κb) α P Ξ Θ0')
                            (mu_assign Θ κ α P Ξ
                                       ((α1 ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_assign. apply mu_lt_intro. right. split.
          - unfold V_assign, Vpskl, Vvar. rewrite HeqP, Hlkα. reflexivity.
          - left. simpl. lia. }
        destruct (IH _ Hlt) as [_ [_ HaIH]].
        destruct (HaIH (add α1 N) Θ0' Ξ α P (κa ++ κb) Θ eq_refl
                       Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hincab Hwfth Hjoin')
          as [Θ1' [Ha' [Hnew Hopt']]].
        exists ((α1 ~ abind_flex_mono) ++ Θ1'). split.
        { apply a_assign__skip;
            [ exact Hαα1 | exact Hγni | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss;
            [ exact Hnew
            | pose proof (a_wf_aenv_uniq Hwf) as Huq0; clear - Huq0;
              simpl_env in Huq0; solve_uniq ] | exact Ha' ]. }
        split; [ eapply avoid_relay_cons_mid; exact Hnew | ].
        intros κ1 Hid Hinc1.
        destruct (a_inc_mid_strip_flex α1 Θ0' Hdecl Hinc1)
          as [κ1a [τ1 [κ1b [Heqκ1 [Hdκ1a [Hinc1b Hinc1ab]]]]]].
        rewrite Heqκ1 in Hid.
        apply Forall_app in Hid as [Hida Hidtail].
        pose proof (Forall_inv Hidtail) as Heγ1.
        pose proof (Forall_inv_tail Hidtail) as Hidb.
        unfold is_id_entry in Heγ1; simpl in Heγ1; subst τ1.
        assert (Hidab : is_id_msubst (κ1a ++ κ1b))
          by (apply Forall_app; split; assumption).
        destruct (a_assign_sound Ha' Hdecl Hwf' HwfP')
          as [[[w [Hidw Hincw]] _] _].
        assert (Hweq : w = κ1a ++ κ1b)
          by (eapply is_id_inc_unique;
              [ exact Hincw | exact Hidw | exact Hinc1ab | exact Hidab ]).
        subst w.
        destruct (Hopt' (κ1a ++ κ1b) Hidab Hincw) as [ζ' [Hζ' Hie']].
        (* facts about the dropped image τα1 *)
        assert (Huqf : uniq (Ξ ++ (α1 ~ abind_flex_mono) ++ Θ0'))
          by (apply a_wf_aenv_uniq; exact Hwf).
        assert (Hα1κa : α1 `notin` dom κa)
          by (rewrite Hdκa; clear - Huqf; simpl_env in Huqf; solve_uniq).
        assert (Hlkγ : msubst_lookup κ α1 = τα1)
          by (rewrite Heqκ; rewrite msubst_lookup_app_notin by exact Hα1κa;
              apply msubst_lookup_cons_eq).
        assert (Hmτα1 : mono_ptyp τα1)
          by (rewrite <- Hlkγ; eapply a_inc_lookup_mono; exact Hinc).
        assert (Hbtγ : a_binds_tvar α1 (Ξ ++ (α1 ~ abind_flex_mono) ++ Θ0'))
          by (right; left; unfold binds; apply in_or_app; right; left;
              reflexivity).
        assert (Hwfτα1 : a_wf_ptyp Θ τα1)
          by (rewrite <- Hlkγ;
              eapply a_inc_lookup_wf;
              [ exact Hinc | exact Hwf | exact Hbtγ ]).
        assert (Hα1κ1a : α1 `notin` dom κ1a)
          by (rewrite Hdκ1a; clear - Huqf; simpl_env in Huqf; solve_uniq).
        assert (Hα1κ1b : α1 `notin` dom κ1b)
          by (pose proof (a_inc_dom_sub Hinc1b) as Hs;
              clear - Hs Hnd; fsetdec).
        exists ((α1, τα1) :: ζ'). split.
        -- apply a_inc__flex; [ exact Hζ' | exact Hwfτα1 | exact Hmτα1 ].
        -- (* compute ζ ∘ κ1 = (ζ' ∘ κ1a) ++ (α1,τα1) :: (ζ' ∘ κ1b), then
              mid-insert the matching flex pair *)
           assert (Heqc : msubst_compose ((α1, τα1) :: ζ')
                            (κ1a ++ (α1, ptyp_var_f α1) :: κ1b)
                        = msubst_compose ζ' κ1a
                          ++ (α1, τα1) :: msubst_compose ζ' κ1b).
           { rewrite msubst_compose_app. f_equal.
             - apply (msubst_compose_cons_l_id τα1 ζ' Hida Hα1κ1a).
             - change (msubst_compose ((α1, τα1) :: ζ')
                         ((α1, ptyp_var_f α1) :: κ1b))
                 with ((α1, msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
                       :: msubst_compose ((α1, τα1) :: ζ') κ1b).
               rewrite (msubst_compose_cons_l_id τα1 ζ' Hidb Hα1κ1b).
               change (msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
                 with (msubst_lookup ((α1, τα1) :: ζ') α1).
               rewrite msubst_lookup_cons_eq. reflexivity. }
           rewrite Heqκ1, Heqκ, Heqc.
           apply a_inc_equiv_mid_insert_flex;
             [ exact Hdecl
             | apply a_wf_aenv_uniq; exact Hwf'
             | exact Hdκa
             | rewrite dom_msubst_compose; exact Hdκ1a
             | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτα1
             | ].
           rewrite <- msubst_compose_app. exact Hie'.
  - (* head [α1̂ ≔ τdef] DEFINED : Assign-Assign, the back-edge into part 1
       over the merged context Ξ ++ Θ0' with both sides substituted by
       [τdef/α1̂].  The competing solution strips its (α1,τα1)-entry
       ([a_inc_mid_strip_flex_def]); the substituted subject/input images
       are ≡ˢ to the node's ([msubst_pskl_subst] + the pointwise-≡ᵗ
       transport over an artificial source), so the sub-call's join is
       the REFLEXIVITY on the monotype κα̂ and both ∅-refinements follow
       by the mono bridges.  V is exactly constant ([Vpskl_backedge]);
       n drops by one (design doc §5.4, A3). *)
    assert (Huqf : uniq (Ξ ++ (α1 ~ abind_flex_mono_def τdef) ++ Θ0'))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfM : a_wf_aenv (Ξ ++ (α1 ~ abind_flex_mono_def τdef) ++ Θ0'))
      by exact Hwf.
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
      by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
    assert (Hwf0 : a_wf_aenv Θ0') by (eapply a_wf_aenv_app_r; exact Hwf').
    assert (Hmidwf : a_wf_aenv ((α1 ~ abind_flex_mono_def τdef) ++ Θ0'))
      by (eapply a_wf_aenv_app_r; exact HwfM).
    assert (Hwfτd : a_wf_ptyp Θ0' τdef) by (inversion Hmidwf; assumption).
    assert (Hmτd : mono_ptyp τdef) by (inversion Hmidwf; assumption).
    assert (Hγd : α1 `notin` dom Θ0') by (inversion Hmidwf; assumption).
    (* strip the defined mid off the competing increment *)
    destruct (a_inc_mid_strip_flex_def α1 τdef Θ0' Hdecl Hinc)
      as [κa [τα1 [κb [Heqκ [Hdκa [Hincb [Hincab [Hwfτα1 [Hmτα1 Heqτα1]]]]]]]]].
    assert (Hα1κa : α1 `notin` dom κa)
      by (rewrite Hdκa; clear - Huqf; simpl_env in Huqf; solve_uniq).
    assert (Hfτd : ftvar_in_ptyp τdef [<=] dom Θ0')
      by (apply a_wf_ptyp_ftv_dom; exact Hwfτd).
    assert (Hα1τd : α1 `notin` ftvar_in_ptyp τdef)
      by (clear - Hfτd Hγd; fsetdec).
    assert (Hagτd : msubst_ptyp (κa ++ κb) τdef = msubst_ptyp κb τdef).
    { apply msubst_ptyp_agree. intros α0 Hα0.
      apply msubst_lookup_app_notin.
      rewrite Hdκa.
      assert (HXd : α0 `in` dom Θ0') by (clear - Hfτd Hα0; fsetdec).
      clear - Huqf HXd. simpl_env in Huqf. solve_uniq. }
    assert (Heqτα1' : Θ ⊢ τα1 ≡ᵗ (msubst_ptyp (κa ++ κb) τdef))
      by (rewrite Hagτd; exact Heqτα1).
    assert (Hlcκ : msubst_lc (κa ++ κb))
      by (eapply a_inc_msubst_lc; exact Hincab).
    assert (Hlcm1 : lc_ptyp (msubst_ptyp (κa ++ κb) τdef))
      by (apply msubst_ptyp_lc_lc;
          [ exact Hlcκ | eapply a_wf_ptyp_lc; exact Hwfτd ]).
    (* the pointwise-≡ᵗ transport over the artificial source *)
    assert (HwfArt : a_wf_aenv
              ((α1 ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0')).
    { apply a_wf_aenv__flex_def.
      - clear - Huqf. simpl_env in Huqf. rewrite dom_app. solve_uniq.
      - eapply a_wf_ptyp_weaken;
          [ intros x b Hb; apply binds_app_3; exact Hb | exact Hwfτd ].
      - exact Hmτd.
      - exact Hwf'. }
    assert (Hlcc1 : msubst_lc
              ((α1, msubst_ptyp (κa ++ κb) τdef) :: κa ++ κb)).
    { intros α0. simpl.
      destruct_if; [ exact Hlcm1 | apply Hlcκ ]. }
    assert (Hlcc2 : msubst_lc ((α1, τα1) :: κa ++ κb)).
    { intros α0. simpl.
      destruct_if;
        [ apply mono_ptyp_lc; exact Hmτα1 | apply Hlcκ ]. }
    assert (Hartsub : forall β2,
              a_scope_pskl ((α1 ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0') β2 ->
              Θ ⊢ (msubst_pskl
                     ((α1, msubst_ptyp (κa ++ κb) τdef) :: κa ++ κb) β2)
                ≡ˢ (msubst_pskl ((α1, τα1) :: κa ++ κb) β2)).
    { intros β2 HwfW.
      eapply a_inc_equiv_msubst_pskl;
        [ exact HwfW | | exact HwfArt | exact Hlcc1 | exact Hlcc2 ].
      apply a_inc_equiv__flex_def.
      - apply a_inc_equiv_refl. exact Hincab.
      - apply a_tyequiv__sym. exact Heqτα1'.
      - apply a_tyequiv__refl. exact Hlcm1. }
    (* the reorder agreement : κ = (α1,τα1) :: (κa ++ κb) pointwise *)
    assert (Hreo : forall (β2 : pskl),
              msubst_pskl κ β2 = msubst_pskl ((α1, τα1) :: κa ++ κb) β2).
    { intro β2. apply msubst_pskl_agree. intros α0 Hα0.
      rewrite Heqκ. destruct (α0 == α1) as [-> | Hne].
      - rewrite msubst_lookup_app_notin by exact Hα1κa.
        rewrite msubst_lookup_cons_eq.
        rewrite msubst_lookup_cons_eq. reflexivity.
      - rewrite msubst_lookup_mid_drop by exact Hne.
        rewrite msubst_lookup_cons_neq by exact Hne. reflexivity. }
    (* wf of the substituted pieces at the stripped context *)
    assert (HbγM : binds α1 (abind_flex_mono_def τdef)
              (Ξ ++ (α1 ~ abind_flex_mono_def τdef) ++ Θ0'))
      by (apply binds_app_3; left; reflexivity).
    assert (Hsubup : forall (β2 : pskl),
              ftvar_in_pskl
                (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 β2)
              [<=] ftvar_in_ptyp τdef `union`
                   remove α1 (ftvar_in_pskl β2)).
    { intro β2.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    β2 (ptyp_to_pskl τdef) α1) as Hup.
      pose proof (ftvar_in_ptyp_to_pskl τdef) as Hfe.
      clear - Hup Hfe. fsetdec. }
    assert (HwfP0s : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 P)).
    { eapply a_wf_pskl_strip_mid.
      - eapply a_wf_pskl_mono_subst;
          [ exact HwfP | exact HwfM | exact HbγM | exact Hmτd ].
      - pose proof (Hsubup P). clear - H Hα1τd. fsetdec. }
    assert (HwfSα : (Ξ ++ (α1 ~ abind_flex_mono_def τdef) ++ Θ0')
              ⨟ empty ⊢ₚₛᵃ (pskl_var_f α)).
    { apply a_wf_pskl__var. right.
      destruct Hfα as [Hb | [τ0 Hb]];
        [ right; left | right; right; exists τ0 ];
        unfold binds in *; apply in_or_app; right; exact Hb. }
    assert (HwfSs : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 (pskl_var_f α))).
    { eapply a_wf_pskl_strip_mid.
      - eapply a_wf_pskl_mono_subst;
          [ exact HwfSα | exact HwfM | exact HbγM | exact Hmτd ].
      - pose proof (Hsubup (pskl_var_f α)). simpl in H.
        clear - H Hα1τd. fsetdec. }
    (* wf of the pieces as a_scope_pskl over the artificial source *)
    assert (HwfPart : a_scope_pskl
              ((α1 ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0') P).
    { eapply a_scope_pskl_weaken;
        [ | eapply a_wf_pskl_to_a_scope_pskl;
            [ exact HwfP | intros x b Hb; exact Hb
            | intros β Hβ; exfalso; clear - Hβ; fsetdec ] ].
      intros x b Hb. unfold binds in *.
      apply in_app_or in Hb. apply in_or_app.
      destruct Hb as [Hb | Hb];
        [ right; apply in_or_app; left; exact Hb | ].
      destruct Hb as [Hb | Hb];
        [ left; left; exact Hb
        | right; apply in_or_app; right; exact Hb ]. }
    assert (HwfVart : a_scope_pskl
              ((α1 ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0')
              (pskl_var_f α)).
    { apply a_scope_pskl__var.
      destruct Hfα as [Hb | [τ0 Hb]].
      - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
          [ discriminate | ].
        right; left. apply binds_cons_3. apply binds_app_3. exact Hb'.
      - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'].
        + inversion He2; subst.
          right; right. eexists. unfold binds. left. reflexivity.
        + right; right. exists τ0.
          apply binds_cons_3. apply binds_app_3. exact Hb'. }
    (* the two ≡ˢ facts (subject and input) *)
    assert (HeqP : Θ ⊢ (msubst_pskl (κa ++ κb)
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 P))
              ≡ˢ (msubst_pskl κ P)).
    { rewrite msubst_pskl_subst. rewrite (Hreo P).
      apply Hartsub. exact HwfPart. }
    assert (HeqS : Θ ⊢ (msubst_pskl (κa ++ κb)
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 (pskl_var_f α)))
              ≡ˢ (msubst_pskl κ (pskl_var_f α))).
    { rewrite msubst_pskl_subst. rewrite (Hreo (pskl_var_f α)).
      apply Hartsub. exact HwfVart. }
    (* the sub-call's competing data : the monotype κα̂ *)
    assert (HbtαM : a_binds_tvar α
              (Ξ ++ (α1 ~ abind_flex_mono_def τdef) ++ Θ0')).
    { destruct Hfα as [Hb | [τ0 Hb]];
        [ right; left | right; right; exists τ0 ];
        unfold binds in *; apply in_or_app; right; exact Hb. }
    assert (HwfC : a_wf_ptyp Θ (msubst_lookup κ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact HbtαM ]).
    assert (HmC : mono_ptyp (msubst_lookup κ α))
      by (eapply a_inc_lookup_mono; exact Hinc).
    assert (HvisC : forall β, β `in` ftvar_in_ptyp (msubst_lookup κ α) ->
              a_binds_tvar β Θ)
      by (intros β Hβ; eapply a_wf_ptyp_ftv_tvarish;
          [ exact HwfC | exact Hβ ]).
    (* sub-join : reflexivity on κα̂, transported to the subject image *)
    assert (Hjrefl : empty ⨟ Θ ⊢ₛᵃ
              (pskl_to_uskl (msubst_pskl κ (pskl_var_f α)))
              ∼ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))).
    { cbn [msubst_pskl].
      rewrite pskl_to_uskl_ptyp.
      eapply ad_pat_consis_psi_cong;
        [ apply consis_mono_refl; [ exact HmC | exact HvisC ]
        | clear; fsetdec ]. }
    destruct (skl_tyequiv_consis_transport HeqS Hwfth
                (fun x b Hb => Hb)) as [_ Hjback].
    pose proof (Hjback _ _ Hjrefl) as Hjsub.
    (* sub-refinements : both from the node's join via the mono bridges *)
    assert (Hrssub : ad_refine_syn_f empty Θ empty
              (pskl_to_bskl_inh (msubst_pskl (κa ++ κb)
                 (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 P)))
              (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))).
    { destruct (skl_tyequiv_refine_syn_f_transport HeqP Hwfth
                  (fun x b Hb => Hb)) as [_ Hback].
      apply Hback.
      replace (msubst_pskl κ P)
        with (uskl_to_pskl (pskl_to_uskl (msubst_pskl κ P)))
        by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      eapply ad_pat_consis_refine_syn_f_mono;
        [ exact Hjoin | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmC
        | clear; fsetdec
        | intros β τ Hb; clear; fsetdec ]. }
    assert (Hrpsub : ad_refine_pskl_f empty Θ empty
              (msubst_pskl (κa ++ κb)
                 (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 (pskl_var_f α)))
              (bskl_to_pskl (pskl_to_bskl_syn
                 (ptyp_to_pskl (msubst_lookup κ α))))).
    { destruct (skl_tyequiv_refine_pskl_f_transport HeqS Hwfth
                  (fun x b Hb => Hb)) as [_ Hback].
      apply Hback.
      replace (msubst_pskl κ (pskl_var_f α))
        with (uskl_to_pskl (pskl_to_uskl (msubst_pskl κ (pskl_var_f α))))
        by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      eapply ad_pat_consis_refine_pskl_f_mono;
        [ exact Hjrefl | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmC
        | clear; fsetdec
        | intros β τ Hb; clear; fsetdec ]. }
    (* the measure : V exactly constant, n drops by one *)
    assert (Hlt : mu_lt
        (mu_consis Θ (κa ++ κb)
           (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 P)
           (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 (pskl_var_f α))
           (Ξ ++ Θ0'))
        (mu_assign Θ κ α P Ξ ((α1, abind_flex_mono_def τdef) :: Θ0'))).
    { unfold mu_consis, mu_assign. apply mu_lt_intro. right. split.
      - unfold V_consis, V_assign.
        erewrite Vpskl_backedge; [ | exact Hwfth | exact Heqτα1' ].
        erewrite Vpskl_backedge; [ | exact Hwfth | exact Heqτα1' ].
        unfold Vpskl, Vvar.
        rewrite <- !Hreo.
        cbn [msubst_pskl].
        rewrite msubst_pskl_ptyp_to_pskl.
        rewrite size_ptyp_to_pskl. lia.
      - left. rewrite length_app. simpl. lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH (add α1 N) empty empty (Ξ ++ Θ0')
                (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 P)
                (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 (pskl_var_f α))
                (κa ++ κb) Θ empty
                (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))
                eq_refl Hwf' HwfP0s HwfSs
                ltac:(intros α0 Hα0; exfalso; clear - Hα0; fsetdec)
                ltac:(intros β τ Hb; clear; fsetdec)
                ltac:(intros Θa β b Θb Heqx Hne; clear; fsetdec)
                Hincab Hwfth
                ltac:(intros β τ Hb; clear; fsetdec)
                ltac:(reflexivity)
                Hjsub Hrssub Hrpsub)
      as [Q' [Θ1' [Hc [Hnew Hopt']]]].
    exists ((α1 ~ abind_flex_mono_def τdef) ++ Θ1'). split.
    { eapply a_assign__assign; [ exact Hfα | | exact Hc ].
      (* the walked definition is in the relayed avoid set [add α1 N] and
         fresh for the merged input, so it misses the output *)
      eapply avoid_head_miss;
        [ exact Hnew
        | pose proof (a_wf_aenv_uniq Hwf) as Huq0; clear - Huq0;
          simpl_env in Huq0; solve_uniq ]. }
    split; [ eapply avoid_relay_cons_mid; exact Hnew | ].
    (* ---- optimality ---- *)
    intros κ1 Hid Hinc1.
    destruct (a_inc_mid_strip_flex_def α1 τdef Θ0' Hdecl Hinc1)
      as [κ1a [τ1γ [κ1b [Heqκ1 [Hdκ1a [Hinc1b [Hinc1ab _]]]]]]].
    rewrite Heqκ1 in Hid.
    apply Forall_app in Hid as [Hida Hidtail].
    pose proof (Forall_inv Hidtail) as Heγ1.
    pose proof (Forall_inv_tail Hidtail) as Hidb.
    unfold is_id_entry in Heγ1; simpl in Heγ1; subst τ1γ.
    assert (Hidab : is_id_msubst (κ1a ++ κ1b))
      by (apply Forall_app; split; assumption).
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ Hc Hwf' HwfP0s HwfSs
                ltac:(intros α0 Hα0; exfalso; clear - Hα0; fsetdec)
                ltac:(intros β τ Hb; clear; fsetdec)
                ltac:(intros Θa β b Θb Heqx Hne; clear; fsetdec))
      as [Hle1 [HwfΘ1' _]].
    destruct Hle1 as [[w [Hidw Hincw]] _].
    assert (Hweq : w = κ1a ++ κ1b)
      by (eapply is_id_inc_unique;
          [ exact Hincw | exact Hidw | exact Hinc1ab | exact Hidab ]).
    subst w.
    destruct (Hopt' (κ1a ++ κ1b) Hidab Hincw)
      as [ζ' [Hζ' [Hie' Hprec']]].
    (* the final ζ re-conses the dropped (α1, τα1) entry *)
    assert (Hα1κ1a : α1 `notin` dom κ1a)
      by (rewrite Hdκ1a; clear - Huqf; simpl_env in Huqf; solve_uniq).
    assert (Hα1κ1b : α1 `notin` dom κ1b)
      by (pose proof (a_inc_dom_sub Hinc1b) as Hs; clear - Hs Hγd; fsetdec).
    (* τα1 ≡ᵗ msubst ζ' τdef *)
    assert (Hwfτd' : a_wf_ptyp (Ξ ++ Θ0') τdef)
      by (eapply a_wf_ptyp_weaken;
          [ intros x b Hb; apply binds_app_3; exact Hb | exact Hwfτd ]).
    assert (Hlc2' : msubst_lc (msubst_compose ζ' (κ1a ++ κ1b))).
    { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ' | ].
      intros a t Hin. eapply is_id_msubst_values_lc;
        [ exact Hidab | exact Hin ]. }
    assert (Heqζτd : Θ ⊢ (msubst_ptyp (κa ++ κb) τdef)
                       ≡ᵗ (msubst_ptyp ζ' τdef)).
    { pose proof (a_inc_equiv_msubst_ptyp Hwfτd' Hie' Hwf' Hlcκ Hlc2')
        as Hmid.
      rewrite (msubst_compose_id_ptyp Hwf' HwfΘ1' Hidab Hincw Hζ'
                 Hwfτd') in Hmid.
      exact Hmid. }
    exists ((α1, τα1) :: ζ'). split.
    + apply a_inc__flex_def;
        [ exact Hζ' | exact Hwfτα1 | exact Hmτα1 | ].
      eapply a_tyequiv__trans; [ exact Heqτα1' | exact Heqζτd ].
    + (* factoring : mid-insert the matching defined pair *)
      assert (Heqc : msubst_compose ((α1, τα1) :: ζ')
                       (κ1a ++ (α1, ptyp_var_f α1) :: κ1b)
                   = msubst_compose ζ' κ1a
                     ++ (α1, τα1) :: msubst_compose ζ' κ1b).
      { rewrite msubst_compose_app. f_equal.
        - apply (msubst_compose_cons_l_id τα1 ζ' Hida Hα1κ1a).
        - change (msubst_compose ((α1, τα1) :: ζ')
                    ((α1, ptyp_var_f α1) :: κ1b))
            with ((α1, msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
                  :: msubst_compose ((α1, τα1) :: ζ') κ1b).
          rewrite (msubst_compose_cons_l_id τα1 ζ' Hidb Hα1κ1b).
          change (msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
            with (msubst_lookup ((α1, τα1) :: ζ') α1).
          rewrite msubst_lookup_cons_eq. reflexivity. }
      rewrite Heqκ1, Heqκ, Heqc.
      apply a_inc_equiv_mid_insert_flex_def;
        [ exact Hdecl
        | apply a_wf_aenv_uniq; exact Hwf'
        | exact Hdκa
        | rewrite dom_msubst_compose; exact Hdκ1a
        | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτα1
        | exact Heqτα1
        | ].
      rewrite <- msubst_compose_app. exact Hie'.
Qed.

(** Part 1 of the paper's proof (:2561-3167): consistency.  The special
    cases are peeled first (:2566-2580) — [P] or [P0] flexible → parts 2/3
    ([t] breaks the tie); [P0 = ◇] → GhostR (axiom); [P0 = ∀◇.P0'] with [P]
    guarded → UnivGhostR ([V] decreases on the input side) — and the main
    dispatch is on the last rule of the declarative join derivation, each
    structural sub-node at strictly smaller [V]. *)
(** Decidability of "is a hatted variable of Θ" (the layer-0 dispatch). *)
Lemma a_flex_tvar_dec : forall Θ (β1 : atom),
  a_flex_tvar Θ β1 \/ ~ a_flex_tvar Θ β1.
Proof.
  induction Θ as [ | [x b] Θ' IHΘ ]; intros β1.
  - right. intros [Hb | [τ Hb]]; inversion Hb.
  - destruct (IHΘ β1) as [Hyes | Hno].
    { left. destruct Hyes as [Hb | [τ Hb]];
        [ left | right; exists τ ]; unfold binds in *; simpl; right; exact Hb. }
    destruct b as [ | A | Q | | τd ];
      try (destruct (β1 == x) as [-> | Hne];
           [ | right; intros [Hb | [τ Hb]];
               apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
               solve [ exfalso; auto | discriminate Hbe
                     | apply Hno; solve [ left; exact Hb
                                        | right; exists τ; exact Hb ] ] ]).
    + (* x ~ tvar, β1 = x *)
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    + (* x ~ var_typ, β1 = x *)
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    + (* x ~ var_skl, β1 = x *)
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    + (* x ~ flex, β1 = x *)
      left. left. left. reflexivity.
    + (* x ~ flex_def τd, β1 = x *)
      left. right. exists τd. left. reflexivity.
Qed.

(** Layer-0 shape dispatch: a well-formed skeleton is a hatted variable of
    [Θ] or non-flex. *)
Lemma a_flex_shape_dec : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  (exists β, P = pskl_var_f β /\ a_flex_tvar Θ β) \/ a_non_flex Θ P.
Proof.
  intros Θ Δ P HwfP.
  pose proof (a_wf_pskl_lc HwfP) as Hlc.
  destruct P as [ | n | β1 | Pa Pb | Pb | | Pt ];
    try (right; split; [ exact Hlc | intro Hfl; solve [ inversion Hfl ] ]).
  destruct (a_flex_tvar_dec Θ β1) as [Hf | Hnf'].
  - left. exists β1. split; [ reflexivity | exact Hf ].
  - right. split; [ exact Hlc | ].
    intro Hfl. apply Hnf'.
    inversion Hfl; subst; [ left | right; eexists ]; eassumption.
Qed.

(** Part 1's MAIN DISPATCH (paper :2582-3167), by induction on the last rule
    of the declarative join derivation, ASSUMING the layer-0 special cases
    (flexible subject / flexible input / P0 = ◇ / P0 = ∀◇ with P guarded)
    have been peeled by [consis_complete_step] below.  The induction (rather
    than a case analysis) is needed ONLY for the target-side definition
    unfolds [flex_r] — those keep the measure constant but shrink the join.
    All structural sub-nodes recurse through the measure hypothesis [IH]. *)
Lemma consis_complete_core : forall Ψ Θ R' Qb,
  Ψ ⨟ Θ ⊢ₛᵃ R' ∼ Qb ->
  forall (N : atoms) Δ1 Δ2 Θ0 P0 P κ,
    (forall m', mu_lt m' (mu_consis Θ κ P0 P Θ0) -> complete_at m') ->
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    κ ∷ Θ0 ⊑ Θ ->
    a_wf_aenv Θ ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    R' = pskl_to_uskl (msubst_pskl κ P) ->
    a_non_flex Θ0 P ->
    a_non_flex Θ0 P0 ->
    P0 <> pskl_hole ->
    (forall P0', P0 = pskl_tophole P0' -> ~ guarded_pskl P) ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl κ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl κ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall γ, γ `in` dom Θ1 -> γ `in` dom Θ0 \/ γ `notin` N) /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           ad_precise_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb)).
Proof.
  intros Ψ Θ R' Qb Hj.
  induction Hj; intros N Δ1 Δ2 Θ0 PP0 PP κ
    IH Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth
    HΨ HeqS HnfP HnfP0 HneP0hole Hnthg Hrs Hrp.
  (* ------------------------------------------------------------- unit *)
  - (* SUBJECT: PP = unit (var subjects are rigid, hence not unit). *)
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    2:{ (* var β1 : rigid, its image is β1 itself *)
      exfalso.
      assert (Hbtδ : binds β1 abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ : β1 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
      simpl in HeqS. discriminate. }
    (* INPUT: PP0 = unit. *)
    destruct PP0 as [ | n0 | β10 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    2:{ inversion Hrs. }
    2:{ (* var β10 : rigid; a rigid variable does not refine to unit *)
      exfalso.
      assert (Hbtδ0 : binds β10 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ0 : β10 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ : binds β10 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds β10 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
            as Hcon; discriminate
      end. }
    2:{ inversion Hrs. }
    2:{ inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ exfalso; apply (Hnthg Pt0 eq_refl); apply guarded_pskl__unit. }
    (* both unit: the axiom node *)
    exists pskl_unit, Θ0. split.
    { apply a_consis__unit. }
    split; [ intros γ Hγ; left; exact Hγ | ].
    intros κ1 Hid Hinc1. exists κ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    cbn [pskl_to_bskl_syn msubst_bskl bskl_to_pskl].
    unfold ad_precise_f.
    apply ad_refine_syn_f_of_plain_no_hole; [ | simpl; exact I ].
    apply consis_precise_mono_join with (A := ptyp_unit) (Qb := bskl_unit);
      [ exact Hwfth | apply mono_ptyp__unit
      | intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec
      | apply ad_pat_consis__unit; clear; fsetdec ].
  (* -------------------------------------------------------------- var *)
  - (* SUBJECT: PP = var β1 with β1 RIGID; forces α = β1, PP0 = var β1. *)
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    assert (Hbtδ : binds β1 abind_tvar Θ0).
    { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
      destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
        [ exfalso; clear - HΔ; fsetdec
        | exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          apply a_flex__var; exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          eapply a_flex__var_def; exact Hb ]. }
    assert (Hβ1κ : β1 `notin` dom κ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
    simpl in HeqS. inversion HeqS; subst α. clear HeqS.
    assert (HbtΘ : binds β1 abind_tvar Θ)
      by (eapply a_inc_binds_tvar; eauto).
    (* INPUT: PP0 = var β1. *)
    destruct PP0 as [ | n0 | β10 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso.
        inversion Hrs; subst.
        match goal with
        | Hbr : binds β1 (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    1:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds β1 (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds β1 (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds β1 (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ exfalso; apply (Hnthg Pt0 eq_refl); apply guarded_pskl__var. }
    (* var β10 rigid; the refinement forces β10 = β1 *)
    assert (Hbtδ0 : binds β10 abind_tvar Θ0).
    { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
      destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
        [ exfalso; clear - HΔ; fsetdec
        | exact Hb
        | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
          apply a_flex__var; exact Hb
        | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
          eapply a_flex__var_def; exact Hb ]. }
    assert (Hβ1κ0 : β10 `notin` dom κ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin κ Hβ1κ0) in Hrs.
    simpl in Hrs.
    assert (Heqδ : β10 = β1).
    { inversion Hrs; subst.
      - reflexivity.
      - exfalso.
        match goal with
        | Hbr : binds β10 (abind_flex_mono_def _) Θ |- _ =>
            assert (HbtΘ0' : binds β10 abind_tvar Θ)
              by (eapply a_inc_binds_tvar; eauto);
            pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                          (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
        end.
      - exfalso.
        match goal with
        | Hbr : binds β1 (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr
                          (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
        end. }
    subst β10.
    exists (pskl_var_f β1), Θ0. split.
    { apply a_consis__rigid. exact Hbtδ. }
    split; [ intros γ Hγ; left; exact Hγ | ].
    intros κ1 Hid Hinc1. exists κ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    unfold ad_precise_f.
    cbn [pskl_to_bskl_syn msubst_bskl].
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    rewrite (msubst_lookup_notin κ Hβ1κ).
    apply ad_refine_syn_f_of_plain_no_hole;
      [ | apply pskl_to_bskl_inh_no_hole, ptyp_to_pskl_no_hole ].
    apply consis_precise_mono_join with (A := ptyp_var_f β1)
                                        (Qb := bskl_var_f β1);
      [ exact Hwfth | apply mono_ptyp__var
      | intros α0 Hα0; simpl in Hα0;
        assert (Hα0δ : α0 = β1) by (clear - Hα0; fsetdec); subst α0;
        left; exact HbtΘ
      | apply ad_pat_consis__var; [ clear; fsetdec | left; exact HbtΘ ] ].
  (* ------------------------------------------------------------ arrow *)
  - (* C-Arrow (paper :2691-2775): two structural sub-nodes at strictly
       smaller V.  The second runs at the first's OUTPUT Θ1 with metasubst
       ζ1 (the first's factoring at the soundness ⊴ id-witness); its
       premises transport from κ to ζ1 by the ≡ˢ-transport layer; the two
       factorings compose by [a_inc_equiv_glue]; the first component's
       precision transports from ζ1 to ζ2 the same way. *)
    match goal with
    | Hpm : ?x ⨟ _ ⊢ₛᵃ R1 ∼ _ |- _ => rename Hpm into Hj1
    end.
    match goal with
    | Hpm : ?x ⨟ _ ⊢ₛᵃ R2 ∼ _ |- _ => rename Hpm into Hj2
    end.
    match goal with
    | Hpe : Ψ [=] union _ _ |- _ => rename Hpe into HΨu
    end.
    assert (HΨ1e : Ψ1 [=] empty) by (clear - HΨ HΨu; fsetdec).
    assert (HΨ2e : Ψ2 [=] empty) by (clear - HΨ HΨu; fsetdec).
    (* SUBJECT: PP = arrow PPa PPb. *)
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var β1 : rigid, its image is β1 itself *)
      exfalso.
      assert (Hbtδ : binds β1 abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ : β1 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R1 R2. clear HeqS.
    assert (HwfPPa : Θ0 ⨟ empty ⊢ₚₛᵃ PPa) by (inversion HwfP; assumption).
    assert (HwfPPb : Θ0 ⨟ empty ⊢ₚₛᵃ PPb) by (inversion HwfP; assumption).
    assert (HlcP : lc_pskl (pskl_arrow PPa PPb))
      by (eapply a_wf_pskl_lc; exact HwfP).
    (* INPUT: PP0 = arrow P0a P0b. *)
    destruct PP0 as [ | n0 | β10 | P0a P0b | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ (* var β10 : rigid; a rigid variable does not refine to an arrow *)
      exfalso.
      assert (Hbtδ0 : binds β10 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ0 : β10 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds β10 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds β10 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr (a_wf_aenv_uniq Hwfth))
            as Hcon; discriminate
      end. }
    2:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ (* ∀◇ input against a GUARDED (arrow) subject was peeled in layer 0d *)
      exfalso. apply (Hnthg Pt0 eq_refl).
      inversion HlcP; subst.
      apply guarded_pskl__arrow; assumption. }
    (* both arrows: invert the two refinements *)
    assert (HwfP0a : Θ0 ⨟ empty ⊢ₚₛᵃ P0a) by (inversion HwfP0; assumption).
    assert (HwfP0b : Θ0 ⨟ empty ⊢ₚₛᵃ P0b) by (inversion HwfP0; assumption).
    inversion Hrs; subst.
    match goal with
    | Ha : ad_refine_syn_f Δ1 Θ Δ1
             (pskl_to_bskl_inh (msubst_pskl κ P0a)) Q1,
      Hb : ad_refine_syn_f Δ1 Θ Δ1
             (pskl_to_bskl_inh (msubst_pskl κ P0b)) Q2 |- _ =>
        rename Ha into Hrs1; rename Hb into Hrs2
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_arrow (msubst_pskl κ PPa) (msubst_pskl κ PPb))
              (pskl_arrow (bskl_to_pskl Q1) (bskl_to_pskl Q2))) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Ha : ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl κ PPa) (bskl_to_pskl Q1),
      Hb : ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl κ PPb) (bskl_to_pskl Q2)
      |- _ =>
        rename Ha into Hrp1; rename Hb into Hrp2
    end.
    (* ---- first component, at (Θ0, κ); V strictly drops ---- *)
    assert (Hlt1 : mu_lt (mu_consis Θ κ P0a PPa Θ0)
                         (mu_consis Θ κ (pskl_arrow P0a P0b)
                                        (pskl_arrow PPa PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      pose proof (Vpskl_arrow_lt1 Θ κ PPa PPb).
      pose proof (Vpskl_arrow_lt1 Θ κ P0a P0b). lia. }
    destruct (IH _ Hlt1) as [HcIH1 _].
    destruct (HcIH1 N Δ1 Δ2 Θ0 P0a PPa κ Θ Ψ1 Q1 eq_refl Hwf0 HwfP0a HwfPPa
                    Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ1e Hj1 Hrs1 Hrp1)
      as [PA1 [Θ1 [Hc1 [Hnew1 Hopt1]]]].
    (* the first node's soundness: id-witness, wf, Δ-invariants *)
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ Hc1
                Hwf0 HwfP0a HwfPPa Hrig Hnfd0 Hfaf)
      as [Hle1 [Hwf1 [Hdom1 [Hinv1 [Hsol1 _]]]]].
    destruct Hle1 as [[w1 [Hidw1 Hincw1]] Hdefs1].
    destruct (Hopt1 w1 Hidw1 Hincw1) as [ζ1 [Hζ1 [Hie1 Hprec1]]].
    (* conjunct 5's coverage, in its OUTPUT-relative form: the protected
       variables are RIGID in Θ0, so they are covered outright *)
    assert (HΔdom : (Δ1 `union` Δ2) ∩ dom Θ1 [<=] dom Θ0).
    { intros α0 Hα0.
      assert (Hα0' : α0 `in` (Δ1 `union` Δ2)) by (clear - Hα0; fsetdec).
      pose proof (Hrig α0 Hα0') as Hb. apply binds_In in Hb. exact Hb. }
    destruct (Hinv1 (Δ1 `union` Δ2) Hnfd0 Hfaf HΔdom
                ltac:(intros α0 Hα0 HnX; exfalso; pose proof (Hrig α0 Hα0) as Hb;
                      apply binds_In in Hb; exact (HnX Hb)))
      as [Hnfd1 [Hfaf1 _]].
    assert (HrigΘ1 : forall α0, α0 `in` (Δ1 `union` Δ2) ->
              binds α0 abind_tvar Θ1)
      by (intros α0 Hα0; eapply a_inc_binds_tvar;
          [ exact Hincw1 | apply Hrig; exact Hα0 ]).
    assert (HwfP0b1 : Θ1 ⨟ empty ⊢ₚₛᵃ P0b).
    { eapply a_wf_pskl_isub; [ exact HwfP0b | ].
      split; [ exists w1; split; assumption | exact Hdefs1 ]. }
    assert (HwfPPb1 : Θ1 ⨟ empty ⊢ₚₛᵃ PPb).
    { eapply a_wf_pskl_isub; [ exact HwfPPb | ].
      split; [ exists w1; split; assumption | exact Hdefs1 ]. }
    (* ---- transport the second component's premises from κ to ζ1 ---- *)
    assert (HawfPPb : a_scope_pskl Θ0 PPb).
    { eapply a_wf_pskl_to_a_scope_pskl;
        [ exact HwfPPb | intros x b Hb; exact Hb
        | intros β Hβ; exfalso; clear - Hβ; fsetdec ]. }
    assert (HawfP0b : a_scope_pskl Θ0 P0b).
    { eapply a_wf_pskl_to_a_scope_pskl;
        [ exact HwfP0b | intros x b Hb; exact Hb
        | intros β Hβ; exfalso; clear - Hβ; fsetdec ]. }
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hlcζ1 : msubst_lc ζ1) by (eapply a_inc_msubst_lc; exact Hζ1).
    assert (Hlcc1 : msubst_lc (msubst_compose ζ1 w1))
      by (apply msubst_lc_compose;
          [ exact Hlcζ1 | eapply is_id_msubst_values_lc; exact Hidw1 ]).
    assert (Heqb : Θ ⊢ (msubst_pskl κ PPb) ≡ˢ (msubst_pskl ζ1 PPb)).
    { replace (msubst_pskl ζ1 PPb)
        with (msubst_pskl (msubst_compose ζ1 w1) PPb)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf0 | exact Hwf1 | exact Hidw1 | exact Hincw1
            | exact Hζ1 | exact HawfPPb ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfPPb | exact Hie1 | exact Hwf0
        | exact Hlcκ | exact Hlcc1 ]. }
    assert (Heqb0 : Θ ⊢ (msubst_pskl κ P0b) ≡ˢ (msubst_pskl ζ1 P0b)).
    { replace (msubst_pskl ζ1 P0b)
        with (msubst_pskl (msubst_compose ζ1 w1) P0b)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf0 | exact Hwf1 | exact Hidw1 | exact Hincw1
            | exact Hζ1 | exact HawfP0b ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfP0b | exact Hie1 | exact Hwf0
        | exact Hlcκ | exact Hlcc1 ]. }
    destruct (skl_tyequiv_consis_transport Heqb Hwfth
                (fun x b Hb => Hb)) as [Hjt _].
    assert (Hj2' : Ψ2 ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl ζ1 PPb)) ∼ Q2)
      by (apply Hjt; exact Hj2).
    destruct (skl_tyequiv_refine_syn_f_transport Heqb0 Hwfth
                (fun x b Hb => Hb)) as [Hrst _].
    pose proof (Hrst _ _ _ Hrs2) as Hrs2'.
    destruct (skl_tyequiv_refine_pskl_f_transport Heqb Hwfth
                (fun x b Hb => Hb)) as [Hrpt _].
    pose proof (Hrpt _ _ _ Hrp2) as Hrp2'.
    (* ---- second component, at (Θ1, ζ1); V constant by M1 then drops --- *)
    assert (HVb : Vpskl Θ ζ1 PPb = Vpskl Θ κ PPb).
    { transitivity (Vpskl Θ (msubst_compose ζ1 w1) PPb).
      - unfold Vpskl.
        erewrite (msubst_compose_id_pskl (P := PPb));
          [ reflexivity | exact Hwf0 | exact Hwf1 | exact Hidw1
          | exact Hincw1 | exact Hζ1 | exact HawfPPb ].
      - symmetry.
        eapply Vpskl_inc_equiv;
          [ exact Hie1 | exact Hwf0 | exact Hwfth | exact HawfPPb ]. }
    assert (HVb0 : Vpskl Θ ζ1 P0b = Vpskl Θ κ P0b).
    { transitivity (Vpskl Θ (msubst_compose ζ1 w1) P0b).
      - unfold Vpskl.
        erewrite (msubst_compose_id_pskl (P := P0b));
          [ reflexivity | exact Hwf0 | exact Hwf1 | exact Hidw1
          | exact Hincw1 | exact Hζ1 | exact HawfP0b ].
      - symmetry.
        eapply Vpskl_inc_equiv;
          [ exact Hie1 | exact Hwf0 | exact Hwfth | exact HawfP0b ]. }
    assert (Hlt2 : mu_lt (mu_consis Θ ζ1 P0b PPb Θ1)
                         (mu_consis Θ κ (pskl_arrow P0a P0b)
                                        (pskl_arrow PPa PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite HVb. rewrite HVb0.
      pose proof (Vpskl_arrow_lt2 Θ κ PPa PPb).
      pose proof (Vpskl_arrow_lt2 Θ κ P0a P0b). lia. }
    destruct (IH _ Hlt2) as [HcIH2 _].
    destruct (HcIH2 N Δ1 Δ2 Θ1 P0b PPb ζ1 Θ Ψ2 Q2 eq_refl Hwf1 HwfP0b1
                    HwfPPb1 HrigΘ1 Hnfd1 Hfaf1 Hζ1 Hwfth Hnfdth HΨ2e
                    Hj2' Hrs2' Hrp2')
      as [PA2 [Θ2 [Hc2 [Hnew2 Hopt2]]]].
    (* ---- assemble the node ---- *)
    exists (pskl_arrow PA1 PA2), Θ2. split.
    { eapply a_consis__arrow; [ exact Hc1 | exact Hc2 ]. }
    split; [ eapply avoid_compose; [ exact Hnew1 | exact Hnew2 ] | ].
    intros κf Hidf Hincf.
    (* the second node's soundness id-witness *)
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ Hc2
                Hwf1 HwfP0b1 HwfPPb1 HrigΘ1 Hnfd1 Hfaf1)
      as [Hle2 [Hwf2 [Hdom2 [Hinv2 [Hsol2 _]]]]].
    destruct Hle2 as [[w2 [Hidw2 Hincw2]] Hdefs2].
    destruct (Hopt2 w2 Hidw2 Hincw2) as [ζ2 [Hζ2 [Hie2 Hprec2]]].
    (* the algorithm's composite id-witness IS w1 (uniqueness) *)
    assert (Heqw : w1 = κf) by (eapply is_id_inc_unique; eauto).
    subst κf.
    exists ζ2. split; [ exact Hζ2 | ]. split.
    { (* factoring composition *)
      eapply a_inc_equiv_glue with
        (Θmid := Θ1) (Θfin := Θ2) (κ1b := w2) (ζ1 := ζ1);
        [ exact Hwf0 | exact Hwf1 | exact Hwf2 | exact Hwfth
        | exact Hidw1 | exact Hidw2
        | (* dom w1 ⊆ dom w2 : Θ0's flexes stay flexible in Θ1 *)
          intros α Hα;
          pose proof (a_inc_dom_flex Hincw1 Hα) as Hfα0';
          eapply a_inc_flex_dom; [ exact Hincw2 | exact Hwf1 | ];
          eapply (proj2 (proj2 a_assign_unify_consis_flex_preserve));
            [ exact Hc1 | exact Hfα0' ]
        | exact Hincw1 | exact Hincw2 | exact Hζ1 | exact Hζ2
        | exact Hie1 | exact Hie2 ]. }
    (* ---- precision: componentwise, first component ζ1 → ζ2 ---- *)
    assert (HawfPA1 : a_scope_pskl Θ1 PA1).
    { destruct Hsol1 as [Qt1 [HeqQt1 [Hjoin1s _]]].
      rewrite <- HeqQt1.
      eapply ad_pat_consis_target_wf; exact Hjoin1s. }
    assert (Hlcζ2 : msubst_lc ζ2) by (eapply a_inc_msubst_lc; exact Hζ2).
    assert (Hlcc2 : msubst_lc (msubst_compose ζ2 w2))
      by (apply msubst_lc_compose;
          [ exact Hlcζ2 | eapply is_id_msubst_values_lc; exact Hidw2 ]).
    assert (Heqζ : Θ ⊢ (msubst_pskl ζ1 PA1) ≡ˢ (msubst_pskl ζ2 PA1)).
    { replace (msubst_pskl ζ2 PA1)
        with (msubst_pskl (msubst_compose ζ2 w2) PA1)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf1 | exact Hwf2 | exact Hidw2 | exact Hincw2
            | exact Hζ2 | exact HawfPA1 ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfPA1 | exact Hie2 | exact Hwf1
        | exact Hlcζ1 | exact Hlcc2 ]. }
    unfold ad_precise_f in Hprec1, Hprec2 |- *.
    rewrite !bskl_to_pskl_msubst_bskl in Hprec1, Hprec2.
    rewrite !bskl_to_pskl_pskl_to_bskl_syn in Hprec1, Hprec2.
    change (ad_refine_syn_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
      (bskl_arrow
         (pskl_to_bskl_inh
            (bskl_to_pskl (msubst_bskl ζ2 (pskl_to_bskl_syn PA1))))
         (pskl_to_bskl_inh
            (bskl_to_pskl (msubst_bskl ζ2 (pskl_to_bskl_syn PA2)))))
      (bskl_arrow (pskl_to_bskl_inh (bskl_to_pskl Q1))
                  (pskl_to_bskl_inh (bskl_to_pskl Q2)))).
    apply ad_refine_syn_f__arrow.
    + (* first component : transport the precision source ζ1 → ζ2 *)
      rewrite bskl_to_pskl_msubst_bskl.
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      destruct (skl_tyequiv_refine_syn_f_transport Heqζ Hwfth
                  (fun x b Hb => Hb)) as [Hpt _].
      apply Hpt. exact Hprec1.
    + (* second component : already at ζ2 *)
      rewrite bskl_to_pskl_msubst_bskl.
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      exact Hprec2.
  (* ------------------------------------------- forall_inh (impossible) *)
  - destruct (msubst_pskl κ PP); simpl in HeqS; discriminate.
  (* --------------------------------------------- forall_inh_untagged *)
  - (* C-ForallInh (paper :2777-2851): open with a fresh rigid α added to
       Θ0, Δ1, Δ2; the recursive call goes through the μ-IH at strictly
       smaller V ([Vpskl_open] + the binder strip); L8 shapes its output
       as [(α~tvar) ++ Θ1] and L9 renames the single instance to the
       cofinite premise of [a_consis__forall_inh]. *)
    match goal with
    | Hpm : forall α, α `notin` _ -> _ ⨟ _ ⊢ₛᵃ _ ∼ _ |- _ =>
        rename Hpm into Hjoin
    end.
    (* SUBJECT: PP = ∀ PPb. *)
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var β1 : rigid, its image is β1 itself *)
      exfalso.
      assert (Hbtδ : binds β1 abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ : β1 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.
    (* INPUT: PP0 = ∀ P0b. *)
    destruct PP0 as [ | n0 | β10 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ (* rigid input var never refines to an inherited ∀ *)
      exfalso.
      assert (Hbtδ0 : binds β10 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ0 : β10 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds β10 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds β10 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                        (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ (* ∀◇ input: its guarded body never refines to an inherited ∀ *)
      exfalso.
      assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
      assert (Hgκ0 : guarded_pskl (msubst_pskl κ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      inversion Hrs; subst.
      eapply ad_refine_syn_f_guarded_src_all_inh_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgκ0 ]. }
    (* both ∀ : invert the two refinements and the wf of the bodies *)
    inversion Hrs; subst.
    match goal with
    | Hn : forall α, α `notin` ?LA ->
             ad_refine_syn_f _ _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_all_syn (msubst_pskl κ PPb))
              (pskl_all_syn (bskl_to_pskl Q))) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Hn : forall α, α `notin` ?LB ->
             ad_refine_pskl_f _ _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb0 : exists Lw0, forall α, α `notin` Lw0 ->
              Θ0 ⨟ (add α empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl P0b (pskl_var_f α))).
    { inversion HwfP0; subst. eexists. eassumption. }
    destruct Hwfb0 as [Lw0 Hwfb0].
    assert (Hwfb : exists Lw, forall α, α `notin` Lw ->
              Θ0 ⨟ (add α empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl PPb (pskl_var_f α))).
    { inversion HwfP; subst. eexists. eassumption. }
    destruct Hwfb as [Lw Hwfb].
    (* the fresh rigid α *)
    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw0 `union` Lw
                        `union` dom Θ0 `union` ftvar_in_aenv Θ0
                        `union` dom Θ `union` dom κ
                        `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPb
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hακ : α `notin` dom κ) by (clear - Fr; fsetdec).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; fsetdec).
    (* the measure strictly drops *)
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) κ Pz
                            = Vpskl Θ κ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) κ
           (open_pskl_wrt_pskl P0b (pskl_var_f α))
           (open_pskl_wrt_pskl PPb (pskl_var_f α))
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ κ (pskl_all_syn P0b) (pskl_all_syn PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open P0b Hwfth Hlcκ Hακ HαΘ).
      rewrite (Vpskl_open PPb Hwfth Hlcκ Hακ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ κ P0b).
      pose proof (Vpskl_all_syn_lt Θ κ PPb). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    (* premises of the opened problem *)
    assert (Hwf0' : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ]).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (open_pskl_wrt_pskl P0b (pskl_var_f α))).
    { eapply a_wf_pskl_delta_to_tvar;
        [ apply Hwfb0; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl PPb (pskl_var_f α))).
    { eapply a_wf_pskl_delta_to_tvar;
        [ apply Hwfb; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (Hrig' : forall α2, α2 `in` (add α Δ1 `union` add α Δ2) ->
              binds α2 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α2 Hα2. destruct (α2 == α) as [-> | Hne];
        [ unfold binds; left; reflexivity
        | apply binds_cons_3; apply Hrig; clear - Hα2 Hne; fsetdec ]. }
    assert (Hnfd0' : no_flex_dep (add α Δ1 `union` add α Δ2)
                       ((α ~ abind_tvar) ++ Θ0)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwf0 | exact Hnfd0 | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hfaf' : flex_above_free (add α Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { eapply faf_cong;
        [ | eapply faf_open_tvar; [ exact Hfaf | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hinc' : κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑
                      ((α ~ abind_tvar) ++ Θ)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc).
      apply a_decls_suffix. apply a_decls__nil. }
    assert (Hwfth' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ exact HαΘ | exact Hwfth ]).
    assert (Hnfdth' : no_flex_dep (add α Δ1 `union` add α Δ2)
                        ((α ~ abind_tvar) ++ Θ)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwfth | exact Hnfdth | exact HαΘ ] ].
      clear. fsetdec. }
    assert (Hjα : Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ₛᵃ
              (pskl_to_uskl (msubst_pskl κ
                 (open_pskl_wrt_pskl PPb (pskl_var_f α))))
              ∼ (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { pose proof (Hjoin α ltac:(clear - Fr; fsetdec)) as Hj0.
      rewrite (msubst_pskl_open_lc PPb Hlcκ Hακ).
      rewrite pskl_to_uskl_open_var.
      exact Hj0. }
    assert (Hrsα : ad_refine_syn_f (add α Δ1) ((α ~ abind_tvar) ++ Θ)
              (add α Δ1)
              (pskl_to_bskl_inh (msubst_pskl κ
                 (open_pskl_wrt_pskl P0b (pskl_var_f α))))
              (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { rewrite (msubst_pskl_open_lc P0b Hlcκ Hακ).
      rewrite pskl_to_bskl_inh_open.
      eapply ad_refine_syn_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_syn_f_fextend_dom;
        [ apply Hrs1; clear - Fr; fsetdec | ].
      intros α1 Hα1. destruct (α1 == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hα1 Hne; fsetdec ]. }
    assert (Hrpα : ad_refine_pskl_f (add α Δ2) ((α ~ abind_tvar) ++ Θ)
              (add α Δ2)
              (msubst_pskl κ (open_pskl_wrt_pskl PPb (pskl_var_f α)))
              (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)))).
    { rewrite (msubst_pskl_open_lc PPb Hlcκ Hακ).
      rewrite bskl_to_pskl_open.
      eapply ad_refine_pskl_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_pskl_f_fextend_dom;
        [ apply Hrp1; clear - Fr; fsetdec | ].
      intros α1 Hα1. destruct (α1 == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hα1 Hne; fsetdec ]. }
    destruct (HcIH N (add α Δ1) (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
                (open_pskl_wrt_pskl P0b (pskl_var_f α))
                (open_pskl_wrt_pskl PPb (pskl_var_f α)) κ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα)
      as [P1 [Θ1' [Hc [Hnew Hopt']]]].
    (* L8 : the output re-attaches the rigid head *)
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.
    (* assemble the exists-fresh node at the run's OWN α *)
    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; fsetdec).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    { (* EXISTS-FRESH (campaign cluster 4): the run's OWN α is the
         rule's binder, so the node is one constructor application —
         no family to rebuild, hence no rename. *)
      apply a_consis__forall_inh with (α := α);
        [ clear - Fr; fsetdec | exact Hc ]. }
    (* the avoid set survives the truncation: [α] is the run's OWN binder,
       so it cannot occur in the tail the node hands back *)
    split.
    { eapply avoid_truncate_cons; [ exact Hnew | ].
      pose proof (auc_uniq_consis Hc Huq0) as Hu1. clear - Hu1. solve_uniq. }
    (* optimality *)
    intros κ1 Hid Hinc1.
    assert (Hinc1' : κ1 ∷ ((α ~ abind_tvar) ++ Θ0) ⊑
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc1).
      apply a_decls_suffix. apply a_decls__nil. }
    destruct (Hopt' κ1 Hid Hinc1') as [ζ [Hζ [Hie Hprec]]].
    exists ζ.
    (* strip the rigid head off the algorithm-side increments *)
    assert (Hζ' : ζ ∷ Θ1 ⊑ Θ).
    { destruct (a_inc_tvar_inv Hζ) as [Ξs [Θ2 [HeqT [Hsuf Hinc2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hinc2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    assert (Hie' : a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ).
    { destruct (a_inc_equiv_tvar_inv Hie) as [Ξs [Θ2 [HeqT [Hsuf Hie2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hie2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    split; [ exact Hζ' | ]. split; [ exact Hie' | ].
    (* precision : rebind the quantifier *)
    assert (Hlcζ : msubst_lc ζ) by (eapply a_inc_msubst_lc; exact Hζ').
    assert (Huq1' : uniq ((α ~ abind_tvar) ++ Θ1))
      by (exact (auc_uniq_consis Hc Huq0)).
    assert (HαΘ1 : α `notin` dom Θ1) by solve_uniq.
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Himg : forall α1 τ, In (α1, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros α1 τ Hin.
      pose proof (a_inc_images_ftv_dom Hζ' _ _ Hin) as Hsc.
      clear - Hsc HαΘ. fsetdec. }
    unfold ad_precise_f in Hprec |- *.
    rewrite bskl_to_pskl_msubst_bskl in Hprec |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec |- *.
    change (ad_refine_syn_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
      (bskl_all_inh (pskl_to_bskl_inh
         (msubst_pskl ζ (close_pskl_wrt_pskl α P1))))
      (bskl_all_inh (pskl_to_bskl_inh (bskl_to_pskl Q)))).
    apply ad_refine_syn_f__all with
      (L := singleton α `union` dom Θ `union` dom Θ1
            `union` Δ1 `union` Δ2
            `union` ftvar_in_bskl Q `union` ftvar_in_pskl P1).
    intros α0 Hα0.
    assert (Hα0ζ : α0 `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb Hα0; fsetdec. }
    rewrite <- !pskl_to_bskl_inh_open.
    rewrite <- (msubst_pskl_open_lc (close_pskl_wrt_pskl α P1) Hlcζ Hα0ζ).
    rewrite <- (subst_pskl_in_pskl_spec P1 (pskl_var_f α0) α).
    rewrite <- bskl_to_pskl_open.
    (* transport the α-instance: ctx-α to Δ, then rename α ↦ α0 *)
    pose proof (ad_refine_syn_f_ctx_to_delta Hprec nil Θ eq_refl
                  ltac:(clear; fsetdec)
                  (a_wf_aenv_uniq Hwfth')) as Hp1.
    simpl in Hp1.
    assert (HαF : α `in` (add α Δ1 `union` add α Δ2))
      by (clear; fsetdec).
    assert (Hdefsκ : forall β τ,
              binds β (abind_flex_mono_def τ) Θ ->
              α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; eassumption).
      clear - Hsc HαΘ. fsetdec. }
    pose proof (ad_refine_syn_f_rename α0 Hp1 HαF HαΘ Hdefsκ) as Hp2.
    rewrite !pskl_to_bskl_inh_subst_var in Hp2.
    rewrite (msubst_pskl_subst_var ζ P1 Hαζ Hα0ζ Himg) in Hp2.
    rewrite bskl_to_pskl_subst_var in Hp2.
    assert (HoQ : open_bskl_wrt_bskl Q (bskl_var_f α0)
                = subst_bskl_in_bskl (bskl_var_f α0) α
                    (open_bskl_wrt_bskl Q (bskl_var_f α)))
      by (apply subst_bskl_in_bskl_intro; clear - Fr; fsetdec).
    rewrite <- HoQ in Hp2.
    eapply ad_refine_syn_f_fmono;
      [ | eapply ad_refine_syn_f_delta_mono; [ exact Hp2 | ] ].
    { clear - HαΔ1 HαΔ2. fsetdec. }
    { clear - HαΔ1 HαΔ2 Hα0. fsetdec. }
  (* ------------------------------------------- forall_syn (impossible) *)
  - destruct (msubst_pskl κ PP); simpl in HeqS; discriminate.
  (* ------------------------------------------------------ forall_syn *)
  - (* C-ForallSyn (paper :2853-2926): as C-ForallInh with the opened α
       added to Δ2 only and the input ∀◇.P0' carried unchanged (the
       Δ1-refinement's [tophole_fill] premise arrives ALREADY at the
       α-extended context). *)
    match goal with
    | Hpm : forall α, α `notin` _ -> _ ⨟ _ ⊢ₛᵃ _ ∼ _ |- _ =>
        rename Hpm into Hjoin
    end.
    (* SUBJECT: PP = ∀ PPb. *)
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { exfalso.
      assert (Hbtδ : binds β1 abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ : β1 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.
    (* INPUT: PP0 = ∀◇ Pt0 (a ∀-syn target only arises by tophole_fill) *)
    destruct PP0 as [ | n0 | β10 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso.
      assert (Hbtδ0 : binds β10 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ0 : β10 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds β10 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds β10 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                        (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; apply HneP0hole; reflexivity. }
    (* invert the two refinements; wf of the pieces *)
    assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
    assert (Hwft0 : Θ0 ⨟ empty ⊢ₚₛᵃ Pt0) by (inversion HwfP0; assumption).
    inversion Hrs; subst.
    1:{ (* __tophole_remove : the guarded body would refine to a ∀-syn *)
      exfalso.
      assert (Hgκ0 : guarded_pskl (msubst_pskl κ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      eapply ad_refine_syn_f_guarded_src_all_syn_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgκ0 ]. }
    match goal with
    | Hn : forall α, α `notin` ?LA ->
             ad_refine_syn_f _ _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_all_syn (msubst_pskl κ PPb))
              (pskl_all_syn (bskl_to_pskl Q))) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Hn : forall α, α `notin` ?LB ->
             ad_refine_pskl_f _ _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb : exists Lw, forall α, α `notin` Lw ->
              Θ0 ⨟ (add α empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl PPb (pskl_var_f α))).
    { inversion HwfP; subst. eexists. eassumption. }
    destruct Hwfb as [Lw Hwfb].
    (* the fresh rigid α *)
    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw
                        `union` dom Θ0 `union` ftvar_in_aenv Θ0
                        `union` dom Θ `union` dom κ
                        `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl Pt0 `union` ftvar_in_pskl PPb
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hακ : α `notin` dom κ) by (clear - Fr; fsetdec).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; fsetdec).
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) κ Pz
                            = Vpskl Θ κ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) κ
           (pskl_tophole Pt0)
           (open_pskl_wrt_pskl PPb (pskl_var_f α))
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ κ (pskl_tophole Pt0) (pskl_all_syn PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open PPb Hwfth Hlcκ Hακ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ κ PPb). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    assert (Hwf0' : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ]).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (pskl_tophole Pt0)).
    { eapply a_wf_pskl_weaken; [ | exact HwfP0 ].
      intros x b Hb. apply binds_cons_3. exact Hb. }
    assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl PPb (pskl_var_f α))).
    { eapply a_wf_pskl_delta_to_tvar;
        [ apply Hwfb; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (Hrig' : forall α2, α2 `in` (Δ1 `union` add α Δ2) ->
              binds α2 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α2 Hα2. destruct (α2 == α) as [-> | Hne];
        [ unfold binds; left; reflexivity
        | apply binds_cons_3; apply Hrig; clear - Hα2 Hne; fsetdec ]. }
    assert (Hnfd0' : no_flex_dep (Δ1 `union` add α Δ2)
                       ((α ~ abind_tvar) ++ Θ0)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwf0 | exact Hnfd0 | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hfaf' : flex_above_free (Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { eapply faf_cong;
        [ | eapply faf_open_tvar; [ exact Hfaf | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hinc' : κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑
                      ((α ~ abind_tvar) ++ Θ)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc).
      apply a_decls_suffix. apply a_decls__nil. }
    assert (Hwfth' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ exact HαΘ | exact Hwfth ]).
    assert (Hnfdth' : no_flex_dep (Δ1 `union` add α Δ2)
                        ((α ~ abind_tvar) ++ Θ)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwfth | exact Hnfdth | exact HαΘ ] ].
      clear. fsetdec. }
    assert (Hjα : Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ₛᵃ
              (pskl_to_uskl (msubst_pskl κ
                 (open_pskl_wrt_pskl PPb (pskl_var_f α))))
              ∼ (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { pose proof (Hjoin α ltac:(clear - Fr; fsetdec)) as Hj0.
      rewrite (msubst_pskl_open_lc PPb Hlcκ Hακ).
      rewrite pskl_to_uskl_open_var.
      exact Hj0. }
    assert (Hrsα : ad_refine_syn_f Δ1 ((α ~ abind_tvar) ++ Θ) Δ1
              (pskl_to_bskl_inh (msubst_pskl κ (pskl_tophole Pt0)))
              (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { simpl. apply Hrs1. clear - Fr. fsetdec. }
    assert (Hrpα : ad_refine_pskl_f (add α Δ2) ((α ~ abind_tvar) ++ Θ)
              (add α Δ2)
              (msubst_pskl κ (open_pskl_wrt_pskl PPb (pskl_var_f α)))
              (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)))).
    { rewrite (msubst_pskl_open_lc PPb Hlcκ Hακ).
      rewrite bskl_to_pskl_open.
      eapply ad_refine_pskl_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_pskl_f_fextend_dom;
        [ apply Hrp1; clear - Fr; fsetdec | ].
      intros α1 Hα1. destruct (α1 == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hα1 Hne; fsetdec ]. }
    destruct (HcIH N Δ1 (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
                (pskl_tophole Pt0)
                (open_pskl_wrt_pskl PPb (pskl_var_f α)) κ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα)
      as [P1 [Θ1' [Hc [Hnew Hopt']]]].
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.
    (* assemble the exists-fresh node at the run's OWN α *)
    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; fsetdec).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    { (* EXISTS-FRESH (campaign cluster 4): the run's OWN α is the
         rule's binder, so the node is one constructor application —
         no family to rebuild, hence no rename. *)
      apply a_consis__forall_syn with (α := α);
        [ clear - Fr; fsetdec | exact Hc ]. }
    (* the avoid set survives the truncation: [α] is the run's OWN binder,
       so it cannot occur in the tail the node hands back *)
    split.
    { eapply avoid_truncate_cons; [ exact Hnew | ].
      pose proof (auc_uniq_consis Hc Huq0) as Hu1. clear - Hu1. solve_uniq. }
    (* optimality *)
    intros κ1 Hid Hinc1.
    assert (Hinc1' : κ1 ∷ ((α ~ abind_tvar) ++ Θ0) ⊑
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc1).
      apply a_decls_suffix. apply a_decls__nil. }
    destruct (Hopt' κ1 Hid Hinc1') as [ζ [Hζ [Hie Hprec]]].
    exists ζ.
    assert (Hζ' : ζ ∷ Θ1 ⊑ Θ).
    { destruct (a_inc_tvar_inv Hζ) as [Ξs [Θ2 [HeqT [Hsuf Hinc2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hinc2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    assert (Hie' : a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ).
    { destruct (a_inc_equiv_tvar_inv Hie) as [Ξs [Θ2 [HeqT [Hsuf Hie2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hie2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    split; [ exact Hζ' | ]. split; [ exact Hie' | ].
    (* precision : rebind the quantifier *)
    assert (Hlcζ : msubst_lc ζ) by (eapply a_inc_msubst_lc; exact Hζ').
    assert (Huq1' : uniq ((α ~ abind_tvar) ++ Θ1))
      by (exact (auc_uniq_consis Hc Huq0)).
    assert (HαΘ1 : α `notin` dom Θ1) by solve_uniq.
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Himg : forall α1 τ, In (α1, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros α1 τ Hin.
      pose proof (a_inc_images_ftv_dom Hζ' _ _ Hin) as Hsc.
      clear - Hsc HαΘ. fsetdec. }
    unfold ad_precise_f in Hprec |- *.
    rewrite bskl_to_pskl_msubst_bskl in Hprec |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec |- *.
    change (ad_refine_syn_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
      (bskl_all_inh (pskl_to_bskl_inh
         (msubst_pskl ζ (close_pskl_wrt_pskl α P1))))
      (bskl_all_inh (pskl_to_bskl_inh (bskl_to_pskl Q)))).
    apply ad_refine_syn_f__all with
      (L := singleton α `union` dom Θ `union` dom Θ1
            `union` Δ1 `union` Δ2
            `union` ftvar_in_bskl Q `union` ftvar_in_pskl P1).
    intros α0 Hα0.
    assert (Hα0ζ : α0 `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb Hα0; fsetdec. }
    rewrite <- !pskl_to_bskl_inh_open.
    rewrite <- (msubst_pskl_open_lc (close_pskl_wrt_pskl α P1) Hlcζ Hα0ζ).
    rewrite <- (subst_pskl_in_pskl_spec P1 (pskl_var_f α0) α).
    rewrite <- bskl_to_pskl_open.
    pose proof (ad_refine_syn_f_ctx_to_delta Hprec nil Θ eq_refl
                  ltac:(clear; fsetdec)
                  (a_wf_aenv_uniq Hwfth')) as Hp1.
    simpl in Hp1.
    assert (HαF : α `in` (Δ1 `union` add α Δ2))
      by (clear; fsetdec).
    assert (Hdefsκ : forall β τ,
              binds β (abind_flex_mono_def τ) Θ ->
              α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; eassumption).
      clear - Hsc HαΘ. fsetdec. }
    pose proof (ad_refine_syn_f_rename α0 Hp1 HαF HαΘ Hdefsκ) as Hp2.
    rewrite !pskl_to_bskl_inh_subst_var in Hp2.
    rewrite (msubst_pskl_subst_var ζ P1 Hαζ Hα0ζ Himg) in Hp2.
    rewrite bskl_to_pskl_subst_var in Hp2.
    assert (HoQ : open_bskl_wrt_bskl Q (bskl_var_f α0)
                = subst_bskl_in_bskl (bskl_var_f α0) α
                    (open_bskl_wrt_bskl Q (bskl_var_f α)))
      by (apply subst_bskl_in_bskl_intro; clear - Fr; fsetdec).
    rewrite <- HoQ in Hp2.
    eapply ad_refine_syn_f_fmono;
      [ | eapply ad_refine_syn_f_delta_mono; [ exact Hp2 | ] ].
    { clear - HαΔ1 HαΔ2. fsetdec. }
    { clear - HαΔ1 HαΔ2 Hα0. fsetdec. }
  (* ---------------------------------------------- ghostg (impossible) *)
  - destruct (msubst_pskl κ PP); simpl in HeqS; discriminate.
  (* -------------------------------------------- topholeg (impossible) *)
  - destruct (msubst_pskl κ PP); simpl in HeqS; discriminate.
  (* ------------------------------------------------------------- hole *)
  - (* C-Ghost (paper :2583-2613): subject ◇, axiom node [a_consis__ghost].
       The side condition [Δ2 ∩ ftv(P0) = ∅] is the rigid-ftv chase: a
       Δ2-variable of ftv(P0) would survive the metasubstitution
       ([msubst_pskl_ftv_keep]) and the competing Δ1-refinement
       right-to-left ([ad_refine_syn_f_rigid_ftv_rev]) into the join's
       fill, whose ftv the Δ2-refinement's hole rule excludes.  Precision
       IS the competing Δ1-refinement. *)
    rename H into HΨfill. rename H0 into HwfFill.
    (* SUBJECT: PP = ◇ (var subjects are rigid, their image a var). *)
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var β1 : rigid, its image is β1 itself *)
      exfalso.
      assert (Hbtδ : binds β1 abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ : β1 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
      simpl in HeqS. discriminate. }
    (* the Δ2-refinement bounds the fill's free variables *)
    change (ad_refine_pskl_f Δ2 Θ Δ2 pskl_hole
              (bskl_to_pskl (pskl_to_bskl_inh P))) in Hrp.
    rewrite bskl_to_pskl_pskl_to_bskl_inh in Hrp.
    (* the ftv chase for the Ghost side condition *)
    assert (Hside : forall α, α `in` Δ2 -> α `notin` ftvar_in_pskl PP0).
    { intros α HinΔ2 HinP0.
      assert (HbX0 : binds α abind_tvar Θ0)
        by (apply Hrig; clear - HinΔ2; fsetdec).
      assert (HbX : binds α abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      assert (HXnd : α `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      assert (Hdefs : forall β τ, binds β (abind_flex_mono_def τ) Θ ->
                                  α `notin` ftvar_in_ptyp τ).
      { intros β τ Hb. pose proof (Hnfdth _ _ Hb) as Hd.
        clear - Hd HinΔ2. fsetdec. }
      assert (HninP : α `notin` ftvar_in_pskl P).
      { inversion Hrp; subst.
        - (* hole : the Δ2-hygiene of the fill *)
          match goal with
          | Hint : Δ2 ∩ ftvar_in_pskl P [=] empty |- _ =>
              clear - Hint HinΔ2; fsetdec
          end.
        - (* flex_r : the fill is a defined flexible, never the rigid α *)
          simpl.
          match goal with
          | Hbr : binds ?α0 (abind_flex_mono_def _) Θ |- _ =>
              assert (Hne : α <> α0)
                by (intro Heq; subst;
                    pose proof (binds_unique _ _ _ _ _ HbX Hbr
                                  (a_wf_aenv_uniq Hwfth)) as Hcon;
                    discriminate)
          end.
          clear - Hne; fsetdec. }
      assert (HinκP0 : α `in` ftvar_in_pskl (msubst_pskl κ PP0))
        by (apply msubst_pskl_ftv_keep; assumption).
      assert (HninSrc : α `notin`
                ftvar_in_bskl (pskl_to_bskl_inh (msubst_pskl κ PP0))).
      { eapply ad_refine_syn_f_rigid_ftv_rev;
          [ exact Hwfth | exact HbX | exact Hdefs | exact Hrs | ].
        pose proof (ftvar_in_bskl_inh P) as Hfe.
        clear - HninP Hfe. fsetdec. }
      pose proof (ftvar_in_bskl_inh (msubst_pskl κ PP0)) as Hfe2.
      clear - HninSrc HinκP0 Hfe2. fsetdec. }
    exists PP0, Θ0. split.
    { apply a_consis__ghost.
      apply inter_empty_pointwise. exact Hside. }
    split; [ intros γ Hγ; left; exact Hγ | ].
    intros κ1 Hid Hinc1. exists κ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    (* precision: exactly the competing Δ1-refinement, F-extended to the
       Δ2 half by the hole-source Δ2-refinement's own target hygiene *)
    unfold ad_precise_f.
    rewrite bskl_to_pskl_msubst_bskl.
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    eapply ad_refine_syn_f_delta_mono with (Δ0 := Δ1);
      [ | clear; fsetdec ].
    eapply ad_refine_syn_f_fextend_ftv; [ exact Hrs | ].
    intros α1 Hα1.
    destruct (AtomSetProperties.In_dec α1 Δ1) as [Hα1Δ1 | Hα1Δ1];
      [ left; exact Hα1Δ1 | right ].
    assert (Hα1Δ2 : α1 `in` Δ2) by (clear - Hα1 Hα1Δ1; fsetdec).
    assert (Hbγ : binds α1 abind_tvar Θ)
      by (eapply a_inc_binds_tvar; [ exact Hinc | ];
          apply Hrig; clear - Hα1Δ2; fsetdec).
    split.
    + assert (Hnq : α1 `notin` ftvar_in_pskl P)
        by (eapply ad_refine_pskl_f_hole_src_target_ftv;
            [ exact Hrp | exact Hwfth
            | clear - Hα1Δ2; fsetdec | exact Hbγ ]).
      pose proof (ftvar_in_bskl_inh P) as Hfe.
      clear - Hnq Hfe. fsetdec.
    + intros β τ Hb.
      pose proof (Hnfdth β τ Hb) as Hi.
      clear - Hi Hα1Δ2. fsetdec.
  (* ---------------------------------------------------------- tophole *)
  - (* C-UnivGhost (paper :2928-2993): both sides strip one ∀◇; wf forces
       the input to be a ∀◇ as well (a guarded input's refinement target is
       guarded, never a ∀◇); V drops by 2, recurse through the μ-IH. *)
    match goal with
    | Hpm : _ ⨟ _ ⊢ₛᵃ _ ∼ _ |- _ => rename Hpm into Hj
    end.
    (* SUBJECT: PP = ∀◇PPt (var subjects are rigid, their image a var). *)
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var β1 : rigid, its image is β1 itself *)
      exfalso.
      assert (Hbtδ : binds β1 abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ : β1 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R. clear HeqS.
    assert (HgPPt : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPPt : Θ0 ⨟ empty ⊢ₚₛᵃ PPt) by (inversion HwfP; assumption).
    assert (HgκP : guarded_pskl (msubst_pskl κ PPt))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (HlcQ : lc_bskl Q).
    { assert (Hlct : lc_bskl (bskl_tophole Q))
        by (eapply ad_refine_syn_f_lc_r; exact Hrs).
      inversion Hlct; assumption. }
    assert (HgQ : guarded_bskl Q).
    { eapply ad_pat_consis_guarded_r;
        [ exact Hj | exact Hwfth | reflexivity | exact HgκP | exact HlcQ ]. }
    (* INPUT: PP0 = ∀◇P0t (every other head's target is not a ∀◇). *)
    destruct PP0 as [ | n0 | β10 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ (* var β10 : rigid; a rigid variable does not refine to a ∀◇ *)
      exfalso.
      assert (Hbtδ0 : binds β10 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ0 : β10 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds β10 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds β10 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr (a_wf_aenv_uniq Hwfth))
            as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; apply HneP0hole; reflexivity. }
    (* PP0 = ∀◇Pt0 : strip the ∀◇ on all three judgments. *)
    assert (Hg0t : guarded_pskl Pt0) by (inversion HwfP0; assumption).
    assert (HwfP0t : Θ0 ⨟ empty ⊢ₚₛᵃ Pt0) by (inversion HwfP0; assumption).
    assert (Hgκ0 : guarded_pskl (msubst_pskl κ Pt0))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
              (pskl_to_bskl_inh (msubst_pskl κ Pt0)) Q).
    { eapply ad_refine_syn_f_tophole_keep_inv;
        [ exact Hwfth | | exact Hrs ].
      apply guarded_pskl_to_bskl_inh. exact Hgκ0. }
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl κ PPt))
              (pskl_tophole (bskl_to_pskl Q))) in Hrp.
    assert (Hrp' : ad_refine_pskl_f Δ2 Θ Δ2
              (msubst_pskl κ PPt) (bskl_to_pskl Q))
      by (eapply ad_refine_pskl_f_tophole_keep_inv;
            [ exact Hwfth | exact HgκP | exact Hrp ]).
    assert (Hlt : mu_lt (mu_consis Θ κ Pt0 PPt Θ0)
                        (mu_consis Θ κ (pskl_tophole Pt0)
                                       (pskl_tophole PPt) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      pose proof (Vpskl_tophole_lt Θ κ Pt0).
      pose proof (Vpskl_tophole_lt Θ κ PPt). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH N Δ1 Δ2 Θ0 Pt0 PPt κ Θ Ψ Q eq_refl Hwf0 HwfP0t HwfPPt
                   Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs' Hrp')
      as [P1 [Θ1 [Hc [Hnew Hopt']]]].
    exists (pskl_tophole P1), Θ1. split.
    { apply a_consis__univ_ghost. exact Hc. }
    split; [ exact Hnew | ].
    intros κ1 Hid Hinc1.
    destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
    unfold ad_precise_f in *. simpl.
    apply ad_refine_syn_f__tophole_keep; [ | exact Hprec ].
    apply guarded_pskl_to_bskl_inh, guarded_bskl_to_pskl. exact HgQ.
  (* ------------------------------------------------------ tophole_inh *)
  - (* C-UnivGhost1 (paper :2995-3070): the input's ∀ opens with a fresh
       rigid α added to Θ0 and Δ1; the subject ∀◇.PPt is carried
       unchanged through the μ-IH and the L9 rename. *)
    match goal with
    | Hpm : forall α, α `notin` _ -> _ ⨟ _ ⊢ₛᵃ _ ∼ _ |- _ =>
        rename Hpm into Hjoin
    end.
    (* SUBJECT: PP = ∀◇ PPt. *)
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { exfalso.
      assert (Hbtδ : binds β1 abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ : β1 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.
    (* INPUT: PP0 = ∀ P0b. *)
    destruct PP0 as [ | n0 | β10 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso.
      assert (Hbtδ0 : binds β10 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ0 : β10 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds β10 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds β10 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                        (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ exfalso.
      assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
      assert (Hgκ0 : guarded_pskl (msubst_pskl κ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      inversion Hrs; subst.
      eapply ad_refine_syn_f_guarded_src_all_inh_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgκ0 ]. }
    (* ∀ input, ∀◇ subject : invert the refinements, wf pieces *)
    assert (HgP : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPt : Θ0 ⨟ empty ⊢ₚₛᵃ PPt) by (inversion HwfP; assumption).
    inversion Hrs; subst.
    match goal with
    | Hn : forall α, α `notin` ?LA ->
             ad_refine_syn_f _ _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl κ PPt))
              (pskl_all_syn (bskl_to_pskl Q))) in Hrp.
    inversion Hrp; subst.
    1:{ (* __tophole_remove : the guarded subject body vs a ∀-syn *)
      exfalso.
      assert (HgκP : guarded_pskl (msubst_pskl κ PPt))
        by (eapply guarded_pskl_msubst_inc; eauto).
      eapply ad_refine_pskl_f_guarded_src_all_syn_absurd;
        [ exact Hwfth | eassumption | exact HgκP ]. }
    match goal with
    | Hn : forall α, α `notin` ?LB ->
             ad_refine_pskl_f _ _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb0 : exists Lw0, forall α, α `notin` Lw0 ->
              Θ0 ⨟ (add α empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl P0b (pskl_var_f α))).
    { inversion HwfP0; subst. eexists. eassumption. }
    destruct Hwfb0 as [Lw0 Hwfb0].
    (* the fresh rigid α *)
    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw0
                        `union` dom Θ0 `union` ftvar_in_aenv Θ0
                        `union` dom Θ `union` dom κ
                        `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPt
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hακ : α `notin` dom κ) by (clear - Fr; fsetdec).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; fsetdec).
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) κ Pz
                            = Vpskl Θ κ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) κ
           (open_pskl_wrt_pskl P0b (pskl_var_f α))
           (pskl_tophole PPt)
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ κ (pskl_all_syn P0b) (pskl_tophole PPt) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open P0b Hwfth Hlcκ Hακ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ κ P0b). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    assert (Hwf0' : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ]).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (open_pskl_wrt_pskl P0b (pskl_var_f α))).
    { eapply a_wf_pskl_delta_to_tvar;
        [ apply Hwfb0; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (pskl_tophole PPt)).
    { eapply a_wf_pskl_weaken; [ | exact HwfP ].
      intros x b Hb. apply binds_cons_3. exact Hb. }
    assert (Hrig' : forall α2, α2 `in` (add α Δ1 `union` Δ2) ->
              binds α2 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α2 Hα2. destruct (α2 == α) as [-> | Hne];
        [ unfold binds; left; reflexivity
        | apply binds_cons_3; apply Hrig; clear - Hα2 Hne; fsetdec ]. }
    assert (Hnfd0' : no_flex_dep (add α Δ1 `union` Δ2)
                       ((α ~ abind_tvar) ++ Θ0)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwf0 | exact Hnfd0 | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hfaf' : flex_above_free (add α Δ1 `union` Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { eapply faf_cong;
        [ | eapply faf_open_tvar; [ exact Hfaf | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hinc' : κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑
                      ((α ~ abind_tvar) ++ Θ)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc).
      apply a_decls_suffix. apply a_decls__nil. }
    assert (Hwfth' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ exact HαΘ | exact Hwfth ]).
    assert (Hnfdth' : no_flex_dep (add α Δ1 `union` Δ2)
                        ((α ~ abind_tvar) ++ Θ)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwfth | exact Hnfdth | exact HαΘ ] ].
      clear. fsetdec. }
    assert (Hjα : Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ₛᵃ
              (pskl_to_uskl (msubst_pskl κ (pskl_tophole PPt)))
              ∼ (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { simpl. apply Hjoin. clear - Fr. fsetdec. }
    assert (Hrsα : ad_refine_syn_f (add α Δ1) ((α ~ abind_tvar) ++ Θ)
              (add α Δ1)
              (pskl_to_bskl_inh (msubst_pskl κ
                 (open_pskl_wrt_pskl P0b (pskl_var_f α))))
              (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { rewrite (msubst_pskl_open_lc P0b Hlcκ Hακ).
      rewrite pskl_to_bskl_inh_open.
      eapply ad_refine_syn_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_syn_f_fextend_dom;
        [ apply Hrs1; clear - Fr; fsetdec | ].
      intros α1 Hα1. destruct (α1 == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hα1 Hne; fsetdec ]. }
    assert (Hrpα : ad_refine_pskl_f Δ2 ((α ~ abind_tvar) ++ Θ) Δ2
              (msubst_pskl κ (pskl_tophole PPt))
              (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)))).
    { simpl. rewrite bskl_to_pskl_open. apply Hrp1.
      clear - Fr. fsetdec. }
    destruct (HcIH N (add α Δ1) Δ2 ((α ~ abind_tvar) ++ Θ0)
                (open_pskl_wrt_pskl P0b (pskl_var_f α))
                (pskl_tophole PPt) κ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα)
      as [P1 [Θ1' [Hc [Hnew Hopt']]]].
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.
    (* assemble the exists-fresh node at the run's OWN α *)
    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; fsetdec).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    { (* EXISTS-FRESH (campaign cluster 4): the run's OWN α is the
         rule's binder, so the node is one constructor application —
         no family to rebuild, hence no rename. *)
      apply a_consis__univ_ghost1 with (α := α);
        [ clear - Fr; fsetdec | exact Hc ]. }
    (* the avoid set survives the truncation: [α] is the run's OWN binder,
       so it cannot occur in the tail the node hands back *)
    split.
    { eapply avoid_truncate_cons; [ exact Hnew | ].
      pose proof (auc_uniq_consis Hc Huq0) as Hu1. clear - Hu1. solve_uniq. }
    (* optimality *)
    intros κ1 Hid Hinc1.
    assert (Hinc1' : κ1 ∷ ((α ~ abind_tvar) ++ Θ0) ⊑
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc1).
      apply a_decls_suffix. apply a_decls__nil. }
    destruct (Hopt' κ1 Hid Hinc1') as [ζ [Hζ [Hie Hprec]]].
    exists ζ.
    assert (Hζ' : ζ ∷ Θ1 ⊑ Θ).
    { destruct (a_inc_tvar_inv Hζ) as [Ξs [Θ2 [HeqT [Hsuf Hinc2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hinc2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    assert (Hie' : a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ).
    { destruct (a_inc_equiv_tvar_inv Hie) as [Ξs [Θ2 [HeqT [Hsuf Hie2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hie2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    split; [ exact Hζ' | ]. split; [ exact Hie' | ].
    assert (Hlcζ : msubst_lc ζ) by (eapply a_inc_msubst_lc; exact Hζ').
    assert (Huq1' : uniq ((α ~ abind_tvar) ++ Θ1))
      by (exact (auc_uniq_consis Hc Huq0)).
    assert (HαΘ1 : α `notin` dom Θ1) by solve_uniq.
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Himg : forall α1 τ, In (α1, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros α1 τ Hin.
      pose proof (a_inc_images_ftv_dom Hζ' _ _ Hin) as Hsc.
      clear - Hsc HαΘ. fsetdec. }
    unfold ad_precise_f in Hprec |- *.
    rewrite bskl_to_pskl_msubst_bskl in Hprec |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec |- *.
    change (ad_refine_syn_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
      (bskl_all_inh (pskl_to_bskl_inh
         (msubst_pskl ζ (close_pskl_wrt_pskl α P1))))
      (bskl_all_inh (pskl_to_bskl_inh (bskl_to_pskl Q)))).
    apply ad_refine_syn_f__all with
      (L := singleton α `union` dom Θ `union` dom Θ1
            `union` Δ1 `union` Δ2
            `union` ftvar_in_bskl Q `union` ftvar_in_pskl P1).
    intros α0 Hα0.
    assert (Hα0ζ : α0 `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb Hα0; fsetdec. }
    rewrite <- !pskl_to_bskl_inh_open.
    rewrite <- (msubst_pskl_open_lc (close_pskl_wrt_pskl α P1) Hlcζ Hα0ζ).
    rewrite <- (subst_pskl_in_pskl_spec P1 (pskl_var_f α0) α).
    rewrite <- bskl_to_pskl_open.
    pose proof (ad_refine_syn_f_ctx_to_delta Hprec nil Θ eq_refl
                  ltac:(clear; fsetdec)
                  (a_wf_aenv_uniq Hwfth')) as Hp1.
    simpl in Hp1.
    assert (HαF : α `in` (add α Δ1 `union` Δ2))
      by (clear; fsetdec).
    assert (Hdefsκ : forall β τ,
              binds β (abind_flex_mono_def τ) Θ ->
              α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; eassumption).
      clear - Hsc HαΘ. fsetdec. }
    pose proof (ad_refine_syn_f_rename α0 Hp1 HαF HαΘ Hdefsκ) as Hp2.
    rewrite !pskl_to_bskl_inh_subst_var in Hp2.
    rewrite (msubst_pskl_subst_var ζ P1 Hαζ Hα0ζ Himg) in Hp2.
    rewrite bskl_to_pskl_subst_var in Hp2.
    assert (HoQ : open_bskl_wrt_bskl Q (bskl_var_f α0)
                = subst_bskl_in_bskl (bskl_var_f α0) α
                    (open_bskl_wrt_bskl Q (bskl_var_f α)))
      by (apply subst_bskl_in_bskl_intro; clear - Fr; fsetdec).
    rewrite <- HoQ in Hp2.
    eapply ad_refine_syn_f_fmono;
      [ | eapply ad_refine_syn_f_delta_mono; [ exact Hp2 | ] ].
    { clear - HαΔ1 HαΔ2. fsetdec. }
    { clear - HαΔ1 HαΔ2 Hα0. fsetdec. }
  (* ----------------------------------------------------- tophole_drop *)
  - (* C-UnivGhost2 (paper :3072-3164): the subject strips its ∀◇; the
       guarded subject body makes the join target Q guarded, which drives
       BOTH sub-cases: input ∀◇P0t (strip on all three, [univ_ghost]) or
       input guarded (subject-only strip, [univ_ghost2]). *)
    match goal with
    | Hpm : _ ⨟ _ ⊢ₛᵃ _ ∼ _ |- _ => rename Hpm into Hj
    end.
    (* SUBJECT: PP = ∀◇PPt. *)
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var β1 : rigid, its image is β1 itself *)
      exfalso.
      assert (Hbtδ : binds β1 abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hβ1κ : β1 `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R. clear HeqS.
    assert (HgPPt : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPPt : Θ0 ⨟ empty ⊢ₚₛᵃ PPt) by (inversion HwfP; assumption).
    assert (HgκP : guarded_pskl (msubst_pskl κ PPt))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (HlcQ : lc_bskl Q) by (eapply ad_refine_syn_f_lc_r; exact Hrs).
    assert (HgQ : guarded_bskl Q).
    { eapply ad_pat_consis_guarded_r;
        [ exact Hj | exact Hwfth | reflexivity | exact HgκP | exact HlcQ ]. }
    (* the subject-side refinement drops its ∀◇ against the guarded Q *)
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl κ PPt)) (bskl_to_pskl Q)) in Hrp.
    assert (Hrp' : ad_refine_pskl_f Δ2 Θ Δ2
              (msubst_pskl κ PPt) (bskl_to_pskl Q)).
    { eapply ad_refine_pskl_f_tophole_guarded_inv;
        [ exact Hwfth | exact Hrp | ].
      apply guarded_bskl_to_pskl. exact HgQ. }
    (* INPUT: split on whether PP0 is a ∀◇. *)
    assert (Hthdec : (exists P0t, PP0 = pskl_tophole P0t) \/
                     (forall P0t, PP0 <> pskl_tophole P0t)).
    { destruct PP0; try (right; intros ? Hc0; discriminate).
      left; eexists; reflexivity. }
    destruct Hthdec as [[P0t ->] | Hnth0].
    + (* PP0 = ∀◇P0t : paper :3098-3132; both inputs strip, [univ_ghost]. *)
      assert (Hg0t : guarded_pskl P0t) by (inversion HwfP0; assumption).
      assert (HwfP0t : Θ0 ⨟ empty ⊢ₚₛᵃ P0t) by (inversion HwfP0; assumption).
      change (ad_refine_syn_f Δ1 Θ Δ1
                (bskl_tophole (pskl_to_bskl_inh (msubst_pskl κ P0t))) Q)
        in Hrs.
      assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
                (pskl_to_bskl_inh (msubst_pskl κ P0t)) Q)
        by (eapply ad_refine_syn_f_tophole_guarded_inv; eauto).
      assert (Hlt : mu_lt (mu_consis Θ κ P0t PPt Θ0)
                          (mu_consis Θ κ (pskl_tophole P0t)
                                         (pskl_tophole PPt) Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
        pose proof (Vpskl_tophole_lt Θ κ P0t).
        pose proof (Vpskl_tophole_lt Θ κ PPt). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH N Δ1 Δ2 Θ0 P0t PPt κ Θ Ψ Q eq_refl Hwf0 HwfP0t HwfPPt
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs' Hrp')
        as [P1 [Θ1 [Hc [Hnew Hopt']]]].
      exists (pskl_tophole P1), Θ1. split.
      { apply a_consis__univ_ghost. exact Hc. }
      split; [ exact Hnew | ].
      intros κ1 Hid Hinc1.
      destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      unfold ad_precise_f in *. simpl.
      apply ad_refine_syn_f__tophole_remove. exact Hprec.
    + (* PP0 guarded : paper :3134-3163; subject-only strip, [univ_ghost2]. *)
      assert (Hg0 : guarded_pskl PP0).
      { destruct PP0 as [ | n0 | β10 | Pa0 Pb0 | Pb0 | | Pt0 ].
        - auto with frost.
        - inversion HwfP0.
        - auto with frost.
        - pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption.
        - (* ∀ : an inherited quantifier never refines to the guarded Q *)
          exfalso. simpl in Hrs.
          eapply ad_refine_syn_f_all_inh_guarded_absurd;
            [ exact Hwfth | exact Hrs | exact HgQ ].
        - exfalso; apply HneP0hole; reflexivity.
        - exfalso; eapply Hnth0; reflexivity. }
      assert (Hlt : mu_lt (mu_consis Θ κ PP0 PPt Θ0)
                          (mu_consis Θ κ PP0 (pskl_tophole PPt) Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
        pose proof (Vpskl_tophole_lt Θ κ PPt). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH N Δ1 Δ2 Θ0 PP0 PPt κ Θ Ψ Q eq_refl Hwf0 HwfP0 HwfPPt
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs Hrp')
        as [P1 [Θ1 [Hc [Hnew Hopt']]]].
      exists P1, Θ1. split.
      { apply a_consis__univ_ghost2;
          [ exact Hg0 | exact HnfP0 | exact Hc ]. }
      split; [ exact Hnew | exact Hopt' ].
  (* ----------------------------------------------- flex_l (impossible) *)
  - (* The subject is non-flex, so a variable subject is RIGID in Θ0 and
       stays rigid in Θ — it cannot be the defined flexible the join's
       left lookup unfolds. *)
    exfalso.
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    assert (Hbtδ : binds β1 abind_tvar Θ0).
    { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
      destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
        [ exfalso; clear - HΔ; fsetdec
        | exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          apply a_flex__var; exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          eapply a_flex__var_def; exact Hb ]. }
    assert (Hβ1κ : β1 `notin` dom κ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
    simpl in HeqS. inversion HeqS; subst α.
    assert (HbtΘ : binds β1 abind_tvar Θ)
      by (eapply a_inc_binds_tvar; eauto).
    pose proof (binds_unique _ _ _ _ _ HbtΘ H (a_wf_aenv_uniq Hwfth))
      as Hcon; discriminate.
  (* ----------------------------------------------------------- flex_r *)
  - (* Target-side definition unfold [Qb = α̂ ≔ τ]: the join shrinks while
       the measure stands still — this is exactly why the core INDUCTS on
       the join.  Transport Hrs/Hrp through the unfold
       ([ad_refine_syn_f_flex_target_unfold] and its uncoloured twin, fed
       by the [no_flex_dep] invariant), recurse on the premise via [IHHj],
       and re-attach the [α̂]-target to the resulting precision by
       [ad_refine_syn__flex_r]. *)
    match goal with
    | Hb : binds _ (abind_flex_mono_def _) _ |- _ => rename Hb into Hbα
    end.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hdisj : (Δ1 `union` Δ2) ∩ ftvar_in_ptyp τ
                      [=] empty)
      by (apply (Hnfdth _ _ Hbα)).
    assert (HΔbt : forall α, α `in` (Δ1 `union` Δ2) ->
                             binds α abind_tvar Θ).
    { intros α0 Hα0. eapply a_inc_binds_tvar; [ exact Hinc | ].
      apply Hrig. exact Hα0. }
    (* transport the two refinement witnesses through the unfold *)
    assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
              (pskl_to_bskl_inh (msubst_pskl κ PP0)) (ptyp_to_bskl_syn τ)).
    { eapply ad_refine_syn_f_flex_target_unfold;
        [ exact Hwfth | exact Hbα
        | intros α0 Hα0; apply HΔbt; clear - Hα0; fsetdec
        | clear - Hdisj; fsetdec
        | exact Hrs ]. }
    assert (Hrp' : ad_refine_pskl_f Δ2 Θ Δ2
              (msubst_pskl κ PP) (bskl_to_pskl (ptyp_to_bskl_syn τ))).
    { unfold ptyp_to_bskl_syn.
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      eapply ad_refine_pskl_f_flex_target_unfold;
        [ exact Hwfth | exact Hbα
        | intros α0 Hα0; apply HΔbt; clear - Hα0; fsetdec
        | clear - Hdisj; fsetdec
        | exact Hrp ]. }
    (* recurse on the premise at the SAME measure *)
    destruct (IHHj N Δ1 Δ2 Θ0 PP0 PP κ IH Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf
                   Hinc Hwfth Hnfdth HΨ HeqS HnfP HnfP0 HneP0hole Hnthg
                   Hrs' Hrp')
      as [P1 [Θ1 [Hc [Hnew Hopt']]]].
    exists P1, Θ1. split; [ exact Hc | ].
    split; [ exact Hnew | ].
    intros κ1 Hid Hinc1.
    destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
    (* re-attach the flexible target to the precision *)
    unfold ad_precise_f in *. simpl.
    eapply ad_refine_syn_f__flex_r; [ exact Hbα | ].
    unfold ptyp_to_bskl_syn in Hprec.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec.
    rewrite (mono_inh_eq_syn Hmτ) in Hprec.
    exact Hprec.
Qed.

Lemma consis_complete_step : forall m,
  (forall m', mu_lt m' m -> complete_at m') ->
  consis_complete_at m.
Proof.
  intros m IH. unfold consis_complete_at.
  intros N Δ1 Δ2 Θ0 P0 P κ Θ Ψ Qb Hm Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf
    Hinc Hwfth Hnfdth HΨ Hjoin Hrs Hrp.
  subst m.
  (* ---- Layer 0a: flexible SUBJECT — parts 2/3 (t breaks the tie) ---- *)
  destruct (a_flex_shape_dec HwfP) as [[β [-> Hfβ]] | HnfP].
  { destruct (a_flex_shape_dec HwfP0) as [[β10 [-> Hfδ0]] | HnfP0].
    - (* C-Flex : both hatted — part 2 (unification). *)
      assert (Hjoin' : empty ⨟ Θ ⊢ₛᵃ
                (pskl_to_uskl (msubst_pskl κ (pskl_var_f β))) ∼ Qb)
        by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
      assert (Hjoin'' : empty ⨟ Θ ⊢ₛᵃ
                (ptyp_to_uskl_syn (msubst_lookup κ β)) ∼ Qb).
      { replace (msubst_pskl κ (pskl_var_f β))
          with (ptyp_to_pskl (msubst_lookup κ β)) in Hjoin' by reflexivity.
        rewrite pskl_to_uskl_ptyp in Hjoin'. exact Hjoin'. }
      assert (Hmβ : mono_ptyp (msubst_lookup κ β))
        by (eapply a_inc_lookup_mono; exact Hinc).
      assert (Hmδ0 : mono_ptyp (msubst_lookup κ β10))
        by (eapply a_inc_lookup_mono; exact Hinc).
      apply ad_refine_syn_f_forget in Hrs.
      replace (msubst_pskl κ (pskl_var_f β10))
        with (ptyp_to_pskl (msubst_lookup κ β10)) in Hrs by reflexivity.
      rewrite (ptyp_to_bskl_inh_syn_eq Hmδ0) in Hrs.
      destruct (refine_mono_join Hrs Hwfth (A := msubst_lookup κ β10)
                  eq_refl Hmδ0) as [C [HmC [HeqQb HeqδC]]].
      subst Qb.
      destruct (consis_mono_join Hjoin'' Hwfth (A := msubst_lookup κ β)
                  eq_refl Hmβ) as [C' [HmC' [HeqQb' HeqβC']]].
      assert (HCC : C = C')
        by (apply ptyp_to_bskl_syn_inj; auto).
      subst C'.
      assert (Heqββ1 : Θ ⊢ (msubst_lookup κ β) ≡ᵗ (msubst_lookup κ β10)).
      { eapply a_tyequiv__trans; [ exact HeqβC' | ].
        apply a_tyequiv__sym; exact HeqδC. }
      assert (Hlt : mu_lt (mu_unify Θ κ β β10 Θ0)
                          (mu_consis Θ κ (pskl_var_f β10) (pskl_var_f β) Θ0)).
      { unfold mu_unify, mu_consis. apply mu_lt_intro. right.
        split; [ symmetry; apply V_flex | ].
        right. split; [ reflexivity | left; lia ]. }
      destruct (IH _ Hlt) as [_ [HuIH _]].
      destruct (HuIH N Θ0 β β10 κ Θ eq_refl Hwf0 Hfβ Hfδ0 Hinc Hwfth Heqββ1)
        as [Θ1 [Hu [Hnew Hopt']]].
      exists (pskl_var_f β), Θ1. split.
      { apply a_consis__flex. exact Hu. }
      split; [ exact Hnew | ].
      intros κ1 Hid Hinc1.
      destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ Hie]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      (* precision recovery for the hatted output (prop_precise_recover) *)
      assert (Hbtβ0 : a_binds_tvar β Θ0) by (right; exact Hfβ).
      assert (Hwfvβ : a_wf_ptyp Θ1 (msubst_lookup κ1 β))
        by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtβ0 ]).
      rewrite (msubst_lookup_id β Hid) in Hwfvβ.
      assert (HbtβΘ1 : a_binds_tvar β Θ1) by (inversion Hwfvβ; assumption).
      destruct (a_unify_sound Hu Hwf0) as [_ [Hwf1 _]].
      try unfold ad_precise_f.
      apply ad_refine_syn_f_of_plain_no_hole;
        [ | apply pskl_to_bskl_inh_no_hole, bskl_to_pskl_no_hole,
            msubst_bskl_no_hole; simpl; exact I ].
      eapply consis_precise_via_join with (Θ0 := Θ0) (κ1 := κ1);
        [ exact Hwfth | exact Hfβ | exact Hinc | exact HbtβΘ1
        | exact Hζ | exact Hwf1 | exact Hie
        | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfβ ]
        | apply (msubst_lookup_id β Hid)
        | exact Hjoin' ].
    - (* C-FlexL : hatted subject, non-flex input — part 3 (assignment).
         The callee's join is built from the competing solution by the
         refine→join mono bridge [refine_inh_mono_consis] (design doc §9.1)
         plus the Q-side mono transport [tyequiv_mono_consis_transport_q];
         precision recovers by [consis_precise_via_join]. *)
      assert (Hjoin' : empty ⨟ Θ ⊢ₛᵃ
                (pskl_to_uskl (msubst_pskl κ (pskl_var_f β))) ∼ Qb)
        by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
      assert (Hjoin'' : empty ⨟ Θ ⊢ₛᵃ
                (ptyp_to_uskl_syn (msubst_lookup κ β)) ∼ Qb).
      { replace (msubst_pskl κ (pskl_var_f β))
          with (ptyp_to_pskl (msubst_lookup κ β)) in Hjoin' by reflexivity.
        rewrite pskl_to_uskl_ptyp in Hjoin'. exact Hjoin'. }
      assert (Hmβ : mono_ptyp (msubst_lookup κ β))
        by (eapply a_inc_lookup_mono; exact Hinc).
      (* the join target is a monotype painting: Qb = syn C, κβ̂ ≡ᵗ C *)
      destruct (consis_mono_join Hjoin'' Hwfth (A := msubst_lookup κ β)
                  eq_refl Hmβ) as [C [HmC [HeqQb HeqβC]]].
      subst Qb.
      (* refine→join bridge on the Δ1-refinement *)
      apply ad_refine_syn_f_forget in Hrs.
      assert (Hbr : empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P0))
                      ∼ (ptyp_to_bskl_syn C)).
      { eapply refine_inh_mono_consis;
          [ exact Hrs | exact Hwfth
          | apply mono_ptyp_to_bskl_syn; exact HmC
          | reflexivity
          | intros α Hα; left; eapply a_inc_binds_tvar;
              [ exact Hinc | apply Hrig; clear - Hα; fsetdec ] ]. }
      (* transport the join target from C to κβ̂ along the equivalence *)
      assert (Hvβ : forall α, α `in` ftvar_in_ptyp (msubst_lookup κ β) ->
                              a_binds_tvar α Θ).
      { intros α Hα. eapply a_wf_ptyp_ftv_tvarish; [ | exact Hα ].
        eapply a_inc_lookup_wf;
          [ exact Hinc | exact Hwf0 | right; exact Hfβ ]. }
      destruct (tyequiv_mono_consis_transport_q HeqβC Hwfth Hmβ Hvβ)
        as [Htq _].
      assert (Hjoin3 : empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P0))
                        ∼ (ptyp_to_bskl_syn (msubst_lookup κ β)))
        by (apply Htq; exact Hbr).
      (* the measure: V constant (pairing), n constant, t breaks the tie *)
      assert (Hlt : mu_lt (mu_assign Θ κ β P0 nil Θ0)
                          (mu_consis Θ κ P0 (pskl_var_f β) Θ0)).
      { unfold mu_assign, mu_consis. apply mu_lt_intro. right.
        split; [ symmetry; apply V_flexL | ].
        right. split; [ reflexivity | left; lia ]. }
      assert (Hdom : dom (nil : aenv) [<=] ftvar_in_pskl P0)
        by (simpl; clear; fsetdec).
      destruct (IH _ Hlt) as [_ [_ HaIH]].
      destruct (HaIH N Θ0 nil β P0 κ Θ eq_refl a_decls__nil Hwf0 Hfβ
                     HwfP0 HnfP0 Hdom Hinc Hwfth Hjoin3)
        as [Θ1 [Ha [Hnew Hopt']]].
      exists (pskl_var_f β), Θ1. split.
      { apply a_consis__flex_l; [ exact HnfP0 | exact Ha ]. }
      split;
        [ intros γ Hγ; destruct (Hnew γ Hγ) as [Hin | Hni];
          [ left; simpl_env in Hin; exact Hin | right; exact Hni ] | ].
      intros κ1 Hid Hinc1.
      destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ Hie]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      (* precision recovery for the hatted output (prop_precise_recover) *)
      assert (Hbtβ0 : a_binds_tvar β Θ0) by (right; exact Hfβ).
      assert (Hwfvβ : a_wf_ptyp Θ1 (msubst_lookup κ1 β))
        by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtβ0 ]).
      rewrite (msubst_lookup_id β Hid) in Hwfvβ.
      assert (HbtβΘ1 : a_binds_tvar β Θ1) by (inversion Hwfvβ; assumption).
      assert (Hwf1 : a_wf_aenv Θ1)
        by (eapply a_assign_preserves_wf;
              [ exact Ha | apply a_decls__nil | exact Hwf0 | exact HwfP0 ]).
      try unfold ad_precise_f.
      apply ad_refine_syn_f_of_plain_no_hole;
        [ | apply pskl_to_bskl_inh_no_hole, bskl_to_pskl_no_hole,
            msubst_bskl_no_hole; simpl; exact I ].
      eapply consis_precise_via_join with (Θ0 := Θ0) (κ1 := κ1);
        [ exact Hwfth | exact Hfβ | exact Hinc | exact HbtβΘ1
        | exact Hζ | exact Hwf1 | exact Hie
        | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfβ ]
        | apply (msubst_lookup_id β Hid)
        | exact Hjoin' ]. }
  (* ---- Layer 0b: flexible INPUT, non-flex subject : C-FlexR --------- *)
  destruct (a_flex_shape_dec HwfP0) as [[β10 [-> Hfδ0]] | HnfP0].
  { (* part 3 (assignment β1̂0 ≔ P): the input β1̂0's image is a monotype, so
       [refine_mono_join] reads Qb = syn C off the Δ1-refinement and the
       join's TARGET transports from C to κβ1̂0 along the equivalence
       ([tyequiv_mono_consis_transport_q] — general subject); precision by
       [consis_precise_via_refine]. *)
    assert (Hjoin' : empty ⨟ Θ ⊢ₛᵃ
              (pskl_to_uskl (msubst_pskl κ P)) ∼ Qb)
      by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
    assert (Hmδ0 : mono_ptyp (msubst_lookup κ β10))
      by (eapply a_inc_lookup_mono; exact Hinc).
    (* the Δ1-refinement's source is a monotype painting: Qb = syn C *)
    pose proof Hrs as Hrs2.
    apply ad_refine_syn_f_forget in Hrs2.
    replace (msubst_pskl κ (pskl_var_f β10))
      with (ptyp_to_pskl (msubst_lookup κ β10)) in Hrs2 by reflexivity.
    rewrite (ptyp_to_bskl_inh_syn_eq Hmδ0) in Hrs2.
    destruct (refine_mono_join Hrs2 Hwfth (A := msubst_lookup κ β10)
                eq_refl Hmδ0) as [C [HmC [HeqQb HeqδC]]].
    (* transport the join target from C to κβ1̂0 along the equivalence *)
    assert (Hvδ : forall α, α `in` ftvar_in_ptyp (msubst_lookup κ β10) ->
                            a_binds_tvar α Θ).
    { intros α Hα. eapply a_wf_ptyp_ftv_tvarish; [ | exact Hα ].
      eapply a_inc_lookup_wf;
        [ exact Hinc | exact Hwf0 | right; exact Hfδ0 ]. }
    destruct (tyequiv_mono_consis_transport_q HeqδC Hwfth Hmδ0 Hvδ)
      as [Htq _].
    assert (Hjoin3 : empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P))
                      ∼ (ptyp_to_bskl_syn (msubst_lookup κ β10))).
    { apply Htq. rewrite <- HeqQb. exact Hjoin'. }
    (* the measure: V constant (pairing), n constant, t breaks the tie *)
    assert (Hlt : mu_lt (mu_assign Θ κ β10 P nil Θ0)
                        (mu_consis Θ κ (pskl_var_f β10) P Θ0)).
    { unfold mu_assign, mu_consis. apply mu_lt_intro. right.
      split; [ symmetry; apply V_flexR | ].
      right. split; [ reflexivity | left; lia ]. }
    assert (Hdom : dom (nil : aenv) [<=] ftvar_in_pskl P)
      by (simpl; clear; fsetdec).
    destruct (IH _ Hlt) as [_ [_ HaIH]].
    destruct (HaIH N Θ0 nil β10 P κ Θ eq_refl a_decls__nil Hwf0 Hfδ0
                   HwfP HnfP Hdom Hinc Hwfth Hjoin3)
      as [Θ1 [Ha [Hnew Hopt']]].
    exists (pskl_var_f β10), Θ1. split.
    { apply a_consis__flex_r; [ exact HnfP | exact Ha ]. }
    split;
      [ intros γ Hγ; destruct (Hnew γ Hγ) as [Hin | Hni];
        [ left; simpl_env in Hin; exact Hin | right; exact Hni ] | ].
    intros κ1 Hid Hinc1.
    destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ Hie]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
    (* precision recovery for the hatted output, off the Δ1-refinement *)
    assert (Hbtδ00 : a_binds_tvar β10 Θ0) by (right; exact Hfδ0).
    assert (Hwfvδ : a_wf_ptyp Θ1 (msubst_lookup κ1 β10))
      by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtδ00 ]).
    rewrite (msubst_lookup_id β10 Hid) in Hwfvδ.
    assert (HbtδΘ1 : a_binds_tvar β10 Θ1) by (inversion Hwfvδ; assumption).
    assert (Hwf1 : a_wf_aenv Θ1)
      by (eapply a_assign_preserves_wf;
            [ exact Ha | apply a_decls__nil | exact Hwf0 | exact HwfP ]).
    try unfold ad_precise_f.
    apply ad_refine_syn_f_of_plain_no_hole;
      [ | apply pskl_to_bskl_inh_no_hole, bskl_to_pskl_no_hole,
          msubst_bskl_no_hole; simpl; exact I ].
    eapply consis_precise_via_refine with (Θ0 := Θ0) (κ1 := κ1);
      [ exact Hwfth | exact Hfδ0 | exact Hinc | exact HbtδΘ1
      | exact Hζ | exact Hwf1 | exact Hie
      | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfδ0 ]
      | apply (msubst_lookup_id β10 Hid)
      | exact Hrs ]. }
  (* ---- Layer 0c: P0 = ◇ : C-GhostR ---------------------------------- *)
  destruct (pskl_eq_dec P0 pskl_hole) as [-> | HneP0hole].
  { (* axiom node [a_consis__ghost_r].  The side condition
       [Δ1 ∩ ftv(P) = ∅] is the mirror rigid-ftv chase, through the JOIN
       ([ad_pat_consis_rigid_ftv_rev]) against the Δ1-hygiene of the hole
       fill in Hrs; precision re-inherits the Δ2-refinement through the
       join by [refine_join_reinherit]. *)
    assert (Hjoin' : empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P)) ∼ Qb)
      by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
    change (ad_refine_syn_f Δ1 Θ Δ1 bskl_hole Qb) in Hrs.
    (* Qb is a syn-painting fixed point (its refinement source is ◇) *)
    assert (HQb : pskl_to_bskl_syn (bskl_to_pskl Qb) = Qb).
    { inversion Hrs; subst.
      - rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity.
      - simpl. reflexivity. }
    (* the ftv chase for the GhostR side condition *)
    assert (Hside : forall α, α `in` Δ1 -> α `notin` ftvar_in_pskl P).
    { intros α HinΔ1 HinP.
      assert (HbX0 : binds α abind_tvar Θ0)
        by (apply Hrig; clear - HinΔ1; fsetdec).
      assert (HbX : binds α abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      assert (HXnd : α `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      assert (Hdefs : forall β τ, binds β (abind_flex_mono_def τ) Θ ->
                                  α `notin` ftvar_in_ptyp τ).
      { intros β τ Hb. pose proof (Hnfdth _ _ Hb) as Hd.
        clear - Hd HinΔ1. fsetdec. }
      assert (HninQb : α `notin` ftvar_in_bskl Qb).
      { inversion Hrs; subst.
        - (* hole : the Δ1-hygiene of the fill *)
          match goal with
          | Hint : Δ1 ∩ (ftvar_in_pskl ?Pf) [=] empty |- _ =>
              pose proof (ftvar_in_bskl_syn Pf) as Hfe;
              clear - Hint HinΔ1 Hfe; fsetdec
          end.
        - (* flex_r : Qb is a defined flexible, never the rigid α *)
          simpl.
          match goal with
          | Hbr : binds ?α0 (abind_flex_mono_def _) Θ |- _ =>
              assert (Hne : α <> α0)
                by (intro Heq; subst;
                    pose proof (binds_unique _ _ _ _ _ HbX Hbr
                                  (a_wf_aenv_uniq Hwfth)) as Hcon;
                    discriminate)
          end.
          clear - Hne; fsetdec. }
      assert (HinκP : α `in` ftvar_in_pskl (msubst_pskl κ P))
        by (apply msubst_pskl_ftv_keep; assumption).
      assert (HninS : α `notin`
                ftvar_in_uskl (pskl_to_uskl (msubst_pskl κ P))).
      { eapply ad_pat_consis_rigid_ftv_rev;
          [ exact Hwfth | exact HbX | exact Hdefs | exact Hjoin'
          | exact HninQb ]. }
      pose proof (ftvar_in_uskl_pskl (msubst_pskl κ P)) as Hfe2.
      clear - HninS HinκP Hfe2. fsetdec. }
    exists P, Θ0. split.
    { apply a_consis__ghost_r.
      apply inter_empty_pointwise. exact Hside. }
    split; [ intros γ Hγ; left; exact Hγ | ].
    intros κ1 Hid Hinc1. exists κ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    (* precision by the re-inherit bridge (subset goal second, AFTER the
       bridge instantiates the Δ) *)
    assert (HwfκP : Θ ⨟ Δ2 ⊢ₚₛᵃ (msubst_pskl κ P)).
    { eapply a_wf_pskl_delta_mono;
        [ eapply a_wf_pskl_msubst_inc;
            [ exact Hinc | exact Hwf0 | exact HwfP
            | intros α Hα; exfalso; clear - Hα; fsetdec ]
        | clear; fsetdec ]. }
    unfold ad_precise_f.
    rewrite bskl_to_pskl_msubst_bskl.
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    eapply ad_refine_syn_f_delta_mono with (Δ0 := Δ2);
      [ | clear; fsetdec ].
    eapply ad_refine_syn_f_fextend_ftv;
      [ eapply refine_join_reinherit with (Θj := Θ);
          [ exact Hrp | exact Hwfth | exact Hwfth
          | intros x b Hb; exact Hb
          | exact HwfκP
          | rewrite HQb; exact Hjoin' ]
      | ].
    intros α1 Hα1.
    destruct (AtomSetProperties.In_dec α1 Δ2) as [Hα1Δ2 | Hα1Δ2];
      [ left; exact Hα1Δ2 | right ].
    assert (Hα1Δ1 : α1 `in` Δ1) by (clear - Hα1 Hα1Δ2; fsetdec).
    assert (Hbγ : binds α1 abind_tvar Θ)
      by (eapply a_inc_binds_tvar; [ exact Hinc | ];
          apply Hrig; clear - Hα1Δ1; fsetdec).
    split.
    + assert (Hnq : α1 `notin` ftvar_in_bskl Qb)
        by (eapply ad_refine_syn_f_hole_src_target_ftv;
            [ exact Hrs | exact Hwfth
            | clear - Hα1Δ1; fsetdec | exact Hbγ ]).
      pose proof (ftvar_in_bskl_inh (bskl_to_pskl Qb)) as Hfe.
      pose proof (ftvar_in_pskl_bskl_to_pskl Qb) as Hfe2.
      clear - Hnq Hfe Hfe2. fsetdec.
    + intros β τ Hb.
      pose proof (Hnfdth β τ Hb) as Hi.
      clear - Hi Hα1Δ1. fsetdec. }
  (* ---- Layer 0d: P0 = ∀◇.P0', P guarded : C-UnivGhostR -------------- *)
  assert (Hthdec : (exists P0', P0 = pskl_tophole P0') \/
                   (forall P0', P0 <> pskl_tophole P0')).
  { destruct P0; try (right; intros ? Hc; discriminate).
    left. eexists. reflexivity. }
  destruct Hthdec as [[P0' ->] | Hnth].
  { pose proof (a_wf_pskl_lc HwfP) as HlcP.
    assert (Hgdec : guarded_pskl P \/ ~ guarded_pskl P).
    { destruct P; try (right; intro Hg; inversion Hg; fail).
      - left; apply guarded_pskl__unit.
      - left; apply guarded_pskl__var.
      - left; inversion HlcP; apply guarded_pskl__arrow; assumption. }
    destruct Hgdec as [HgP | HngP].
    - (* C-UnivGhostR : strip the input's ∀◇, V drops on the input side. *)
      assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0') by (inversion HwfP0; assumption).
      assert (Hgκ : guarded_pskl (msubst_pskl κ P))
        by (eapply guarded_pskl_msubst_inc; eauto).
      assert (HlcQb : lc_bskl Qb) by (eapply ad_refine_syn_f_lc_r; eauto).
      assert (HgQb : guarded_bskl Qb)
        by (eapply ad_pat_consis_guarded_r; eauto).
      change (ad_refine_syn_f Δ1 Θ Δ1
                (bskl_tophole (pskl_to_bskl_inh (msubst_pskl κ P0'))) Qb)
        in Hrs.
      assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
                (pskl_to_bskl_inh (msubst_pskl κ P0')) Qb)
        by (eapply ad_refine_syn_f_tophole_guarded_inv; eauto).
      assert (Hlt : mu_lt (mu_consis Θ κ P0' P Θ0)
                          (mu_consis Θ κ (pskl_tophole P0') P Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left.
        unfold V_consis.
        pose proof (Vpskl_tophole_lt Θ κ P0'). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH N Δ1 Δ2 Θ0 P0' P κ Θ Ψ Qb eq_refl Hwf0 HwfP0' HwfP
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hjoin Hrs' Hrp)
        as [P1 [Θ1 [Hc [Hnew Hopt']]]].
      exists P1, Θ1. split.
      { apply a_consis__univ_ghost_r;
          [ exact HgP | exact HnfP | exact Hc ]. }
      split; [ exact Hnew | exact Hopt' ].
    - (* P unguarded: fall through to the main dispatch. *)
      eapply (consis_complete_core Hjoin);
        try eassumption; try reflexivity.
      intros P0'' Heq0 Hg. inversion Heq0; subst P0''. exact (HngP Hg). }
  (* ---- Layer 1: the main dispatch ----------------------------------- *)
  eapply (consis_complete_core Hjoin);
    try eassumption; try reflexivity.
  intros P0'' Heq0 Hg. exact (Hnth P0'' Heq0).
Qed.

(* ===================================================================== *)
(*  §4  The bundle, by well-founded induction on μ                        *)
(* ===================================================================== *)

Theorem complete_mu : forall m, complete_at m.
Proof.
  intro m; induction (mu_lt_wf m) as [m _ IH].
  repeat split;
    [ apply consis_complete_step
    | apply unify_complete_step
    | apply assign_complete_step ]; exact IH.
Qed.

(* ===================================================================== *)
(*  §5  Corollaries                                                       *)
(* ===================================================================== *)

(** The join-shaped statement the earlier scaffold stated directly (kept
    verbatim for downstream compatibility); now an instance of the bundle. *)
Lemma consis_complete : forall Ψ Θ R Qb,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Qb ->
  forall Δ1 Δ2 Θ0 P0 P κ,
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    κ ∷ Θ0 ⊑ Θ ->
    a_wf_aenv Θ ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    R = pskl_to_uskl (msubst_pskl κ P) ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl κ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl κ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           ad_precise_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb)).
Proof.
  intros Ψ Θ R Qb Hj Δ1 Δ2 Θ0 P0 P κ
    Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ HeqS Hrs Hrp.
  subst R.
  destruct (complete_mu (mu_consis Θ κ P0 P Θ0)) as [Hc _].
  (* the avoid set is vacuous at the top: [N := ∅] *)
  destruct (Hc empty Δ1 Δ2 Θ0 P0 P κ Θ Ψ Qb eq_refl Hwf0 HwfP0 HwfP Hrig
              Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs Hrp)
    as [P1 [Θ1 [Hcons [_ Hopt]]]].
  exists P1, Θ1. split; [ exact Hcons | exact Hopt ].
Qed.

(* ===================================================================== *)
(*  Top-level completeness of consistency, DERIVED from the bundle by     *)
(*  instantiating the augmentation to Δ1 = Δ2 = ∅, Ψ = ∅.  The paper's    *)
(*  unaugmented statement (this is the [TODO] the old bundle left open).  *)
(* ===================================================================== *)
Lemma a_consis_complete_thm : forall Θ0 P0 P,
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  forall κ Θ Qb,
    κ ∷ Θ0 ⊑ Θ ->
    a_wf_aenv Θ ->
    empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P)) ∼ Qb ->
    ad_refine_syn_f empty Θ empty (pskl_to_bskl_inh (msubst_pskl κ P0)) Qb ->
    ad_refine_pskl_f empty Θ empty (msubst_pskl κ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis empty empty Θ0 P0 P P1 Θ1 /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           Θ ⨟ empty ⊢ₚᵣᵃ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb)).
Proof.
  intros Θ0 P0 P Hwf0 HwfP0 HwfP κ Θ Qb Hinc Hwfth Hjoin Hrs Hrp.
  (* [Δ1 ∪ Δ2 = ∅], so rigid / no_flex_dep / flex_above_free are vacuous. *)
  assert (Hcc : exists P1 Θ1,
      a_consis empty empty Θ0 P0 P P1 Θ1 /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           ad_precise_f (empty `union` empty) Θ (empty `union` empty)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb))).
  { eapply consis_complete with (Δ1 := empty) (Δ2 := empty).
    all: try (first [ eassumption | reflexivity ]).
    all: try (intros α Hα; exfalso; clear - Hα; fsetdec).  (* rigid: α ∈ ∅ *)
    all: repeat intro; fsetdec. }     (* no_flex_dep / flex_above_free / Ψ *)
  destruct Hcc as [P1 [Θ1 [Hc Hopt]]].
  exists P1, Θ1. split; [ exact Hc | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
  exists ζ. repeat split; try assumption.
  (* forget the hygiene, then shrink [∅ ∪ ∅ ⊆ ∅]. *)
  apply ad_precise_f_forget in Hprec.
  eapply ad_refine_syn_delta_mono; [ exact Hprec | clear; fsetdec ].
Qed.
