(* ===================================================================== *)
(*  COMPLETENESS of consistency / unification / assignment                *)
(*  (thm:complete-consistency; paper proof: consistency-proofs.tex        *)
(*  :2225-3167 "Completeness of Consistency", all three parts).           *)
(*                                                                        *)
(*  The paper proceeds "by mutual induction for the three parts":         *)
(*    part 1 (consistency)  — case analysis on the last rule of the       *)
(*      declarative join derivation, with the special cases peeled first  *)
(*      (:2566-2580): P₀ = ◇ → GhostR; P₀ = ⊤◇.P₀' with P guarded →       *)
(*      UnivGhostR; P or P₀ flexible → parts 2/3.                          *)
(*    part 2 (unification)  — walk of the context Θ₀.                      *)
(*    part 3 (assignment)   — walk of the context pair Θ₀ ∣ Ξ.             *)
(*                                                                        *)
(*  [paper-gap] The paper's three stated induction subjects do NOT        *)
(*  combine into a well-founded order (docs/DESIGN-completeness-          *)
(*  measure.md §3): the back-edges Flex-Flex-Assign / Assign-Assign hand  *)
(*  part 1 a declarative derivation that can be strictly LARGER than the  *)
(*  caller's, and UnivGhostR recurses with the SAME one.  The repaired    *)
(*  measure (design doc §4, infrastructure green in prop_consis_exist.v)  *)
(*                                                                        *)
(*      μ = (V, n, t, k)   lexicographic on ℕ⁴                            *)
(*                                                                        *)
(*  runs on V = the size of the node's two skeletons AS THE SOLUTION      *)
(*  SEES THEM (⇓ˢ[Θ] ∘ θ): V strictly decreases on every consistency-      *)
(*  internal edge, is exactly constant on every cross/back-edge — where   *)
(*  n = |Θ₀| (resp. |Ξ|+|Θ₀|) then strictly decreases; t breaks the       *)
(*  consis→unify/assign tie; k breaks Assign-Depend.  All 21 edges are    *)
(*  verified in the design doc §5.                                        *)
(*                                                                        *)
(*  The statement is the paper's FUSED one (:2246-2255): existence of the *)
(*  algorithmic derivation TOGETHER WITH the factoring (ζ, a_inc_equiv)   *)
(*  and — for consistency — the PRECISION of the output (⊑ against the    *)
(*  competing solution's join target), on the AUGMENTED problem           *)
(*  (Δ₁;Δ₂;Ψ;Θ₀;P₀;S) of :2230-2242.  COMPLETE — no admits; the whole      *)
(*  bundle (and [a_consis_complete_thm]) is axiom-free.                   *)
(* ===================================================================== *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_precise_recover.
Require Import src.frost.algo.prop_consis_rename.

Set Implicit Arguments.

(* ##################################################################### *)
(*  PART A — THE μ-MEASURE (formerly algo/prop_consis_exist.v, merged     *)
(*  2026-07-18; that file and the deprecated OPT-bundle file               *)
(*  prop_consis_complete.v were folded into this one).                     *)
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
        (reflexivity at the solved θ(α̂[τ/β̂])).
      - UnivGhostR (consis → consis): the premise reuses the caller's
        derivation IDENTICALLY (the ⊤◇ is peeled from the problem, not from
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

      V = size of the SOLVED skeletons  size (⇓ˢ[Θ] (θ X)) + size (⇓ˢ[Θ] (θ Y))
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
    solution's metasubstitution [θ], then through the target context [Θ]'s own
    definitions ([⇓ˢ]).  For a variable subject we use its metasubstitution image
    ([msubst_lookup θ α], a [ptyp]) and the type-level normal form [⇓ᵗ]. *)
Definition Vpskl (Θ : aenv) (θ : metasubst) (P : pskl) : nat :=
  size_pskl (⇓ˢ[Θ] (msubst_pskl θ P)).

Definition Vptyp (Θ : aenv) (θ : metasubst) (A : ptyp) : nat :=
  size_ptyp (⇓ᵗ[Θ] (msubst_ptyp θ A)).

Definition Vvar (Θ : aenv) (θ : metasubst) (α : atom) : nat :=
  size_ptyp (⇓ᵗ[Θ] (msubst_lookup θ α)).

(** The [V] component of the three node kinds (the "pair of skeletons" of the
    design doc §1: consis → [(P,P0)], unify → [(α̂,β̂)], assign → [(P,α̂)]). *)
Definition V_consis (Θ : aenv) (θ : metasubst) (P0 P : pskl) : nat :=
  Vpskl Θ θ P + Vpskl Θ θ P0.
Definition V_unify (Θ : aenv) (θ : metasubst) (α β : atom) : nat :=
  Vvar Θ θ α + Vvar Θ θ β.
Definition V_assign (Θ : aenv) (θ : metasubst) (α : atom) (P : pskl) : nat :=
  Vpskl Θ θ P + Vvar Θ θ α.

(** [Vvar] is [Vptyp] on the variable seen as a type. *)
Lemma Vvar_ptyp : forall Θ θ α,
  Vvar Θ θ α = Vptyp Θ θ (ptyp_var_f α).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  §3a  Homomorphism of [Vpskl] — the consistency-internal V-decreases    *)
(* ===================================================================== *)

(** [⇓ˢ ∘ θ] commutes with every skeleton former, because both [msubst_pskl]s
    do; hence [size_pskl] adds exactly the shape's own node.  These are the
    strict V-decrease facts of design doc §5.1 (Arrow / Forall / UnivGhost /
    Tophole edges). *)
Lemma Vpskl_arrow : forall Θ θ P1 P2,
  Vpskl Θ θ (pskl_arrow P1 P2) = 1 + Vpskl Θ θ P1 + Vpskl Θ θ P2.
Proof. reflexivity. Qed.

Lemma Vpskl_all_syn : forall Θ θ P,
  Vpskl Θ θ (pskl_all_syn P) = 1 + Vpskl Θ θ P.
Proof. reflexivity. Qed.

Lemma Vpskl_tophole : forall Θ θ P,
  Vpskl Θ θ (pskl_tophole P) = 1 + Vpskl Θ θ P.
Proof. reflexivity. Qed.

(** Every skeleton has positive [Vpskl] (its normal form is a non-empty
    skeleton), so a former's component is STRICTLY smaller than the whole. *)
Lemma Vpskl_pos : forall Θ θ P, 1 <= Vpskl Θ θ P.
Proof. intros. unfold Vpskl. apply size_pskl_min. Qed.

Lemma Vpskl_arrow_lt1 : forall Θ θ P1 P2,
  Vpskl Θ θ P1 < Vpskl Θ θ (pskl_arrow P1 P2).
Proof. intros. rewrite Vpskl_arrow. pose proof (Vpskl_pos Θ θ P2). lia. Qed.

Lemma Vpskl_arrow_lt2 : forall Θ θ P1 P2,
  Vpskl Θ θ P2 < Vpskl Θ θ (pskl_arrow P1 P2).
Proof. intros. rewrite Vpskl_arrow. pose proof (Vpskl_pos Θ θ P1). lia. Qed.

Lemma Vpskl_all_syn_lt : forall Θ θ P,
  Vpskl Θ θ P < Vpskl Θ θ (pskl_all_syn P).
Proof. intros. rewrite Vpskl_all_syn. lia. Qed.

Lemma Vpskl_tophole_lt : forall Θ θ P,
  Vpskl Θ θ P < Vpskl Θ θ (pskl_tophole P).
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
Lemma Vpskl_var : forall Θ θ α,
  Vpskl Θ θ (pskl_var_f α) = Vvar Θ θ α.
Proof.
  intros. unfold Vpskl, Vvar. cbn [msubst_pskl].
  rewrite msubst_pskl_ptyp_to_pskl. apply size_ptyp_to_pskl.
Qed.

(** [FlexL]: [consis(Θ0; P0; α̂)] -> [assign(Θ0; ·; α̂; P0)].  [V] is exactly
    preserved (the two skeletons swap roles). *)
Lemma V_flexL : forall Θ θ α P0,
  V_consis Θ θ P0 (pskl_var_f α) = V_assign Θ θ α P0.
Proof. intros. unfold V_consis, V_assign. rewrite Vpskl_var. lia. Qed.

(** [FlexR]: [consis(Θ0; α̂; P)] -> [assign(Θ0; ·; α̂; P)]. *)
Lemma V_flexR : forall Θ θ α P,
  V_consis Θ θ (pskl_var_f α) P = V_assign Θ θ α P.
Proof. intros. unfold V_consis, V_assign. rewrite Vpskl_var. lia. Qed.

(** [Flex]: [consis(Θ0; β̂; α̂)] -> [unify(Θ0; α̂; β̂)]. *)
Lemma V_flex : forall Θ θ α β,
  V_consis Θ θ (pskl_var_f β) (pskl_var_f α) = V_unify Θ θ α β.
Proof. intros. unfold V_consis, V_unify. rewrite !Vpskl_var. lia. Qed.

(* ===================================================================== *)
(*  §3c  V-CONSTANCY under (M1) and (M2) — the back-edges and Arrow's 2nd  *)
(* ===================================================================== *)

(** (M1) [Vpskl] is invariant under passing an [a_inc_equiv]alent
    metasubstitution — this is what makes [Arrow]'s SECOND premise (which runs
    at the extended [Θ1] with [θ1 ≡ θ] on [Θ0]) leave [V] untouched, so the
    context-blow-up of design doc §3.1 is simply not measured. *)
Lemma Vpskl_inc_equiv : forall Θ0 θ1 θ2 Θ P,
  a_inc_equiv Θ0 θ1 θ2 Θ ->
  a_wf_aenv Θ0 -> a_wf_aenv Θ -> a_wf_pskl Θ0 P ->
  Vpskl Θ θ1 P = Vpskl Θ θ2 P.
Proof.
  intros. unfold Vpskl. eapply a_inc_equiv_downarrow_pskl_size; eauto.
Qed.

Lemma Vptyp_inc_equiv : forall Θ0 θ1 θ2 Θ A,
  a_inc_equiv Θ0 θ1 θ2 Θ ->
  a_wf_aenv Θ0 -> a_wf_aenv Θ -> a_wf_ptyp Θ0 A ->
  Vptyp Θ θ1 A = Vptyp Θ θ2 A.
Proof.
  intros. unfold Vptyp. eapply a_inc_equiv_downarrow_ptyp_size; eauto.
Qed.

(** (M2) The BACK-EDGE move [X[τ/γ̂] ↦ X], with the outer metasubstitution
    dropping its head [γ̂ ↦ τ'].  [V] is exactly preserved — the back-edge merely
    unfolds a definition the solution had already unfolded ([Flex-Flex-Assign],
    [Assign-Assign], design doc §5.4).  The [≡ᵗ] premise is [a_inc__flex_def]'s. *)
Lemma Vpskl_backedge : forall Θ θ0 γ τ τ' P,
  a_wf_aenv Θ ->
  Θ ⊢ τ' ≡ᵗ (msubst_ptyp θ0 τ) ->
  Vpskl Θ θ0 (subst_pskl_in_pskl (ptyp_to_pskl τ) γ P)
  = Vpskl Θ ((γ, τ') :: θ0) P.
Proof.
  intros. unfold Vpskl. eapply downarrow_subst_pskl_size; eauto.
Qed.

Lemma Vvar_backedge : forall Θ θ0 γ τ τ' α,
  a_wf_aenv Θ ->
  Θ ⊢ τ' ≡ᵗ (msubst_ptyp θ0 τ) ->
  Vptyp Θ θ0 (subst_ptyp_in_ptyp τ γ (ptyp_var_f α))
  = Vptyp Θ ((γ, τ') :: θ0) (ptyp_var_f α).
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
  - pick fresh X.
    apply lc_pskl_all_syn_exists with (Xps1 := X).
    rewrite <- ptyp_to_pskl_open. auto.
Qed.

(** [msubst_pskl] commutes with recursive opening when the map's images are
    locally closed (they have no bound variable to be captured). *)
Lemma msubst_pskl_open_rec_lc : forall θ,
  msubst_lc θ ->
  forall P V k,
  msubst_pskl θ (open_pskl_wrt_pskl_rec k V P)
  = open_pskl_wrt_pskl_rec k (msubst_pskl θ V) (msubst_pskl θ P).
Proof.
  intros θ Hlc P;
    induction P as [ | n | X | P1 IH1 P2 IH2 | P0 IH0 | | P0 IH0 ];
    intros V k; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - symmetry.
    apply open_pskl_wrt_pskl_rec_degree_pskl_wrt_pskl.
    apply degree_pskl_wrt_pskl_O.
    apply degree_pskl_wrt_pskl_of_lc_pskl.
    apply ptyp_to_pskl_lc. apply Hlc.
Qed.

Lemma msubst_pskl_open_lc : forall θ P X,
  msubst_lc θ ->
  X `notin` dom θ ->
  msubst_pskl θ (open_pskl_wrt_pskl P (pskl_var_f X))
  = open_pskl_wrt_pskl (msubst_pskl θ P) (pskl_var_f X).
Proof.
  intros θ P X Hlc HX. unfold open_pskl_wrt_pskl.
  rewrite (msubst_pskl_open_rec_lc Hlc P (pskl_var_f X) 0).
  cbn [msubst_pskl]. rewrite msubst_lookup_notin by exact HX.
  reflexivity.
Qed.

(** [ForallInh]/[ForallSyn]/[UnivGhost1] open the body by a FRESH RIGID [α]
    added to the context.  [⇓] ignores the rigid entry ([aenv_msubst_tvar]) and
    [θ] does not touch [α] ([α ∉ dom θ]), so opening changes neither [⇓ˢ ∘ θ] nor
    the size — [V] is unchanged (design doc §4.3).  Hence the body's [V] is
    STRICTLY below the [all_syn]/[tophole]-headed parent's. *)
Lemma Vpskl_open : forall Θ ρ P α,
  a_wf_aenv Θ ->
  msubst_lc ρ ->
  α `notin` dom ρ ->
  α `notin` dom Θ ->
  Vpskl Θ ρ (open_pskl_wrt_pskl P (pskl_var_f α)) = Vpskl Θ ρ P.
Proof.
  intros Θ ρ P α Hwf Hlcρ Hαρ HαΘ. unfold Vpskl.
  assert (HαΘ' : α `notin` dom (aenv_msubst Θ))
    by (pose proof (dom_aenv_msubst Θ); clear - HαΘ H; fsetdec).
  rewrite msubst_pskl_open_lc by assumption.
  rewrite (msubst_pskl_open_lc (θ := aenv_msubst Θ));
    [ apply size_pskl_open_pskl_wrt_pskl_var
    | apply aenv_msubst_lc; exact Hwf
    | exact HαΘ' ].
Qed.

(* ===================================================================== *)
(*  §4  The STUCK-CHECK (design doc §9.2 — the paper gap)                 *)
(* ===================================================================== *)

(** A metasubstitution never ERASES a free variable outside its domain: if
    [X ∉ dom θ] and [X ∈ ftv(P)] then [X ∈ ftv(θP)].  ([θ] can only REPLACE the
    variables it is defined on; everything else survives verbatim.) *)
Lemma msubst_pskl_ftv_notin_dom : forall θ P X,
  X `notin` dom θ ->
  X `in` ftvar_in_pskl P ->
  X `in` ftvar_in_pskl (msubst_pskl θ P).
Proof.
  intros θ P;
    induction P as [ | n | Y | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros X HX Hin; simpl in *.
  - clear - Hin; fsetdec.
  - clear - Hin; fsetdec.
  - (* pskl_var_f Y : Hin forces X = Y, and Y ∉ dom θ so θ leaves it alone *)
    assert (X = Y) by (clear - Hin; fsetdec); subst Y.
    rewrite msubst_lookup_notin by exact HX. simpl. clear; fsetdec.
  - apply AtomSetImpl.union_1 in Hin. destruct Hin as [Hin | Hin].
    + assert (Hs : X `in` ftvar_in_pskl (msubst_pskl θ Pa)) by (apply IHa; auto).
      clear - Hs; fsetdec.
    + assert (Hs : X `in` ftvar_in_pskl (msubst_pskl θ Pb)) by (apply IHb; auto).
      clear - Hs; fsetdec.
  - apply IHall; assumption.
  - clear - Hin; fsetdec.
  - apply IHt; assumption.
Qed.

(** THE STUCK-CHECK, provable half (design doc §9.2, the [Assign-SkipRigid] /
    [Assign-SolveM] "occurs" obligation): a RIGID variable [β] that occurs in the
    walked skeleton [P] is preserved by ANY solution's metasubstitution [θ] into
    [Θ] — [β ∈ ftv(θP)].

    This is the "[β] is not erased" ingredient.  [a_inc] keeps a rigid variable
    rigid, so it never enters [θ]'s domain ([a_inc_tvar_notin_dom]); a variable
    [θ] does not act on survives verbatim ([msubst_pskl_ftv_notin_dom]).

    [paper-gap] The FULL not-stuck argument (that the assignment walk never
    reaches a rigid head [β ∈ ftv(P)], for which there is NO rule) closes the
    contradiction from here as follows — the two remaining ingredients are NOT
    supplied in this file (see the report / docs/PAPER-GAPS.md §9.2):

      (i)  [β ∉ ftv(θα̂)]: at the stuck head [β] is ABOVE [α̂] in the walked
           context, so [a_inc] peels [β] (via [a_inc__tvar]) before reaching
           [α̂]; hence [θα̂] is well-formed in a target BELOW [β] and cannot
           mention it.  Needs an [a_inc]-position / target-wf lemma.
      (ii) [β ∈ ftv(θα̂)]: the assignment solution's JOIN
           [empty ⨟ Θ ⊨ₛᵃ ⌊θP⌋ ≈ syn(θα̂)] against the MONOTYPE [θα̂]
           ([a_inc_lookup_mono]) transports (via [consis_refine_mono_tyequiv],
           prop_mono_bridge.v) to [θP ≡ᵗ θα̂]; combined with [β ∈ ftv(θP)]
           (this lemma) it should force [β ∈ ftv(θα̂)].  The subtlety flagged in
           the report: [≡ᵗ]'s [flex_def] rule is NOT rigid-ftv-preserving in
           general, so (ii) needs a dedicated "rigid ftv survives [≡ᵗ] into a
           definition-free-below-[β] target" lemma, not a bare [≡ᵗ] rewrite.

    (i) and (ii) contradict, so the stuck head is unreachable.  The clean,
    self-contained half — that the solution does not erase [β] — is [Qed]'d here. *)
Lemma rigid_survives_solution : forall Θ1 ρ Θ β P,
  Θ1 ≤[ ρ ] Θ ->
  a_wf_aenv Θ1 ->
  binds β abind_tvar Θ1 ->
  β `in` ftvar_in_pskl P ->
  β `in` ftvar_in_pskl (msubst_pskl ρ P).
Proof.
  intros Θ1 ρ Θ β P Hinc Hwf Hb Hin.
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
(*  (THE CRUX) a mono-join uskl(S) ≈ syn(mono C) forces ⇓ˢ[Θ]S scoped to any    *)
(*  def-closed D that scopes C — so the walked payload downarrows into the      *)
(*  sub-target.  Holes contribute no ftv; the ∀/inh cases cannot fire (C mono). *)


Lemma join_pskl_downarrow_mono_scoped : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  a_wf_aenv Θ ->
  forall S0 C D,
    S = pskl_to_uskl S0 ->
    Q = ptyp_to_bskl_syn C -> mono_ptyp C ->
    (forall α τ, binds α (abind_flex_mono_def τ) Θ -> α `in` D -> ftvar_in_ptyp τ [<=] D) ->
    ftvar_in_ptyp C [<=] D ->
    ftvar_in_pskl (⇓ˢ[ Θ ] S0) [<=] D.
Proof.
  intros Ψ Θ S Q Hc Hwf; induction Hc;
    intros S0 C0 D HeqS HeqC HmC0 Hcl HCD;
    unfold ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct S0; simpl in HeqS; try discriminate.
    simpl. clear; fsetdec.
  - (* var *)
    destruct S0; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    simpl. rewrite ftvar_in_ptyp_to_pskl.
    match goal with
    | |- context[msubst_lookup ?r ?X] =>
        replace (msubst_lookup r X) with (⇓ᵗ[ Θ ] (ptyp_var_f X)) by reflexivity
    end.
    apply downarrow_ftv_closed;
      [ exact Hwf | simpl; clear - HCD; simpl in HCD; fsetdec | exact Hcl ].
  - (* arrow *)
    destruct S0 as [ | n | X | S01 S02 | S0a | | S0b ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    inversion HmC0 as [ | | ? ? HmC1 HmC2 ]; subst.
    simpl. intros Z HZ.
    apply AtomSetImpl.union_1 in HZ. destruct HZ as [HZl | HZr].
    + apply (IHHc1 Hwf S01 C1 D eq_refl eq_refl HmC1 Hcl
               ltac:(clear - HCD; simpl in HCD; fsetdec) Z HZl).
    + apply (IHHc2 Hwf S02 C2 D eq_refl eq_refl HmC2 Hcl
               ltac:(clear - HCD; simpl in HCD; fsetdec) Z HZr).
  - (* forall_inh_tagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_inh_untagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_syn_tagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_syn *) destruct HmC0; simpl in HeqC; discriminate.
  - (* ghostg *) destruct HmC0; simpl in HeqC; discriminate.
  - (* topholeg *) destruct HmC0; simpl in HeqC; discriminate.
  - (* hole : subject is a ghost hole, ⇓ contributes no ftv *)
    destruct S0; simpl in HeqS; try discriminate.
    simpl. clear; fsetdec.
  - (* tophole *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_inh *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_drop *)
    destruct S0 as [ | | | | | | S0t ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl. apply (IHHc Hwf S0t C0 D eq_refl eq_refl HmC0 Hcl HCD).
  - (* flex_l : subject is a defined flexible *)
    destruct S0 as [ | | Xv | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) Xv = ⇓ᵗ[ Θ ] τ)
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
    apply (IHHc Hwf S0 τ D eq_refl eq_refl Hmτ Hcl Hτcl).
Qed.


(* ===================================================================== *)
(*  CONTEXT-STRENGTHENING for the join (ad_pat_consis) and skeleton-wf     *)
(*  (ad_wf_pskl) judgments — the SkipRigid / SkipTmVar walk cases move    *)
(*  the competing join from the grown target down to the sub-target.       *)
(* ===================================================================== *)


Lemma ad_wf_pskl_strengthen : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall Θ', uniq Θ ->
  (forall x, x `in` Δ -> x `notin` dom Θ) ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall X, X `in` ftvar_in_pskl P -> X `in` Δ \/ X `in` dom Θ') ->
  Θ' ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H; induction H; intros Θ' Hu Hdisj Hsub Hsc.
  - apply ad_wf_pskl__unit.
  - apply ad_wf_pskl__var.
    assert (HXin : X `in` ftvar_in_pskl (pskl_var_f X)) by (simpl; fsetdec).
    destruct (Hsc X HXin) as [HΔ | Hd]; [ left; exact HΔ | ].
    destruct H as [HΔ | Htv]; [ left; exact HΔ | ].
    right. eapply a_binds_tvar_strengthen; eauto.
  - apply ad_wf_pskl__arrow.
    + apply IHad_wf_pskl1; auto. intros X HX. apply Hsc. simpl. fsetdec.
    + apply IHad_wf_pskl2; auto. intros X HX. apply Hsc. simpl. fsetdec.
  - apply ad_wf_pskl__all with (L := L `union` dom Θ `union` dom Θ' `union` Δ).
    intros X HX. apply H0.
    + clear - HX; fsetdec.
    + exact Hu.
    + assert (HxnΘ : X `notin` dom Θ) by (clear - HX; fsetdec).
      intros y Hy. destruct (y == X) as [-> | Hyne];
        [ exact HxnΘ | apply Hdisj; clear - Hy Hyne; fsetdec ].
    + exact Hsub.
    + intros Y HY.
      destruct (Y == X) as [-> | Hne]; [ left; clear; fsetdec | ].
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f X)) as Hup.
      assert (HYP : Y `in` ftvar_in_pskl P) by (simpl in Hup; clear - HY Hup Hne; fsetdec).
      destruct (Hsc Y HYP) as [HΔ | Hd]; [ left; clear - HΔ; fsetdec | right; exact Hd ].
  - apply ad_wf_pskl__hole.
  - apply ad_wf_pskl__tophole; [ exact H | ].
    apply IHad_wf_pskl; auto.
    + intros y Hy; clear - Hy; fsetdec.
    + intros X HX. right.
      pose proof (ad_wf_pskl_ftv_tvarish H0 HX) as Htv.
      assert (HxΘ : X `in` dom Θ).
      { destruct Htv as [He | Ht]; [ clear - He; fsetdec | ].
        destruct Ht as [Hb|[Hb|[τ Hb]]]; apply binds_In in Hb; exact Hb. }
      assert (HXtop : X `in` ftvar_in_pskl (pskl_tophole P)) by (simpl; exact HX).
      destruct (Hsc X HXtop) as [HΔ | Hd]; [ | exact Hd ].
      exfalso. apply (Hdisj X HΔ). exact HxΘ.
Qed.


Ltac str_forall H0 Hu Hwf' Hsub HscS HscQ Rr Qq X HX openU openB :=
  apply H0;
  [ clear - HX; fsetdec
  | simpl_env; apply uniq_push; [ exact Hu | clear - HX; fsetdec ]
  | apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf' ]
  | apply binds_sub_cons with (e := (X ~ abind_tvar)); exact Hsub
  | intros Y HY;
    pose proof (openU Rr (uskl_var_f X)) as HupU; simpl in HupU;
    destruct (Y == X) as [-> | Hne]; [ simpl; clear; fsetdec | ];
    simpl; apply AtomSetImpl.add_2; apply HscS; clear - HY HupU Hne; fsetdec
  | intros Y HY;
    pose proof (openB Qq (bskl_var_f X)) as HupB; simpl in HupB;
    destruct (Y == X) as [-> | Hne]; [ simpl; clear; fsetdec | ];
    simpl; apply AtomSetImpl.add_2; apply HscQ; clear - HY HupB Hne; fsetdec ].

Lemma ad_pat_consis_strengthen : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  forall Θ', uniq Θ -> a_wf_aenv Θ' ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall X, X `in` ftvar_in_uskl S -> X `in` dom Θ') ->
  (forall X, X `in` ftvar_in_bskl Q -> X `in` dom Θ') ->
  Ψ ⨟ Θ' ⊨ₛᵃ S ≈ Q.
Proof.
  intros Ψ Θ S Q H; induction H;
    intros Θ' Hu Hwf' Hsub HscS HscQ; simpl in *.
  - apply ad_pat_consis__unit; auto.
  - apply ad_pat_consis__var; [ assumption | ].
    eapply a_binds_tvar_strengthen;
      [ eassumption | exact Hu | exact Hsub | apply HscS; fsetdec ].
  - eapply ad_pat_consis__arrow; [ | | exact H1 ].
    + apply IHad_pat_consis1; auto; intros X HX;
        solve [ apply HscS; fsetdec | apply HscQ; fsetdec ].
    + apply IHad_pat_consis2; auto; intros X HX;
        solve [ apply HscS; fsetdec | apply HscQ; fsetdec ].
  - eapply ad_pat_consis__forall_inh_tagged
      with (L := L `union` dom Θ `union` dom Θ'); [ | exact H1 ].
    intros X HX.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q X HX
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_inh_untagged
      with (L := L `union` dom Θ `union` dom Θ').
    intros X HX.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q X HX
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_syn_tagged
      with (L := L `union` dom Θ `union` dom Θ').
    intros X HX.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q X HX
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_syn
      with (L := L `union` dom Θ `union` dom Θ').
    intros X HX.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q X HX
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - apply ad_pat_consis__ghostg; auto.
  - apply ad_pat_consis__topholeg. apply IHad_pat_consis; auto.
  - apply ad_pat_consis__hole; auto.
    eapply ad_wf_pskl_strengthen; [ exact H0 | exact Hu | intros y Hy; clear - Hy; fsetdec | exact Hsub | ].
    intros X HX. right. apply HscQ.
    pose proof (ftvar_in_bskl_inh P) as Hb. clear - HX Hb. fsetdec.
  - apply ad_pat_consis__tophole. apply IHad_pat_consis; auto.
  - eapply ad_pat_consis__tophole_inh
      with (L := L `union` dom Θ `union` dom Θ').
    intros X HX.
    apply H0.
    + clear - HX; fsetdec.
    + simpl_env; apply uniq_push; [ exact Hu | clear - HX; fsetdec ].
    + apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf' ].
    + apply binds_sub_cons with (e := (X ~ abind_tvar)); exact Hsub.
    + intros Y HY. simpl in HY. simpl.
      apply AtomSetImpl.add_2. apply HscS; exact HY.
    + intros Y HY.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f X)) as HupB;
        simpl in HupB.
      destruct (Y == X) as [-> | Hne]; [ simpl; clear; fsetdec | ].
      simpl. apply AtomSetImpl.add_2. apply HscQ; clear - HY HupB Hne; fsetdec.
  - apply ad_pat_consis__tophole_drop. apply IHad_pat_consis; auto.
  - eapply ad_pat_consis__flex_l.
    + eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscS; fsetdec ].
    + apply IHad_pat_consis; auto.
      intros X HX.
      assert (Hbd' : binds α (abind_flex_mono_def τ) Θ')
        by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscS; fsetdec ]).
      assert (Hwfτ : a_wf_ptyp Θ' τ) by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hbd' ]).
      pose proof (a_wf_ptyp_ftv_dom' Hwfτ) as Hftv.
      pose proof (ftvar_in_uskl_ptyp_syn τ) as Hco.
      clear - HX Hftv Hco. fsetdec.
  - eapply ad_pat_consis__flex_r.
    + eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscQ; fsetdec ].
    + apply IHad_pat_consis; auto.
      intros X HX.
      assert (Hbd' : binds α (abind_flex_mono_def τ) Θ')
        by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscQ; fsetdec ]).
      assert (Hwfτ : a_wf_ptyp Θ' τ) by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hbd' ]).
      pose proof (a_wf_ptyp_ftv_dom' Hwfτ) as Hftv.
      pose proof (ftvar_in_bskl_ptyp_syn τ) as Hco.
      clear - HX Hftv Hco. fsetdec.
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
  (forall X, X `in` ftvar_in_ptyp A -> a_binds_tvar X Θ) ->
  empty ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl_syn A) ≈ Qb ->
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
Lemma bskl_to_pskl_msubst_bskl : forall ρ Q,
  bskl_to_pskl (msubst_bskl ρ Q) = msubst_pskl ρ (bskl_to_pskl Q).
Proof.
  intros ρ Q; induction Q; simpl; try reflexivity.
  - rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity.
  - rewrite IHQ1, IHQ2. reflexivity.
  - rewrite IHQ. reflexivity.
  - rewrite IHQ. reflexivity.
  - rewrite IHQ. reflexivity.
Qed.

(** A join whose SUBJECT is the ghost hole forces the target painting to be
    fully INHERITED: it is invariant under erase-then-reinherit.  (The only
    two rules that can conclude [uskl_hole ≈ Qb] are [__hole], whose target is
    an [inh] painting, and [__flex_r], whose target is a defined-flex variable
    — both fixed points of [inh ∘ erase].) *)
Lemma consis_hole_target_inh : forall Ψ Θ Qb,
  Ψ ⨟ Θ ⊨ₛᵃ uskl_hole ≈ Qb ->
  pskl_to_bskl_inh (bskl_to_pskl Qb) = Qb.
Proof.
  intros Ψ Θ Qb H.
  remember uskl_hole as S eqn:HS.
  induction H; try discriminate HS.
  - rewrite bskl_to_pskl_pskl_to_bskl_inh. reflexivity.
  - reflexivity.
Qed.


(** A guarded consistency subject has a guarded target.  Stated with an
    explicit local-closure premise on the target so the Arrow case needs no
    separate regularity development.  A left-side defined-flex lookup recurs
    on its definition; a right-side lookup lands at a guarded variable. *)
Lemma ad_pat_consis_guarded_r : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  a_wf_aenv Θ ->
  forall P,
    S = pskl_to_uskl P ->
    guarded_pskl P ->
    lc_bskl Q ->
    guarded_bskl Q.
Proof.
  intros Ψ Θ S Q Hc Hwf; induction Hc; intros P0 HeqS Hg Hlc;
    try solve [ destruct P0; simpl in HeqS; try discriminate;
                inversion Hg ].
  - destruct P0; simpl in HeqS; try discriminate.
    apply guarded_bskl__unit.
  - destruct P0; simpl in HeqS; try discriminate.
    apply guarded_bskl__var.
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
Lemma ad_refine_syn_f_tophole_guarded_inv : forall F Θ Δ Q R,
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ (bskl_tophole Q) R ->
  guarded_bskl R ->
  ad_refine_syn_f F Θ Δ Q R.
Proof.
  intros F Θ Δ Q R Hwf Hr.
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

Lemma ad_refine_pskl_f_tophole_guarded_inv : forall F Θ Δ P Q,
  a_wf_aenv Θ ->
  ad_refine_pskl_f F Θ Δ (pskl_tophole P) Q ->
  guarded_pskl Q ->
  ad_refine_pskl_f F Θ Δ P Q.
Proof.
  intros F Θ Δ P Q Hwf Hr.
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
  Ψ ⨟ Θ ⊨ₛᵃ (uskl_tophole (pskl_to_uskl P)) ≈ Q ->
  guarded_pskl P ->
  guarded_bskl Q ->
  Ψ ⨟ Θ ⊨ₛᵃ (pskl_to_uskl P) ≈ Q.
Proof.
  intros Ψ Θ P Q Hwf Hc.
  remember (uskl_tophole (pskl_to_uskl P)) as S eqn:HeqS.
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

Lemma ad_refine_syn_f_tophole_keep_inv : forall F Θ Δ P Q,
  a_wf_aenv Θ ->
  guarded_bskl P ->
  ad_refine_syn_f F Θ Δ (bskl_tophole P) (bskl_tophole Q) ->
  ad_refine_syn_f F Θ Δ P Q.
Proof.
  intros F Θ Δ P Q Hwf Hg Hr.
  inversion Hr; subst; try discriminate.
  - match goal with
    | Hsub : ad_refine_syn_f _ _ _ P (bskl_tophole Q) |- _ =>
        pose proof (ad_refine_syn_f_guarded_r Hwf Hsub Hg) as Hbad;
        inversion Hbad
    end.
  - assumption.
Qed.

Lemma ad_refine_pskl_f_tophole_keep_inv : forall F Θ Δ P Q,
  a_wf_aenv Θ ->
  guarded_pskl P ->
  ad_refine_pskl_f F Θ Δ (pskl_tophole P) (pskl_tophole Q) ->
  ad_refine_pskl_f F Θ Δ P Q.
Proof.
  intros F Θ Δ P Q Hwf Hg Hr.
  inversion Hr; subst; try discriminate.
  - match goal with
    | Hsub : ad_refine_pskl_f _ _ _ P (pskl_tophole Q) |- _ =>
        pose proof (ad_refine_pskl_f_guarded_r Hwf Hsub Hg) as Hbad;
        inversion Hbad
    end.
  - assumption.
Qed.

(* The join is invariant under ⇓-normalizing the SUBJECT, when the RHS is a
   monotype (mono C prunes every ∀/tophole_inh case, exactly as in
   join_pskl_downarrow_mono_scoped).  This transfers the assign-node join
   (subject msubst ρ P, RHS syn(mono ρα)) onto the ⇓-normalized subject,
   which [join_pskl_downarrow_mono_scoped] shows is scoped to the
   sub-target Θ'.  (Consumed by the ⇓-truncation walk cases of the
   μ-bundle in prop_consis_complete.v.) *)
Lemma consis_downarrow_subject : forall Ψ Θ S Q,
  ad_pat_consis Ψ Θ S Q ->
  a_wf_aenv Θ ->
  forall S0 C,
    S = pskl_to_uskl S0 ->
    Q = ptyp_to_bskl_syn C -> mono_ptyp C ->
    ad_pat_consis Ψ Θ (pskl_to_uskl (⇓ˢ[ Θ ] S0)) Q.
Proof.
  intros Ψ Θ S Q Hc Hwf; induction Hc;
    intros S0 C0 HeqS HeqC HmC0;
    unfold ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct S0; simpl in HeqS; try discriminate.
    simpl. apply ad_pat_consis__unit; assumption.
  - (* var X : uniform ⇓(var X) ≡ var X route (covers tvar/flex_mono/flex_def) *)
    destruct S0 as [ | | Xp | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | Xc | | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    simpl.
    replace (ptyp_to_pskl (msubst_lookup (aenv_msubst Θ) Xc))
       with (ptyp_to_pskl (⇓ᵗ[ Θ ] (ptyp_var_f Xc))) by reflexivity.
    assert (Hwfx : a_wf_ptyp Θ (ptyp_var_f Xc)) by (apply a_wf_ptyp__var; exact H0).
    assert (Hmono_x : mono_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f Xc)))
      by (apply mono_downarrow; [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]).
    assert (Hwf_x : a_wf_ptyp Θ (⇓ᵗ[ Θ ] (ptyp_var_f Xc)))
      by (apply a_wf_ptyp_downarrow_mono; [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]).
    assert (Hvis : forall Y, Y `in` ftvar_in_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f Xc)) ->
                   a_binds_tvar Y Θ)
      by (intros Y HY; eapply a_wf_ptyp_ftv_tvarish; [ exact Hwf_x | exact HY ]).
    assert (Heqd : Θ ⊢ (⇓ᵗ[ Θ ] (ptyp_var_f Xc)) ≡ᵗ (ptyp_var_f Xc)).
    { apply a_tyequiv__sym.
      apply a_tyequiv_to_downarrow_mono;
        [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]. }
    destruct (tyequiv_mono_consis_transport_q Heqd Hwf Hmono_x Hvis) as [_ Hfwd].
    rewrite ptyp_to_uskl_syn_eq.
    change (bskl_var_f Xc) with (ptyp_to_bskl_syn (ptyp_var_f Xc)).
    apply Hfwd.
    eapply ad_pat_consis_psi_cong;
      [ apply consis_mono_refl; [ exact Hmono_x | exact Hvis ]
      | fsetdec ].
  - (* arrow *)
    destruct S0 as [ | | | S01 S02 | | | ]; simpl in HeqS; try discriminate.
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
    destruct S0; simpl in HeqS; try discriminate.
    simpl. apply ad_pat_consis__hole; [ exact H | exact H0 ].
  - (* tophole *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_inh *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_drop *)
    destruct S0 as [ | | | | | | S0t ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl. apply ad_pat_consis__tophole_drop.
    apply (IHHc Hwf S0t C0 eq_refl eq_refl HmC0).
  - (* flex_l : subject is a defined flexible *)
    destruct S0 as [ | | Xv | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) Xv = ⇓ᵗ[ Θ ] τ)
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
    apply (IHHc Hwf S0 τ eq_refl eq_refl Hmτ).
Qed.


(* ===================================================================== *)
(*  §1  The three node measures                                           *)
(* ===================================================================== *)

Definition mu_consis (Θ : aenv) (ρ : metasubst) (P0 P : pskl)
    (Θ0 : aenv) : mu_ty :=
  (V_consis Θ ρ P0 P, (length Θ0, (1, 0))).

Definition mu_unify (Θ : aenv) (ρ : metasubst) (α β : atom)
    (Θ0 : aenv) : mu_ty :=
  (V_unify Θ ρ α β, (length Θ0, (0, 0))).

Definition mu_assign (Θ : aenv) (ρ : metasubst) (α : atom) (P : pskl)
    (Ξ Θ0 : aenv) : mu_ty :=
  (V_assign Θ ρ α P, (length Ξ + length Θ0, (0, length Θ0))).

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

Lemma ad_precise_f_forget : forall F Θ Δ P Q,
  ad_precise_f F Θ Δ P Q -> Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ Q.
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

Lemma bskl_no_hole_open_rec : forall Q X k,
  bskl_no_hole Q ->
  bskl_no_hole (open_bskl_wrt_bskl_rec k (bskl_var_f X) Q).
Proof.
  induction Q; simpl; intros X k Hnh; try contradiction; try exact I;
    try solve [ apply IHQ; assumption ];
    try solve [ destruct Hnh; split;
                [ apply IHQ1 | apply IHQ2 ]; assumption ].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; exact I.
Qed.

Lemma bskl_no_hole_open : forall Q X,
  bskl_no_hole Q ->
  bskl_no_hole (open_bskl_wrt_bskl Q (bskl_var_f X)).
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

Lemma ad_refine_syn_f_of_plain_no_hole : forall Θ Δ Q P,
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ P ->
  bskl_no_hole Q ->
  forall F, ad_refine_syn_f F Θ Δ Q P.
Proof.
  intros * H; induction H; intros Hnh F; simpl in Hnh.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - destruct Hnh. apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros X HX.
    apply H0; [ exact HX | apply bskl_no_hole_open; assumption ].
  - destruct Hnh.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L). intros X HX.
    apply H0; [ exact HX | exact Hnh ].
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
Lemma ad_refine_syn_f_fextend_ftv : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P ->
  forall F',
  (forall γ, γ `in` F' -> γ `in` F \/
     (γ `notin` ftvar_in_bskl P /\
      (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
         γ `notin` ftvar_in_ptyp τ))) ->
  ad_refine_syn_f F' Θ Δ Q P.
Proof.
  intros * H; induction H; intros F' Hcond; simpl in *.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - apply ad_refine_syn_f__arrow.
    + apply IHad_refine_syn_f1. intros γ Hγ.
      destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
        [ left; exact HinF | right; split; [ | exact Hd ] ].
      clear - Hf. fsetdec.
    + apply IHad_refine_syn_f2. intros γ Hγ.
      destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
        [ left; exact HinF | right; split; [ | exact Hd ] ].
      clear - Hf. fsetdec.
  - apply ad_refine_syn_f__all with (L := L `union` F').
    intros X HX.
    apply H0; [ clear - HX; fsetdec | ].
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
      [ left; exact HinF | right; split; [ | exact Hd ] ].
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                  P (bskl_var_f X)) as Hup.
    simpl in Hup.
    assert (γ <> X) by (clear - HX Hγ; fsetdec).
    clear - Hf Hup H1. fsetdec.
  - apply ad_refine_syn_f__hole; [ | assumption ].
    apply inter_empty_pointwise. intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | [Hf Hd]].
    + intro Hc.
      assert (Hin : γ `in` AtomSetImpl.inter F (ftvar_in_pskl P))
        by (apply AtomSetImpl.inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec.
    + rewrite ftvar_in_bskl_syn in Hf. exact Hf.
  - apply ad_refine_syn_f__tophole_remove. apply IHad_refine_syn_f.
    exact Hcond.
  - apply ad_refine_syn_f__tophole_fill with (L := L `union` F').
    intros X HX.
    apply H0; [ clear - HX; fsetdec | ].
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
      [ left; exact HinF | right ].
    split.
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                    P (bskl_var_f X)) as Hup.
      simpl in Hup.
      assert (γ <> X) by (clear - HX Hγ; fsetdec).
      clear - Hf Hup H1. fsetdec.
    + intros β τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | exact (Hd β τ Hb') ].
  - apply ad_refine_syn_f__tophole_keep; [ assumption | ].
    apply IHad_refine_syn_f.
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
      [ left; exact HinF | right; split; [ | exact Hd ] ].
    clear - Hf. fsetdec.
  - eapply ad_refine_syn_f__flex_l; [ eassumption | ].
    apply IHad_refine_syn_f. exact Hcond.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    apply IHad_refine_syn_f.
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
      [ left; exact HinF | right; split; [ | exact Hd ] ].
    rewrite ftvar_in_bskl_ptyp_syn. exact (Hd _ _ H).
Qed.

(** A hole-source Δ2-refinement polices its WHOLE target against rigid
    [F]-atoms: the [__hole] rule checks the fill (= the target) directly,
    and the only other applicable rule, [__flex_r], routes the target
    through a DEFINED (hence non-rigid) variable. *)
Lemma ad_refine_pskl_f_hole_src_target_ftv : forall F Θ Δ Qt,
  ad_refine_pskl_f F Θ Δ pskl_hole Qt ->
  a_wf_aenv Θ ->
  forall γ, γ `in` F -> binds γ abind_tvar Θ ->
  γ `notin` ftvar_in_pskl Qt.
Proof.
  intros * H.
  remember pskl_hole as S eqn:HeqS.
  induction H; intros Hwf γ HγF Hbγ; try discriminate HeqS.
  - (* __hole : the fill is the target *)
    intro Hc.
    assert (Hin : γ `in` AtomSetImpl.inter F (ftvar_in_pskl Q))
      by (apply AtomSetImpl.inter_3; assumption).
    rewrite H in Hin. clear - Hin. fsetdec.
  - (* __flex_r : target is a defined flexible, not the rigid γ *)
    simpl. intro Hc.
    assert (Heqγ : γ = α) by (clear - Hc; fsetdec). subst α.
    pose proof (binds_unique _ _ _ _ _ H Hbγ (a_wf_aenv_uniq Hwf)) as Hcon.
    discriminate.
Qed.

(** The syn-side twin: a hole-source Δ1-refinement polices its whole
    target against rigid [F]-atoms. *)
Lemma ad_refine_syn_f_hole_src_target_ftv : forall F Θ Δ Qt,
  ad_refine_syn_f F Θ Δ bskl_hole Qt ->
  a_wf_aenv Θ ->
  forall γ, γ `in` F -> binds γ abind_tvar Θ ->
  γ `notin` ftvar_in_bskl Qt.
Proof.
  intros * H.
  remember bskl_hole as S eqn:HeqS.
  induction H; intros Hwf γ HγF Hbγ; try discriminate HeqS.
  - (* __hole : the fill is the target *)
    rewrite ftvar_in_bskl_syn.
    intro Hc.
    assert (Hin : γ `in` AtomSetImpl.inter F (ftvar_in_pskl P))
      by (apply AtomSetImpl.inter_3; assumption).
    rewrite H in Hin. clear - Hin. fsetdec.
  - (* __flex_r : target is a defined flexible, not the rigid γ *)
    simpl. intro Hc.
    assert (Heqγ : γ = α) by (clear - Hc; fsetdec). subst α.
    pose proof (binds_unique _ _ _ _ _ H Hbγ (a_wf_aenv_uniq Hwf)) as Hcon.
    discriminate.
Qed.

(* ===================================================================== *)
(*  §1c  ∀-case transports: weakening / F-extension / Δ↔context moves     *)
(* ===================================================================== *)

(** Free variables of a wf skeleton are scoped by its Δ and context. *)
Lemma ad_wf_pskl_ftv_dom : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  ftvar_in_pskl P [<=] (Δ `union` dom Θ).
Proof.
  intros * H; induction H; simpl; try solve [ clear; fsetdec ].
  - (* var *)
    destruct H as [HΔ | Hbt]; [ clear - HΔ; fsetdec | ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]]; apply binds_In in Hb;
      clear - Hb; fsetdec.
  - (* arrow *) clear - IHad_wf_pskl1 IHad_wf_pskl2. fsetdec.
  - (* all *)
    pick fresh X for (L `union` ftvar_in_pskl P `union` Δ
                        `union` dom Θ).
    assert (HXL : X `notin` L) by (clear - Fr; fsetdec).
    pose proof (H0 X HXL) as Hsub.
    intros Z HZ.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower
                  P (pskl_var_f X)) as Hlo.
    assert (HZ' : Z `in` (add X Δ `union` dom Θ))
      by (apply Hsub; clear - HZ Hlo; fsetdec).
    assert (Hne : Z <> X) by (clear - HZ Fr; fsetdec).
    clear - HZ' Hne. fsetdec.
  - (* tophole *) clear - IHad_wf_pskl. fsetdec.
Qed.

(** Context weakening (binds-monotone) for the hygienic refinements. *)
Lemma ad_refine_syn_f_weaken_ctx : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P ->
  forall Θ', (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  ad_refine_syn_f F Θ' Δ Q P.
Proof.
  intros * H; induction H; intros Θ' Hmon.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Hbt]; [ left; exact HΔ | right ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros X HX. auto.
  - apply ad_refine_syn_f__hole; [ exact H | ].
    eapply ad_wf_pskl_weaken; eassumption.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L). intros X HX.
    apply H0; [ exact HX | ].
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
      [ subst; unfold binds; left; reflexivity
      | apply binds_cons_3; apply Hmon; exact Hb' ].
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; [ apply Hmon; eassumption | auto ].
  - eapply ad_refine_syn_f__flex_r; [ apply Hmon; eassumption | auto ].
Qed.

Lemma ad_refine_pskl_f_weaken_ctx : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q ->
  forall Θ', (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  ad_refine_pskl_f F Θ' Δ P Q.
Proof.
  intros * H; induction H; intros Θ' Hmon.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var.
    destruct H as [HΔ | Hbt]; [ left; exact HΔ | right ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
  - apply ad_refine_pskl_f__arrow; auto.
  - apply ad_refine_pskl_f__all with (L := L). intros X HX. auto.
  - apply ad_refine_pskl_f__hole; [ exact H | ].
    eapply ad_wf_pskl_weaken; eassumption.
  - apply ad_refine_pskl_f__tophole_remove; auto.
  - apply ad_refine_pskl_f__tophole_fill with (L := L). intros X HX.
    apply H0; [ exact HX | ].
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
Lemma ad_refine_syn_f_fextend_dom : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P ->
  forall F', (forall γ, γ `in` F' -> γ `in` F \/ γ `notin` dom Θ) ->
  ad_refine_syn_f F' Θ Δ Q P.
Proof.
  intros * H; induction H; intros F' Hcond.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros X HX. auto.
  - apply ad_refine_syn_f__hole; [ | exact H0 ].
    apply inter_empty_pointwise. intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | Hnd].
    + intro Hc.
      assert (Hin : γ `in` AtomSetImpl.inter F (ftvar_in_pskl P))
        by (apply AtomSetImpl.inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec.
    + pose proof (ad_wf_pskl_ftv_dom H0) as Hsc.
      clear - Hnd Hsc. fsetdec.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L `union` F').
    intros X HX.
    apply H0; [ clear - HX; fsetdec | ].
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | Hnd]; [ left; exact HinF | right ].
    simpl dom.
    assert (γ <> X) by (clear - HX Hγ; fsetdec).
    clear - Hnd H1. fsetdec.
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; [ eassumption | auto ].
  - eapply ad_refine_syn_f__flex_r; [ eassumption | auto ].
Qed.

Lemma ad_refine_pskl_f_fextend_dom : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q ->
  forall F', (forall γ, γ `in` F' -> γ `in` F \/ γ `notin` dom Θ) ->
  ad_refine_pskl_f F' Θ Δ P Q.
Proof.
  intros * H; induction H; intros F' Hcond.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var; assumption.
  - apply ad_refine_pskl_f__arrow; auto.
  - apply ad_refine_pskl_f__all with (L := L). intros X HX. auto.
  - apply ad_refine_pskl_f__hole; [ | exact H0 ].
    apply inter_empty_pointwise. intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | Hnd].
    + intro Hc.
      assert (Hin : γ `in` AtomSetImpl.inter F (ftvar_in_pskl Q))
        by (apply AtomSetImpl.inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec.
    + pose proof (ad_wf_pskl_ftv_dom H0) as Hsc.
      clear - Hnd Hsc. fsetdec.
  - apply ad_refine_pskl_f__tophole_remove; auto.
  - apply ad_refine_pskl_f__tophole_fill with (L := L `union` F').
    intros X HX.
    apply H0; [ clear - HX; fsetdec | ].
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | Hnd]; [ left; exact HinF | right ].
    simpl dom.
    assert (γ <> X) by (clear - HX Hγ; fsetdec).
    clear - Hnd H1. fsetdec.
  - apply ad_refine_pskl_f__tophole_keep; auto.
  - eapply ad_refine_pskl_f__flex_l; [ eassumption | auto ].
  - eapply ad_refine_pskl_f__flex_r; [ eassumption | auto ].
Qed.

(** Moving a Δ-variable of a wf skeleton into the context as a rigid. *)
Lemma ad_wf_pskl_delta_to_tvar : forall Θ Δ0 P,
  Θ ⨟ Δ0 ⊢ₚₛᵃ P ->
  forall X Δ, Δ0 [<=] add X Δ ->
  ((X ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros * H; induction H; intros Y Δ' Hsub.
  - apply ad_wf_pskl__unit.
  - destruct H as [HΔ | Hbt].
    + destruct (X == Y) as [-> | Hne].
      * apply ad_wf_pskl__var. right. left.
        unfold binds. left. reflexivity.
      * apply ad_wf_pskl__var. left. clear - HΔ Hsub Hne. fsetdec.
    + apply ad_wf_pskl__var. right.
      apply a_binds_tvar_weaken_cons. exact Hbt.
  - apply ad_wf_pskl__arrow; auto.
  - apply ad_wf_pskl__all with (L := L `union` singleton Y).
    intros Z HZ.
    apply H0; [ clear - HZ; fsetdec | clear - Hsub HZ; fsetdec ].
  - apply ad_wf_pskl__hole.
  - apply ad_wf_pskl__tophole; [ exact H | ].
    apply IHad_wf_pskl. clear. fsetdec.
Qed.

(** A guarded source never refines to an inherited quantifier (the mirror
    of [ad_refine_syn_f_all_inh_guarded_absurd]): the rules with an
    [all_inh] target need an [all_inh] source or a defined-flexible whose
    monotype unfolding is guarded again. *)
Lemma ad_refine_syn_f_guarded_src_all_inh_absurd : forall F Θ Δ Q R,
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ Q (bskl_all_inh R) ->
  guarded_bskl Q ->
  False.
Proof.
  intros * Hwf Hr.
  remember (bskl_all_inh R) as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT.
  - (* __all : the source is an inherited quantifier, not guarded *)
    inversion Hg.
  - (* __hole : a syn painting is never an inherited quantifier *)
    destruct P; simpl in HeqT; discriminate.
  - (* __tophole_remove : a ⊤◇ source is not guarded *)
    inversion Hg.
  - (* __flex_l : unfold to the (guarded) monotype *)
    apply IHHr; [ exact Hwf | exact HeqT | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** Mirror: a guarded source never refines to a ∀-syn target either
    (that target only arises by [tophole_fill], whose source is a ⊤◇). *)
Lemma ad_refine_syn_f_guarded_src_all_syn_absurd : forall F Θ Δ Q R,
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ Q (bskl_all_syn R) ->
  guarded_bskl Q ->
  False.
Proof.
  intros * Hwf Hr.
  remember (bskl_all_syn R) as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT;
    try solve [ inversion Hg ].
  apply IHHr; [ exact Hwf | exact HeqT | ].
  apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
  eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** The pskl-side mirror. *)
Lemma ad_refine_pskl_f_guarded_src_all_syn_absurd : forall F Θ Δ Q R,
  a_wf_aenv Θ ->
  ad_refine_pskl_f F Θ Δ Q (pskl_all_syn R) ->
  guarded_pskl Q ->
  False.
Proof.
  intros * Hwf Hr.
  remember (pskl_all_syn R) as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT;
    try solve [ inversion Hg ].
  apply IHHr; [ exact Hwf | exact HeqT | ].
  apply mono_ptyp_to_pskl_guarded.
  eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** Moving the rigid mid entry into the Δ-slot of a HYGIENIC refinement
    ([α ∈ F] guarantees no fill mentions it, which is exactly what lets
    the fills' wf strengthen past the removed entry). *)
Lemma ad_refine_syn_f_ctx_to_delta : forall F Θfull Δ Q P,
  ad_refine_syn_f F Θfull Δ Q P ->
  forall Θ1 α Θ0, Θfull = Θ1 ++ (α ~ abind_tvar) ++ Θ0 ->
  α `in` F ->
  uniq Θfull ->
  ad_refine_syn_f F (Θ1 ++ Θ0) (add α Δ) Q P.
Proof.
  intros F Θfull Δ Q P H; induction H;
    intros Θ1 α0 Θt HeqΘ HαF Hu; subst Θ.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Hbt]; [ left; clear - HΔ; fsetdec | ].
    destruct (X == α0) as [-> | Hne];
      [ left; clear; fsetdec | right ].
    eapply a_binds_tvar_strip_mid;
      [ exact Hbt
      | intro Hc; inversion Hc; congruence
      | intro Hc; inversion Hc
      | intros τ0 Hc; inversion Hc ].
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros X HX.
    eapply ad_refine_syn_f_delta_mono;
      [ apply (H0 X HX Θ1 α0 Θt eq_refl HαF Hu) | clear; fsetdec ].
  - apply ad_refine_syn_f__hole; [ exact H | ].
    assert (HαP : α0 `notin` ftvar_in_pskl P).
    { intro Hc.
      assert (Hin : α0 `in` AtomSetImpl.inter F (ftvar_in_pskl P))
        by (apply AtomSetImpl.inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec. }
    pose proof (ad_wf_pskl_ftv_dom H0) as Hsc.
    eapply ad_wf_pskl_strengthen;
      [ exact H0 | exact Hu
      | intros x Hx; exfalso; clear - Hx; fsetdec
      | intros x b Hb; apply binds_weaken; exact Hb
      | ].
    intros X HX. right.
    assert (Hd : X `in` dom (Θ1 ++ (α0 ~ abind_tvar) ++ Θt))
      by (clear - Hsc HX; fsetdec).
    assert (Hne : X <> α0) by (intro; subst; contradiction).
    repeat rewrite dom_app in *. simpl dom in Hd.
    clear - Hd Hne. fsetdec.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with
      (L := L `union` dom (Θ1 ++ (α0 ~ abind_tvar) ++ Θt)).
    intros X HX.
    apply (H0 X ltac:(clear - HX; fsetdec)
             ((X ~ abind_tvar) ++ Θ1) α0 Θt eq_refl HαF).
    apply uniq_push; [ exact Hu | clear - HX; fsetdec ].
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

Lemma pskl_to_bskl_inh_subst_var : forall X α P,
  subst_bskl_in_bskl (bskl_var_f X) α (pskl_to_bskl_inh P)
  = pskl_to_bskl_inh (subst_pskl_in_pskl (pskl_var_f X) α P).
Proof.
  intros X α P; induction P; simpl;
    try solve [ reflexivity
              | rewrite IHP; reflexivity
              | rewrite IHP1, IHP2; reflexivity ].
  match goal with |- context [ if ?t then _ else _ ] => destruct t end;
    reflexivity.
Qed.

Lemma bskl_to_pskl_subst_var : forall X α Q,
  subst_pskl_in_pskl (pskl_var_f X) α (bskl_to_pskl Q)
  = bskl_to_pskl (subst_bskl_in_bskl (bskl_var_f X) α Q).
Proof.
  intros X α Q; induction Q; simpl;
    try solve [ reflexivity
              | rewrite IHQ; reflexivity
              | rewrite IHQ1, IHQ2; reflexivity ].
  match goal with |- context [ if ?t then _ else _ ] => destruct t end;
    reflexivity.
Qed.

Lemma msubst_lookup_in_or : forall (ζ : metasubst) (β : atom),
  In (β, msubst_lookup ζ β) ζ \/
  (β `notin` dom ζ /\ msubst_lookup ζ β = ptyp_var_f β).
Proof.
  induction ζ as [ | [γ τ] ζ' IH ]; intros β; simpl.
  - right. split; [ fsetdec | reflexivity ].
  - destruct (β == γ) as [-> | Hne].
    + left. left. reflexivity.
    + destruct (IH β) as [Hin | [Hni Heq]];
        [ left; right; exact Hin
        | right; split; [ clear - Hni Hne; fsetdec | exact Heq ] ].
Qed.

(** Renaming a rigid [α ↦ X] commutes with a metasubstitution that does
    not touch either name (its images avoid [α]; both are off its
    domain). *)
Lemma msubst_pskl_subst_var : forall ζ α X P,
  α `notin` dom ζ ->
  X `notin` dom ζ ->
  (forall γ τ, In (γ, τ) ζ -> α `notin` ftvar_in_ptyp τ) ->
  subst_pskl_in_pskl (pskl_var_f X) α (msubst_pskl ζ P)
  = msubst_pskl ζ (subst_pskl_in_pskl (pskl_var_f X) α P).
Proof.
  intros ζ α X P Hαd HXd Him;
    induction P as [ | n | β | Pa IHa Pb IHb | Pb IHb | | Pt IHt ]; simpl;
    try solve [ reflexivity
              | rewrite IHb; reflexivity
              | rewrite IHt; reflexivity
              | rewrite IHa, IHb; reflexivity ].
  (* var *)
  match goal with |- context [ if ?t then _ else _ ] =>
    destruct t as [-> | Hne] end.
  - (* the renamed variable: off the domain on both sides *)
    rewrite (msubst_lookup_notin ζ Hαd). simpl.
    match goal with |- context [ if ?t then _ else _ ] =>
      destruct t as [_ | Hc]; [ | congruence ] end.
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
      match goal with |- context [ if ?t then _ else _ ] =>
        destruct t as [Hc | _]; [ congruence | reflexivity ] end.
Qed.

(** Images of an information increase are scoped by the target. *)
Lemma a_inc_images_ftv_dom : forall Θ0 ζ Θ,
  Θ0 ≤[ ζ ] Θ ->
  forall γ τ, In (γ, τ) ζ -> ftvar_in_ptyp τ [<=] dom Θ.
Proof.
  intros Θ0 ζ Θ H; induction H; intros γ0 τ0 Hin.
  - inversion Hin.
  - destruct Hin as [Heq | Hin];
      [ inversion Heq; subst; apply a_wf_ptyp_ftv_dom; assumption
      | eapply IHa_inc; exact Hin ].
  - destruct Hin as [Heq | Hin];
      [ inversion Heq; subst; apply a_wf_ptyp_ftv_dom; assumption
      | eapply IHa_inc; exact Hin ].
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros Z HZ. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub Z HZ). clear - H2. fsetdec.
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros Z HZ. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub Z HZ). clear - H2. fsetdec.
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros Z HZ. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub Z HZ). clear - H1. fsetdec.
Qed.

(* ===================================================================== *)
(*  §1e  ⇓-idempotence: a normalized term is invariant under any          *)
(*       sub-context's normalization (V-constancy for the walk's          *)
(*       target-truncating recursions)                                    *)
(* ===================================================================== *)

Lemma msubst_pskl_ftv_ex : forall ζ P X,
  X `in` ftvar_in_pskl (msubst_pskl ζ P) ->
  exists Y, Y `in` ftvar_in_pskl P /\
            X `in` ftvar_in_ptyp (msubst_lookup ζ Y).
Proof.
  intros ζ P; induction P as [ | n | Z | Pa IHa Pb IHb | Pb IHb | | Pt IHt ];
    intros X HX; simpl in *.
  - clear - HX; fsetdec.
  - clear - HX; fsetdec.
  - exists Z. split; [ fsetdec | ].
    rewrite ftvar_in_ptyp_to_pskl in HX. exact HX.
  - apply AtomSetImpl.union_1 in HX. destruct HX as [H1 | H2].
    + destruct (IHa X H1) as [Y [HY1 HY2]].
      exists Y; split; [ fsetdec | exact HY2 ].
    + destruct (IHb X H2) as [Y [HY1 HY2]].
      exists Y; split; [ fsetdec | exact HY2 ].
  - destruct (IHb X HX) as [Y [HY1 HY2]].
    exists Y; split; [ fsetdec | exact HY2 ].
  - clear - HX; fsetdec.
  - destruct (IHt X HX) as [Y [HY1 HY2]].
    exists Y; split; [ fsetdec | exact HY2 ].
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
  forall Y,
  ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) Y) [<=] add Y (dom Θ).
Proof.
  intros Θ Hwf; induction Hwf; intros Y;
    try rewrite aenv_msubst_cons_flex;
    try rewrite aenv_msubst_cons_def;
    try rewrite aenv_msubst_tvar;
    try rewrite aenv_msubst_var_typ;
    try rewrite aenv_msubst_var_skl.
  - (* nil *) simpl. clear; fsetdec.
  - (* flex_mono *)
    destruct (Y == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq. simpl. simpl_env.
      clear; fsetdec.
    + rewrite msubst_lookup_cons_neq by exact Hne. simpl_env.
      pose proof (IHHwf Y) as Him. clear - Him. fsetdec.
  - (* flex_mono_def *)
    destruct (Y == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq.
      intros X HX.
      destruct (msubst_ptyp_ftv _ _ HX) as [Z [HZ1 HZ2]].
      assert (HZd : Z `in` dom Θ)
        by (pose proof (a_wf_ptyp_ftv_dom H0) as Hsc;
            clear - Hsc HZ1; fsetdec).
      pose proof (IHHwf Z) as Him.
      simpl_env. clear - HZ2 Him HZd. fsetdec.
    + rewrite msubst_lookup_cons_neq by exact Hne. simpl_env.
      pose proof (IHHwf Y) as Him. clear - Him. fsetdec.
  - (* var_skl *) simpl_env.
    pose proof (IHHwf Y) as Him. clear - Him. fsetdec.
  - (* var_typ *) simpl_env.
    pose proof (IHHwf Y) as Him. clear - Him. fsetdec.
  - (* tvar *) simpl_env.
    pose proof (IHHwf Y) as Him. clear - Him. fsetdec.
Qed.

(** No image of [⇓[Θ]] mentions a DEFINED variable of [Θ]. *)
Lemma aenv_msubst_image_no_def : forall Θ,
  a_wf_aenv Θ ->
  forall Y X, X `in` ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) Y) ->
  forall τ, ~ binds X (abind_flex_mono_def τ) Θ.
Proof.
  intros Θ Hwf; induction Hwf; intros Y X HX τq Hb;
    try rewrite aenv_msubst_cons_flex in HX;
    try rewrite aenv_msubst_cons_def in HX;
    try rewrite aenv_msubst_tvar in HX;
    try rewrite aenv_msubst_var_typ in HX;
    try rewrite aenv_msubst_var_skl in HX.
  - (* nil *) inversion Hb.
  - (* flex_mono α *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | ].
    destruct (Y == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq in HX. simpl in HX.
      assert (X = α) by (clear - HX; fsetdec). subst X.
      apply binds_In in Hb'. contradiction.
    + rewrite msubst_lookup_cons_neq in HX by exact Hne.
      exact (IHHwf Y X HX τq Hb').
  - (* flex_mono_def α τ0 *)
    destruct (Y == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq in HX.
      destruct (msubst_ptyp_ftv _ _ HX) as [Z [HZ1 HZ2]].
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'].
      * subst X. exfalso.
        assert (HZd : Z `in` dom Θ)
          by (pose proof (a_wf_ptyp_ftv_dom H0) as Hsc;
              clear - Hsc HZ1; fsetdec).
        pose proof (aenv_msubst_image_ftv Hwf Z) as Him.
        assert (Hin1 : α `in` add Z (dom Θ))
          by (clear - HZ2 Him; fsetdec).
        assert (Hne1 : α <> Z) by (intro; subst; contradiction).
        clear - Hin1 Hne1 H. fsetdec.
      * exact (IHHwf Z X HZ2 τq Hb').
    + rewrite msubst_lookup_cons_neq in HX by exact Hne.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'].
      * subst X. exfalso.
        pose proof (aenv_msubst_image_ftv Hwf Y) as Him.
        assert (Hin1 : α `in` add Y (dom Θ))
          by (clear - HX Him; fsetdec).
        assert (Hne1 : α <> Y) by (intro; subst; contradiction).
        clear - Hin1 Hne1 H. fsetdec.
      * exact (IHHwf Y X HX τq Hb').
  - (* var_skl *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | exact (IHHwf Y X HX τq Hb') ].
  - (* var_typ *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | exact (IHHwf Y X HX τq Hb') ].
  - (* tvar *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | exact (IHHwf Y X HX τq Hb') ].
Qed.

(** Look-up under a context none of whose definitions can be hit. *)
Lemma aenv_msubst_lookup_no_def : forall Θ X,
  (forall τ, ~ binds X (abind_flex_mono_def τ) Θ) ->
  msubst_lookup (aenv_msubst Θ) X = ptyp_var_f X.
Proof.
  induction Θ as [ | [γ b] Θ' IH ]; intros X Hnd.
  - reflexivity.
  - destruct b as [ | A | Q | | τ0 ]; simpl aenv_msubst.
    + apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + destruct (X == γ) as [-> | Hne].
      * rewrite msubst_lookup_cons_eq. reflexivity.
      * rewrite msubst_lookup_cons_neq by exact Hne.
        apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + destruct (X == γ) as [-> | Hne].
      * exfalso. apply (Hnd τ0). unfold binds. left. reflexivity.
      * rewrite msubst_lookup_cons_neq by exact Hne.
        apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
Qed.

Lemma msubst_ptyp_lookup_refl : forall θ A,
  (forall X, X `in` ftvar_in_ptyp A -> msubst_lookup θ X = ptyp_var_f X) ->
  msubst_ptyp θ A = A.
Proof.
  intros θ A; induction A as [ | n | Z | A1 IH1 A2 IH2 | A0 IH0 ];
    intros Hlk; simpl in *.
  - reflexivity.
  - reflexivity.
  - apply Hlk. fsetdec.
  - rewrite IH1, IH2;
      [ reflexivity
      | intros X HX; apply Hlk; fsetdec
      | intros X HX; apply Hlk; fsetdec ].
  - rewrite IH0; [ reflexivity | intros X HX; apply Hlk; fsetdec ].
Qed.

Lemma msubst_pskl_lookup_refl : forall θ P,
  (forall X, X `in` ftvar_in_pskl P -> msubst_lookup θ X = ptyp_var_f X) ->
  msubst_pskl θ P = P.
Proof.
  intros θ P;
    induction P as [ | n | Z | Pa IHa Pb IHb | Pb IHb | | Pt IHt ];
    intros Hlk; simpl in *.
  - reflexivity.
  - reflexivity.
  - rewrite Hlk; [ reflexivity | fsetdec ].
  - rewrite IHa, IHb;
      [ reflexivity
      | intros X HX; apply Hlk; fsetdec
      | intros X HX; apply Hlk; fsetdec ].
  - rewrite IHb; [ reflexivity | intros X HX; apply Hlk; fsetdec ].
  - reflexivity.
  - rewrite IHt; [ reflexivity | intros X HX; apply Hlk; fsetdec ].
Qed.

(** ⇓-idempotence along a context restriction. *)
Lemma downarrow_idem_sub_ptyp : forall Θ Θs A,
  a_wf_aenv Θ ->
  (forall x (b : abind), binds x b Θs -> binds x b Θ) ->
  ⇓ᵗ[ Θs ] (⇓ᵗ[ Θ ] A) = ⇓ᵗ[ Θ ] A.
Proof.
  intros * Hwf Hsub.
  apply msubst_ptyp_lookup_refl. intros X HX.
  apply aenv_msubst_lookup_no_def. intros τ Hb.
  destruct (msubst_ptyp_ftv _ _ HX) as [Y [HY1 HY2]].
  assert (Hno : forall τ0, ~ binds X (abind_flex_mono_def τ0) Θ)
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
  apply msubst_pskl_lookup_refl. intros X HX.
  apply aenv_msubst_lookup_no_def. intros τ Hb.
  destruct (msubst_pskl_ftv_ex _ _ HX) as [Y [HY1 HY2]].
  assert (Hno : forall τ0, ~ binds X (abind_flex_mono_def τ0) Θ)
    by (intros τ0; eapply aenv_msubst_image_no_def;
        [ exact Hwf | exact HY2 ]).
  exact (Hno τ (Hsub _ _ Hb)).
Qed.

(* ===================================================================== *)
(*  §1f  var_skl / tvar middle twins of the walk-case a_inc tooling       *)
(* ===================================================================== *)

Lemma a_pskl_tyequiv_weaken : forall Θ Θ' P Q,
  (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  Θ ⊢ P ≡ˢ Q ->
  Θ' ⊢ P ≡ˢ Q.
Proof.
  intros * Hmon Heq; revert Θ' Hmon; induction Heq; intros Θ' Hmon;
    eauto using a_pskl_tyequiv.
Qed.

Lemma a_wf_pskl_weaken : forall Θ Θ' P,
  (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  a_wf_pskl Θ P ->
  a_wf_pskl Θ' P.
Proof.
  intros * Hmon Hwf; revert Θ' Hmon; induction Hwf; intros Θ' Hmon.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L). intros X HX.
    apply H0; [ exact HX | ].
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
      [ subst; unfold binds; left; reflexivity
      | apply binds_cons_3; apply Hmon; exact Hb' ].
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; auto.
Qed.

Lemma a_inc_var_skl_mid_strip_id : forall Ξ x Q Θ0 ρ Θ1,
  a_decls Ξ ->
  is_id_msubst ρ ->
  (Ξ ++ (x ~ abind_var_skl Q) ++ Θ0) ≤[ ρ ] ((x ~ abind_var_skl Q) ++ Θ1) ->
  (Ξ ++ Θ0) ≤[ ρ ] Θ1.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros x Q Θ0 ρ Θ1 Hdec Hid Hinc.
  - simpl in Hinc.
    destruct (a_inc_var_skl_inv Hinc)
      as [Ξv [P' [Θ2 [Heqt [Heqv [Hsuf Hinc']]]]]].
    destruct Ξv as [ | [z bz] Ξv' ].
    + simpl in Heqt. inversion Heqt; subst. exact Hinc'.
    + exfalso. simpl in Heqt. inversion Heqt; subst.
      inversion Hsuf as [ | z0 b0 Ξ0 Hsuf0 Hsb ]; subst.
      inversion Hsb.
  - inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs ρs Θts aa τ Hinc' Hwfτ Hmτ | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    apply a_inc__flex; [ | | apply mono_ptyp__var ].
    2:{ apply a_wf_ptyp__var.
        inversion Hwfτ as [ | Θw Xw Hbt | | ]; subst.
        eapply a_binds_tvar_strip_mid with
          (c := x) (b := abind_var_skl Q) (Ξ := (@nil (atom * abind)));
          [ simpl; exact Hbt
          | intro Hc; inversion Hc
          | intro Hc; inversion Hc
          | intros ? Hc; inversion Hc ]. }
    eapply IH; [ exact Hdec' | exact Hid' | exact Hinc' ].
Qed.

Lemma a_inc_equiv_mid_insert_var_skl :
  forall Ξ x Θ0 Θ' Ξv ρ1 ρ2 σ1 σ2 Qm Qm',
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom ρ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  Θ' ⊢ Qm' ≡ˢ (msubst_pskl ρ2 Qm) ->
  a_suffix Ξv ->
  a_inc_equiv (Ξ ++ Θ0) (ρ1 ++ ρ2) (σ1 ++ σ2) Θ' ->
  a_inc_equiv (Ξ ++ (x ~ abind_var_skl Qm) ++ Θ0)
              (ρ1 ++ ρ2) (σ1 ++ σ2)
              (Ξv ++ (x ~ abind_var_skl Qm') ++ Θ').
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros x Θ0 Θ' Ξv ρ1 ρ2 σ1 σ2 Qm Qm' Hdec Huq Hdρ Hdσ Heqm Hsuf Hie.
  - rewrite dom_nil in Hdρ, Hdσ.
    apply metasubst_dom_empty in Hdρ; apply metasubst_dom_empty in Hdσ;
      subst.
    simpl in Hie |- *.
    apply a_inc_equiv__var_skl; [ exact Hie | exact Heqm | exact Hsuf ].
  - inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Huρ : uniq (ρ1 ++ ρ2))
      by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
    assert (Huσ : uniq (σ1 ++ σ2))
      by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
    assert (HaΞ : a `notin` dom Ξ')
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    destruct ρ1 as [ | [ar tr] ρ1' ];
      [ exfalso; rewrite dom_nil in Hdρ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdρ in Hin; clear - Hin; fsetdec | ].
    destruct σ1 as [ | [asg ts] σ1' ];
      [ exfalso; rewrite dom_nil in Hdσ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
    assert (Harρ : ar `notin` dom ρ1')
      by (clear - Huρ; simpl_env in Huρ; solve_uniq).
    assert (Hasσ : asg `notin` dom σ1')
      by (clear - Huσ; simpl_env in Huσ; solve_uniq).
    simpl in Hie.
    inversion Hie as [ | S q1 q2 T aa u1 u2 Hie' Hequ | | | | ]; subst.
    simpl_env in Hdρ; simpl_env in Hdσ.
    simpl. apply a_inc_equiv__flex.
    2:{ apply a_tyequiv_weaken with (Θ := Θ');
        [ intros y b Hb; simpl_env; auto | exact Hequ ]. }
    apply IH; auto.
    + clear - Hdρ Harρ HaΞ. simpl_env in *. fsetdec.
    + clear - Hdσ Hasσ HaΞ. simpl_env in *. fsetdec.
Qed.

Lemma a_inc_equiv_mid_insert_tvar :
  forall Ξ c Θ0 Θ' Ξv ρ1 ρ2 σ1 σ2,
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom ρ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  a_suffix Ξv ->
  a_inc_equiv (Ξ ++ Θ0) (ρ1 ++ ρ2) (σ1 ++ σ2) Θ' ->
  a_inc_equiv (Ξ ++ (c ~ abind_tvar) ++ Θ0)
              (ρ1 ++ ρ2) (σ1 ++ σ2)
              (Ξv ++ (c ~ abind_tvar) ++ Θ').
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros c Θ0 Θ' Ξv ρ1 ρ2 σ1 σ2 Hdec Huq Hdρ Hdσ Hsuf Hie.
  - rewrite dom_nil in Hdρ, Hdσ.
    apply metasubst_dom_empty in Hdρ; apply metasubst_dom_empty in Hdσ;
      subst.
    simpl in Hie |- *.
    apply a_inc_equiv__tvar; [ exact Hie | exact Hsuf ].
  - inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Huρ : uniq (ρ1 ++ ρ2))
      by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
    assert (Huσ : uniq (σ1 ++ σ2))
      by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
    assert (HaΞ : a `notin` dom Ξ')
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    destruct ρ1 as [ | [ar tr] ρ1' ];
      [ exfalso; rewrite dom_nil in Hdρ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdρ in Hin; clear - Hin; fsetdec | ].
    destruct σ1 as [ | [asg ts] σ1' ];
      [ exfalso; rewrite dom_nil in Hdσ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
    assert (Harρ : ar `notin` dom ρ1')
      by (clear - Huρ; simpl_env in Huρ; solve_uniq).
    assert (Hasσ : asg `notin` dom σ1')
      by (clear - Huσ; simpl_env in Huσ; solve_uniq).
    simpl in Hie.
    inversion Hie as [ | S q1 q2 T aa u1 u2 Hie' Hequ | | | | ]; subst.
    simpl_env in Hdρ; simpl_env in Hdσ.
    simpl. apply a_inc_equiv__flex.
    2:{ apply a_tyequiv_weaken with (Θ := Θ');
        [ intros y b Hb; simpl_env; auto | exact Hequ ]. }
    apply IH; auto.
    + clear - Hdρ Harρ HaΞ. simpl_env in *. fsetdec.
    + clear - Hdσ Hasσ HaΞ. simpl_env in *. fsetdec.
Qed.

(** Strip a DEFINED flexible mid off a competing increment (the
    [flex_def] twin of [a_inc_mid_strip_flex]): additionally returns the
    dropped image's wf/mono data and its ≡ᵗ-tie to the definition. *)
Lemma a_inc_mid_strip_flex_def : forall Ξ β τd Θ0 ρ Θ,
  a_decls Ξ ->
  (Ξ ++ (β ~ abind_flex_mono_def τd) ++ Θ0) ≤[ ρ ] Θ ->
  exists ρ1 τ ρ2,
    ρ = ρ1 ++ (β, τ) :: ρ2 /\
    dom ρ1 [=] dom Ξ /\
    Θ0 ≤[ ρ2 ] Θ /\
    (Ξ ++ Θ0) ≤[ ρ1 ++ ρ2 ] Θ /\
    a_wf_ptyp Θ τ /\ mono_ptyp τ /\
    Θ ⊢ τ ≡ᵗ (msubst_ptyp ρ2 τd).
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros β τd Θ0 ρ Θ Hdec Hinc.
  - (* Ξ = nil : head is the defined mid β itself *)
    simpl in Hinc.
    inversion Hinc as [ | | Θs ρs Θt βs τ0 τ' Hinc' Hwfτ Hmτ Heqv
                          [Heqβ Heqρ] Heqt | | | ]; subst.
    exists (@nil (atom * ptyp)), τ', ρs. simpl.
    split; [ reflexivity | ].
    split; [ clear; fsetdec | ].
    split; [ exact Hinc' | ].
    split; [ exact Hinc' | ].
    split; [ exact Hwfτ | ].
    split; [ exact Hmτ | exact Heqv ].
  - (* Ξ = (a ~ flex) ++ Ξ' : peel the head flex a, recurse *)
    inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs ρs Θt as' τ Hinc' Hwfτ Hmτ [Heqa Heqρ] Heqt
                      | | | | ]; subst.
    destruct (IH β τd Θ0 ρs Θ Hdec' Hinc')
      as [ρ1 [τ2 [ρ2 [Heqρ [Hdom [Hinc2 [Hrec [Hwf2 [Hm2 Heqv2]]]]]]]]].
    exists ((a, τ) :: ρ1), τ2, ρ2. simpl.
    split; [ rewrite Heqρ; reflexivity | ].
    split; [ clear - Hdom; simpl_env; fsetdec | ].
    split; [ exact Hinc2 | ].
    split; [ apply a_inc__flex; auto | ].
    split; [ exact Hwf2 | ].
    split; [ exact Hm2 | exact Heqv2 ].
Qed.

(** Mid-insertion of a DEFINED flexible pair into a factoring (the
    [flex_def] twin of [a_inc_equiv_mid_insert_flex]). *)
Lemma a_inc_equiv_mid_insert_flex_def :
  forall Ξ β τd Θ0 Θ ρ1 ρ2 σ1 σ2 τ1 τ2,
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom ρ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  Θ ⊢ τ1 ≡ᵗ τ2 ->
  Θ ⊢ τ1 ≡ᵗ (msubst_ptyp ρ2 τd) ->
  a_inc_equiv (Ξ ++ Θ0) (ρ1 ++ ρ2) (σ1 ++ σ2) Θ ->
  a_inc_equiv (Ξ ++ (β ~ abind_flex_mono_def τd) ++ Θ0)
              (ρ1 ++ (β, τ1) :: ρ2) (σ1 ++ (β, τ2) :: σ2) Θ.
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros β τd Θ0 Θ ρ1 ρ2 σ1 σ2 τ1 τ2 Hdec Huq Hdρ Hdσ Heqτ Heqd Hie.
  - rewrite dom_nil in Hdρ, Hdσ.
    apply metasubst_dom_empty in Hdρ; apply metasubst_dom_empty in Hdσ;
      subst.
    simpl in Hie |- *.
    apply a_inc_equiv__flex_def;
      [ exact Hie | exact Heqτ | exact Heqd ].
  - inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Huρ : uniq (ρ1 ++ ρ2))
      by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
    assert (Huσ : uniq (σ1 ++ σ2))
      by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
    assert (HaΞ : a `notin` dom Ξ')
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    destruct ρ1 as [ | [ar tr] ρ1' ];
      [ exfalso; rewrite dom_nil in Hdρ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdρ in Hin; clear - Hin; fsetdec | ].
    destruct σ1 as [ | [asg ts] σ1' ];
      [ exfalso; rewrite dom_nil in Hdσ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
          by (simpl; fsetdec);
        rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
    assert (Harρ : ar `notin` dom ρ1')
      by (clear - Huρ; simpl_env in Huρ; solve_uniq).
    assert (Hasσ : asg `notin` dom σ1')
      by (clear - Huσ; simpl_env in Huσ; solve_uniq).
    simpl in Hie.
    inversion Hie as [ | S q1 q2 T aa u1 u2 Hie' Hequ | | | | ]; subst.
    simpl_env in Hdρ; simpl_env in Hdσ.
    simpl. apply a_inc_equiv__flex; [ | exact Hequ ].
    apply IH; auto.
    + clear - Hdρ Harρ HaΞ. simpl_env in *. fsetdec.
    + clear - Hdσ Hasσ HaΞ. simpl_env in *. fsetdec.
Qed.

Lemma a_inc_tvar_mid_strip_id : forall Ξ c Θ0 ρ Θ1,
  a_decls Ξ ->
  uniq (Ξ ++ (c ~ abind_tvar) ++ Θ0) ->
  is_id_msubst ρ ->
  (Ξ ++ (c ~ abind_tvar) ++ Θ0) ≤[ ρ ] ((c ~ abind_tvar) ++ Θ1) ->
  (Ξ ++ Θ0) ≤[ ρ ] Θ1.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros c Θ0 ρ Θ1 Hdec Huq Hid Hinc.
  - simpl in Hinc.
    destruct (a_inc_tvar_inv Hinc) as [Ξv [Θ2 [Heqt [Hsuf Hinc']]]].
    destruct Ξv as [ | [z bz] Ξv' ].
    + simpl in Heqt. inversion Heqt; subst. exact Hinc'.
    + exfalso. simpl in Heqt. inversion Heqt; subst.
      inversion Hsuf as [ | z0 b0 Ξ0 Hsuf0 Hsb ]; subst.
      inversion Hsb.
  - inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Hac : a <> c)
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ (c ~ abind_tvar) ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    simpl in Hinc.
    inversion Hinc as [ | Θs ρs Θts aa τ Hinc' Hwfτ Hmτ | | | | ]; subst.
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
(* ===================================================================== *)

Definition consis_complete_at (m : mu_ty) : Prop :=
  forall F Δ1 Δ2 Θ0 P0 P ρ Θ Ψ Qb,
    m = mu_consis Θ ρ P0 P Θ0 ->
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (forall X, X `in` (Δ1 `union` Δ2) -> binds X abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    Ψ ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P)) ≈ Qb ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis F Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           ad_precise_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb)).

Definition unify_complete_at (m : mu_ty) : Prop :=
  forall F Θ0 α β ρ Θ,
    m = mu_unify Θ ρ α β Θ0 ->
    a_wf_aenv Θ0 ->
    a_flex_tvar Θ0 α ->
    a_flex_tvar Θ0 β ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    Θ ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β) ->
    exists Θ1,
      Θ0 ⊲[ F ] α ≈ᵘ β ⊣ Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ).

Definition assign_complete_at (m : mu_ty) : Prop :=
  forall F Θ0 Ξ α P ρ Θ,
    m = mu_assign Θ ρ α P Ξ Θ0 ->
    a_decls Ξ ->
    a_wf_aenv (Ξ ++ Θ0) ->
    a_flex_tvar Θ0 α ->
    (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
    a_non_flex (Ξ ++ Θ0) P ->
    dom Ξ [<=] ftvar_in_pskl P ->
    (Ξ ++ Θ0) ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P))
                 ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α))) ->
    exists Θ1,
      Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> (Ξ ++ Θ0) ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv (Ξ ++ Θ0) ρ (msubst_compose ζ ρ1) Θ).

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

(** A hatted variable other than the head is hatted in the tail. *)
Lemma a_flex_tvar_strip_head : forall (γ : atom) b Θ0 δ,
  δ <> γ ->
  a_flex_tvar ((γ ~ b) ++ Θ0) δ ->
  a_flex_tvar Θ0 δ.
Proof.
  intros γ b Θ0 δ Hne [Hb | [τ Hb]];
    apply binds_cons_1 in Hb as [[Heq _] | Hb];
    solve [ exfalso; auto | left; exact Hb | right; exists τ; exact Hb ].
Qed.

(** The [V]-measure of an embedded monotype is its type-level measure. *)
Lemma Vpskl_ptyp_to_pskl : forall Θ θ A,
  Vpskl Θ θ (ptyp_to_pskl A) = Vptyp Θ θ A.
Proof.
  intros. unfold Vpskl, Vptyp.
  rewrite msubst_pskl_ptyp_to_pskl. rewrite msubst_pskl_ptyp_to_pskl.
  apply size_ptyp_to_pskl.
Qed.

(** [Vvar] ignores a target prefix the image cannot mention (the walk cases
    for rigid / term-variable heads truncate the solution target). *)
Lemma Vvar_strengthen_mid : forall Ξ (c : atom) b Θt ρ α,
  uniq (Ξ ++ (c ~ b) ++ Θt) ->
  a_wf_ptyp Θt (msubst_lookup ρ α) ->
  Vvar (Ξ ++ (c ~ b) ++ Θt) ρ α = Vvar Θt ρ α.
Proof.
  intros Ξ c b Θt ρ α Huniq Hwf. unfold Vvar.
  rewrite <- app_assoc in Huniq |- *.
  rewrite (downarrow_app_agree_ptyp _ _ _ Huniq
             (a_wf_ptyp_ftv_dom Hwf)).
  reflexivity.
Qed.

(** A variable outside the metasubstitution's domain keeps its free
    occurrences under it (substitution only adds or preserves them). *)
Lemma msubst_pskl_ftv_keep : forall ρ P X,
  X `notin` dom ρ ->
  X `in` ftvar_in_pskl P ->
  X `in` ftvar_in_pskl (msubst_pskl ρ P).
Proof.
  intros ρ P X Hnd;
    induction P as [ | n | x | P1 IH1 P2 IH2 | Pb IHb | | Pt IHt ];
    simpl; intros Hin; try solve [ fsetdec ].
  (* var_f : the occurrence IS X, whose lookup is itself *)
  assert (Heq : X = x) by (clear - Hin; fsetdec). subst x.
  rewrite (msubst_lookup_notin ρ Hnd). simpl. fsetdec.
Qed.

(** Extending Θ with a fresh rigid entry preserves the three fixed
    hypotheses of the ftv-survival inductions below. *)
Local Ltac ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY :=
  assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
    by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]);
  assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
    by (apply binds_cons_3; exact HbX);
  assert (HdefsY : forall β τ,
            binds β (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
            X `notin` ftvar_in_ptyp τ)
    by (intros β τ Hb;
        apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | exact (Hdefs _ _ Hb) ]).

(** Rigid free variables survive fill-hygienic refinement RIGHT-TO-LEFT:
    a rigid [X] (never mentioned by a Θ-definition) absent from the target
    is absent from the source.  This is the ftv-chase behind Ghost's
    [Δ2 ∩ ftv(P0) = ∅] side condition (and GhostR's mirror). *)
Lemma ad_refine_syn_f_rigid_ftv_rev : forall F Θ Δ Qs Qt X,
  a_wf_aenv Θ ->
  binds X abind_tvar Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
               X `notin` ftvar_in_ptyp τ) ->
  ad_refine_syn_f F Θ Δ Qs Qt ->
  X `notin` ftvar_in_bskl Qt ->
  X `notin` ftvar_in_bskl Qs.
Proof.
  intros F Θ Δ Qs Qt X Hwf HbX Hdefs Hr.
  induction Hr; intros Hout; simpl in *.
  - (* unit *) clear; fsetdec.
  - (* var *) clear - Hout; fsetdec.
  - (* arrow *)
    assert (Hn1 : X `notin` ftvar_in_bskl Q1)
      by (apply IHHr1;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    assert (Hn2 : X `notin` ftvar_in_bskl Q2)
      by (apply IHHr2;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    clear - Hn1 Hn2; fsetdec.
  - (* all (cofinite; Θ unchanged) *)
    pick fresh Y for (L `union` singleton X `union` ftvar_in_bskl P
                        `union` ftvar_in_bskl Q).
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl P (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) Hwf HbX Hdefs HnT) as HnS.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* hole *) clear; fsetdec.
  - (* tophole_remove *) exact (IHHr Hwf HbX Hdefs Hout).
  - (* tophole_fill (cofinite; Θ grows by the fresh rigid Y) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_bskl P `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl P (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    simpl in HnS. clear - HnS. fsetdec.
  - (* tophole_keep *) exact (IHHr Hwf HbX Hdefs Hout).
  - (* flex_l : the source is a defined flexible, never the rigid X *)
    assert (Hne : X <> α).
    { intro Heq; subst α.
      pose proof (binds_unique _ _ _ _ _ HbX H (a_wf_aenv_uniq Hwf)) as Hc;
        discriminate. }
    clear - Hne; fsetdec.
  - (* flex_r : unfold the target definition; its ftv avoids X *)
    apply IHHr; [ assumption | assumption | assumption | ].
    rewrite ftvar_in_bskl_ptyp_syn.
    apply (Hdefs _ _ H).
Qed.

(** The mirror on the JOIN: a rigid [X] absent from the join target is
    absent from the (painted) subject.  Drives GhostR's side condition. *)
Lemma ad_pat_consis_rigid_ftv_rev : forall Ψ Θ S Qt X,
  a_wf_aenv Θ ->
  binds X abind_tvar Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
               X `notin` ftvar_in_ptyp τ) ->
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  X `notin` ftvar_in_bskl Qt ->
  X `notin` ftvar_in_uskl S.
Proof.
  intros Ψ Θ S Qt X Hwf HbX Hdefs Hc.
  induction Hc; intros Hout; simpl in *.
  - (* unit *) clear; fsetdec.
  - (* var *) clear - Hout; fsetdec.
  - (* arrow *)
    assert (Hn1 : X `notin` ftvar_in_uskl R1)
      by (apply IHHc1;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    assert (Hn2 : X `notin` ftvar_in_uskl R2)
      by (apply IHHc2;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    clear - Hn1 Hn2; fsetdec.
  - (* forall_inh_tagged (cofinite; Θ grows) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_inh_untagged (cofinite; Θ grows) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn_tagged (cofinite; Θ grows) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn (cofinite; Θ grows) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* ghostg *) clear; fsetdec.
  - (* topholeg *) exact (IHHc Hwf HbX Hdefs Hout).
  - (* hole : the subject is the ghost hole, no free variables *)
    clear; fsetdec.
  - (* tophole *) exact (IHHc Hwf HbX Hdefs Hout).
  - (* tophole_inh (cofinite target; Θ grows; subject fixed) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    simpl in HnS. clear - HnS. fsetdec.
  - (* tophole_drop *) exact (IHHc Hwf HbX Hdefs Hout).
  - (* flex_l : the subject is a defined flexible, never the rigid X *)
    assert (Hne : X <> α).
    { intro Heq; subst α.
      pose proof (binds_unique _ _ _ _ _ HbX H (a_wf_aenv_uniq Hwf)) as Hc';
        discriminate. }
    clear - Hne; fsetdec.
  - (* flex_r : unfold the join definition; its ftv avoids X *)
    apply IHHc; [ assumption | assumption | assumption | ].
    rewrite ftvar_in_bskl_ptyp_syn.
    apply (Hdefs _ _ H).
Qed.

(** SCOPED variant of the join ftv-survival: the definition side condition
    only holds for definitions REACHABLE from the target's scope [D] (the
    truncated context of the SkipRigid stuck-check).  A rigid [X] outside
    [D] absent from a [D]-scoped target is absent from the subject. *)
Lemma ad_pat_consis_rigid_ftv_rev_scoped : forall Ψ Θ S Qt X D,
  a_wf_aenv Θ ->
  binds X abind_tvar Θ ->
  X `notin` D ->
  (forall γ τ, binds γ (abind_flex_mono_def τ) Θ -> γ `in` D ->
               ftvar_in_ptyp τ [<=] D) ->
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  ftvar_in_bskl Qt [<=] D ->
  X `notin` ftvar_in_uskl S.
Proof.
  intros Ψ Θ S Qt X D Hwf HbX HXD Hdefs Hc.
  revert D HXD Hdefs.
  induction Hc; intros D HXD Hdefs Hout; simpl in *.
  - (* unit *) clear; fsetdec.
  - (* var *) clear - Hout HXD; fsetdec.
  - (* arrow *)
    assert (Hn1 : X `notin` ftvar_in_uskl R1)
      by (apply (IHHc1 Hwf HbX D HXD Hdefs); clear - Hout; fsetdec).
    assert (Hn2 : X `notin` ftvar_in_uskl R2)
      by (apply (IHHc2 Hwf HbX D HXD Hdefs); clear - Hout; fsetdec).
    clear - Hn1 Hn2; fsetdec.
  - (* forall_inh_tagged (cofinite; Θ and D grow by the fresh Y) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall γ τ,
              binds γ (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
              γ `in` (add Y D) -> ftvar_in_ptyp τ [<=] (add Y D)).
    { intros γ τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : γ <> Y).
      { intro Heq; subst γ. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : γ `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : X `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y))).
    { apply (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY (add Y D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_inh_untagged *)
    pick fresh Y for (L `union` dom Θ `union` singleton X `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall γ τ,
              binds γ (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
              γ `in` (add Y D) -> ftvar_in_ptyp τ [<=] (add Y D)).
    { intros γ τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : γ <> Y).
      { intro Heq; subst γ. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : γ `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : X `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y))).
    { apply (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY (add Y D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn_tagged *)
    pick fresh Y for (L `union` dom Θ `union` singleton X `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall γ τ,
              binds γ (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
              γ `in` (add Y D) -> ftvar_in_ptyp τ [<=] (add Y D)).
    { intros γ τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : γ <> Y).
      { intro Heq; subst γ. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : γ `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : X `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y))).
    { apply (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY (add Y D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn *)
    pick fresh Y for (L `union` dom Θ `union` singleton X `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall γ τ,
              binds γ (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
              γ `in` (add Y D) -> ftvar_in_ptyp τ [<=] (add Y D)).
    { intros γ τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : γ <> Y).
      { intro Heq; subst γ. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : γ `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : X `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y))).
    { apply (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY (add Y D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* ghostg *) clear; fsetdec.
  - (* topholeg *) apply (IHHc Hwf HbX D HXD Hdefs Hout).
  - (* hole *) clear; fsetdec.
  - (* tophole *) apply (IHHc Hwf HbX D HXD Hdefs Hout).
  - (* tophole_inh *)
    pick fresh Y for (L `union` dom Θ `union` singleton X `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall γ τ,
              binds γ (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
              γ `in` (add Y D) -> ftvar_in_ptyp τ [<=] (add Y D)).
    { intros γ τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : γ <> Y).
      { intro Heq; subst γ. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : γ `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : X `notin` ftvar_in_uskl (uskl_tophole R)).
    { apply (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY (add Y D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    simpl in HnS. clear - HnS. fsetdec.
  - (* tophole_drop *) apply (IHHc Hwf HbX D HXD Hdefs Hout).
  - (* flex_l : the subject is a defined flexible, never the rigid X *)
    assert (Hne : X <> α).
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
Lemma ad_wf_pskl_msubst_inc : forall Θ0 ρ Θ Δ P,
  Θ0 ≤[ ρ ] Θ ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ Δ ⊢ₚₛᵃ P ->
  (forall X, X `in` Δ -> X `notin` dom ρ) ->
  Θ ⨟ Δ ⊢ₚₛᵃ (msubst_pskl ρ P).
Proof.
  intros Θ0 ρ Θ Δ P Hinc Hwf0 Hwf; induction Hwf; intros HΔ; simpl.
  - apply ad_wf_pskl__unit.
  - (* var : rigid occurrences stay; flexibles map to wf target types *)
    destruct H as [HXΔ | Hbt].
    + rewrite (msubst_lookup_notin ρ (HΔ _ HXΔ)). simpl.
      apply ad_wf_pskl__var; left; exact HXΔ.
    + apply a_wf_ptyp_to_wf_pskl.
      eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf0 | exact Hbt ].
  - apply ad_wf_pskl__arrow;
      [ apply IHHwf1 | apply IHHwf2 ]; try assumption.
  - (* all : open with a binder fresh from the substitution *)
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; eauto).
    apply ad_wf_pskl__all with (L := L `union` dom ρ).
    intros X HX.
    rewrite <- msubst_pskl_open_lc_local;
      [ | exact Hlcρ | clear - HX; fsetdec ].
    apply H0; [ clear - HX; fsetdec | exact Hinc | exact Hwf0 | ].
    intros Y HY.
    destruct (Y == X) as [-> | Hne].
    + clear - HX; fsetdec.
    + apply HΔ. clear - HY Hne; fsetdec.
  - apply ad_wf_pskl__hole.
  - (* tophole : the body is guarded and closed under Δ = ∅ *)
    apply ad_wf_pskl__tophole.
    + eapply guarded_pskl_msubst_inc; eauto.
    + apply IHHwf; [ exact Hinc | exact Hwf0 | ].
      intros Y HY. exfalso. clear - HY. fsetdec.
Qed.

(** The non-mono RE-INHERIT bridge (the OPT C-GhostR plan,
    prop_consis_complete.v:1752): an uncoloured refinement [A ⊳ B] whose two
    sides are JOINED at the syn painting re-inherits to the coloured
    refinement of the inh paintings.  [Θr] is the refinement context; [Θj]
    the join context, which extends [Θr] by rigid opens only (at the top
    level Θj = Θr).  The wf of [A] supplies guardedness of ⊤◇-bodies, which
    is what forces the join to strip/keep wrappers in lockstep with the
    refinement. *)
Lemma refine_join_reinherit : forall F Θr Δ A B,
  ad_refine_pskl_f F Θr Δ A B ->
  forall Θj,
  a_wf_aenv Θr ->
  a_wf_aenv Θj ->
  (forall x b, binds x b Θr -> binds x b Θj) ->
  Θr ⨟ Δ ⊢ₚₛᵃ A ->
  empty ⨟ Θj ⊨ₛᵃ (pskl_to_uskl A) ≈ (pskl_to_bskl_syn B) ->
  ad_refine_syn_f F Θr Δ (pskl_to_bskl_inh A) (pskl_to_bskl_inh B).
Proof.
  intros F Θr Δ A B Hr.
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
    | Hn : forall _, _ -> ad_wf_pskl _ _ _ |- _ => rename Hn into Hwfb
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
    intros X HX.
    rewrite <- pskl_to_bskl_inh_open, <- pskl_to_bskl_inh_open.
    apply (H0 X ltac:(clear - HX; fsetdec) ((X ~ abind_tvar) ++ Θj) Hwfr).
    + apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf ].
    + intros x b Hb. apply binds_cons_3. apply Hincl; exact Hb.
    + apply Hwfb. clear - HX; fsetdec.
    + rewrite pskl_to_uskl_open_var, pskl_to_bskl_syn_open.
      apply Hsub. clear - HX; fsetdec.
  - (* hole : the join forces the fill to be inh-invariant *)
    pose proof (consis_hole_target_inh Hj) as Hqi.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hqi.
    rewrite Hqi. apply ad_refine_syn_f__hole; [ exact H | exact H0 ].
  - (* tophole_remove : the join strips its subject ⊤◇ in lockstep *)
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    assert (HwfP : Θ ⨟ empty ⊢ₚₛᵃ P) by (inversion HwfA; assumption).
    assert (HwfPΔ : Θ ⨟ Δ ⊢ₚₛᵃ P)
      by (eapply ad_wf_pskl_delta_mono; [ exact HwfP | clear; fsetdec ]).
    apply ad_refine_syn_f__tophole_remove.
    apply (IHHr Θj Hwfr Hwf Hincl HwfPΔ).
    (* the join: ⊤◇⌊P⌋ ≈ syn Q must strip the subject wrapper *)
    inversion Hj; subst.
    + (* __tophole : the target would be a ⊤◇ — but the guarded [P]
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
  - (* tophole_fill : VACUOUS — no join matches a ⊤◇ subject against a
       ∀-syn target *)
    exfalso.
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    pick fresh X for (L `union` dom Θ).
    assert (HlcQX : lc_pskl (open_pskl_wrt_pskl Q (pskl_var_f X)))
      by (eapply ad_refine_pskl_f_lc_r; apply H; clear - Fr; fsetdec).
    assert (HlcQ : lc_bskl (pskl_to_bskl_syn (pskl_all_syn Q))).
    { apply pskl_to_bskl_syn_lc.
      apply (lc_pskl_all_syn_exists X). exact HlcQX. }
    inversion Hj; subst.
    (* only __tophole_drop survives the target shape; its stripped subject
       is guarded against a ∀-syn target *)
    match goal with
    | Hdrop : _ ⨟ _ ⊨ₛᵃ (pskl_to_uskl P) ≈ _ |- _ =>
        pose proof (ad_pat_consis_guarded_r Hdrop Hwf eq_refl HgP HlcQ)
          as Hbad
    end.
    inversion Hbad.
  - (* tophole_keep : the join keeps (or cannot drop) the wrapper *)
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    assert (HwfP : Θ ⨟ empty ⊢ₚₛᵃ P) by (inversion HwfA; assumption).
    assert (HwfPΔ : Θ ⨟ Δ ⊢ₚₛᵃ P)
      by (eapply ad_wf_pskl_delta_mono; [ exact HwfP | clear; fsetdec ]).
    apply ad_refine_syn_f__tophole_keep;
      [ apply guarded_pskl_to_bskl_inh; exact H | ].
    apply (IHHr Θj Hwfr Hwf Hincl HwfPΔ).
    inversion Hj; subst.
    + (* __tophole : both wrappers strip *) assumption.
    + (* __tophole_drop : the guarded stripped subject cannot join a ⊤◇ *)
      exfalso.
      assert (HlcQt : lc_bskl (bskl_tophole (pskl_to_bskl_syn Q))).
      { apply lc_bskl_tophole. apply pskl_to_bskl_syn_lc.
        eapply ad_refine_pskl_f_lc_r; exact Hr. }
      match goal with
      | Hdrop : _ ⨟ _ ⊨ₛᵃ (pskl_to_uskl P) ≈ _ |- _ =>
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
(*  premises can be rewritten with θ₁` (:2744) and Assign-Assign's        *)
(*  soundness needed as the ≡ˢ-subject transport: a join is invariant     *)
(*  under replacing its subject by an ≡ˢ-equivalent skeleton (the         *)
(*  equational theory only unfolds flexible definitions and is a          *)
(*  congruence elsewhere).  Mirrors [tyequiv_mono_consis_transport],      *)
(*  which covers only monotype subjects.                                  *)
(* --------------------------------------------------------------------- *)

(** Transport a ∀-syn subject componentwise: only [forall_inh_untagged] /
    [forall_syn] / [flex_r] can have an [all_syn] subject. *)
Lemma consis_forall_subject_transport : forall Ψ Θ S Qt,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  forall S0 T0 L0,
  S = uskl_all_syn S0 ->
  (forall X, X `notin` L0 -> forall Ψ' Q',
     Ψ' ⨟ ((X ~ abind_tvar) ++ Θ) ⊨ₛᵃ
       (open_uskl_wrt_uskl S0 (uskl_var_f X)) ≈ Q' ->
     Ψ' ⨟ ((X ~ abind_tvar) ++ Θ) ⊨ₛᵃ
       (open_uskl_wrt_uskl T0 (uskl_var_f X)) ≈ Q') ->
  Ψ ⨟ Θ ⊨ₛᵃ (uskl_all_syn T0) ≈ Qt.
Proof.
  intros Ψ Θ S Qt Hc; induction Hc; intros S0 T0 L0 HeqS Htr;
    try discriminate HeqS.
  - (* forall_inh_untagged *)
    inversion HeqS; subst.
    apply ad_pat_consis__forall_inh_untagged with (L := L `union` L0).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | ].
    apply H; clear - HX; fsetdec.
  - (* forall_syn *)
    inversion HeqS; subst.
    apply ad_pat_consis__forall_syn with (L := L `union` L0).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | ].
    apply H; clear - HX; fsetdec.
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

(** Transport a ⊤◇ subject componentwise.  The component transport is
    context-generalized because [tophole_inh] keeps the SAME subject under
    an extended context. *)
Lemma consis_tophole_subject_transport : forall Ψ Θ S Qt,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  a_wf_aenv Θ ->
  forall S0 T0,
  S = uskl_tophole S0 ->
  (forall Θ' Ψ' Q',
     a_wf_aenv Θ' ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     Ψ' ⨟ Θ' ⊨ₛᵃ S0 ≈ Q' -> Ψ' ⨟ Θ' ⊨ₛᵃ T0 ≈ Q') ->
  Ψ ⨟ Θ ⊨ₛᵃ (uskl_tophole T0) ≈ Qt.
Proof.
  intros Ψ Θ S Qt Hc; induction Hc; intros HwfΘ S0 T0 HeqS Htr;
    try discriminate HeqS.
  - (* tophole *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc ].
  - (* tophole_inh : same subject, extended context *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole_inh with (L := L `union` dom Θ).
    intros X HX.
    assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact HwfΘ ]).
    apply (H0 X ltac:(clear - HX; fsetdec) HwfX S0 T0 eq_refl).
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
    equivalence's context (the generality the ∀/⊤◇ congruences need). *)
Lemma skl_tyequiv_consis_transport : forall Θ A B,
  Θ ⊢ A ≡ˢ B ->
  forall Θ',
  a_wf_aenv Θ' ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall Ψ Qt, Ψ ⨟ Θ' ⊨ₛᵃ (pskl_to_uskl A) ≈ Qt ->
                Ψ ⨟ Θ' ⊨ₛᵃ (pskl_to_uskl B) ≈ Qt) /\
  (forall Ψ Qt, Ψ ⨟ Θ' ⊨ₛᵃ (pskl_to_uskl B) ≈ Qt ->
                Ψ ⨟ Θ' ⊨ₛᵃ (pskl_to_uskl A) ≈ Qt).
Proof.
  intros Θ A B Heq; induction Heq; intros Θ' Hwf' Hincl.
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
      intros X HX Ψ' Q' Hc'.
      assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ'))
        by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf' ]).
      assert (HinclX : forall x b, binds x b Θ ->
                binds x b ((X ~ abind_tvar) ++ Θ'))
        by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb).
      destruct (H0 X ltac:(clear - HX; fsetdec)
                  ((X ~ abind_tvar) ++ Θ') HwfX HinclX) as [Hl _].
      rewrite <- pskl_to_uskl_open_var in Hc'.
      rewrite <- pskl_to_uskl_open_var.
      apply Hl. exact Hc'.
    + eapply consis_forall_subject_transport with (L0 := L `union` dom Θ');
        [ exact Hc | reflexivity | ].
      intros X HX Ψ' Q' Hc'.
      assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ'))
        by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf' ]).
      assert (HinclX : forall x b, binds x b Θ ->
                binds x b ((X ~ abind_tvar) ++ Θ'))
        by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb).
      destruct (H0 X ltac:(clear - HX; fsetdec)
                  ((X ~ abind_tvar) ++ Θ') HwfX HinclX) as [_ Hr].
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
  apply ad_wf_pskl_mono_ptyp; assumption.
Qed.

(** Reflexivity of the uncoloured fill-hygienic refinement on a monotype. *)
Lemma ad_refine_pskl_f_mono_refl : forall F Θ Δ τ,
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  ad_refine_pskl_f F Θ Δ (ptyp_to_pskl τ) (ptyp_to_pskl τ).
Proof.
  intros F Θ Δ τ Hm Hwf.
  apply ad_refine_pskl_f_refl.
  apply ad_wf_pskl_mono_ptyp; assumption.
Qed.

(* --------------------------------------------------------------------- *)
(*  The ≡ˢ-SOURCE TRANSPORTS of the two refinement judgments — the        *)
(*  companions of [skl_tyequiv_consis_transport] for C-Arrow's (g)/(i)    *)
(*  premises and Assign-Assign.  Same architecture: per-source-shape      *)
(*  helpers (each chasing the [flex_r] target chains), then the main      *)
(*  induction on [≡ˢ].                                                    *)
(* --------------------------------------------------------------------- *)

(** Unfold a DEFINED source variable inside a Δ1-refinement: only [var] /
    [flex_l] / [flex_r] can have source [γ̂]. *)
Lemma ad_refine_syn_f_unfold_def_source : forall F Θ Δ S Qt,
  ad_refine_syn_f F Θ Δ S Qt ->
  a_wf_aenv Θ ->
  forall γ τ, S = bskl_var_f γ ->
  binds γ (abind_flex_mono_def τ) Θ ->
  ad_refine_syn_f F Θ Δ (ptyp_to_bskl_syn τ) Qt.
Proof.
  intros F Θ Δ S Qt Hr Hwf; induction Hr; intros γ0 τ0 HeqS Hb;
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
Lemma ad_refine_syn_f_arrow_source_transport : forall F Θ Δ S Qt,
  ad_refine_syn_f F Θ Δ S Qt ->
  forall S1 S2 T1 T2,
  S = bskl_arrow S1 S2 ->
  (forall Qt', ad_refine_syn_f F Θ Δ S1 Qt' ->
               ad_refine_syn_f F Θ Δ T1 Qt') ->
  (forall Qt', ad_refine_syn_f F Θ Δ S2 Qt' ->
               ad_refine_syn_f F Θ Δ T2 Qt') ->
  ad_refine_syn_f F Θ Δ (bskl_arrow T1 T2) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros S1' S2' T1 T2 HeqS Htr1 Htr2;
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
Lemma ad_refine_syn_f_forall_source_transport : forall F Θ Δ S Qt,
  ad_refine_syn_f F Θ Δ S Qt ->
  forall S0 T0 L0,
  S = bskl_all_inh S0 ->
  (forall X, X `notin` L0 -> forall Δ' Qt',
     ad_refine_syn_f F Θ Δ'
       (open_bskl_wrt_bskl S0 (bskl_var_f X)) Qt' ->
     ad_refine_syn_f F Θ Δ'
       (open_bskl_wrt_bskl T0 (bskl_var_f X)) Qt') ->
  ad_refine_syn_f F Θ Δ (bskl_all_inh T0) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros S0 T0 L0 HeqS Htr;
    try discriminate HeqS.
  - (* all *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__all with (L := L `union` L0).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | ].
    apply H; clear - HX; fsetdec.
  - (* flex_r *)
    eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport a ⊤◇ source componentwise.  Context-generalized: the
    [tophole_fill] premise keeps the SAME source under an extended Θ. *)
Lemma ad_refine_syn_f_tophole_source_transport : forall F Θ Δ S Qt,
  ad_refine_syn_f F Θ Δ S Qt ->
  a_wf_aenv Θ ->
  forall S0 T0,
  S = bskl_tophole S0 ->
  (forall Θ' Qt',
     a_wf_aenv Θ' ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     ad_refine_syn_f F Θ' Δ S0 Qt' ->
     ad_refine_syn_f F Θ' Δ T0 Qt') ->
  ad_refine_syn_f F Θ Δ (bskl_tophole T0) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros HwfΘ S0 T0 HeqS Htr;
    try discriminate HeqS.
  - (* tophole_remove *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__tophole_remove.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  - (* tophole_fill : same source, extended context *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__tophole_fill with (L := L `union` dom Θ).
    intros X HX.
    assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact HwfΘ ]).
    apply (H0 X ltac:(clear - HX; fsetdec) HwfX S0 T0 eq_refl).
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
Lemma skl_tyequiv_refine_syn_f_transport : forall Θ A B,
  Θ ⊢ A ≡ˢ B ->
  forall Θ',
  a_wf_aenv Θ' ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall F Δ Qt,
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh A) Qt ->
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh B) Qt) /\
  (forall F Δ Qt,
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh B) Qt ->
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh A) Qt).
Proof.
  intros Θ A B Heq; induction Heq; intros Θ' Hwf' Hincl.
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
      intros X HX Δ' Qt' Hr'.
      destruct (H0 X ltac:(clear - HX; fsetdec) Θ' Hwf' Hincl) as [Hl _].
      rewrite <- pskl_to_bskl_inh_open in Hr'.
      rewrite <- pskl_to_bskl_inh_open.
      apply Hl. exact Hr'.
    + eapply ad_refine_syn_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros X HX Δ' Qt' Hr'.
      destruct (H0 X ltac:(clear - HX; fsetdec) Θ' Hwf' Hincl) as [_ Hrr].
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
Lemma ad_refine_pskl_f_unfold_def_source : forall F Θ Δ S Qt,
  ad_refine_pskl_f F Θ Δ S Qt ->
  a_wf_aenv Θ ->
  forall γ τ, S = pskl_var_f γ ->
  binds γ (abind_flex_mono_def τ) Θ ->
  ad_refine_pskl_f F Θ Δ (ptyp_to_pskl τ) Qt.
Proof.
  intros F Θ Δ S Qt Hr Hwf; induction Hr; intros γ0 τ0 HeqS Hb;
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
Lemma ad_refine_pskl_f_arrow_source_transport : forall F Θ Δ S Qt,
  ad_refine_pskl_f F Θ Δ S Qt ->
  forall S1 S2 T1 T2,
  S = pskl_arrow S1 S2 ->
  (forall Qt', ad_refine_pskl_f F Θ Δ S1 Qt' ->
               ad_refine_pskl_f F Θ Δ T1 Qt') ->
  (forall Qt', ad_refine_pskl_f F Θ Δ S2 Qt' ->
               ad_refine_pskl_f F Θ Δ T2 Qt') ->
  ad_refine_pskl_f F Θ Δ (pskl_arrow T1 T2) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros S1' S2' T1 T2 HeqS Htr1 Htr2;
    try discriminate HeqS.
  - (* arrow *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__arrow; [ apply Htr1 | apply Htr2 ]; assumption.
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport a ∀-syn source componentwise (uncoloured; Δ grows). *)
Lemma ad_refine_pskl_f_forall_source_transport : forall F Θ Δ S Qt,
  ad_refine_pskl_f F Θ Δ S Qt ->
  forall S0 T0 L0,
  S = pskl_all_syn S0 ->
  (forall X, X `notin` L0 -> forall Δ' Qt',
     ad_refine_pskl_f F Θ Δ'
       (open_pskl_wrt_pskl S0 (pskl_var_f X)) Qt' ->
     ad_refine_pskl_f F Θ Δ'
       (open_pskl_wrt_pskl T0 (pskl_var_f X)) Qt') ->
  ad_refine_pskl_f F Θ Δ (pskl_all_syn T0) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros S0 T0 L0 HeqS Htr;
    try discriminate HeqS.
  - (* all *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__all with (L := L `union` L0).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | ].
    apply H; clear - HX; fsetdec.
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport a ⊤◇ source componentwise (uncoloured; context-generalized
    for [tophole_fill]). *)
Lemma ad_refine_pskl_f_tophole_source_transport : forall F Θ Δ S Qt,
  ad_refine_pskl_f F Θ Δ S Qt ->
  a_wf_aenv Θ ->
  forall S0 T0,
  S = pskl_tophole S0 ->
  (forall Θ' Qt',
     a_wf_aenv Θ' ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     ad_refine_pskl_f F Θ' Δ S0 Qt' ->
     ad_refine_pskl_f F Θ' Δ T0 Qt') ->
  ad_refine_pskl_f F Θ Δ (pskl_tophole T0) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros HwfΘ S0 T0 HeqS Htr;
    try discriminate HeqS.
  - (* tophole_remove *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__tophole_remove.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  - (* tophole_fill *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__tophole_fill with (L := L `union` dom Θ).
    intros X HX.
    assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact HwfΘ ]).
    apply (H0 X ltac:(clear - HX; fsetdec) HwfX S0 T0 eq_refl).
    intros Θ' Qt' Hwf' Hincl' Hr'.
    apply (Htr Θ' Qt' Hwf'); [ | exact Hr' ].
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
Lemma skl_tyequiv_refine_pskl_f_transport : forall Θ A B,
  Θ ⊢ A ≡ˢ B ->
  forall Θ',
  a_wf_aenv Θ' ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall F Δ Qt,
     ad_refine_pskl_f F Θ' Δ A Qt ->
     ad_refine_pskl_f F Θ' Δ B Qt) /\
  (forall F Δ Qt,
     ad_refine_pskl_f F Θ' Δ B Qt ->
     ad_refine_pskl_f F Θ' Δ A Qt).
Proof.
  intros Θ A B Heq; induction Heq; intros Θ' Hwf' Hincl.
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
    split; intros F Δ Qt Hr.
    + eapply ad_refine_pskl_f_unfold_def_source;
        [ exact Hr | exact Hwf' | reflexivity | exact HbΘ' ].
    + eapply ad_refine_pskl_f__flex_l; [ exact HbΘ' | exact Hr ].
  - (* arrow *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros F Δ Qt Hr.
    + eapply ad_refine_pskl_f_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1l | apply H2l ].
    + eapply ad_refine_pskl_f_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1r | apply H2r ].
  - (* all *)
    split; intros F Δ Qt Hr.
    + eapply ad_refine_pskl_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros X HX Δ' Qt' Hr'.
      destruct (H0 X ltac:(clear - HX; fsetdec) Θ' Hwf' Hincl) as [Hl _].
      apply Hl. exact Hr'.
    + eapply ad_refine_pskl_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros X HX Δ' Qt' Hr'.
      destruct (H0 X ltac:(clear - HX; fsetdec) Θ' Hwf' Hincl) as [_ Hrr].
      apply Hrr. exact Hr'.
  - (* tophole *)
    split; intros F Δ Qt Hr.
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
Lemma ad_wf_pskl_to_a_wf_pskl : forall Θ Δ P,
  ad_wf_pskl Θ Δ P ->
  forall Θa,
  (forall x b, binds x b Θ -> binds x b Θa) ->
  (forall X, X `in` Δ -> a_binds_tvar X Θa) ->
  a_wf_pskl Θa P.
Proof.
  intros Θ Δ P Hwfd; induction Hwfd; intros Θa Hincl HΔ.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HXΔ | Hbt]; [ apply HΔ; exact HXΔ | ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ];
      apply Hincl; exact Hb.
  - apply a_wf_pskl__arrow;
      [ apply IHHwfd1 | apply IHHwfd2 ]; assumption.
  - apply a_wf_pskl__all with (L := L).
    intros X HX.
    apply H0; [ exact HX | | ].
    + intros x b Hb. apply binds_cons_3. apply Hincl; exact Hb.
    + intros Y HY. destruct (Y == X) as [-> | Hne].
      * left. unfold binds. left. reflexivity.
      * destruct (HΔ Y ltac:(clear - HY Hne; fsetdec))
          as [Hb | [Hb | [τ Hb]]];
          [ left | right; left | right; right; exists τ ];
          apply binds_cons_3; exact Hb.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole.
    apply IHHwfd; [ exact Hincl | ].
    intros Y HY. exfalso. clear - HY. fsetdec.
Qed.

(** The join's target erases to a well-formed (Δ-free) skeleton — the
    output-regularity C-Arrow's precision transport needs. *)
Lemma ad_pat_consis_target_wf : forall Ψ Θ S Qt,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  a_wf_pskl Θ (bskl_to_pskl Qt).
Proof.
  intros Ψ Θ S Qt Hc; induction Hc; simpl.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var; exact H0.
  - apply a_wf_pskl__arrow; assumption.
  - (* forall_inh_tagged *)
    apply a_wf_pskl__all with (L := L).
    intros X HX. rewrite <- bskl_to_pskl_open. apply H0; exact HX.
  - (* forall_inh_untagged *)
    apply a_wf_pskl__all with (L := L).
    intros X HX. rewrite <- bskl_to_pskl_open. apply H0; exact HX.
  - (* forall_syn_tagged *)
    apply a_wf_pskl__all with (L := L).
    intros X HX. rewrite <- bskl_to_pskl_open. apply H0; exact HX.
  - (* forall_syn *)
    apply a_wf_pskl__all with (L := L).
    intros X HX. rewrite <- bskl_to_pskl_open. apply H0; exact HX.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; assumption.
  - (* hole : the fill is wf by the rule's own premise *)
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    eapply ad_wf_pskl_to_a_wf_pskl;
      [ exact H0 | intros x b Hb; exact Hb
      | intros Y HY; exfalso; clear - HY; fsetdec ].
  - apply a_wf_pskl__tophole; assumption.
  - (* tophole_inh *)
    apply a_wf_pskl__all with (L := L).
    intros X HX. rewrite <- bskl_to_pskl_open. apply H0; exact HX.
  - (* tophole_drop *) assumption.
  - (* flex_l *) assumption.
  - (* flex_r *)
    apply a_wf_pskl__var. right; right; exists τ; exact H.
Qed.

(** The empty hygiene set is free: the plain refinement IS the
    fill-hygienic one at [F = ∅] (the hole rule's ∅-disjointness is
    trivial).  Lets the precision goal reuse the [_f] transports. *)
Lemma ad_refine_syn_f_of_plain : forall Θ Δ Q P,
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ P ->
  ad_refine_syn_f empty Θ Δ Q P.
Proof.
  intros Θ Δ Q P H; induction H;
    try solve [ eauto using ad_refine_syn_f ].
  apply ad_refine_syn_f__hole; [ clear; fsetdec | exact H ].
Qed.

(** An inherited quantifier never refines to a guarded skeleton (the target
    of every rule applicable to an [all_inh] source is an [all_inh] or a
    defined flexible whose unfolding is a monotype painting — itself guarded,
    recursing).  Kills the [P0 = ∀.P0'] sub-case of C-UnivGhost2. *)
Lemma ad_refine_syn_f_all_inh_guarded_absurd : forall F Θ Δ Q R,
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ (bskl_all_inh Q) R ->
  guarded_bskl R ->
  False.
Proof.
  intros F Θ Δ Q R Hwf Hr.
  remember (bskl_all_inh Q) as S eqn:HeqS.
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
Lemma ad_refine_syn_f_flex_target_unfold : forall F Θ Δ S α τ,
  a_wf_aenv Θ ->
  binds α (abind_flex_mono_def τ) Θ ->
  (forall X, X `in` Δ -> binds X abind_tvar Θ) ->
  AtomSetImpl.inter F (ftvar_in_ptyp τ) [=] empty ->
  ad_refine_syn_f F Θ Δ S (bskl_var_f α) ->
  ad_refine_syn_f F Θ Δ S (ptyp_to_bskl_syn τ).
Proof.
  intros F Θ Δ S α τ Hwf Hbα HΔ Hdisj Hr.
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
  assert (Hwfτ : a_wf_ptyp Θ τ) by (eapply a_wf_aenv_binds_def_wf; eauto).
  remember (bskl_var_f α) as T eqn:HeqT.
  induction Hr; try discriminate HeqT.
  - (* __var : the source IS the defined flexible; unfold it on the left *)
    inversion HeqT; subst X.
    assert (Hbtα : binds α abind_tvar Θ \/ binds α abind_flex_mono Θ \/
                   (exists τ', binds α (abind_flex_mono_def τ') Θ)).
    { destruct H as [HinΔ | Hbt]; [ left; apply HΔ; exact HinΔ | exact Hbt ]. }
    destruct Hbtα as [Hb | [Hb | [τ' Hb]]];
      try solve [ pose proof (binds_unique _ _ _ _ _ Hb Hbα
                                (a_wf_aenv_uniq Hwf)) as Hcon; discriminate ].
    eapply ad_refine_syn_f__flex_l; [ exact Hbα | ].
    apply ad_refine_syn_f_mono_refl; assumption.
  - (* __hole : the fill is the defined flexible; refill with its definition *)
    destruct P as [ | n | δ | | | | ]; simpl in HeqT; try discriminate.
    inversion HeqT; subst δ.
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
Lemma ad_refine_pskl_f_flex_target_unfold : forall F Θ Δ S α τ,
  a_wf_aenv Θ ->
  binds α (abind_flex_mono_def τ) Θ ->
  (forall X, X `in` Δ -> binds X abind_tvar Θ) ->
  AtomSetImpl.inter F (ftvar_in_ptyp τ) [=] empty ->
  ad_refine_pskl_f F Θ Δ S (pskl_var_f α) ->
  ad_refine_pskl_f F Θ Δ S (ptyp_to_pskl τ).
Proof.
  intros F Θ Δ S α τ Hwf Hbα HΔ Hdisj Hr.
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
  assert (Hwfτ : a_wf_ptyp Θ τ) by (eapply a_wf_aenv_binds_def_wf; eauto).
  remember (pskl_var_f α) as T eqn:HeqT.
  induction Hr; try discriminate HeqT.
  - (* __var *)
    inversion HeqT; subst X.
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
  intros F Θ0 α β ρ Θ Hm Hwf Hfα Hfβ Hinc Hwfth Heq. subst m.
  destruct (α == β) as [-> | Hne].
  { (* Flex-Flex-Id : axiom, Θ1 = Θ0; ζ := ρ. *)
    exists Θ0. split; [ apply a_unify__flex_id; exact Hfα | ].
    intros ρ1 Hid Hinc1. exists ρ.
    exact (opt_axiom_factor Hwf Hid Hinc1 Hinc). }
  assert (Hβα : β <> α) by auto.
  destruct Θ0 as [ | [γ b] Θ0' ].
  { exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb. }
  destruct b as [ | A | Q | | τdef ].
  - (* head [γ ~ tvar] : Flex-Flex-Skip' (rigid). *)
    inversion Hwf as [ | | | | | γh Θh Hnd Hwf0 ]; subst.
    assert (Hγα : α <> γ)
      by (intros ->; destruct Hfα as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hγβ : β <> γ)
      by (intros ->; destruct Hfβ as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hfα0 : a_flex_tvar Θ0' α)
      by (eapply a_flex_tvar_strip_head; [ exact Hγα | exact Hfα ]).
    assert (Hfβ0 : a_flex_tvar Θ0' β)
      by (eapply a_flex_tvar_strip_head; [ exact Hγβ | exact Hfβ ]).
    assert (Hbtα : a_binds_tvar α Θ0') by (right; exact Hfα0).
    assert (Hbtβ : a_binds_tvar β Θ0') by (right; exact Hfβ0).
    apply a_inc_tvar_inv in Hinc as [Ξ [Θ2 [-> [HΞ Hinc']]]].
    assert (Hwfth2 : a_wf_aenv Θ2)
      by (rewrite <- app_assoc in Hwfth;
          apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
    assert (Hwflα : a_wf_ptyp Θ2 (msubst_lookup ρ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]).
    assert (Hwflβ : a_wf_ptyp Θ2 (msubst_lookup ρ β))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]).
    assert (Heq2 : Θ2 ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β)).
    { eapply a_tyequiv_strengthen_mono_mid;
        [ exact Hwfth | exact Hwflα
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Hwflβ
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Heq ]. }
    assert (Huniq : uniq (Ξ ++ (γ ~ abind_tvar) ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hlt : mu_lt (mu_unify Θ2 ρ α β Θ0')
                        (mu_unify (Ξ ++ (γ ~ abind_tvar) ++ Θ2) ρ α β
                                  ((γ ~ abind_tvar) ++ Θ0'))).
    { unfold mu_unify. apply mu_lt_intro. right. split.
      - unfold V_unify.
        rewrite (@Vvar_strengthen_mid Ξ γ abind_tvar Θ2 ρ α Huniq Hwflα).
        rewrite (@Vvar_strengthen_mid Ξ γ abind_tvar Θ2 ρ β Huniq Hwflβ).
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add γ F) Θ0' α β ρ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu Hopt']].
    exists ((γ ~ abind_tvar) ++ Θ1'). split.
    { apply a_unify__skip_other; [ left; reflexivity | exact Hu ]. }
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : Θ0' ≤[ ρ1 ] Θ1')
      by (eapply a_inc_id_mid_strip; [ left; reflexivity | exact Hinc1 ]).
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
    exists ζ'. split.
    + apply a_inc__tvar; [ exact Hζ' | exact HΞ ].
    + apply a_inc_equiv__tvar; [ exact Hie' | exact HΞ ].
  - (* head [x ~ var_typ A] : Flex-Flex-Skip' (semantic type middle). *)
    destruct (a_wf_aenv_var_typ_inv Hwf) as [Hnd [HwfA Hwf0]].
    assert (Hγα : α <> γ)
      by (intros ->; destruct Hfα as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hγβ : β <> γ)
      by (intros ->; destruct Hfβ as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hfα0 : a_flex_tvar Θ0' α)
      by (eapply a_flex_tvar_strip_head; [ exact Hγα | exact Hfα ]).
    assert (Hfβ0 : a_flex_tvar Θ0' β)
      by (eapply a_flex_tvar_strip_head; [ exact Hγβ | exact Hfβ ]).
    assert (Hbtα : a_binds_tvar α Θ0') by (right; exact Hfα0).
    assert (Hbtβ : a_binds_tvar β Θ0') by (right; exact Hfβ0).
    apply a_inc_var_inv in Hinc as [Ξ [A' [Θ2 [-> [HA'eq [HΞ Hinc']]]]]].
    assert (Hwfth2 : a_wf_aenv Θ2)
      by (rewrite <- app_assoc in Hwfth;
          apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
    assert (Hwflα : a_wf_ptyp Θ2 (msubst_lookup ρ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]).
    assert (Hwflβ : a_wf_ptyp Θ2 (msubst_lookup ρ β))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]).
    assert (Heq2 : Θ2 ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β)).
    { eapply a_tyequiv_strengthen_mono_mid;
        [ exact Hwfth | exact Hwflα
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Hwflβ
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Heq ]. }
    assert (Huniq : uniq (Ξ ++ (γ ~ abind_var_typ A') ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hlt : mu_lt (mu_unify Θ2 ρ α β Θ0')
                        (mu_unify (Ξ ++ (γ ~ abind_var_typ A') ++ Θ2) ρ α β
                                  ((γ ~ abind_var_typ A) ++ Θ0'))).
    { unfold mu_unify. apply mu_lt_intro. right. split.
      - unfold V_unify.
        rewrite (@Vvar_strengthen_mid Ξ γ (abind_var_typ A') Θ2 ρ α Huniq Hwflα).
        rewrite (@Vvar_strengthen_mid Ξ γ (abind_var_typ A') Θ2 ρ β Huniq Hwflβ).
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add γ F) Θ0' α β ρ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu Hopt']].
    exists ((γ ~ abind_var_typ A) ++ Θ1'). split.
    { apply a_unify__skip_other;
        [ right; left; exists A; reflexivity | exact Hu ]. }
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : Θ0' ≤[ ρ1 ] Θ1')
      by (eapply a_inc_id_mid_strip;
          [ right; left; exists A; reflexivity | exact Hinc1 ]).
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
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
    assert (Hγα : α <> γ)
      by (intros ->; destruct Hfα as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hγβ : β <> γ)
      by (intros ->; destruct Hfβ as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hfα0 : a_flex_tvar Θ0' α)
      by (eapply a_flex_tvar_strip_head; [ exact Hγα | exact Hfα ]).
    assert (Hfβ0 : a_flex_tvar Θ0' β)
      by (eapply a_flex_tvar_strip_head; [ exact Hγβ | exact Hfβ ]).
    assert (Hbtα : a_binds_tvar α Θ0') by (right; exact Hfα0).
    assert (Hbtβ : a_binds_tvar β Θ0') by (right; exact Hfβ0).
    apply a_inc_var_skl_inv in Hinc as [Ξ [P' [Θ2 [-> [HP'eq [HΞ Hinc']]]]]].
    assert (Hwfth2 : a_wf_aenv Θ2)
      by (rewrite <- app_assoc in Hwfth;
          apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
    assert (Hwflα : a_wf_ptyp Θ2 (msubst_lookup ρ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]).
    assert (Hwflβ : a_wf_ptyp Θ2 (msubst_lookup ρ β))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]).
    assert (Heq2 : Θ2 ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β)).
    { eapply a_tyequiv_strengthen_mono_mid;
        [ exact Hwfth | exact Hwflα
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Hwflβ
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Heq ]. }
    assert (Huniq : uniq (Ξ ++ (γ ~ abind_var_skl P') ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hlt : mu_lt (mu_unify Θ2 ρ α β Θ0')
                        (mu_unify (Ξ ++ (γ ~ abind_var_skl P') ++ Θ2) ρ α β
                                  ((γ ~ abind_var_skl Q) ++ Θ0'))).
    { unfold mu_unify. apply mu_lt_intro. right. split.
      - unfold V_unify.
        rewrite (@Vvar_strengthen_mid Ξ γ (abind_var_skl P') Θ2 ρ α Huniq Hwflα).
        rewrite (@Vvar_strengthen_mid Ξ γ (abind_var_skl P') Θ2 ρ β Huniq Hwflβ).
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add γ F) Θ0' α β ρ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu Hopt']].
    exists ((γ ~ abind_var_skl Q) ++ Θ1'). split.
    { apply a_unify__skip_other;
        [ right; right; exists Q; reflexivity | exact Hu ]. }
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : Θ0' ≤[ ρ1 ] Θ1')
      by (eapply a_inc_id_mid_strip;
          [ right; right; exists Q; reflexivity | exact Hinc1 ]).
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
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
  - (* head [γ̂] undefined flexible : Flex-Flex-L / Flex-Flex-R / Skip. *)
    inversion Hwf as [ | γh Θh Hnd Hwf0 | | | | ]; subst.
    destruct (γ == α) as [-> | Hγα].
    + (* Flex-Flex-L : α̂ ≔ β̂; axiom, ζ := ρ. *)
      inversion Hinc as [ | Θs ρs Θt αs τ Hinc' Hwfτ Hmτ [Heqα Heqρ] Heqt
                        | | | | ]; subst.
      assert (Hfβ0 : a_flex_tvar Θ0' β)
        by (eapply a_flex_tvar_strip_head; [ exact Hβα | exact Hfβ ]).
      exists ((α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0'). split.
      { apply a_unify__flex_l; [ exact Hne | exact Hfβ0 ]. }
      intros ρ1 Hid Hinc1. exists ((α, τ) :: ρs). split.
      * apply a_inc__flex_def; auto.
        rewrite msubst_lookup_cons_eq in Heq.
        rewrite (msubst_lookup_cons_neq τ ρs Hβα) in Heq.
        exact Heq.
      * rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
        apply a_inc_equiv_refl; exact Hinc.
    + destruct (γ == β) as [-> | Hγβ].
      * (* Flex-Flex-R : β̂ ≔ α̂; axiom, ζ := ρ. *)
        inversion Hinc as [ | Θs ρs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqρ] Heqt
                          | | | | ]; subst.
        assert (Hγα' : α <> β) by exact Hne.
        assert (Hfα0 : a_flex_tvar Θ0' α)
          by (eapply a_flex_tvar_strip_head; [ exact Hne | exact Hfα ]).
        exists ((β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0'). split.
        { apply a_unify__flex_r; [ exact Hne | exact Hfα0 ]. }
        intros ρ1 Hid Hinc1. exists ((β, τ) :: ρs). split.
        -- apply a_inc__flex_def; auto.
           rewrite msubst_lookup_cons_eq in Heq.
           rewrite (msubst_lookup_cons_neq τ ρs Hγα') in Heq.
           apply a_tyequiv__sym; exact Heq.
        -- rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
           apply a_inc_equiv_refl; exact Hinc.
      * (* Flex-Flex-Skip : γ̂ ∉ {α̂, β̂} walked past. *)
        inversion Hinc as [ | Θs ρs Θt γs τγ Hincs Hwfτ Hmτ [Heqγ Heqρ] Heqt
                          | | | | ]; subst.
        assert (Hαγ : α <> γ) by auto.
        assert (Hβγ : β <> γ) by auto.
        assert (Hfα0 : a_flex_tvar Θ0' α)
          by (eapply a_flex_tvar_strip_head; [ exact Hαγ | exact Hfα ]).
        assert (Hfβ0 : a_flex_tvar Θ0' β)
          by (eapply a_flex_tvar_strip_head; [ exact Hβγ | exact Hfβ ]).
        rewrite (msubst_lookup_cons_neq τγ ρs Hαγ) in Heq.
        rewrite (msubst_lookup_cons_neq τγ ρs Hβγ) in Heq.
        assert (Hlt : mu_lt (mu_unify Θ ρs α β Θ0')
                            (mu_unify Θ ((γ, τγ) :: ρs) α β
                                      ((γ ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_unify. apply mu_lt_intro. right. split.
          - unfold V_unify, Vvar.
            rewrite (msubst_lookup_cons_neq τγ ρs Hαγ).
            rewrite (msubst_lookup_cons_neq τγ ρs Hβγ).
            reflexivity.
          - left. simpl. lia. }
        destruct (IH _ Hlt) as [_ [HuIH _]].
        destruct (HuIH (add γ F) Θ0' α β ρs Θ eq_refl Hwf0 Hfα0 Hfβ0
                       Hincs Hwfth Heq) as [Θ1' [Hu Hopt']].
        exists ((γ ~ abind_flex_mono) ++ Θ1'). split.
        { apply a_unify__flex_skip;
            [ auto | auto | exact Hu ]. }
        intros ρ1 Hid Hinc1.
        inversion Hinc1 as [ | Θp ρp Θq γp τp Hincp Hwfp Hmp [Heqγ1 Heqρ1] Heqt1
                           | | | | ]; subst.
        apply is_id_msubst_inv in Hid as [Heqτp Hid']; subst τp.
        destruct (a_unify_sound Hu Hwf0)
          as [[[w [Hidw Hincw]] _] _].
        assert (Hw : ρp = w)
          by (eapply is_id_inc_unique; eauto).
        subst w.
        assert (Hγw : γ `notin` dom ρp)
          by (pose proof (a_inc_dom_sub Hincw) as Hs; clear - Hs Hnd; fsetdec).
        destruct (Hopt' ρp Hid' Hincw) as [ζ' [Hζ' Hie']].
        exists ((γ, τγ) :: ζ'). split.
        -- apply a_inc__flex; auto.
        -- assert (Heqc : msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: ρp)
                         = (γ, τγ) :: msubst_compose ζ' ρp).
           { change (msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: ρp))
               with ((γ, msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                     :: msubst_compose ((γ, τγ) :: ζ') ρp).
             rewrite (msubst_compose_cons_l_id τγ ζ' Hid' Hγw).
             change (msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
               with (msubst_lookup ((γ, τγ) :: ζ') γ).
             rewrite msubst_lookup_cons_eq. reflexivity. }
           rewrite Heqc.
           apply a_inc_equiv__flex; [ exact Hie' | ].
           apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτ.
  - (* head [γ̂ ≔ τdef] : Flex-Flex-Assign, the back-edge into part 1. *)
    inversion Hwf as [ | | γh τh Θh Hnd Hwfτd Hmτd Hwf0 | | | ]; subst.
    inversion Hinc as [ | | Θs ρs Θt γs τd τγ Hinc' Hwfτγ Hmτγ Heqd
                          [Heqγ Heqρ] Heqt | | | ]; subst.
    (* the substituted subjects and their facts, uniformly in the variable *)
    assert (Hgen : forall δ,
        a_flex_tvar ((γ ~ abind_flex_mono_def τdef) ++ Θ0') δ ->
        a_wf_ptyp Θ0' (subst_ptyp_in_ptyp τdef γ (ptyp_var_f δ)) /\
        mono_ptyp (subst_ptyp_in_ptyp τdef γ (ptyp_var_f δ)) /\
        Θ ⊢ (msubst_ptyp ρs (subst_ptyp_in_ptyp τdef γ (ptyp_var_f δ)))
          ≡ᵗ (msubst_lookup ((γ, τγ) :: ρs) δ)).
    { intros δ Hfδ. cbn [subst_ptyp_in_ptyp].
      match goal with
      | |- context [if ?s then _ else _] => destruct s as [-> | Hδγ]
      end.
      - repeat split;
          [ exact Hwfτd | exact Hmτd
          | rewrite msubst_lookup_cons_eq;
            apply a_tyequiv__sym; exact Heqd ].
      - assert (Hfδ' : a_flex_tvar Θ0' δ)
          by (eapply a_flex_tvar_strip_head; [ exact Hδγ | exact Hfδ ]).
        repeat split.
        + apply a_wf_ptyp__var. right. exact Hfδ'.
        + apply mono_ptyp__var.
        + rewrite (msubst_lookup_cons_neq τγ ρs Hδγ).
          cbn [msubst_ptyp].
          apply a_tyequiv__refl. apply mono_ptyp_lc.
          eapply a_inc_lookup_mono; exact Hinc'. }
    destruct (Hgen α Hfα) as [HwfAσ [HmAσ HeqAρ]].
    destruct (Hgen β Hfβ) as [HwfBσ [HmBσ HeqBρ]].
    clear Hgen.
    set (Aσ := subst_ptyp_in_ptyp τdef γ (ptyp_var_f α)) in *.
    set (Bσ := subst_ptyp_in_ptyp τdef γ (ptyp_var_f β)) in *.
    (* the sub-node's solution facts *)
    assert (HmA' : mono_ptyp (msubst_ptyp ρs Aσ))
      by (eapply mono_ptyp_msubst; [ exact Hinc' | exact HmAσ ]).
    assert (HmB' : mono_ptyp (msubst_ptyp ρs Bσ))
      by (eapply mono_ptyp_msubst; [ exact Hinc' | exact HmBσ ]).
    assert (HwfA' : a_wf_ptyp Θ (msubst_ptyp ρs Aσ))
      by (eapply a_wf_ptyp_msubst; [ exact HwfAσ | exact Hwf0 | exact Hinc' ]).
    assert (HwfB' : a_wf_ptyp Θ (msubst_ptyp ρs Bσ))
      by (eapply a_wf_ptyp_msubst; [ exact HwfBσ | exact Hwf0 | exact Hinc' ]).
    assert (HeqAB : Θ ⊢ (msubst_ptyp ρs Aσ) ≡ᵗ (msubst_ptyp ρs Bσ)).
    { eapply a_tyequiv__trans; [ exact HeqAρ | ].
      eapply a_tyequiv__trans; [ exact Heq | ].
      apply a_tyequiv__sym; exact HeqBρ. }
    assert (Hjoin0 : empty ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl_syn (msubst_ptyp ρs Aσ))
                       ≈ (ptyp_to_bskl_syn (msubst_ptyp ρs Bσ))).
    { apply tyequiv_mono_consis;
        [ exact HeqAB | exact Hwfth | exact HmA'
        | intros X HX; eapply a_wf_ptyp_ftv_tvarish;
            [ exact HwfA' | exact HX ] ]. }
    assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρs (ptyp_to_pskl Aσ)))
              ≈ (ptyp_to_bskl_syn (msubst_ptyp ρs Bσ)))
      by (rewrite msubst_pskl_ptyp_to_pskl, pskl_to_uskl_ptyp; exact Hjoin0).
    assert (Hrs' : ad_refine_syn_f empty Θ empty
              (pskl_to_bskl_inh (msubst_pskl ρs (ptyp_to_pskl Bσ)))
              (ptyp_to_bskl_syn (msubst_ptyp ρs Bσ))).
    { rewrite msubst_pskl_ptyp_to_pskl.
      replace (pskl_to_bskl_inh (ptyp_to_pskl (msubst_ptyp ρs Bσ)))
        with (pskl_to_bskl_inh (uskl_to_pskl (ptyp_to_uskl_syn (msubst_ptyp ρs Bσ))))
        by (rewrite uskl_to_pskl_ptyp; reflexivity).
      eapply ad_pat_consis_refine_syn_f_mono;
        [ apply consis_mono_refl;
            [ exact HmB'
            | intros X HX; eapply a_wf_ptyp_ftv_tvarish;
                [ exact HwfB' | exact HX ] ]
        | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmB'
        | clear; fsetdec
        | intros β0 τ0 Hb0; clear; fsetdec ]. }
    assert (Hrp' : ad_refine_pskl_f empty Θ empty
              (msubst_pskl ρs (ptyp_to_pskl Aσ))
              (bskl_to_pskl (ptyp_to_bskl_syn (msubst_ptyp ρs Bσ)))).
    { rewrite msubst_pskl_ptyp_to_pskl.
      replace (ptyp_to_pskl (msubst_ptyp ρs Aσ))
        with (uskl_to_pskl (ptyp_to_uskl_syn (msubst_ptyp ρs Aσ)))
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
        (mu_consis Θ ρs (ptyp_to_pskl Bσ) (ptyp_to_pskl Aσ) Θ0')
        (mu_unify Θ ((γ, τγ) :: ρs) α β
                  ((γ ~ abind_flex_mono_def τdef) ++ Θ0'))).
    { unfold mu_consis, mu_unify. apply mu_lt_intro. right. split.
      - unfold V_consis, V_unify.
        rewrite (Vpskl_ptyp_to_pskl Θ ρs Aσ).
        rewrite (Vpskl_ptyp_to_pskl Θ ρs Bσ).
        unfold Aσ, Bσ.
        rewrite (@Vvar_backedge Θ ρs γ τdef τγ α Hwfth Heqd).
        rewrite (@Vvar_backedge Θ ρs γ τdef τγ β Hwfth Heqd).
        unfold Vvar, Vptyp; cbn [msubst_ptyp]; reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH (add γ F) empty empty Θ0' (ptyp_to_pskl Bσ)
                   (ptyp_to_pskl Aσ) ρs Θ empty
                   (ptyp_to_bskl_syn (msubst_ptyp ρs Bσ))
                   eq_refl Hwf0 HwfPB HwfPA
                   ltac:(intros X HX; exfalso; clear - HX; fsetdec)
                   ltac:(repeat intro; fsetdec)
                   ltac:(repeat intro; fsetdec)
                   Hinc' Hwfth
                   ltac:(repeat intro; fsetdec)
                   Hpsi Hjoin' Hrs' Hrp')
      as [P1 [Θ1' [Hcons Hopt']]].
    exists ((γ ~ abind_flex_mono_def τdef) ++ Θ1'). split.
    { eapply a_unify__flex_assign;
        [ exact Hfα | exact Hfβ | exact Hcons ]. }
    intros ρ1 Hid Hinc1.
    inversion Hinc1 as [ | | Θp ρp Θq γp τd1 τ1 Hincp Hwf1p Hm1p Heq1p
                           [Heqγ1 Heqρ1] Heqt1 | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ1 Hid']; subst τ1.
    (* the sub-derivation's own soundness: id-witness + target wf *)
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ _ Hcons
                Hwf0 HwfPB HwfPA
                ltac:(intros X HX; exfalso; clear - HX; fsetdec)
                ltac:(repeat intro; fsetdec)
                ltac:(repeat intro; fsetdec))
      as [[[w [Hidw Hincw]] _] [Hwf1' _]].
    assert (Hw : ρp = w) by (eapply is_id_inc_unique; eauto).
    subst w.
    assert (Hγw : γ `notin` dom ρp)
      by (pose proof (a_inc_dom_sub Hincw) as Hs; clear - Hs Hnd; fsetdec).
    destruct (Hopt' ρp Hid' Hincw) as [ζ' [Hζ' [Hie' _]]].
    exists ((γ, τγ) :: ζ'). split.
    + apply a_inc__flex_def; [ exact Hζ' | exact Hwfτγ | exact Hmτγ | ].
      (* the definition's image transports across the equivalent increments *)
      eapply a_tyequiv__trans; [ exact Heqd | ].
      rewrite <- (msubst_compose_id_ptyp Hwf0 Hwf1' Hid' Hincw Hζ' Hwfτd).
      eapply a_inc_equiv_msubst_ptyp;
        [ exact Hwfτd | exact Hie' | exact Hwf0
        | eapply a_inc_msubst_lc; exact Hinc'
        | eapply msubst_lc_compose;
            [ eapply a_inc_msubst_lc; exact Hζ'
            | eapply is_id_msubst_values_lc; exact Hidw ] ].
    + assert (Heqc : msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: ρp)
                     = (γ, τγ) :: msubst_compose ζ' ρp).
      { change (msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: ρp))
          with ((γ, msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                :: msubst_compose ((γ, τγ) :: ζ') ρp).
        rewrite (msubst_compose_cons_l_id τγ ζ' Hid' Hγw).
        change (msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
          with (msubst_lookup ((γ, τγ) :: ζ') γ).
        rewrite msubst_lookup_cons_eq. reflexivity. }
      rewrite Heqc.
      apply a_inc_equiv__flex_def;
        [ exact Hie'
        | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτγ
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
  (exists X, P = pskl_var_f X) \/ (forall X, P <> pskl_var_f X).
Proof.
  destruct P;
    first [ left; eexists; reflexivity
          | right; intros ? Hcx; discriminate Hcx ].
Qed.

(** An identity metasubstitution's mid entry is the identity on its key. *)
Lemma is_id_msubst_mid : forall ρa β τ ρb,
  is_id_msubst (ρa ++ (β, τ) :: ρb) ->
  τ = ptyp_var_f β /\ is_id_msubst (ρa ++ ρb).
Proof.
  induction ρa as [ | [a t] ρa' IH ]; intros β τ ρb Hid; simpl in *.
  - apply is_id_msubst_inv in Hid as [Heq Hid']; auto.
  - inversion Hid as [ | e es He Hes ]; subst.
    destruct (IH _ _ _ Hes) as [Heq Hid']; subst.
    split; [ reflexivity | constructor; assumption ].
Qed.

(** Composition with an identity multiplicand only reads the left factor's
    lookups on the identity's keys. *)
Lemma msubst_compose_agree_id : forall ζ ζ' ρ1,
  is_id_msubst ρ1 ->
  (forall X, X `in` dom ρ1 -> msubst_lookup ζ X = msubst_lookup ζ' X) ->
  msubst_compose ζ ρ1 = msubst_compose ζ' ρ1.
Proof.
  intros ζ ζ' ρ1; induction ρ1 as [ | [a t] ρ1' IH ]; intros Hid Hag;
    [ reflexivity | ].
  apply is_id_msubst_inv in Hid as [Heq Hid']; subst.
  unfold msubst_compose in *; simpl.
  rewrite (Hag a) by (simpl; fsetdec).
  rewrite IH; [ reflexivity | exact Hid' | ].
  intros X HX. apply Hag. simpl. fsetdec.
Qed.

(** [msubst_compose_is_id_r] with a source-disjoint prefix on the left
    factor: the prefix is never consulted on the identity's keys. *)
Lemma msubst_compose_is_id_r_ext : forall Θ0 ρ1 Θ1 ρ Θ ζpre,
  a_wf_aenv Θ0 ->
  is_id_msubst ρ1 ->
  Θ0 ≤[ ρ1 ] Θ1 ->
  Θ0 ≤[ ρ ] Θ ->
  (forall X, X `in` dom ζpre -> X `notin` dom Θ0) ->
  msubst_compose (ζpre ++ ρ) ρ1 = ρ.
Proof.
  intros Θ0 ρ1 Θ1 ρ Θ ζpre Hwf Hid Hinc1 Hinc Hdisj.
  assert (Hag : forall X, X `in` dom ρ1 ->
            msubst_lookup (ζpre ++ ρ) X = msubst_lookup ρ X).
  { intros X HX.
    pose proof (a_inc_dom_sub Hinc1) as Hsub.
    apply msubst_lookup_app_notin.
    assert (HXΘ0 : X `in` dom Θ0) by (clear - HX Hsub; fsetdec).
    destruct (AtomSetProperties.In_dec X (dom ζpre)) as [Hin | Hni];
      [ exfalso; exact (Hdisj X Hin HXΘ0) | exact Hni ]. }
  rewrite (@msubst_compose_agree_id (ζpre ++ ρ) ρ ρ1 Hid Hag).
  eapply msubst_compose_is_id_r; eauto.
Qed.

(* ===================================================================== *)
(*  §2g  Assign-SolveM: the var-base mono bridge                          *)
(* ===================================================================== *)

Lemma join_var_tyequiv : forall Ψ Θ A C,
  Ψ ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (ptyp_to_pskl A)) ≈ (ptyp_to_bskl_syn C) ->
  a_wf_aenv Θ ->
  mono_ptyp A ->
  mono_ptyp C ->
  Θ ⊢ A ≡ᵗ C.
Proof.
  intros Ψ Θ A C Hc Hwf HmA HmC.
  rewrite ptyp_to_uskl_syn_eq in Hc.
  destruct (consis_mono_join Hc Hwf (A := A) eq_refl HmA)
    as [C' [HmC' [HeqQ Heqv]]].
  assert (HeqC : C' = C)
    by (apply ptyp_to_bskl_syn_inj; auto).
  subst C'. exact Heqv.
Qed.

(* ===================================================================== *)
(*  §2h  Assign-SolveM: OCCURS — the α-occurrence size walk                               *)
(* ===================================================================== *)

Lemma occurs_join_size_aux : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  a_wf_aenv Θ ->
  forall θm,
  (forall X, mono_ptyp (msubst_lookup θm X)) ->
  forall α P C Θw Δw,
    (forall X, P <> pskl_var_f X) ->
    S = pskl_to_uskl (msubst_pskl θm P) ->
    Q = ptyp_to_bskl_syn C ->
    mono_ptyp C ->
    Θw ⨟ Δw ⊢ₚₛᵃ P ->
    α `in` ftvar_in_pskl P ->
    size_ptyp (⇓ᵗ[Θ] (msubst_lookup θm α)) <= size_ptyp (⇓ᵗ[Θ] C) /\
    (P = pskl_tophole (pskl_var_f α) \/
     size_ptyp (⇓ᵗ[Θ] (msubst_lookup θm α)) < size_ptyp (⇓ᵗ[Θ] C)).
Proof.
  intros Ψ Θ S Q Hc Hwf θm Hmlk.
  induction Hc; intros α0 P0 C0 Θw Δw Hnv HeqS HeqQ HmC0 HwfP0 Hocc.
  - (* unit *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    simpl in Hocc. exfalso. clear - Hocc. fsetdec.
  - (* var *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* arrow *)
    destruct P0 as [ | | X | P1 P2 | | | ]; simpl in HeqS; try discriminate;
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
    simpl in Hocc. apply AtomSetImpl.union_1 in Hocc.
    destruct Hocc as [Hocc | Hocc].
    + (* α ∈ ftv P1 *)
      assert (Hle : size_ptyp (⇓ᵗ[Θ] (msubst_lookup θm α0))
                      <= size_ptyp (⇓ᵗ[Θ] C1)).
      { destruct (pskl_var_dec P1) as [[X1 HeqP1] | Hnv1].
        - subst P1. simpl in Hocc.
          assert (HeqX : X1 = α0) by (clear - Hocc; fsetdec). subst X1.
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
      assert (Hle : size_ptyp (⇓ᵗ[Θ] (msubst_lookup θm α0))
                      <= size_ptyp (⇓ᵗ[Θ] C2)).
      { destruct (pskl_var_dec P2) as [[X2 HeqP2] | Hnv2].
        - subst P2. simpl in Hocc.
          assert (HeqX : X2 = α0) by (clear - Hocc; fsetdec). subst X2.
          simpl in Hc2.
          rewrite (a_tyequiv_downarrow Hwf
                     (join_var_tyequiv Hc2 Hwf (Hmlk α0) HmC2)).
          lia.
        - destruct (IHHc2 Hwf α0 P2 C2 Θw Δw Hnv2 eq_refl eq_refl
                      HmC2 HwfP2 Hocc) as [Hle2 _].
          exact Hle2. }
      split; [ | right ];
        simpl; pose proof (size_ptyp_min (⇓ᵗ[Θ] C1)); lia.
  - (* forall_inh_tagged : S = uskl_all_etag, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_inh_untagged : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* forall_syn_tagged : S = uskl_all_etag, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_syn : Q = bskl_all_syn, mono C refutes *)
    destruct C0; simpl in HeqQ; try discriminate. inversion HmC0.
  - (* ghostg : S = uskl_holeg, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* topholeg : S = uskl_topholeg, unreachable *)
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
  - (* tophole_drop : P = ⊤◇P', same C *)
    destruct P0 as [ | | | | | | P' ]; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    inversion HeqS; subst R.
    inversion HwfP0; subst.
    match goal with H : guarded_pskl P' |- _ => rename H into Hgu end.
    match goal with H : _ ⨟ empty ⊢ₚₛᵃ P' |- _ => rename H into HwfP' end.
    simpl in Hocc.
    destruct (pskl_var_dec P') as [[X' HeqP'] | Hnv'].
    + (* P = ⊤◇X' : the drop-to-var base *)
      subst P'. simpl in Hocc.
      assert (HeqX : X' = α0) by (clear - Hocc; fsetdec). subst X'.
      simpl in Hc.
      rewrite (a_tyequiv_downarrow Hwf
                 (join_var_tyequiv Hc Hwf (Hmlk α0) HmC0)).
      split; [ lia | left; reflexivity ].
    + (* body not a var : recurse; P' = ⊤◇α̂ is killed by guardedness *)
      destruct (IHHc Hwf α0 P' C0 Θw empty Hnv' eq_refl eq_refl
                  HmC0 HwfP' Hocc) as [Hle Hdisj].
      split; [ exact Hle | right ].
      destruct Hdisj as [HeqP' | Hlt]; [ | exact Hlt ].
      subst P'. inversion Hgu.
  - (* flex_l : S = uskl_var, P must be a var — excluded *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* flex_r : unfold the RHS definition, same P *)
    destruct C0 as [ | | X0 | | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst X0.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHc Hwf α0 P0 τ Θw Δw Hnv HeqS eq_refl Hmτ HwfP0 Hocc)
      as [Hle Hdisj].
    assert (Heqd : ⇓ᵗ[Θ] (ptyp_var_f α) = ⇓ᵗ[Θ] τ)
      by (apply a_tyequiv_downarrow;
          [ exact Hwf | apply a_tyequiv__flex_def; exact H ]).
    rewrite Heqd. split; [ exact Hle | exact Hdisj ].
Qed.

(** The wrapper: full occurs-size fact, var case included. *)
Lemma occurs_join_size : forall Ψ Θ θm α P C Θw Δw,
  Ψ ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θm P)) ≈ (ptyp_to_bskl_syn C) ->
  a_wf_aenv Θ ->
  (forall X, mono_ptyp (msubst_lookup θm X)) ->
  mono_ptyp C ->
  Θw ⨟ Δw ⊢ₚₛᵃ P ->
  α `in` ftvar_in_pskl P ->
  size_ptyp (⇓ᵗ[Θ] (msubst_lookup θm α)) <= size_ptyp (⇓ᵗ[Θ] C) /\
  (P = pskl_var_f α \/ P = pskl_tophole (pskl_var_f α) \/
   size_ptyp (⇓ᵗ[Θ] (msubst_lookup θm α)) < size_ptyp (⇓ᵗ[Θ] C)).
Proof.
  intros Ψ Θ θm α P C Θw Δw Hc Hwf Hmlk HmC HwfP Hocc.
  destruct (pskl_var_dec P) as [[X HeqP] | Hnv].
  - (* P = var X *)
    subst P. simpl in Hocc.
    assert (HeqX : X = α) by (clear - Hocc; fsetdec). subst X.
    simpl in Hc.
    rewrite (a_tyequiv_downarrow Hwf
               (join_var_tyequiv Hc Hwf (Hmlk α) HmC)).
    split; [ lia | left; reflexivity ].
  - destruct (occurs_join_size_aux Hc Hwf θm Hmlk Hnv eq_refl eq_refl
                HmC HwfP Hocc) as [Hle Hdisj].
    split; [ exact Hle | destruct Hdisj; auto ].
Qed.

(* ===================================================================== *)
(*  §2i  Assign-SolveM: GUESS — existence + the ζ-images from the join                   *)
(* ===================================================================== *)

(** The trivial tuple at a variable: guess keeps the variable, no fresh
    names, and the equation is the base bridge. *)
Lemma guess_witness_var_tuple : forall Θ θm X C L,
  Θ ⊢ (msubst_lookup θm X) ≡ᵗ C ->
  exists βs τg ζβ,
    (forall Θg, a_guess_mono Θg (pskl_var_f X) βs τg) /\
    mono_ptyp τg /\
    uniq βs /\
    (forall γ0, γ0 `in` dom βs -> γ0 `notin` L) /\
    dom ζβ [=] dom βs /\
    (forall E ρE, E ≤[ ρE ] Θ -> (βs ++ E) ≤[ ζβ ++ ρE ] Θ) /\
    Θ ⊢ (msubst_ptyp (ζβ ++ θm) τg) ≡ᵗ C.
Proof.
  intros Θ θm X C L Heqv.
  exists nil, (ptyp_var_f X), (@nil (atom * ptyp)).
  split; [ intros Θg; apply a_guess_mono__var | ].
  split; [ apply mono_ptyp__var | ].
  split; [ constructor | ].
  split; [ intros γ0 Hγ0; simpl in Hγ0; exfalso; clear - Hγ0; fsetdec | ].
  split; [ simpl; reflexivity | ].
  split; [ intros E ρE HE; simpl; exact HE | ].
  simpl. exact Heqv.
Qed.

Lemma guess_join_witness_aux : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  a_wf_aenv Θ ->
  forall θm,
  (forall X, mono_ptyp (msubst_lookup θm X)) ->
  forall P C,
    (forall X, P <> pskl_var_f X) ->
    S = pskl_to_uskl (msubst_pskl θm P) ->
    Q = ptyp_to_bskl_syn C ->
    mono_ptyp C ->
    a_wf_ptyp Θ C ->
    forall L, exists βs τg ζβ,
      (forall Θg, a_guess_mono Θg P βs τg) /\
      mono_ptyp τg /\
      uniq βs /\
      (forall γ0, γ0 `in` dom βs -> γ0 `notin` L) /\
      dom ζβ [=] dom βs /\
      (forall E ρE, E ≤[ ρE ] Θ -> (βs ++ E) ≤[ ζβ ++ ρE ] Θ) /\
      Θ ⊢ (msubst_ptyp (ζβ ++ θm) τg) ≡ᵗ C.
Proof.
  intros Ψ Θ S Q Hc Hwf θm Hmlk.
  induction Hc; intros P0 C0 Hnv HeqS HeqQ HmC0 HwfC0 Lav.
  - (* unit *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    destruct C0; simpl in HeqQ; try discriminate.
    exists nil, ptyp_unit, (@nil (atom * ptyp)).
    split; [ intros Θg; apply a_guess_mono__unit | ].
    split; [ apply mono_ptyp__unit | ].
    split; [ constructor | ].
    split; [ intros γ0 Hγ0; simpl in Hγ0; exfalso; clear - Hγ0; fsetdec | ].
    split; [ simpl; reflexivity | ].
    split; [ intros E ρE HE; simpl; exact HE | ].
    simpl. apply a_tyequiv__refl. apply lc_ptyp_unit.
  - (* var : P must be a var — excluded *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* arrow *)
    destruct P0 as [ | | X | P1 P2 | | | ]; simpl in HeqS; try discriminate;
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
        (forall Θg, a_guess_mono Θg P1 βs1 τ1) /\
        mono_ptyp τ1 /\ uniq βs1 /\
        (forall γ0, γ0 `in` dom βs1 -> γ0 `notin` L1) /\
        dom ζ1 [=] dom βs1 /\
        (forall E ρE, E ≤[ ρE ] Θ -> (βs1 ++ E) ≤[ ζ1 ++ ρE ] Θ) /\
        Θ ⊢ (msubst_ptyp (ζ1 ++ θm) τ1) ≡ᵗ C1).
    { destruct (pskl_var_dec P1) as [[X1 HeqP1] | Hnv1].
      - subst P1. simpl in Hc1.
        apply guess_witness_var_tuple.
        apply (join_var_tyequiv Hc1 Hwf (Hmlk X1) HmC1).
      - apply (IHHc1 Hwf P1 C1 Hnv1 eq_refl eq_refl HmC1 HwfC1 L1). }
    destruct Hcomp1 as [βs1 [τ1 [ζ1 [Hg1 [Hm1 [Hu1 [Hf1 [Hd1 [Ht1 He1]]]]]]]]].
    set (L2 := L1 `union` dom βs1).
    assert (Hcomp2 : exists βs2 τ2 ζ2,
        (forall Θg, a_guess_mono Θg P2 βs2 τ2) /\
        mono_ptyp τ2 /\ uniq βs2 /\
        (forall γ0, γ0 `in` dom βs2 -> γ0 `notin` L2) /\
        dom ζ2 [=] dom βs2 /\
        (forall E ρE, E ≤[ ρE ] Θ -> (βs2 ++ E) ≤[ ζ2 ++ ρE ] Θ) /\
        Θ ⊢ (msubst_ptyp (ζ2 ++ θm) τ2) ≡ᵗ C2).
    { destruct (pskl_var_dec P2) as [[X2 HeqP2] | Hnv2].
      - subst P2. simpl in Hc2.
        apply guess_witness_var_tuple.
        apply (join_var_tyequiv Hc2 Hwf (Hmlk X2) HmC2).
      - apply (IHHc2 Hwf P2 C2 Hnv2 eq_refl eq_refl HmC2 HwfC2 L2). }
    destruct Hcomp2 as [βs2 [τ2 [ζ2 [Hg2 [Hm2 [Hu2 [Hf2 [Hd2 [Ht2 He2]]]]]]]]].
    exists (βs1 ++ βs2), (ptyp_arrow τ1 τ2), (ζ1 ++ ζ2).
    assert (Hdisj12 : forall γ0, γ0 `in` dom βs2 -> γ0 `notin` dom βs1).
    { intros γ0 Hγ0. specialize (Hf2 γ0 Hγ0).
      clear - Hf2. unfold L2 in Hf2. fsetdec. }
    (* the two msubst-agree transports *)
    pose proof (a_guess_mono_ftv (Hg1 Θ)) as Hftv1.
    pose proof (a_guess_mono_ftv (Hg2 Θ)) as Hftv2.
    assert (Hag1 : msubst_ptyp ((ζ1 ++ ζ2) ++ θm) τ1
                 = msubst_ptyp (ζ1 ++ θm) τ1).
    { apply msubst_ptyp_agree. intros X0 HX0.
      assert (HX0' : X0 `in` ftvar_in_pskl P1 `union` dom βs1)
        by (clear - Hftv1 HX0; fsetdec).
      rewrite app_assoc.
      destruct (AtomSetProperties.In_dec X0 (dom ζ1)) as [Hin | Hni].
      - rewrite (msubst_lookup_app_in ζ1 (ζ2 ++ θm) Hin).
        rewrite (msubst_lookup_app_in ζ1 θm Hin). reflexivity.
      - rewrite (msubst_lookup_app_notin _ _ Hni).
        rewrite (msubst_lookup_app_notin _ _ Hni).
        assert (HX0P1 : X0 `in` ftvar_in_pskl P1)
          by (rewrite Hd1 in Hni; clear - HX0' Hni; fsetdec).
        assert (Hniζ2 : X0 `notin` dom ζ2).
        { rewrite Hd2. intros Hin2.
          specialize (Hf2 X0 Hin2). clear - Hf2 HX0P1.
          unfold L2, L1 in Hf2. simpl in Hf2. fsetdec. }
        rewrite (msubst_lookup_app_notin _ _ Hniζ2). reflexivity. }
    assert (Hag2 : msubst_ptyp ((ζ1 ++ ζ2) ++ θm) τ2
                 = msubst_ptyp (ζ2 ++ θm) τ2).
    { apply msubst_ptyp_agree. intros X0 HX0.
      assert (HX0' : X0 `in` ftvar_in_pskl P2 `union` dom βs2)
        by (clear - Hftv2 HX0; fsetdec).
      rewrite app_assoc.
      assert (Hniζ1 : X0 `notin` dom ζ1).
      { rewrite Hd1.
        destruct (AtomSetProperties.In_dec X0 (dom βs2)) as [Hin2 | Hni2].
        - exact (Hdisj12 X0 Hin2).
        - assert (HX0P2 : X0 `in` ftvar_in_pskl P2)
            by (clear - HX0' Hni2; fsetdec).
          intros Hin1. specialize (Hf1 X0 Hin1).
          clear - Hf1 HX0P2. unfold L1 in Hf1. simpl in Hf1. fsetdec. }
      rewrite (msubst_lookup_app_notin _ _ Hniζ1). reflexivity. }
    split; [ intros Θg; apply a_guess_mono__arrow;
             [ apply Hg1 | apply Hg2 ] | ].
    split; [ apply mono_ptyp__arrow; assumption | ].
    split.
    { apply uniq_app_4; auto.
      unfold disjoint. intros x Hx.
      assert (Hx1 : x `in` dom βs1) by (clear - Hx; fsetdec).
      assert (Hx2 : x `in` dom βs2) by (clear - Hx; fsetdec).
      exfalso. exact (Hdisj12 x Hx2 Hx1). }
    split.
    { intros γ0 Hγ0. rewrite dom_app in Hγ0.
      apply AtomSetImpl.union_1 in Hγ0. destruct Hγ0 as [Hγ0 | Hγ0].
      - specialize (Hf1 γ0 Hγ0). clear - Hf1. unfold L1 in Hf1. fsetdec.
      - specialize (Hf2 γ0 Hγ0). clear - Hf2. unfold L2, L1 in Hf2. fsetdec. }
    split.
    { repeat rewrite dom_app. rewrite Hd1. rewrite Hd2. reflexivity. }
    split.
    { intros E ρE HE.
      rewrite app_assoc. rewrite app_assoc.
      apply Ht1. apply Ht2. exact HE. }
    simpl. apply a_tyequiv__arrow;
      [ rewrite Hag1; exact He1 | rewrite Hag2; exact He2 ].
  - (* forall_inh_tagged : S = uskl_all_etag, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_inh_untagged : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* forall_syn_tagged *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_syn : Q = bskl_all_syn, mono C refutes *)
    destruct C0; simpl in HeqQ; try discriminate. inversion HmC0.
  - (* ghostg *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* topholeg *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* hole : the crux — a fresh β̂ whose ζ-image is C *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    destruct (atom_fresh Lav) as [β Hβ].
    exists (β ~ abind_flex_mono), (ptyp_var_f β), ((β, C0) :: nil).
    split; [ intros Θg; apply a_guess_mono__hole | ].
    split; [ apply mono_ptyp__var | ].
    split; [ solve_uniq | ].
    split.
    { intros γ0 Hγ0. simpl in Hγ0.
      assert (Heqγ : γ0 = β) by (clear - Hγ0; fsetdec).
      subst γ0. exact Hβ. }
    split; [ simpl; fsetdec | ].
    split.
    { intros E ρE HE. simpl.
      apply a_inc__flex; [ exact HE | exact HwfC0 | exact HmC0 ]. }
    simpl. destruct (β == β) as [_ | Hne]; [ | exfalso; auto ].
    apply a_tyequiv__refl. apply mono_ptyp_lc. exact HmC0.
  - (* tophole : Q = bskl_tophole, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* tophole_inh : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* tophole_drop : P = ⊤◇P', recurse on the body *)
    destruct P0 as [ | | | | | | P' ]; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    inversion HeqS; subst R.
    assert (Hbody : exists βs τg ζβ,
        (forall Θg, a_guess_mono Θg P' βs τg) /\
        mono_ptyp τg /\ uniq βs /\
        (forall γ0, γ0 `in` dom βs -> γ0 `notin` Lav) /\
        dom ζβ [=] dom βs /\
        (forall E ρE, E ≤[ ρE ] Θ -> (βs ++ E) ≤[ ζβ ++ ρE ] Θ) /\
        Θ ⊢ (msubst_ptyp (ζβ ++ θm) τg) ≡ᵗ C0).
    { destruct (pskl_var_dec P') as [[X' HeqP'] | Hnv'].
      - subst P'. simpl in Hc. rewrite HeqQ in Hc.
        apply guess_witness_var_tuple.
        apply (join_var_tyequiv Hc Hwf (Hmlk X') HmC0).
      - apply (IHHc Hwf P' C0 Hnv' eq_refl HeqQ HmC0 HwfC0 Lav). }
    destruct Hbody as [βs [τg [ζβ [Hg [Hm [Hu [Hf [Hd [Ht He]]]]]]]]].
    exists βs, τg, ζβ.
    split; [ intros Θg; apply a_guess_mono__tophole; apply Hg | ].
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
    destruct C0 as [ | | X0 | | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst X0.
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
Lemma guess_join_witness : forall Ψ Θ θm P C,
  Ψ ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θm P)) ≈ (ptyp_to_bskl_syn C) ->
  a_wf_aenv Θ ->
  (forall X, mono_ptyp (msubst_lookup θm X)) ->
  mono_ptyp C ->
  a_wf_ptyp Θ C ->
  forall L, exists βs τg ζβ,
    (forall Θg, a_guess_mono Θg P βs τg) /\
    mono_ptyp τg /\
    uniq βs /\
    (forall γ0, γ0 `in` dom βs -> γ0 `notin` L) /\
    dom ζβ [=] dom βs /\
    (forall E ρE, E ≤[ ρE ] Θ -> (βs ++ E) ≤[ ζβ ++ ρE ] Θ) /\
    Θ ⊢ (msubst_ptyp (ζβ ++ θm) τg) ≡ᵗ C.
Proof.
  intros Ψ Θ θm P C Hc Hwf Hmlk HmC HwfC L.
  destruct (pskl_var_dec P) as [[X HeqP] | Hnv].
  - subst P. simpl in Hc.
    apply guess_witness_var_tuple.
    apply (join_var_tyequiv Hc Hwf (Hmlk X) HmC).
  - eapply (guess_join_witness_aux Hc Hwf θm Hmlk Hnv eq_refl eq_refl
              HmC HwfC).
Qed.

(* ===================================================================== *)
(*  §2j  The Assign-SolveM completeness case, assembled                   *)
(* ===================================================================== *)

Lemma assign_solve_m_complete : forall F Θ0' Ξ α P ρ Θ,
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ->
  (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ⨟ empty ⊢ₚₛᵃ P ->
  a_non_flex (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') P ->
  P <> pskl_tophole (pskl_var_f α) ->
  (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ≤[ ρ ] Θ ->
  a_wf_aenv Θ ->
  empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P))
             ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α))) ->
  exists Θ1,
    ((α ~ abind_flex_mono) ++ Θ0') ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 /\
    (forall ρ1, is_id_msubst ρ1 ->
       (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ≤[ ρ1 ] Θ1 ->
       exists ζ, Θ1 ≤[ ζ ] Θ /\
         a_inc_equiv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ρ
                     (msubst_compose ζ ρ1) Θ).
Proof.
  intros F Θ0' Ξ α P ρ Θ Hdecl Hwf HwfP Hnf HneP Hinc Hwfth Hjoin.
  set (τα := msubst_lookup ρ α) in *.
  assert (Huq : uniq (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Hbα : binds α abind_flex_mono (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
    by (apply binds_app_3; left; reflexivity).
  assert (Hbtα : a_binds_tvar α (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
    by (right; left; exact Hbα).
  assert (Hmτα : mono_ptyp τα) by (eapply a_inc_lookup_mono; exact Hinc).
  assert (Hwτα : a_wf_ptyp Θ τα)
    by (eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact Hbtα ]).
  assert (Hmlk : forall X, mono_ptyp (msubst_lookup ρ X))
    by (intros X; eapply a_inc_lookup_mono; exact Hinc).
  (* ---- occurs check ---- *)
  assert (Hocc : α `notin` ftvar_in_pskl P).
  { destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P))
      as [Hin | Hni]; [ exfalso | exact Hni ].
    destruct (occurs_join_size ρ Hjoin Hwfth Hmlk Hmτα HwfP Hin)
      as [Hle Hdisj].
    destruct Hdisj as [HeqP | [HeqP | Hlt]].
    - subst P. destruct Hnf as [_ Hnfl].
      apply Hnfl. apply a_flex__var. exact Hbα.
    - exact (HneP HeqP).
    - exact (Nat.lt_irrefl _ Hlt). }
  (* ---- the guess witness ---- *)
  set (L := F `union` add α (dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
              `union` ftvar_in_pskl P `union` dom Θ).
  destruct (guess_join_witness ρ P Hjoin Hwfth Hmlk Hmτα Hwτα L)
    as [βs [τg [ζβ [Hg [Hmτg [Huβ [Hfβ [Hdζ [Htr Heqn]]]]]]]]].
  (* ---- the algorithmic step ---- *)
  exists ((α ~ abind_flex_mono_def τg) ++ βs ++ Ξ ++ Θ0').
  split.
  { apply a_assign__solve_m.
    - exact Hocc.
    - apply Hg.
    - exact Hmτg.
    - exact Huβ.
    - intros γ0 Hγ0. specialize (Hfβ γ0 Hγ0).
      clear - Hfβ. unfold L in Hfβ. simpl_env in *. fsetdec. }
  (* ---- optimality ---- *)
  intros ρ1 Hid Hinc1.
  (* strip the competing solution at the α entry *)
  destruct (@a_inc_mid_strip_flex Ξ α Θ0' ρ Θ Hdecl Hinc)
    as [ρa [τα' [ρ0 [Heqρ [Hdρa [Hinc0 Hincs]]]]]].
  assert (Hαρa : α `notin` dom ρa).
  { rewrite Hdρa. clear - Huq. simpl_env in Huq. solve_uniq. }
  assert (Heqτα : τα = τα').
  { unfold τα. rewrite Heqρ.
    rewrite (msubst_lookup_app_notin _ _ Hαρa). simpl.
    destruct (α == α) as [_ | Hne]; [ reflexivity | exfalso; auto ]. }
  subst τα'.
  (* the factoring ζ *)
  exists ((α, τα) :: ζβ ++ ρa ++ ρ0).
  assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
    by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact Hwf ]).
  assert (Hαftvτg : α `notin` ftvar_in_ptyp τg).
  { pose proof (a_guess_mono_ftv (Hg Θ)) as Hftv.
    intros Hinτ. apply Hftv in Hinτ.
    apply AtomSetImpl.union_1 in Hinτ. destruct Hinτ as [HinP | Hinβ].
    - clear - HinP Hocc. fsetdec.
    - specialize (Hfβ α Hinβ). clear - Hfβ. unfold L in Hfβ. fsetdec. }
  (* the deposited definition is ζ-consistent *)
  assert (Heqdef : Θ ⊢ τα ≡ᵗ (msubst_ptyp (ζβ ++ ρa ++ ρ0) τg)).
  { apply a_tyequiv__sym.
    assert (Hagd : msubst_ptyp (ζβ ++ ρa ++ ρ0) τg
                 = msubst_ptyp (ζβ ++ ρ) τg).
    { apply msubst_ptyp_agree. intros X0 HX0.
      rewrite Heqρ.
      rewrite <- app_assoc. rewrite <- (app_assoc _ ζβ ρa ((α, τα) :: ρ0)).
      assert (HneX : X0 <> α)
        by (intros ->; exact (Hαftvτg HX0)).
      rewrite (msubst_lookup_mid_drop _ _ _ HneX). reflexivity. }
    rewrite Hagd. exact Heqn. }
  split.
  { (* Θ1 ≤[ζ] Θ *)
    simpl_env.
    apply a_inc__flex_def.
    - simpl_env. apply Htr. exact Hincs.
    - exact Hwτα.
    - exact Hmτα.
    - simpl_env. exact Heqdef. }
  (* ---- the metasubstitution equivalence ---- *)
  destruct (@a_inc_mid_strip_flex Ξ α Θ0' ρ1
              ((α ~ abind_flex_mono_def τg) ++ βs ++ Ξ ++ Θ0') Hdecl Hinc1)
    as [ρ1a [τid [ρ1b [Heqρ1 [Hdρ1a [Hinc10 Hinc1s]]]]]].
  assert (Hidm : τid = ptyp_var_f α /\ is_id_msubst (ρ1a ++ ρ1b))
    by (rewrite Heqρ1 in Hid; apply is_id_msubst_mid; exact Hid).
  destruct Hidm as [Heqτid Hid'].
  subst τid.
  rewrite Heqρ1. rewrite Heqρ.
  rewrite msubst_compose_app.
  replace (msubst_compose ((α, τα) :: ζβ ++ ρa ++ ρ0)
             ((α, ptyp_var_f α) :: ρ1b))
    with ((α, τα) :: msubst_compose ((α, τα) :: ζβ ++ ρa ++ ρ0) ρ1b)
    by (unfold msubst_compose; simpl;
        destruct (α == α); [ reflexivity | exfalso; auto ]).
  apply a_inc_equiv_mid_insert_flex.
  - exact Hdecl.
  - clear - Huq. simpl_env in *. solve_uniq.
  - exact Hdρa.
  - rewrite dom_msubst_compose. exact Hdρ1a.
  - apply a_tyequiv__refl. apply mono_ptyp_lc. exact Hmτα.
  - (* collapse ζ ∘ (ρ1a ++ ρ1b) to ρa ++ ρ0, then reflexivity *)
    rewrite <- msubst_compose_app.
    change ((α, τα) :: ζβ ++ ρa ++ ρ0)
      with (((α, τα) :: ζβ) ++ ρa ++ ρ0).
    rewrite (msubst_compose_is_id_r_ext ((α, τα) :: ζβ) Hwf' Hid' Hinc1s Hincs).
    + apply a_inc_equiv_refl. exact Hincs.
    + intros X0 HX0. simpl in HX0.
      destruct (AtomSetProperties.In_dec X0 (dom ζβ)) as [Hinζ | Hniζ].
      * rewrite Hdζ in Hinζ. specialize (Hfβ X0 Hinζ).
        clear - Hfβ. unfold L in Hfβ. simpl_env in *. fsetdec.
      * assert (HeqX : X0 = α) by (clear - HX0 Hniζ; fsetdec).
        subst X0. clear - Huq. simpl_env in Huq. solve_uniq.
Qed.

Lemma assign_complete_step : forall m,
  (forall m', mu_lt m' m -> complete_at m') ->
  assign_complete_at m.
Proof.
  intros m IH. unfold assign_complete_at.
  intros F Θ0 Ξ α P ρ Θ Hm Hdecl Hwf Hfα HwfP Hnf Hdomξ Hinc Hwfth Hjoin.
  subst m.
  destruct Θ0 as [ | [γ b] Θ0' ].
  { exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb. }
  destruct b as [ | A | Q | | τdef ].
  - (* head [γ ~ tvar] RIGID. *)
    destruct (AtomSetProperties.In_dec γ (ftvar_in_pskl P)) as [Hγin | Hγni].
    + (* γ ∈ ftv(P) : NO RULE fires — the STUCK-CHECK (design doc §9.2,
         [paper-gap]: the paper never proves the walk cannot reach this
         head) refutes the solution.  [a_inc] peels γ before reaching α̂
         ([a_inc_tvar_inv]), so θα̂ is wf BELOW γ; γ survives the solution
         into θP ([rigid_survives_solution]) while the join confines the
         subject's rigid ftv to θα̂'s scope
         ([ad_pat_consis_rigid_ftv_rev_scoped]) — contradiction. *)
      exfalso.
      (* decompose the competing increment at the rigid head *)
      destruct (@a_inc_strip_decls_prefix Ξ ((γ, abind_tvar) :: Θ0') ρ Θ
                  Hdecl Hinc)
        as [ρa [ρb [Heqρ [Hdρa Hincb]]]].
      destruct (a_inc_tvar_inv Hincb)
        as [Ξv [Θt [HeqΘ [HsufΞv Hincb']]]].
      assert (Huq : uniq (Ξ ++ (γ, abind_tvar) :: Θ0'))
        by (apply a_wf_aenv_uniq; exact Hwf).
      assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
      assert (Hbγ : binds γ abind_tvar (Ξ ++ (γ, abind_tvar) :: Θ0')).
      { apply binds_app_3. left. reflexivity. }
      assert (HbγΘ : binds γ abind_tvar Θ)
        by (eapply a_inc_binds_tvar; [ exact Hinc | exact Hbγ ]).
      assert (HγΘt : γ `notin` dom Θt).
      { rewrite HeqΘ in HuqΘ. clear - HuqΘ.
        simpl_env in HuqΘ. solve_uniq. }
      (* θα̂ is well-formed in the truncated target Θt, below γ *)
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
      assert (Hαρa : α `notin` dom ρa).
      { rewrite Hdρa. clear - Huq HαΘ0'.
        simpl_env in Huq. solve_uniq. }
      assert (Hwf2 : a_wf_aenv ((Ξ ++ (γ ~ abind_tvar)) ++ Θ0'))
        by (simpl_env; exact Hwf).
      assert (Hwf0' : a_wf_aenv Θ0')
        by (eapply a_wf_aenv_app_r; exact Hwf2).
      assert (Hwfα : a_wf_ptyp Θt (msubst_lookup ρ α)).
      { rewrite Heqρ. rewrite (msubst_lookup_app_notin ρa ρb Hαρa).
        eapply a_inc_lookup_wf;
          [ exact Hincb' | exact Hwf0' | exact Hbtα0 ]. }
      assert (Hftvα : ftvar_in_ptyp (msubst_lookup ρ α) [<=] dom Θt)
        by (apply a_wf_ptyp_ftv_dom; exact Hwfα).
      (* definitions visible in dom Θt are Θt's own, scoped to Θt *)
      assert (HwfΘt : a_wf_aenv Θt).
      { rewrite HeqΘ in Hwfth.
        assert (Hwtmp : a_wf_aenv ((Ξv ++ (γ ~ abind_tvar)) ++ Θt))
          by (simpl_env; simpl_env in Hwfth; exact Hwfth).
        eapply a_wf_aenv_app_r; exact Hwtmp. }
      assert (Hdefs : forall δ τ, binds δ (abind_flex_mono_def τ) Θ ->
                δ `in` dom Θt -> ftvar_in_ptyp τ [<=] dom Θt).
      { intros δ τ Hb HδD.
        assert (Hbt : binds δ (abind_flex_mono_def τ) Θt).
        { rewrite HeqΘ in Hb.
          assert (Hb2 : binds δ (abind_flex_mono_def τ)
                    ((Ξv ++ (γ ~ abind_tvar)) ++ Θt))
            by (simpl_env; simpl_env in Hb; exact Hb).
          apply binds_app_iff in Hb2.
          destruct Hb2 as [Hb2 | Hb2]; [ exfalso | exact Hb2 ].
          apply binds_In in Hb2.
          rewrite HeqΘ in HuqΘ.
          assert (Hu2 : uniq ((Ξv ++ (γ ~ abind_tvar)) ++ Θt))
            by (simpl_env; simpl_env in HuqΘ; exact HuqΘ).
          apply uniq_app_iff in Hu2. destruct Hu2 as [_ [_ Hdisj]].
          clear - Hdisj Hb2 HδD. unfold disjoint in Hdisj. fsetdec. }
        apply a_wf_ptyp_ftv_dom.
        eapply a_wf_aenv_binds_def_wf_local; [ exact HwfΘt | exact Hbt ]. }
      (* γ survives the solution into θP … *)
      assert (HγθP : γ `in` ftvar_in_pskl (msubst_pskl ρ P))
        by (eapply rigid_survives_solution;
            [ exact Hinc | exact Hwf | exact Hbγ | exact Hγin ]).
      (* … but the join confines the subject's rigid ftv to dom Θt *)
      assert (HγnS : γ `notin`
                ftvar_in_uskl (pskl_to_uskl (msubst_pskl ρ P))).
      { eapply ad_pat_consis_rigid_ftv_rev_scoped with (D := dom Θt);
          [ exact Hwfth | exact HbγΘ | exact HγΘt | exact Hdefs
          | exact Hjoin | ].
        pose proof (ftvar_in_bskl_syn
                      (ptyp_to_pskl (msubst_lookup ρ α))) as Hf1.
        pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup ρ α)) as Hf2.
        clear - Hf1 Hf2 Hftvα. fsetdec. }
      pose proof (ftvar_in_uskl_pskl (msubst_pskl ρ P)) as Hf3.
      clear - HγnS HγθP Hf3. fsetdec.
    + (* Assign-SkipRigid proper (γ ∉ ftv P): the same ⇓-truncation as
           SkipTmVar, with the rigid middle re-attached verbatim (no
           semantic-middle obligation). *)
      assert (Huqf : uniq (Ξ ++ (γ ~ abind_tvar) ++ Θ0'))
        by (apply a_wf_aenv_uniq; exact Hwf).
      assert (HwfM : a_wf_aenv (Ξ ++ (γ ~ abind_tvar) ++ Θ0'))
        by (exact Hwf).
      assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
        by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
      assert (Huq' : uniq (Ξ ++ Θ0')) by (apply a_wf_aenv_uniq; exact Hwf').
      assert (Hwf0 : a_wf_aenv Θ0') by (eapply a_wf_aenv_app_r; exact Hwf').
      assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
      pose proof Hγni as Hγfr.
      assert (HwfP' : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
        by (eapply ad_wf_pskl_strip_mid; [ exact HwfP | exact Hγfr ]).
      assert (Hfα0 : a_flex_tvar Θ0' α).
      { destruct Hfα as [Hb | [τ0 Hb]];
          [ destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
            [ discriminate | left; exact Hb' ]
          | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
            [ discriminate | right; exists τ0; exact Hb' ] ]. }
      assert (Hbw : forall (δ : atom) (bb : abind),
                binds δ bb (Ξ ++ Θ0') ->
                binds δ bb (Ξ ++ (γ ~ abind_tvar) ++ Θ0')).
      { intros δ bb Hb. unfold binds in *.
        apply in_app_or in Hb. apply in_or_app.
        destruct Hb as [Hb | Hb];
          [ left; exact Hb | right; simpl; right; exact Hb ]. }
      assert (Hnf' : a_non_flex (Ξ ++ Θ0') P).
      { destruct Hnf as [Hlc Hnfl]. split; [ exact Hlc | ].
        intro Hfl. apply Hnfl.
        inversion Hfl as [Θf δ Hb | Θf δ τ0 Hb]; subst;
          [ apply a_flex__var; apply Hbw; exact Hb
          | eapply a_flex__var_def; apply Hbw; exact Hb ]. }
      (* competing: strip Ξ, invert the γ-var middle *)
      destruct (@a_inc_strip_decls_prefix Ξ ((γ ~ abind_tvar) ++ Θ0')
                  ρ Θ Hdecl Hinc) as [ρa [ρb' [Heqρ [Hdρa Hincxb]]]].
      destruct (a_inc_tvar_inv Hincxb)
        as [Ξv [Θ' [HeqΘ [HsufΞv Hincb]]]].
      assert (HwfΘ' : a_wf_aenv Θ').
      { rewrite HeqΘ in Hwfth.
        eapply a_wf_aenv_app_r with (Θp := Ξv ++ (γ ~ abind_tvar)).
        simpl_env. simpl_env in Hwfth. exact Hwfth. }
      assert (HeqW : (Ξv ++ (γ ~ abind_tvar)) ++ Θ' = Θ)
        by (rewrite HeqΘ; simpl_env; reflexivity).
      assert (Hincb_n : Θ0' ≤[ msubst_compose (aenv_msubst Θ) ρb' ] Θ').
      { pose proof (a_inc_self_downarrow Hincb
                      (Ξv ++ (γ ~ abind_tvar))) as Hs.
        rewrite HeqW in Hs. apply Hs; [ exact Hwfth | exact HuqΘ | exact Hwf0 ]. }
      assert (Hside : forall Y, Y `in` ftvar_in_pskl P ->
                Y `in` dom ρ \/ Y `notin` dom (aenv_msubst Θ)).
      { intros Y HY.
        destruct (AtomSetProperties.In_dec Y (dom ρ)) as [Hin | Hni];
          [ left; exact Hin | right ].
        intro Hin2. apply aenv_msubst_dom_inv in Hin2.
        destruct (ad_wf_pskl_ftv_tvarish HwfP HY) as [Hemp | Hbt];
          [ clear - Hemp; fsetdec | ].
        destruct Hbt as [Htv | [Hfm | [τ0 Hfd]]].
        - assert (HtvΘ : binds Y abind_tvar Θ)
            by (eapply a_inc_binds_tvar; [ exact Hinc | exact Htv ]).
          destruct Hin2 as [Hb | [τ1 Hb]];
            (pose proof (binds_unique _ _ _ _ _ HtvΘ Hb
                           (a_wf_aenv_uniq Hwfth)) as Heqb;
             discriminate Heqb).
        - assert (Hyd : Y `in` dom ρ)
            by (eapply a_inc_flex_dom;
                [ exact Hinc | exact Hwf | left; exact Hfm ]).
          contradiction.
        - assert (Hyd : Y `in` dom ρ)
            by (eapply a_inc_flex_dom;
                [ exact Hinc | exact Hwf | right; exists τ0; exact Hfd ]).
          contradiction. }
      assert (Hmona : mono_ptyp (msubst_lookup ρ α))
        by (eapply a_inc_lookup_mono; exact Hinc).
      assert (HO2 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)) [<=] dom Θ').
      { eapply join_pskl_downarrow_mono_scoped;
          [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
          | exact Hmona | | ].
        - intros β τ Hbβ Hβd.
          assert (Hβpre : β `notin` dom (Ξv ++ (γ ~ abind_tvar))).
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
          assert (Hαρa : α `notin` dom ρa).
          { rewrite Hdρa. clear - Huqf HαΘ0. simpl_env in Huqf. solve_uniq. }
          assert (Hwfα : a_wf_ptyp Θ' (msubst_lookup ρ α)).
          { rewrite Heqρ. rewrite (msubst_lookup_app_notin ρa ρb' Hαρa).
            eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ].
            destruct Hfα0 as [Hb | [τ0 Hb]];
              [ right; left; exact Hb | right; right; exists τ0; exact Hb ]. }
          apply a_wf_ptyp_ftv_dom. exact Hwfα. }
      assert (Hgr : forall X, X `in` dom ρa ->
                 ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup ρa X)) [<=] dom Θ').
      { intros X HX.
        assert (HXP : X `in` ftvar_in_pskl P)
          by (apply Hdomξ; rewrite <- Hdρa; exact HX).
        assert (HXρ : X `in` dom ρ)
          by (rewrite Heqρ; rewrite dom_app; clear - HX; fsetdec).
        assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup ρa X)
                       = msubst_lookup (msubst_compose (aenv_msubst Θ) ρ) X).
        { rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ (or_introl HXρ)).
          f_equal. rewrite Heqρ. symmetry.
          apply msubst_lookup_app_in; exact HX. }
        rewrite Heqlk.
        eapply AtomSetProperties.subset_trans;
          [ apply (msubst_pskl_ftv_lower
                     (msubst_compose (aenv_msubst Θ) ρ) P HXP) | ].
        rewrite msubst_pskl_compose; [ exact HO2 | exact Hside ]. }
      assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
      { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
        exact Hb. }
      assert (Hinc_sub0 : (Ξ ++ Θ0') ≤[ (msubst_compose (aenv_msubst Θ) ρa)
                              ++ (msubst_compose (aenv_msubst Θ) ρb') ] Θ').
      { assert (HincR : (Ξ ++ (γ ~ abind_tvar) ++ Θ0') ≤[ ρa ++ ρb' ] Θ)
          by (rewrite <- Heqρ; exact Hinc).
        eapply a_inc_downarrow_prefix;
          [ exact Hdecl | exact HincR | exact Huqf | exact Hdρa
          | exact Hincb_n | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
      assert (Hinc_sub : (Ξ ++ Θ0') ≤[ msubst_compose (aenv_msubst Θ) ρ ] Θ').
      { rewrite Heqρ. rewrite msubst_compose_app. exact Hinc_sub0. }
      (* the join over Θ' at ⇓ρ *)
      assert (HαΘ0 : α `in` dom Θ0')
        by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
      assert (Hαρa : α `notin` dom ρa)
        by (rewrite Hdρa; clear - Huqf HαΘ0; simpl_env in Huqf; solve_uniq).
      assert (Hbtα0 : a_binds_tvar α Θ0')
        by (destruct Hfα0 as [Hb | [τ0 Hb]];
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]).
      assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup ρ α)).
      { rewrite Heqρ. rewrite (msubst_lookup_app_notin ρa ρb' Hαρa).
        eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | exact Hbtα0 ]. }
      assert (Hftvα : ftvar_in_ptyp (msubst_lookup ρ α) [<=] dom Θ')
        by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
      assert (Hvisα : forall Y, Y `in` ftvar_in_ptyp (msubst_lookup ρ α) ->
                a_binds_tvar Y Θ).
      { intros Y HY.
        assert (HbtY' : a_binds_tvar Y Θ')
          by (eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfα' | exact HY ]).
        destruct HbtY' as [Hb | [Hb | [τ0 Hb]]];
          [ left | right; left | right; right; exists τ0 ];
          apply Hsub'; exact Hb. }
      assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup ρ α)
                   = ⇓ᵗ[ Θ' ] (msubst_lookup ρ α)).
      { rewrite <- HeqW.
        apply downarrow_app_agree_ptyp;
          [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
      assert (Hj1 : ad_pat_consis empty Θ
                (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)))
                (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α)))).
      { eapply consis_downarrow_subject;
          [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
          | exact Hmona ]. }
      assert (Heqρα : Θ ⊢ (msubst_lookup ρ α)
                        ≡ᵗ (⇓ᵗ[ Θ ] (msubst_lookup ρ α))).
      { apply a_tyequiv_to_downarrow_mono;
          [ exact Hwfth
          | eapply a_wf_ptyp_weaken; [ exact Hsub' | exact Hwfα' ]
          | exact Hmona ]. }
      destruct (tyequiv_mono_consis_transport_q Heqρα Hwfth Hmona Hvisα)
        as [_ Hfwd].
      pose proof (Hfwd empty _ Hj1) as Hj2.
      assert (Hjstr : ad_pat_consis empty Θ'
                (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)))
                (pskl_to_bskl_syn (ptyp_to_pskl
                   (⇓ᵗ[ Θ ] (msubst_lookup ρ α))))).
      { eapply ad_pat_consis_strengthen;
          [ exact Hj2 | exact HuqΘ | exact HwfΘ' | exact Hsub' | | ].
        - intros Z HZ. rewrite ftvar_in_uskl_pskl in HZ.
          clear - HO2 HZ. fsetdec.
        - intros Z HZ. rewrite ftvar_in_bskl_syn in HZ.
          rewrite ftvar_in_ptyp_to_pskl in HZ.
          rewrite Hddα in HZ.
          assert (Hwfd : a_wf_ptyp Θ' (⇓ᵗ[ Θ' ] (msubst_lookup ρ α)))
            by (apply a_wf_ptyp_downarrow_mono;
                [ exact HwfΘ' | exact Hwfα' | exact Hmona ]).
          apply a_wf_ptyp_ftv_dom in Hwfd. clear - Hwfd HZ. fsetdec. }
      assert (Hαρdom : α `in` dom ρ).
      { rewrite Heqρ. rewrite dom_app.
        assert (Hαb : α `in` dom ρb')
          by (eapply a_inc_flex_dom;
              [ exact Hincb | exact Hwf0 | exact Hfα0 ]).
        clear - Hαb. fsetdec. }
      assert (Hjoin_sub : empty ⨟ Θ' ⊨ₛᵃ
                (pskl_to_uskl (msubst_pskl
                   (msubst_compose (aenv_msubst Θ) ρ) P))
              ≈ (pskl_to_bskl_syn (ptyp_to_pskl
                  (msubst_lookup (msubst_compose (aenv_msubst Θ) ρ) α)))).
      { rewrite (msubst_pskl_compose (aenv_msubst Θ) ρ P Hside).
        rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ (or_introl Hαρdom)).
        exact Hjstr. }
      (* ---- the μ-IH at the truncated problem : V is exactly constant ---- *)
      assert (Hlt : mu_lt
          (mu_assign Θ' (msubst_compose (aenv_msubst Θ) ρ) α P Ξ Θ0')
          (mu_assign Θ ρ α P Ξ ((γ, abind_tvar) :: Θ0'))).
      { unfold mu_assign. apply mu_lt_intro. right. split.
        - unfold V_assign, Vpskl, Vvar.
          rewrite (msubst_pskl_compose (aenv_msubst Θ) ρ P Hside).
          rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ
                     (or_introl Hαρdom)).
          rewrite downarrow_idem_sub_pskl;
            [ | exact Hwfth | exact Hsub' ].
          rewrite downarrow_idem_sub_ptyp;
            [ | exact Hwfth | exact Hsub' ].
          reflexivity.
        - left. simpl. lia. }
      destruct (IH _ Hlt) as [_ [_ HaIH]].
      destruct (HaIH (add γ F) Θ0' Ξ α P
                     (msubst_compose (aenv_msubst Θ) ρ) Θ' eq_refl
                     Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hinc_sub HwfΘ'
                     Hjoin_sub)
        as [Θ1 [Ha' Hopt'']].
      exists ((γ ~ abind_tvar) ++ Θ1). split.
      { apply a_assign__skip_rigid; [ exact Hγni | exact Ha' ]. }
      (* ---- optimality : the OPT twin's two conjuncts ---- *)
      intros ρ1 Hid Hinc1.
      assert (Hinc1_s : (Ξ ++ Θ0') ≤[ ρ1 ] Θ1)
        by (eapply a_inc_tvar_mid_strip_id;
            [ exact Hdecl | exact Huqf | exact Hid | exact Hinc1 ]).
      destruct (Hopt'' ρ1 Hid Hinc1_s) as [ζ' [Hζ' Hie']].
      exists ζ'. split.
      * (* ((γ~tvar)++Θ1) ≤[ζ'] Θ  via a_inc__tvar *)
        rewrite HeqΘ. apply a_inc__tvar; [ exact Hζ' | exact HsufΞv ].
      * (* factoring: mid_insert_tvar over ⇓ρ, then ⇓ρ→ρ *)
        destruct (@a_inc_strip_decls_prefix Ξ ((γ ~ abind_tvar) ++ Θ0')
                    ρ1 ((γ ~ abind_tvar) ++ Θ1) Hdecl Hinc1)
          as [ρ1a [ρ1b' [Heqρ1' [Hdρ1a Hinc1x]]]].
        assert (Hmi : a_inc_equiv (Ξ ++ (γ ~ abind_tvar) ++ Θ0')
                        (msubst_compose (aenv_msubst Θ) ρ)
                        (msubst_compose ζ' ρ1)
                        (Ξv ++ (γ ~ abind_tvar) ++ Θ')).
        { rewrite Heqρ. rewrite (msubst_compose_app (aenv_msubst Θ) ρa ρb').
          rewrite Heqρ1'. rewrite (msubst_compose_app ζ' ρ1a ρ1b').
          apply a_inc_equiv_mid_insert_tvar;
            [ exact Hdecl | exact Huq'
            | rewrite dom_msubst_compose; exact Hdρa
            | rewrite dom_msubst_compose; exact Hdρ1a
            | exact HsufΞv | ].
          rewrite Heqρ in Hie'.
          rewrite (msubst_compose_app (aenv_msubst Θ) ρa ρb') in Hie'.
          rewrite Heqρ1' in Hie'.
          rewrite (msubst_compose_app ζ' ρ1a ρ1b') in Hie'.
          exact Hie'. }
        rewrite <- HeqΘ in Hmi.
        eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
        pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
          as Hself.
        simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ].
  - (* head [γ ~ var_typ A] : Assign-SkipTmVar — the EX+OPT fusion of the
       CLOSED OPT twin [skip_tm_var_case] (prop_consis_complete.v:990):
       ⇓-normalize the competing increment below the middle, strengthen
       the join to the truncated target, recurse through the μ-IH (V is
       exactly constant by ⇓-idempotence, §1e), rebuild with the semantic
       middle. *)
    assert (Huqf : uniq (Ξ ++ (γ ~ abind_var_typ A) ++ Θ0'))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfM : a_wf_aenv (Ξ ++ (γ ~ abind_var_typ A) ++ Θ0'))
      by (exact Hwf).
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
      by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
    assert (Huq' : uniq (Ξ ++ Θ0')) by (apply a_wf_aenv_uniq; exact Hwf').
    assert (Hwf0 : a_wf_aenv Θ0') by (eapply a_wf_aenv_app_r; exact Hwf').
    assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hγfr : γ `notin` ftvar_in_pskl P).
    { intro Hx. destruct (ad_wf_pskl_ftv_tvarish HwfP Hx) as [Hemp | Hbt].
      - clear - Hemp. fsetdec.
      - assert (Hbx : binds γ (abind_var_typ A)
                  (Ξ ++ (γ ~ abind_var_typ A) ++ Θ0'))
          by (apply binds_app_3; left; reflexivity).
        destruct Hbt as [Hb | [Hb | [τ Hb]]];
          (pose proof (binds_unique _ _ _ _ _ Hb Hbx
                         (a_wf_aenv_uniq Hwf)) as Heq;
           discriminate Heq). }
    assert (HwfP' : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
      by (eapply ad_wf_pskl_strip_mid; [ exact HwfP | exact Hγfr ]).
    assert (Hfα0 : a_flex_tvar Θ0' α).
    { destruct Hfα as [Hb | [τ0 Hb]];
        [ destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
          [ discriminate | left; exact Hb' ]
        | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
          [ discriminate | right; exists τ0; exact Hb' ] ]. }
    assert (Hbw : forall (δ : atom) (bb : abind),
              binds δ bb (Ξ ++ Θ0') ->
              binds δ bb (Ξ ++ (γ ~ abind_var_typ A) ++ Θ0')).
    { intros δ bb Hb. unfold binds in *.
      apply in_app_or in Hb. apply in_or_app.
      destruct Hb as [Hb | Hb];
        [ left; exact Hb | right; simpl; right; exact Hb ]. }
    assert (Hnf' : a_non_flex (Ξ ++ Θ0') P).
    { destruct Hnf as [Hlc Hnfl]. split; [ exact Hlc | ].
      intro Hfl. apply Hnfl.
      inversion Hfl as [Θf δ Hb | Θf δ τ0 Hb]; subst;
        [ apply a_flex__var; apply Hbw; exact Hb
        | eapply a_flex__var_def; apply Hbw; exact Hb ]. }
    (* competing: strip Ξ, invert the γ-var middle *)
    destruct (@a_inc_strip_decls_prefix Ξ ((γ ~ abind_var_typ A) ++ Θ0')
                ρ Θ Hdecl Hinc) as [ρa [ρb' [Heqρ [Hdρa Hincxb]]]].
    destruct (a_inc_var_inv Hincxb)
      as [Ξv [A' [Θ' [HeqΘ [HeqA' [HsufΞv Hincb]]]]]].
    assert (HwfΘ' : a_wf_aenv Θ').
    { rewrite HeqΘ in Hwfth.
      eapply a_wf_aenv_app_r with (Θp := Ξv ++ (γ ~ abind_var_typ A')).
      simpl_env. simpl_env in Hwfth. exact Hwfth. }
    assert (HeqW : (Ξv ++ (γ ~ abind_var_typ A')) ++ Θ' = Θ)
      by (rewrite HeqΘ; simpl_env; reflexivity).
    assert (Hincb_n : Θ0' ≤[ msubst_compose (aenv_msubst Θ) ρb' ] Θ').
    { pose proof (a_inc_self_downarrow Hincb
                    (Ξv ++ (γ ~ abind_var_typ A'))) as Hs.
      rewrite HeqW in Hs. apply Hs; [ exact Hwfth | exact HuqΘ | exact Hwf0 ]. }
    assert (Hside : forall Y, Y `in` ftvar_in_pskl P ->
              Y `in` dom ρ \/ Y `notin` dom (aenv_msubst Θ)).
    { intros Y HY.
      destruct (AtomSetProperties.In_dec Y (dom ρ)) as [Hin | Hni];
        [ left; exact Hin | right ].
      intro Hin2. apply aenv_msubst_dom_inv in Hin2.
      destruct (ad_wf_pskl_ftv_tvarish HwfP HY) as [Hemp | Hbt];
        [ clear - Hemp; fsetdec | ].
      destruct Hbt as [Htv | [Hfm | [τ0 Hfd]]].
      - assert (HtvΘ : binds Y abind_tvar Θ)
          by (eapply a_inc_binds_tvar; [ exact Hinc | exact Htv ]).
        destruct Hin2 as [Hb | [τ1 Hb]];
          (pose proof (binds_unique _ _ _ _ _ HtvΘ Hb
                         (a_wf_aenv_uniq Hwfth)) as Heqb;
           discriminate Heqb).
      - assert (Hyd : Y `in` dom ρ)
          by (eapply a_inc_flex_dom;
              [ exact Hinc | exact Hwf | left; exact Hfm ]).
        contradiction.
      - assert (Hyd : Y `in` dom ρ)
          by (eapply a_inc_flex_dom;
              [ exact Hinc | exact Hwf | right; exists τ0; exact Hfd ]).
        contradiction. }
    assert (Hmona : mono_ptyp (msubst_lookup ρ α))
      by (eapply a_inc_lookup_mono; exact Hinc).
    assert (HO2 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)) [<=] dom Θ').
    { eapply join_pskl_downarrow_mono_scoped;
        [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
        | exact Hmona | | ].
      - intros β τ Hbβ Hβd.
        assert (Hβpre : β `notin` dom (Ξv ++ (γ ~ abind_var_typ A'))).
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
        assert (Hαρa : α `notin` dom ρa).
        { rewrite Hdρa. clear - Huqf HαΘ0. simpl_env in Huqf. solve_uniq. }
        assert (Hwfα : a_wf_ptyp Θ' (msubst_lookup ρ α)).
        { rewrite Heqρ. rewrite (msubst_lookup_app_notin ρa ρb' Hαρa).
          eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ].
          destruct Hfα0 as [Hb | [τ0 Hb]];
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]. }
        apply a_wf_ptyp_ftv_dom. exact Hwfα. }
    assert (Hgr : forall X, X `in` dom ρa ->
               ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup ρa X)) [<=] dom Θ').
    { intros X HX.
      assert (HXP : X `in` ftvar_in_pskl P)
        by (apply Hdomξ; rewrite <- Hdρa; exact HX).
      assert (HXρ : X `in` dom ρ)
        by (rewrite Heqρ; rewrite dom_app; clear - HX; fsetdec).
      assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup ρa X)
                     = msubst_lookup (msubst_compose (aenv_msubst Θ) ρ) X).
      { rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ (or_introl HXρ)).
        f_equal. rewrite Heqρ. symmetry.
        apply msubst_lookup_app_in; exact HX. }
      rewrite Heqlk.
      eapply AtomSetProperties.subset_trans;
        [ apply (msubst_pskl_ftv_lower
                   (msubst_compose (aenv_msubst Θ) ρ) P HXP) | ].
      rewrite msubst_pskl_compose; [ exact HO2 | exact Hside ]. }
    assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
    { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
      exact Hb. }
    assert (Hinc_sub0 : (Ξ ++ Θ0') ≤[ (msubst_compose (aenv_msubst Θ) ρa)
                            ++ (msubst_compose (aenv_msubst Θ) ρb') ] Θ').
    { assert (HincR : (Ξ ++ (γ ~ abind_var_typ A) ++ Θ0') ≤[ ρa ++ ρb' ] Θ)
        by (rewrite <- Heqρ; exact Hinc).
      eapply a_inc_downarrow_prefix;
        [ exact Hdecl | exact HincR | exact Huqf | exact Hdρa
        | exact Hincb_n | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
    assert (Hinc_sub : (Ξ ++ Θ0') ≤[ msubst_compose (aenv_msubst Θ) ρ ] Θ').
    { rewrite Heqρ. rewrite msubst_compose_app. exact Hinc_sub0. }
    (* the join over Θ' at ⇓ρ *)
    assert (HαΘ0 : α `in` dom Θ0')
      by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
    assert (Hαρa : α `notin` dom ρa)
      by (rewrite Hdρa; clear - Huqf HαΘ0; simpl_env in Huqf; solve_uniq).
    assert (Hbtα0 : a_binds_tvar α Θ0')
      by (destruct Hfα0 as [Hb | [τ0 Hb]];
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]).
    assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup ρ α)).
    { rewrite Heqρ. rewrite (msubst_lookup_app_notin ρa ρb' Hαρa).
      eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | exact Hbtα0 ]. }
    assert (Hftvα : ftvar_in_ptyp (msubst_lookup ρ α) [<=] dom Θ')
      by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
    assert (Hvisα : forall Y, Y `in` ftvar_in_ptyp (msubst_lookup ρ α) ->
              a_binds_tvar Y Θ).
    { intros Y HY.
      assert (HbtY' : a_binds_tvar Y Θ')
        by (eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfα' | exact HY ]).
      destruct HbtY' as [Hb | [Hb | [τ0 Hb]]];
        [ left | right; left | right; right; exists τ0 ];
        apply Hsub'; exact Hb. }
    assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup ρ α)
                 = ⇓ᵗ[ Θ' ] (msubst_lookup ρ α)).
    { rewrite <- HeqW.
      apply downarrow_app_agree_ptyp;
        [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
    assert (Hj1 : ad_pat_consis empty Θ
              (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)))
              (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α)))).
    { eapply consis_downarrow_subject;
        [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
        | exact Hmona ]. }
    assert (Heqρα : Θ ⊢ (msubst_lookup ρ α)
                      ≡ᵗ (⇓ᵗ[ Θ ] (msubst_lookup ρ α))).
    { apply a_tyequiv_to_downarrow_mono;
        [ exact Hwfth
        | eapply a_wf_ptyp_weaken; [ exact Hsub' | exact Hwfα' ]
        | exact Hmona ]. }
    destruct (tyequiv_mono_consis_transport_q Heqρα Hwfth Hmona Hvisα)
      as [_ Hfwd].
    pose proof (Hfwd empty _ Hj1) as Hj2.
    assert (Hjstr : ad_pat_consis empty Θ'
              (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)))
              (pskl_to_bskl_syn (ptyp_to_pskl
                 (⇓ᵗ[ Θ ] (msubst_lookup ρ α))))).
    { eapply ad_pat_consis_strengthen;
        [ exact Hj2 | exact HuqΘ | exact HwfΘ' | exact Hsub' | | ].
      - intros Z HZ. rewrite ftvar_in_uskl_pskl in HZ.
        clear - HO2 HZ. fsetdec.
      - intros Z HZ. rewrite ftvar_in_bskl_syn in HZ.
        rewrite ftvar_in_ptyp_to_pskl in HZ.
        rewrite Hddα in HZ.
        assert (Hwfd : a_wf_ptyp Θ' (⇓ᵗ[ Θ' ] (msubst_lookup ρ α)))
          by (apply a_wf_ptyp_downarrow_mono;
              [ exact HwfΘ' | exact Hwfα' | exact Hmona ]).
        apply a_wf_ptyp_ftv_dom in Hwfd. clear - Hwfd HZ. fsetdec. }
    assert (Hαρdom : α `in` dom ρ).
    { rewrite Heqρ. rewrite dom_app.
      assert (Hαb : α `in` dom ρb')
        by (eapply a_inc_flex_dom;
            [ exact Hincb | exact Hwf0 | exact Hfα0 ]).
      clear - Hαb. fsetdec. }
    assert (Hjoin_sub : empty ⨟ Θ' ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl
                 (msubst_compose (aenv_msubst Θ) ρ) P))
            ≈ (pskl_to_bskl_syn (ptyp_to_pskl
                (msubst_lookup (msubst_compose (aenv_msubst Θ) ρ) α)))).
    { rewrite (msubst_pskl_compose (aenv_msubst Θ) ρ P Hside).
      rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ (or_introl Hαρdom)).
      exact Hjstr. }
    (* ---- the μ-IH at the truncated problem : V is exactly constant ---- *)
    assert (Hlt : mu_lt
        (mu_assign Θ' (msubst_compose (aenv_msubst Θ) ρ) α P Ξ Θ0')
        (mu_assign Θ ρ α P Ξ ((γ, abind_var_typ A) :: Θ0'))).
    { unfold mu_assign. apply mu_lt_intro. right. split.
      - unfold V_assign, Vpskl, Vvar.
        rewrite (msubst_pskl_compose (aenv_msubst Θ) ρ P Hside).
        rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ
                   (or_introl Hαρdom)).
        rewrite downarrow_idem_sub_pskl;
          [ | exact Hwfth | exact Hsub' ].
        rewrite downarrow_idem_sub_ptyp;
          [ | exact Hwfth | exact Hsub' ].
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [_ HaIH]].
    destruct (HaIH (add γ F) Θ0' Ξ α P
                   (msubst_compose (aenv_msubst Θ) ρ) Θ' eq_refl
                   Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hinc_sub HwfΘ'
                   Hjoin_sub)
      as [Θ1 [Ha' Hopt'']].
    exists ((γ ~ abind_var_typ A) ++ Θ1). split.
    { apply a_assign__skip_tm_var. exact Ha'. }
    (* ---- optimality : the OPT twin's two conjuncts ---- *)
    intros ρ1 Hid Hinc1.
    assert (Hinc1_s : (Ξ ++ Θ0') ≤[ ρ1 ] Θ1)
      by (eapply a_inc_var_mid_strip_id;
          [ exact Hdecl | exact Hid | exact Hinc1 ]).
    destruct (Hopt'' ρ1 Hid Hinc1_s) as [ζ' [Hζ' Hie']].
    exists ζ'. split.
    + (* ((γ:A)++Θ1) ≤[ζ'] Θ  via a_inc__var *)
      rewrite HeqΘ. apply a_inc__var; [ exact Hζ' | | exact HsufΞv ].
      assert (HwfaΘ0x : a_wf_aenv ((γ ~ abind_var_typ A) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      destruct (a_wf_aenv_var_typ_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HwfQ : a_wf_ptyp (Ξ ++ Θ0') A)
        by (eapply a_wf_ptyp_weaken;
            [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
      assert (HlcQ : lc_ptyp A) by (eapply a_wf_ptyp_lc; exact HwfQ0).
      assert (HwfΘ1 : a_wf_aenv Θ1)
        by (eapply a_assign_preserves_wf;
            [ exact Ha' | exact Hdecl | exact Hwf' | exact HwfP' ]).
      assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) ρ))
        by (eapply a_inc_msubst_lc; exact Hinc_sub).
      assert (Hlc2 : msubst_lc (msubst_compose ζ' ρ1)).
      { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ' | ].
        intros a t Hin. eapply is_id_msubst_values_lc;
          [ exact Hid | exact Hin ]. }
      pose proof (a_inc_equiv_msubst_ptyp HwfQ Hie' Hwf' Hlc1 Hlc2)
        as Hmid.
      rewrite (msubst_compose_id_ptyp Hwf' HwfΘ1 Hid Hinc1_s Hζ' HwfQ)
        in Hmid.
      assert (Hag : msubst_ptyp (msubst_compose (aenv_msubst Θ) ρ) A
                  = msubst_ptyp (msubst_compose (aenv_msubst Θ) ρb') A).
      { apply msubst_ptyp_agree. intros X HXQ.
        rewrite Heqρ. rewrite msubst_compose_app.
        apply msubst_lookup_app_notin.
        rewrite dom_msubst_compose. rewrite Hdρa.
        assert (HXΘ0 : X `in` dom Θ0')
          by (apply a_wf_ptyp_ftv_dom in HwfQ0;
              clear - HwfQ0 HXQ; fsetdec).
        clear - Huqf HXΘ0. simpl_env in Huqf. solve_uniq. }
      rewrite Hag in Hmid.
      eapply a_tyequiv__trans; [ exact HeqA' | ].
      eapply a_tyequiv__trans; [ | exact Hmid ].
      apply a_tyequiv__sym.
      eapply msubst_compose_downarrow_tyequiv
        with (Θpre := Ξv ++ (γ ~ abind_var_typ A'));
        [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth
        | exact HwfΘ' | eapply a_inc_msubst_lc; exact Hincb
        | intros X HXd;
          destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
          (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
        | exact HlcQ ].
    + (* factoring: mid_insert_var over ⇓ρ, then ⇓ρ→ρ via self_downarrow *)
      assert (HwfaΘ0x : a_wf_aenv ((γ ~ abind_var_typ A) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      destruct (a_wf_aenv_var_typ_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HlcQ : lc_ptyp A) by (eapply a_wf_ptyp_lc; exact HwfQ0).
      destruct (@a_inc_strip_decls_prefix Ξ ((γ ~ abind_var_typ A) ++ Θ0')
                  ρ1 ((γ ~ abind_var_typ A) ++ Θ1) Hdecl Hinc1)
        as [ρ1a [ρ1b' [Heqρ1' [Hdρ1a Hinc1x]]]].
      assert (Hmiddle : Θ' ⊢ A' ≡ᵗ
                msubst_ptyp (msubst_compose (aenv_msubst Θ) ρb') A).
      { eapply a_tyequiv__trans; [ exact HeqA' | ].
        apply a_tyequiv__sym.
        eapply msubst_compose_downarrow_tyequiv
          with (Θpre := Ξv ++ (γ ~ abind_var_typ A'));
          [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
          | eapply a_inc_msubst_lc; exact Hincb
          | intros X HXd;
            destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
            (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
          | exact HlcQ ]. }
      assert (Hmi : a_inc_equiv (Ξ ++ (γ ~ abind_var_typ A) ++ Θ0')
                      (msubst_compose (aenv_msubst Θ) ρ)
                      (msubst_compose ζ' ρ1)
                      (Ξv ++ (γ ~ abind_var_typ A') ++ Θ')).
      { rewrite Heqρ. rewrite (msubst_compose_app (aenv_msubst Θ) ρa ρb').
        rewrite Heqρ1'. rewrite (msubst_compose_app ζ' ρ1a ρ1b').
        apply a_inc_equiv_mid_insert_var;
          [ exact Hdecl | exact Huq'
          | rewrite dom_msubst_compose; exact Hdρa
          | rewrite dom_msubst_compose; exact Hdρ1a
          | exact Hmiddle | exact HsufΞv | ].
        rewrite Heqρ in Hie'.
        rewrite (msubst_compose_app (aenv_msubst Θ) ρa ρb') in Hie'.
        rewrite Heqρ1' in Hie'.
        rewrite (msubst_compose_app ζ' ρ1a ρ1b') in Hie'.
        exact Hie'. }
      rewrite <- HeqΘ in Hmi.
      eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
      pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
        as Hself.
      simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ].
  - (* head [γ ~ var_skl Q] : Assign-SkipTmSkl — as SkipTmVar with the
       ≡ˢ semantic middle throughout. *)
    assert (Huqf : uniq (Ξ ++ (γ ~ abind_var_skl Q) ++ Θ0'))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfM : a_wf_aenv (Ξ ++ (γ ~ abind_var_skl Q) ++ Θ0'))
      by (exact Hwf).
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
      by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
    assert (Huq' : uniq (Ξ ++ Θ0')) by (apply a_wf_aenv_uniq; exact Hwf').
    assert (Hwf0 : a_wf_aenv Θ0') by (eapply a_wf_aenv_app_r; exact Hwf').
    assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hγfr : γ `notin` ftvar_in_pskl P).
    { intro Hx. destruct (ad_wf_pskl_ftv_tvarish HwfP Hx) as [Hemp | Hbt].
      - clear - Hemp. fsetdec.
      - assert (Hbx : binds γ (abind_var_skl Q)
                  (Ξ ++ (γ ~ abind_var_skl Q) ++ Θ0'))
          by (apply binds_app_3; left; reflexivity).
        destruct Hbt as [Hb | [Hb | [τ Hb]]];
          (pose proof (binds_unique _ _ _ _ _ Hb Hbx
                         (a_wf_aenv_uniq Hwf)) as Heq;
           discriminate Heq). }
    assert (HwfP' : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
      by (eapply ad_wf_pskl_strip_mid; [ exact HwfP | exact Hγfr ]).
    assert (Hfα0 : a_flex_tvar Θ0' α).
    { destruct Hfα as [Hb | [τ0 Hb]];
        [ destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
          [ discriminate | left; exact Hb' ]
        | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
          [ discriminate | right; exists τ0; exact Hb' ] ]. }
    assert (Hbw : forall (δ : atom) (bb : abind),
              binds δ bb (Ξ ++ Θ0') ->
              binds δ bb (Ξ ++ (γ ~ abind_var_skl Q) ++ Θ0')).
    { intros δ bb Hb. unfold binds in *.
      apply in_app_or in Hb. apply in_or_app.
      destruct Hb as [Hb | Hb];
        [ left; exact Hb | right; simpl; right; exact Hb ]. }
    assert (Hnf' : a_non_flex (Ξ ++ Θ0') P).
    { destruct Hnf as [Hlc Hnfl]. split; [ exact Hlc | ].
      intro Hfl. apply Hnfl.
      inversion Hfl as [Θf δ Hb | Θf δ τ0 Hb]; subst;
        [ apply a_flex__var; apply Hbw; exact Hb
        | eapply a_flex__var_def; apply Hbw; exact Hb ]. }
    (* competing: strip Ξ, invert the γ-var middle *)
    destruct (@a_inc_strip_decls_prefix Ξ ((γ ~ abind_var_skl Q) ++ Θ0')
                ρ Θ Hdecl Hinc) as [ρa [ρb' [Heqρ [Hdρa Hincxb]]]].
    destruct (a_inc_var_skl_inv Hincxb)
      as [Ξv [Q' [Θ' [HeqΘ [HeqQ' [HsufΞv Hincb]]]]]].
    assert (HwfΘ' : a_wf_aenv Θ').
    { rewrite HeqΘ in Hwfth.
      eapply a_wf_aenv_app_r with (Θp := Ξv ++ (γ ~ abind_var_skl Q')).
      simpl_env. simpl_env in Hwfth. exact Hwfth. }
    assert (HeqW : (Ξv ++ (γ ~ abind_var_skl Q')) ++ Θ' = Θ)
      by (rewrite HeqΘ; simpl_env; reflexivity).
    assert (Hincb_n : Θ0' ≤[ msubst_compose (aenv_msubst Θ) ρb' ] Θ').
    { pose proof (a_inc_self_downarrow Hincb
                    (Ξv ++ (γ ~ abind_var_skl Q'))) as Hs.
      rewrite HeqW in Hs. apply Hs; [ exact Hwfth | exact HuqΘ | exact Hwf0 ]. }
    assert (Hside : forall Y, Y `in` ftvar_in_pskl P ->
              Y `in` dom ρ \/ Y `notin` dom (aenv_msubst Θ)).
    { intros Y HY.
      destruct (AtomSetProperties.In_dec Y (dom ρ)) as [Hin | Hni];
        [ left; exact Hin | right ].
      intro Hin2. apply aenv_msubst_dom_inv in Hin2.
      destruct (ad_wf_pskl_ftv_tvarish HwfP HY) as [Hemp | Hbt];
        [ clear - Hemp; fsetdec | ].
      destruct Hbt as [Htv | [Hfm | [τ0 Hfd]]].
      - assert (HtvΘ : binds Y abind_tvar Θ)
          by (eapply a_inc_binds_tvar; [ exact Hinc | exact Htv ]).
        destruct Hin2 as [Hb | [τ1 Hb]];
          (pose proof (binds_unique _ _ _ _ _ HtvΘ Hb
                         (a_wf_aenv_uniq Hwfth)) as Heqb;
           discriminate Heqb).
      - assert (Hyd : Y `in` dom ρ)
          by (eapply a_inc_flex_dom;
              [ exact Hinc | exact Hwf | left; exact Hfm ]).
        contradiction.
      - assert (Hyd : Y `in` dom ρ)
          by (eapply a_inc_flex_dom;
              [ exact Hinc | exact Hwf | right; exists τ0; exact Hfd ]).
        contradiction. }
    assert (Hmona : mono_ptyp (msubst_lookup ρ α))
      by (eapply a_inc_lookup_mono; exact Hinc).
    assert (HO2 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)) [<=] dom Θ').
    { eapply join_pskl_downarrow_mono_scoped;
        [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
        | exact Hmona | | ].
      - intros β τ Hbβ Hβd.
        assert (Hβpre : β `notin` dom (Ξv ++ (γ ~ abind_var_skl Q'))).
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
        assert (Hαρa : α `notin` dom ρa).
        { rewrite Hdρa. clear - Huqf HαΘ0. simpl_env in Huqf. solve_uniq. }
        assert (Hwfα : a_wf_ptyp Θ' (msubst_lookup ρ α)).
        { rewrite Heqρ. rewrite (msubst_lookup_app_notin ρa ρb' Hαρa).
          eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ].
          destruct Hfα0 as [Hb | [τ0 Hb]];
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]. }
        apply a_wf_ptyp_ftv_dom. exact Hwfα. }
    assert (Hgr : forall X, X `in` dom ρa ->
               ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup ρa X)) [<=] dom Θ').
    { intros X HX.
      assert (HXP : X `in` ftvar_in_pskl P)
        by (apply Hdomξ; rewrite <- Hdρa; exact HX).
      assert (HXρ : X `in` dom ρ)
        by (rewrite Heqρ; rewrite dom_app; clear - HX; fsetdec).
      assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup ρa X)
                     = msubst_lookup (msubst_compose (aenv_msubst Θ) ρ) X).
      { rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ (or_introl HXρ)).
        f_equal. rewrite Heqρ. symmetry.
        apply msubst_lookup_app_in; exact HX. }
      rewrite Heqlk.
      eapply AtomSetProperties.subset_trans;
        [ apply (msubst_pskl_ftv_lower
                   (msubst_compose (aenv_msubst Θ) ρ) P HXP) | ].
      rewrite msubst_pskl_compose; [ exact HO2 | exact Hside ]. }
    assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
    { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
      exact Hb. }
    assert (Hinc_sub0 : (Ξ ++ Θ0') ≤[ (msubst_compose (aenv_msubst Θ) ρa)
                            ++ (msubst_compose (aenv_msubst Θ) ρb') ] Θ').
    { assert (HincR : (Ξ ++ (γ ~ abind_var_skl Q) ++ Θ0') ≤[ ρa ++ ρb' ] Θ)
        by (rewrite <- Heqρ; exact Hinc).
      eapply a_inc_downarrow_prefix;
        [ exact Hdecl | exact HincR | exact Huqf | exact Hdρa
        | exact Hincb_n | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
    assert (Hinc_sub : (Ξ ++ Θ0') ≤[ msubst_compose (aenv_msubst Θ) ρ ] Θ').
    { rewrite Heqρ. rewrite msubst_compose_app. exact Hinc_sub0. }
    (* the join over Θ' at ⇓ρ *)
    assert (HαΘ0 : α `in` dom Θ0')
      by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
    assert (Hαρa : α `notin` dom ρa)
      by (rewrite Hdρa; clear - Huqf HαΘ0; simpl_env in Huqf; solve_uniq).
    assert (Hbtα0 : a_binds_tvar α Θ0')
      by (destruct Hfα0 as [Hb | [τ0 Hb]];
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]).
    assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup ρ α)).
    { rewrite Heqρ. rewrite (msubst_lookup_app_notin ρa ρb' Hαρa).
      eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | exact Hbtα0 ]. }
    assert (Hftvα : ftvar_in_ptyp (msubst_lookup ρ α) [<=] dom Θ')
      by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
    assert (Hvisα : forall Y, Y `in` ftvar_in_ptyp (msubst_lookup ρ α) ->
              a_binds_tvar Y Θ).
    { intros Y HY.
      assert (HbtY' : a_binds_tvar Y Θ')
        by (eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfα' | exact HY ]).
      destruct HbtY' as [Hb | [Hb | [τ0 Hb]]];
        [ left | right; left | right; right; exists τ0 ];
        apply Hsub'; exact Hb. }
    assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup ρ α)
                 = ⇓ᵗ[ Θ' ] (msubst_lookup ρ α)).
    { rewrite <- HeqW.
      apply downarrow_app_agree_ptyp;
        [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
    assert (Hj1 : ad_pat_consis empty Θ
              (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)))
              (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α)))).
    { eapply consis_downarrow_subject;
        [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
        | exact Hmona ]. }
    assert (Heqρα : Θ ⊢ (msubst_lookup ρ α)
                      ≡ᵗ (⇓ᵗ[ Θ ] (msubst_lookup ρ α))).
    { apply a_tyequiv_to_downarrow_mono;
        [ exact Hwfth
        | eapply a_wf_ptyp_weaken; [ exact Hsub' | exact Hwfα' ]
        | exact Hmona ]. }
    destruct (tyequiv_mono_consis_transport_q Heqρα Hwfth Hmona Hvisα)
      as [_ Hfwd].
    pose proof (Hfwd empty _ Hj1) as Hj2.
    assert (Hjstr : ad_pat_consis empty Θ'
              (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)))
              (pskl_to_bskl_syn (ptyp_to_pskl
                 (⇓ᵗ[ Θ ] (msubst_lookup ρ α))))).
    { eapply ad_pat_consis_strengthen;
        [ exact Hj2 | exact HuqΘ | exact HwfΘ' | exact Hsub' | | ].
      - intros Z HZ. rewrite ftvar_in_uskl_pskl in HZ.
        clear - HO2 HZ. fsetdec.
      - intros Z HZ. rewrite ftvar_in_bskl_syn in HZ.
        rewrite ftvar_in_ptyp_to_pskl in HZ.
        rewrite Hddα in HZ.
        assert (Hwfd : a_wf_ptyp Θ' (⇓ᵗ[ Θ' ] (msubst_lookup ρ α)))
          by (apply a_wf_ptyp_downarrow_mono;
              [ exact HwfΘ' | exact Hwfα' | exact Hmona ]).
        apply a_wf_ptyp_ftv_dom in Hwfd. clear - Hwfd HZ. fsetdec. }
    assert (Hαρdom : α `in` dom ρ).
    { rewrite Heqρ. rewrite dom_app.
      assert (Hαb : α `in` dom ρb')
        by (eapply a_inc_flex_dom;
            [ exact Hincb | exact Hwf0 | exact Hfα0 ]).
      clear - Hαb. fsetdec. }
    assert (Hjoin_sub : empty ⨟ Θ' ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl
                 (msubst_compose (aenv_msubst Θ) ρ) P))
            ≈ (pskl_to_bskl_syn (ptyp_to_pskl
                (msubst_lookup (msubst_compose (aenv_msubst Θ) ρ) α)))).
    { rewrite (msubst_pskl_compose (aenv_msubst Θ) ρ P Hside).
      rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ (or_introl Hαρdom)).
      exact Hjstr. }
    (* ---- the μ-IH at the truncated problem : V is exactly constant ---- *)
    assert (Hlt : mu_lt
        (mu_assign Θ' (msubst_compose (aenv_msubst Θ) ρ) α P Ξ Θ0')
        (mu_assign Θ ρ α P Ξ ((γ, abind_var_skl Q) :: Θ0'))).
    { unfold mu_assign. apply mu_lt_intro. right. split.
      - unfold V_assign, Vpskl, Vvar.
        rewrite (msubst_pskl_compose (aenv_msubst Θ) ρ P Hside).
        rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ
                   (or_introl Hαρdom)).
        rewrite downarrow_idem_sub_pskl;
          [ | exact Hwfth | exact Hsub' ].
        rewrite downarrow_idem_sub_ptyp;
          [ | exact Hwfth | exact Hsub' ].
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [_ HaIH]].
    destruct (HaIH (add γ F) Θ0' Ξ α P
                   (msubst_compose (aenv_msubst Θ) ρ) Θ' eq_refl
                   Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hinc_sub HwfΘ'
                   Hjoin_sub)
      as [Θ1 [Ha' Hopt'']].
    exists ((γ ~ abind_var_skl Q) ++ Θ1). split.
    { apply a_assign__skip_tm_skl. exact Ha'. }
    (* ---- optimality : the OPT twin's two conjuncts ---- *)
    intros ρ1 Hid Hinc1.
    assert (Hinc1_s : (Ξ ++ Θ0') ≤[ ρ1 ] Θ1)
      by (eapply a_inc_var_skl_mid_strip_id;
          [ exact Hdecl | exact Hid | exact Hinc1 ]).
    destruct (Hopt'' ρ1 Hid Hinc1_s) as [ζ' [Hζ' Hie']].
    exists ζ'. split.
    + (* ((γ:A)++Θ1) ≤[ζ'] Θ  via a_inc__var *)
      rewrite HeqΘ. apply a_inc__var_skl; [ exact Hζ' | | exact HsufΞv ].
      assert (HwfaΘ0x : a_wf_aenv ((γ ~ abind_var_skl Q) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      destruct (a_wf_aenv_var_skl_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HwfQ : a_wf_pskl (Ξ ++ Θ0') Q)
        by (eapply a_wf_pskl_weaken;
            [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
      assert (HlcQ : lc_pskl Q) by (eapply a_wf_pskl_lc; exact HwfQ0).
      assert (HwfΘ1 : a_wf_aenv Θ1)
        by (eapply a_assign_preserves_wf;
            [ exact Ha' | exact Hdecl | exact Hwf' | exact HwfP' ]).
      assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) ρ))
        by (eapply a_inc_msubst_lc; exact Hinc_sub).
      assert (Hlc2 : msubst_lc (msubst_compose ζ' ρ1)).
      { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ' | ].
        intros a t Hin. eapply is_id_msubst_values_lc;
          [ exact Hid | exact Hin ]. }
      pose proof (a_inc_equiv_msubst_pskl HwfQ Hie' Hwf' Hlc1 Hlc2)
        as Hmid.
      rewrite (msubst_compose_id_pskl Hwf' HwfΘ1 Hid Hinc1_s Hζ' HwfQ)
        in Hmid.
      assert (Hag : msubst_pskl (msubst_compose (aenv_msubst Θ) ρ) Q
                  = msubst_pskl (msubst_compose (aenv_msubst Θ) ρb') Q).
      { apply msubst_pskl_agree. intros X HXQ.
        rewrite Heqρ. rewrite msubst_compose_app.
        apply msubst_lookup_app_notin.
        rewrite dom_msubst_compose. rewrite Hdρa.
        assert (HXΘ0 : X `in` dom Θ0')
          by (apply a_wf_pskl_ftv_dom' in HwfQ0;
              clear - HwfQ0 HXQ; fsetdec).
        clear - Huqf HXΘ0. simpl_env in Huqf. solve_uniq. }
      rewrite Hag in Hmid.
      eapply a_pskl_tyequiv__trans; [ exact HeqQ' | ].
      eapply a_pskl_tyequiv__trans; [ | exact Hmid ].
      apply a_pskl_tyequiv__sym.
      eapply msubst_pskl_compose_downarrow_tyequiv
        with (Θpre := Ξv ++ (γ ~ abind_var_skl Q'));
        [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth
        | exact HwfΘ' | eapply a_inc_msubst_lc; exact Hincb
        | intros X HXd;
          destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
          (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
        | exact HlcQ ].
    + (* factoring: mid_insert_var over ⇓ρ, then ⇓ρ→ρ via self_downarrow *)
      assert (HwfaΘ0x : a_wf_aenv ((γ ~ abind_var_skl Q) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      destruct (a_wf_aenv_var_skl_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HlcQ : lc_pskl Q) by (eapply a_wf_pskl_lc; exact HwfQ0).
      destruct (@a_inc_strip_decls_prefix Ξ ((γ ~ abind_var_skl Q) ++ Θ0')
                  ρ1 ((γ ~ abind_var_skl Q) ++ Θ1) Hdecl Hinc1)
        as [ρ1a [ρ1b' [Heqρ1' [Hdρ1a Hinc1x]]]].
      assert (Hmiddle : Θ' ⊢ Q' ≡ˢ
                msubst_pskl (msubst_compose (aenv_msubst Θ) ρb') Q).
      { eapply a_pskl_tyequiv__trans; [ exact HeqQ' | ].
        apply a_pskl_tyequiv__sym.
        eapply msubst_pskl_compose_downarrow_tyequiv
          with (Θpre := Ξv ++ (γ ~ abind_var_skl Q'));
          [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
          | eapply a_inc_msubst_lc; exact Hincb
          | intros X HXd;
            destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
            (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
          | exact HlcQ ]. }
      assert (Hmi : a_inc_equiv (Ξ ++ (γ ~ abind_var_skl Q) ++ Θ0')
                      (msubst_compose (aenv_msubst Θ) ρ)
                      (msubst_compose ζ' ρ1)
                      (Ξv ++ (γ ~ abind_var_skl Q') ++ Θ')).
      { rewrite Heqρ. rewrite (msubst_compose_app (aenv_msubst Θ) ρa ρb').
        rewrite Heqρ1'. rewrite (msubst_compose_app ζ' ρ1a ρ1b').
        apply a_inc_equiv_mid_insert_var_skl;
          [ exact Hdecl | exact Huq'
          | rewrite dom_msubst_compose; exact Hdρa
          | rewrite dom_msubst_compose; exact Hdρ1a
          | exact Hmiddle | exact HsufΞv | ].
        rewrite Heqρ in Hie'.
        rewrite (msubst_compose_app (aenv_msubst Θ) ρa ρb') in Hie'.
        rewrite Heqρ1' in Hie'.
        rewrite (msubst_compose_app ζ' ρ1a ρ1b') in Hie'.
        exact Hie'. }
      rewrite <- HeqΘ in Hmi.
      eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
      pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
        as Hself.
      simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ].
  - (* head [γ̂] undefined flexible *)
    destruct (γ == α) as [-> | Hγα].
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
        intros ρ1 Hid Hinc1. exists ρ.
        exact (opt_axiom_factor Hwf Hid Hinc1 Hinc).
      * (* Assign-SolveM : the standalone lemma above supplies the two
           premises the paper leaves implicit (design doc §9.2) — the
           occurs check and the mono guess witness — plus the ζ-factoring. *)
        apply (assign_solve_m_complete F Θ0' Hdecl Hwf HwfP Hnf HneP Hinc
                 Hwfth Hjoin).
    + (* γ̂ ≠ α̂ : Assign-Depend (γ ∈ ftv P) / Assign-Skip (γ ∉ ftv P) *)
      assert (Hαγ : α <> γ) by auto.
      assert (Hwfmid : a_wf_aenv ((γ ~ abind_flex_mono) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      inversion Hwfmid as [ | γh Θh Hnd Hwf0 | | | | ]; subst.
      assert (Hfα0 : a_flex_tvar Θ0' α)
        by (eapply a_flex_tvar_strip_head; [ exact Hαγ | exact Hfα ]).
      destruct (AtomSetProperties.In_dec γ (ftvar_in_pskl P)) as [Hγin | Hγni].
      * (* Assign-Depend : γ̂ moves to the tail of Ξ; pure re-association. *)
        assert (Hdecl' : a_decls (Ξ ++ (γ ~ abind_flex_mono)))
          by (apply a_decls_app;
              [ exact Hdecl | apply (a_decls__cons γ); apply a_decls__nil ]).
        assert (Hdomξ' : dom (Ξ ++ (γ ~ abind_flex_mono)) [<=] ftvar_in_pskl P)
          by (rewrite dom_app; simpl; clear - Hdomξ Hγin; fsetdec).
        assert (Hwf2 : a_wf_aenv ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0'))
          by (simpl_env; exact Hwf).
        assert (HwfP2 : ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
          by (simpl_env; exact HwfP).
        assert (Hnf2 : a_non_flex ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0') P)
          by (simpl_env; exact Hnf).
        assert (Hinc2 : ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0') ≤[ ρ ] Θ)
          by (simpl_env; exact Hinc).
        assert (Hlt : mu_lt (mu_assign Θ ρ α P (Ξ ++ (γ ~ abind_flex_mono)) Θ0')
                            (mu_assign Θ ρ α P Ξ ((γ ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_assign. apply mu_lt_intro. right. split; [ reflexivity | ].
          right. split.
          - rewrite length_app. simpl. lia.
          - right. split; [ reflexivity | simpl; lia ]. }
        destruct (IH _ Hlt) as [_ [_ HaIH]].
        destruct (HaIH F Θ0' (Ξ ++ (γ ~ abind_flex_mono)) α P ρ Θ eq_refl
                       Hdecl' Hwf2 Hfα0 HwfP2 Hnf2 Hdomξ' Hinc2 Hwfth Hjoin)
          as [Θ1 [Ha' Hopt']].
        exists Θ1. split.
        { apply a_assign__depend; [ exact Hαγ | exact Hγin | exact Ha' ]. }
        intros ρ1 Hid Hinc1.
        assert (Hinc1' : ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0') ≤[ ρ1 ] Θ1)
          by (simpl_env; exact Hinc1).
        destruct (Hopt' ρ1 Hid Hinc1') as [ζ [Hζ Hie]].
        exists ζ. split; [ exact Hζ | ].
        simpl_env in Hie. exact Hie.
      * (* Assign-Skip : γ̂ dropped from the walked context (mid-strip). *)
        destruct (a_inc_mid_strip_flex γ Θ0' Hdecl Hinc)
          as [ρa [τγ [ρb [Heqρ [Hdρa [Hincb Hincab]]]]]].
        assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
          by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact Hwf ]).
        assert (HwfP' : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
          by (eapply ad_wf_pskl_strip_mid; [ exact HwfP | exact Hγni ]).
        assert (Hbw : forall (δ : atom) (bb : abind),
                  binds δ bb (Ξ ++ Θ0') ->
                  binds δ bb (Ξ ++ (γ ~ abind_flex_mono) ++ Θ0')).
        { intros δ bb Hb. unfold binds in *.
          apply in_app_or in Hb. apply in_or_app.
          destruct Hb as [Hb | Hb];
            [ left; exact Hb | right; simpl; right; exact Hb ]. }
        assert (Hnf' : a_non_flex (Ξ ++ Θ0') P).
        { destruct Hnf as [Hlc Hnfl]. split; [ exact Hlc | ].
          intro Hfl. apply Hnfl.
          inversion Hfl as [Θf δ Hb | Θf δ τ0 Hb]; subst;
            [ apply a_flex__var; apply Hbw; exact Hb
            | eapply a_flex__var_def; apply Hbw; exact Hb ]. }
        assert (HeqP : msubst_pskl (ρa ++ ρb) P = msubst_pskl ρ P).
        { rewrite Heqρ. apply msubst_pskl_agree. intros X HX.
          symmetry. apply msubst_lookup_mid_drop.
          clear - HX Hγni. intro; subst X; contradiction. }
        assert (Hlkα : msubst_lookup (ρa ++ ρb) α = msubst_lookup ρ α)
          by (rewrite Heqρ; symmetry; apply msubst_lookup_mid_drop; exact Hαγ).
        assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
                  (pskl_to_uskl (msubst_pskl (ρa ++ ρb) P))
                ≈ (pskl_to_bskl_syn (ptyp_to_pskl
                     (msubst_lookup (ρa ++ ρb) α))))
          by (rewrite HeqP, Hlkα; exact Hjoin).
        assert (Hlt : mu_lt (mu_assign Θ (ρa ++ ρb) α P Ξ Θ0')
                            (mu_assign Θ ρ α P Ξ
                                       ((γ ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_assign. apply mu_lt_intro. right. split.
          - unfold V_assign, Vpskl, Vvar. rewrite HeqP, Hlkα. reflexivity.
          - left. simpl. lia. }
        destruct (IH _ Hlt) as [_ [_ HaIH]].
        destruct (HaIH (add γ F) Θ0' Ξ α P (ρa ++ ρb) Θ eq_refl
                       Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hincab Hwfth Hjoin')
          as [Θ1' [Ha' Hopt']].
        exists ((γ ~ abind_flex_mono) ++ Θ1'). split.
        { apply a_assign__skip; [ exact Hαγ | exact Hγni | exact Ha' ]. }
        intros ρ1 Hid Hinc1.
        destruct (a_inc_mid_strip_flex γ Θ0' Hdecl Hinc1)
          as [ρ1a [τ1 [ρ1b [Heqρ1 [Hdρ1a [Hinc1b Hinc1ab]]]]]].
        rewrite Heqρ1 in Hid.
        apply Forall_app in Hid as [Hida Hidtail].
        pose proof (Forall_inv Hidtail) as Heγ1.
        pose proof (Forall_inv_tail Hidtail) as Hidb.
        unfold is_id_entry in Heγ1; simpl in Heγ1; subst τ1.
        assert (Hidab : is_id_msubst (ρ1a ++ ρ1b))
          by (apply Forall_app; split; assumption).
        destruct (a_assign_sound Ha' Hdecl Hwf' HwfP')
          as [[[w [Hidw Hincw]] _] _].
        assert (Hweq : w = ρ1a ++ ρ1b)
          by (eapply is_id_inc_unique;
              [ exact Hincw | exact Hidw | exact Hinc1ab | exact Hidab ]).
        subst w.
        destruct (Hopt' (ρ1a ++ ρ1b) Hidab Hincw) as [ζ' [Hζ' Hie']].
        (* facts about the dropped image τγ *)
        assert (Huqf : uniq (Ξ ++ (γ ~ abind_flex_mono) ++ Θ0'))
          by (apply a_wf_aenv_uniq; exact Hwf).
        assert (Hγρa : γ `notin` dom ρa)
          by (rewrite Hdρa; clear - Huqf; simpl_env in Huqf; solve_uniq).
        assert (Hlkγ : msubst_lookup ρ γ = τγ)
          by (rewrite Heqρ; rewrite msubst_lookup_app_notin by exact Hγρa;
              apply msubst_lookup_cons_eq).
        assert (Hmτγ : mono_ptyp τγ)
          by (rewrite <- Hlkγ; eapply a_inc_lookup_mono; exact Hinc).
        assert (Hbtγ : a_binds_tvar γ (Ξ ++ (γ ~ abind_flex_mono) ++ Θ0'))
          by (right; left; unfold binds; apply in_or_app; right; left;
              reflexivity).
        assert (Hwfτγ : a_wf_ptyp Θ τγ)
          by (rewrite <- Hlkγ;
              eapply a_inc_lookup_wf;
              [ exact Hinc | exact Hwf | exact Hbtγ ]).
        assert (Hγρ1a : γ `notin` dom ρ1a)
          by (rewrite Hdρ1a; clear - Huqf; simpl_env in Huqf; solve_uniq).
        assert (Hγρ1b : γ `notin` dom ρ1b)
          by (pose proof (a_inc_dom_sub Hinc1b) as Hs;
              clear - Hs Hnd; fsetdec).
        exists ((γ, τγ) :: ζ'). split.
        -- apply a_inc__flex; [ exact Hζ' | exact Hwfτγ | exact Hmτγ ].
        -- (* compute ζ ∘ ρ1 = (ζ' ∘ ρ1a) ++ (γ,τγ) :: (ζ' ∘ ρ1b), then
              mid-insert the matching flex pair *)
           assert (Heqc : msubst_compose ((γ, τγ) :: ζ')
                            (ρ1a ++ (γ, ptyp_var_f γ) :: ρ1b)
                        = msubst_compose ζ' ρ1a
                          ++ (γ, τγ) :: msubst_compose ζ' ρ1b).
           { rewrite msubst_compose_app. f_equal.
             - apply (msubst_compose_cons_l_id τγ ζ' Hida Hγρ1a).
             - change (msubst_compose ((γ, τγ) :: ζ')
                         ((γ, ptyp_var_f γ) :: ρ1b))
                 with ((γ, msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                       :: msubst_compose ((γ, τγ) :: ζ') ρ1b).
               rewrite (msubst_compose_cons_l_id τγ ζ' Hidb Hγρ1b).
               change (msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                 with (msubst_lookup ((γ, τγ) :: ζ') γ).
               rewrite msubst_lookup_cons_eq. reflexivity. }
           rewrite Heqρ1, Heqρ, Heqc.
           apply a_inc_equiv_mid_insert_flex;
             [ exact Hdecl
             | apply a_wf_aenv_uniq; exact Hwf'
             | exact Hdρa
             | rewrite dom_msubst_compose; exact Hdρ1a
             | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτγ
             | ].
           rewrite <- msubst_compose_app. exact Hie'.
  - (* head [γ̂ ≔ τdef] DEFINED : Assign-Assign, the back-edge into part 1
       over the merged context Ξ ++ Θ0' with both sides substituted by
       [τdef/γ̂].  The competing solution strips its (γ,τγ)-entry
       ([a_inc_mid_strip_flex_def]); the substituted subject/input images
       are ≡ˢ to the node's ([msubst_pskl_subst] + the pointwise-≡ᵗ
       transport over an artificial source), so the sub-call's join is
       the REFLEXIVITY on the monotype θα̂ and both ∅-refinements follow
       by the mono bridges.  V is exactly constant ([Vpskl_backedge]);
       n drops by one (design doc §5.4, A3). *)
    assert (Huqf : uniq (Ξ ++ (γ ~ abind_flex_mono_def τdef) ++ Θ0'))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfM : a_wf_aenv (Ξ ++ (γ ~ abind_flex_mono_def τdef) ++ Θ0'))
      by exact Hwf.
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
      by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
    assert (Hwf0 : a_wf_aenv Θ0') by (eapply a_wf_aenv_app_r; exact Hwf').
    assert (Hmidwf : a_wf_aenv ((γ ~ abind_flex_mono_def τdef) ++ Θ0'))
      by (eapply a_wf_aenv_app_r; exact HwfM).
    assert (Hwfτd : a_wf_ptyp Θ0' τdef) by (inversion Hmidwf; assumption).
    assert (Hmτd : mono_ptyp τdef) by (inversion Hmidwf; assumption).
    assert (Hγd : γ `notin` dom Θ0') by (inversion Hmidwf; assumption).
    (* strip the defined mid off the competing increment *)
    destruct (a_inc_mid_strip_flex_def γ τdef Θ0' Hdecl Hinc)
      as [ρa [τγ [ρb [Heqρ [Hdρa [Hincb [Hincab [Hwfτγ [Hmτγ Heqτγ]]]]]]]]].
    assert (Hγρa : γ `notin` dom ρa)
      by (rewrite Hdρa; clear - Huqf; simpl_env in Huqf; solve_uniq).
    assert (Hfτd : ftvar_in_ptyp τdef [<=] dom Θ0')
      by (apply a_wf_ptyp_ftv_dom; exact Hwfτd).
    assert (Hγτd : γ `notin` ftvar_in_ptyp τdef)
      by (clear - Hfτd Hγd; fsetdec).
    assert (Hagτd : msubst_ptyp (ρa ++ ρb) τdef = msubst_ptyp ρb τdef).
    { apply msubst_ptyp_agree. intros X HX.
      apply msubst_lookup_app_notin.
      rewrite Hdρa.
      assert (HXd : X `in` dom Θ0') by (clear - Hfτd HX; fsetdec).
      clear - Huqf HXd. simpl_env in Huqf. solve_uniq. }
    assert (Heqτγ' : Θ ⊢ τγ ≡ᵗ (msubst_ptyp (ρa ++ ρb) τdef))
      by (rewrite Hagτd; exact Heqτγ).
    assert (Hlcθ : msubst_lc (ρa ++ ρb))
      by (eapply a_inc_msubst_lc; exact Hincab).
    assert (Hlcm1 : lc_ptyp (msubst_ptyp (ρa ++ ρb) τdef))
      by (apply msubst_ptyp_lc_lc;
          [ exact Hlcθ | eapply a_wf_ptyp_lc; exact Hwfτd ]).
    (* the pointwise-≡ᵗ transport over the artificial source *)
    assert (HwfArt : a_wf_aenv
              ((γ ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0')).
    { apply a_wf_aenv__flex_def.
      - clear - Huqf. simpl_env in Huqf. rewrite dom_app. solve_uniq.
      - eapply a_wf_ptyp_weaken;
          [ intros x b Hb; apply binds_app_3; exact Hb | exact Hwfτd ].
      - exact Hmτd.
      - exact Hwf'. }
    assert (Hlcc1 : msubst_lc
              ((γ, msubst_ptyp (ρa ++ ρb) τdef) :: ρa ++ ρb)).
    { intros X. simpl.
      match goal with |- context [ if ?t then _ else _ ] =>
        destruct t end; [ exact Hlcm1 | apply Hlcθ ]. }
    assert (Hlcc2 : msubst_lc ((γ, τγ) :: ρa ++ ρb)).
    { intros X. simpl.
      match goal with |- context [ if ?t then _ else _ ] =>
        destruct t end;
        [ apply mono_ptyp_lc; exact Hmτγ | apply Hlcθ ]. }
    assert (Hartsub : forall W,
              a_wf_pskl ((γ ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0') W ->
              Θ ⊢ (msubst_pskl
                     ((γ, msubst_ptyp (ρa ++ ρb) τdef) :: ρa ++ ρb) W)
                ≡ˢ (msubst_pskl ((γ, τγ) :: ρa ++ ρb) W)).
    { intros W HwfW.
      eapply a_inc_equiv_msubst_pskl;
        [ exact HwfW | | exact HwfArt | exact Hlcc1 | exact Hlcc2 ].
      apply a_inc_equiv__flex_def.
      - apply a_inc_equiv_refl. exact Hincab.
      - apply a_tyequiv__sym. exact Heqτγ'.
      - apply a_tyequiv__refl. exact Hlcm1. }
    (* the reorder agreement : ρ = (γ,τγ) :: (ρa ++ ρb) pointwise *)
    assert (Hreo : forall (W : pskl),
              msubst_pskl ρ W = msubst_pskl ((γ, τγ) :: ρa ++ ρb) W).
    { intro W. apply msubst_pskl_agree. intros X HX.
      rewrite Heqρ. destruct (X == γ) as [-> | Hne].
      - rewrite msubst_lookup_app_notin by exact Hγρa.
        rewrite msubst_lookup_cons_eq.
        rewrite msubst_lookup_cons_eq. reflexivity.
      - rewrite msubst_lookup_mid_drop by exact Hne.
        rewrite msubst_lookup_cons_neq by exact Hne. reflexivity. }
    (* wf of the substituted pieces at the stripped context *)
    assert (HbγM : binds γ (abind_flex_mono_def τdef)
              (Ξ ++ (γ ~ abind_flex_mono_def τdef) ++ Θ0'))
      by (apply binds_app_3; left; reflexivity).
    assert (Hsubup : forall (W : pskl),
              ftvar_in_pskl
                (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ W)
              [<=] ftvar_in_ptyp τdef `union`
                   remove γ (ftvar_in_pskl W)).
    { intro W.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    W (ptyp_to_pskl τdef) γ) as Hup.
      pose proof (ftvar_in_ptyp_to_pskl τdef) as Hfe.
      clear - Hup Hfe. fsetdec. }
    assert (HwfP0s : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ P)).
    { eapply ad_wf_pskl_strip_mid.
      - eapply ad_wf_pskl_mono_subst;
          [ exact HwfP | exact HwfM | exact HbγM | exact Hmτd ].
      - pose proof (Hsubup P). clear - H Hγτd. fsetdec. }
    assert (HwfSα : (Ξ ++ (γ ~ abind_flex_mono_def τdef) ++ Θ0')
              ⨟ empty ⊢ₚₛᵃ (pskl_var_f α)).
    { apply ad_wf_pskl__var. right.
      destruct Hfα as [Hb | [τ0 Hb]];
        [ right; left | right; right; exists τ0 ];
        unfold binds in *; apply in_or_app; right; exact Hb. }
    assert (HwfSs : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ (pskl_var_f α))).
    { eapply ad_wf_pskl_strip_mid.
      - eapply ad_wf_pskl_mono_subst;
          [ exact HwfSα | exact HwfM | exact HbγM | exact Hmτd ].
      - pose proof (Hsubup (pskl_var_f α)). simpl in H.
        clear - H Hγτd. fsetdec. }
    (* wf of the pieces as a_wf_pskl over the artificial source *)
    assert (HwfPart : a_wf_pskl
              ((γ ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0') P).
    { eapply a_wf_pskl_weaken;
        [ | eapply ad_wf_pskl_to_a_wf_pskl;
            [ exact HwfP | intros x b Hb; exact Hb
            | intros Y HY; exfalso; clear - HY; fsetdec ] ].
      intros x b Hb. unfold binds in *.
      apply in_app_or in Hb. apply in_or_app.
      destruct Hb as [Hb | Hb];
        [ right; apply in_or_app; left; exact Hb | ].
      destruct Hb as [Hb | Hb];
        [ left; left; exact Hb
        | right; apply in_or_app; right; exact Hb ]. }
    assert (HwfVart : a_wf_pskl
              ((γ ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0')
              (pskl_var_f α)).
    { apply a_wf_pskl__var.
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
    assert (HeqP : Θ ⊢ (msubst_pskl (ρa ++ ρb)
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ P))
              ≡ˢ (msubst_pskl ρ P)).
    { rewrite msubst_pskl_subst. rewrite (Hreo P).
      apply Hartsub. exact HwfPart. }
    assert (HeqS : Θ ⊢ (msubst_pskl (ρa ++ ρb)
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ (pskl_var_f α)))
              ≡ˢ (msubst_pskl ρ (pskl_var_f α))).
    { rewrite msubst_pskl_subst. rewrite (Hreo (pskl_var_f α)).
      apply Hartsub. exact HwfVart. }
    (* the sub-call's competing data : the monotype θα̂ *)
    assert (HbtαM : a_binds_tvar α
              (Ξ ++ (γ ~ abind_flex_mono_def τdef) ++ Θ0')).
    { destruct Hfα as [Hb | [τ0 Hb]];
        [ right; left | right; right; exists τ0 ];
        unfold binds in *; apply in_or_app; right; exact Hb. }
    assert (HwfC : a_wf_ptyp Θ (msubst_lookup ρ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact HbtαM ]).
    assert (HmC : mono_ptyp (msubst_lookup ρ α))
      by (eapply a_inc_lookup_mono; exact Hinc).
    assert (HvisC : forall Y, Y `in` ftvar_in_ptyp (msubst_lookup ρ α) ->
              a_binds_tvar Y Θ)
      by (intros Y HY; eapply a_wf_ptyp_ftv_tvarish;
          [ exact HwfC | exact HY ]).
    (* sub-join : reflexivity on θα̂, transported to the subject image *)
    assert (Hjrefl : empty ⨟ Θ ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρ (pskl_var_f α)))
              ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α)))).
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
              (pskl_to_bskl_inh (msubst_pskl (ρa ++ ρb)
                 (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ P)))
              (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α)))).
    { destruct (skl_tyequiv_refine_syn_f_transport HeqP Hwfth
                  (fun x b Hb => Hb)) as [_ Hback].
      apply Hback.
      replace (msubst_pskl ρ P)
        with (uskl_to_pskl (pskl_to_uskl (msubst_pskl ρ P)))
        by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      eapply ad_pat_consis_refine_syn_f_mono;
        [ exact Hjoin | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmC
        | clear; fsetdec
        | intros β τ Hb; clear; fsetdec ]. }
    assert (Hrpsub : ad_refine_pskl_f empty Θ empty
              (msubst_pskl (ρa ++ ρb)
                 (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ (pskl_var_f α)))
              (bskl_to_pskl (pskl_to_bskl_syn
                 (ptyp_to_pskl (msubst_lookup ρ α))))).
    { destruct (skl_tyequiv_refine_pskl_f_transport HeqS Hwfth
                  (fun x b Hb => Hb)) as [_ Hback].
      apply Hback.
      replace (msubst_pskl ρ (pskl_var_f α))
        with (uskl_to_pskl (pskl_to_uskl (msubst_pskl ρ (pskl_var_f α))))
        by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      eapply ad_pat_consis_refine_pskl_f_mono;
        [ exact Hjrefl | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmC
        | clear; fsetdec
        | intros β τ Hb; clear; fsetdec ]. }
    (* the measure : V exactly constant, n drops by one *)
    assert (Hlt : mu_lt
        (mu_consis Θ (ρa ++ ρb)
           (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ P)
           (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ (pskl_var_f α))
           (Ξ ++ Θ0'))
        (mu_assign Θ ρ α P Ξ ((γ, abind_flex_mono_def τdef) :: Θ0'))).
    { unfold mu_consis, mu_assign. apply mu_lt_intro. right. split.
      - unfold V_consis, V_assign.
        erewrite Vpskl_backedge; [ | exact Hwfth | exact Heqτγ' ].
        erewrite Vpskl_backedge; [ | exact Hwfth | exact Heqτγ' ].
        unfold Vpskl, Vvar.
        rewrite <- !Hreo.
        cbn [msubst_pskl].
        rewrite msubst_pskl_ptyp_to_pskl.
        rewrite size_ptyp_to_pskl. lia.
      - left. rewrite length_app. simpl. lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH (add γ F) empty empty (Ξ ++ Θ0')
                (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ P)
                (subst_pskl_in_pskl (ptyp_to_pskl τdef) γ (pskl_var_f α))
                (ρa ++ ρb) Θ empty
                (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α)))
                eq_refl Hwf' HwfP0s HwfSs
                ltac:(intros X HX; exfalso; clear - HX; fsetdec)
                ltac:(intros β τ Hb; clear; fsetdec)
                ltac:(intros Θa β b Θb Heqx Hne; clear; fsetdec)
                Hincab Hwfth
                ltac:(intros β τ Hb; clear; fsetdec)
                ltac:(reflexivity)
                Hjsub Hrssub Hrpsub)
      as [Q' [Θ1' [Hc Hopt']]].
    exists ((γ ~ abind_flex_mono_def τdef) ++ Θ1'). split.
    { eapply a_assign__assign; [ exact Hfα | exact Hc ]. }
    (* ---- optimality ---- *)
    intros ρ1 Hid Hinc1.
    destruct (a_inc_mid_strip_flex_def γ τdef Θ0' Hdecl Hinc1)
      as [ρ1a [τ1γ [ρ1b [Heqρ1 [Hdρ1a [Hinc1b [Hinc1ab _]]]]]]].
    rewrite Heqρ1 in Hid.
    apply Forall_app in Hid as [Hida Hidtail].
    pose proof (Forall_inv Hidtail) as Heγ1.
    pose proof (Forall_inv_tail Hidtail) as Hidb.
    unfold is_id_entry in Heγ1; simpl in Heγ1; subst τ1γ.
    assert (Hidab : is_id_msubst (ρ1a ++ ρ1b))
      by (apply Forall_app; split; assumption).
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ _
                Hc Hwf' HwfP0s HwfSs
                ltac:(intros X HX; exfalso; clear - HX; fsetdec)
                ltac:(intros β τ Hb; clear; fsetdec)
                ltac:(intros Θa β b Θb Heqx Hne; clear; fsetdec))
      as [Hle1 [HwfΘ1' _]].
    destruct Hle1 as [[w [Hidw Hincw]] _].
    assert (Hweq : w = ρ1a ++ ρ1b)
      by (eapply is_id_inc_unique;
          [ exact Hincw | exact Hidw | exact Hinc1ab | exact Hidab ]).
    subst w.
    destruct (Hopt' (ρ1a ++ ρ1b) Hidab Hincw)
      as [ζ' [Hζ' [Hie' Hprec']]].
    (* the final ζ re-conses the dropped (γ, τγ) entry *)
    assert (Hγρ1a : γ `notin` dom ρ1a)
      by (rewrite Hdρ1a; clear - Huqf; simpl_env in Huqf; solve_uniq).
    assert (Hγρ1b : γ `notin` dom ρ1b)
      by (pose proof (a_inc_dom_sub Hinc1b) as Hs; clear - Hs Hγd; fsetdec).
    (* τγ ≡ᵗ msubst ζ' τdef *)
    assert (Hwfτd' : a_wf_ptyp (Ξ ++ Θ0') τdef)
      by (eapply a_wf_ptyp_weaken;
          [ intros x b Hb; apply binds_app_3; exact Hb | exact Hwfτd ]).
    assert (Hlc2' : msubst_lc (msubst_compose ζ' (ρ1a ++ ρ1b))).
    { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ' | ].
      intros a t Hin. eapply is_id_msubst_values_lc;
        [ exact Hidab | exact Hin ]. }
    assert (Heqζτd : Θ ⊢ (msubst_ptyp (ρa ++ ρb) τdef)
                       ≡ᵗ (msubst_ptyp ζ' τdef)).
    { pose proof (a_inc_equiv_msubst_ptyp Hwfτd' Hie' Hwf' Hlcθ Hlc2')
        as Hmid.
      rewrite (msubst_compose_id_ptyp Hwf' HwfΘ1' Hidab Hincw Hζ'
                 Hwfτd') in Hmid.
      exact Hmid. }
    exists ((γ, τγ) :: ζ'). split.
    + apply a_inc__flex_def;
        [ exact Hζ' | exact Hwfτγ | exact Hmτγ | ].
      eapply a_tyequiv__trans; [ exact Heqτγ' | exact Heqζτd ].
    + (* factoring : mid-insert the matching defined pair *)
      assert (Heqc : msubst_compose ((γ, τγ) :: ζ')
                       (ρ1a ++ (γ, ptyp_var_f γ) :: ρ1b)
                   = msubst_compose ζ' ρ1a
                     ++ (γ, τγ) :: msubst_compose ζ' ρ1b).
      { rewrite msubst_compose_app. f_equal.
        - apply (msubst_compose_cons_l_id τγ ζ' Hida Hγρ1a).
        - change (msubst_compose ((γ, τγ) :: ζ')
                    ((γ, ptyp_var_f γ) :: ρ1b))
            with ((γ, msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                  :: msubst_compose ((γ, τγ) :: ζ') ρ1b).
          rewrite (msubst_compose_cons_l_id τγ ζ' Hidb Hγρ1b).
          change (msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
            with (msubst_lookup ((γ, τγ) :: ζ') γ).
          rewrite msubst_lookup_cons_eq. reflexivity. }
      rewrite Heqρ1, Heqρ, Heqc.
      apply a_inc_equiv_mid_insert_flex_def;
        [ exact Hdecl
        | apply a_wf_aenv_uniq; exact Hwf'
        | exact Hdρa
        | rewrite dom_msubst_compose; exact Hdρ1a
        | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτγ
        | exact Heqτγ
        | ].
      rewrite <- msubst_compose_app. exact Hie'.
Qed.

(** Part 1 of the paper's proof (:2561-3167): consistency.  The special
    cases are peeled first (:2566-2580) — [P] or [P0] flexible → parts 2/3
    ([t] breaks the tie); [P0 = ◇] → GhostR (axiom); [P0 = ⊤◇.P0'] with [P]
    guarded → UnivGhostR ([V] decreases on the input side) — and the main
    dispatch is on the last rule of the declarative join derivation, each
    structural sub-node at strictly smaller [V]. *)
(** Decidability of "is a hatted variable of Θ" (the layer-0 dispatch). *)
Lemma a_flex_tvar_dec : forall Θ (δ : atom),
  a_flex_tvar Θ δ \/ ~ a_flex_tvar Θ δ.
Proof.
  induction Θ as [ | [x b] Θ' IHΘ ]; intros δ.
  - right. intros [Hb | [τ Hb]]; inversion Hb.
  - destruct (IHΘ δ) as [Hyes | Hno].
    { left. destruct Hyes as [Hb | [τ Hb]];
        [ left | right; exists τ ]; unfold binds in *; simpl; right; exact Hb. }
    destruct b as [ | A | Q | | τd ];
      try (destruct (δ == x) as [-> | Hne];
           [ | right; intros [Hb | [τ Hb]];
               apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
               solve [ exfalso; auto | discriminate Hbe
                     | apply Hno; solve [ left; exact Hb
                                        | right; exists τ; exact Hb ] ] ]).
    + (* x ~ tvar, δ = x *)
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    + (* x ~ var_typ, δ = x *)
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    + (* x ~ var_skl, δ = x *)
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    + (* x ~ flex, δ = x *)
      left. left. left. reflexivity.
    + (* x ~ flex_def τd, δ = x *)
      left. right. exists τd. left. reflexivity.
Qed.

(** Layer-0 shape dispatch: a well-formed skeleton is a hatted variable of
    [Θ] or non-flex. *)
Lemma a_flex_shape_dec : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  (exists β, P = pskl_var_f β /\ a_flex_tvar Θ β) \/ a_non_flex Θ P.
Proof.
  intros Θ Δ P HwfP.
  pose proof (ad_wf_pskl_lc HwfP) as Hlc.
  destruct P as [ | n | δ | Pa Pb | Pb | | Pt ];
    try (right; split; [ exact Hlc | intro Hfl; solve [ inversion Hfl ] ]).
  destruct (a_flex_tvar_dec Θ δ) as [Hf | Hnf'].
  - left. exists δ. split; [ reflexivity | exact Hf ].
  - right. split; [ exact Hlc | ].
    intro Hfl. apply Hnf'.
    inversion Hfl; subst; [ left | right; eexists ]; eassumption.
Qed.

(** Part 1's MAIN DISPATCH (paper :2582-3167), by induction on the last rule
    of the declarative join derivation, ASSUMING the layer-0 special cases
    (flexible subject / flexible input / P0 = ◇ / P0 = ⊤◇ with P guarded)
    have been peeled by [consis_complete_step] below.  The induction (rather
    than a case analysis) is needed ONLY for the target-side definition
    unfolds [flex_r] — those keep the measure constant but shrink the join.
    All structural sub-nodes recurse through the measure hypothesis [IH]. *)
Lemma consis_complete_core : forall Ψ Θ S Qb,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qb ->
  forall F Δ1 Δ2 Θ0 P0 P ρ,
    (forall m', mu_lt m' (mu_consis Θ ρ P0 P Θ0) -> complete_at m') ->
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (forall X, X `in` (Δ1 `union` Δ2) -> binds X abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    S = pskl_to_uskl (msubst_pskl ρ P) ->
    a_non_flex Θ0 P ->
    a_non_flex Θ0 P0 ->
    P0 <> pskl_hole ->
    (forall P0', P0 = pskl_tophole P0' -> ~ guarded_pskl P) ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis F Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           ad_precise_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb)).
Proof.
  intros Ψ Θ S Qb Hj.
  induction Hj; intros F Δ1 Δ2 Θ0 PP0 PP ρ
    IH Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth
    HΨ HeqS HnfP HnfP0 HneP0hole Hnthg Hrs Hrp.
  (* ------------------------------------------------------------- unit *)
  - (* SUBJECT: PP = unit (var subjects are rigid, hence not unit). *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    2:{ (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    (* INPUT: PP0 = unit. *)
    destruct PP0 as [ | n0 | δ0 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    2:{ inversion Hrs. }
    2:{ (* var δ0 : rigid; a rigid variable does not refine to unit *)
      exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
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
    intros ρ1 Hid Hinc1. exists ρ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    cbn [pskl_to_bskl_syn msubst_bskl bskl_to_pskl].
    unfold ad_precise_f.
    apply ad_refine_syn_f_of_plain_no_hole; [ | simpl; exact I ].
    apply consis_precise_mono_join with (A := ptyp_unit) (Qb := bskl_unit);
      [ exact Hwfth | apply mono_ptyp__unit
      | intros X HX; simpl in HX; clear - HX; fsetdec
      | apply ad_pat_consis__unit; clear; fsetdec ].
  (* -------------------------------------------------------------- var *)
  - (* SUBJECT: PP = var δ with δ RIGID; forces X = δ, PP0 = var δ. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    assert (Hbtδ : binds δ abind_tvar Θ0).
    { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
      destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
        [ exfalso; clear - HΔ; fsetdec
        | exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          apply a_flex__var; exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          eapply a_flex__var_def; exact Hb ]. }
    assert (Hδρ : δ `notin` dom ρ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
    simpl in HeqS. inversion HeqS; subst X. clear HeqS.
    assert (HbtΘ : binds δ abind_tvar Θ)
      by (eapply a_inc_binds_tvar; eauto).
    (* INPUT: PP0 = var δ. *)
    destruct PP0 as [ | n0 | δ0 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso.
        inversion Hrs; subst.
        match goal with
        | Hbr : binds δ (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    1:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds δ (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds δ (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds δ (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ exfalso; apply (Hnthg Pt0 eq_refl); apply guarded_pskl__var. }
    (* var δ0 rigid; the refinement forces δ0 = δ *)
    assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
    { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
      destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
        [ exfalso; clear - HΔ; fsetdec
        | exact Hb
        | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
          apply a_flex__var; exact Hb
        | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
          eapply a_flex__var_def; exact Hb ]. }
    assert (Hδρ0 : δ0 `notin` dom ρ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
    simpl in Hrs.
    assert (Heqδ : δ0 = δ).
    { inversion Hrs; subst.
      - reflexivity.
      - exfalso.
        match goal with
        | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
            assert (HbtΘ0' : binds δ0 abind_tvar Θ)
              by (eapply a_inc_binds_tvar; eauto);
            pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                          (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
        end.
      - exfalso.
        match goal with
        | Hbr : binds δ (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr
                          (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
        end. }
    subst δ0.
    exists (pskl_var_f δ), Θ0. split.
    { apply a_consis__rigid. exact Hbtδ. }
    intros ρ1 Hid Hinc1. exists ρ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    unfold ad_precise_f.
    cbn [pskl_to_bskl_syn msubst_bskl].
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    rewrite (msubst_lookup_notin ρ Hδρ).
    apply ad_refine_syn_f_of_plain_no_hole;
      [ | apply pskl_to_bskl_inh_no_hole, ptyp_to_pskl_no_hole ].
    apply consis_precise_mono_join with (A := ptyp_var_f δ)
                                        (Qb := bskl_var_f δ);
      [ exact Hwfth | apply mono_ptyp__var
      | intros X HX; simpl in HX;
        assert (HXδ : X = δ) by (clear - HX; fsetdec); subst X;
        left; exact HbtΘ
      | apply ad_pat_consis__var; [ clear; fsetdec | left; exact HbtΘ ] ].
  (* ------------------------------------------------------------ arrow *)
  - (* C-Arrow (paper :2691-2775): two structural sub-nodes at strictly
       smaller V.  The second runs at the first's OUTPUT Θ1 with metasubst
       ζ1 (the first's factoring at the soundness ⊴ id-witness); its
       premises transport from ρ to ζ1 by the ≡ˢ-transport layer; the two
       factorings compose by [a_inc_equiv_glue]; the first component's
       precision transports from ζ1 to ζ2 the same way. *)
    match goal with
    | Hpm : ?x ⨟ _ ⊨ₛᵃ R1 ≈ _ |- _ => rename Hpm into Hj1
    end.
    match goal with
    | Hpm : ?x ⨟ _ ⊨ₛᵃ R2 ≈ _ |- _ => rename Hpm into Hj2
    end.
    match goal with
    | Hpe : Ψ [=] union _ _ |- _ => rename Hpe into HΨu
    end.
    assert (HΨ1e : Ψ1 [=] empty) by (clear - HΨ HΨu; fsetdec).
    assert (HΨ2e : Ψ2 [=] empty) by (clear - HΨ HΨu; fsetdec).
    (* SUBJECT: PP = arrow PPa PPb. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R1 R2. clear HeqS.
    assert (HwfPPa : Θ0 ⨟ empty ⊢ₚₛᵃ PPa) by (inversion HwfP; assumption).
    assert (HwfPPb : Θ0 ⨟ empty ⊢ₚₛᵃ PPb) by (inversion HwfP; assumption).
    assert (HlcP : lc_pskl (pskl_arrow PPa PPb))
      by (eapply ad_wf_pskl_lc; exact HwfP).
    (* INPUT: PP0 = arrow P0a P0b. *)
    destruct PP0 as [ | n0 | δ0 | P0a P0b | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ (* var δ0 : rigid; a rigid variable does not refine to an arrow *)
      exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr (a_wf_aenv_uniq Hwfth))
            as Hcon; discriminate
      end. }
    2:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ (* ⊤◇ input against a GUARDED (arrow) subject was peeled in layer 0d *)
      exfalso. apply (Hnthg Pt0 eq_refl).
      inversion HlcP; subst.
      apply guarded_pskl__arrow; assumption. }
    (* both arrows: invert the two refinements *)
    assert (HwfP0a : Θ0 ⨟ empty ⊢ₚₛᵃ P0a) by (inversion HwfP0; assumption).
    assert (HwfP0b : Θ0 ⨟ empty ⊢ₚₛᵃ P0b) by (inversion HwfP0; assumption).
    inversion Hrs; subst.
    match goal with
    | Ha : ad_refine_syn_f Δ1 Θ Δ1
             (pskl_to_bskl_inh (msubst_pskl ρ P0a)) Q1,
      Hb : ad_refine_syn_f Δ1 Θ Δ1
             (pskl_to_bskl_inh (msubst_pskl ρ P0b)) Q2 |- _ =>
        rename Ha into Hrs1; rename Hb into Hrs2
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_arrow (msubst_pskl ρ PPa) (msubst_pskl ρ PPb))
              (pskl_arrow (bskl_to_pskl Q1) (bskl_to_pskl Q2))) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Ha : ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ PPa) (bskl_to_pskl Q1),
      Hb : ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ PPb) (bskl_to_pskl Q2)
      |- _ =>
        rename Ha into Hrp1; rename Hb into Hrp2
    end.
    (* ---- first component, at (Θ0, ρ); V strictly drops ---- *)
    assert (Hlt1 : mu_lt (mu_consis Θ ρ P0a PPa Θ0)
                         (mu_consis Θ ρ (pskl_arrow P0a P0b)
                                        (pskl_arrow PPa PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      pose proof (Vpskl_arrow_lt1 Θ ρ PPa PPb).
      pose proof (Vpskl_arrow_lt1 Θ ρ P0a P0b). lia. }
    destruct (IH _ Hlt1) as [HcIH1 _].
    destruct (HcIH1 F Δ1 Δ2 Θ0 P0a PPa ρ Θ Ψ1 Q1 eq_refl Hwf0 HwfP0a HwfPPa
                    Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ1e Hj1 Hrs1 Hrp1)
      as [PA1 [Θ1 [Hc1 Hopt1]]].
    (* the first node's soundness: id-witness, wf, Δ-invariants *)
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ _ Hc1
                Hwf0 HwfP0a HwfPPa Hrig Hnfd0 Hfaf)
      as [Hle1 [Hwf1 [Hdom1 [Hfr1 [Hinv1 [Hsol1 _]]]]]].
    destruct Hle1 as [[w1 [Hidw1 Hincw1]] Hdefs1].
    destruct (Hopt1 w1 Hidw1 Hincw1) as [ζ1 [Hζ1 [Hie1 Hprec1]]].
    assert (HΔdom : (Δ1 `union` Δ2) [<=] (F `union` dom Θ0)).
    { intros X HX. pose proof (Hrig X HX) as Hb.
      apply binds_In in Hb. clear - Hb. fsetdec. }
    destruct (Hinv1 (Δ1 `union` Δ2) Hnfd0 Hfaf HΔdom
                ltac:(intros X HX HnX; exfalso; pose proof (Hrig X HX) as Hb;
                      apply binds_In in Hb; exact (HnX Hb)))
      as [Hnfd1 [Hfaf1 _]].
    assert (HrigΘ1 : forall X, X `in` (Δ1 `union` Δ2) ->
              binds X abind_tvar Θ1)
      by (intros X HX; eapply a_inc_binds_tvar;
          [ exact Hincw1 | apply Hrig; exact HX ]).
    assert (HwfP0b1 : Θ1 ⨟ empty ⊢ₚₛᵃ P0b).
    { eapply ad_wf_pskl_isub; [ exact HwfP0b | ].
      split; [ exists w1; split; assumption | exact Hdefs1 ]. }
    assert (HwfPPb1 : Θ1 ⨟ empty ⊢ₚₛᵃ PPb).
    { eapply ad_wf_pskl_isub; [ exact HwfPPb | ].
      split; [ exists w1; split; assumption | exact Hdefs1 ]. }
    (* ---- transport the second component's premises from ρ to ζ1 ---- *)
    assert (HawfPPb : a_wf_pskl Θ0 PPb).
    { eapply ad_wf_pskl_to_a_wf_pskl;
        [ exact HwfPPb | intros x b Hb; exact Hb
        | intros Y HY; exfalso; clear - HY; fsetdec ]. }
    assert (HawfP0b : a_wf_pskl Θ0 P0b).
    { eapply ad_wf_pskl_to_a_wf_pskl;
        [ exact HwfP0b | intros x b Hb; exact Hb
        | intros Y HY; exfalso; clear - HY; fsetdec ]. }
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hlcζ1 : msubst_lc ζ1) by (eapply a_inc_msubst_lc; exact Hζ1).
    assert (Hlcc1 : msubst_lc (msubst_compose ζ1 w1))
      by (apply msubst_lc_compose;
          [ exact Hlcζ1 | eapply is_id_msubst_values_lc; exact Hidw1 ]).
    assert (Heqb : Θ ⊢ (msubst_pskl ρ PPb) ≡ˢ (msubst_pskl ζ1 PPb)).
    { replace (msubst_pskl ζ1 PPb)
        with (msubst_pskl (msubst_compose ζ1 w1) PPb)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf0 | exact Hwf1 | exact Hidw1 | exact Hincw1
            | exact Hζ1 | exact HawfPPb ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfPPb | exact Hie1 | exact Hwf0
        | exact Hlcρ | exact Hlcc1 ]. }
    assert (Heqb0 : Θ ⊢ (msubst_pskl ρ P0b) ≡ˢ (msubst_pskl ζ1 P0b)).
    { replace (msubst_pskl ζ1 P0b)
        with (msubst_pskl (msubst_compose ζ1 w1) P0b)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf0 | exact Hwf1 | exact Hidw1 | exact Hincw1
            | exact Hζ1 | exact HawfP0b ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfP0b | exact Hie1 | exact Hwf0
        | exact Hlcρ | exact Hlcc1 ]. }
    destruct (skl_tyequiv_consis_transport Heqb Hwfth
                (fun x b Hb => Hb)) as [Hjt _].
    assert (Hj2' : Ψ2 ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ζ1 PPb)) ≈ Q2)
      by (apply Hjt; exact Hj2).
    destruct (skl_tyequiv_refine_syn_f_transport Heqb0 Hwfth
                (fun x b Hb => Hb)) as [Hrst _].
    pose proof (Hrst _ _ _ Hrs2) as Hrs2'.
    destruct (skl_tyequiv_refine_pskl_f_transport Heqb Hwfth
                (fun x b Hb => Hb)) as [Hrpt _].
    pose proof (Hrpt _ _ _ Hrp2) as Hrp2'.
    (* ---- second component, at (Θ1, ζ1); V constant by M1 then drops --- *)
    assert (HVb : Vpskl Θ ζ1 PPb = Vpskl Θ ρ PPb).
    { transitivity (Vpskl Θ (msubst_compose ζ1 w1) PPb).
      - unfold Vpskl.
        erewrite (msubst_compose_id_pskl (P := PPb));
          [ reflexivity | exact Hwf0 | exact Hwf1 | exact Hidw1
          | exact Hincw1 | exact Hζ1 | exact HawfPPb ].
      - symmetry.
        eapply Vpskl_inc_equiv;
          [ exact Hie1 | exact Hwf0 | exact Hwfth | exact HawfPPb ]. }
    assert (HVb0 : Vpskl Θ ζ1 P0b = Vpskl Θ ρ P0b).
    { transitivity (Vpskl Θ (msubst_compose ζ1 w1) P0b).
      - unfold Vpskl.
        erewrite (msubst_compose_id_pskl (P := P0b));
          [ reflexivity | exact Hwf0 | exact Hwf1 | exact Hidw1
          | exact Hincw1 | exact Hζ1 | exact HawfP0b ].
      - symmetry.
        eapply Vpskl_inc_equiv;
          [ exact Hie1 | exact Hwf0 | exact Hwfth | exact HawfP0b ]. }
    assert (Hlt2 : mu_lt (mu_consis Θ ζ1 P0b PPb Θ1)
                         (mu_consis Θ ρ (pskl_arrow P0a P0b)
                                        (pskl_arrow PPa PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite HVb. rewrite HVb0.
      pose proof (Vpskl_arrow_lt2 Θ ρ PPa PPb).
      pose proof (Vpskl_arrow_lt2 Θ ρ P0a P0b). lia. }
    destruct (IH _ Hlt2) as [HcIH2 _].
    destruct (HcIH2 F Δ1 Δ2 Θ1 P0b PPb ζ1 Θ Ψ2 Q2 eq_refl Hwf1 HwfP0b1
                    HwfPPb1 HrigΘ1 Hnfd1 Hfaf1 Hζ1 Hwfth Hnfdth HΨ2e
                    Hj2' Hrs2' Hrp2')
      as [PA2 [Θ2 [Hc2 Hopt2]]].
    (* ---- assemble the node ---- *)
    exists (pskl_arrow PA1 PA2), Θ2. split.
    { eapply a_consis__arrow; [ exact Hc1 | exact Hc2 ]. }
    intros ρf Hidf Hincf.
    (* the second node's soundness id-witness *)
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ _ Hc2
                Hwf1 HwfP0b1 HwfPPb1 HrigΘ1 Hnfd1 Hfaf1)
      as [Hle2 [Hwf2 [Hdom2 [Hfr2 [Hinv2 [Hsol2 _]]]]]].
    destruct Hle2 as [[w2 [Hidw2 Hincw2]] Hdefs2].
    destruct (Hopt2 w2 Hidw2 Hincw2) as [ζ2 [Hζ2 [Hie2 Hprec2]]].
    (* the algorithm's composite id-witness IS w1 (uniqueness) *)
    assert (Heqw : w1 = ρf) by (eapply is_id_inc_unique; eauto).
    subst ρf.
    exists ζ2. split; [ exact Hζ2 | ]. split.
    { (* factoring composition *)
      eapply a_inc_equiv_glue with
        (Θmid := Θ1) (Θfin := Θ2) (ρ1b := w2) (ζ1 := ζ1);
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
    assert (HawfPA1 : a_wf_pskl Θ1 PA1).
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
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* --------------------------------------------- forall_inh_untagged *)
  - (* C-ForallInh (paper :2777-2851): open with a fresh rigid α added to
       Θ0, Δ1, Δ2; the recursive call goes through the μ-IH at strictly
       smaller V ([Vpskl_open] + the binder strip); L8 shapes its output
       as [(α~tvar) ++ Θ1] and L9 renames the single instance to the
       cofinite premise of [a_consis__forall_inh]. *)
    match goal with
    | Hpm : forall X, X `notin` _ -> _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ =>
        rename Hpm into Hjoin
    end.
    (* SUBJECT: PP = ∀ PPb. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.
    (* INPUT: PP0 = ∀ P0b. *)
    destruct PP0 as [ | n0 | δ0 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ (* rigid input var never refines to an inherited ∀ *)
      exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                        (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ (* ⊤◇ input: its guarded body never refines to an inherited ∀ *)
      exfalso.
      assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
      assert (Hgρ0 : guarded_pskl (msubst_pskl ρ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      inversion Hrs; subst.
      eapply ad_refine_syn_f_guarded_src_all_inh_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgρ0 ]. }
    (* both ∀ : invert the two refinements and the wf of the bodies *)
    inversion Hrs; subst.
    match goal with
    | Hn : forall X, X `notin` ?LA ->
             ad_refine_syn_f _ _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_all_syn (msubst_pskl ρ PPb))
              (pskl_all_syn (bskl_to_pskl Q))) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Hn : forall X, X `notin` ?LB ->
             ad_refine_pskl_f _ _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb0 : exists Lw0, forall X, X `notin` Lw0 ->
              Θ0 ⨟ (add X empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl P0b (pskl_var_f X))).
    { inversion HwfP0; subst. eexists. eassumption. }
    destruct Hwfb0 as [Lw0 Hwfb0].
    assert (Hwfb : exists Lw, forall X, X `notin` Lw ->
              Θ0 ⨟ (add X empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl PPb (pskl_var_f X))).
    { inversion HwfP; subst. eexists. eassumption. }
    destruct Hwfb as [Lw Hwfb].
    (* the fresh rigid α *)
    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw0 `union` Lw
                        `union` dom Θ0 `union` dom Θ `union` dom ρ
                        `union` F `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPb
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hαρ : α `notin` dom ρ) by (clear - Fr; fsetdec).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; fsetdec).
    (* the measure strictly drops *)
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) ρ Pz
                            = Vpskl Θ ρ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) ρ
           (open_pskl_wrt_pskl P0b (pskl_var_f α))
           (open_pskl_wrt_pskl PPb (pskl_var_f α))
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ ρ (pskl_all_syn P0b) (pskl_all_syn PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open P0b Hwfth Hlcρ Hαρ HαΘ).
      rewrite (Vpskl_open PPb Hwfth Hlcρ Hαρ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ ρ P0b).
      pose proof (Vpskl_all_syn_lt Θ ρ PPb). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    (* premises of the opened problem *)
    assert (Hwf0' : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ]).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (open_pskl_wrt_pskl P0b (pskl_var_f α))).
    { eapply ad_wf_pskl_delta_to_tvar;
        [ apply Hwfb0; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl PPb (pskl_var_f α))).
    { eapply ad_wf_pskl_delta_to_tvar;
        [ apply Hwfb; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (Hrig' : forall Z, Z `in` (add α Δ1 `union` add α Δ2) ->
              binds Z abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros Z HZ. destruct (Z == α) as [-> | Hne];
        [ unfold binds; left; reflexivity
        | apply binds_cons_3; apply Hrig; clear - HZ Hne; fsetdec ]. }
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
    assert (Hinc' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ ]
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
    assert (Hjα : Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρ
                 (open_pskl_wrt_pskl PPb (pskl_var_f α))))
              ≈ (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { pose proof (Hjoin α ltac:(clear - Fr; fsetdec)) as Hj0.
      rewrite (msubst_pskl_open_lc PPb Hlcρ Hαρ).
      rewrite pskl_to_uskl_open_var.
      exact Hj0. }
    assert (Hrsα : ad_refine_syn_f (add α Δ1) ((α ~ abind_tvar) ++ Θ)
              (add α Δ1)
              (pskl_to_bskl_inh (msubst_pskl ρ
                 (open_pskl_wrt_pskl P0b (pskl_var_f α))))
              (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { rewrite (msubst_pskl_open_lc P0b Hlcρ Hαρ).
      rewrite pskl_to_bskl_inh_open.
      eapply ad_refine_syn_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_syn_f_fextend_dom;
        [ apply Hrs1; clear - Fr; fsetdec | ].
      intros γ Hγ. destruct (γ == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hγ Hne; fsetdec ]. }
    assert (Hrpα : ad_refine_pskl_f (add α Δ2) ((α ~ abind_tvar) ++ Θ)
              (add α Δ2)
              (msubst_pskl ρ (open_pskl_wrt_pskl PPb (pskl_var_f α)))
              (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)))).
    { rewrite (msubst_pskl_open_lc PPb Hlcρ Hαρ).
      rewrite bskl_to_pskl_open.
      eapply ad_refine_pskl_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_pskl_f_fextend_dom;
        [ apply Hrp1; clear - Fr; fsetdec | ].
      intros γ Hγ. destruct (γ == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hγ Hne; fsetdec ]. }
    destruct (HcIH F (add α Δ1) (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
                (open_pskl_wrt_pskl P0b (pskl_var_f α))
                (open_pskl_wrt_pskl PPb (pskl_var_f α)) ρ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα)
      as [P1 [Θ1' [Hc Hopt']]].
    (* L8 : the output re-attaches the rigid head *)
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _
                _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.
    (* assemble the cofinite node by renaming the α-instance (L9) *)
    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; fsetdec).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    { apply a_consis__forall_inh with
        (L := L `union` dom Θ0 `union` dom Θ1 `union` dom Θ
              `union` singleton α `union` F `union` Δ1 `union` Δ2
              `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPb
              `union` ftvar_in_pskl P1).
      intros X HX.
      assert (HXα : X <> α) by (clear - HX; fsetdec).
      assert (HXΘ0 : X `notin` dom Θ0) by (clear - HX; fsetdec).
      assert (HXΘ1 : X `notin` dom Θ1) by (clear - HX; fsetdec).
      assert (HXΔ1 : X `notin` Δ1) by (clear - HX; fsetdec).
      assert (HXΔ2 : X `notin` Δ2) by (clear - HX; fsetdec).
      assert (HXP0b : X `notin` ftvar_in_pskl P0b)
        by (clear - HX; fsetdec).
      assert (HXPPb : X `notin` ftvar_in_pskl PPb)
        by (clear - HX; fsetdec).
      assert (HXP1 : X `notin` ftvar_in_pskl P1)
        by (clear - HX; fsetdec).
      destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α X))
                  _ _ _ _ _ _ _ _ Hc nil Θ0 eq_refl tvar_prefix_nil
                  Huq0
                  ltac:(simpl; clear - HXΘ0 HXα; fsetdec)
                  ltac:(simpl; clear - HXΘ1 HXα; fsetdec)
                  ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          P0b (pskl_var_f α)) as Hup;
                        simpl in Hup;
                        clear - HXα HXP0b Hup; fsetdec)
                  ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          PPb (pskl_var_f α)) as Hup;
                        simpl in Hup;
                        clear - HXα HXPPb Hup; fsetdec)
                  ltac:(clear - HXP1; fsetdec)
                  ltac:(clear - HXα HXΔ1; fsetdec)
                  ltac:(clear - HXα HXΔ2; fsetdec))
        as [Θt [HeqΘt Hren]].
      simpl in HeqΘt. inversion HeqΘt. subst Θt.
      assert (Ho0 : open_pskl_wrt_pskl P0b (pskl_var_f X)
                  = subst_pskl_in_pskl (pskl_var_f X) α
                      (open_pskl_wrt_pskl P0b (pskl_var_f α)))
        by (apply subst_pskl_in_pskl_intro; clear - Fr; fsetdec).
      assert (Ho1 : open_pskl_wrt_pskl PPb (pskl_var_f X)
                  = subst_pskl_in_pskl (pskl_var_f X) α
                      (open_pskl_wrt_pskl PPb (pskl_var_f α)))
        by (apply subst_pskl_in_pskl_intro; clear - Fr; fsetdec).
      rewrite <- Ho0, <- Ho1 in Hren.
      rewrite (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α) in Hren.
      eapply (proj2 (proj2 a_assign_unify_consis_compat));
        [ exact Hren
        | intros γ Hγ; left; exact Hγ
        | apply rn_set_add_same; exact HαΔ1
        | apply rn_set_add_same; exact HαΔ2 ].
    }
    (* optimality *)
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ1 ]
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc1).
      apply a_decls_suffix. apply a_decls__nil. }
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ [Hζ [Hie Hprec]]].
    exists ζ.
    (* strip the rigid head off the algorithm-side increments *)
    assert (Hζ' : Θ1 ≤[ ζ ] Θ).
    { destruct (a_inc_tvar_inv Hζ) as [Ξs [Θ2 [HeqT [Hsuf Hinc2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hinc2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    assert (Hie' : a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ).
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
      by (destruct (auc_uniq_consis Hc Huq0) as [Hu1 _]; exact Hu1).
    assert (HαΘ1 : α `notin` dom Θ1) by solve_uniq.
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Himg : forall γ τ, In (γ, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros γ τ Hin.
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
    intros X HX.
    assert (HXζ : X `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HX; fsetdec. }
    rewrite <- !pskl_to_bskl_inh_open.
    rewrite <- (msubst_pskl_open_lc (close_pskl_wrt_pskl α P1) Hlcζ HXζ).
    rewrite <- (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α).
    rewrite <- bskl_to_pskl_open.
    (* transport the α-instance: ctx-α to Δ, then rename α ↦ X *)
    pose proof (ad_refine_syn_f_ctx_to_delta Hprec nil Θ eq_refl
                  ltac:(clear; fsetdec)
                  (a_wf_aenv_uniq Hwfth')) as Hp1.
    simpl in Hp1.
    assert (HαF : α `in` (add α Δ1 `union` add α Δ2))
      by (clear; fsetdec).
    assert (Hdefsθ : forall β τ,
              binds β (abind_flex_mono_def τ) Θ ->
              α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; eassumption).
      clear - Hsc HαΘ. fsetdec. }
    pose proof (ad_refine_syn_f_rename X Hp1 HαF HαΘ Hdefsθ) as Hp2.
    rewrite !pskl_to_bskl_inh_subst_var in Hp2.
    rewrite (msubst_pskl_subst_var ζ P1 Hαζ HXζ Himg) in Hp2.
    rewrite bskl_to_pskl_subst_var in Hp2.
    assert (HoQ : open_bskl_wrt_bskl Q (bskl_var_f X)
                = subst_bskl_in_bskl (bskl_var_f X) α
                    (open_bskl_wrt_bskl Q (bskl_var_f α)))
      by (apply subst_bskl_in_bskl_intro; clear - Fr; fsetdec).
    rewrite <- HoQ in Hp2.
    eapply ad_refine_syn_f_fmono;
      [ | eapply ad_refine_syn_f_delta_mono; [ exact Hp2 | ] ].
    { clear - HαΔ1 HαΔ2. fsetdec. }
    { clear - HαΔ1 HαΔ2 HX. fsetdec. }
  (* ------------------------------------------- forall_syn (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* ------------------------------------------------------ forall_syn *)
  - (* C-ForallSyn (paper :2853-2926): as C-ForallInh with the opened α
       added to Δ2 only and the input ⊤◇.P0' carried unchanged (the
       Δ1-refinement's [tophole_fill] premise arrives ALREADY at the
       α-extended context). *)
    match goal with
    | Hpm : forall X, X `notin` _ -> _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ =>
        rename Hpm into Hjoin
    end.
    (* SUBJECT: PP = ∀ PPb. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.
    (* INPUT: PP0 = ⊤◇ Pt0 (a ∀-syn target only arises by tophole_fill) *)
    destruct PP0 as [ | n0 | δ0 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
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
      assert (Hgρ0 : guarded_pskl (msubst_pskl ρ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      eapply ad_refine_syn_f_guarded_src_all_syn_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgρ0 ]. }
    match goal with
    | Hn : forall X, X `notin` ?LA ->
             ad_refine_syn_f _ _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_all_syn (msubst_pskl ρ PPb))
              (pskl_all_syn (bskl_to_pskl Q))) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Hn : forall X, X `notin` ?LB ->
             ad_refine_pskl_f _ _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb : exists Lw, forall X, X `notin` Lw ->
              Θ0 ⨟ (add X empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl PPb (pskl_var_f X))).
    { inversion HwfP; subst. eexists. eassumption. }
    destruct Hwfb as [Lw Hwfb].
    (* the fresh rigid α *)
    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw
                        `union` dom Θ0 `union` dom Θ `union` dom ρ
                        `union` F `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl Pt0 `union` ftvar_in_pskl PPb
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hαρ : α `notin` dom ρ) by (clear - Fr; fsetdec).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; fsetdec).
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) ρ Pz
                            = Vpskl Θ ρ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) ρ
           (pskl_tophole Pt0)
           (open_pskl_wrt_pskl PPb (pskl_var_f α))
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ ρ (pskl_tophole Pt0) (pskl_all_syn PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open PPb Hwfth Hlcρ Hαρ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ ρ PPb). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    assert (Hwf0' : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ]).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (pskl_tophole Pt0)).
    { eapply ad_wf_pskl_weaken; [ | exact HwfP0 ].
      intros x b Hb. apply binds_cons_3. exact Hb. }
    assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl PPb (pskl_var_f α))).
    { eapply ad_wf_pskl_delta_to_tvar;
        [ apply Hwfb; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (Hrig' : forall Z, Z `in` (Δ1 `union` add α Δ2) ->
              binds Z abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros Z HZ. destruct (Z == α) as [-> | Hne];
        [ unfold binds; left; reflexivity
        | apply binds_cons_3; apply Hrig; clear - HZ Hne; fsetdec ]. }
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
    assert (Hinc' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ ]
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
    assert (Hjα : Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρ
                 (open_pskl_wrt_pskl PPb (pskl_var_f α))))
              ≈ (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { pose proof (Hjoin α ltac:(clear - Fr; fsetdec)) as Hj0.
      rewrite (msubst_pskl_open_lc PPb Hlcρ Hαρ).
      rewrite pskl_to_uskl_open_var.
      exact Hj0. }
    assert (Hrsα : ad_refine_syn_f Δ1 ((α ~ abind_tvar) ++ Θ) Δ1
              (pskl_to_bskl_inh (msubst_pskl ρ (pskl_tophole Pt0)))
              (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { simpl. apply Hrs1. clear - Fr. fsetdec. }
    assert (Hrpα : ad_refine_pskl_f (add α Δ2) ((α ~ abind_tvar) ++ Θ)
              (add α Δ2)
              (msubst_pskl ρ (open_pskl_wrt_pskl PPb (pskl_var_f α)))
              (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)))).
    { rewrite (msubst_pskl_open_lc PPb Hlcρ Hαρ).
      rewrite bskl_to_pskl_open.
      eapply ad_refine_pskl_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_pskl_f_fextend_dom;
        [ apply Hrp1; clear - Fr; fsetdec | ].
      intros γ Hγ. destruct (γ == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hγ Hne; fsetdec ]. }
    destruct (HcIH F Δ1 (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
                (pskl_tophole Pt0)
                (open_pskl_wrt_pskl PPb (pskl_var_f α)) ρ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα)
      as [P1 [Θ1' [Hc Hopt']]].
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _
                _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.
    (* assemble the cofinite node by renaming the α-instance (L9) *)
    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; fsetdec).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    { apply a_consis__forall_syn with
        (L := L `union` dom Θ0 `union` dom Θ1 `union` dom Θ
              `union` singleton α `union` F `union` Δ1 `union` Δ2
              `union` ftvar_in_pskl Pt0 `union` ftvar_in_pskl PPb
              `union` ftvar_in_pskl P1).
      intros X HX.
      assert (HXα : X <> α) by (clear - HX; fsetdec).
      assert (HXΘ0 : X `notin` dom Θ0) by (clear - HX; fsetdec).
      assert (HXΘ1 : X `notin` dom Θ1) by (clear - HX; fsetdec).
      assert (HXΔ1 : X `notin` Δ1) by (clear - HX; fsetdec).
      assert (HXΔ2 : X `notin` Δ2) by (clear - HX; fsetdec).
      assert (HXPt0 : X `notin` ftvar_in_pskl Pt0)
        by (clear - HX; fsetdec).
      assert (HXPPb : X `notin` ftvar_in_pskl PPb)
        by (clear - HX; fsetdec).
      assert (HXP1 : X `notin` ftvar_in_pskl P1)
        by (clear - HX; fsetdec).
      destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α X))
                  _ _ _ _ _ _ _ _ Hc nil Θ0 eq_refl tvar_prefix_nil
                  Huq0
                  ltac:(simpl; clear - HXΘ0 HXα; fsetdec)
                  ltac:(simpl; clear - HXΘ1 HXα; fsetdec)
                  ltac:(simpl; clear - HXα HXPt0; fsetdec)
                  ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          PPb (pskl_var_f α)) as Hup;
                        simpl in Hup;
                        clear - HXα HXPPb Hup; fsetdec)
                  ltac:(clear - HXP1; fsetdec)
                  ltac:(clear - HXα HXΔ1; fsetdec)
                  ltac:(clear - HXα HXΔ2; fsetdec))
        as [Θt [HeqΘt Hren]].
      simpl in HeqΘt. inversion HeqΘt. subst Θt.
      assert (Ht0 : subst_pskl_in_pskl (pskl_var_f X) α
                      (pskl_tophole Pt0) = pskl_tophole Pt0)
        by (apply subst_pskl_in_pskl_fresh_eq; simpl;
            clear - Fr; fsetdec).
      assert (Ho1 : open_pskl_wrt_pskl PPb (pskl_var_f X)
                  = subst_pskl_in_pskl (pskl_var_f X) α
                      (open_pskl_wrt_pskl PPb (pskl_var_f α)))
        by (apply subst_pskl_in_pskl_intro; clear - Fr; fsetdec).
      rewrite Ht0 in Hren. rewrite <- Ho1 in Hren.
      rewrite (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α) in Hren.
      eapply (proj2 (proj2 a_assign_unify_consis_compat));
        [ exact Hren
        | intros γ Hγ; left; exact Hγ
        | apply rn_set_notin; exact HαΔ1
        | apply rn_set_add_same; exact HαΔ2 ].
    }
    (* optimality *)
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ1 ]
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc1).
      apply a_decls_suffix. apply a_decls__nil. }
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ [Hζ [Hie Hprec]]].
    exists ζ.
    assert (Hζ' : Θ1 ≤[ ζ ] Θ).
    { destruct (a_inc_tvar_inv Hζ) as [Ξs [Θ2 [HeqT [Hsuf Hinc2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hinc2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    assert (Hie' : a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ).
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
      by (destruct (auc_uniq_consis Hc Huq0) as [Hu1 _]; exact Hu1).
    assert (HαΘ1 : α `notin` dom Θ1) by solve_uniq.
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Himg : forall γ τ, In (γ, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros γ τ Hin.
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
    intros X HX.
    assert (HXζ : X `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HX; fsetdec. }
    rewrite <- !pskl_to_bskl_inh_open.
    rewrite <- (msubst_pskl_open_lc (close_pskl_wrt_pskl α P1) Hlcζ HXζ).
    rewrite <- (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α).
    rewrite <- bskl_to_pskl_open.
    pose proof (ad_refine_syn_f_ctx_to_delta Hprec nil Θ eq_refl
                  ltac:(clear; fsetdec)
                  (a_wf_aenv_uniq Hwfth')) as Hp1.
    simpl in Hp1.
    assert (HαF : α `in` (Δ1 `union` add α Δ2))
      by (clear; fsetdec).
    assert (Hdefsθ : forall β τ,
              binds β (abind_flex_mono_def τ) Θ ->
              α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; eassumption).
      clear - Hsc HαΘ. fsetdec. }
    pose proof (ad_refine_syn_f_rename X Hp1 HαF HαΘ Hdefsθ) as Hp2.
    rewrite !pskl_to_bskl_inh_subst_var in Hp2.
    rewrite (msubst_pskl_subst_var ζ P1 Hαζ HXζ Himg) in Hp2.
    rewrite bskl_to_pskl_subst_var in Hp2.
    assert (HoQ : open_bskl_wrt_bskl Q (bskl_var_f X)
                = subst_bskl_in_bskl (bskl_var_f X) α
                    (open_bskl_wrt_bskl Q (bskl_var_f α)))
      by (apply subst_bskl_in_bskl_intro; clear - Fr; fsetdec).
    rewrite <- HoQ in Hp2.
    eapply ad_refine_syn_f_fmono;
      [ | eapply ad_refine_syn_f_delta_mono; [ exact Hp2 | ] ].
    { clear - HαΔ1 HαΔ2. fsetdec. }
    { clear - HαΔ1 HαΔ2 HX. fsetdec. }
  (* ---------------------------------------------- ghostg (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* -------------------------------------------- topholeg (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
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
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    (* the Δ2-refinement bounds the fill's free variables *)
    change (ad_refine_pskl_f Δ2 Θ Δ2 pskl_hole
              (bskl_to_pskl (pskl_to_bskl_inh P))) in Hrp.
    rewrite bskl_to_pskl_pskl_to_bskl_inh in Hrp.
    (* the ftv chase for the Ghost side condition *)
    assert (Hside : forall X, X `in` Δ2 -> X `notin` ftvar_in_pskl PP0).
    { intros X HinΔ2 HinP0.
      assert (HbX0 : binds X abind_tvar Θ0)
        by (apply Hrig; clear - HinΔ2; fsetdec).
      assert (HbX : binds X abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      assert (HXnd : X `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      assert (Hdefs : forall β τ, binds β (abind_flex_mono_def τ) Θ ->
                                  X `notin` ftvar_in_ptyp τ).
      { intros β τ Hb. pose proof (Hnfdth _ _ Hb) as Hd.
        clear - Hd HinΔ2. fsetdec. }
      assert (HninP : X `notin` ftvar_in_pskl P).
      { inversion Hrp; subst.
        - (* hole : the Δ2-hygiene of the fill *)
          match goal with
          | Hint : AtomSetImpl.inter Δ2 (ftvar_in_pskl P) [=] empty |- _ =>
              clear - Hint HinΔ2; fsetdec
          end.
        - (* flex_r : the fill is a defined flexible, never the rigid X *)
          simpl.
          match goal with
          | Hbr : binds ?α0 (abind_flex_mono_def _) Θ |- _ =>
              assert (Hne : X <> α0)
                by (intro Heq; subst;
                    pose proof (binds_unique _ _ _ _ _ HbX Hbr
                                  (a_wf_aenv_uniq Hwfth)) as Hcon;
                    discriminate)
          end.
          clear - Hne; fsetdec. }
      assert (HinθP0 : X `in` ftvar_in_pskl (msubst_pskl ρ PP0))
        by (apply msubst_pskl_ftv_keep; assumption).
      assert (HninSrc : X `notin`
                ftvar_in_bskl (pskl_to_bskl_inh (msubst_pskl ρ PP0))).
      { eapply ad_refine_syn_f_rigid_ftv_rev;
          [ exact Hwfth | exact HbX | exact Hdefs | exact Hrs | ].
        pose proof (ftvar_in_bskl_inh P) as Hfe.
        clear - HninP Hfe. fsetdec. }
      pose proof (ftvar_in_bskl_inh (msubst_pskl ρ PP0)) as Hfe2.
      clear - HninSrc HinθP0 Hfe2. fsetdec. }
    exists PP0, Θ0. split.
    { apply a_consis__ghost.
      apply inter_empty_pointwise. exact Hside. }
    intros ρ1 Hid Hinc1. exists ρ.
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
    intros γ Hγ.
    destruct (AtomSetProperties.In_dec γ Δ1) as [HγΔ1 | HγΔ1];
      [ left; exact HγΔ1 | right ].
    assert (HγΔ2 : γ `in` Δ2) by (clear - Hγ HγΔ1; fsetdec).
    assert (Hbγ : binds γ abind_tvar Θ)
      by (eapply a_inc_binds_tvar; [ exact Hinc | ];
          apply Hrig; clear - HγΔ2; fsetdec).
    split.
    + assert (Hnq : γ `notin` ftvar_in_pskl P)
        by (eapply ad_refine_pskl_f_hole_src_target_ftv;
            [ exact Hrp | exact Hwfth
            | clear - HγΔ2; fsetdec | exact Hbγ ]).
      pose proof (ftvar_in_bskl_inh P) as Hfe.
      clear - Hnq Hfe. fsetdec.
    + intros β τ Hb.
      pose proof (Hnfdth β τ Hb) as Hi.
      clear - Hi HγΔ2. fsetdec.
  (* ---------------------------------------------------------- tophole *)
  - (* C-UnivGhost (paper :2928-2993): both sides strip one ⊤◇; wf forces
       the input to be a ⊤◇ as well (a guarded input's refinement target is
       guarded, never a ⊤◇); V drops by 2, recurse through the μ-IH. *)
    match goal with
    | Hpm : _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ => rename Hpm into Hj
    end.
    (* SUBJECT: PP = ⊤◇PPt (var subjects are rigid, their image a var). *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R. clear HeqS.
    assert (HgPPt : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPPt : Θ0 ⨟ empty ⊢ₚₛᵃ PPt) by (inversion HwfP; assumption).
    assert (HgρP : guarded_pskl (msubst_pskl ρ PPt))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (HlcQ : lc_bskl Q).
    { assert (Hlct : lc_bskl (bskl_tophole Q))
        by (eapply ad_refine_syn_f_lc_r; exact Hrs).
      inversion Hlct; assumption. }
    assert (HgQ : guarded_bskl Q).
    { eapply ad_pat_consis_guarded_r;
        [ exact Hj | exact Hwfth | reflexivity | exact HgρP | exact HlcQ ]. }
    (* INPUT: PP0 = ⊤◇P0t (every other head's target is not a ⊤◇). *)
    destruct PP0 as [ | n0 | δ0 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ (* var δ0 : rigid; a rigid variable does not refine to a ⊤◇ *)
      exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr (a_wf_aenv_uniq Hwfth))
            as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; apply HneP0hole; reflexivity. }
    (* PP0 = ⊤◇Pt0 : strip the ⊤◇ on all three judgments. *)
    assert (Hg0t : guarded_pskl Pt0) by (inversion HwfP0; assumption).
    assert (HwfP0t : Θ0 ⨟ empty ⊢ₚₛᵃ Pt0) by (inversion HwfP0; assumption).
    assert (Hgρ0 : guarded_pskl (msubst_pskl ρ Pt0))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
              (pskl_to_bskl_inh (msubst_pskl ρ Pt0)) Q).
    { eapply ad_refine_syn_f_tophole_keep_inv;
        [ exact Hwfth | | exact Hrs ].
      apply guarded_pskl_to_bskl_inh. exact Hgρ0. }
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl ρ PPt))
              (pskl_tophole (bskl_to_pskl Q))) in Hrp.
    assert (Hrp' : ad_refine_pskl_f Δ2 Θ Δ2
              (msubst_pskl ρ PPt) (bskl_to_pskl Q))
      by (eapply ad_refine_pskl_f_tophole_keep_inv;
            [ exact Hwfth | exact HgρP | exact Hrp ]).
    assert (Hlt : mu_lt (mu_consis Θ ρ Pt0 PPt Θ0)
                        (mu_consis Θ ρ (pskl_tophole Pt0)
                                       (pskl_tophole PPt) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      pose proof (Vpskl_tophole_lt Θ ρ Pt0).
      pose proof (Vpskl_tophole_lt Θ ρ PPt). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH F Δ1 Δ2 Θ0 Pt0 PPt ρ Θ Ψ Q eq_refl Hwf0 HwfP0t HwfPPt
                   Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs' Hrp')
      as [P1 [Θ1 [Hc Hopt']]].
    exists (pskl_tophole P1), Θ1. split.
    { apply a_consis__univ_ghost. exact Hc. }
    intros ρ1 Hid Hinc1.
    destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
    unfold ad_precise_f in *. simpl.
    apply ad_refine_syn_f__tophole_keep; [ | exact Hprec ].
    apply guarded_pskl_to_bskl_inh, guarded_bskl_to_pskl. exact HgQ.
  (* ------------------------------------------------------ tophole_inh *)
  - (* C-UnivGhost1 (paper :2995-3070): the input's ∀ opens with a fresh
       rigid α added to Θ0 and Δ1; the subject ⊤◇.PPt is carried
       unchanged through the μ-IH and the L9 rename. *)
    match goal with
    | Hpm : forall X, X `notin` _ -> _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ =>
        rename Hpm into Hjoin
    end.
    (* SUBJECT: PP = ⊤◇ PPt. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.
    (* INPUT: PP0 = ∀ P0b. *)
    destruct PP0 as [ | n0 | δ0 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                        (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ exfalso.
      assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
      assert (Hgρ0 : guarded_pskl (msubst_pskl ρ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      inversion Hrs; subst.
      eapply ad_refine_syn_f_guarded_src_all_inh_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgρ0 ]. }
    (* ∀ input, ⊤◇ subject : invert the refinements, wf pieces *)
    assert (HgP : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPt : Θ0 ⨟ empty ⊢ₚₛᵃ PPt) by (inversion HwfP; assumption).
    inversion Hrs; subst.
    match goal with
    | Hn : forall X, X `notin` ?LA ->
             ad_refine_syn_f _ _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl ρ PPt))
              (pskl_all_syn (bskl_to_pskl Q))) in Hrp.
    inversion Hrp; subst.
    1:{ (* __tophole_remove : the guarded subject body vs a ∀-syn *)
      exfalso.
      assert (HgρP : guarded_pskl (msubst_pskl ρ PPt))
        by (eapply guarded_pskl_msubst_inc; eauto).
      eapply ad_refine_pskl_f_guarded_src_all_syn_absurd;
        [ exact Hwfth | eassumption | exact HgρP ]. }
    match goal with
    | Hn : forall X, X `notin` ?LB ->
             ad_refine_pskl_f _ _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb0 : exists Lw0, forall X, X `notin` Lw0 ->
              Θ0 ⨟ (add X empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl P0b (pskl_var_f X))).
    { inversion HwfP0; subst. eexists. eassumption. }
    destruct Hwfb0 as [Lw0 Hwfb0].
    (* the fresh rigid α *)
    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw0
                        `union` dom Θ0 `union` dom Θ `union` dom ρ
                        `union` F `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPt
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hαρ : α `notin` dom ρ) by (clear - Fr; fsetdec).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; fsetdec).
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) ρ Pz
                            = Vpskl Θ ρ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) ρ
           (open_pskl_wrt_pskl P0b (pskl_var_f α))
           (pskl_tophole PPt)
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ ρ (pskl_all_syn P0b) (pskl_tophole PPt) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open P0b Hwfth Hlcρ Hαρ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ ρ P0b). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    assert (Hwf0' : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ]).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (open_pskl_wrt_pskl P0b (pskl_var_f α))).
    { eapply ad_wf_pskl_delta_to_tvar;
        [ apply Hwfb0; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (pskl_tophole PPt)).
    { eapply ad_wf_pskl_weaken; [ | exact HwfP ].
      intros x b Hb. apply binds_cons_3. exact Hb. }
    assert (Hrig' : forall Z, Z `in` (add α Δ1 `union` Δ2) ->
              binds Z abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros Z HZ. destruct (Z == α) as [-> | Hne];
        [ unfold binds; left; reflexivity
        | apply binds_cons_3; apply Hrig; clear - HZ Hne; fsetdec ]. }
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
    assert (Hinc' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ ]
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
    assert (Hjα : Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρ (pskl_tophole PPt)))
              ≈ (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { simpl. apply Hjoin. clear - Fr. fsetdec. }
    assert (Hrsα : ad_refine_syn_f (add α Δ1) ((α ~ abind_tvar) ++ Θ)
              (add α Δ1)
              (pskl_to_bskl_inh (msubst_pskl ρ
                 (open_pskl_wrt_pskl P0b (pskl_var_f α))))
              (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { rewrite (msubst_pskl_open_lc P0b Hlcρ Hαρ).
      rewrite pskl_to_bskl_inh_open.
      eapply ad_refine_syn_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_syn_f_fextend_dom;
        [ apply Hrs1; clear - Fr; fsetdec | ].
      intros γ Hγ. destruct (γ == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hγ Hne; fsetdec ]. }
    assert (Hrpα : ad_refine_pskl_f Δ2 ((α ~ abind_tvar) ++ Θ) Δ2
              (msubst_pskl ρ (pskl_tophole PPt))
              (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)))).
    { simpl. rewrite bskl_to_pskl_open. apply Hrp1.
      clear - Fr. fsetdec. }
    destruct (HcIH F (add α Δ1) Δ2 ((α ~ abind_tvar) ++ Θ0)
                (open_pskl_wrt_pskl P0b (pskl_var_f α))
                (pskl_tophole PPt) ρ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα)
      as [P1 [Θ1' [Hc Hopt']]].
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _
                _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.
    (* assemble the cofinite node by renaming the α-instance (L9) *)
    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; fsetdec).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    { apply a_consis__univ_ghost1 with
        (L := L `union` dom Θ0 `union` dom Θ1 `union` dom Θ
              `union` singleton α `union` F `union` Δ1 `union` Δ2
              `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPt
              `union` ftvar_in_pskl P1).
      intros X HX.
      assert (HXα : X <> α) by (clear - HX; fsetdec).
      assert (HXΘ0 : X `notin` dom Θ0) by (clear - HX; fsetdec).
      assert (HXΘ1 : X `notin` dom Θ1) by (clear - HX; fsetdec).
      assert (HXΔ1 : X `notin` Δ1) by (clear - HX; fsetdec).
      assert (HXΔ2 : X `notin` Δ2) by (clear - HX; fsetdec).
      assert (HXP0b : X `notin` ftvar_in_pskl P0b)
        by (clear - HX; fsetdec).
      assert (HXPPt : X `notin` ftvar_in_pskl PPt)
        by (clear - HX; fsetdec).
      assert (HXP1 : X `notin` ftvar_in_pskl P1)
        by (clear - HX; fsetdec).
      destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α X))
                  _ _ _ _ _ _ _ _ Hc nil Θ0 eq_refl tvar_prefix_nil
                  Huq0
                  ltac:(simpl; clear - HXΘ0 HXα; fsetdec)
                  ltac:(simpl; clear - HXΘ1 HXα; fsetdec)
                  ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          P0b (pskl_var_f α)) as Hup;
                        simpl in Hup;
                        clear - HXα HXP0b Hup; fsetdec)
                  ltac:(simpl; clear - HXα HXPPt; fsetdec)
                  ltac:(clear - HXP1; fsetdec)
                  ltac:(clear - HXα HXΔ1; fsetdec)
                  ltac:(clear - HXα HXΔ2; fsetdec))
        as [Θt [HeqΘt Hren]].
      simpl in HeqΘt. inversion HeqΘt. subst Θt.
      assert (Ho0 : open_pskl_wrt_pskl P0b (pskl_var_f X)
                  = subst_pskl_in_pskl (pskl_var_f X) α
                      (open_pskl_wrt_pskl P0b (pskl_var_f α)))
        by (apply subst_pskl_in_pskl_intro; clear - Fr; fsetdec).
      assert (Ht0 : subst_pskl_in_pskl (pskl_var_f X) α
                      (pskl_tophole PPt) = pskl_tophole PPt)
        by (apply subst_pskl_in_pskl_fresh_eq; simpl;
            clear - Fr; fsetdec).
      rewrite <- Ho0 in Hren. rewrite Ht0 in Hren.
      rewrite (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α) in Hren.
      eapply (proj2 (proj2 a_assign_unify_consis_compat));
        [ exact Hren
        | intros γ Hγ; left; exact Hγ
        | apply rn_set_add_same; exact HαΔ1
        | apply rn_set_notin; exact HαΔ2 ].
    }
    (* optimality *)
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ1 ]
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc1).
      apply a_decls_suffix. apply a_decls__nil. }
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ [Hζ [Hie Hprec]]].
    exists ζ.
    assert (Hζ' : Θ1 ≤[ ζ ] Θ).
    { destruct (a_inc_tvar_inv Hζ) as [Ξs [Θ2 [HeqT [Hsuf Hinc2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hinc2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    assert (Hie' : a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ).
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
      by (destruct (auc_uniq_consis Hc Huq0) as [Hu1 _]; exact Hu1).
    assert (HαΘ1 : α `notin` dom Θ1) by solve_uniq.
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Himg : forall γ τ, In (γ, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros γ τ Hin.
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
    intros X HX.
    assert (HXζ : X `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HX; fsetdec. }
    rewrite <- !pskl_to_bskl_inh_open.
    rewrite <- (msubst_pskl_open_lc (close_pskl_wrt_pskl α P1) Hlcζ HXζ).
    rewrite <- (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α).
    rewrite <- bskl_to_pskl_open.
    pose proof (ad_refine_syn_f_ctx_to_delta Hprec nil Θ eq_refl
                  ltac:(clear; fsetdec)
                  (a_wf_aenv_uniq Hwfth')) as Hp1.
    simpl in Hp1.
    assert (HαF : α `in` (add α Δ1 `union` Δ2))
      by (clear; fsetdec).
    assert (Hdefsθ : forall β τ,
              binds β (abind_flex_mono_def τ) Θ ->
              α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; eassumption).
      clear - Hsc HαΘ. fsetdec. }
    pose proof (ad_refine_syn_f_rename X Hp1 HαF HαΘ Hdefsθ) as Hp2.
    rewrite !pskl_to_bskl_inh_subst_var in Hp2.
    rewrite (msubst_pskl_subst_var ζ P1 Hαζ HXζ Himg) in Hp2.
    rewrite bskl_to_pskl_subst_var in Hp2.
    assert (HoQ : open_bskl_wrt_bskl Q (bskl_var_f X)
                = subst_bskl_in_bskl (bskl_var_f X) α
                    (open_bskl_wrt_bskl Q (bskl_var_f α)))
      by (apply subst_bskl_in_bskl_intro; clear - Fr; fsetdec).
    rewrite <- HoQ in Hp2.
    eapply ad_refine_syn_f_fmono;
      [ | eapply ad_refine_syn_f_delta_mono; [ exact Hp2 | ] ].
    { clear - HαΔ1 HαΔ2. fsetdec. }
    { clear - HαΔ1 HαΔ2 HX. fsetdec. }
  (* ----------------------------------------------------- tophole_drop *)
  - (* C-UnivGhost2 (paper :3072-3164): the subject strips its ⊤◇; the
       guarded subject body makes the join target Q guarded, which drives
       BOTH sub-cases: input ⊤◇P0t (strip on all three, [univ_ghost]) or
       input guarded (subject-only strip, [univ_ghost2]). *)
    match goal with
    | Hpm : _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ => rename Hpm into Hj
    end.
    (* SUBJECT: PP = ⊤◇PPt. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R. clear HeqS.
    assert (HgPPt : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPPt : Θ0 ⨟ empty ⊢ₚₛᵃ PPt) by (inversion HwfP; assumption).
    assert (HgρP : guarded_pskl (msubst_pskl ρ PPt))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (HlcQ : lc_bskl Q) by (eapply ad_refine_syn_f_lc_r; exact Hrs).
    assert (HgQ : guarded_bskl Q).
    { eapply ad_pat_consis_guarded_r;
        [ exact Hj | exact Hwfth | reflexivity | exact HgρP | exact HlcQ ]. }
    (* the subject-side refinement drops its ⊤◇ against the guarded Q *)
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl ρ PPt)) (bskl_to_pskl Q)) in Hrp.
    assert (Hrp' : ad_refine_pskl_f Δ2 Θ Δ2
              (msubst_pskl ρ PPt) (bskl_to_pskl Q)).
    { eapply ad_refine_pskl_f_tophole_guarded_inv;
        [ exact Hwfth | exact Hrp | ].
      apply guarded_bskl_to_pskl. exact HgQ. }
    (* INPUT: split on whether PP0 is a ⊤◇. *)
    assert (Hthdec : (exists P0t, PP0 = pskl_tophole P0t) \/
                     (forall P0t, PP0 <> pskl_tophole P0t)).
    { destruct PP0; try (right; intros ? Hc0; discriminate).
      left; eexists; reflexivity. }
    destruct Hthdec as [[P0t ->] | Hnth0].
    + (* PP0 = ⊤◇P0t : paper :3098-3132; both inputs strip, [univ_ghost]. *)
      assert (Hg0t : guarded_pskl P0t) by (inversion HwfP0; assumption).
      assert (HwfP0t : Θ0 ⨟ empty ⊢ₚₛᵃ P0t) by (inversion HwfP0; assumption).
      change (ad_refine_syn_f Δ1 Θ Δ1
                (bskl_tophole (pskl_to_bskl_inh (msubst_pskl ρ P0t))) Q)
        in Hrs.
      assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
                (pskl_to_bskl_inh (msubst_pskl ρ P0t)) Q)
        by (eapply ad_refine_syn_f_tophole_guarded_inv; eauto).
      assert (Hlt : mu_lt (mu_consis Θ ρ P0t PPt Θ0)
                          (mu_consis Θ ρ (pskl_tophole P0t)
                                         (pskl_tophole PPt) Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
        pose proof (Vpskl_tophole_lt Θ ρ P0t).
        pose proof (Vpskl_tophole_lt Θ ρ PPt). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH F Δ1 Δ2 Θ0 P0t PPt ρ Θ Ψ Q eq_refl Hwf0 HwfP0t HwfPPt
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs' Hrp')
        as [P1 [Θ1 [Hc Hopt']]].
      exists (pskl_tophole P1), Θ1. split.
      { apply a_consis__univ_ghost. exact Hc. }
      intros ρ1 Hid Hinc1.
      destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      unfold ad_precise_f in *. simpl.
      apply ad_refine_syn_f__tophole_remove. exact Hprec.
    + (* PP0 guarded : paper :3134-3163; subject-only strip, [univ_ghost2]. *)
      assert (Hg0 : guarded_pskl PP0).
      { destruct PP0 as [ | n0 | δ0 | Pa0 Pb0 | Pb0 | | Pt0 ].
        - apply guarded_pskl__unit.
        - inversion HwfP0.
        - apply guarded_pskl__var.
        - pose proof (ad_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption.
        - (* ∀ : an inherited quantifier never refines to the guarded Q *)
          exfalso. simpl in Hrs.
          eapply ad_refine_syn_f_all_inh_guarded_absurd;
            [ exact Hwfth | exact Hrs | exact HgQ ].
        - exfalso; apply HneP0hole; reflexivity.
        - exfalso; eapply Hnth0; reflexivity. }
      assert (Hlt : mu_lt (mu_consis Θ ρ PP0 PPt Θ0)
                          (mu_consis Θ ρ PP0 (pskl_tophole PPt) Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
        pose proof (Vpskl_tophole_lt Θ ρ PPt). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH F Δ1 Δ2 Θ0 PP0 PPt ρ Θ Ψ Q eq_refl Hwf0 HwfP0 HwfPPt
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs Hrp')
        as [P1 [Θ1 [Hc Hopt']]].
      exists P1, Θ1. split.
      { apply a_consis__univ_ghost2;
          [ exact Hg0 | exact HnfP0 | exact Hc ]. }
      exact Hopt'.
  (* ----------------------------------------------- flex_l (impossible) *)
  - (* The subject is non-flex, so a variable subject is RIGID in Θ0 and
       stays rigid in Θ — it cannot be the defined flexible the join's
       left lookup unfolds. *)
    exfalso.
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    assert (Hbtδ : binds δ abind_tvar Θ0).
    { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
      destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
        [ exfalso; clear - HΔ; fsetdec
        | exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          apply a_flex__var; exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          eapply a_flex__var_def; exact Hb ]. }
    assert (Hδρ : δ `notin` dom ρ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
    simpl in HeqS. inversion HeqS; subst α.
    assert (HbtΘ : binds δ abind_tvar Θ)
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
    assert (Hdisj : AtomSetImpl.inter (Δ1 `union` Δ2) (ftvar_in_ptyp τ)
                      [=] empty)
      by (apply (Hnfdth _ _ Hbα)).
    assert (HΔbt : forall X, X `in` (Δ1 `union` Δ2) ->
                             binds X abind_tvar Θ).
    { intros X HX. eapply a_inc_binds_tvar; [ exact Hinc | ].
      apply Hrig. exact HX. }
    (* transport the two refinement witnesses through the unfold *)
    assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
              (pskl_to_bskl_inh (msubst_pskl ρ PP0)) (ptyp_to_bskl_syn τ)).
    { eapply ad_refine_syn_f_flex_target_unfold;
        [ exact Hwfth | exact Hbα
        | intros X HX; apply HΔbt; clear - HX; fsetdec
        | clear - Hdisj; fsetdec
        | exact Hrs ]. }
    assert (Hrp' : ad_refine_pskl_f Δ2 Θ Δ2
              (msubst_pskl ρ PP) (bskl_to_pskl (ptyp_to_bskl_syn τ))).
    { unfold ptyp_to_bskl_syn.
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      eapply ad_refine_pskl_f_flex_target_unfold;
        [ exact Hwfth | exact Hbα
        | intros X HX; apply HΔbt; clear - HX; fsetdec
        | clear - Hdisj; fsetdec
        | exact Hrp ]. }
    (* recurse on the premise at the SAME measure *)
    destruct (IHHj F Δ1 Δ2 Θ0 PP0 PP ρ IH Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf
                   Hinc Hwfth Hnfdth HΨ HeqS HnfP HnfP0 HneP0hole Hnthg
                   Hrs' Hrp')
      as [P1 [Θ1 [Hc Hopt']]].
    exists P1, Θ1. split; [ exact Hc | ].
    intros ρ1 Hid Hinc1.
    destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
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
  intros F Δ1 Δ2 Θ0 P0 P ρ Θ Ψ Qb Hm Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf
    Hinc Hwfth Hnfdth HΨ Hjoin Hrs Hrp.
  subst m.
  (* ---- Layer 0a: flexible SUBJECT — parts 2/3 (t breaks the tie) ---- *)
  destruct (a_flex_shape_dec HwfP) as [[β [-> Hfβ]] | HnfP].
  { destruct (a_flex_shape_dec HwfP0) as [[δ0 [-> Hfδ0]] | HnfP0].
    - (* C-Flex : both hatted — part 2 (unification). *)
      assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
                (pskl_to_uskl (msubst_pskl ρ (pskl_var_f β))) ≈ Qb)
        by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
      assert (Hjoin'' : empty ⨟ Θ ⊨ₛᵃ
                (ptyp_to_uskl_syn (msubst_lookup ρ β)) ≈ Qb).
      { replace (msubst_pskl ρ (pskl_var_f β))
          with (ptyp_to_pskl (msubst_lookup ρ β)) in Hjoin' by reflexivity.
        rewrite pskl_to_uskl_ptyp in Hjoin'. exact Hjoin'. }
      assert (Hmβ : mono_ptyp (msubst_lookup ρ β))
        by (eapply a_inc_lookup_mono; exact Hinc).
      assert (Hmδ0 : mono_ptyp (msubst_lookup ρ δ0))
        by (eapply a_inc_lookup_mono; exact Hinc).
      apply ad_refine_syn_f_forget in Hrs.
      replace (msubst_pskl ρ (pskl_var_f δ0))
        with (ptyp_to_pskl (msubst_lookup ρ δ0)) in Hrs by reflexivity.
      rewrite (ptyp_to_bskl_inh_syn_eq Hmδ0) in Hrs.
      destruct (refine_mono_join Hrs Hwfth (B := msubst_lookup ρ δ0)
                  eq_refl Hmδ0) as [C [HmC [HeqQb HeqδC]]].
      subst Qb.
      destruct (consis_mono_join Hjoin'' Hwfth (A := msubst_lookup ρ β)
                  eq_refl Hmβ) as [C' [HmC' [HeqQb' HeqβC']]].
      assert (HCC : C = C')
        by (apply ptyp_to_bskl_syn_inj; auto).
      subst C'.
      assert (Heqβδ : Θ ⊢ (msubst_lookup ρ β) ≡ᵗ (msubst_lookup ρ δ0)).
      { eapply a_tyequiv__trans; [ exact HeqβC' | ].
        apply a_tyequiv__sym; exact HeqδC. }
      assert (Hlt : mu_lt (mu_unify Θ ρ β δ0 Θ0)
                          (mu_consis Θ ρ (pskl_var_f δ0) (pskl_var_f β) Θ0)).
      { unfold mu_unify, mu_consis. apply mu_lt_intro. right.
        split; [ symmetry; apply V_flex | ].
        right. split; [ reflexivity | left; lia ]. }
      destruct (IH _ Hlt) as [_ [HuIH _]].
      destruct (HuIH F Θ0 β δ0 ρ Θ eq_refl Hwf0 Hfβ Hfδ0 Hinc Hwfth Heqβδ)
        as [Θ1 [Hu Hopt']].
      exists (pskl_var_f β), Θ1. split.
      { apply a_consis__flex. exact Hu. }
      intros ρ1 Hid Hinc1.
      destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ Hie]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      (* precision recovery for the hatted output (prop_precise_recover) *)
      assert (Hbtβ0 : a_binds_tvar β Θ0) by (right; exact Hfβ).
      assert (Hwfvβ : a_wf_ptyp Θ1 (msubst_lookup ρ1 β))
        by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtβ0 ]).
      rewrite (msubst_lookup_id β Hid) in Hwfvβ.
      assert (HbtβΘ1 : a_binds_tvar β Θ1) by (inversion Hwfvβ; assumption).
      destruct (a_unify_sound Hu Hwf0) as [_ [Hwf1 _]].
      try unfold ad_precise_f.
      apply ad_refine_syn_f_of_plain_no_hole;
        [ | apply pskl_to_bskl_inh_no_hole, bskl_to_pskl_no_hole,
            msubst_bskl_no_hole; simpl; exact I ].
      eapply consis_precise_via_join with (Θ0 := Θ0) (θ1 := ρ1);
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
      assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
                (pskl_to_uskl (msubst_pskl ρ (pskl_var_f β))) ≈ Qb)
        by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
      assert (Hjoin'' : empty ⨟ Θ ⊨ₛᵃ
                (ptyp_to_uskl_syn (msubst_lookup ρ β)) ≈ Qb).
      { replace (msubst_pskl ρ (pskl_var_f β))
          with (ptyp_to_pskl (msubst_lookup ρ β)) in Hjoin' by reflexivity.
        rewrite pskl_to_uskl_ptyp in Hjoin'. exact Hjoin'. }
      assert (Hmβ : mono_ptyp (msubst_lookup ρ β))
        by (eapply a_inc_lookup_mono; exact Hinc).
      (* the join target is a monotype painting: Qb = syn C, θβ̂ ≡ᵗ C *)
      destruct (consis_mono_join Hjoin'' Hwfth (A := msubst_lookup ρ β)
                  eq_refl Hmβ) as [C [HmC [HeqQb HeqβC]]].
      subst Qb.
      (* refine→join bridge on the Δ1-refinement *)
      apply ad_refine_syn_f_forget in Hrs.
      assert (Hbr : empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P0))
                      ≈ (ptyp_to_bskl_syn C)).
      { eapply refine_inh_mono_consis;
          [ exact Hrs | exact Hwfth
          | apply mono_ptyp_to_bskl_syn; exact HmC
          | reflexivity
          | intros X HX; left; eapply a_inc_binds_tvar;
              [ exact Hinc | apply Hrig; clear - HX; fsetdec ] ]. }
      (* transport the join target from C to θβ̂ along the equivalence *)
      assert (Hvβ : forall X, X `in` ftvar_in_ptyp (msubst_lookup ρ β) ->
                              a_binds_tvar X Θ).
      { intros X HX. eapply a_wf_ptyp_ftv_tvarish; [ | exact HX ].
        eapply a_inc_lookup_wf;
          [ exact Hinc | exact Hwf0 | right; exact Hfβ ]. }
      destruct (tyequiv_mono_consis_transport_q HeqβC Hwfth Hmβ Hvβ)
        as [Htq _].
      assert (Hjoin3 : empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P0))
                        ≈ (ptyp_to_bskl_syn (msubst_lookup ρ β)))
        by (apply Htq; exact Hbr).
      (* the measure: V constant (pairing), n constant, t breaks the tie *)
      assert (Hlt : mu_lt (mu_assign Θ ρ β P0 nil Θ0)
                          (mu_consis Θ ρ P0 (pskl_var_f β) Θ0)).
      { unfold mu_assign, mu_consis. apply mu_lt_intro. right.
        split; [ symmetry; apply V_flexL | ].
        right. split; [ reflexivity | left; lia ]. }
      assert (Hdom : dom (nil : aenv) [<=] ftvar_in_pskl P0)
        by (simpl; clear; fsetdec).
      destruct (IH _ Hlt) as [_ [_ HaIH]].
      destruct (HaIH F Θ0 nil β P0 ρ Θ eq_refl a_decls__nil Hwf0 Hfβ
                     HwfP0 HnfP0 Hdom Hinc Hwfth Hjoin3)
        as [Θ1 [Ha Hopt']].
      exists (pskl_var_f β), Θ1. split.
      { apply a_consis__flex_l; [ exact HnfP0 | exact Ha ]. }
      intros ρ1 Hid Hinc1.
      destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ Hie]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      (* precision recovery for the hatted output (prop_precise_recover) *)
      assert (Hbtβ0 : a_binds_tvar β Θ0) by (right; exact Hfβ).
      assert (Hwfvβ : a_wf_ptyp Θ1 (msubst_lookup ρ1 β))
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
      eapply consis_precise_via_join with (Θ0 := Θ0) (θ1 := ρ1);
        [ exact Hwfth | exact Hfβ | exact Hinc | exact HbtβΘ1
        | exact Hζ | exact Hwf1 | exact Hie
        | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfβ ]
        | apply (msubst_lookup_id β Hid)
        | exact Hjoin' ]. }
  (* ---- Layer 0b: flexible INPUT, non-flex subject : C-FlexR --------- *)
  destruct (a_flex_shape_dec HwfP0) as [[δ0 [-> Hfδ0]] | HnfP0].
  { (* part 3 (assignment δ̂0 ≔ P): the input δ̂0's image is a monotype, so
       [refine_mono_join] reads Qb = syn C off the Δ1-refinement and the
       join's TARGET transports from C to θδ̂0 along the equivalence
       ([tyequiv_mono_consis_transport_q] — general subject); precision by
       [consis_precise_via_refine]. *)
    assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρ P)) ≈ Qb)
      by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
    assert (Hmδ0 : mono_ptyp (msubst_lookup ρ δ0))
      by (eapply a_inc_lookup_mono; exact Hinc).
    (* the Δ1-refinement's source is a monotype painting: Qb = syn C *)
    pose proof Hrs as Hrs2.
    apply ad_refine_syn_f_forget in Hrs2.
    replace (msubst_pskl ρ (pskl_var_f δ0))
      with (ptyp_to_pskl (msubst_lookup ρ δ0)) in Hrs2 by reflexivity.
    rewrite (ptyp_to_bskl_inh_syn_eq Hmδ0) in Hrs2.
    destruct (refine_mono_join Hrs2 Hwfth (B := msubst_lookup ρ δ0)
                eq_refl Hmδ0) as [C [HmC [HeqQb HeqδC]]].
    (* transport the join target from C to θδ̂0 along the equivalence *)
    assert (Hvδ : forall X, X `in` ftvar_in_ptyp (msubst_lookup ρ δ0) ->
                            a_binds_tvar X Θ).
    { intros X HX. eapply a_wf_ptyp_ftv_tvarish; [ | exact HX ].
      eapply a_inc_lookup_wf;
        [ exact Hinc | exact Hwf0 | right; exact Hfδ0 ]. }
    destruct (tyequiv_mono_consis_transport_q HeqδC Hwfth Hmδ0 Hvδ)
      as [Htq _].
    assert (Hjoin3 : empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P))
                      ≈ (ptyp_to_bskl_syn (msubst_lookup ρ δ0))).
    { apply Htq. rewrite <- HeqQb. exact Hjoin'. }
    (* the measure: V constant (pairing), n constant, t breaks the tie *)
    assert (Hlt : mu_lt (mu_assign Θ ρ δ0 P nil Θ0)
                        (mu_consis Θ ρ (pskl_var_f δ0) P Θ0)).
    { unfold mu_assign, mu_consis. apply mu_lt_intro. right.
      split; [ symmetry; apply V_flexR | ].
      right. split; [ reflexivity | left; lia ]. }
    assert (Hdom : dom (nil : aenv) [<=] ftvar_in_pskl P)
      by (simpl; clear; fsetdec).
    destruct (IH _ Hlt) as [_ [_ HaIH]].
    destruct (HaIH F Θ0 nil δ0 P ρ Θ eq_refl a_decls__nil Hwf0 Hfδ0
                   HwfP HnfP Hdom Hinc Hwfth Hjoin3)
      as [Θ1 [Ha Hopt']].
    exists (pskl_var_f δ0), Θ1. split.
    { apply a_consis__flex_r; [ exact HnfP | exact Ha ]. }
    intros ρ1 Hid Hinc1.
    destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ Hie]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
    (* precision recovery for the hatted output, off the Δ1-refinement *)
    assert (Hbtδ00 : a_binds_tvar δ0 Θ0) by (right; exact Hfδ0).
    assert (Hwfvδ : a_wf_ptyp Θ1 (msubst_lookup ρ1 δ0))
      by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtδ00 ]).
    rewrite (msubst_lookup_id δ0 Hid) in Hwfvδ.
    assert (HbtδΘ1 : a_binds_tvar δ0 Θ1) by (inversion Hwfvδ; assumption).
    assert (Hwf1 : a_wf_aenv Θ1)
      by (eapply a_assign_preserves_wf;
            [ exact Ha | apply a_decls__nil | exact Hwf0 | exact HwfP ]).
    try unfold ad_precise_f.
    apply ad_refine_syn_f_of_plain_no_hole;
      [ | apply pskl_to_bskl_inh_no_hole, bskl_to_pskl_no_hole,
          msubst_bskl_no_hole; simpl; exact I ].
    eapply consis_precise_via_refine with (Θ0 := Θ0) (θ1 := ρ1);
      [ exact Hwfth | exact Hfδ0 | exact Hinc | exact HbtδΘ1
      | exact Hζ | exact Hwf1 | exact Hie
      | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfδ0 ]
      | apply (msubst_lookup_id δ0 Hid)
      | exact Hrs ]. }
  (* ---- Layer 0c: P0 = ◇ : C-GhostR ---------------------------------- *)
  destruct (pskl_eq_dec P0 pskl_hole) as [-> | HneP0hole].
  { (* axiom node [a_consis__ghost_r].  The side condition
       [Δ1 ∩ ftv(P) = ∅] is the mirror rigid-ftv chase, through the JOIN
       ([ad_pat_consis_rigid_ftv_rev]) against the Δ1-hygiene of the hole
       fill in Hrs; precision re-inherits the Δ2-refinement through the
       join by [refine_join_reinherit]. *)
    assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P)) ≈ Qb)
      by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
    change (ad_refine_syn_f Δ1 Θ Δ1 bskl_hole Qb) in Hrs.
    (* Qb is a syn-painting fixed point (its refinement source is ◇) *)
    assert (HQb : pskl_to_bskl_syn (bskl_to_pskl Qb) = Qb).
    { inversion Hrs; subst.
      - rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity.
      - simpl. reflexivity. }
    (* the ftv chase for the GhostR side condition *)
    assert (Hside : forall X, X `in` Δ1 -> X `notin` ftvar_in_pskl P).
    { intros X HinΔ1 HinP.
      assert (HbX0 : binds X abind_tvar Θ0)
        by (apply Hrig; clear - HinΔ1; fsetdec).
      assert (HbX : binds X abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      assert (HXnd : X `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      assert (Hdefs : forall β τ, binds β (abind_flex_mono_def τ) Θ ->
                                  X `notin` ftvar_in_ptyp τ).
      { intros β τ Hb. pose proof (Hnfdth _ _ Hb) as Hd.
        clear - Hd HinΔ1. fsetdec. }
      assert (HninQb : X `notin` ftvar_in_bskl Qb).
      { inversion Hrs; subst.
        - (* hole : the Δ1-hygiene of the fill *)
          match goal with
          | Hint : AtomSetImpl.inter Δ1 (ftvar_in_pskl ?Pf) [=] empty |- _ =>
              pose proof (ftvar_in_bskl_syn Pf) as Hfe;
              clear - Hint HinΔ1 Hfe; fsetdec
          end.
        - (* flex_r : Qb is a defined flexible, never the rigid X *)
          simpl.
          match goal with
          | Hbr : binds ?α0 (abind_flex_mono_def _) Θ |- _ =>
              assert (Hne : X <> α0)
                by (intro Heq; subst;
                    pose proof (binds_unique _ _ _ _ _ HbX Hbr
                                  (a_wf_aenv_uniq Hwfth)) as Hcon;
                    discriminate)
          end.
          clear - Hne; fsetdec. }
      assert (HinθP : X `in` ftvar_in_pskl (msubst_pskl ρ P))
        by (apply msubst_pskl_ftv_keep; assumption).
      assert (HninS : X `notin`
                ftvar_in_uskl (pskl_to_uskl (msubst_pskl ρ P))).
      { eapply ad_pat_consis_rigid_ftv_rev;
          [ exact Hwfth | exact HbX | exact Hdefs | exact Hjoin'
          | exact HninQb ]. }
      pose proof (ftvar_in_uskl_pskl (msubst_pskl ρ P)) as Hfe2.
      clear - HninS HinθP Hfe2. fsetdec. }
    exists P, Θ0. split.
    { apply a_consis__ghost_r.
      apply inter_empty_pointwise. exact Hside. }
    intros ρ1 Hid Hinc1. exists ρ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    (* precision by the re-inherit bridge (subset goal second, AFTER the
       bridge instantiates the Δ) *)
    assert (HwfθP : Θ ⨟ Δ2 ⊢ₚₛᵃ (msubst_pskl ρ P)).
    { eapply ad_wf_pskl_delta_mono;
        [ eapply ad_wf_pskl_msubst_inc;
            [ exact Hinc | exact Hwf0 | exact HwfP
            | intros X HX; exfalso; clear - HX; fsetdec ]
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
          | exact HwfθP
          | rewrite HQb; exact Hjoin' ]
      | ].
    intros γ Hγ.
    destruct (AtomSetProperties.In_dec γ Δ2) as [HγΔ2 | HγΔ2];
      [ left; exact HγΔ2 | right ].
    assert (HγΔ1 : γ `in` Δ1) by (clear - Hγ HγΔ2; fsetdec).
    assert (Hbγ : binds γ abind_tvar Θ)
      by (eapply a_inc_binds_tvar; [ exact Hinc | ];
          apply Hrig; clear - HγΔ1; fsetdec).
    split.
    + assert (Hnq : γ `notin` ftvar_in_bskl Qb)
        by (eapply ad_refine_syn_f_hole_src_target_ftv;
            [ exact Hrs | exact Hwfth
            | clear - HγΔ1; fsetdec | exact Hbγ ]).
      pose proof (ftvar_in_bskl_inh (bskl_to_pskl Qb)) as Hfe.
      pose proof (ftvar_in_pskl_bskl_to_pskl Qb) as Hfe2.
      clear - Hnq Hfe Hfe2. fsetdec.
    + intros β τ Hb.
      pose proof (Hnfdth β τ Hb) as Hi.
      clear - Hi HγΔ1. fsetdec. }
  (* ---- Layer 0d: P0 = ⊤◇.P0', P guarded : C-UnivGhostR -------------- *)
  assert (Hthdec : (exists P0', P0 = pskl_tophole P0') \/
                   (forall P0', P0 <> pskl_tophole P0')).
  { destruct P0; try (right; intros ? Hc; discriminate).
    left. eexists. reflexivity. }
  destruct Hthdec as [[P0' ->] | Hnth].
  { pose proof (ad_wf_pskl_lc HwfP) as HlcP.
    assert (Hgdec : guarded_pskl P \/ ~ guarded_pskl P).
    { destruct P; try (right; intro Hg; inversion Hg; fail).
      - left; apply guarded_pskl__unit.
      - left; apply guarded_pskl__var.
      - left; inversion HlcP; apply guarded_pskl__arrow; assumption. }
    destruct Hgdec as [HgP | HngP].
    - (* C-UnivGhostR : strip the input's ⊤◇, V drops on the input side. *)
      assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0') by (inversion HwfP0; assumption).
      assert (Hgρ : guarded_pskl (msubst_pskl ρ P))
        by (eapply guarded_pskl_msubst_inc; eauto).
      assert (HlcQb : lc_bskl Qb) by (eapply ad_refine_syn_f_lc_r; eauto).
      assert (HgQb : guarded_bskl Qb)
        by (eapply ad_pat_consis_guarded_r; eauto).
      change (ad_refine_syn_f Δ1 Θ Δ1
                (bskl_tophole (pskl_to_bskl_inh (msubst_pskl ρ P0'))) Qb)
        in Hrs.
      assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
                (pskl_to_bskl_inh (msubst_pskl ρ P0')) Qb)
        by (eapply ad_refine_syn_f_tophole_guarded_inv; eauto).
      assert (Hlt : mu_lt (mu_consis Θ ρ P0' P Θ0)
                          (mu_consis Θ ρ (pskl_tophole P0') P Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left.
        unfold V_consis.
        pose proof (Vpskl_tophole_lt Θ ρ P0'). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH F Δ1 Δ2 Θ0 P0' P ρ Θ Ψ Qb eq_refl Hwf0 HwfP0' HwfP
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hjoin Hrs' Hrp)
        as [P1 [Θ1 [Hc Hopt']]].
      exists P1, Θ1. split.
      { apply a_consis__univ_ghost_r;
          [ exact HgP | exact HnfP | exact Hc ]. }
      exact Hopt'.
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
Lemma consis_complete : forall Ψ Θ S Qb,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qb ->
  forall F Δ1 Δ2 Θ0 P0 P ρ,
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (forall X, X `in` (Δ1 `union` Δ2) -> binds X abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    S = pskl_to_uskl (msubst_pskl ρ P) ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis F Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           ad_precise_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb)).
Proof.
  intros Ψ Θ S Qb Hj F Δ1 Δ2 Θ0 P0 P ρ
    Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ HeqS Hrs Hrp.
  subst S.
  destruct (complete_mu (mu_consis Θ ρ P0 P Θ0)) as [Hc _].
  eapply Hc; try eassumption; reflexivity.
Qed.

(* ===================================================================== *)
(*  Top-level completeness of consistency, DERIVED from the bundle by     *)
(*  instantiating the augmentation to Δ1 = Δ2 = ∅, Ψ = ∅.  The paper's    *)
(*  unaugmented statement (this is the [TODO] the old bundle left open).  *)
(* ===================================================================== *)
Lemma a_consis_complete_thm : forall F Θ0 P0 P,
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  forall ρ Θ Qb,
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P)) ≈ Qb ->
    ad_refine_syn_f empty Θ empty (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb ->
    ad_refine_pskl_f empty Θ empty (msubst_pskl ρ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis F empty empty Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           Θ ⨟ empty ⊢ₚᵣᵃ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb)).
Proof.
  intros F Θ0 P0 P Hwf0 HwfP0 HwfP ρ Θ Qb Hinc Hwfth Hjoin Hrs Hrp.
  (* [Δ1 ∪ Δ2 = ∅], so rigid / no_flex_dep / flex_above_free are vacuous. *)
  assert (Hcc : exists P1 Θ1,
      a_consis F empty empty Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           ad_precise_f (empty `union` empty) Θ (empty `union` empty)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb))).
  { eapply consis_complete with (Δ1 := empty) (Δ2 := empty).
    all: try (first [ eassumption | reflexivity ]).
    all: try (intros X HX; exfalso; clear - HX; fsetdec).  (* rigid: X ∈ ∅ *)
    all: repeat intro; fsetdec. }     (* no_flex_dep / flex_above_free / Ψ *)
  destruct Hcc as [P1 [Θ1 [Hc Hopt]]].
  exists P1, Θ1. split; [ exact Hc | ].
  intros ρ1 Hid Hinc1.
  destruct (Hopt ρ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
  exists ζ. repeat split; try assumption.
  (* forget the hygiene, then shrink [∅ ∪ ∅ ⊆ ∅]. *)
  apply ad_precise_f_forget in Hprec.
  eapply ad_refine_syn_delta_mono; [ exact Hprec | clear; fsetdec ].
Qed.
