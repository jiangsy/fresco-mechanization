(** EXISTENCE for [thm:complete-consistency] — the well-founded-measure half.

    If a consistency / unification / assignment problem HAS a solution, the
    algorithm PRODUCES a derivation.  This half cannot induct on a derivation it
    does not yet have, so it runs on the WELL-FOUNDED MEASURE

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

Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_consis_complete.

Set Implicit Arguments.

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
