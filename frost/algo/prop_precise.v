(** Skeleton PRECISION and its interaction with refinement
    (full-algo-spec.tex:710-721).

    The paper defines precision as refinement between the two INHERITED
    paintings:

      Θ ⊢ P ⊑ Q   :=   Θ ⊢ inh{P} ⊳ inh{Q}

    and states [lemma:precision-preserves-refinement]: a more precise input
    skeleton refines to whatever the less precise one refines to.  This is
    the key lemma feeding completeness of consistency / type inference.

    Mechanically the lemma is an instance of TRANSITIVITY of [ad_refine_syn],
    whose crux is that the SYNTHESISED paintings are closed under refinement:
    if [syn{P} ⊳ B] then [B] is itself a synthesised painting (of a
    well-formed skeleton).  That closure is what lets the ghost rule
    [ad_refine_syn__hole] — whose right-hand side must be a [syn] painting —
    be re-applied after a further refinement step. *)

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
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Precision  [Θ ⨟ Δ ⊢ P ⊑ Q]  :=  [Θ ⨟ Δ ⊢ᵣ inh{P} ⊳ inh{Q}]            *)
(* ===================================================================== *)

Definition ad_precise (Θ : aenv) (Δ : atoms) (P Q : pskl) : Prop :=
  Θ ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh Q).

Notation "Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ Q" := (ad_precise Θ Δ P Q)
  (at level 75, Δ at level 74, P at level 74, Q at level 74,
   no associativity) : type_scope.

(** Precision is reflexive (it is refinement of a painting against itself). *)
Lemma ad_precise_refl : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ P.
Proof. intros. apply ad_refine_syn_refl_inh; auto. Qed.

(* ===================================================================== *)
(*  Support: paintings, closing, guardedness, and definition skeletons     *)
(* ===================================================================== *)

(** The synthesised painting commutes with closing (converse of the
    lngen-style [pskl_to_bskl_syn_open]). *)
Lemma pskl_to_bskl_syn_close_rec : forall P X k,
  pskl_to_bskl_syn (close_pskl_wrt_pskl_rec k X P)
  = close_bskl_wrt_bskl_rec k X (pskl_to_bskl_syn P).
Proof.
  induction P; intros; simpl; f_equal; auto;
    repeat match goal with
    | |- context [ if ?t then _ else _ ] => destruct t
    | |- context [ lt_ge_dec ?a ?b ] => destruct (lt_ge_dec a b)
    end; reflexivity.
Qed.

Lemma pskl_to_bskl_syn_close : forall P X,
  pskl_to_bskl_syn (close_pskl_wrt_pskl X P)
  = close_bskl_wrt_bskl X (pskl_to_bskl_syn P).
Proof.
  intros. unfold close_pskl_wrt_pskl, close_bskl_wrt_bskl.
  apply pskl_to_bskl_syn_close_rec.
Qed.

(** Guardedness transfers back across the synthesised painting (the
    local-closure side conditions come from the skeleton's own wf). *)
Lemma guarded_pskl_of_bskl_syn : forall P,
  lc_pskl P ->
  guarded_bskl (pskl_to_bskl_syn P) ->
  guarded_pskl P.
Proof.
  intros P Hlc Hg; destruct P; simpl in Hg; inversion Hg; subst;
    inversion Hlc; subst; constructor; auto.
Qed.

(** A flexible variable's definition is well-formed in its own context. *)
Lemma a_wf_aenv_binds_def_wf : forall Θ γ τ,
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

(** A monotype's skeleton is a well-formed skeleton.  Stated in VISIBILITY
    form: [a_wf_ptyp] puts a quantifier's variable in the CONTEXT, whereas
    [ad_wf_pskl] puts it in the Δ-slot, so a direct transfer would have to
    move a context entry into Δ — which is unsound in general (the ghost
    rules demand an EMPTY Δ).  Quantifying over the free variables instead
    sidesteps the mismatch; [ptyp_to_pskl] images carry no ghosts, so this
    is exactly what is needed. *)
Lemma a_wf_pskl_of_ptyp_vis : forall A Θ Δ,
  lc_ptyp A ->
  (forall X, X `in` ftvar_in_ptyp A -> X `in` Δ \/ a_binds_tvar X Θ) ->
  Θ ⨟ Δ ⊢ₚₛᵃ (ptyp_to_pskl A).
Proof.
  intros A Θ Δ Hlc; revert Δ; induction Hlc; intros Δ Hvis; simpl.
  - apply ad_wf_pskl__unit.
  - apply ad_wf_pskl__var. apply Hvis. simpl. fsetdec.
  - apply ad_wf_pskl__arrow;
      [ apply IHHlc1 | apply IHHlc2 ];
      intros X HX; apply Hvis; simpl; fsetdec.
  - apply ad_wf_pskl__all with (L := ftvar_in_ptyp A).
    intros X HX.
    rewrite <- ptyp_to_pskl_open.
    apply H0.
    intros Y HY.
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper
                  A (ptyp_var_f X)) as Hup.
    simpl in Hup.
    assert (HY' : Y `in` (singleton X `union` ftvar_in_ptyp A))
      by (clear - HY Hup; fsetdec).
    destruct (AtomSetImpl.union_1 HY') as [HYX | HYA].
    + apply AtomSetImpl.singleton_1 in HYX; subst.
      left. clear; fsetdec.
    + destruct (Hvis Y HYA) as [HD | Ht];
        [ left; clear - HD; fsetdec | right; exact Ht ].
Qed.

(** The skeleton of a flexible variable's definition is well-formed. *)
Lemma a_wf_ptyp_to_wf_pskl : forall Θ Δ A,
  a_wf_ptyp Θ A ->
  Θ ⨟ Δ ⊢ₚₛᵃ (ptyp_to_pskl A).
Proof.
  intros Θ Δ A H. apply a_wf_pskl_of_ptyp_vis.
  - eapply a_wf_ptyp_lc; eauto.
  - intros X HX. right. eapply a_wf_ptyp_ftv_tvarish; eauto.
Qed.

(* ===================================================================== *)
(*  STOP — the next step is BLOCKED by a counterexample.                   *)
(*                                                                         *)
(*  [lemma:precision-preserves-refinement] (full-algo-spec.tex:716) is an   *)
(*  instance of TRANSITIVITY of [ad_refine_syn].  Refinement is NOT         *)
(*  transitive: see [cex_refine_not_transitive.v], where                    *)
(*  [ad_refine_syn_not_transitive] is proved (Qed, axiom-free).  The paper's *)
(*  GhostForall rule lets a ghost be filled with the very ∀-variable that   *)
(*  rule binds, because it extends Γ but not Δ — and Δ is what the Ghost    *)
(*  rule's side condition tests.  The resulting skeleton is not             *)
(*  well-formed, so a ghost cannot refine to it.                            *)
(*                                                                         *)
(*  Flagged to the authors; the completeness development waits on the fix.  *)
(* ===================================================================== *)
