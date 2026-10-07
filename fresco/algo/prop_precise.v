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

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_stability.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_refine.
Require Import src.fresco.algo.consis.prop_soundness_consis.

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope fresco_ad_scope.

(* ===================================================================== *)
(*  Precision  [Θ ⨟ Δ ⊢ P ⊑ Q]  :=  [Θ ⨟ Δ ⊢ᵣ inh{P} ⊳ inh{Q}]            *)
(* ===================================================================== *)

Definition ad_precise (Θ : aenv) (Δ : atoms) (P Q : pskl) : Prop :=
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh Q) }}ad.

Notation "{{ Θ ⨟ Δ ⊢ₚᵣ P ⊑ Q }}ad" := (ad_precise Θ Δ P Q)
  (at level 0, Δ at level 74, P at level 74, Q at level 74,
   format "'{{'  Θ  ⨟  Δ  ⊢ₚᵣ  P  ⊑  Q  '}}ad'") : fresco_ad_scope.

(** Precision is reflexive (it is refinement of a painting against itself). *)
Lemma ad_precise_refl : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ₚᵣ P ⊑ P }}ad.
Proof. intros. apply ad_refine_syn_refl_inh; auto. Qed.

(* ===================================================================== *)
(*  Support: paintings, closing, guardedness, and definition skeletons     *)
(* ===================================================================== *)

(** The synthesised painting commutes with closing (converse of the
    lngen-style [pskl_to_bskl_syn_open]). *)
Lemma pskl_to_bskl_syn_close_rec : forall P α' k,
  pskl_to_bskl_syn (close_pskl_wrt_pskl_rec k α' P)
  = close_bskl_wrt_bskl_rec k α' (pskl_to_bskl_syn P).
Proof.
  induction P; intros; simpl; f_equal; auto;
    repeat match goal with
    | |- context [ if ?t then _ else _ ] => destruct t
    | |- context [ lt_ge_dec ?a ?b ] => destruct (lt_ge_dec a b)
    end; reflexivity.
Qed.

Lemma pskl_to_bskl_syn_close : forall P α,
  pskl_to_bskl_syn (close_pskl_wrt_pskl α P)
  = close_bskl_wrt_bskl α (pskl_to_bskl_syn P).
Proof.
  intros. unfold close_pskl_wrt_pskl, close_bskl_wrt_bskl.
  apply pskl_to_bskl_syn_close_rec.
Qed.

(** A flexible variable's definition is well-formed in its own context. *)
(** A monotype's skeleton is a well-formed skeleton.  Stated in VISIBILITY
    form: [a_wf_ptyp] puts a quantifier's variable in the CONTEXT, whereas
    [a_wf_pskl] puts it in the Δ-slot, so a direct transfer would have to
    move a context entry into Δ — which is unsound in general (the ghost
    rules demand an EMPTY Δ).  Quantifying over the free variables instead
    sidesteps the mismatch; [ptyp_to_pskl] images carry no ghosts, so this
    is exactly what is needed. *)
Lemma a_scope_pskl_of_ptyp_vis : forall A Θ Δ,
  lc_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> α `in` Δ \/ a_binds_tvar α Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl A) }}a.
Proof.
  intros A Θ Δ Hlc; revert Δ; induction Hlc; intros Δ Hvis; simpl.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. apply Hvis. simpl. fsetdec.
  - apply a_wf_pskl__arrow;
      [ apply IHHlc1 | apply IHHlc2 ];
      intros α Hα; apply Hvis; simpl; fsetdec.
  - apply a_wf_pskl__all with (L := ftvar_in_ptyp A).
    intros α Hα.
    rewrite <- ptyp_to_pskl_open.
    apply H0.
    intros β Hβ.
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper
                  A (ptyp_var_f α)) as Hup.
    simpl in Hup.
    assert (HY' : β `in` (singleton α `union` ftvar_in_ptyp A))
      by (clear - Hβ Hup; fsetdec).
    destruct (union_1 HY') as [HYX | HYA].
    + apply singleton_1 in HYX; subst.
      left. clear; fsetdec.
    + destruct (Hvis β HYA) as [HD | Ht];
        [ left; clear - HD; fsetdec | right; exact Ht ].
Qed.

(** The skeleton of a flexible variable's definition is well-formed. *)
Lemma a_wf_ptyp_to_wf_pskl : forall Θ Δ A,
  a_wf_ptyp Θ A ->
  {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl A) }}a.
Proof.
  intros Θ Δ A H. apply a_scope_pskl_of_ptyp_vis.
  - eapply a_wf_ptyp_lc; eauto.
  - intros α Hα. right. eapply a_wf_ptyp_ftv_tvarish; eauto.
Qed.

(* ===================================================================== *)
(*  Refinement lands in a SYNTHESISED painting (shape only).               *)
(*                                                                         *)
(*  NB no well-formedness here — and none is derivable: refinement does NOT *)
(*  preserve well-formedness (cex_refine_not_transitive.v).  That is why    *)
(*  well-formedness is carried by the STATEMENTS below rather than by the   *)
(*  rules, exactly as the paper's GhostForall comment intends (“we already  *)
(*  required well-formedness separately”).                                  *)
(* ===================================================================== *)

Lemma ad_refine_syn_syn_l : forall Θ Δ Qb Q,
  {{ Θ ⨟ Δ ⊢ᵣ Qb ⊳ Q }}ad ->
  forall P, Qb = pskl_to_bskl_syn P ->
  exists P', Q = pskl_to_bskl_syn P'.
Proof.
  intros Θ Δ Qb Q Href; induction Href; intros P0 Heq.
  - (* unit *) exists pskl_unit. reflexivity.
  - (* var *) exists (pskl_var_f α). reflexivity.
  - (* arrow *)
    destruct P0 as [ | | | Pa Pb | | | ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (IHHref1 _ eq_refl) as [Pa' ->].
    destruct (IHHref2 _ eq_refl) as [Pb' ->].
    exists (pskl_arrow Pa' Pb'). reflexivity.
  - (* all : a syn painting is never [bskl_all_inh] *)
    destruct P0; simpl in Heq; discriminate.
  - (* hole : the fill IS a syn painting *)
    exists P. reflexivity.
  - (* tophole_remove *)
    destruct P0 as [ | | | | | | Pt ]; simpl in Heq; try discriminate.
    inversion Heq; subst. exact (IHHref _ eq_refl).
  - (* tophole_fill : close the body over the fresh variable *)
    destruct P0 as [ | | | | | | Pt ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    pick fresh α for (L `union` dom Θ `union` ftvar_in_bskl P).
    destruct (H0 α ltac:(auto) (pskl_tophole Pt) eq_refl) as [RX HeqRX].
    exists (pskl_all_syn (close_pskl_wrt_pskl α RX)).
    simpl. rewrite pskl_to_bskl_syn_close. rewrite <- HeqRX.
    rewrite close_bskl_wrt_bskl_open_bskl_wrt_bskl;
      [ reflexivity | clear - Fr; fsetdec ].
  - (* tophole_keep *)
    destruct P0 as [ | | | | | | Pt ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (IHHref _ eq_refl) as [R ->].
    exists (pskl_tophole R). reflexivity.
  - (* flex_l : [ptyp_to_bskl_syn] IS a syn painting, by definition *)
    exact (IHHref (ptyp_to_pskl τ) eq_refl).
  - (* flex_r : the result is a bare variable *)
    exists (pskl_var_f α). reflexivity.
Qed.

(* ===================================================================== *)
(*  The Δ-discipline: Δ holds the refinement-local ∀-variables, which are   *)
(*  fresh for Θ.  Two consequences we need to re-apply the Ghost rule,      *)
(*  whose fill must be well-formed at the EMPTY Δ.                          *)
(* ===================================================================== *)

(** Δ-variables the skeleton does not mention may be dropped. *)
Lemma a_wf_pskl_delta_shrink : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Δ', (forall α, α `in` Δ -> α `in` ftvar_in_pskl P -> α `in` Δ') ->
  {{ Θ ⨟ Δ' ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P H; induction H; intros Δ' Hkeep.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; apply Hkeep; auto; simpl; fsetdec
                             | right; exact Htv ].
  - apply a_wf_pskl__arrow;
      [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      intros α Hα HP; apply Hkeep; auto; simpl; fsetdec.
  - apply a_wf_pskl__all with (L := L `union` ftvar_in_pskl P).
    intros α Hα. apply H0; auto.
    intros β Hβ HP.
    destruct (β == α) as [->|Hne]; [ clear; fsetdec | ].
    assert (HβΔ : β `in` Δ) by (clear - Hβ Hne; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hup.
    simpl in Hup.
    assert (HYP : β `in` ftvar_in_pskl P)
      by (assert (β `in` (singleton α `union` ftvar_in_pskl P))
            by (clear - HP Hup; fsetdec);
          clear - H1 Hne; fsetdec).
    assert (β `in` Δ') by (apply Hkeep; auto).
    clear - H1; fsetdec.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; [ exact H | exact H0 ].
Qed.

(** A skeleton well-formed at the EMPTY Δ mentions only Θ-variables; so if
    Δ is disjoint from Θ (the ∀-variables are refinement-local), it is
    Δ-free. *)
Lemma a_wf_pskl_empty_delta_free : forall Θ Δ P,
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  Δ ∩ ftvar_in_pskl P [=] empty.
Proof.
  intros Θ Δ P Hwf Hdisj.
  apply inter_empty_pointwise. intros α HαΔ.
  intro HXP.
  destruct (a_wf_pskl_ftv_tvarish Hwf HXP) as [Hemp | Htv];
    [ clear - Hemp; fsetdec | ].
  apply (Hdisj α HαΔ).
  destruct Htv as [Hb | [Hb | [τ Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

(** With a SYNTHESISED painting on the left the [all] rule can never fire (a
    syn painting has no [bskl_all_inh]), so Δ never grows: Δ-freeness
    propagates across the refinement. *)
Lemma ad_refine_syn_syn_delta_free : forall Θ Δ Qb Q,
  {{ Θ ⨟ Δ ⊢ᵣ Qb ⊳ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall F, Qb = pskl_to_bskl_syn F ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  Δ ∩ ftvar_in_bskl Qb [=] empty ->
  Δ ∩ ftvar_in_bskl Q [=] empty.
Proof.
  intros Θ Δ Qb Q Href; induction Href; intros Hwf F Heq Hdisj Hfree.
  - (* unit *) simpl. clear; fsetdec.
  - (* var *) exact Hfree.
  - (* arrow *)
    destruct F as [ | | | Fa Fb | | | ]; simpl in Heq; try discriminate.
    inversion Heq; subst. simpl in Hfree |- *.
    apply inter_empty_pointwise. intros α Hα.
    assert (H1 : α `notin` ftvar_in_bskl (pskl_to_bskl_syn Fa)
                 `union` ftvar_in_bskl (pskl_to_bskl_syn Fb))
      by (clear - Hα Hfree; fsetdec).
    assert (Ha := IHHref1 Hwf Fa eq_refl Hdisj
             ltac:(apply inter_empty_pointwise; intros β Hβ;
                   clear - Hβ Hfree; solve_notin_auto)).
    assert (Hb := IHHref2 Hwf Fb eq_refl Hdisj
             ltac:(apply inter_empty_pointwise; intros β Hβ;
                   clear - Hβ Hfree; solve_notin_auto)).
    clear - Hα Ha Hb. fsetdec.
  - (* all : impossible — a syn painting is never [bskl_all_inh] *)
    destruct F; simpl in Heq; discriminate.
  - (* hole : the fill is wf at the EMPTY Δ, hence Δ-free *)
    rewrite ftvar_pskl_to_bskl_syn.
    eapply a_wf_pskl_empty_delta_free; [ exact H | exact Hdisj ].
  - (* tophole_remove *)
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    eapply IHHref; [ exact Hwf | reflexivity | exact Hdisj
                   | simpl in Hfree; exact Hfree ].
  - (* tophole_fill : the bound variable is fresh, and gets closed over *)
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    pick fresh α for (L `union` Δ `union` dom Θ `union` ftvar_in_bskl P).
    assert (HdisjX : forall β, β `in` Δ ->
                     β `notin` dom ((α ~ abind_tvar) ++ Θ)).
    { intros β Hβ. simpl.
      assert (HYX : β <> α) by (clear - Hβ Fr; fsetdec).
      assert (HβΘ : β `notin` dom Θ) by (apply Hdisj; exact Hβ).
      clear - HYX HβΘ. fsetdec. }
    assert (Hsub : Δ ∩
                     (ftvar_in_bskl (open_bskl_wrt_bskl P (bskl_var_f α)))
                   [=] empty).
    { eapply (H0 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)
                (pskl_tophole Ft) eq_refl HdisjX).
      simpl in Hfree |- *. exact Hfree. }
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower P (bskl_var_f α))
      as Hlow.
    simpl.
    apply inter_empty_pointwise. intros β Hβ HYP.
    assert (HYo : β `in` ftvar_in_bskl (open_bskl_wrt_bskl P (bskl_var_f α)))
      by (clear - HYP Hlow; fsetdec).
    clear - Hβ HYo Hsub. fsetdec.
  - (* tophole_keep *)
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst. simpl.
    eapply IHHref; [ exact Hwf | reflexivity | exact Hdisj
                   | simpl in Hfree; exact Hfree ].
  - (* flex_l : the definition's painting IS a syn painting; it is wf in Θ,
       hence (Δ being fresh for Θ) Δ-free *)
    eapply IHHref; [ exact Hwf | reflexivity | exact Hdisj | ].
    unfold ptyp_to_bskl_syn. rewrite ftvar_pskl_to_bskl_syn.
    eapply a_wf_pskl_empty_delta_free; [ | exact Hdisj ].
    apply a_wf_ptyp_to_wf_pskl.
    eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact H ].
  - (* flex_r : the result is a bare variable, BOUND in Θ — and Δ is fresh
       for Θ, so it is not a Δ-variable *)
    simpl. apply inter_empty_pointwise. intros β Hβ Hβα.
    assert (HeqY : β = α) by (clear - Hβα; fsetdec). subst.
    apply (Hdisj α Hβ). apply binds_In in H. exact H.
Qed.

(* ===================================================================== *)
(*  THE CRUX, in the shape the Ghost rule needs.                           *)
(*                                                                         *)
(*  To re-apply [ad_refine_syn__hole] after a further refinement step we    *)
(*  need the new fill to be a syn painting of a skeleton well-formed at the *)
(*  EMPTY Δ.  Refinement does NOT give us that (it does not preserve        *)
(*  well-formedness at all — cex_refine_not_transitive.v).  So we ASSUME    *)
(*  well-formedness of the result — the paper's “we already required        *)
(*  well-formedness separately” — and recover the empty-Δ form from the     *)
(*  Δ-discipline: Δ holds refinement-local ∀-variables, fresh for Θ, and    *)
(*  a syn-headed refinement never grows Δ, so the result stays Δ-free.      *)
(* ===================================================================== *)

Lemma ad_refine_syn_syn_l_wf : forall Θ Δ P Q,
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_syn P) ⊳ Q }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  exists G, Q = pskl_to_bskl_syn G /\ {{ Θ ⨟ empty ⊢ₚₛ G }}a.
Proof.
  intros Θ Δ P Q Href Hwf Hdisj HwfF HwfB.
  destruct (ad_refine_syn_syn_l Href P eq_refl) as [G HeqG].
  exists G. split; [ exact HeqG | ].
  assert (Hdf : Δ ∩ ftvar_in_bskl Q [=] empty).
  { eapply ad_refine_syn_syn_delta_free;
      [ exact Href | exact Hwf | reflexivity | exact Hdisj | ].
    rewrite ftvar_pskl_to_bskl_syn.
    eapply a_wf_pskl_empty_delta_free; [ exact HwfF | exact Hdisj ]. }
  subst Q.
  rewrite bskl_to_pskl_pskl_to_bskl_syn in HwfB.
  rewrite ftvar_pskl_to_bskl_syn in Hdf.
  eapply a_wf_pskl_delta_shrink; [ exact HwfB | ].
  intros α HαΔ HXG. exfalso. clear - HαΔ HXG Hdf. fsetdec.
Qed.

(* ===================================================================== *)
(*  TRANSITIVITY of refinement, under the paper's external wf condition.   *)
(*                                                                         *)
(*  Refinement is NOT transitive outright (cex_refine_not_transitive.v).   *)
(*  It IS transitive once the result is required to be well-formed — which *)
(*  declarative.tex:1427 requires of every refinement judgment anyway.      *)
(*                                                                         *)
(*  Structure: OUTER induction on the second derivation; INNER induction on *)
(*  the first, to peel the left-hand administrative rules [tophole_remove]  *)
(*  and [flex_l] (which shrink the left skeleton while the right stands     *)
(*  still).  Every case whose left side is a GHOST is discharged by         *)
(*  [ad_refine_syn_syn_l_wf] — that is what the crux is for.                *)
(* ===================================================================== *)

(** The left-hand administrative rules, packaged: whatever a syn painting
    refines to, a ghost refines to as well (given the result is well-formed). *)
Lemma ad_refine_syn_hole_l : forall Θ Δ P Qr,
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_syn P) ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Qr) }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ bskl_hole ⊳ Qr }}ad.
Proof.
  intros Θ Δ P Qr Href Hwf Hdisj HwfF HwfQr.
  destruct (ad_refine_syn_syn_l_wf Href Hwf Hdisj HwfF HwfQr) as [G [-> HwfG]].
  apply ad_refine_syn__hole. exact HwfG.
Qed.

Lemma ad_refine_syn_trans : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣ Qm ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Qr) }}a ->
  forall Ql,
  {{ Θ ⨟ Δ ⊢ᵣ Ql ⊳ Qm }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Ql ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Hr.
  induction Hr; intros Hwf Hdisj HwfQr Ql Hp.
  - (* unit : Qm = Qr = unit *) exact Hp.
  - (* var *) exact Hp.
  - (* arrow *)
    rename Q1 into Qa. rename Q2 into Qb. rename P1 into Pa. rename P2 into Pb.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_arrow Qa Qb) ⊳ (bskl_arrow Pa Pb) }}ad)
      by (apply ad_refine_syn__arrow; assumption).
    remember (bskl_arrow Qa Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + inversion HM; subst. simpl in HwfQr.
      inversion HwfQr as [ | | Θw Δw Pw1 Pw2 Hw1 Hw2 | | | ]; subst.
      apply ad_refine_syn__arrow; [ apply IHHr1 | apply IHHr2 ]; auto.
    + eapply ad_refine_syn_hole_l with (P := P);
        [ exact Hrr | exact Hwf | exact Hdisj | eassumption
        | exact HwfQr ].
    + apply ad_refine_syn__tophole_remove. apply IHHp; auto.
    + eapply ad_refine_syn__flex_l;
        [ eassumption | ]. apply IHHp; auto.
  - (* all : ∀^inh Q ⊳ ∀^inh P *)
    rename Q into Qb. rename P into Pb.
    remember (bskl_all_inh Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate;
      [ | destruct P; simpl in HM; discriminate | | ].
    + (* ∀ ⊳ ∀ *)
      inversion HM; subst. simpl in HwfQr.
      inversion HwfQr as [ | | | L2 Θw Δw Pw Hbody | | ]; subst.
      apply ad_refine_syn__all
        with (L := L `union` L0 `union` L2 `union` dom Θ `union` Δ).
      intros α Hα.
      apply H0 with (α := α); auto.
      { intros β Hβ.
        destruct (β == α) as [->|Hne]; [ clear - Hα; fsetdec | ].
        apply Hdisj. clear - Hβ Hne. fsetdec. }
      { rewrite bskl_to_pskl_open. apply Hbody. clear - Hα; fsetdec. }
    + apply ad_refine_syn__tophole_remove. apply IHHp; auto.
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* hole : Qm = □, Qr = syn P *)
    rename P into Pf.
    remember (@bskl_hole) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + (* □ ⊳ □ : the fill of Hp must itself be a ghost *)
      destruct P; simpl in HM; try discriminate.
      apply ad_refine_syn__hole. assumption.
    + apply ad_refine_syn__tophole_remove. apply IHHp; auto.
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* tophole_remove : Qm = ∀◇Q, Qr from Q ⊳ Qr *)
    rename Q into Qb. rename P into Pb.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Qb) ⊳ Pb }}ad)
      by (apply ad_refine_syn__tophole_remove; assumption).
    remember (bskl_tophole Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_hole_l with (P := P);
        [ exact Hrr | exact Hwf | exact Hdisj | eassumption
        | exact HwfQr ].
    + apply ad_refine_syn__tophole_remove. apply IHHp; auto.
    + (* tophole_keep on the left : peel both *)
      inversion HM; subst.
      apply ad_refine_syn__tophole_remove. apply IHHr; auto.
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* tophole_fill : ∀◇Q ⊳ ∀^syn P *)
    rename Q into Qb. rename P into Pb.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Qb) ⊳ (bskl_all_syn Pb) }}ad)
      by (eapply ad_refine_syn__tophole_fill with (L := L); assumption).
    remember (bskl_tophole Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_hole_l with (P := P);
        [ exact Hrr | exact Hwf | exact Hdisj | eassumption
        | exact HwfQr ].
    + apply ad_refine_syn__tophole_remove. apply IHHp; auto.
    + (* tophole_keep on the left : rebuild the ∀ *)
      inversion HM; subst.
      simpl in HwfQr.
      inversion HwfQr as [ | | | L2 Θw Δw Pw Hbody | | ]; subst.
      apply ad_refine_syn__tophole_fill
        with (L := L `union` L2 `union` dom Θ `union` Δ).
      intros α Hα.
      apply H0 with (α := α); auto.
      { apply a_wf_aenv__tvar; auto. }
      { intros β Hβ. simpl.
        assert (HYX : β <> α) by (clear - Hβ Hα; fsetdec).
        assert (HβΘ : β `notin` dom Θ) by (apply Hdisj; exact Hβ).
        clear - HYX HβΘ. fsetdec. }
      { rewrite bskl_to_pskl_open.
        eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_reassoc
                     (Hbody α ltac:(clear - Hα; solve_notin_auto)) α)
          | clear; fsetdec ]. }
      { eapply ad_refine_syn_weaken;
          [ apply ad_refine_syn__tophole_keep; eassumption
          | intros y b Hb; unfold binds; right; exact Hb ]. }
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* tophole_keep : ∀◇Q ⊳ ∀◇P *)
    rename Q into Qb. rename P into Pb.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Qb) ⊳ (bskl_tophole Pb) }}ad)
      by (apply ad_refine_syn__tophole_keep; assumption).
    remember (bskl_tophole Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_hole_l with (P := P);
        [ exact Hrr | exact Hwf | exact Hdisj | eassumption
        | exact HwfQr ].
    + apply ad_refine_syn__tophole_remove. apply IHHp; auto.
    + inversion HM; subst.
      simpl in HwfQr.
      inversion HwfQr as [ | | | | | Θw Δw Pw Hg Hwb ]; subst.
      apply ad_refine_syn__tophole_keep; [ assumption | ].
      apply IHHr; auto.
      eapply a_wf_pskl_delta_mono; [ exact Hwb | clear; fsetdec ].
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* flex_l : Qm = α̂ with α̂ := τ *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ Q }}ad)
      by (eapply ad_refine_syn__flex_l; eassumption).
    remember (bskl_var_f α) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + (* var ⊳ var : rebuild the lookup *)
      inversion HM; subst.
      eapply ad_refine_syn__flex_l; eassumption.
    + eapply ad_refine_syn_hole_l with (P := P);
        [ exact Hrr | exact Hwf | exact Hdisj | eassumption
        | exact HwfQr ].
    + apply ad_refine_syn__tophole_remove. apply IHHp; auto.
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
    + (* flex_r on the left : the two definitions coincide *)
      inversion HM; subst.
      match goal with
      | Hb1 : binds ?a (abind_flex_mono_def ?t1) Θ,
        Hb2 : binds ?a (abind_flex_mono_def ?t2) Θ |- _ =>
          assert (Heqτ : t1 = t2) by
            (pose proof (a_wf_aenv_uniq Hwf) as Hu;
             pose proof (binds_unique _ _ _ _ _ Hb1 Hb2 Hu) as He;
             inversion He; reflexivity)
      end.
      subst.
      apply IHHr; auto.
  - (* flex_r : Qr = α̂ with α̂ := τ; recurse into the definition *)
    eapply ad_refine_syn__flex_r; [ eassumption | ].
    apply IHHr; auto.
    unfold ptyp_to_bskl_syn. rewrite bskl_to_pskl_pskl_to_bskl_syn.
    apply a_wf_ptyp_to_wf_pskl.
    eapply a_wf_aenv_binds_def_wf; [ exact Hwf | eassumption ].
Qed.

(* ===================================================================== *)
(*  lemma:precision-preserves-refinement (full-algo-spec.tex:716)          *)
(*                                                                         *)
(*  "If Θ ⊢ P ⊑ Q and Θ ⊢ inh{Q} ⊳ bid{A}, then Θ ⊢ inh{P} ⊳ bid{A}."      *)
(*                                                                         *)
(*  Precision is DEFINED as refinement between the two inherited paintings, *)
(*  so this is an instance of transitivity — available exactly because the   *)
(*  result is required to be well-formed, which declarative.tex:1427         *)
(*  requires of every refinement judgment anyway.                            *)
(* ===================================================================== *)

Corollary ad_precise_preserves_refine : forall Θ Δ P P' Q,
  {{ Θ ⨟ Δ ⊢ₚᵣ P ⊑ P' }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P') ⊳ Q }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Q }}ad.
Proof.
  intros Θ Δ P P' Q Hprec Href Hwf Hdisj HwfA.
  eapply ad_refine_syn_trans;
    [ exact Href | exact Hwf | exact Hdisj | exact HwfA | exact Hprec ].
Qed.

(** ⚙ Local copy of prop_pat_sub.v's [ftvar_ptyp_to_pskl] —
    prop_pat_sub sits ABOVE this file in the dependency order. *)
(* ===================================================================== *)
(*  The UNCOLOURED mirror of the [ad_refine_syn_trans] chain.              *)
(*                                                                         *)
(*  [ad_refine_pskl]'s [__hole] fill is a plain wf skeleton (no painting    *)
(*  shape), so the crux needs NO analogue of [ad_refine_syn_syn_l]: the     *)
(*  ghost-left package reduces to Δ-freeness propagation alone.  ⚠️ Unlike  *)
(*  the syn level — where a syn subject kills the [__all] row outright —    *)
(*  the pskl [__all] row DOES fire and grows Δ, so the Δ-freeness           *)
(*  statement tracks a set DECOUPLED from the judgement's ambient Δ.       *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  TRANSITIVITY of the uncoloured refinement, under the same external wf  *)
(*  condition as [ad_refine_syn_trans] — GENERALIZED over a reassociation  *)
(*  [Θ ⨟ Δ ↦ Θx ⨟ Δx] (Hmap: bindings preserved; Hsplit: every source      *)
(*  Δ-variable is either still in Δx or has become a RIGID of Θx).         *)
(* ===================================================================== *)

Lemma a_wf_pskl_all_inv : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}a ->
  exists L, forall α, α `notin` L ->
    {{ Θ ⨟ (add α Δ) ⊢ₚₛ (open_pskl_wrt_pskl P (pskl_var_f α)) }}a.
Proof. intros * H; inversion H; subst; eauto. Qed.

(* ===================================================================== *)
(*  Precision DROPS to the uncoloured level: [inh P' ⊳ inh P] implies      *)
(*  [P' ⊳ P] — the pskl [__hole] fill demands strictly less (any wf        *)
(*  skeleton vs a synthesised painting).                                   *)
(* ===================================================================== *)

