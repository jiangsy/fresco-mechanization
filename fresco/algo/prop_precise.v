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
(** A monotype's skeleton is well-formed wherever its free variables are
    bound.  [ptyp_to_pskl] images carry no ghosts, so the Δ-slot (read only
    by the [∀◇] rule) plays no role, and a quantifier's variable goes into
    the context exactly as [a_wf_ptyp] puts it there. *)
Lemma a_scope_pskl_of_ptyp_vis : forall A Θ Δ,
  lc_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl A) }}a.
Proof.
  intros A Θ Δ Hlc; revert Θ Δ; induction Hlc; intros Θ Δ Hvis; simpl.
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
    apply a_binds_tvar_cons_tvar.
    destruct (union_1 HY') as [HYX | HYA].
    + apply singleton_1 in HYX; subst. left; reflexivity.
    + right. apply Hvis. exact HYA.
Qed.

(** The skeleton of a flexible variable's definition is well-formed. *)
Lemma a_wf_ptyp_to_wf_pskl : forall Θ Δ A,
  a_wf_ptyp Θ A ->
  {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl A) }}a.
Proof.
  intros Θ Δ A H. apply a_scope_pskl_of_ptyp_vis.
  - eapply a_wf_ptyp_lc; eauto.
  - intros α Hα. eapply a_wf_ptyp_ftv_tvarish; eauto.
Qed.

(* ===================================================================== *)
(*  Refinement lands in a SYNTHESISED painting (shape only).               *)
(*                                                                         *)
(*  NB no well-formedness here — and none is derivable: the rules alone do *)
(*  NOT preserve well-formedness ([ad_refine_syn_output_not_wf],            *)
(*  cex_refine_not_transitive.v).  That is why well-formedness of both     *)
(*  sides — the paper's presupposition — is carried by the STATEMENTS       *)
(*  below rather than by the rules.                                         *)
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
    pick fresh α for (L `union` dom Θ `union` ftvar_in_bskl Q').
    destruct (H1 α ltac:(auto) (pskl_tophole Pt) eq_refl) as [RX HeqRX].
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
(*  The Δ-discipline.  The Ghost rule's side condition is Δ-freeness of    *)
(*  the fill ([Δ ∩ ftv P [=] empty]), so to re-apply it after a further    *)
(*  refinement step we must know Δ-freeness propagates.  It does, as long  *)
(*  as no flexible variable is a Δ-variable and no flexible definition     *)
(*  mentions one — the two hypotheses [Hdefs] / [Hflex] below.  Both hold  *)
(*  when Δ is fresh for Θ, and both survive the [all] rule (which puts its *)
(*  variable into Θ AND Δ), whereas freshness for Θ does not.              *)
(* ===================================================================== *)

(** Δ-variables the skeleton does not mention may be dropped.  Under the
    paper's rules a SMALLER Δ is always easier (Δ is read only by the [∀◇]
    rule, which removes it from the context), so [Hkeep] is no longer the
    content; the new [Δ' [<=] Δ] is. *)
Lemma a_wf_pskl_delta_shrink : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Δ', (forall α, α `in` Δ -> α `in` ftvar_in_pskl P -> α `in` Δ') ->
  Δ' [<=] Δ ->
  {{ Θ ⨟ Δ' ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P H Δ' _ Hsub.
  eapply a_wf_pskl_delta_mono; [ exact H | ].
  intros α _ Hα. apply Hsub. exact Hα.
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

(** A [tvar] head adds no flexible definition. *)
Lemma binds_flex_def_cons_tvar_inv : forall α β τ Θ,
  binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ) ->
  binds β (abind_flex_mono_def τ) Θ.
Proof.
  intros * Hb.
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
    [ discriminate | exact Hb' ].
Qed.

(** The two Δ-hypotheses follow from Δ being fresh for a well-formed Θ. *)
Lemma delta_fresh_flex_defs : forall Θ Δ,
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) /\
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ).
Proof.
  intros Θ Δ Hwf Hdisj. split.
  - intros β τ Hb. apply inter_empty_pointwise. intros γ Hγ Hγτ.
    apply (Hdisj γ Hγ). apply a_binds_tvar_in_dom.
    eapply a_wf_ptyp_ftv_tvarish;
      [ eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb ] | exact Hγτ ].
  - intros β τ Hβ Hb. apply (Hdisj β Hβ). apply binds_In in Hb. exact Hb.
Qed.

(** ... and survive a [tvar] head that leaves Δ alone ([tophole_fill]) ... *)
Lemma delta_flex_defs_cons_tvar : forall α Θ Δ,
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  (forall β τ, binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ) ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) /\
  (forall β τ, β `in` Δ ->
     ~ binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ)).
Proof.
  intros α Θ Δ Hdefs Hflex. split.
  - intros β τ Hb. apply binds_flex_def_cons_tvar_inv in Hb.
    exact (Hdefs β τ Hb).
  - intros β τ Hβ Hb. apply binds_flex_def_cons_tvar_inv in Hb.
    exact (Hflex β τ Hβ Hb).
Qed.

(** ... and a fresh [tvar] head that also enters Δ ([all]). *)
Lemma delta_flex_defs_cons_tvar_add : forall α Θ Δ,
  {{ ⊢ Θ }}a ->
  α `notin` dom Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  (forall β τ, binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ) ->
     (add α Δ) ∩ ftvar_in_ptyp τ [=] empty) /\
  (forall β τ, β `in` (add α Δ) ->
     ~ binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ)).
Proof.
  intros α Θ Δ Hwf Hα Hdefs Hflex. split.
  - intros β τ Hb. apply binds_flex_def_cons_tvar_inv in Hb.
    pose proof (Hdefs β τ Hb) as Hd.
    apply inter_empty_pointwise. intros γ Hγ Hγτ.
    destruct (γ == α) as [-> | Hne].
    + apply Hα. apply a_binds_tvar_in_dom.
      eapply a_wf_ptyp_ftv_tvarish;
        [ eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb ]
        | exact Hγτ ].
    + assert (HγΔ : γ `in` Δ) by (clear - Hγ Hne; fsetdec).
      assert (Hin : γ `in` Δ ∩ ftvar_in_ptyp τ) by (apply inter_3; auto).
      rewrite Hd in Hin. clear - Hin. fsetdec.
  - intros β τ Hβ Hb. apply binds_flex_def_cons_tvar_inv in Hb.
    destruct (β == α) as [-> | Hne].
    + apply Hα. apply binds_In in Hb. exact Hb.
    + apply (Hflex β τ); [ clear - Hβ Hne; fsetdec | exact Hb ].
Qed.

(** With a SYNTHESISED painting on the left the [all] rule can never fire (a
    syn painting has no [bskl_all_inh]), so Δ never grows: Δ-freeness
    propagates across the refinement. *)
Lemma ad_refine_syn_syn_delta_free_gen : forall Θ Δ Qb Q,
  {{ Θ ⨟ Δ ⊢ᵣ Qb ⊳ Q }}ad ->
  forall F, Qb = pskl_to_bskl_syn F ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  Δ ∩ ftvar_in_bskl Qb [=] empty ->
  Δ ∩ ftvar_in_bskl Q [=] empty.
Proof.
  intros Θ Δ Qb Q Href; induction Href; intros F Heq Hdefs Hflex Hfree.
  - (* unit *) simpl. clear; fsetdec.
  - (* var *) exact Hfree.
  - (* arrow *)
    destruct F as [ | | | Fa Fb | | | ]; simpl in Heq; try discriminate.
    inversion Heq; subst. simpl in Hfree |- *.
    apply inter_empty_pointwise. intros α Hα.
    assert (Ha := IHHref1 Fa eq_refl Hdefs Hflex
             ltac:(apply inter_empty_pointwise; intros β Hβ;
                   clear - Hβ Hfree; solve_notin_auto)).
    assert (Hb := IHHref2 Fb eq_refl Hdefs Hflex
             ltac:(apply inter_empty_pointwise; intros β Hβ;
                   clear - Hβ Hfree; solve_notin_auto)).
    clear - Hα Ha Hb. fsetdec.
  - (* all : impossible — a syn painting is never [bskl_all_inh] *)
    destruct F; simpl in Heq; discriminate.
  - (* hole : Δ-freeness of the fill is the rule's own premise *)
    rewrite ftvar_pskl_to_bskl_syn. exact H.
  - (* tophole_remove *)
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    eapply IHHref; [ reflexivity | exact Hdefs | exact Hflex
                   | simpl in Hfree; exact Hfree ].
  - (* tophole_fill : the bound variable is fresh, and gets closed over *)
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    pick fresh α for (L `union` Δ `union` ftvar_in_bskl Q').
    destruct (@delta_flex_defs_cons_tvar α Θ Δ Hdefs Hflex) as [Hdefs' Hflex'].
    assert (Hsub : Δ ∩
                     (ftvar_in_bskl (open_bskl_wrt_bskl Q' (bskl_var_f α)))
                   [=] empty).
    { eapply (H1 α ltac:(auto) (pskl_tophole Ft) eq_refl Hdefs' Hflex').
      simpl in Hfree |- *. exact Hfree. }
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q' (bskl_var_f α))
      as Hlow.
    simpl.
    apply inter_empty_pointwise. intros β Hβ HYP.
    assert (HYo : β `in` ftvar_in_bskl (open_bskl_wrt_bskl Q' (bskl_var_f α)))
      by (clear - HYP Hlow; fsetdec).
    clear - Hβ HYo Hsub. fsetdec.
  - (* tophole_keep *)
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst. simpl.
    eapply IHHref; [ reflexivity | exact Hdefs | exact Hflex
                   | simpl in Hfree; exact Hfree ].
  - (* flex_l : the definition's painting IS a syn painting, and Δ-free *)
    eapply IHHref; [ reflexivity | exact Hdefs | exact Hflex | ].
    unfold ptyp_to_bskl_syn. rewrite ftvar_pskl_to_bskl_syn.
    pose proof (Hdefs α τ H) as Hd.
    apply inter_empty_pointwise. intros β Hβ Hβτ.
    rewrite ftvar_ptyp_to_pskl in Hβτ.
    assert (Hin : β `in` Δ ∩ ftvar_in_ptyp τ) by (apply inter_3; auto).
    rewrite Hd in Hin. clear - Hin. fsetdec.
  - (* flex_r : the result is a bare FLEXIBLE variable, never in Δ *)
    simpl. apply inter_empty_pointwise. intros β Hβ Hβα.
    assert (HeqY : β = α) by (clear - Hβα; fsetdec). subst.
    exact (Hflex α τ Hβ H).
Qed.

(** The same, with the two Δ-hypotheses read off Δ's freshness for Θ. *)
Lemma ad_refine_syn_syn_delta_free : forall Θ Δ Qb Q,
  {{ Θ ⨟ Δ ⊢ᵣ Qb ⊳ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall F, Qb = pskl_to_bskl_syn F ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  Δ ∩ ftvar_in_bskl Qb [=] empty ->
  Δ ∩ ftvar_in_bskl Q [=] empty.
Proof.
  intros Θ Δ Qb Q Href Hwf F Heq Hdisj Hfree.
  destruct (delta_fresh_flex_defs Hwf Hdisj) as [Hdefs Hflex].
  eapply ad_refine_syn_syn_delta_free_gen; eauto.
Qed.

(* ===================================================================== *)
(*  THE CRUX, in the shape the Ghost rule needs.                           *)
(*                                                                         *)
(*  To re-apply [ad_refine_syn__hole] after a further refinement step we    *)
(*  need the new fill to be a syn painting that is Δ-free.  Refinement      *)
(*  gives both: the shape by [ad_refine_syn_syn_l], Δ-freeness by the       *)
(*  Δ-discipline above — packaged as [ad_refine_syn_hole_l_gen] below,      *)
(*  which is what the transitivity proof uses.  The form here, which also   *)
(*  recovers a skeleton well-formed at the EMPTY Δ, ASSUMES                 *)
(*  well-formedness of the result (the paper's presupposition).             *)
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
  subst Q.
  rewrite bskl_to_pskl_pskl_to_bskl_syn in HwfB.
  eapply a_wf_pskl_delta_mono; [ exact HwfB | ].
  intros α _ Hα. clear - Hα. fsetdec.
Qed.

(* ===================================================================== *)
(*  TRANSITIVITY of refinement, under the paper's external wf condition.   *)
(*                                                                         *)
(*  Proved once the result is required to be well-formed — which the paper *)
(*  presupposes of every refinement judgment anyway.  (⚙ The old           *)
(*  refutation of transitivity without it, cex_refine_not_transitive.v,    *)
(*  was RETRACTED 2026-10-08: it rested on the mech's old ghost rule       *)
(*  demanding a wf fill.  Whether transitivity holds outright is open.)    *)
(*                                                                         *)
(*  Structure: OUTER induction on the second derivation; INNER induction on *)
(*  the first, to peel the left-hand administrative rules [tophole_remove]  *)
(*  and [flex_l] (which shrink the left skeleton while the right stands     *)
(*  still).  Every case whose left side is a GHOST is discharged by         *)
(*  [ad_refine_syn_hole_l_gen] — that is what the crux is for.             *)
(* ===================================================================== *)

(** The left-hand administrative rules, packaged: whatever a Δ-free syn
    painting refines to, a ghost refines to as well. *)
Lemma ad_refine_syn_hole_l_gen : forall Θ Δ P Qr,
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_syn P) ⊳ Qr }}ad ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  Δ ∩ ftvar_in_pskl P [=] empty ->
  {{ Θ ⨟ Δ ⊢ᵣ bskl_hole ⊳ Qr }}ad.
Proof.
  intros Θ Δ P Qr Href Hdefs Hflex HfrP.
  pose proof (ad_refine_syn_syn_delta_free_gen Href P eq_refl Hdefs Hflex
                ltac:(rewrite ftvar_pskl_to_bskl_syn; exact HfrP)) as Hfr.
  destruct (ad_refine_syn_syn_l Href P eq_refl) as [G ->].
  apply ad_refine_syn__hole.
  rewrite ftvar_pskl_to_bskl_syn in Hfr. exact Hfr.
Qed.

Lemma ad_refine_syn_hole_l : forall Θ Δ P Qr,
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_syn P) ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Qr) }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ bskl_hole ⊳ Qr }}ad.
Proof.
  intros Θ Δ P Qr Href Hwf Hdisj HwfF _.
  destruct (delta_fresh_flex_defs Hwf Hdisj) as [Hdefs Hflex].
  eapply ad_refine_syn_hole_l_gen; [ exact Href | exact Hdefs | exact Hflex | ].
  eapply a_wf_pskl_empty_delta_free; [ exact HwfF | exact Hdisj ].
Qed.

Lemma ad_refine_syn_trans_gen : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣ Qm ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Qr) }}a ->
  forall Ql,
  {{ Θ ⨟ Δ ⊢ᵣ Ql ⊳ Qm }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Ql ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Hr.
  induction Hr; intros Hwf Hdefs Hflex HwfQr Ql Hp.
  - (* unit : Qm = Qr = unit *) exact Hp.
  - (* var *) exact Hp.
  - (* arrow *)
    rename Q1 into Qa. rename Q2 into Qb. rename Q3 into Qc. rename Q4 into Qd.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_arrow Qa Qb) ⊳ (bskl_arrow Qc Qd) }}ad)
      by (apply ad_refine_syn__arrow; assumption).
    remember (bskl_arrow Qa Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + inversion HM; subst. simpl in HwfQr.
      inversion HwfQr as [ | | Θw Δw Pw1 Pw2 Hw1 Hw2 | | | ]; subst.
      apply ad_refine_syn__arrow; [ assumption | apply IHHr1 | apply IHHr2 ]; auto.
    + eapply ad_refine_syn_hole_l_gen with (P := P);
        [ exact Hrr | exact Hdefs | exact Hflex | eassumption ].
    + apply ad_refine_syn__tophole_remove; [ assumption | apply IHHp; auto ].
    + eapply ad_refine_syn__flex_l;
        [ eassumption | ]. apply IHHp; auto.
  - (* all : ∀^inh Q ⊳ ∀^inh P *)
    rename Q into Qb. rename Q' into Qc.
    remember (bskl_all_inh Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate;
      [ | destruct P; simpl in HM; discriminate | | ].
    + (* ∀ ⊳ ∀ *)
      inversion HM; subst. simpl in HwfQr.
      inversion HwfQr as [ | | | L2 Θw Δw Pw Hbody | | ]; subst.
      apply ad_refine_syn__all
        with (L := L `union` L0 `union` L2 `union` dom Θ `union` Δ);
        [ assumption | intros α Hα ].
      assert (HαΘ : α `notin` dom Θ) by (clear - Hα; fsetdec).
      destruct (delta_flex_defs_cons_tvar_add Hwf HαΘ Hdefs Hflex)
        as [Hdefs' Hflex'].
      apply H1 with (α := α);
        [ clear - Hα; fsetdec | apply a_wf_aenv__tvar; auto
        | exact Hdefs' | exact Hflex'
        | rewrite bskl_to_pskl_open; apply Hbody; clear - Hα; fsetdec
        | apply H3; clear - Hα; fsetdec ].
    + apply ad_refine_syn__tophole_remove; [ assumption | apply IHHp; auto ].
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* hole : Qm = □, Qr = syn P *)
    rename P into Pf.
    remember (@bskl_hole) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + (* □ ⊳ □ : the fill of Hp must itself be a ghost *)
      destruct P; simpl in HM; try discriminate.
      apply ad_refine_syn__hole. assumption.
    + apply ad_refine_syn__tophole_remove; [ assumption | apply IHHp; auto ].
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* tophole_remove : Qm = ∀◇Q, Qr from Q ⊳ Qr *)
    rename Q into Qb. rename Q' into Qc.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Qb) ⊳ Qc }}ad)
      by (apply ad_refine_syn__tophole_remove; assumption).
    remember (bskl_tophole Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_hole_l_gen with (P := P);
        [ exact Hrr | exact Hdefs | exact Hflex | eassumption ].
    + apply ad_refine_syn__tophole_remove; [ assumption | apply IHHp; auto ].
    + (* tophole_keep on the left : peel both *)
      inversion HM; subst.
      apply ad_refine_syn__tophole_remove; [ assumption | apply IHHr; auto ].
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* tophole_fill : ∀◇Q ⊳ ∀^syn P *)
    rename Q into Qb. rename Q' into Qc.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Qb) ⊳ (bskl_all_syn Qc) }}ad)
      by (eapply ad_refine_syn__tophole_fill with (L := L); assumption).
    remember (bskl_tophole Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_hole_l_gen with (P := P);
        [ exact Hrr | exact Hdefs | exact Hflex | eassumption ].
    + apply ad_refine_syn__tophole_remove; [ assumption | apply IHHp; auto ].
    + (* tophole_keep on the left : rebuild the ∀ *)
      inversion HM; subst.
      simpl in HwfQr.
      inversion HwfQr as [ | | | L2 Θw Δw Pw Hbody | | ]; subst.
      apply ad_refine_syn__tophole_fill
        with (L := L `union` L2 `union` dom Θ `union` Δ);
        [ assumption | intros α Hα ].
      destruct (@delta_flex_defs_cons_tvar α Θ Δ Hdefs Hflex) as [Hdefs' Hflex'].
      apply H1 with (α := α);
        [ clear - Hα; fsetdec
        | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
        | exact Hdefs' | exact Hflex'
        | | ].
      { rewrite bskl_to_pskl_open.
        eapply a_wf_pskl_delta_mono;
          [ apply (Hbody α ltac:(clear - Hα; solve_notin_auto))
          | intros β _ Hβ; clear - Hβ; fsetdec ]. }
      { eapply ad_refine_syn_weaken;
          [ apply ad_refine_syn__tophole_keep; eassumption
          | intros y b Hb; unfold binds; right; exact Hb ]. }
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* tophole_keep : ∀◇Q ⊳ ∀◇P *)
    rename Q into Qb. rename Q' into Qc.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Qb) ⊳ (bskl_tophole Qc) }}ad)
      by (apply ad_refine_syn__tophole_keep; assumption).
    remember (bskl_tophole Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_hole_l_gen with (P := P);
        [ exact Hrr | exact Hdefs | exact Hflex | eassumption ].
    + apply ad_refine_syn__tophole_remove; [ assumption | apply IHHp; auto ].
    + inversion HM; subst.
      simpl in HwfQr.
      inversion HwfQr as [ | | | | | Θw Δw Pw Hg Hwb ]; subst.
      apply ad_refine_syn__tophole_keep; [ assumption | ].
      apply IHHr; auto.
      (* the kept body is wf at [Θ∖Δ ⨟ ∅], hence Δ-free and wf at [Θ ⨟ Δ] *)
      eapply a_wf_pskl_delta_mono.
      * eapply a_wf_pskl_tvar_mono; [ exact Hwb | ].
        intros β Hb. apply a_binds_tvar_aenv_minus in Hb. apply Hb.
      * intros β Hβ HβΔ. exfalso.
        pose proof (a_wf_pskl_ftv_binds Hwb Hβ) as Hb.
        apply a_binds_tvar_aenv_minus in Hb. destruct Hb as [_ Hn].
        exact (Hn HβΔ).
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* flex_l : Qm = α̂ with α̂ := τ *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ Q' }}ad)
      by (eapply ad_refine_syn__flex_l; eassumption).
    remember (bskl_var_f α) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + (* var ⊳ var : rebuild the lookup *)
      inversion HM; subst.
      eapply ad_refine_syn__flex_l; eassumption.
    + eapply ad_refine_syn_hole_l_gen with (P := P);
        [ exact Hrr | exact Hdefs | exact Hflex | eassumption ].
    + apply ad_refine_syn__tophole_remove; [ assumption | apply IHHp; auto ].
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

Lemma ad_refine_syn_trans : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣ Qm ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Qr) }}a ->
  forall Ql,
  {{ Θ ⨟ Δ ⊢ᵣ Ql ⊳ Qm }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Ql ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Hr Hwf Hdisj HwfQr Ql Hp.
  destruct (delta_fresh_flex_defs Hwf Hdisj) as [Hdefs Hflex].
  eapply ad_refine_syn_trans_gen; eauto.
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

(* ===================================================================== *)
(*  The UNCOLOURED mirror of the [ad_refine_syn_trans] chain.              *)
(*                                                                         *)
(*  [ad_refine_pskl]'s [__hole] fill is any Δ-free skeleton (no painting  *)
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
    {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ₚₛ
         (open_pskl_wrt_pskl P (pskl_var_f α)) }}a.
Proof. intros * H; inversion H; subst; eauto. Qed.

(* ===================================================================== *)
(*  Precision DROPS to the uncoloured level: [inh P' ⊳ inh P] implies      *)
(*  [P' ⊳ P] — the pskl [__hole] fill demands strictly less (any Δ-free    *)
(*  skeleton vs a Δ-free synthesised painting).                            *)
(* ===================================================================== *)

