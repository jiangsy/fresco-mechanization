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
Require Import src.frost.decl.prop_skeleton.
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

(** Colour erasure commutes with opening. *)
Lemma bskl_to_pskl_open_rec : forall Q V k,
  bskl_to_pskl (open_bskl_wrt_bskl_rec k V Q)
  = open_pskl_wrt_pskl_rec k (bskl_to_pskl V) (bskl_to_pskl Q).
Proof.
  induction Q; intros; simpl; f_equal; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma bskl_to_pskl_open : forall Q X,
  bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f X))
  = open_pskl_wrt_pskl (bskl_to_pskl Q) (pskl_var_f X).
Proof.
  intros. unfold open_bskl_wrt_bskl, open_pskl_wrt_pskl.
  apply bskl_to_pskl_open_rec.
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
(*  Refinement lands in a SYNTHESISED painting (shape only).               *)
(*                                                                         *)
(*  NB no well-formedness here — and none is derivable: refinement does NOT *)
(*  preserve well-formedness (cex_refine_not_transitive.v).  That is why    *)
(*  well-formedness is carried by the STATEMENTS below rather than by the   *)
(*  rules, exactly as the paper's GhostForall comment intends ("we already  *)
(*  required well-formedness separately").                                  *)
(* ===================================================================== *)

Lemma ad_refine_syn_syn_l : forall Θ Δ Qb B,
  Θ ⨟ Δ ⊢ᵣᵃ Qb ⊳ B ->
  forall P, Qb = pskl_to_bskl_syn P ->
  exists P', B = pskl_to_bskl_syn P'.
Proof.
  intros Θ Δ Qb B Href; induction Href; intros P0 Heq.
  - (* unit *) exists pskl_unit. reflexivity.
  - (* var *) exists (pskl_var_f X). reflexivity.
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
    pick fresh X for (L `union` dom Θ `union` ftvar_in_bskl P).
    destruct (H0 X ltac:(auto) (pskl_tophole Pt) eq_refl) as [RX HeqRX].
    exists (pskl_all_syn (close_pskl_wrt_pskl X RX)).
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
Lemma ad_wf_pskl_delta_shrink : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall Δ', (forall X, X `in` Δ -> X `in` ftvar_in_pskl P -> X `in` Δ') ->
  Θ ⨟ Δ' ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H; induction H; intros Δ' Hkeep.
  - apply ad_wf_pskl__unit.
  - apply ad_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; apply Hkeep; auto; simpl; fsetdec
                             | right; exact Htv ].
  - apply ad_wf_pskl__arrow;
      [ apply IHad_wf_pskl1 | apply IHad_wf_pskl2 ];
      intros X HX HP; apply Hkeep; auto; simpl; fsetdec.
  - apply ad_wf_pskl__all with (L := L `union` ftvar_in_pskl P).
    intros X HX. apply H0; auto.
    intros Y HY HP.
    destruct (Y == X) as [->|Hne]; [ clear; fsetdec | ].
    assert (HYΔ : Y `in` Δ) by (clear - HY Hne; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f X)) as Hup.
    simpl in Hup.
    assert (HYP : Y `in` ftvar_in_pskl P)
      by (assert (Y `in` (singleton X `union` ftvar_in_pskl P))
            by (clear - HP Hup; fsetdec);
          clear - H1 Hne; fsetdec).
    assert (Y `in` Δ') by (apply Hkeep; auto).
    clear - H1; fsetdec.
  - apply ad_wf_pskl__hole.
  - apply ad_wf_pskl__tophole; [ exact H | exact H0 ].
Qed.

(** A skeleton well-formed at the EMPTY Δ mentions only Θ-variables; so if
    Δ is disjoint from Θ (the ∀-variables are refinement-local), it is
    Δ-free. *)
Lemma ad_wf_pskl_empty_delta_free : forall Θ Δ P,
  Θ ⨟ empty ⊢ₚₛᵃ P ->
  (forall X, X `in` Δ -> X `notin` dom Θ) ->
  AtomSetImpl.inter Δ (ftvar_in_pskl P) [=] empty.
Proof.
  intros Θ Δ P Hwf Hdisj.
  apply inter_empty_pointwise. intros X HXΔ.
  intro HXP.
  destruct (ad_wf_pskl_ftv_tvarish Hwf HXP) as [Hemp | Htv];
    [ clear - Hemp; fsetdec | ].
  apply (Hdisj X HXΔ).
  destruct Htv as [Hb | [Hb | [τ Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

(** With a SYNTHESISED painting on the left the [all] rule can never fire (a
    syn painting has no [bskl_all_inh]), so Δ never grows: Δ-freeness
    propagates across the refinement. *)
Lemma ad_refine_syn_syn_delta_free : forall Θ Δ Qb B,
  Θ ⨟ Δ ⊢ᵣᵃ Qb ⊳ B ->
  a_wf_aenv Θ ->
  forall F, Qb = pskl_to_bskl_syn F ->
  (forall X, X `in` Δ -> X `notin` dom Θ) ->
  AtomSetImpl.inter Δ (ftvar_in_bskl Qb) [=] empty ->
  AtomSetImpl.inter Δ (ftvar_in_bskl B) [=] empty.
Proof.
  intros Θ Δ Qb B Href; induction Href; intros Hwf F Heq Hdisj Hfree.
  - (* unit *) simpl. clear; fsetdec.
  - (* var *) exact Hfree.
  - (* arrow *)
    destruct F as [ | | | Fa Fb | | | ]; simpl in Heq; try discriminate.
    inversion Heq; subst. simpl in Hfree |- *.
    apply inter_empty_pointwise. intros X HX.
    assert (H1 : X `notin` ftvar_in_bskl (pskl_to_bskl_syn Fa)
                 `union` ftvar_in_bskl (pskl_to_bskl_syn Fb))
      by (clear - HX Hfree; fsetdec).
    assert (Ha := IHHref1 Hwf Fa eq_refl Hdisj
             ltac:(apply inter_empty_pointwise; intros Y HY;
                   clear - HY Hfree; fsetdec)).
    assert (Hb := IHHref2 Hwf Fb eq_refl Hdisj
             ltac:(apply inter_empty_pointwise; intros Y HY;
                   clear - HY Hfree; fsetdec)).
    clear - HX Ha Hb. fsetdec.
  - (* all : impossible — a syn painting is never [bskl_all_inh] *)
    destruct F; simpl in Heq; discriminate.
  - (* hole : the fill is wf at the EMPTY Δ, hence Δ-free *)
    rewrite ftvar_pskl_to_bskl_syn.
    eapply ad_wf_pskl_empty_delta_free; [ exact H | exact Hdisj ].
  - (* tophole_remove *)
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    eapply IHHref; [ exact Hwf | reflexivity | exact Hdisj
                   | simpl in Hfree; exact Hfree ].
  - (* tophole_fill : the bound variable is fresh, and gets closed over *)
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    pick fresh X for (L `union` Δ `union` dom Θ `union` ftvar_in_bskl P).
    assert (HdisjX : forall Y, Y `in` Δ ->
                     Y `notin` dom ((X ~ abind_tvar) ++ Θ)).
    { intros Y HY. simpl.
      assert (HYX : Y <> X) by (clear - HY Fr; fsetdec).
      assert (HYΘ : Y `notin` dom Θ) by (apply Hdisj; exact HY).
      clear - HYX HYΘ. fsetdec. }
    assert (Hsub : AtomSetImpl.inter Δ
                     (ftvar_in_bskl (open_bskl_wrt_bskl P (bskl_var_f X)))
                   [=] empty).
    { eapply (H0 X ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)
                (pskl_tophole Ft) eq_refl HdisjX).
      simpl in Hfree |- *. exact Hfree. }
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower P (bskl_var_f X))
      as Hlow.
    simpl.
    apply inter_empty_pointwise. intros Y HY HYP.
    assert (HYo : Y `in` ftvar_in_bskl (open_bskl_wrt_bskl P (bskl_var_f X)))
      by (clear - HYP Hlow; fsetdec).
    clear - HY HYo Hsub. fsetdec.
  - (* tophole_keep *)
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst. simpl.
    eapply IHHref; [ exact Hwf | reflexivity | exact Hdisj
                   | simpl in Hfree; exact Hfree ].
  - (* flex_l : the definition's painting IS a syn painting; it is wf in Θ,
       hence (Δ being fresh for Θ) Δ-free *)
    eapply IHHref; [ exact Hwf | reflexivity | exact Hdisj | ].
    unfold ptyp_to_bskl_syn. rewrite ftvar_pskl_to_bskl_syn.
    eapply ad_wf_pskl_empty_delta_free; [ | exact Hdisj ].
    apply a_wf_ptyp_to_wf_pskl.
    eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact H ].
  - (* flex_r : the result is a bare variable, BOUND in Θ — and Δ is fresh
       for Θ, so it is not a Δ-variable *)
    simpl. apply inter_empty_pointwise. intros Y HY HYα.
    assert (HeqY : Y = α) by (clear - HYα; fsetdec). subst.
    apply (Hdisj α HY). apply binds_In in H. exact H.
Qed.

(* ===================================================================== *)
(*  THE CRUX, in the shape the Ghost rule needs.                           *)
(*                                                                         *)
(*  To re-apply [ad_refine_syn__hole] after a further refinement step we    *)
(*  need the new fill to be a syn painting of a skeleton well-formed at the *)
(*  EMPTY Δ.  Refinement does NOT give us that (it does not preserve        *)
(*  well-formedness at all — cex_refine_not_transitive.v).  So we ASSUME    *)
(*  well-formedness of the result — the paper's "we already required        *)
(*  well-formedness separately" — and recover the empty-Δ form from the     *)
(*  Δ-discipline: Δ holds refinement-local ∀-variables, fresh for Θ, and    *)
(*  a syn-headed refinement never grows Δ, so the result stays Δ-free.      *)
(* ===================================================================== *)

Lemma ad_refine_syn_syn_l_wf : forall Θ Δ F B,
  Θ ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_syn F) ⊳ B ->
  a_wf_aenv Θ ->
  (forall X, X `in` Δ -> X `notin` dom Θ) ->
  Θ ⨟ empty ⊢ₚₛᵃ F ->
  Θ ⨟ Δ ⊢ₚₛᵃ (bskl_to_pskl B) ->
  exists G, B = pskl_to_bskl_syn G /\ Θ ⨟ empty ⊢ₚₛᵃ G.
Proof.
  intros Θ Δ F B Href Hwf Hdisj HwfF HwfB.
  destruct (ad_refine_syn_syn_l Href F eq_refl) as [G HeqG].
  exists G. split; [ exact HeqG | ].
  assert (Hdf : AtomSetImpl.inter Δ (ftvar_in_bskl B) [=] empty).
  { eapply ad_refine_syn_syn_delta_free;
      [ exact Href | exact Hwf | reflexivity | exact Hdisj | ].
    rewrite ftvar_pskl_to_bskl_syn.
    eapply ad_wf_pskl_empty_delta_free; [ exact HwfF | exact Hdisj ]. }
  subst B.
  rewrite bskl_to_pskl_pskl_to_bskl_syn in HwfB.
  rewrite ftvar_pskl_to_bskl_syn in Hdf.
  eapply ad_wf_pskl_delta_shrink; [ exact HwfB | ].
  intros X HXΔ HXG. exfalso. clear - HXΔ HXG Hdf. fsetdec.
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
Lemma ad_refine_syn_hole_l : forall Θ Δ F Qr,
  Θ ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_syn F) ⊳ Qr ->
  a_wf_aenv Θ ->
  (forall X, X `in` Δ -> X `notin` dom Θ) ->
  Θ ⨟ empty ⊢ₚₛᵃ F ->
  Θ ⨟ Δ ⊢ₚₛᵃ (bskl_to_pskl Qr) ->
  Θ ⨟ Δ ⊢ᵣᵃ bskl_hole ⊳ Qr.
Proof.
  intros Θ Δ F Qr Href Hwf Hdisj HwfF HwfQr.
  destruct (ad_refine_syn_syn_l_wf Href Hwf Hdisj HwfF HwfQr) as [G [-> HwfG]].
  apply ad_refine_syn__hole. exact HwfG.
Qed.

Lemma ad_refine_syn_trans : forall Θ Δ Qm Qr,
  Θ ⨟ Δ ⊢ᵣᵃ Qm ⊳ Qr ->
  a_wf_aenv Θ ->
  (forall X, X `in` Δ -> X `notin` dom Θ) ->
  Θ ⨟ Δ ⊢ₚₛᵃ (bskl_to_pskl Qr) ->
  forall Sl,
  Θ ⨟ Δ ⊢ᵣᵃ Sl ⊳ Qm ->
  Θ ⨟ Δ ⊢ᵣᵃ Sl ⊳ Qr.
Proof.
  intros Θ Δ Qm Qr Hr.
  induction Hr; intros Hwf Hdisj HwfQr Sl Hp.
  - (* unit : Qm = Qr = unit *) exact Hp.
  - (* var *) exact Hp.
  - (* arrow *)
    rename Q1 into Qa. rename Q2 into Qb. rename P1 into Pa. rename P2 into Pb.
    assert (Hrr : Θ ⨟ Δ ⊢ᵣᵃ (bskl_arrow Qa Qb) ⊳ (bskl_arrow Pa Pb))
      by (apply ad_refine_syn__arrow; assumption).
    remember (bskl_arrow Qa Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + inversion HM; subst. simpl in HwfQr.
      inversion HwfQr as [ | | Θw Δw Pw1 Pw2 Hw1 Hw2 | | | ]; subst.
      apply ad_refine_syn__arrow; [ apply IHHr1 | apply IHHr2 ]; auto.
    + eapply ad_refine_syn_hole_l with (F := P);
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
      intros X HX.
      apply H0 with (X := X); auto.
      { intros Y HY.
        destruct (Y == X) as [->|Hne]; [ clear - HX; fsetdec | ].
        apply Hdisj. clear - HY Hne. fsetdec. }
      { rewrite bskl_to_pskl_open. apply Hbody. clear - HX; fsetdec. }
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
  - (* tophole_remove : Qm = ⊤.Q, Qr from Q ⊳ Qr *)
    rename Q into Qb. rename P into Pb.
    assert (Hrr : Θ ⨟ Δ ⊢ᵣᵃ (bskl_tophole Qb) ⊳ Pb)
      by (apply ad_refine_syn__tophole_remove; assumption).
    remember (bskl_tophole Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_hole_l with (F := P);
        [ exact Hrr | exact Hwf | exact Hdisj | eassumption
        | exact HwfQr ].
    + apply ad_refine_syn__tophole_remove. apply IHHp; auto.
    + (* tophole_keep on the left : peel both *)
      inversion HM; subst.
      apply ad_refine_syn__tophole_remove. apply IHHr; auto.
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* tophole_fill : ⊤.Q ⊳ ∀^syn P *)
    rename Q into Qb. rename P into Pb.
    assert (Hrr : Θ ⨟ Δ ⊢ᵣᵃ (bskl_tophole Qb) ⊳ (bskl_all_syn Pb))
      by (eapply ad_refine_syn__tophole_fill with (L := L); assumption).
    remember (bskl_tophole Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_hole_l with (F := P);
        [ exact Hrr | exact Hwf | exact Hdisj | eassumption
        | exact HwfQr ].
    + apply ad_refine_syn__tophole_remove. apply IHHp; auto.
    + (* tophole_keep on the left : rebuild the ∀ *)
      inversion HM; subst.
      simpl in HwfQr.
      inversion HwfQr as [ | | | L2 Θw Δw Pw Hbody | | ]; subst.
      apply ad_refine_syn__tophole_fill
        with (L := L `union` L2 `union` dom Θ `union` Δ).
      intros X HX.
      apply H0 with (X := X); auto.
      { apply a_wf_aenv__tvar; auto. }
      { intros Y HY. simpl.
        assert (HYX : Y <> X) by (clear - HY HX; fsetdec).
        assert (HYΘ : Y `notin` dom Θ) by (apply Hdisj; exact HY).
        clear - HYX HYΘ. fsetdec. }
      { rewrite bskl_to_pskl_open.
        eapply ad_wf_pskl_delta_mono;
          [ apply (ad_wf_pskl_reassoc
                     (Hbody X ltac:(clear - HX; fsetdec)) X)
          | clear; fsetdec ]. }
      { eapply ad_refine_syn_weaken;
          [ apply ad_refine_syn__tophole_keep; eassumption
          | intros y b Hb; unfold binds; right; exact Hb ]. }
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* tophole_keep : ⊤.Q ⊳ ⊤.P *)
    rename Q into Qb. rename P into Pb.
    assert (Hrr : Θ ⨟ Δ ⊢ᵣᵃ (bskl_tophole Qb) ⊳ (bskl_tophole Pb))
      by (apply ad_refine_syn__tophole_keep; assumption).
    remember (bskl_tophole Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_hole_l with (F := P);
        [ exact Hrr | exact Hwf | exact Hdisj | eassumption
        | exact HwfQr ].
    + apply ad_refine_syn__tophole_remove. apply IHHp; auto.
    + inversion HM; subst.
      simpl in HwfQr.
      inversion HwfQr as [ | | | | | Θw Δw Pw Hg Hwb ]; subst.
      apply ad_refine_syn__tophole_keep; [ assumption | ].
      apply IHHr; auto.
      eapply ad_wf_pskl_delta_mono; [ exact Hwb | clear; fsetdec ].
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  - (* flex_l : Qm = α̂ with α̂ := τ *)
    assert (Hrr : Θ ⨟ Δ ⊢ᵣᵃ (bskl_var_f α) ⊳ Q)
      by (eapply ad_refine_syn__flex_l; eassumption).
    remember (bskl_var_f α) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + (* var ⊳ var : rebuild the lookup *)
      inversion HM; subst.
      eapply ad_refine_syn__flex_l; eassumption.
    + eapply ad_refine_syn_hole_l with (F := P);
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

Corollary ad_precise_preserves_refine : forall Θ Δ P Q A,
  Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ Q ->
  Θ ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_inh Q) ⊳ A ->
  a_wf_aenv Θ ->
  (forall X, X `in` Δ -> X `notin` dom Θ) ->
  Θ ⨟ Δ ⊢ₚₛᵃ (bskl_to_pskl A) ->
  Θ ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ A.
Proof.
  intros Θ Δ P Q A Hprec Href Hwf Hdisj HwfA.
  eapply ad_refine_syn_trans;
    [ exact Href | exact Hwf | exact Hdisj | exact HwfA | exact Hprec ].
Qed.
