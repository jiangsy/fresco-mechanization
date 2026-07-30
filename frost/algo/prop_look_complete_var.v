(* P6-Cv: completeness of consistency-constraint solving for the variable
   case — [a_solve_eq_complete_var] (consistency-proofs.tex:1180), CLOSED
   axiom-free and PREMISE-FAITHFUL to the paper (the earlier mech-only
   [pskl_no_hole P0] side condition was removed by the [aenv_split] bag
   rework, 2026-07-27).  Extends prop_look_complete.v with the ForallSyn
   machinery (the bag-split generalized theorem, the aenv-tvar precision
   rename, and the three ForallGhost / GhostL / UnivGhost rows). *)
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_consis_precise.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_sub_complete.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_look_complete.

Set Implicit Arguments.

(* Most P6-Cv leaf/absurd helpers live in prop_look_complete.v; this file
   adds the ForallSyn-specific kit and the main induction over the whole
   consistency judgment. *)



(** [MECH-ONLY kit] Moving a Δ-entry of skeleton well-formedness into the
    aenv as a rigid tvar (mid-insertion general; the ∀◇-body stays at
    empty Δ and only needs binds-weakening).  No paper counterpart: the
    paper writes every descent binder as "Θ,β" and never distinguishes
    the aenv from the skeleton-scope Δ, so these transports are implicit
    there. *)
Lemma a_wf_pskl_delta_to_tvar_mid : forall Θfull Δ P,
  Θfull ⨟ Δ ⊢ₚₛᵃ P ->
  forall α1 Θ1 Θ2 Δ', Θfull = Θ1 ++ Θ2 ->
  Δ [<=] add α1 Δ' ->
  (Θ1 ++ (α1 ~ abind_tvar) ++ Θ2) ⨟ Δ' ⊢ₚₛᵃ P.
Proof.
  intros Θfull Δ P H; induction H; intros α1 Θ1 Θ2 Δ' HeqΘ Hsub; subst.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    match goal with Hor : _ \/ a_binds_tvar ?α0 _ |- _ =>
      destruct Hor as [HΔ | Hbt];
      [ destruct (α0 == α1) as [-> | Hne];
        [ right; left; unfold binds;
          apply in_or_app; right; left; reflexivity
        | left; clear - HΔ Hsub Hne; fsetdec ]
      | right;
        destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        [ left; apply binds_weaken; exact Hb
        | right; left; apply binds_weaken; exact Hb
        | right; right; exists τ0; apply binds_weaken; exact Hb ] ]
    end.
  - apply a_wf_pskl__arrow; eauto.
  - apply a_wf_pskl__all with (L := L).
    intros α Hα.
    apply (H0 α Hα α1 Θ1 Θ2 (add α Δ') eq_refl).
    clear - Hsub; fsetdec.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; [ assumption | ].
    eapply a_wf_pskl_weaken;
      [ intros x b Hb; apply binds_weaken; exact Hb | eassumption ].
Qed.

Lemma a_wf_pskl_delta_to_tvar : forall Θ Δ P α1 Δ',
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  Δ [<=] add α1 Δ' ->
  ((α1 ~ abind_tvar) ++ Θ) ⨟ Δ' ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P α1 Δ' H Hsub.
  exact (@a_wf_pskl_delta_to_tvar_mid _ _ _ H α1 nil Θ Δ' eq_refl Hsub).
Qed.

(** a_inc images are Θ-scoped (the prose wf side-condition, pointwise). *)
Lemma a_inc_image_ftv_dom : forall Θ0 κ Θ,
  κ ∷ Θ0 ⊑ Θ ->
  forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ.
Proof.
  intros Θ0 κ Θ H; induction H; intros p Hp; simpl in Hp.
  - contradiction.
  - destruct Hp as [<- | Hp];
      [ simpl; apply a_wf_ptyp_ftv_dom'; assumption | eauto ].
  - destruct Hp as [<- | Hp];
      [ simpl; apply a_wf_ptyp_ftv_dom'; assumption | eauto ].
  - pose proof (IHa_inc p Hp) as Hb.
    repeat rewrite dom_app. clear - Hb; fsetdec.
  - pose proof (IHa_inc p Hp) as Hb.
    repeat rewrite dom_app. clear - Hb; fsetdec.
  - pose proof (IHa_inc p Hp) as Hb.
    repeat rewrite dom_app. clear - Hb; fsetdec.
Qed.

(* The paper-form statement is now the COROLLARY of the generalized
   theorem below (Θtv := [], Δr := ∅, R := ∅); the paper mapping is
   documented on the corollary [a_solve_eq_complete_var]. *)


(* ===================================================================== *)
(*  THE GENERALIZED STATEMENT (repair architecture, DESIGN §6(m), bag     *)
(*  form).  Θ splits as a binds-level BAG [aenv_split Θ Θtv Θr] (Θtv =    *)
(*  the ForallInh descent binders, all rigid; Θr = the original context   *)
(*  PLUS the refinement-visible ForallSyn binders); the refinement        *)
(*  premise lives at (Θr, Δr) with Δr [=] dom Θtv, so □-fills stay wf     *)
(*  away from the Θtv binders; the conclusion returns a fresh-extension   *)
(*  FAMILY of precisions, which is what lets the ForallInh/ForallSyn □-   *)
(*  and ∀◇-fill-rows fold their bodies at (add α Δ).  The paper's         *)
(*  statement is the Θtv := [] / R := ∅ corollary.                        *)
(* ===================================================================== *)
(*  ForallSyn kit: flex_apart TARGET descent through an all_etag binder    *)
(*  (the ∀◇-body is guarded, which excludes the all_syn source that would  *)
(*  otherwise block the descent).  [MECH-ONLY: maintenance lemmas for the  *)
(*  mech-only flex_apart premise — the paper has no counterpart because    *)
(*  its proof never states the FlexR-freshening reachability invariant.]   *)
(* ===================================================================== *)

(** Guarded source: descend the all_etag target one binder. *)
Lemma flex_apart_guarded_all_etag_descent : forall Θ0 Δρ P0 ε ψ,
  guarded_pskl P0 ->
  flex_apart Θ0 Δρ P0 (uskl_all_etag ε ψ) ->
  forall α, α `notin` Δρ ->
  flex_apart Θ0 Δρ P0 (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros Θ0 Δρ P0 ε ψ Hg Hfa α Hα; inversion Hg; subst.
  - (* unit *) apply fa_unit.
  - (* var *)
    inversion Hfa; subst.
    + apply fa_clean.
      match goal with Hc : _ ∩ _ [=] empty |- _ =>
        pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                      (uskl_var_f α)) as Hup;
        simpl in *; clear - Hc Hup Hα; fsetdec end.
    + apply fa_var_rigid; assumption.
    + (* fa_flexfree : the payload is untouched *)
      apply fa_flexfree; assumption.
  - (* arrow *)
    inversion Hfa; subst;
      [ | (* fa_flexfree : the payload is untouched *)
          apply fa_flexfree; assumption ].
    apply fa_clean.
    match goal with Hc : _ ∩ _ [=] empty |- _ =>
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                    (uskl_var_f α)) as Hup;
      simpl in *; clear - Hc Hup Hα; fsetdec end.
Qed.

(** ∀◇ source (guarded body): descend the all_etag target one binder. *)
Lemma flex_apart_tophole_all_etag_descent : forall Θ0 Δρ P0' ε ψ,
  guarded_pskl P0' ->
  flex_apart Θ0 Δρ (pskl_tophole P0') (uskl_all_etag ε ψ) ->
  forall α, α `notin` Δρ ->
  flex_apart Θ0 Δρ (pskl_tophole P0') (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros Θ0 Δρ P0' ε ψ Hg Hfa α Hα.
  inversion Hfa; subst.
  - (* fa_clean *)
    apply fa_clean.
    match goal with Hc : _ ∩ _ [=] empty |- _ =>
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α))
        as Hup;
      simpl in *; clear - Hc Hup Hα; fsetdec end.
  - (* fa_tophole: descend the guarded body *)
    apply fa_tophole.
    eapply flex_apart_guarded_all_etag_descent;
      [ exact Hg | eassumption | exact Hα ].
  - (* fa_flexfree : the payload is untouched *)
    apply fa_flexfree; assumption.
Qed.

(* RESTART NOTE (no-hole removal rework): the "ForallSyn kit (2)" that
   lived here — [bskl_no_hole] + [ad_refine_syn_aenv_to_delta(_mid)], the
   aenv→Δr transport of the refinement premise, valid only for hole-free
   sources — was DELETED as dead.  The bag split [aenv_split] lets the
   ForallSyn binder join Θr, so the tophole_fill body is the IH's
   refinement premise VERBATIM and no transport (hence no pskl_no_hole
   premise) is needed. *)


(* ===================================================================== *)
(*  ForallSyn kit (4): rename a tvar α2↦β2 in the AENV of a precision       *)
(*  derivation.  Needed to build the ad_ppre__tophole_fill cofinite       *)
(*  family (binder in the aenv) from a SINGLE IHα instance.               *)
(*  [PAPER: implicit — the paper's "removing β as necessary" α-renames    *)
(*  the fill binder without comment; a cofinite-quantified rule needs     *)
(*  the rename made explicit.  The solve output is NOT deterministic, so  *)
(*  re-running the IH per family member would return unrelated Pa's —     *)
(*  renaming the single run is the only route.]                           *)
(* ===================================================================== *)

Lemma binds_swap_mid : forall (α : atom) (b : abind) Θ1 Θ0 α1 β1 c c',
  binds α b (Θ1 ++ (α1 ~ c) ++ Θ0) -> α <> α1 ->
  binds α b (Θ1 ++ (β1 ~ c') ++ Θ0).
Proof.
  intros α b Θ1 Θ0 α1 β1 c c' Hb Hne.
  unfold binds in *.
  apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb | Hb]; [ left; exact Hb | right ].
  simpl in Hb. destruct Hb as [Heq | Hb].
  - inversion Heq; subst. contradiction.
  - simpl. right. exact Hb.
Qed.

Lemma ad_partial_precise_rename_tvar : forall Θfull Δ Ψ P ψ,
  Θfull ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall α1 β1 Θ1 Θ0,
  uniq Θfull ->
  Θfull = Θ1 ++ (α1 ~ abind_tvar) ++ Θ0 ->
  β1 `notin` dom Θfull ->
  β1 `notin` Δ ->
  β1 `notin` ftvar_in_pskl P ->
  β1 `notin` ftvar_in_uskl ψ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θfull ->
     α1 `notin` ftvar_in_ptyp τ /\ β1 `notin` ftvar_in_ptyp τ) ->
  (Θ1 ++ (β1 ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢
    (subst_pskl_in_pskl (pskl_var_f β1) α1 P)
    ⊑ᵖ[ Ψ ] (subst_bskl_in_uskl (uskl_var_f β1) α1 ψ).
Proof.
  intros Θfull Δ Ψ P ψ H; induction H;
    intros α1 β1 Θ1 Θ0 Hu Heq HWd Hβ2Δ HWP Hβ2ψ Hdefs; subst; simpl in *.
  - (* unit *) apply ad_ppre__unit; assumption.
  - (* var α *)
    destruct (eq_var α α1) as [-> | Hne].
    + repeat (destruct_if as [_ | Hc]; [ | exfalso; apply Hc; reflexivity ]).
      apply ad_ppre__var; [ assumption | ].
      right. left. unfold binds; apply in_or_app; right; left; reflexivity.
    + repeat (destruct_if as [Hc | _]; [ exfalso; apply Hne; exact Hc | ]).
      apply ad_ppre__var; [ assumption | ].
      destruct H0 as [HΔ | Hbt]; [ left; exact HΔ | right ].
      destruct Hbt as [Hb | [Hb | [τ Hb]]];
        [ left | right; left | right; right; exists τ ];
        eapply binds_swap_mid; try exact Hb; exact Hne.
  - (* arrow *)
    eapply ad_ppre__arrow;
      [ apply IHad_partial_precise1;
          [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
          | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ]
      | apply IHad_partial_precise2;
          [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
          | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ]
      | assumption ].
  - (* forall: binder β into Δ, aenv unchanged *)
    eapply ad_ppre__forall with
      (L := L `union` singleton α1 `union` singleton β1
              `union` Δ `union` dom (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0));
      [ | eassumption ].
    intros β Hβ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    apply (H0 β ltac:(clear - Hβ; fsetdec) α1 β1 Θ1 Θ0 Hu eq_refl HWd);
      [ clear - Hβ2Δ Hβ; fsetdec
      | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P
                      (pskl_var_f β)) as Hup;
        simpl in Hup; clear - HWP Hβ Hup; fsetdec
      | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                      (uskl_var_f β)) as Hup;
        simpl in Hup; clear - Hβ2ψ Hβ Hup; fsetdec
      | exact Hdefs ].
  - (* hole *)
    assert (Hα2ψ : α1 `notin` ftvar_in_uskl ψ \/ α1 `in` ftvar_in_uskl ψ)
      by (destruct (AtomSetProperties.In_dec α1 (ftvar_in_uskl ψ));
          [ right | left ]; assumption).
    apply ad_ppre__hole; [ assumption | ].
    pose proof (ftvar_in_uskl_subst_bskl_in_uskl_upper ψ (uskl_var_f β1) α1)
      as Hup. simpl in Hup.
    match goal with Hint : Δ ∩ _ [=] empty |- _ =>
      clear - Hint Hβ2Δ Hup; fsetdec end.
  - (* tophole_remove *)
    apply ad_ppre__tophole_remove.
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ].
  - (* tophole_fill: binder α into the AENV front *)
    eapply ad_ppre__tophole_fill with
      (L := L `union` singleton α1 `union` singleton β1
              `union` Δ `union` dom (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0)).
    intros β Hβ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    replace (pskl_tophole (subst_pskl_in_pskl (pskl_var_f β1) α1 P))
      with (subst_pskl_in_pskl (pskl_var_f β1) α1 (pskl_tophole P))
      by reflexivity.
    assert (Hu' : uniq ((β ~ abind_tvar) ++ Θ1 ++ (α1 ~ abind_tvar) ++ Θ0))
      by (apply uniq_push; [ exact Hu | clear - Hβ; solve_notin ]).
    apply (H0 β ltac:(clear - Hβ; fsetdec) α1 β1
             ((β ~ abind_tvar) ++ Θ1) Θ0 Hu' eq_refl);
      [ simpl; clear - HWd Hβ; solve_notin
      | exact Hβ2Δ
      | simpl; clear - HWP; solve_notin
      | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                      (uskl_var_f β)) as Hup;
        simpl in Hup; clear - Hβ2ψ Hβ Hup; fsetdec
      | intros αd τ Hb;
        apply Hdefs with (α := αd);
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          [ discriminate Hc | exact Hb' ] ].
  - (* tophole_keep *)
    apply ad_ppre__tophole_keep.
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ].
  - (* flex_l: α ≠ α1 (uniq); the def τ is α1-free (Hdefs) *)
    assert (Hne : α <> α1).
    { intro; subst.
      assert (Hbz : binds α1 abind_tvar (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      pose proof (binds_unique _ _ _ _ _ H Hbz Hu) as Hc; discriminate Hc. }
    destruct_if as [Hc | _]; [ exfalso; apply Hne; exact Hc | ].
    destruct (Hdefs _ _ H) as [Hα2τ Hβ2τ].
    eapply ad_ppre__flex_l;
      [ eapply binds_swap_mid; [ exact H | exact Hne ] | ].
    assert (Hfr : α1 `notin` ftvar_in_pskl (ptyp_to_pskl τ))
      by (rewrite ftvar_in_pskl_ptyp_to_pskl; exact Hα2τ).
    rewrite <- (subst_pskl_in_pskl_fresh_eq (ptyp_to_pskl τ)
                  (pskl_var_f β1) α1 Hfr).
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | rewrite ftvar_in_pskl_ptyp_to_pskl; exact Hβ2τ
      | clear - Hβ2ψ; solve_notin | exact Hdefs ].
  - (* flex_r: α ≠ α1 (uniq); the def τ is α1-free (Hdefs) *)
    assert (Hne : α <> α1).
    { intro; subst.
      assert (Hbz : binds α1 abind_tvar (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      pose proof (binds_unique _ _ _ _ _ H Hbz Hu) as Hc; discriminate Hc. }
    destruct_if as [Hc | _]; [ exfalso; apply Hne; exact Hc | ].
    destruct (Hdefs _ _ H) as [Hα2τ Hβ2τ].
    eapply ad_ppre__flex_r;
      [ eapply binds_swap_mid; [ exact H | exact Hne ] | ].
    assert (Hfr : α1 `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ))
      by (rewrite ftvar_in_uskl_ptyp_to_uskl_syn; exact Hα2τ).
    rewrite <- (subst_bskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τ)
               (uskl_var_f β1) α1 Hfr).
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | clear - HWP; solve_notin
      | rewrite ftvar_in_uskl_ptyp_to_uskl_syn; exact Hβ2τ | exact Hdefs ].
Qed.

(* ===================================================================== *)
(*  The BAG split  [aenv_split Θf Θtv Θr]  (no-hole-removal rework).      *)
(*  The old split was the LIST equation Θ = Θtv ++ Θr, which cannot put   *)
(*  the ForallSyn binder INTO Θr (the consistency rule prepends it to Θ,  *)
(*  so the equation forces it into Θtv) — that forced the aenv→Δr         *)
(*  transport [ad_refine_syn_aenv_to_delta], which is false for holey     *)
(*  sources and hence forced the pskl_no_hole premise.  A binds-level     *)
(*  split has no order, so ForallSyn can use Θr_ih := (α~tvar)++Θr and    *)
(*  take the tophole_fill body as the IH's refinement premise VERBATIM.   *)
(*  Θr's defs are no longer "a suffix of Θ", so their self-containedness  *)
(*  is carried as an explicit a_wf_aenv Θr premise.                       *)
(* ===================================================================== *)

Definition aenv_split (Θf Θtv Θr : aenv) : Prop :=
  (forall x (b : abind), binds x b Θf <-> binds x b Θtv \/ binds x b Θr) /\
  dom Θf [=] dom Θtv `union` dom Θr /\
  (dom Θtv) ∩ dom Θr [=] empty.

Lemma aenv_split_nil : forall Θf, aenv_split Θf nil Θf.
Proof.
  intros Θf; split; [ | split ].
  - intros x b; split; intros Hb;
      [ right; exact Hb
      | destruct Hb as [Hb | Hb]; [ inversion Hb | exact Hb ] ].
  - simpl. clear; fsetdec.
  - simpl. clear; fsetdec.
Qed.

Lemma aenv_split_cons_tv : forall Θf Θtv Θr α,
  aenv_split Θf Θtv Θr -> α `notin` dom Θf ->
  aenv_split ((α ~ abind_tvar) ++ Θf) ((α ~ abind_tvar) ++ Θtv) Θr.
Proof.
  intros Θf Θtv Θr α (Hbs & Hdom & Hdisj) Hα; split; [ | split ].
  - intros x b; split.
    + intros Hb.
      unfold binds in Hb; simpl in Hb.
      destruct Hb as [Heq | Hb];
        [ left; unfold binds; simpl; left; exact Heq | ].
      apply Hbs in Hb.
      destruct Hb as [Hb | Hb];
        [ left; unfold binds; simpl; right; exact Hb | right; exact Hb ].
    + intros Hor.
      unfold binds; simpl.
      destruct Hor as [Hb | Hb];
        [ unfold binds in Hb; simpl in Hb;
          destruct Hb as [Heq | Hb];
          [ left; exact Heq | right; apply Hbs; left; exact Hb ]
        | right; apply Hbs; right; exact Hb ].
  - simpl. clear - Hdom; fsetdec.
  - simpl. clear - Hdisj Hdom Hα; fsetdec.
Qed.

Lemma aenv_split_cons_r : forall Θf Θtv Θr α,
  aenv_split Θf Θtv Θr -> α `notin` dom Θf ->
  aenv_split ((α ~ abind_tvar) ++ Θf) Θtv ((α ~ abind_tvar) ++ Θr).
Proof.
  intros Θf Θtv Θr α (Hbs & Hdom & Hdisj) Hα; split; [ | split ].
  - intros x b; split.
    + intros Hb.
      unfold binds in Hb; simpl in Hb.
      destruct Hb as [Heq | Hb];
        [ right; unfold binds; simpl; left; exact Heq | ].
      apply Hbs in Hb.
      destruct Hb as [Hb | Hb];
        [ left; exact Hb | right; unfold binds; simpl; right; exact Hb ].
    + intros Hor.
      unfold binds; simpl.
      destruct Hor as [Hb | Hb];
        [ right; apply Hbs; left; exact Hb
        | unfold binds in Hb; simpl in Hb;
          destruct Hb as [Heq | Hb];
          [ left; exact Heq | right; apply Hbs; right; exact Hb ] ].
  - simpl. clear - Hdom; fsetdec.
  - simpl. clear - Hdisj Hdom Hα; fsetdec.
Qed.

Lemma aenv_split_sub_r : forall Θf Θtv Θr,
  aenv_split Θf Θtv Θr ->
  forall x (b : abind), binds x b Θr -> binds x b Θf.
Proof.
  intros Θf Θtv Θr (Hbs & _ & _) x b Hb. apply Hbs. right; exact Hb.
Qed.

Lemma aenv_split_dom_r : forall Θf Θtv Θr,
  aenv_split Θf Θtv Θr -> dom Θr [<=] dom Θf.
Proof.
  intros Θf Θtv Θr (_ & Hdom & _). clear - Hdom; fsetdec.
Qed.

(** Non-tvar bindings of the full context live on the Θr side. *)
Lemma aenv_split_binds_def_r : forall Θf Θtv Θr α τ,
  aenv_split Θf Θtv Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  binds α (abind_flex_mono_def τ) Θf ->
  binds α (abind_flex_mono_def τ) Θr.
Proof.
  intros Θf Θtv Θr α τ (Hbs & _ & _) Htvs Hb.
  apply Hbs in Hb.
  destruct Hb as [Hb | Hb]; [ | exact Hb ].
  pose proof (Htvs _ _ Hb) as Hc; discriminate Hc.
Qed.

(** [refine_primary_to_plain], bag-split form: weaken Θr into the full
    context and absorb Δr (= dom Θtv, all rigid there). *)
Lemma refine_primary_to_plain_split : forall Θf Θtv Θr Δr Q' Q,
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  aenv_split Θf Θtv Θr ->
  Δr [=] dom Θtv ->
  Θr ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  Θf ⨟ empty ⊢ᵣᵃ Q' ⊳ Q.
Proof.
  intros Θf Θtv Θr Δr Q' Q Htvs Hsp HΔr H.
  eapply ad_refine_syn_delta_absorb with (Δr := Δr).
  - eapply ad_refine_syn_weaken;
      [ exact H | intros x b Hb; eapply aenv_split_sub_r; eassumption ].
  - intros α2 Hα2. right.
    assert (HZd : α2 `in` dom Θtv) by (clear - Hα2 HΔr; fsetdec).
    apply binds_In_inv in HZd; destruct HZd as [b Hb].
    pose proof (Htvs _ _ Hb) as Heqb; subst b.
    destruct Hsp as (Hbs & _ & _). apply Hbs. left; exact Hb.
Qed.

(** [consis_subject_ftv_split_bound], bag-split form (Θr's defs are
    self-contained by its OWN wf, not by suffix position). *)
Lemma consis_subject_ftv_bag_bound : forall Ψ Θf R Q Θtv Θr,
  Ψ ⨟ Θf ⊢ₛᵃ R ∼ Q ->
  aenv_split Θf Θtv Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  a_wf_aenv Θr ->
  ftvar_in_uskl R [<=] ftvar_in_bskl Q `union` dom Θr.
Proof.
  intros Ψ Θf R Q Θtv Θr H Hsp Htvs HwfΘr.
  intros x Hx.
  destruct (ad_pat_consis_ftv_bound H Hx) as [Hin | (α & τ & Hb & Hor)].
  - clear - Hin; fsetdec.
  - assert (Hbr : binds α (abind_flex_mono_def τ) Θr)
      by (eapply aenv_split_binds_def_r; eassumption).
    destruct Hor as [-> | Hτ].
    + pose proof (binds_In _ _ _ _ Hbr) as Hd. clear - Hd; fsetdec.
    + assert (Hd : ftvar_in_ptyp τ [<=] dom Θr)
        by (eapply a_wf_aenv_def_ftv_dom; [ exact HwfΘr | exact Hbr ]).
      clear - Hτ Hd; fsetdec.
Qed.

Theorem a_solve_eq_complete_var_gen :
  forall NM Θ Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  (* the context split, as a BINDS-LEVEL bag (see the block above): the
     consistency induction keeps a variable aenv index, and the ForallSyn
     binder can join Θr (refinement-visible) instead of Θtv *)
  aenv_split Θ Θtv Θr ->
  aenv_split Θ0 Θtv Θ0r ->
  a_wf_aenv Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  Δr [=] dom Θtv ->
  Δρ ∩ dom Θtv [=] empty ->
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  uskl_rho NM Θ Δρ Ψρ ψsub ψa ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  Ψρ ∩ Ψ' [=] empty ->
  rho_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->
  flex_apart Θ0 Δρ P0 ψa ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
  Ψsub [<=] Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  Ψsub ⨟ Θ ⊢ₛᵃ ψsub ∼ Q ->
  Θr ⨟ Δr ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
    forall Δ',
      Δ' ∩ Δ [=] empty ->
      Δ' ∩ dom Θr [=] empty ->
      delta_def_fresh Δ' Θ ->
      Θ ⨟ (Δ `union` Δ') ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  intros NM Θ Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hrho Htags
         Hsub Hinter Hfresh Hdelta Hshield Hdfresh Hapart Hpre
         Hsubeq1 Hsubeq2 Hconsis Hrefine.
  revert NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa ψa Pi P0
         HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hrho Htags
         Hsub Hinter Hfresh Hdelta Hshield Hdfresh Hapart Hpre
         Hsubeq1 Hsubeq2 Hrefine.
  induction Hconsis; intros
    NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa ψa Pi P0
    HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hrho Htags
    Hsub Hinter Hfresh Hdelta Hshield Hdfresh Hapart Hpre
    Hsubeq1 Hsubeq2 Hrefine.
  - (* unit *)
    assert (Hrefine' : Θ ⨟ empty ⊢ᵣᵃ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_unit)
      by (eapply refine_primary_to_plain_split; eassumption).
    destruct (uskl_rho_unit_l_inv Hrho) as [[-> HΨρ] | Hleaf].
    + assert (HΨ'e : Ψ' [=] empty)
        by (exact (d_tags_skl_unit_inv (a_tags_sort_d_tags Htags))).
      assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
      assert (Hsz : size_pskl Pi + size_pskl P0
                      <= size_pskl Pi + size_pskl P0) by lia.
      destruct (a_solve_eq_cv_unit (Θ := Θ) (Δ := Δ)
                  Hsz HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine')
        as (Pa & Hsolve & Hprec).
      exists Pa; split; [ exact Hsolve | ].
      intros Δ' HS1 HS2 HS3.
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_partial_precise_delta_weaken_fresh;
            [ exact Hprec | simpl; clear; fsetdec | exact HS3 ]
        | clear - HΨae; fsetdec ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf)
        as (Pa & Hs & Hq).
      exists Pa; split; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
  - (* var: the target is [var α]; the Δ'-extension splits on where α
       lives — Θr-side (Δ' avoids it) vs binder-side (the primary
       refinement forces a hole-free P0, and solve preserves it) *)
    assert (Hrefine' : Θ ⨟ empty ⊢ᵣᵃ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (bskl_var_f α))
      by (eapply refine_primary_to_plain_split; eassumption).
    destruct (uskl_rho_var_l_inv Hrho) as [[-> HΨρ] | Hleaf].
    + assert (HΨ'e : Ψ' [=] empty)
        by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
      assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
      assert (Hsz : size_pskl Pi + size_pskl P0
                      <= size_pskl Pi + size_pskl P0) by lia.
      destruct (a_solve_eq_cv_var (Θ := Θ) (Δ := Δ)
                  Hsz HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hdfresh Hpre Hrefine')
        as (Pa & Hsolve & Hprec).
      exists Pa; split; [ exact Hsolve | ].
      intros Δ' HS1 HS2 HS3.
      destruct (AtomSetProperties.In_dec α (dom Θr)) as [HinR | HninR].
      * (* Θr-side: Δ' avoids the target variable *)
        eapply ad_partial_precise_psi_cong;
          [ eapply ad_partial_precise_delta_weaken_fresh;
              [ exact Hprec
              | simpl; clear - HS2 HinR; fsetdec
              | exact HS3 ]
          | clear - HΨae; fsetdec ].
      * (* binder-side: the primary refinement forces a hole-free P0
           (the □-fill would have to BE the Δr-binder variable, which is
           not Θr-wf), and solve preserves it — precision is Δ-monotone *)
        assert (HnhP0d : pskl_no_hole P0).
        { eapply msubst_pskl_no_hole_inv with (κ := κ).
          eapply ad_refine_inh_deltar_var_rhs_no_hole;
            [ exact Hrefine | reflexivity | reflexivity | exact HninR ]. }
        assert (HnhPa : pskl_no_hole Pa)
          by (eapply a_solve_eq_no_hole_p0; [ exact Hsolve | exact HnhP0d ]).
        eapply ad_partial_precise_psi_cong;
          [ eapply ad_ppre_no_hole_subject_delta_mono;
              [ exact Hprec | apply msubst_pskl_no_hole; exact HnhPa
              | clear; fsetdec ]
          | clear - HΨae; fsetdec ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf)
        as (Pa & Hs & Hq).
      exists Pa; split; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
  - (* arrow: KEY continuation; CORE grid on size Pi + size P0 at the
       fixed arrow target, with the PRIMARY (Θr, Δr) refinement threaded
       through the recursion and ∀Δ' families out of every row. *)
    assert (HwfΘr2 := HwfΘr).
    assert (KEY : forall ψa1 ψa2 Ψρ1 Ψρ2,
      uskl_rho NM Θ Δρ Ψρ1 R1 ψa1 ->
      uskl_rho NM Θ Δρ Ψρ2 R2 ψa2 ->
      Ψρ [=] Ψρ1 `union` Ψρ2 ->
      a_tags_sort NM Ψ' (uskl_arrow ψa1 ψa2) ->
      flex_apart Θ0 Δρ P0 (uskl_arrow ψa1 ψa2) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_arrow ψa1 ψa2) ->
      exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
        forall Δ',
          Δ' ∩ Δ [=] empty ->
          Δ' ∩ dom Θr [=] empty ->
          delta_def_fresh Δ' Θ ->
          Θ ⨟ (Δ `union` Δ') ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ]
            (uskl_arrow ψa1 ψa2)).
    { intros ψa1 ψa2 Ψρ1 Ψρ2 Hrho1 Hrho2 HΨρs Htags0 Hap0 Hpre0.
      destruct (a_tags_sort_arrow_inv Htags0)
        as (Ψ'1 & Ψ'2 & Htags1 & Htags2 & HΨ'disj & HΨ's).
      (* branch tag-flow facts, fixed for the whole grid *)
      assert (Hft1 : Ψ1 [<=] Ψρ1 `union` Ψ'1).
      { pose proof (ad_pat_consis_ftag_sub Hconsis1) as Ha.
        pose proof (uskl_rho_ftag_sub Hrho1) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags1)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hft2 : Ψ2 [<=] Ψρ2 `union` Ψ'2).
      { pose proof (ad_pat_consis_ftag_sub Hconsis2) as Ha.
        pose proof (uskl_rho_ftag_sub Hrho2) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags2)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      (* the branch solved-tag split Ψa_k := Ψ_k ∩ Ψ'_k *)
      assert (Hbs1 : Ψ1 [<=] Ψρ1 `union` (Ψ1 ∩ Ψ'1))
        by (clear - Hft1; fsetdec).
      assert (Hbs2 : Ψ2 [<=] Ψρ2 `union` (Ψ2 ∩ Ψ'2))
        by (clear - Hft2; fsetdec).
      assert (Hba1 : Ψ1 ∩ Ψ'1 [<=] Ψ1) by (clear; fsetdec).
      assert (Hba2 : Ψ2 ∩ Ψ'2 [<=] Ψ2) by (clear; fsetdec).
      assert (Hint1 : Ψρ1 ∩ Ψ'1 [=] empty)
        by (clear - Hinter HΨρs HΨ's; fsetdec).
      assert (Hint2 : Ψρ2 ∩ Ψ'2 [=] empty)
        by (clear - Hinter HΨρs HΨ's; fsetdec).
      assert (HΨaeq : Ψa [=] (Ψ1 ∩ Ψ'1)
                        `union` (Ψ2 ∩ Ψ'2)).
      { clear - Hsubeq1 Hsubeq2 H Hsub Hinter HΨρs HΨ's Hft1 Hft2; fsetdec. }
      (* the P0=□ rows' target bound *)
      assert (HψaB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr ->
                ftvar_in_uskl (uskl_arrow ψa1 ψa2)
                  [<=] dom Θr `union` Δρ).
      { intros HQB.
        assert (HftR : ftvar_in_uskl (uskl_arrow R1 R2) [<=]
                  ftvar_in_bskl (bskl_arrow Q1 Q2) `union` dom Θr)
          by (eapply consis_subject_ftv_bag_bound;
                [ eapply ad_pat_consis__arrow; eassumption
                | exact HspΘ | exact Htvs | exact HwfΘr ]).
        assert (HftA : ftvar_in_uskl (uskl_arrow ψa1 ψa2) [<=]
                  ftvar_in_uskl (uskl_arrow R1 R2) `union` Δρ).
        { apply uskl_rho_ftv_target_bound with (NM := NM) (Θ := Θ)
            (Ψρ := Ψρ).
          eapply urho__arrow; [ exact Hrho1 | exact Hrho2 | exact HΨρs ]. }
        clear - HQB HftR HftA; fsetdec. }
      (* P0 = □ ⇒ Q synthesized ⇒ the consistency solves no tags *)
      assert (VACR : Θr ⨟ Δr ⊢ᵣᵃ bskl_hole ⊳ (bskl_arrow Q1 Q2) ->
                     Ψa [=] empty).
      { intros Hrh.
        pose proof (ad_refine_syn_hole_sskl Hrh eq_refl) as Hss.
        assert (HskQ1 : is_sskl Q1) by (inversion Hss; subst; assumption).
        assert (HskQ2 : is_sskl Q2) by (inversion Hss; subst; assumption).
        assert (HΨ1e : Ψ1 [=] empty)
          by (eapply ad_pat_consis_sskl_tags;
                [ exact Hconsis1 | exact HwfΘ | exact HskQ1 ]).
        assert (HΨ2e : Ψ2 [=] empty)
          by (eapply ad_pat_consis_sskl_tags;
                [ exact Hconsis2 | exact HwfΘ | exact HskQ2 ]).
        clear - Hsubeq2 H HΨ1e HΨ2e; fsetdec. }
      (* the repaired flexible-P0 discharge chain, Δ-universal via B2 *)
      assert (FLEX : forall β,
        flex_apart Θ0 Δρ (pskl_var_f β) (uskl_arrow ψa1 ψa2) ->
        a_flex_tvar Θ0 β ->
        Θr ⨟ Δr ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β)))
             ⊳ (bskl_arrow Q1 Q2) ->
        Ψa [=] empty /\
        (exists τa1 τa2, mono_ptyp τa1 /\ mono_ptyp τa2 /\
           ψa1 = ptyp_to_uskl_syn τa1 /\ ψa2 = ptyp_to_uskl_syn τa2) /\
        forall Δx,
          Θ ⨟ Δx ⊢ (msubst_pskl κ (pskl_var_f β)) ⊑ᵖ[ empty ]
            (uskl_arrow ψa1 ψa2)).
      { intros β Hapβ Hflxβ Hrefβ.
        assert (Hclean : (ftvar_in_uskl (uskl_arrow ψa1 ψa2)) ∩ Δρ [=] empty).
        { inversion Hapβ; subst.
          - assumption.
          - (* fa_var_rigid clashes with flexibility via wf-uniq *)
            exfalso.
            match goal with Hb : binds β abind_tvar _ |- _ =>
              destruct Hflxβ as [Hb' | [τx Hb']];
              pose proof (binds_unique _ _ _ _ _ Hb Hb'
                            (a_wf_aenv_uniq HwfΘ0)) as Hcc;
              discriminate Hcc
            end.
          - (* fa_flexfree clashes with flexibility directly.  NB [fa_rho_var]
               is discriminated: this target is an ARROW, not a variable. *)
            exfalso.
            match goal with Hff : pskl_flex_free _ _ |- _ =>
              apply (Hff β); [ simpl; clear; fsetdec | exact Hflxβ ] end. }
        simpl in Hclean.
        destruct (uskl_rho_clean_eq Hrho1 ltac:(clear - Hclean; fsetdec))
          as [HeqR1 HΨρ1e].
        destruct (uskl_rho_clean_eq Hrho2 ltac:(clear - Hclean; fsetdec))
          as [HeqR2 HΨρ2e].
        subst R1 R2.
        assert (Hml : mono_ptyp (msubst_lookup κ β))
          by (eapply a_inc_lookup_mono; eauto).
        simpl in Hrefβ.
        rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefβ.
        assert (Hmi : bskl_monoish (bskl_arrow Q1 Q2))
          by (eapply ad_refine_mono_paint_rhs_monoish;
                [ exact HwfΘr | exact Hrefβ | reflexivity | exact Hml ]).
        assert (Hmi1 : bskl_monoish Q1) by (inversion Hmi; assumption).
        assert (Hmi2 : bskl_monoish Q2) by (inversion Hmi; assumption).
        assert (Htsk1 : is_tskl ψa1) by (inversion Htags1; assumption).
        assert (Htsk2 : is_tskl ψa2) by (inversion Htags2; assumption).
        destruct (ad_pat_consis_monoish_counterpart Hconsis1 HwfΘ Htsk1 Hmi1)
          as (HΨ1e & τa1 & Hma1 & Heqψ1).
        destruct (ad_pat_consis_monoish_counterpart Hconsis2 HwfΘ Htsk2 Hmi2)
          as (HΨ2e & τa2 & Hma2 & Heqψ2).
        split; [ clear - Hsubeq2 H HΨ1e HΨ2e; fsetdec | ].
        split; [ exists τa1, τa2; repeat split; assumption | ].
        assert (Hcons' : Ψ ⨟ Θ ⊢ₛᵃ (uskl_arrow ψa1 ψa2)
                           ∼ (bskl_arrow Q1 Q2))
          by (eapply ad_pat_consis__arrow; eassumption).
        assert (Hrefβ' : Θ ⨟ empty ⊢ᵣᵃ (ptyp_to_bskl_syn (msubst_lookup κ β))
                           ⊳ (bskl_arrow Q1 Q2))
          by (eapply refine_primary_to_plain_split; eassumption).
        intros Δx.
        simpl.
        rewrite Heqψ1, Heqψ2.
        change (uskl_arrow (ptyp_to_uskl_syn τa1) (ptyp_to_uskl_syn τa2))
          with (ptyp_to_uskl_syn (ptyp_arrow τa1 τa2)).
        eapply mono_paint_paint_refine_consis_ppre with (Δr := empty);
          [ exact Hcons' | exact HwfΘ | rewrite Heqψ1, Heqψ2; reflexivity
          | apply mono_ptyp__arrow; assumption
          | clear; fsetdec | exact Hml | exact Hrefβ' ]. }
      (* CORE: the grid, by strong induction on the sizes *)
      assert (CORE : forall n Pi P0 Ψi,
        size_pskl Pi + size_pskl P0 <= n ->
        Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
        Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
        (forall α, α `in` Δρ ->
           α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
        flex_apart Θ0 Δρ P0 (uskl_arrow ψa1 ψa2) ->
        Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_arrow ψa1 ψa2) ->
        Θr ⨟ Δr ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0))
              ⊳ (bskl_arrow Q1 Q2) ->
        exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
          forall Δ',
            Δ' ∩ Δ [=] empty ->
            Δ' ∩ dom Θr [=] empty ->
            delta_def_fresh Δ' Θ ->
            Θ ⨟ (Δ `union` Δ') ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ]
              (uskl_arrow ψa1 ψa2)).
      { intros n; induction n as [ | n IHn ];
          intros Pi0 P00 Ψi0 Hn HwfPi0 HwfP00 Hshield0 Hap1 Hpre1
            Hrefine1.
        { pose proof (size_pskl_min Pi0); pose proof (size_pskl_min P00);
          lia. }
        destruct Pi0 as [ | nb | β | Pi1 Pi2 | Pib | | Pi' ].
        - (* Pi = unit: no precision into an arrow *)
          simpl in Hpre1. inversion Hpre1.
        - (* Pi = var_b *) inversion HwfPi0.
        - (* Pi = var β: SE-Var; a mono-paint subject forces Ψ' = ∅ *)
          assert (HΨ'e : Ψ' [=] empty).
          { eapply ad_ppre_mono_subject_target_tags_empty
              with (τ := msubst_lookup κ β);
              [ exact HwfΘ | exact Hpre1 | reflexivity
              | eapply a_inc_lookup_mono; eauto
              | exact (a_tags_sort_d_tags Htags0) ]. }
          assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
          exists (pskl_var_f β); split; [ apply a_solve_eq__var | ].
          intros Δ' HS1 HS2 HS3.
          eapply ad_partial_precise_psi_cong;
            [ eapply ad_ppre_no_hole_subject_delta_mono;
                [ exact Hpre1
                | apply msubst_pskl_no_hole; simpl; exact I
                | clear; fsetdec ]
            | clear - HΨae; fsetdec ].
        - (* Pi = arrow Pi1 Pi2 *)
          assert (HwfPi1 : Θ0 ⨟ empty ⊢ₚₛᵃ Pi1)
            by (inversion HwfPi0; assumption).
          assert (HwfPi2 : Θ0 ⨟ empty ⊢ₚₛᵃ Pi2)
            by (inversion HwfPi0; assumption).
          destruct P00 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          + (* P0 = unit: refinement absurd *)
            simpl in Hrefine1. inversion Hrefine1.
          + (* P0 = var_b *) inversion HwfP00.
          + (* P0 = var β: rigid absurd / flexible = the repaired subcase *)
            inversion HwfP00; subst;
            match goal with Hor : _ \/ a_binds_tvar β _ |- _ =>
              destruct Hor as [Hemp | Habt] end;
              [ clear - Hemp; fsetdec | ].
            destruct Habt as [Hrig | Hflx].
            * (* rigid: no refinement into an arrow *)
              exfalso.
              assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
                by (eapply msubst_pskl_tvar_id;
                    [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
              rewrite Hmid in Hrefine1. simpl in Hrefine1.
              eapply (ad_refine_syn_rigid_var_nonvar_absurd_sub Hrefine1);
                [ intros x b Hb; eapply aenv_split_sub_r;
                    [ exact HspΘ | exact Hb ]
                | apply a_wf_aenv_uniq; exact HwfΘ
                | eapply a_inc_binds_tvar; eauto
                | intros β0 Hcc; discriminate Hcc ].
            * (* flexible: SE-FlexR + the discharge chain *)
              destruct (FLEX β Hap1 Hflx Hrefine1)
                as (HΨae
                    & (τa1 & τa2 & Hma1 & Hma2 & Heq1 & Heq2) & Hqf).
              assert (HΨie : Ψi0 [=] empty).
              { rewrite Heq1, Heq2 in Hpre1.
                eapply ad_ppre_mono_tags_empty
                  with (τ := ptyp_arrow τa1 τa2);
                  [ exact HwfΘ | exact Hpre1 | reflexivity
                  | apply mono_ptyp__arrow; assumption ]. }
              exists (pskl_var_f β); split.
              -- apply a_solve_eq__flex_r;
                   [ exact Hflx
                   | split; [ eapply a_wf_pskl_lc; exact HwfPi0
                            | intros Hf; inversion Hf ] ].
              -- intros Δ' HS1 HS2 HS3.
                 eapply ad_partial_precise_psi_cong;
                   [ exact (Hqf (Δ `union` Δ'))
                   | clear - HΨie HΨae; fsetdec ].
          + (* P0 = arrow P01 P02: componentwise via the branch main IHs *)
            assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01)
              by (inversion HwfP00; assumption).
            assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02)
              by (inversion HwfP00; assumption).
            destruct (flex_apart_arrow_inv Hap1) as [Hap01 Hap02].
            simpl in Hrefine1.
            destruct (ad_refine_arrow_arrow_inv Hrefine1) as [Hrb1 Hrb2].
            simpl in Hpre1.
            destruct (ad_ppre_arrow_arrow_inv Hpre1)
              as (Ψib1 & Ψib2 & Hpb1 & Hpb2 & HΨis).
            assert (Hsubk1 : Ψib1 `union` (Ψ1 ∩ Ψ'1)
                               [<=] Ψ'1).
            { assert (Hts : Ψib1 [<=] Ψ'1)
                by (eapply ad_partial_precise_tags_sub;
                      [ exact HwfΘ | exact Hpb1
                      | exact (a_tags_sort_d_tags Htags1) ]).
              clear - Hts; fsetdec. }
            assert (Hsubk2 : Ψib2 `union` (Ψ2 ∩ Ψ'2)
                               [<=] Ψ'2).
            { assert (Hts : Ψib2 [<=] Ψ'2)
                by (eapply ad_partial_precise_tags_sub;
                      [ exact HwfΘ | exact Hpb2
                      | exact (a_tags_sort_d_tags Htags2) ]).
              clear - Hts; fsetdec. }
            assert (Hshld1 : forall α, α `in` Δρ ->
                      α `notin` pskl_shielded_ftv (msubst_pskl κ Pi1)).
            { intros α0 HX0; pose proof (Hshield0 α0 HX0) as Hs0;
              simpl in Hs0; clear - Hs0; fsetdec. }
            assert (Hshld2 : forall α, α `in` Δρ ->
                      α `notin` pskl_shielded_ftv (msubst_pskl κ Pi2)).
            { intros α0 HX0; pose proof (Hshield0 α0 HX0) as Hs0;
              simpl in Hs0; clear - Hs0; fsetdec. }
            destruct (IHHconsis1 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ1 Ψ'1 _ _
                        ψa1 Pi1 P01
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 HwfPi1 HwfP01 Hκ Hrho1 Htags1
                        Hsubk1 Hint1 Hfresh Hdelta Hshld1 Hdfresh Hap01
                        Hpb1 Hbs1 Hba1 Hrb1)
              as (Pa1 & Hs1 & Hq1).
            destruct (IHHconsis2 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ2 Ψ'2 _ _
                        ψa2 Pi2 P02
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 HwfPi2 HwfP02 Hκ Hrho2 Htags2
                        Hsubk2 Hint2 Hfresh Hdelta Hshld2 Hdfresh Hap02
                        Hpb2 Hbs2 Hba2 Hrb2)
              as (Pa2 & Hs2 & Hq2).
            exists (pskl_arrow Pa1 Pa2); split.
            * apply a_solve_eq__arrow; assumption.
            * intros Δ' HS1 HS2 HS3.
              simpl. eapply ad_ppre__arrow;
                [ exact (Hq1 Δ' HS1 HS2 HS3) | exact (Hq2 Δ' HS1 HS2 HS3) | ].
              clear - HΨis HΨaeq; fsetdec.
          + (* P0 = all_syn: refinement absurd *)
            simpl in Hrefine1. inversion Hrefine1.
          + (* P0 = □: SE-VacuousR *)
            simpl in Hrefine1.
            assert (HΨae : Ψa [=] empty) by (apply VACR; exact Hrefine1).
            assert (HQB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr).
            { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine1).
              simpl in Ht. simpl. clear - Ht; fsetdec. }
            exists (pskl_arrow Pi1 Pi2); split;
              [ apply a_solve_eq__hole_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨae; fsetdec ].
          + (* P0 = ∀◇.P0': GuardedGhost-right + same-node recursion *)
            assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
              by (inversion HwfP00; assumption).
            simpl in Hrefine1.
            inversion Hrefine1; subst.
            match goal with
            | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _
              |- _ =>
              destruct (IHn (pskl_arrow Pi1 Pi2) P0' Ψi0
                          ltac:(simpl in Hn; simpl; lia)
                          HwfPi0 HwfP0' Hshield0
                          (flex_apart_tophole_p0_inv Hap1) Hpre1 Hin)
                as (Pa & Hs & Hq)
            end.
            exists Pa; split.
            * apply a_solve_eq__tophole_r_guarded;
                [ apply guarded_pskl__arrow;
                    [ eapply a_wf_pskl_lc; exact HwfPi1
                    | eapply a_wf_pskl_lc; exact HwfPi2 ]
                | exact Hs ].
            * exact Hq.
        - (* Pi = all_syn: no precision into an arrow *)
          simpl in Hpre1. inversion Hpre1.
        - (* Pi = □ *)
          simpl in Hpre1.
          assert (HΨie : Ψi0 [=] empty) by (inversion Hpre1; assumption).
          assert (Hhd : Δ ∩
                    (ftvar_in_uskl (uskl_arrow ψa1 ψa2)) [=] empty)
            by (inversion Hpre1; assumption).
          simpl in Hhd.
          destruct P00 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          + (* P0 = unit: refinement absurd *)
            simpl in Hrefine1. inversion Hrefine1.
          + (* P0 = var_b *) inversion HwfP00.
          + (* P0 = var β: rigid absurd / flexible via SE-GhostL + FLEX *)
            inversion HwfP00; subst;
            match goal with Hor : _ \/ a_binds_tvar β _ |- _ =>
              destruct Hor as [Hemp | Habt] end;
              [ clear - Hemp; fsetdec | ].
            destruct Habt as [Hrig | Hflx].
            * exfalso.
              assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
                by (eapply msubst_pskl_tvar_id;
                    [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
              rewrite Hmid in Hrefine1. simpl in Hrefine1.
              eapply (ad_refine_syn_rigid_var_nonvar_absurd_sub Hrefine1);
                [ intros x b Hb; eapply aenv_split_sub_r;
                    [ exact HspΘ | exact Hb ]
                | apply a_wf_aenv_uniq; exact HwfΘ
                | eapply a_inc_binds_tvar; eauto
                | intros β0 Hcc; discriminate Hcc ].
            * destruct (FLEX β Hap1 Hflx Hrefine1) as (HΨae & _ & Hqf).
              exists (pskl_var_f β); split; [ apply a_solve_eq__hole_l | ].
              intros Δ' HS1 HS2 HS3.
              eapply ad_partial_precise_psi_cong;
                [ exact (Hqf (Δ `union` Δ'))
                | clear - HΨie HΨae; fsetdec ].
          + (* P0 = arrow: □-precisions per branch + branch main IHs *)
            assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01)
              by (inversion HwfP00; assumption).
            assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02)
              by (inversion HwfP00; assumption).
            destruct (flex_apart_arrow_inv Hap1) as [Hap01 Hap02].
            simpl in Hrefine1.
            destruct (ad_refine_arrow_arrow_inv Hrefine1) as [Hrb1 Hrb2].
            assert (Hp01 : Θ ⨟ Δ ⊢ msubst_pskl κ pskl_hole
                             ⊑ᵖ[ empty ] ψa1).
            { simpl. apply ad_ppre__hole;
                [ clear; fsetdec | clear - Hhd; fsetdec ]. }
            assert (Hp02 : Θ ⨟ Δ ⊢ msubst_pskl κ pskl_hole
                             ⊑ᵖ[ empty ] ψa2).
            { simpl. apply ad_ppre__hole;
                [ clear; fsetdec | clear - Hhd; fsetdec ]. }
            assert (Hsubk01 : empty `union` (Ψ1 ∩ Ψ'1)
                                [<=] Ψ'1) by (clear; fsetdec).
            assert (Hsubk02 : empty `union` (Ψ2 ∩ Ψ'2)
                                [<=] Ψ'2) by (clear; fsetdec).
            destruct (IHHconsis1 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ1 Ψ'1 _ _
                        ψa1 pskl_hole P01
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 ltac:(apply a_wf_pskl__hole) HwfP01
                        Hκ
                        Hrho1 Htags1 Hsubk01 Hint1 Hfresh Hdelta
                        ltac:(intros α0 HX0; simpl; auto)
                        Hdfresh Hap01 Hp01 Hbs1 Hba1 Hrb1)
              as (Pa1 & Hs1 & Hq1).
            destruct (IHHconsis2 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ2 Ψ'2 _ _
                        ψa2 pskl_hole P02
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 ltac:(apply a_wf_pskl__hole) HwfP02
                        Hκ
                        Hrho2 Htags2 Hsubk02 Hint2 Hfresh Hdelta
                        ltac:(intros α0 HX0; simpl; auto)
                        Hdfresh Hap02 Hp02 Hbs2 Hba2 Hrb2)
              as (Pa2 & Hs2 & Hq2).
            pose proof (a_solve_eq_hole_subject_inv Hs1) as HPa1e;
              subst Pa1.
            pose proof (a_solve_eq_hole_subject_inv Hs2) as HPa2e;
              subst Pa2.
            exists (pskl_arrow P01 P02); split;
              [ apply a_solve_eq__hole_l | ].
            intros Δ' HS1 HS2 HS3.
            simpl. eapply ad_ppre__arrow;
              [ exact (Hq1 Δ' HS1 HS2 HS3) | exact (Hq2 Δ' HS1 HS2 HS3) | ].
            clear - HΨie HΨaeq; fsetdec.
          + (* P0 = all_syn: refinement absurd *)
            simpl in Hrefine1. inversion Hrefine1.
          + (* P0 = □: SE-VacuousR *)
            simpl in Hrefine1.
            assert (HΨae : Ψa [=] empty) by (apply VACR; exact Hrefine1).
            assert (HQB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr).
            { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine1).
              simpl in Ht. simpl. clear - Ht; fsetdec. }
            exists pskl_hole; split; [ apply a_solve_eq__hole_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨae; fsetdec ].
          + (* P0 = ∀◇.P0': SE-GhostL + same-node recursion at (□, P0') *)
            assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
              by (inversion HwfP00; assumption).
            simpl in Hrefine1.
            inversion Hrefine1; subst.
            match goal with
            | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _
              |- _ =>
              destruct (IHn pskl_hole P0' Ψi0
                          ltac:(simpl in Hn; simpl; lia)
                          ltac:(apply a_wf_pskl__hole) HwfP0'
                          ltac:(intros α0 HX0; simpl; auto)
                          (flex_apart_tophole_p0_inv Hap1) Hpre1 Hin)
                as (Pa' & Hs' & Hq')
            end.
            pose proof (a_solve_eq_hole_subject_inv Hs') as HPa'e;
              subst Pa'.
            exists (pskl_tophole P0'); split;
              [ apply a_solve_eq__hole_l | ].
            intros Δ' HS1 HS2 HS3.
            simpl. apply ad_ppre__tophole_remove.
            exact (Hq' Δ' HS1 HS2 HS3).
        - (* Pi = ∀◇.Pi' *)
          assert (HgPi' : guarded_pskl Pi')
            by (inversion HwfPi0; assumption).
          assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi')
            by (inversion HwfPi0; assumption).
          simpl in Hpre1.
          inversion Hpre1; subst.
          match goal with
          | Hp' : _ ⨟ _ ⊢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_arrow ψa1 ψa2
            |- _ => rename Hp' into Hpre'
          end.
          assert (Hshield' : forall α, α `in` Δρ ->
                    α `notin` pskl_shielded_ftv (msubst_pskl κ Pi')).
          { intros α0 HX0.
            pose proof (Hshield0 α0 HX0) as Hsh0. simpl in Hsh0.
            pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi')).
            fsetdec. }
          destruct P00 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          + (* P0 = unit: GhostGuarded *)
            destruct (IHn Pi' pskl_unit Ψi0
                        ltac:(simpl in Hn; simpl; lia)
                        HwfPi' HwfP00 Hshield' Hap1 Hpre' Hrefine1)
              as (Pa & Hs & Hq).
            exists Pa; split;
              [ apply a_solve_eq__tophole_l_guarded;
                  [ apply guarded_pskl__unit | exact Hs ]
              | exact Hq ].
          + (* P0 = var_b *) inversion HwfP00.
          + (* P0 = var: GhostGuarded (a var is guarded) *)
            destruct (IHn Pi' (pskl_var_f β) Ψi0
                        ltac:(simpl in Hn; simpl; lia)
                        HwfPi' HwfP00 Hshield' Hap1 Hpre' Hrefine1)
              as (Pa & Hs & Hq).
            exists Pa; split;
              [ apply a_solve_eq__tophole_l_guarded;
                  [ apply guarded_pskl__var | exact Hs ]
              | exact Hq ].
          + (* P0 = arrow: GhostGuarded *)
            assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01)
              by (inversion HwfP00; assumption).
            assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02)
              by (inversion HwfP00; assumption).
            destruct (IHn Pi' (pskl_arrow P01 P02) Ψi0
                        ltac:(simpl in Hn; simpl; lia)
                        HwfPi' HwfP00 Hshield' Hap1 Hpre' Hrefine1)
              as (Pa & Hs & Hq).
            exists Pa; split;
              [ apply a_solve_eq__tophole_l_guarded;
                  [ apply guarded_pskl__arrow;
                      [ eapply a_wf_pskl_lc; exact HwfP01
                      | eapply a_wf_pskl_lc; exact HwfP02 ]
                  | exact Hs ]
              | exact Hq ].
          + (* P0 = all_syn: refinement absurd *)
            simpl in Hrefine1. inversion Hrefine1.
          + (* P0 = □: SE-VacuousR *)
            simpl in Hrefine1.
            assert (HΨae : Ψa [=] empty) by (apply VACR; exact Hrefine1).
            assert (HQB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr).
            { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine1).
              simpl in Ht. simpl. clear - Ht; fsetdec. }
            exists (pskl_tophole Pi'); split;
              [ apply a_solve_eq__hole_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨae; fsetdec ].
          + (* P0 = ∀◇.P0': SE-UnivGhost *)
            assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
              by (inversion HwfP00; assumption).
            simpl in Hrefine1.
            inversion Hrefine1; subst.
            match goal with
            | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _
              |- _ =>
              destruct (IHn Pi' P0' Ψi0
                          ltac:(simpl in Hn; lia)
                          HwfPi' HwfP0' Hshield'
                          (flex_apart_tophole_p0_inv Hap1) Hpre' Hin)
                as (Pa' & Hs' & Hq')
            end.
            exists (pskl_tophole Pa'); split;
              [ apply a_solve_eq__tophole_both; exact Hs' | ].
            intros Δ' HS1 HS2 HS3.
            simpl. apply ad_ppre__tophole_remove.
            exact (Hq' Δ' HS1 HS2 HS3). }
      assert (Hsz : size_pskl Pi + size_pskl P0
                      <= size_pskl Pi + size_pskl P0) by lia.
      eapply CORE;
        [ exact Hsz | exact HwfPi | exact HwfP0 | exact Hshield
        | exact Hap0 | exact Hpre0 | exact Hrefine ]. }
    destruct (uskl_rho_arrow_l_inv Hrho)
      as [[Heqψa HΨρe]
         | [Hleaf | (ψa1 & ψa2 & Ψρ1 & Ψρ2 & Heqψa & Hrho1 & Hrho2 & HΨρs)]].
    + (* refl: recast as a congruence with refl branch-ρs *)
      subst ψa.
      assert (Htsk : is_tskl (uskl_arrow R1 R2))
        by (inversion Htags; assumption).
      assert (HlcR1 : lc_uskl R1)
        by (apply is_tskl_lc; inversion Htsk; assumption).
      assert (HlcR2 : lc_uskl R2)
        by (apply is_tskl_lc; inversion Htsk; assumption).
      apply (KEY R1 R2 empty empty);
        [ apply urho__refl; [ exact HlcR1 | clear; fsetdec ]
        | apply urho__refl; [ exact HlcR2 | clear; fsetdec ]
        | clear - HΨρe; fsetdec
        | exact Htags | exact Hapart | exact Hpre ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf)
        as (Pa & Hs & Hq).
      exists Pa; split; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
    + subst ψa.
      apply (KEY ψa1 ψa2 Ψρ1 Ψρ2);
        [ exact Hrho1 | exact Hrho2 | exact HΨρs
        | exact Htags | exact Hapart | exact Hpre ].
  - (* forall_inh_tagged (case 1): rows A (Pi=∀) / B (Pi=□) / C (Pi=∀◇
       via the precision fill); everything else is absurd (guardedness /
       paint-shape / ε-tag contradictions).  DESIGN §6(o). *)
    assert (HwfΘr2 := HwfΘr).
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hκ).
    assert (Himav : forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ)
      by (intros p Hp; eapply a_inc_image_ftv_dom; [ exact Hκ | exact Hp ]).
    assert (KEYF : forall ψR Lr,
      (forall α, α `notin` Lr ->
         uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl R (uskl_var_f α))
                             (open_uskl_wrt_uskl ψR (uskl_var_f α))) ->
      a_tags_sort NM Ψ' (uskl_all_etag ε ψR) ->
      flex_apart Θ0 Δρ P0 (uskl_all_etag ε ψR) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_all_etag ε ψR) ->
      exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
        forall Δ',
          Δ' ∩ Δ [=] empty ->
          Δ' ∩ dom Θr [=] empty ->
          delta_def_fresh Δ' Θ ->
          Θ ⨟ (Δ `union` Δ') ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ]
            (uskl_all_etag ε ψR)).
    { intros ψR Lr Hrhof Htags0 Hap0 Hpre0.
      destruct (a_tags_sort_all_etag_inv Htags0)
        as (Lt & Ψ0' & Htagsf & Hεnin & HΨ'eq).
      (* ε is premise-solved: it is a Ψ'-tag, hence never ρ-introduced *)
      assert (Hεa : ε `in` Ψa)
        by (clear - H1 Hsubeq1 Hinter HΨ'eq; fsetdec).
      (* the body ftag flow, at one fresh variable *)
      assert (HbF : Ψ0 [<=] Ψρ `union` Ψ0').
      { pick fresh αf for (L `union` Lr `union` Lt).
        pose proof (ad_pat_consis_ftag_sub
                      (H αf ltac:(clear - Fr; solve_notin))) as Ha.
        pose proof (uskl_rho_ftag_sub
                      (Hrhof αf ltac:(clear - Fr; solve_notin))) as Hb.
        pose proof (d_tags_skl_ftag
                      (a_tags_sort_d_tags
                         (Htagsf αf ltac:(clear - Fr; solve_notin)))) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hsubeq1b : Ψ0 [<=] Ψρ `union` (remove ε Ψa))
        by (clear - H1 Hsubeq1 HbF Hεnin HΨ'eq Hinter; fsetdec).
      assert (Hsubeq2b : (remove ε Ψa) [<=] Ψ0)
        by (clear - H1 Hsubeq2; fsetdec).
      assert (Hintb : Ψρ ∩ Ψ0' [=] empty)
        by (clear - Hinter HΨ'eq; fsetdec).
      assert (Hdomsub : dom Θr [<=] dom Θ)
        by (eapply aenv_split_dom_r; exact HspΘ).
      (* P0-grid: only P0 = ∀.P0b survives the refinement *)
      destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
      - (* unit *) simpl in Hrefine. inversion Hrefine.
      - (* var_b *) inversion HwfP0.
      - (* var β: rigid / flexible both die against all_inh *)
        exfalso.
        assert (Hor : β `in` empty \/ a_binds_tvar β Θ0)
          by (inversion HwfP0; subst; assumption).
        destruct Hor as [Hemp | Habt]; [ clear - Hemp; fsetdec | ].
        destruct Habt as [Hrig | Hflx].
        + assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
            by (eapply msubst_pskl_tvar_id;
                [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
          rewrite Hmid in Hrefine. simpl in Hrefine.
          eapply (ad_refine_syn_rigid_var_nonvar_absurd_sub Hrefine)
            with (Θfull := Θ);
            [ intros x b Hb; eapply aenv_split_sub_r;
                [ exact HspΘ | exact Hb ]
            | apply a_wf_aenv_uniq; exact HwfΘ
            | eapply a_inc_binds_tvar; eauto
            | intros β0 Hcc; discriminate Hcc ].
        + assert (Hml : mono_ptyp (msubst_lookup κ β))
            by (eapply a_inc_lookup_mono; eauto).
          simpl in Hrefine.
          rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
          eapply ad_refine_mono_paint_allinh_rhs_absurd;
            [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
            | exact Hml ].
      - (* arrow *) simpl in Hrefine. inversion Hrefine.
      - (* P0 = ∀.P0b: the REAL column *)
        assert (HwfP0f : exists Lw0, forall α, α `notin` Lw0 ->
                  ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                  (open_pskl_wrt_pskl P0b (pskl_var_f α))).
        { assert (Hi : exists Lw0, forall α0, α0 `notin` Lw0 ->
                    Θ0 ⨟ (add α0 empty) ⊢ₚₛᵃ
                    (open_pskl_wrt_pskl P0b (pskl_var_f α0)))
            by (inversion HwfP0; subst; eexists; eassumption).
          destruct Hi as (Lw0 & Hi).
          exists Lw0; intros α0 Hα0.
          eapply a_wf_pskl_delta_to_tvar;
            [ apply Hi; exact Hα0 | clear; fsetdec ]. }
        destruct HwfP0f as (Lw0 & HwfP0f).
        assert (Hreff : exists Lq, forall α, α `notin` Lq ->
          Θr ⨟ (add α Δr) ⊢ᵣᵃ
            pskl_to_bskl_inh (msubst_pskl κ
              (open_pskl_wrt_pskl P0b (pskl_var_f α)))
            ⊳ open_bskl_wrt_bskl Q (bskl_var_f α)).
        { simpl in Hrefine.
          inversion Hrefine; subst.
          match goal with
          | Hf : forall α0, α0 `notin` ?L0 -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ _ |- _ =>
            exists (L0 `union` dom κ); intros α0 Hα0;
            rewrite msubst_pskl_open_lc_local;
              [ | exact Hlcκ | clear - Hα0; fsetdec ];
            rewrite pskl_to_bskl_inh_open;
            apply Hf; clear - Hα0; fsetdec
          end. }
        destruct Hreff as (Lq & Hreff).
        assert (HapFp : exists La, forall α, α `notin` La ->
                  flex_apart Θ0 Δρ (open_pskl_wrt_pskl P0b (pskl_var_f α))
                             (open_uskl_wrt_uskl ψR (uskl_var_f α)))
          by (destruct (flex_apart_all_etag_forall_inv Hap0) as (La & Hf);
              exists La; exact Hf).
        destruct HapFp as (La & HapF).
        (* the shared body-IH invocation *)
        assert (IHX : forall α Pi0 Ψi0 Δx,
          α `notin` (L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b) ->
          Δρ [<=] Δx -> Δx [<=] add α Δ ->
          ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi0 ->
          (forall α0, α0 `in` Δρ ->
             α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi0)) ->
          ((α ~ abind_tvar) ++ Θ) ⨟ Δx ⊢ (msubst_pskl κ Pi0)
              ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψR (uskl_var_f α)) ->
          Ψi0 [<=] Ψ0' ->
          exists Pa0, ((α ~ abind_tvar) ++ Θ0) ⊢ₑ Pi0 ∼
               (open_pskl_wrt_pskl P0b (pskl_var_f α)) ⤳ Pa0 /\
            forall Δ', Δ' ∩ Δx [=] empty ->
              Δ' ∩ dom Θr [=] empty ->
              delta_def_fresh Δ' ((α ~ abind_tvar) ++ Θ) ->
              ((α ~ abind_tvar) ++ Θ) ⨟ (Δx `union` Δ')
                ⊢ (msubst_pskl κ Pa0)
                  ⊑ᵖ[ Ψi0 `union` (remove ε Ψa) ]
                  (open_uskl_wrt_uskl ψR (uskl_var_f α))).
        { intros α Pi0 Ψi0 Δx HXf HΔρx HΔxs HwfPi0 Hshld0 Hpre0x HΨi0s.
          apply (H0 α ltac:(clear - HXf; solve_notin)
                   NM ((α ~ abind_tvar) ++ Θ0)
                   ((α ~ abind_tvar) ++ Θtv) Θr Θ0r κ
                   Δx Δρ (add α Δr) Ψρ Ψ0' Ψi0 (remove ε Ψa)
                   (open_uskl_wrt_uskl ψR (uskl_var_f α))
                   Pi0 (open_pskl_wrt_pskl P0b (pskl_var_f α))).
          - apply aenv_split_cons_tv; [ exact HspΘ | clear - HXf; solve_notin ].
          - apply aenv_split_cons_tv; [ exact HspΘ0 | clear - HXf; solve_notin ].
          - exact HwfΘr.
          - intros x b Hb.
            destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
              [ exact Heqb | exact (Htvs _ _ Hb') ].
          - simpl. clear - HΔrd; fsetdec.
          - simpl. clear - HΔρtv HXf; destruct_notin; fsetdec.
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ ].
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ0 ].
          - exact HwfPi0.
          - apply HwfP0f. clear - HXf; solve_notin.
          - apply a_inc__tvar with (Ξ := (@nil (atom * abind)));
              [ exact Hκ | apply a_suffix__nil ].
          - eapply uskl_rho_weaken;
              [ apply Hrhof; clear - HXf; solve_notin
              | intros x b Hb; apply binds_cons_3; exact Hb ].
          - apply Htagsf. clear - HXf; solve_notin.
          - clear - HΨi0s Hsub HΨ'eq; fsetdec.
          - exact Hintb.
          - intros x Hx.
            destruct (Hfresh x Hx) as (Hb & Hav & Hdef).
            repeat split.
            + apply binds_cons_3; exact Hb.
            + exact Hav.
            + intros αd τ Hbd.
              destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
                [ discriminate Hc | exact (Hdef _ _ Hbd') ].
          - exact HΔρx.
          - exact Hshld0.
          - intros Yd αd τ HYd Hbd.
            destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
              [ discriminate Hc | ].
            assert (HYx : Yd `in` add α Δ) by (clear - HYd HΔxs; fsetdec).
            destruct (Yd == α) as [-> | Hne].
            + assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                by (eapply a_wf_aenv_def_ftv_dom;
                    [ exact HwfΘ | exact Hbd' ]).
              clear - Hd HXf; destruct_notin; fsetdec.
            + eapply Hdfresh; [ | exact Hbd' ].
              clear - HYx Hne; fsetdec.
          - eapply flex_apart_weaken;
              [ apply HapF; clear - HXf; solve_notin
              | intros x b Hb; apply binds_cons_3; exact Hb
              | apply a_flex_tvar_strip_tvar ].
          - exact Hpre0x.
          - exact Hsubeq1b.
          - exact Hsubeq2b.
          - apply Hreff. clear - HXf; solve_notin. }
        (* the shared per-instance fold: strengthen + rename + rewrites *)
        assert (FOLD : forall α PaR Ψc Δ',
          α `notin` (L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b) ->
          Δ' ∩ Δ [=] empty ->
          Δ' ∩ dom Θr [=] empty ->
          delta_def_fresh Δ' Θ ->
          ((α ~ abind_tvar) ++ Θ)
            ⨟ (add α (Δ `union` (remove α Δ')))
            ⊢ (msubst_pskl κ PaR) ⊑ᵖ[ Ψc ]
              (open_uskl_wrt_uskl ψR (uskl_var_f α)) ->
          forall α', α' `notin` (L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b `union` Δ' `union` singleton α
              `union` ftvar_in_pskl (msubst_pskl κ PaR)) ->
          Θ ⨟ (add α' (Δ `union` Δ')) ⊢
            (msubst_pskl κ (open_pskl_wrt_pskl
               (close_pskl_wrt_pskl α PaR) (pskl_var_f α')))
            ⊑ᵖ[ Ψc ] (open_uskl_wrt_uskl ψR (uskl_var_f α'))).
        { intros α PaR Ψc Δ' HXf HS1 HS2 HS3 Hrun α' HX'f.
          assert (Hst : Θ ⨟ (add α (Δ `union` (remove α Δ')))
                   ⊢ (msubst_pskl κ PaR) ⊑ᵖ[ Ψc ]
                   (open_uskl_wrt_uskl ψR (uskl_var_f α)))
            by (eapply ad_partial_precise_strengthen_tvar;
                [ exact Hrun | clear; fsetdec ]).
          assert (Hrn : Θ ⨟ (add α' (remove α (add α (Δ `union` (remove α Δ')))))
                   ⊢ (subst_pskl_in_pskl (pskl_var_f α') α
                        (msubst_pskl κ PaR))
                   ⊑ᵖ[ Ψc ]
                   (subst_bskl_in_uskl (uskl_var_f α') α
                        (open_uskl_wrt_uskl ψR (uskl_var_f α)))).
          { eapply ad_partial_precise_rename;
              [ exact Hst
              | clear; fsetdec
              | clear - HXf; solve_notin
              | clear - HX'f; solve_notin
              | clear - HX'f; solve_notin
              | clear - HX'f; solve_notin
              | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                              (uskl_var_f α)) as Hup;
                simpl in Hup; clear - HX'f Hup; destruct_notin; fsetdec
              | intros αd τ Hbd;
                assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                  by (eapply a_wf_aenv_def_ftv_dom;
                      [ exact HwfΘ | exact Hbd ]);
                split; [ clear - Hd HXf; destruct_notin; fsetdec
                       | clear - Hd HX'f; destruct_notin; fsetdec ] ]. }
          rewrite <- (subst_bskl_in_uskl_intro α ψR (uskl_var_f α')
                        ltac:(clear - HXf; solve_notin)) in Hrn.
          rewrite (@msubst_pskl_subst_var κ PaR α α'
                     ltac:(clear - HXf; solve_notin)
                     ltac:(clear - HX'f; solve_notin)
                     ltac:(intros p Hp;
                           pose proof (Himav p Hp) as Hd;
                           clear - Hd HXf; destruct_notin; fsetdec)) in Hrn.
          rewrite (subst_pskl_in_pskl_spec PaR (pskl_var_f α') α) in Hrn.
          eapply ad_partial_precise_delta_cong;
            [ eapply ad_partial_precise_delta_weaken_fresh
                with (Δ' := Δ' ∩ singleton α);
                [ exact Hrn
                | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                (uskl_var_f α')) as Hup;
                  simpl in Hup;
                  apply atoms_inter_empty_pointwise;
                  intros y Hy;
                  assert (Heqy : y = α) by (clear - Hy; fsetdec);
                  subst y;
                  clear - HXf HX'f Hup; destruct_notin; fsetdec
                | intros Yd αd τ HYd Hbd;
                  assert (Heqy : Yd = α) by (clear - HYd; fsetdec);
                  subst Yd;
                  assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                    by (eapply a_wf_aenv_def_ftv_dom;
                        [ exact HwfΘ | exact Hbd ]);
                  clear - Hd HXf; destruct_notin; fsetdec ]
            | clear - HXf HX'f; destruct_notin; fsetdec ]. }
        (* ---- the Pi grid ---- *)
        destruct Pi as [ | nb | β | Pi1 Pi2 | Pib | | Pi' ].
        + (* unit *) simpl in Hpre0. inversion Hpre0.
        + (* var_b *) inversion HwfPi.
        + (* var: a mono-paint subject vs the ε-tagged target *)
          exfalso.
          assert (HΨ'e : Ψ' [=] empty).
          { eapply ad_ppre_mono_subject_target_tags_empty
              with (τ := msubst_lookup κ β);
              [ exact HwfΘ | exact Hpre0 | reflexivity
              | eapply a_inc_lookup_mono; eauto
              | exact (a_tags_sort_d_tags Htags0) ]. }
          assert (Hcon : ε `in` empty).
          { apply (proj1 (HΨ'e ε)). apply (proj2 (HΨ'eq ε)).
            clear; fsetdec. }
          clear - Hcon; fsetdec.
        + (* arrow *) simpl in Hpre0. inversion Hpre0.
        + (* Pi = ∀.Pib — ROW A: SE-Forall from a single fresh-α run;
             the family folds via FOLD (family{α} → strengthen → rename) *)
          assert (HwfPif : exists Lwi, forall α, α `notin` Lwi ->
                    ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                    (open_pskl_wrt_pskl Pib (pskl_var_f α))).
          { assert (Hi : exists Lwi, forall α0, α0 `notin` Lwi ->
                      Θ0 ⨟ (add α0 empty) ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl Pib (pskl_var_f α0)))
              by (inversion HwfPi; subst; eexists; eassumption).
            destruct Hi as (Lwi & Hi).
            exists Lwi; intros α0 Hα0.
            eapply a_wf_pskl_delta_to_tvar;
              [ apply Hi; exact Hα0 | clear; fsetdec ]. }
          destruct HwfPif as (Lwi & HwfPif).
          assert (HpreF : exists Lp Ψi',
            (forall α, α `notin` Lp ->
               Θ ⨟ (add α Δ) ⊢
                 (msubst_pskl κ (open_pskl_wrt_pskl Pib (pskl_var_f α)))
                 ⊑ᵖ[ Ψi' ] (open_uskl_wrt_uskl ψR (uskl_var_f α))) /\
            Ψi [=] add ε Ψi').
          { simpl in Hpre0.
            inversion Hpre0; subst.
            match goal with
            | Hf : forall α0, α0 `notin` ?L0 ->
                _ ⨟ _ ⊢ _ ⊑ᵖ[ ?PS ] _ |- _ =>
              exists (L0 `union` dom κ), PS; split;
                [ intros α0 Hα0;
                  rewrite msubst_pskl_open_lc_local;
                    [ apply Hf; clear - Hα0; fsetdec
                    | exact Hlcκ | clear - Hα0; fsetdec ]
                | assumption ]
            end. }
          destruct HpreF as (Lp & Ψi' & HpreF & HΨis).
          assert (HΨi's : Ψi' [<=] Ψ0').
          { pick fresh αp for (Lp `union` Lt).
            eapply ad_partial_precise_tags_sub;
              [ exact HwfΘ
              | apply HpreF; clear - Fr; solve_notin
              | exact (a_tags_sort_d_tags
                        (Htagsf αp ltac:(clear - Fr; solve_notin))) ]. }
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
               `union` Lwi `union` Lp `union` ftvar_in_pskl Pib).
          destruct (IHX α (open_pskl_wrt_pskl Pib (pskl_var_f α)) Ψi'
                      (add α Δ)
                      ltac:(clear - Fr; solve_notin)
                      ltac:(clear - Hdelta; fsetdec)
                      ltac:(clear; fsetdec)
                      (HwfPif α ltac:(clear - Fr; solve_notin))
                      ltac:(intros α0 HX0;
                            pose proof (Hshield α0 HX0) as Hs0;
                            simpl in Hs0;
                            rewrite msubst_pskl_open_lc_local;
                              [ | exact Hlcκ | clear - Fr; solve_notin ];
                            pose proof (pskl_shielded_ftv_open_upper
                              (msubst_pskl κ Pib) (pskl_var_f α)) as Hup;
                            simpl in Hup;
                            assert (HneX0 : α0 <> α)
                              by (clear - HX0 Fr; destruct_notin; fsetdec);
                            clear - Hs0 Hup HneX0; fsetdec)
                      ltac:(eapply ad_partial_precise_weaken;
                              [ apply HpreF; clear - Fr; solve_notin
                              | intros x b Hb; apply binds_cons_3;
                                exact Hb ])
                      HΨi's)
            as (PaX & HsX & HqX).
          assert (HsX0 : Θ0 ⊢ₑ (open_pskl_wrt_pskl Pib (pskl_var_f α))
                    ∼ (open_pskl_wrt_pskl P0b (pskl_var_f α)) ⤳ PaX)
            by (eapply a_solve_eq_strengthen_tvar; exact HsX).
          exists (pskl_all_syn (close_pskl_wrt_pskl α PaX)); split.
          { apply a_solve_eq__forall with
              (L := L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
                 `union` Lwi `union` Lp `union` singleton α
                 `union` ftvar_in_pskl Pib `union` ftvar_in_pskl PaX).
            intros β Hβ.
            pose proof ((proj2 a_solve_sub_eq_rename) _ _ _ _ HsX0 α β
                          ltac:(clear - Fr; solve_notin)
                          ltac:(clear - Hβ; fsetdec)) as Hrn.
            rewrite <- (subst_pskl_in_pskl_intro α Pib (pskl_var_f β)
                          ltac:(clear - Fr; solve_notin)) in Hrn.
            rewrite <- (subst_pskl_in_pskl_intro α P0b (pskl_var_f β)
                          ltac:(clear - Fr; solve_notin)) in Hrn.
            rewrite (subst_pskl_in_pskl_spec PaX (pskl_var_f β) α) in Hrn.
            exact Hrn. }
          intros Δ' HS1 HS2 HS3.
          simpl.
          apply ad_ppre__forall with
            (L := L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
               `union` Δ' `union` singleton α
               `union` ftvar_in_pskl (msubst_pskl κ PaX))
            (Ψ0 := Ψi' `union` (remove ε Ψa));
            [ | clear - HΨis Hεa; fsetdec ].
          intros α' HX'.
          rewrite <- msubst_pskl_open_lc_local;
            [ | exact Hlcκ | clear - HX'; solve_notin ].
          assert (Hrun : ((α ~ abind_tvar) ++ Θ) ⨟
                    (add α (Δ `union` (remove α Δ'))) ⊢
                    (msubst_pskl κ PaX) ⊑ᵖ[ Ψi' `union` (remove ε Ψa) ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α))).
          { eapply ad_partial_precise_delta_cong;
              [ apply (HqX (remove α Δ'));
                [ clear - HS1; destruct_notin; fsetdec
                | simpl; clear - HS2; fsetdec
                | intros Yd αd τ HYd Hbd;
                  destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                    as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                  eapply HS3; [ clear - HYd; fsetdec | exact Hbd' ] ]
              | clear; fsetdec ]. }
          apply (FOLD α PaX (Ψi' `union` (remove ε Ψa)) Δ'
                   ltac:(clear - Fr; solve_notin) HS1 HS2 HS3 Hrun
                   α' ltac:(clear - HX'; solve_notin)).
        + (* Pi = □ — ROW B: SE-GhostL; ONE fresh-α body-IH run at the row
             top (not per-instance — the giant IH must not be re-elaborated
             under the ∀-fold binder), then FOLD-rename.  The solve is a
             single a_solve_eq__hole_l (Pa := ∀.P0b). *)
          assert (HΨie : Ψi [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          assert (Hhd : Δ ∩
                    (ftvar_in_uskl (uskl_all_etag ε ψR)) [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          simpl in Hhd.
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b).
          assert (Hp0X : ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢
                    (msubst_pskl κ pskl_hole) ⊑ᵖ[ empty ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α))).
          { simpl. apply ad_ppre__hole; [ clear; fsetdec | ].
            pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                          (uskl_var_f α)) as Hup.
            simpl in Hup. clear - Hhd Hup Fr; destruct_notin; fsetdec. }
          exists (pskl_all_syn P0b); split;
            [ apply a_solve_eq__hole_l | ].
          intros Δ' HS1 HS2 HS3.
          simpl.
          apply ad_ppre__forall with
            (L := L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b `union` Δ')
            (Ψ0 := empty `union` (remove ε Ψa));
            [ | clear - HΨie Hεa; fsetdec ].
          intros α' HX'.
          rewrite <- msubst_pskl_open_lc_local;
            [ | exact Hlcκ | clear - HX'; solve_notin ].
          assert (Hp0X' : ((α' ~ abind_tvar) ++ Θ) ⨟ Δ ⊢
                    (msubst_pskl κ pskl_hole) ⊑ᵖ[ empty ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α'))).
          { simpl. apply ad_ppre__hole; [ clear; fsetdec | ].
            pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                          (uskl_var_f α')) as Hup.
            simpl in Hup. clear - Hhd Hup HX'; destruct_notin; fsetdec. }
          clear FOLD.
          destruct (IHX α' pskl_hole empty Δ
                      ltac:(clear - HX'; solve_notin)
                      Hdelta
                      ltac:(clear; fsetdec)
                      ltac:(apply a_wf_pskl__hole)
                      ltac:(intros α0 HX0; simpl; auto)
                      Hp0X'
                      ltac:(clear; fsetdec))
            as (Pa0 & Hs0 & Hq0).
          pose proof (a_solve_eq_hole_subject_inv Hs0) as HPa0; subst Pa0.
          assert (HqS : ((α' ~ abind_tvar) ++ Θ) ⨟
                    (Δ `union` (add α' Δ')) ⊢
                    (msubst_pskl κ (open_pskl_wrt_pskl P0b (pskl_var_f α')))
                    ⊑ᵖ[ empty `union` (remove ε Ψa) ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α'))).
          { apply (Hq0 (add α' Δ')).
            - clear - HS1 HX'; destruct_notin; fsetdec.
            - clear - HS2 HX' Hdomsub; destruct_notin; fsetdec.
            - intros Yd αd τ HYd Hbd.
              destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
                [ discriminate Hc | ].
              destruct (Yd == α') as [-> | Hne].
              + assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                  by (eapply a_wf_aenv_def_ftv_dom;
                      [ exact HwfΘ | exact Hbd' ]).
                clear - Hd HX'; destruct_notin; fsetdec.
              + eapply HS3; [ clear - HYd Hne; fsetdec | exact Hbd' ]. }
          eapply ad_partial_precise_delta_cong;
            [ eapply ad_partial_precise_strengthen_tvar;
                [ exact HqS | clear; fsetdec ]
            | clear; fsetdec ].
        + (* Pi = ∀◇.Pi' — the remove-branch dies (guarded body);
             the fill branch is ROW C (SE-GhostForall) *)
          assert (Hg : guarded_pskl Pi' /\ (Θ0 ⨟ empty ⊢ₚₛᵃ Pi'))
            by (inversion HwfPi; subst; split; assumption).
          destruct Hg as [HgPi' HwfPi'].
          assert (Hdisj :
            (Θ ⨟ Δ ⊢ (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ]
               (uskl_all_etag ε ψR)) \/
            (exists Lf, forall α, α `notin` Lf ->
               ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢
                 pskl_tophole (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ]
                 (open_uskl_wrt_uskl ψR (uskl_var_f α)))).
          { simpl in Hpre0. inversion Hpre0; subst;
              [ left; assumption | right; eexists; eassumption ]. }
          destruct Hdisj as [Hrem | (Lf & HF)].
          * (* remove: the guarded body dies against the ε-tagged target *)
            exfalso.
            inversion HgPi'; subst.
            -- simpl in Hrem. inversion Hrem.
            -- assert (HΨ'e : Ψ' [=] empty).
               { eapply ad_ppre_mono_subject_target_tags_empty
                   with (τ := msubst_lookup κ α);
                   [ exact HwfΘ | exact Hrem | reflexivity
                   | eapply a_inc_lookup_mono; eauto
                   | exact (a_tags_sort_d_tags Htags0) ]. }
               assert (Hcon : ε `in` empty).
          { apply (proj1 (HΨ'e ε)). apply (proj2 (HΨ'eq ε)).
            clear; fsetdec. }
          clear - Hcon; fsetdec.
            -- simpl in Hrem. inversion Hrem.
          * (* fill — ROW C *)
            assert (HΨiS : Ψi [<=] Ψ0').
            { pick fresh αp for (Lf `union` Lt `union` dom Θ).
              assert (HwfΘx : a_wf_aenv ((αp ~ abind_tvar) ++ Θ))
                by (apply a_wf_aenv__tvar;
                    [ clear - Fr; solve_notin | exact HwfΘ ]).
              eapply ad_partial_precise_tags_sub;
                [ exact HwfΘx
                | apply HF; clear - Fr; solve_notin
                | exact (a_tags_sort_d_tags
                          (Htagsf αp ltac:(clear - Fr; solve_notin))) ]. }
            pick fresh α for
              (L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
                 `union` Lf `union` ftvar_in_pskl Pi').
            destruct (IHX α (pskl_tophole Pi') Ψi Δ
                        ltac:(clear - Fr; solve_notin)
                        Hdelta
                        ltac:(clear; fsetdec)
                        ltac:(eapply a_wf_pskl_weaken;
                              [ intros x b Hb; apply binds_cons_3;
                                exact Hb
                              | exact HwfPi ])
                        Hshield
                        (HF α ltac:(clear - Fr; solve_notin))
                        HΨiS)
              as (PaX & HsX & HqX).
            assert (HsX0 : Θ0 ⊢ₑ (pskl_tophole Pi')
                      ∼ (open_pskl_wrt_pskl P0b (pskl_var_f α)) ⤳ PaX)
              by (eapply a_solve_eq_strengthen_tvar; exact HsX).
            exists (pskl_all_syn (close_pskl_wrt_pskl α PaX)); split.
            { apply a_solve_eq__tophole_l_all with
                (L := L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
                   `union` Lf `union` singleton α
                   `union` ftvar_in_pskl Pi' `union` ftvar_in_pskl PaX).
              intros β Hβ.
              pose proof ((proj2 a_solve_sub_eq_rename) _ _ _ _ HsX0 α β
                            ltac:(clear - Fr; solve_notin)
                            ltac:(clear - Hβ; fsetdec)) as Hrn.
              rewrite (subst_pskl_in_pskl_fresh_eq (pskl_tophole Pi')
                         (pskl_var_f β) α
                         ltac:(simpl; clear - Fr; solve_notin)) in Hrn.
              rewrite <- (subst_pskl_in_pskl_intro α P0b (pskl_var_f β)
                            ltac:(clear - Fr; solve_notin)) in Hrn.
              rewrite (subst_pskl_in_pskl_spec PaX (pskl_var_f β) α)
                in Hrn.
              exact Hrn. }
            intros Δ' HS1 HS2 HS3.
            simpl.
            apply ad_ppre__forall with
              (L := L `union` Lr `union` Lt `union` Lw0 `union` Lq `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
                 `union` Lf `union` Δ' `union` singleton α
                 `union` ftvar_in_pskl (msubst_pskl κ PaX))
              (Ψ0 := Ψi `union` (remove ε Ψa));
              [ | clear - Hεa; fsetdec ].
            intros α' HX'.
            rewrite <- msubst_pskl_open_lc_local;
              [ | exact Hlcκ | clear - HX'; solve_notin ].
            assert (Hrun : ((α ~ abind_tvar) ++ Θ) ⨟
                      (add α (Δ `union` (remove α Δ'))) ⊢
                      (msubst_pskl κ PaX)
                      ⊑ᵖ[ Ψi `union` (remove ε Ψa) ]
                      (open_uskl_wrt_uskl ψR (uskl_var_f α))).
            { eapply ad_partial_precise_delta_cong;
                [ apply (HqX (add α Δ'));
                  [ clear - HS1 Fr; destruct_notin; fsetdec
                  | clear - HS2 Fr Hdomsub; destruct_notin; fsetdec
                  | intros Yd αd τ HYd Hbd;
                    destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                      as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                    destruct (Yd == α) as [-> | Hne];
                    [ assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                        by (eapply a_wf_aenv_def_ftv_dom;
                            [ exact HwfΘ | exact Hbd' ]);
                      clear - Hd Fr; destruct_notin; fsetdec
                    | eapply HS3;
                      [ clear - HYd Hne; fsetdec | exact Hbd' ] ] ]
                | clear; fsetdec ]. }
            apply (FOLD α PaX (Ψi `union` (remove ε Ψa)) Δ'
                     ltac:(clear - Fr; solve_notin) HS1 HS2 HS3 Hrun
                     α' ltac:(clear - HX'; solve_notin)).
      - (* P0 = □: the fill would be an all_inh — not a syn paint *)
        exfalso.
        simpl in Hrefine.
        inversion Hrefine; subst.
        match goal with
        | Heq : pskl_to_bskl_syn ?P = bskl_all_inh _ |- _ =>
          destruct P; simpl in Heq; discriminate Heq
        | Heq : bskl_all_inh _ = pskl_to_bskl_syn ?P |- _ =>
          destruct P; simpl in Heq; discriminate Heq
        end.
      - (* P0 = ∀◇.P0': the guarded body dies against all_inh *)
        exfalso.
        assert (Hg : guarded_pskl P0' /\ (Θ0 ⨟ empty ⊢ₚₛᵃ P0')).
        { inversion HwfP0; subst; split; assumption. }
        destruct Hg as [HgP0' HwfP0'].
        simpl in Hrefine.
        inversion Hrefine; subst.
        inversion HgP0'; subst.
        + match goal with
          | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _
            |- _ => simpl in Hin; inversion Hin
          end.
        + (* var: rigid / flexible both die *)
          match goal with
          | Hwv : _ ⨟ _ ⊢ₚₛᵃ pskl_var_f ?v,
            Hin : _ ⨟ _ ⊢ᵣᵃ
              pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _ |- _ =>
            assert (Hor : v `in` empty \/ a_binds_tvar v Θ0)
              by (inversion Hwv; subst; assumption);
            destruct Hor as [Hemp | Habt]; [ clear - Hemp; fsetdec | ];
            destruct Habt as [Hrig | Hflx];
            [ let Hmid := fresh in
              assert (Hmid : msubst_pskl κ (pskl_var_f v) = pskl_var_f v)
                by (eapply msubst_pskl_tvar_id;
                    [ exact HwfΘ0 | exact Hκ | exact Hrig ]);
              rewrite Hmid in Hin; simpl in Hin;
              eapply (ad_refine_syn_rigid_var_nonvar_absurd_sub Hin);
                [ intros x b Hb; eapply aenv_split_sub_r;
                    [ exact HspΘ | exact Hb ]
                | apply a_wf_aenv_uniq; exact HwfΘ
                | eapply a_inc_binds_tvar; eauto
                | intros β0 Hcc; discriminate Hcc ]
            | let Hml := fresh in
              assert (Hml : mono_ptyp (msubst_lookup κ v))
                by (eapply a_inc_lookup_mono; eauto);
              simpl in Hin;
              rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
              eapply ad_refine_mono_paint_allinh_rhs_absurd;
                [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                | exact Hml ] ]
          end.
        + match goal with
          | Hin : _ ⨟ _ ⊢ᵣᵃ
              pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _
            |- _ => simpl in Hin; inversion Hin
          end. }
    destruct (uskl_rho_all_etag_l_inv Hrho)
      as [[Heqψa HΨρe] | [Hleaf | (Lr & ψR & Heqψa & Hrhof)]].
    + (* refl: recast as a congruence with refl bodies *)
      subst ψa.
      assert (Htskf : exists Li, forall α, α `notin` Li ->
                is_tskl (open_uskl_wrt_uskl R (uskl_var_f α))).
      { destruct (a_tags_sort_all_etag_inv Htags)
          as (Lt0 & Ψt0 & Hf & _ & _).
        exists Lt0; intros α0 Hα0.
        destruct (Hf α0 Hα0); assumption. }
      destruct Htskf as (Li & Htskf).
      apply (KEYF R Li);
        [ intros α0 Hα0; apply urho__refl;
            [ apply is_tskl_lc; apply Htskf; exact Hα0 | exact HΨρe ]
        | exact Htags | exact Hapart | exact Hpre ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf)
        as (Pa & Hs & Hq).
      exists Pa; split; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
    + subst ψa.
      apply (KEYF ψR Lr);
        [ exact Hrhof | exact Htags | exact Hapart | exact Hpre ].
  - (* forall_inh_untagged: tag-sort absurd *)
    destruct (uskl_rho_all_syn_l_inv Hrho)
      as [[-> _] | [Hleaf | (L' & R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  - (* forall_syn_tagged: subject ∀^ε.R ∼ bskl_all_syn Q.  ε is a Ψ'-only
       tag (the rule keeps Ψ, does NOT add ε), so NO ε-split.  P0 grid:
       □ (VacuousR) and ∀◇.P0' (the main tophole_fill column) are real;
       the rest are refinement-absurd.  Split-A (DESIGN §6(t)):
       Θtv_ih:=(α~tvar)++Θtv, Θr_ih:=Θr — valid split (α at front), tight
       family dom Θr; matches the CLOSED forall_inh_tagged IHX exactly. *)
    assert (HwfΘr2 := HwfΘr).
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hκ).
    assert (Himav : forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ)
      by (intros p Hp; eapply a_inc_image_ftv_dom; [ exact Hκ | exact Hp ]).
    assert (KEYF : forall ψR Lr,
      (forall α, α `notin` Lr ->
         uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl R (uskl_var_f α))
                             (open_uskl_wrt_uskl ψR (uskl_var_f α))) ->
      a_tags_sort NM Ψ' (uskl_all_etag ε ψR) ->
      flex_apart Θ0 Δρ P0 (uskl_all_etag ε ψR) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_all_etag ε ψR) ->
      exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
        forall Δ',
          Δ' ∩ Δ [=] empty ->
          Δ' ∩ dom Θr [=] empty ->
          delta_def_fresh Δ' Θ ->
          Θ ⨟ (Δ `union` Δ') ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ]
            (uskl_all_etag ε ψR)).
    { intros ψR Lr Hrhof Htags0 Hap0 Hpre0.
      destruct (a_tags_sort_all_etag_inv Htags0)
        as (Lt & Ψ0' & Htagsf & Hεnin & HΨ'eq).
      assert (Hdomsub : dom Θr [<=] dom Θ)
        by (eapply aenv_split_dom_r; exact HspΘ).
      (* body ftag flow at one fresh var: Ψ ⊆ Ψρ ∪ Ψ0' *)
      assert (HbF : Ψ [<=] Ψρ `union` Ψ0').
      { pick fresh αf for (L `union` Lr `union` Lt).
        pose proof (ad_pat_consis_ftag_sub
                      (H αf ltac:(clear - Fr; solve_notin))) as Ha.
        pose proof (uskl_rho_ftag_sub
                      (Hrhof αf ltac:(clear - Fr; solve_notin))) as Hb.
        pose proof (d_tags_skl_ftag
                      (a_tags_sort_d_tags
                         (Htagsf αf ltac:(clear - Fr; solve_notin)))) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      (* Ψa ⊆ Ψ0' (Ψa ⊆ Ψ ⊆ Ψρ∪Ψ0', and Ψa ⊆ Ψ' disjoint Ψρ) *)
      assert (HΨaΨ0' : Ψa [<=] Ψ0')
        by (clear - Hsubeq2 HbF Hinter HΨ'eq Hsub; fsetdec).
      assert (Hintb : Ψρ ∩ Ψ0' [=] empty)
        by (clear - Hinter HΨ'eq; fsetdec).
      (* target ftv bound: reconstruct the whole ρ and bound ftv ψR *)
      assert (Hrhow : uskl_rho NM Θ Δρ Ψρ (uskl_all_etag ε R)
                        (uskl_all_etag ε ψR))
        by (eapply urho__all_etag with (L := Lr); exact Hrhof).
      assert (HψaB : ftvar_in_bskl Q [<=] dom Θr ->
                ftvar_in_uskl (uskl_all_etag ε ψR) [<=] dom Θr `union` Δρ).
      { intros HQB.
        assert (HftR : ftvar_in_uskl (uskl_all_etag ε R) [<=]
                  ftvar_in_bskl (bskl_all_syn Q) `union` dom Θr)
          by (eapply consis_subject_ftv_bag_bound;
                [ eapply ad_pat_consis__forall_syn_tagged; exact H
                | exact HspΘ | exact Htvs | exact HwfΘr ]).
        pose proof (uskl_rho_ftv_target_bound Hrhow) as HftA.
        simpl in *. clear - HQB HftR HftA; fsetdec. }
      (* P0-grid *)
      destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
      - (* unit *) simpl in Hrefine. inversion Hrefine.
      - (* var_b *) inversion HwfP0.
      - (* var β: rigid absurd / flex → mono paint vs all_syn absurd *)
        exfalso.
        assert (Hor : β `in` empty \/ a_binds_tvar β Θ0)
          by (inversion HwfP0; subst; assumption).
        destruct Hor as [Hemp | Habt]; [ clear - Hemp; fsetdec | ].
        destruct Habt as [Hrig | Hflx].
        + assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
            by (eapply msubst_pskl_tvar_id;
                [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
          rewrite Hmid in Hrefine. simpl in Hrefine.
          eapply (ad_refine_syn_rigid_var_nonvar_absurd_sub Hrefine)
            with (Θfull := Θ);
            [ intros x b Hb; eapply aenv_split_sub_r;
                [ exact HspΘ | exact Hb ]
            | apply a_wf_aenv_uniq; exact HwfΘ
            | eapply a_inc_binds_tvar; eauto
            | intros β0 Hcc; discriminate Hcc ].
        + assert (Hml : mono_ptyp (msubst_lookup κ β))
            by (eapply a_inc_lookup_mono; eauto).
          simpl in Hrefine.
          rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
          eapply ad_refine_mono_paint_allsyn_rhs_absurd;
            [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
            | exact Hml ].
      - (* arrow *) simpl in Hrefine. inversion Hrefine.
      - (* all_syn P0b: inh-paint = bskl_all_inh, refines to all_syn absurd *)
        exfalso. simpl in Hrefine. inversion Hrefine.
      - (* P0 = □: VacuousR.  Q = all_syn synthesised ⇒ Ψ = ∅ ⇒ Ψa = ∅ *)
        simpl in Hrefine.
        pose proof (ad_refine_syn_hole_sskl Hrefine eq_refl) as Hss.
        assert (HΨe : Ψ [=] empty).
        { eapply ad_pat_consis_sskl_tags;
            [ eapply ad_pat_consis__forall_syn_tagged; exact H
            | exact HwfΘ | exact Hss ]. }
        assert (HΨae : Ψa [=] empty) by (clear - Hsubeq2 HΨe; fsetdec).
        assert (HQB : ftvar_in_bskl Q [<=] dom Θr).
        { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine).
          simpl in Ht. clear - Ht; fsetdec. }
        exists Pi; split; [ apply a_solve_eq__hole_r | ].
        intros Δ' HS1 HS2 HS3.
        eapply ad_partial_precise_psi_cong;
          [ eapply ad_partial_precise_delta_weaken_fresh;
              [ exact Hpre0
              | pose proof (HψaB HQB) as Hbb;
                clear - Hbb HS1 HS2 Hdelta; fsetdec
              | exact HS3 ]
          | clear - HΨae; fsetdec ].
      - (* P0 = ∀◇.P0': the MAIN tophole_fill column.  IHX runs the body
           IH with the binder joining Θr (bag split: Θr_ih:=(α~tvar)++Θr);
           Hrefb = the inverted tophole_fill body at (α~tvar)++Θr ⨟ Δr,
           which is the IH's refinement premise VERBATIM. *)
        assert (HgP0' : guarded_pskl P0') by (inversion HwfP0; assumption).
        assert (HwfP0'0 : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
          by (inversion HwfP0; assumption).
        (* invert the tophole_fill refinement: the fill body sits at
           (α~tvar)++Θr ⨟ Δr — exactly the IH's refinement premise *)
        simpl in Hrefine.
        assert (Hrefb : exists Lq, forall α, α `notin` Lq ->
          ((α ~ abind_tvar) ++ Θr) ⨟ Δr ⊢ᵣᵃ
            (bskl_tophole (pskl_to_bskl_inh (msubst_pskl κ P0')))
            ⊳ open_bskl_wrt_bskl Q (bskl_var_f α)).
        { inversion Hrefine; subst.
          - (* tophole_remove: the guarded body can't refine to all_syn *)
            exfalso. inversion HgP0'; subst.
            + match goal with
              | Hin : _ ⨟ _ ⊢ᵣᵃ
                  pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ |- _ =>
                simpl in Hin; inversion Hin
              end.
            + match goal with
              | Hin : _ ⨟ _ ⊢ᵣᵃ
                  pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _ |- _ =>
                let Hml := fresh in
                assert (Hml : mono_ptyp (msubst_lookup κ v))
                  by (eapply a_inc_lookup_mono; eauto);
                simpl in Hin;
                rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
                eapply ad_refine_mono_paint_allsyn_rhs_absurd;
                  [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                  | exact Hml ]
              end.
            + match goal with
              | Hin : _ ⨟ _ ⊢ᵣᵃ
                  pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _ |- _ =>
                simpl in Hin; inversion Hin
              end.
          - (* tophole_fill: the cofinite premise IS the fill body *)
            rename H5 into Hfill; rename L0 into Lfill.
            exists Lfill; exact Hfill. }
        destruct Hrefb as (Lrb & Hrefb).
        assert (HapFp : exists La, forall α, α `notin` La ->
                  flex_apart Θ0 Δρ (pskl_tophole P0')
                             (open_uskl_wrt_uskl ψR (uskl_var_f α)))
          by (exists Δρ; intros α0 Hα0;
              eapply flex_apart_tophole_all_etag_descent;
                [ exact HgP0' | exact Hap0 | exact Hα0 ]).
        destruct HapFp as (La & HapF).
        (* the body-IH wrapper (bag split: Θtv_ih:=Θtv, Θr_ih:=(α0~tvar)++Θr,
           Δr_ih:=Δr) — the family premise grows to dom((α0~tvar)++Θr), so
           rows whose α0 predates Δ' instantiate at Δ'∖{α0} and weaken the
           missing Δ'∩{α0} back; refinement per row = Hrefb verbatim.  Δx is
           the IH's Δ (Δ for ∀◇/□, add α0 Δ for the ∀ row). *)
        assert (IHX : forall α0 Pi0 Ψi0 P0i Δx,
          α0 `notin` (L `union` Lr `union` Lt `union` Lrb `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0') ->
          Δρ [<=] Δx -> Δx [<=] add α0 Δ ->
          ((α0 ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi0 ->
          ((α0 ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0i ->
          (forall α00, α00 `in` Δρ ->
             α00 `notin` pskl_shielded_ftv (msubst_pskl κ Pi0)) ->
          flex_apart ((α0 ~ abind_tvar) ++ Θ0) Δρ P0i
             (open_uskl_wrt_uskl ψR (uskl_var_f α0)) ->
          ((α0 ~ abind_tvar) ++ Θ) ⨟ Δx ⊢ (msubst_pskl κ Pi0)
              ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψR (uskl_var_f α0)) ->
          Ψi0 [<=] Ψ0' ->
          ((α0 ~ abind_tvar) ++ Θr) ⨟ Δr ⊢ᵣᵃ
             (pskl_to_bskl_inh (msubst_pskl κ P0i))
             ⊳ open_bskl_wrt_bskl Q (bskl_var_f α0) ->
          exists Pa0, ((α0 ~ abind_tvar) ++ Θ0) ⊢ₑ Pi0 ∼ P0i ⤳ Pa0 /\
            forall Δ', Δ' ∩ Δx [=] empty ->
              Δ' ∩ (dom ((α0 ~ abind_tvar) ++ Θr)) [=] empty ->
              delta_def_fresh Δ' ((α0 ~ abind_tvar) ++ Θ) ->
              ((α0 ~ abind_tvar) ++ Θ) ⨟ (Δx `union` Δ')
                ⊢ (msubst_pskl κ Pa0)
                  ⊑ᵖ[ Ψi0 `union` Ψa ]
                  (open_uskl_wrt_uskl ψR (uskl_var_f α0))).
        { intros α0 Pi0 Ψi0 P0i Δx HXf HΔρx HΔxs HwfPi0 HwfP0i Hshld0
                 HapX Hpre0x HΨi0s Hrefi.
          apply (H0 α0 ltac:(clear - HXf; solve_notin)
                   NM ((α0 ~ abind_tvar) ++ Θ0)
                   Θtv ((α0 ~ abind_tvar) ++ Θr)
                   ((α0 ~ abind_tvar) ++ Θ0r) κ
                   Δx Δρ Δr Ψρ Ψ0' Ψi0 Ψa
                   (open_uskl_wrt_uskl ψR (uskl_var_f α0))
                   Pi0 P0i).
          - apply aenv_split_cons_r;
              [ exact HspΘ | clear - HXf; solve_notin ].
          - apply aenv_split_cons_r;
              [ exact HspΘ0 | clear - HXf; solve_notin ].
          - apply a_wf_aenv__tvar;
              [ clear - HXf Hdomsub; destruct_notin; fsetdec
              | exact HwfΘr ].
          - exact Htvs.
          - exact HΔrd.
          - exact HΔρtv.
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ ].
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ0 ].
          - exact HwfPi0.
          - exact HwfP0i.
          - apply a_inc__tvar with (Ξ := (@nil (atom * abind)));
              [ exact Hκ | apply a_suffix__nil ].
          - eapply uskl_rho_weaken;
              [ apply Hrhof; clear - HXf; solve_notin
              | intros x b Hb; apply binds_cons_3; exact Hb ].
          - apply Htagsf. clear - HXf; solve_notin.
          - clear - HΨi0s HΨaΨ0'; fsetdec.
          - exact Hintb.
          - intros x Hx.
            destruct (Hfresh x Hx) as (Hb & Hav & Hdef).
            repeat split.
            + apply binds_cons_3; exact Hb.
            + exact Hav.
            + intros αd τ Hbd.
              destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
                [ discriminate Hc | exact (Hdef _ _ Hbd') ].
          - exact HΔρx.
          - exact Hshld0.
          - intros Yd αd τ HYd Hbd.
            destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
              [ discriminate Hc | ].
            assert (HYx : Yd `in` add α0 Δ) by (clear - HYd HΔxs; fsetdec).
            destruct (Yd == α0) as [-> | Hne].
            + assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                by (eapply a_wf_aenv_def_ftv_dom;
                    [ exact HwfΘ | exact Hbd' ]).
              clear - Hd HXf; destruct_notin; fsetdec.
            + eapply Hdfresh; [ | exact Hbd' ].
              clear - HYx Hne; fsetdec.
          - eapply flex_apart_weaken;
              [ exact HapX
              | intros x b Hb; exact Hb
              | intros αf Hf; exact Hf ].
          - exact Hpre0x.
          - exact Hsubeq1.
          - exact Hsubeq2.
          - exact Hrefi. }
        (* per-instance fold (strengthen α out of the aenv [α∈Δ] + rename
           α↦α' in Δ), for the ∀-row precision via ad_ppre__forall *)
        assert (FOLD : forall α PaR Ψc Δ',
          α `notin` (L `union` Lr `union` Lt `union` Lrb `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0') ->
          Δ' ∩ Δ [=] empty ->
          Δ' ∩ dom Θr [=] empty ->
          delta_def_fresh Δ' Θ ->
          ((α ~ abind_tvar) ++ Θ)
            ⨟ (add α (Δ `union` (remove α Δ')))
            ⊢ (msubst_pskl κ PaR) ⊑ᵖ[ Ψc ]
              (open_uskl_wrt_uskl ψR (uskl_var_f α)) ->
          forall α', α' `notin` (L `union` Lr `union` Lt `union` Lrb
               `union` La `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` dom Θr `union` dom κ `union` singleton ε
               `union` ftvar_in_uskl ψR `union` ftvar_in_pskl P0'
               `union` Δ' `union` singleton α
               `union` ftvar_in_pskl (msubst_pskl κ PaR)) ->
          Θ ⨟ (add α' (Δ `union` Δ')) ⊢
            (msubst_pskl κ (open_pskl_wrt_pskl
               (close_pskl_wrt_pskl α PaR) (pskl_var_f α')))
            ⊑ᵖ[ Ψc ] (open_uskl_wrt_uskl ψR (uskl_var_f α'))).
        { intros α PaR Ψc Δ' HXf HS1 HS2 HS3 Hrun α' HX'f.
          assert (Hst : Θ ⨟ (add α (Δ `union` (remove α Δ')))
                   ⊢ (msubst_pskl κ PaR) ⊑ᵖ[ Ψc ]
                   (open_uskl_wrt_uskl ψR (uskl_var_f α)))
            by (eapply ad_partial_precise_strengthen_tvar;
                [ exact Hrun | clear; fsetdec ]).
          assert (Hrn : Θ ⨟ (add α' (remove α (add α (Δ `union`
                    (remove α Δ')))))
                   ⊢ (subst_pskl_in_pskl (pskl_var_f α') α
                        (msubst_pskl κ PaR))
                   ⊑ᵖ[ Ψc ]
                   (subst_bskl_in_uskl (uskl_var_f α') α
                        (open_uskl_wrt_uskl ψR (uskl_var_f α)))).
          { eapply ad_partial_precise_rename;
              [ exact Hst
              | clear; fsetdec
              | clear - HXf; solve_notin
              | clear - HX'f; solve_notin
              | clear - HX'f; solve_notin
              | clear - HX'f; solve_notin
              | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                              (uskl_var_f α)) as Hup;
                simpl in Hup; clear - HX'f Hup; destruct_notin; fsetdec
              | intros αd τ Hbd;
                assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                  by (eapply a_wf_aenv_def_ftv_dom;
                      [ exact HwfΘ | exact Hbd ]);
                split; [ clear - Hd HXf; destruct_notin; fsetdec
                       | clear - Hd HX'f; destruct_notin; fsetdec ] ]. }
          rewrite <- (subst_bskl_in_uskl_intro α ψR (uskl_var_f α')
                        ltac:(clear - HXf; solve_notin)) in Hrn.
          rewrite (@msubst_pskl_subst_var κ PaR α α'
                     ltac:(clear - HXf; solve_notin)
                     ltac:(clear - HX'f; solve_notin)
                     ltac:(intros p Hp;
                           pose proof (Himav p Hp) as Hd;
                           clear - Hd HXf; destruct_notin; fsetdec)) in Hrn.
          rewrite (subst_pskl_in_pskl_spec PaR (pskl_var_f α') α) in Hrn.
          eapply ad_partial_precise_delta_cong;
            [ eapply ad_partial_precise_delta_weaken_fresh
                with (Δ' := Δ' ∩ singleton α);
                [ exact Hrn
                | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                (uskl_var_f α')) as Hup;
                  simpl in Hup;
                  apply atoms_inter_empty_pointwise;
                  intros y Hy;
                  assert (Heqy : y = α) by (clear - Hy; fsetdec);
                  subst y;
                  clear - HXf HX'f Hup; destruct_notin; fsetdec
                | intros Yd αd τ HYd Hbd;
                  assert (Heqy : Yd = α) by (clear - HYd; fsetdec);
                  subst Yd;
                  assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                    by (eapply a_wf_aenv_def_ftv_dom;
                        [ exact HwfΘ | exact Hbd ]);
                  clear - Hd HXf; destruct_notin; fsetdec ]
            | clear - HXf HX'f; destruct_notin; fsetdec ]. }
        (* the Pi grid *)
        destruct Pi as [ | nb | β | Pi1 Pi2 | Pib | | Pi' ].
        + (* unit: no precision into all_etag *)
          simpl in Hpre0. inversion Hpre0.
        + (* var_b *) inversion HwfPi.
        + (* var β: mono-paint subject vs ε-tagged target — Ψ' = ∅ absurd *)
          exfalso.
          assert (HΨ'e : Ψ' [=] empty).
          { eapply ad_ppre_mono_subject_target_tags_empty
              with (τ := msubst_lookup κ β);
              [ exact HwfΘ | exact Hpre0 | reflexivity
              | eapply a_inc_lookup_mono; eauto
              | exact (a_tags_sort_d_tags Htags0) ]. }
          clear - HΨ'e HΨ'eq Hεnin; fsetdec.
        + (* arrow *) simpl in Hpre0. inversion Hpre0.
        + (* Pi = ∀.Pib — ForallGhost row: solve = a_solve_eq__all_l_tophole
             (P0i:=∀◇.P0' KEPT, α-free); IHX at Δx:=add α Δ (α∈Δ ⇒ FOLD);
             precision conclusion = ad_ppre__forall (Pa = ∀.close). *)
          assert (HwfPif : exists Lwi, forall α, α `notin` Lwi ->
                    ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                    (open_pskl_wrt_pskl Pib (pskl_var_f α))).
          { assert (Hi : exists Lwi, forall α0, α0 `notin` Lwi ->
                      Θ0 ⨟ (add α0 empty) ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl Pib (pskl_var_f α0)))
              by (inversion HwfPi; subst; eexists; eassumption).
            destruct Hi as (Lwi & Hi).
            exists Lwi; intros α0 Hα0.
            eapply a_wf_pskl_delta_to_tvar;
              [ apply Hi; exact Hα0 | clear; fsetdec ]. }
          destruct HwfPif as (Lwi & HwfPif).
          assert (HpreF : exists Lp Ψi',
            (forall α, α `notin` Lp ->
               Θ ⨟ (add α Δ) ⊢
                 (msubst_pskl κ (open_pskl_wrt_pskl Pib (pskl_var_f α)))
                 ⊑ᵖ[ Ψi' ] (open_uskl_wrt_uskl ψR (uskl_var_f α))) /\
            Ψi [=] add ε Ψi').
          { simpl in Hpre0.
            inversion Hpre0; subst.
            match goal with
            | Hf : forall α0, α0 `notin` ?L0 ->
                _ ⨟ _ ⊢ _ ⊑ᵖ[ ?PS ] _ |- _ =>
              exists (L0 `union` dom κ), PS; split;
                [ intros α0 Hα0;
                  rewrite msubst_pskl_open_lc_local;
                    [ apply Hf; clear - Hα0; fsetdec
                    | exact Hlcκ | clear - Hα0; fsetdec ]
                | assumption ]
            end. }
          destruct HpreF as (Lp & Ψi' & HpreF & HΨis).
          assert (HΨi's : Ψi' [<=] Ψ0').
          { pick fresh αp for (Lp `union` Lt).
            eapply ad_partial_precise_tags_sub;
              [ exact HwfΘ
              | apply HpreF; clear - Fr; solve_notin
              | exact (a_tags_sort_d_tags
                        (Htagsf αp ltac:(clear - Fr; solve_notin))) ]. }
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lrb `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0'
               `union` Lwi `union` Lp `union` ftvar_in_pskl Pib).
          destruct (IHX α (open_pskl_wrt_pskl Pib (pskl_var_f α)) Ψi'
                      (pskl_tophole P0') (add α Δ)
                      ltac:(clear - Fr; solve_notin)
                      ltac:(clear - Hdelta; fsetdec)
                      ltac:(clear; fsetdec)
                      (HwfPif α ltac:(clear - Fr; solve_notin))
                      ltac:(eapply a_wf_pskl_weaken;
                            [ intros x b Hb; apply binds_cons_3; exact Hb
                            | exact HwfP0 ])
                      ltac:(intros α0 HX0;
                            pose proof (Hshield α0 HX0) as Hs0;
                            simpl in Hs0;
                            rewrite msubst_pskl_open_lc_local;
                              [ | exact Hlcκ | clear - Fr; solve_notin ];
                            pose proof (pskl_shielded_ftv_open_upper
                              (msubst_pskl κ Pib) (pskl_var_f α)) as Hup;
                            simpl in Hup;
                            assert (HneX0 : α0 <> α)
                              by (clear - HX0 Fr; destruct_notin; fsetdec);
                            clear - Hs0 Hup HneX0; fsetdec)
                      ltac:(eapply flex_apart_weaken;
                            [ apply HapF; clear - Fr; solve_notin
                            | intros x b Hb; apply binds_cons_3; exact Hb
                            | apply a_flex_tvar_strip_tvar ])
                      ltac:(eapply ad_partial_precise_weaken;
                              [ apply HpreF; clear - Fr; solve_notin
                              | intros x b Hb; apply binds_cons_3;
                                exact Hb ])
                      HΨi's
                      ltac:(apply Hrefb; clear - Fr; solve_notin))
            as (PaX & HsX & HqX).
          assert (HsX0 : Θ0 ⊢ₑ (open_pskl_wrt_pskl Pib (pskl_var_f α))
                    ∼ (pskl_tophole P0') ⤳ PaX)
            by (eapply a_solve_eq_strengthen_tvar; exact HsX).
          exists (pskl_all_syn (close_pskl_wrt_pskl α PaX)); split.
          { apply a_solve_eq__all_l_tophole with
              (L := L `union` Lr `union` Lt `union` Lrb `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0'
                 `union` Lwi `union` Lp `union` singleton α
                 `union` ftvar_in_pskl Pib `union` ftvar_in_pskl PaX).
            intros β Hβ.
            pose proof ((proj2 a_solve_sub_eq_rename) _ _ _ _ HsX0 α β
                          ltac:(clear - Fr; solve_notin)
                          ltac:(clear - Hβ; fsetdec)) as Hrn.
            rewrite <- (subst_pskl_in_pskl_intro α Pib (pskl_var_f β)
                          ltac:(clear - Fr; solve_notin)) in Hrn.
            rewrite (subst_pskl_in_pskl_fresh_eq (pskl_tophole P0')
                       (pskl_var_f β) α
                       ltac:(simpl; clear - Fr; solve_notin)) in Hrn.
            rewrite (subst_pskl_in_pskl_spec PaX (pskl_var_f β) α) in Hrn.
            exact Hrn. }
          intros Δ' HS1 HS2 HS3.
          simpl.
          apply ad_ppre__forall with (ε := ε)
            (L := L `union` Lr `union` Lt `union` Lrb `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0'
               `union` Δ' `union` singleton α
               `union` ftvar_in_pskl (msubst_pskl κ PaX))
            (Ψ0 := Ψi' `union` Ψa);
            [ | clear - HΨis; fsetdec ].
          intros α' HX'.
          rewrite <- msubst_pskl_open_lc_local;
            [ | exact Hlcκ | clear - HX'; solve_notin ].
          assert (Hrun : ((α ~ abind_tvar) ++ Θ) ⨟
                    (add α (Δ `union` (remove α Δ'))) ⊢
                    (msubst_pskl κ PaX) ⊑ᵖ[ Ψi' `union` Ψa ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α))).
          { eapply ad_partial_precise_delta_cong;
              [ apply (HqX (remove α Δ'));
                [ clear - HS1; destruct_notin; fsetdec
                | simpl; clear - HS2; fsetdec
                | intros Yd αd τ HYd Hbd;
                  destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                    as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                  eapply HS3; [ clear - HYd; fsetdec | exact Hbd' ] ]
              | clear; fsetdec ]. }
          apply (FOLD α PaX (Ψi' `union` Ψa) Δ'
                   ltac:(clear - Fr; solve_notin) HS1 HS2 HS3 Hrun
                   α' ltac:(clear - HX'; solve_notin)).
        + (* Pi = □ — GhostL row.  solve = a_solve_eq__hole_l (Pa:=∀◇.P0');
             precision = ad_ppre__tophole_fill, family via rename_tvar.
             Pi0:=□ (Hpre0x = ad_ppre__hole); refinement + closure as ∀◇. *)
          assert (HΨie : Ψi [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          assert (Hhd : Δ ∩
                    (ftvar_in_uskl (uskl_all_etag ε ψR)) [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          simpl in Hhd.
          exists (pskl_tophole P0'); split; [ apply a_solve_eq__hole_l | ].
          intros Δ' HS1 HS2 HS3.
          simpl.
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lrb `union` La
             `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
             `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
             `union` ftvar_in_pskl P0' `union` Δ').
          destruct (IHX α pskl_hole Ψi (pskl_tophole P0') Δ
                      ltac:(clear - Fr; solve_notin)
                      Hdelta
                      ltac:(clear; fsetdec)
                      ltac:(apply a_wf_pskl__hole)
                      ltac:(eapply a_wf_pskl_weaken;
                            [ intros x b Hb; apply binds_cons_3; exact Hb
                            | exact HwfP0 ])
                      ltac:(intros α0 HX0; simpl; auto)
                      ltac:(eapply flex_apart_weaken;
                            [ apply HapF; clear - Fr; solve_notin
                            | intros x b Hb; apply binds_cons_3; exact Hb
                            | apply a_flex_tvar_strip_tvar ])
                      ltac:(simpl; apply ad_ppre__hole;
                            [ exact HΨie
                            | pose proof
                                (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                   (uskl_var_f α)) as Hup;
                              simpl in Hup; clear - Hhd Hup Fr;
                              destruct_notin; fsetdec ])
                      ltac:(clear - HΨie; fsetdec)
                      ltac:(apply Hrefb; clear - Fr; solve_notin))
            as (PaX & HsX & HqX).
          pose proof (a_solve_eq_hole_subject_inv HsX) as HPaXe; subst PaX.
          (* α ∉ ftv(msubst κ (∀◇.P0')) *)
          assert (HXPaX : α `notin` ftvar_in_pskl
                    (msubst_pskl κ (pskl_tophole P0'))).
          { apply msubst_pskl_ftv_avoid.
            - intros p Hp; pose proof (Himav p Hp) as Hb;
                clear - Hb Fr; destruct_notin; fsetdec.
            - simpl;
              assert (HXP0' : α `notin` ftvar_in_pskl P0')
                by (pose proof (a_wf_pskl_ftv_dom HwfP0'0) as Hd;
                    clear - Hd Fr; destruct_notin; fsetdec);
              exact HXP0'. }
          apply ad_ppre__tophole_fill with (ε := ε)
            (L := Δ `union` Δ' `union` dom Θ `union` dom Θ0 `union` dom κ
               `union` singleton ε `union` singleton α `union` Δρ
               `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl (msubst_pskl κ P0')).
          intros α' HX'.
          assert (HS3' : delta_def_fresh Δ' ((α ~ abind_tvar) ++ Θ)).
          { intros Yd αd τ HYd Hbd.
            destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
              [ discriminate Hc | exact (HS3 Yd αd τ HYd Hbd') ]. }
          pose proof (HqX Δ' HS1
                        ltac:(simpl; clear - HS2 Fr; destruct_notin; fsetdec)
                        HS3') as Hq1.
          pose proof (@ad_partial_precise_rename_tvar
                        _ _ _ _ _ Hq1 α α' (@nil (atom * abind)) Θ
                        ltac:(apply a_wf_aenv_uniq; apply a_wf_aenv__tvar;
                              [ clear - Fr; solve_notin | exact HwfΘ ])
                        eq_refl
                        ltac:(simpl; clear - Fr HX'; solve_notin)
                        ltac:(clear - HX'; solve_notin)
                        ltac:(simpl; clear - HX' HXPaX; simpl in HXPaX;
                              solve_notin)
                        ltac:(pose proof
                                (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                   (uskl_var_f α)) as Hup;
                              simpl in Hup; clear - HX' Hup;
                              destruct_notin; fsetdec)
                        ltac:(intros αd τ Hb;
                              destruct (binds_cons_1 _ _ _ _ _ _ Hb)
                                as [[_ Hc] | Hb'];
                                [ discriminate Hc | ];
                              assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                                by (eapply a_wf_aenv_def_ftv_dom;
                                    [ exact HwfΘ | exact Hb' ]);
                              split; [ clear - Hd Fr | clear - Hd HX' ];
                              destruct_notin; fsetdec))
            as Hren.
          simpl in Hren.
          rewrite (subst_pskl_in_pskl_fresh_eq _ (pskl_var_f α') α)
            in Hren;
            [ | simpl in HXPaX; exact HXPaX ].
          rewrite <- (subst_bskl_in_uskl_intro α ψR (uskl_var_f α')
                        ltac:(clear - Fr; solve_notin)) in Hren.
          exact Hren.
        + (* Pi = ∀◇.Pi' — UnivGhost row.  WRAPPED IHX (Pi0:=∀◇.Pi',
             P0i:=∀◇.P0'); refinement = Hrefb verbatim; solve = IHX output
             (tophole_both, strengthen_tvar); precision =
             ad_ppre__tophole_fill (subject ∀◇.P', keeps Ψ, no ε), family
             built by ad_partial_precise_rename_tvar (aenv-tvar rename). *)
          assert (HgPi'w : guarded_pskl Pi' /\ (Θ0 ⨟ empty ⊢ₚₛᵃ Pi'))
            by (inversion HwfPi; subst; split; assumption).
          destruct HgPi'w as [HgPi' HwfPi'].
          assert (Hdisj :
            (Θ ⨟ Δ ⊢ (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ] (uskl_all_etag ε ψR)) \/
            (exists Lf, forall α, α `notin` Lf ->
               ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢
                 pskl_tophole (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ]
                 (open_uskl_wrt_uskl ψR (uskl_var_f α)))).
          { simpl in Hpre0. inversion Hpre0; subst;
              [ left; assumption | right; eexists; eassumption ]. }
          destruct Hdisj as [Hrem | (Lf & HF)].
          * (* remove: the guarded body dies against the ε-tagged target *)
            exfalso. inversion HgPi'; subst.
            -- simpl in Hrem. inversion Hrem.
            -- assert (HΨ'e : Ψ' [=] empty).
               { eapply ad_ppre_mono_subject_target_tags_empty
                   with (τ := msubst_lookup κ α);
                   [ exact HwfΘ | exact Hrem | reflexivity
                   | eapply a_inc_lookup_mono; eauto
                   | exact (a_tags_sort_d_tags Htags0) ]. }
               clear - HΨ'e HΨ'eq Hεnin; fsetdec.
            -- simpl in Hrem. inversion Hrem.
          * (* fill *)
            assert (HΨiS : Ψi [<=] Ψ0').
            { pick fresh αp for (Lf `union` Lt `union` dom Θ).
              assert (HwfΘx : a_wf_aenv ((αp ~ abind_tvar) ++ Θ))
                by (apply a_wf_aenv__tvar;
                    [ clear - Fr; solve_notin | exact HwfΘ ]).
              eapply ad_partial_precise_tags_sub;
                [ exact HwfΘx
                | apply HF; clear - Fr; solve_notin
                | exact (a_tags_sort_d_tags
                          (Htagsf αp ltac:(clear - Fr; solve_notin))) ]. }
            pick fresh α for
              (L `union` Lr `union` Lt `union` Lrb `union` La
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0' `union` Lf `union` ftvar_in_pskl Pi').
            destruct (IHX α (pskl_tophole Pi') Ψi (pskl_tophole P0') Δ
                        ltac:(clear - Fr; solve_notin)
                        Hdelta
                        ltac:(clear; fsetdec)
                        ltac:(eapply a_wf_pskl_weaken;
                              [ intros x b Hb; apply binds_cons_3; exact Hb
                              | exact HwfPi ])
                        ltac:(eapply a_wf_pskl_weaken;
                              [ intros x b Hb; apply binds_cons_3; exact Hb
                              | exact HwfP0 ])
                        Hshield
                        ltac:(eapply flex_apart_weaken;
                              [ apply HapF; clear - Fr; solve_notin
                              | intros x b Hb; apply binds_cons_3; exact Hb
                              | apply a_flex_tvar_strip_tvar ])
                        (HF α ltac:(clear - Fr; solve_notin))
                        HΨiS
                        ltac:(apply Hrefb; clear - Fr; solve_notin))
              as (PaX & HsX & HqX).
            assert (HsX0 : Θ0 ⊢ₑ (pskl_tophole Pi') ∼ (pskl_tophole P0')
                      ⤳ PaX)
              by (eapply a_solve_eq_strengthen_tvar; exact HsX).
            (* α ∉ ftv(msubst κ PaX): ftv PaX ⊆ ftv Pi' ∪ ftv P0', both α-free *)
            assert (HXPaX : α `notin` ftvar_in_pskl (msubst_pskl κ PaX)).
            { apply msubst_pskl_ftv_avoid.
              - intros p Hp; pose proof (Himav p Hp) as Hb;
                  clear - Hb Fr; destruct_notin; fsetdec.
              - pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ HsX) as Hfsub;
                  simpl in Hfsub;
                assert (HXPi' : α `notin` ftvar_in_pskl Pi')
                  by (pose proof (a_wf_pskl_ftv_dom HwfPi') as Hd;
                      clear - Hd Fr; simpl in Hd; destruct_notin; fsetdec);
                assert (HXP0' : α `notin` ftvar_in_pskl P0')
                  by (pose proof (a_wf_pskl_ftv_dom HwfP0'0) as Hd;
                      clear - Hd Fr; destruct_notin; fsetdec);
                clear - Hfsub HXPi' HXP0'; fsetdec. }
            (* tophole_both ⇒ PaX = ∀◇.Pbody (avoid global subst: HeqΘ would
               clear Θ) *)
            assert (Hpaform : exists Pbody, PaX = pskl_tophole Pbody).
            { inversion HsX;
                solve [ eexists; reflexivity
                      | match goal with
                        | Hg : guarded_pskl (pskl_tophole _) |- _ =>
                          inversion Hg
                        end ]. }
            destruct Hpaform as [Pbody Hpeq]; subst PaX.
            exists (pskl_tophole Pbody); split; [ exact HsX0 | ].
            intros Δ' HS1 HS2 HS3.
            simpl.
            apply ad_ppre__tophole_fill with (ε := ε)
              (L := Δ `union` Δ' `union` dom Θ `union` dom Θ0 `union` dom κ
                 `union` singleton ε `union` singleton α `union` Δρ
                 `union` ftvar_in_uskl ψR
                 `union` ftvar_in_pskl (msubst_pskl κ Pbody)).
            intros α' HX'.
            (* rename α↦α' in the single IHX precision instance *)
            assert (HS3' : delta_def_fresh Δ' ((α ~ abind_tvar) ++ Θ)).
            { intros Yd αd τ HYd Hbd.
              destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
                [ discriminate Hc | exact (HS3 Yd αd τ HYd Hbd') ]. }
            (* α was picked BEFORE Δ' (it flows into the solve output), so
               instantiate the family at Δ'∖{α} and weaken the missing
               Δ'∩{α} back at the end (α is fresh for the renamed target). *)
            pose proof (HqX (remove α Δ')
                          ltac:(clear - HS1; fsetdec)
                          ltac:(simpl; clear - HS2; fsetdec)
                          ltac:(intros Yd αd τ HYd Hbd;
                                eapply HS3';
                                  [ clear - HYd; fsetdec | exact Hbd ]))
              as Hq1.
            pose proof (@ad_partial_precise_rename_tvar
                          _ _ _ _ _ Hq1 α α' (@nil (atom * abind)) Θ
                          ltac:(apply a_wf_aenv_uniq; apply a_wf_aenv__tvar;
                                [ clear - Fr; solve_notin | exact HwfΘ ])
                          eq_refl
                          ltac:(simpl; clear - Fr HX'; solve_notin)
                          ltac:(clear - HX'; solve_notin)
                          ltac:(simpl; clear - HX' HXPaX; simpl in HXPaX;
                                solve_notin)
                          ltac:(pose proof
                                  (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                     (uskl_var_f α)) as Hup;
                                simpl in Hup; clear - HX' Hup;
                                destruct_notin; fsetdec)
                          ltac:(intros αd τ Hb;
                                destruct (binds_cons_1 _ _ _ _ _ _ Hb)
                                  as [[_ Hc] | Hb'];
                                  [ discriminate Hc | ];
                                assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                                  by (eapply a_wf_aenv_def_ftv_dom;
                                      [ exact HwfΘ | exact Hb' ]);
                                split; [ clear - Hd Fr | clear - Hd HX' ];
                                destruct_notin; fsetdec))
              as Hren.
            simpl in Hren.
            rewrite (subst_pskl_in_pskl_fresh_eq _ (pskl_var_f α') α)
              in Hren;
              [ | simpl in HXPaX; exact HXPaX ].
            rewrite <- (subst_bskl_in_uskl_intro α ψR (uskl_var_f α')
                          ltac:(clear - Fr; solve_notin)) in Hren.
            eapply ad_partial_precise_delta_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh
                  with (Δ' := Δ' ∩ singleton α);
                  [ exact Hren
                  | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                  (uskl_var_f α')) as Hup;
                    simpl in Hup;
                    apply atoms_inter_empty_pointwise;
                    intros y Hy;
                    assert (Heqy : y = α) by (clear - Hy; fsetdec);
                    subst y;
                    clear - Fr HX' Hup; destruct_notin; fsetdec
                  | intros Yd αd τ HYd Hbd;
                    assert (Heqy : Yd = α) by (clear - HYd; fsetdec);
                    subst Yd;
                    destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                      as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                    assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                      by (eapply a_wf_aenv_def_ftv_dom;
                          [ exact HwfΘ | exact Hbd' ]);
                    clear - Hd Fr; destruct_notin; fsetdec ]
              | clear; fsetdec ]. }
    (* the tophole_fill family leaves the rule's ε-witness unconstrained
       (any ε inhabits the same family); discharge it with the case's ε. *)
    Unshelve. all: match goal with |- εvar => exact ε | |- _ => idtac end.
    destruct (uskl_rho_all_etag_l_inv Hrho)
      as [[Heqψa HΨρe] | [Hleaf | (Lr & ψR & Heqψa & Hrhof)]].
    + (* refl *)
      subst ψa.
      assert (Htskf : exists Li, forall α, α `notin` Li ->
                is_tskl (open_uskl_wrt_uskl R (uskl_var_f α))).
      { destruct (a_tags_sort_all_etag_inv Htags)
          as (Lt0 & Ψt0 & Hf & _ & _).
        exists Lt0; intros α0 Hα0. destruct (Hf α0 Hα0); assumption. }
      destruct Htskf as (Li & Htskf).
      apply (KEYF R Li);
        [ intros α0 Hα0; apply urho__refl;
            [ apply is_tskl_lc; apply Htskf; exact Hα0 | exact HΨρe ]
        | exact Htags | exact Hapart | exact Hpre ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf)
        as (Pa & Hs & Hq).
      exists Pa; split; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
    + subst ψa.
      apply (KEYF ψR Lr);
        [ exact Hrhof | exact Htags | exact Hapart | exact Hpre ].
  - (* forall_syn: tag-sort absurd *)
    destruct (uskl_rho_all_syn_l_inv Hrho)
      as [[-> _] | [Hleaf | (L' & R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  - (* ghostg *)
    assert (Hrefine' : Θ ⨟ empty ⊢ᵣᵃ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_hole)
      by (eapply refine_primary_to_plain_split; eassumption).
    destruct (uskl_rho_holeg_l_inv Hrho) as [[-> HΨρ] | Hleaf].
    + assert (HΨ'e : Ψ' [=] empty)
        by (exact (d_tags_skl_holeg_inv (a_tags_sort_d_tags Htags))).
      assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
      destruct (a_solve_eq_cv_ghostg HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine')
        as (Pa & Hsolve & Hprec).
      exists Pa; split; [ exact Hsolve | ].
      intros Δ' HS1 HS2 HS3.
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_partial_precise_delta_weaken_fresh;
            [ exact Hprec | simpl; clear; fsetdec | exact HS3 ]
        | clear - HΨae; fsetdec ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf)
        as (Pa & Hs & Hq).
      exists Pa; split; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
  - (* topholeg: the ∀◈ congruence — recurse through the main IH.  Both
       the refl and congruence branches of the ρ-inversion land in KEY. *)
    assert (HwfΘr2 := HwfΘr).
    assert (KEY : forall ψa0,
      uskl_rho NM Θ Δρ Ψρ R ψa0 ->
      a_tags_sort NM Ψ' (uskl_topholeg ψa0) ->
      flex_apart Θ0 Δρ P0 (uskl_topholeg ψa0) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_topholeg ψa0) ->
      exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
        forall Δ',
          Δ' ∩ Δ [=] empty ->
          Δ' ∩ dom Θr [=] empty ->
          delta_def_fresh Δ' Θ ->
          Θ ⨟ (Δ `union` Δ') ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ]
            (uskl_topholeg ψa0)).
    { intros ψa0 Hrho0 Htags0 Hap0 Hpre0.
      assert (Htags1 : a_tags_sort NM Ψ' ψa0)
        by (apply a_tags_sort_topholeg_inv; exact Htags0).
      (* the P0=□ rows' target bound: ψa0's variables are Θr- or
         Δρ-scoped once the counterpart is a synthesised fill *)
      assert (HψaB : ftvar_in_bskl Q [<=] dom Θr ->
                ftvar_in_uskl ψa0 [<=] dom Θr `union` Δρ).
      { intros HQB.
        assert (HftR : ftvar_in_uskl R [<=]
                  ftvar_in_bskl Q `union` dom Θr)
          by (eapply consis_subject_ftv_bag_bound;
                [ exact Hconsis | exact HspΘ | exact Htvs | exact HwfΘr ]).
        pose proof (uskl_rho_ftv_target_bound Hrho0) as HftA.
        clear - HQB HftR HftA; fsetdec. }
      destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
      - (* Pi = unit: no precision into ∀◈ *)
        simpl in Hpre0. inversion Hpre0.
      - (* Pi = var_b *) inversion HwfPi.
      - (* Pi = var: mono paint, absurd *)
        exfalso. simpl in Hpre0.
        eapply ad_ppre_mono_paint_topholeg_absurd;
          [ exact HwfΘ | exact Hpre0 | reflexivity | reflexivity
          | eapply a_inc_lookup_mono; eauto ].
      - (* Pi = arrow *) simpl in Hpre0. inversion Hpre0.
      - (* Pi = all_syn *) simpl in Hpre0. inversion Hpre0.
      - (* Pi = □: SE-GhostL / VacuousR column *)
        destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
        + (* P0 = unit *) simpl in Hrefine. inversion Hrefine.
        + (* P0 = var_b *) inversion HwfP0.
        + (* P0 = var: mono paint vs ∀◇ RHS, absurd *)
          exfalso. simpl in Hrefine.
          assert (Hml : mono_ptyp (msubst_lookup κ β))
            by (eapply a_inc_lookup_mono; eauto).
          rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
          eapply ad_refine_mono_paint_tophole_rhs_absurd;
            [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
            | exact Hml ].
        + (* P0 = arrow *) simpl in Hrefine. inversion Hrefine.
        + (* P0 = all_syn *) simpl in Hrefine. inversion Hrefine.
        + (* P0 = □: SE-VacuousR; Q synthesized ⇒ Ψa = ∅ *)
          simpl in Hrefine.
          pose proof (ad_refine_syn_hole_sskl Hrefine eq_refl) as Hss.
          assert (HskQ : is_sskl Q) by (inversion Hss; subst; assumption).
          pose proof (ad_pat_consis_sskl_tags Hconsis HwfΘ HskQ) as HΨe.
          assert (HQB : ftvar_in_bskl Q [<=] dom Θr).
          { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine).
            simpl in Ht. clear - Ht; fsetdec. }
          exists pskl_hole; split; [ apply a_solve_eq__hole_r | ].
          intros Δ' HS1 HS2 HS3.
          eapply ad_partial_precise_psi_cong;
            [ eapply ad_partial_precise_delta_weaken_fresh;
                [ exact Hpre0
                | simpl;
                  pose proof (HψaB HQB) as Hbb;
                  clear - Hbb HS1 HS2 Hdelta; fsetdec
                | exact HS3 ]
            | clear - HΨe Hsubeq2; fsetdec ].
        + (* P0 = ∀◇.P0': Pa := P0; body precision via the main IH at □ *)
          assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
            by (inversion HwfP0; assumption).
          assert (HgP0' : guarded_pskl P0')
            by (inversion HwfP0; assumption).
          simpl in Hrefine.
          inversion Hrefine; subst.
          * (* tophole_remove: the guarded body dies against a ∀◇ RHS *)
            exfalso. inversion HgP0'; subst.
            -- match goal with
               | Hin : _ ⨟ _ ⊢ᵣᵃ
                   pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ |- _ =>
                 simpl in Hin; inversion Hin
               end.
            -- match goal with
               | Hin : _ ⨟ _ ⊢ᵣᵃ
                   pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _
                 |- _ =>
                 let Hml := fresh in
                 assert (Hml : mono_ptyp (msubst_lookup κ v))
                   by (eapply a_inc_lookup_mono; eauto);
                 simpl in Hin;
                 rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
                 eapply ad_refine_mono_paint_tophole_rhs_absurd;
                   [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                   | exact Hml ]
               end.
            -- match goal with
               | Hin : _ ⨟ _ ⊢ᵣᵃ
                   pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _
                 |- _ =>
                 simpl in Hin; inversion Hin
               end.
          * (* tophole_keep: recurse with Pi := □ *)
            assert (Hhp0 : Θ ⨟ Δ ⊢
                      msubst_pskl κ pskl_hole ⊑ᵖ[ Ψi ] ψa0).
            { simpl. simpl in Hpre0. inversion Hpre0; subst.
              match goal with
              | HΨE : Ψi [=] empty,
                Hint : _ ∩ _ [=] empty |- _ =>
                apply ad_ppre__hole; [ exact HΨE | ];
                simpl in Hint; exact Hint
              end. }
            match goal with
            | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ Q
              |- _ =>
              destruct (IHHconsis NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr
                          Ψρ Ψ' Ψi Ψa ψa0 pskl_hole P0'
                          HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                          HwfΘ HwfΘ0 ltac:(apply a_wf_pskl__hole) HwfP0'
                          Hκ
                          Hrho0 Htags1 Hsub Hinter Hfresh Hdelta
                          ltac:(intros α0 HX0; simpl; auto)
                          Hdfresh
                          ltac:(apply flex_apart_topholeg_target_inv;
                                apply flex_apart_tophole_p0_inv; exact Hap0)
                          Hhp0 Hsubeq1 Hsubeq2 Hin)
                as (Pa' & Hs' & Hq')
            end.
            pose proof (a_solve_eq_hole_subject_inv Hs') as HPa'; subst Pa'.
            exists (pskl_tophole P0'); split;
              [ apply a_solve_eq__hole_l | ].
            intros Δ' HS1 HS2 HS3.
            simpl. apply ad_ppre__tophole_keep.
            exact (Hq' Δ' HS1 HS2 HS3).
      - (* Pi = ∀◇.Pi' *)
        assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
        assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi') by (inversion HwfPi; assumption).
        simpl in Hpre0. inversion Hpre0; subst.
        + (* tophole_remove: the guarded body dies against ∀◈ *)
          exfalso. inversion HgPi'; subst.
          * match goal with
            | Hp' : _ ⨟ _ ⊢ msubst_pskl κ pskl_unit ⊑ᵖ[ _ ] _ |- _ =>
                simpl in Hp'; inversion Hp'
            end.
          * match goal with
            | Hp' : _ ⨟ _ ⊢ msubst_pskl κ (pskl_var_f ?v) ⊑ᵖ[ _ ] _ |- _ =>
                simpl in Hp';
                eapply ad_ppre_mono_paint_topholeg_absurd;
                  [ exact HwfΘ | exact Hp' | reflexivity | reflexivity
                  | eapply a_inc_lookup_mono; eauto ]
            end.
          * match goal with
            | Hp' : _ ⨟ _ ⊢ msubst_pskl κ (pskl_arrow _ _) ⊑ᵖ[ _ ] _ |- _ =>
                simpl in Hp'; inversion Hp'
            end.
        + (* tophole_keep: the live congruence *)
          match goal with
          | Hp' : _ ⨟ _ ⊢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] ψa0 |- _ =>
            rename Hp' into Hpre1
          end.
          assert (Hshield' : forall α, α `in` Δρ ->
                    α `notin` pskl_shielded_ftv (msubst_pskl κ Pi')).
          { intros α0 HX0.
            pose proof (Hshield α0 HX0) as Hsh. simpl in Hsh.
            pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi')).
            fsetdec. }
          destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          * (* P0 = unit *) simpl in Hrefine. inversion Hrefine.
          * (* P0 = var_b *) inversion HwfP0.
          * (* P0 = var: mono paint vs ∀◇ RHS *)
            exfalso. simpl in Hrefine.
            assert (Hml : mono_ptyp (msubst_lookup κ β))
              by (eapply a_inc_lookup_mono; eauto).
            rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
            eapply ad_refine_mono_paint_tophole_rhs_absurd;
              [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
              | exact Hml ].
          * (* P0 = arrow *) simpl in Hrefine. inversion Hrefine.
          * (* P0 = all_syn *) simpl in Hrefine. inversion Hrefine.
          * (* P0 = □: SE-VacuousR *)
            simpl in Hrefine.
            pose proof (ad_refine_syn_hole_sskl Hrefine eq_refl) as Hss.
            assert (HskQ : is_sskl Q) by (inversion Hss; subst; assumption).
            pose proof (ad_pat_consis_sskl_tags Hconsis HwfΘ HskQ) as HΨe.
            assert (HQB : ftvar_in_bskl Q [<=] dom Θr).
            { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine).
              simpl in Ht. clear - Ht; fsetdec. }
            exists (pskl_tophole Pi'); split;
              [ apply a_solve_eq__hole_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ simpl; apply ad_ppre__tophole_keep;
                eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨe Hsubeq2; fsetdec ].
          * (* P0 = ∀◇.P0': SE-UnivGhost via the main IH *)
            assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
              by (inversion HwfP0; assumption).
            assert (HgP0' : guarded_pskl P0')
              by (inversion HwfP0; assumption).
            simpl in Hrefine.
            inversion Hrefine; subst.
            -- (* tophole_remove: guarded body dies *)
               exfalso. inversion HgP0'; subst.
               ++ match goal with
                  | Hin : _ ⨟ _ ⊢ᵣᵃ
                      pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ |- _ =>
                    simpl in Hin; inversion Hin
                  end.
               ++ match goal with
                  | Hin : _ ⨟ _ ⊢ᵣᵃ
                      pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _
                    |- _ =>
                    let Hml := fresh in
                    assert (Hml : mono_ptyp (msubst_lookup κ v))
                      by (eapply a_inc_lookup_mono; eauto);
                    simpl in Hin;
                    rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
                    eapply ad_refine_mono_paint_tophole_rhs_absurd;
                      [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                      | exact Hml ]
                  end.
               ++ match goal with
                  | Hin : _ ⨟ _ ⊢ᵣᵃ
                      pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _
                    |- _ =>
                    simpl in Hin; inversion Hin
                  end.
            -- (* tophole_keep: recurse *)
               match goal with
               | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ Q
                 |- _ =>
                 destruct (IHHconsis NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr
                             Ψρ Ψ' Ψi Ψa ψa0 Pi' P0'
                             HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                             HwfΘ HwfΘ0 HwfPi' HwfP0' Hκ
                             Hrho0 Htags1 Hsub Hinter Hfresh Hdelta
                             Hshield' Hdfresh
                             ltac:(apply flex_apart_topholeg_target_inv;
                                   apply flex_apart_tophole_p0_inv;
                                   exact Hap0)
                             Hpre1 Hsubeq1 Hsubeq2 Hin)
                   as (Pa' & Hs' & Hq')
               end.
               exists (pskl_tophole Pa'); split;
                 [ apply a_solve_eq__tophole_both; exact Hs' | ].
               intros Δ' HS1 HS2 HS3.
               simpl. apply ad_ppre__tophole_keep.
               exact (Hq' Δ' HS1 HS2 HS3). }
    destruct (uskl_rho_topholeg_l_inv Hrho)
      as [[Heqψa HΨρ] | [Hleaf | (ψa0 & Heqψa & Hrho0)]].
    + (* refl: recast as a congruence with a refl body-ρ *)
      subst ψa.
      assert (HlcR : lc_uskl R).
      { apply is_tskl_lc.
        match goal with Ht : a_tags_sort _ _ (uskl_topholeg R) |- _ =>
          inversion Ht; subst;
          match goal with Hti : is_tskl (uskl_topholeg _) |- _ =>
            inversion Hti; subst; assumption end end. }
      apply KEY;
        [ apply urho__refl; [ exact HlcR | exact HΨρ ]
        | exact Htags | exact Hapart | exact Hpre ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf)
        as (Pa & Hs & Hq).
      exists Pa; split; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
    + subst ψa.
      apply KEY; [ exact Hrho0 | exact Htags | exact Hapart | exact Hpre ].
  - (* hole: ψa is tag-sorted, hence never a PLAIN ghost *)
    destruct (uskl_rho_hole_l_inv Hrho) as [[-> _] | Hleaf].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
  - (* tophole *)
    destruct (uskl_rho_tophole_l_inv Hrho)
      as [[-> _] | [Hleaf | (R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  - (* tophole_inh *)
    destruct (uskl_rho_tophole_l_inv Hrho)
      as [[-> _] | [Hleaf | (R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  - (* tophole_drop *)
    destruct (uskl_rho_tophole_l_inv Hrho)
      as [[-> _] | [Hleaf | (R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  - (* flex_l: switch the whole problem to the definition's mono paint *)
    destruct (uskl_rho_var_l_inv Hrho) as [[-> HΨρ] | Hleaf];
      [ | destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                      HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf)
            as (Pa & Hs & Hq);
          exists Pa; split;
            [ exact Hs
            | intros Δ' HS1 HS2 HS3; apply Hq; clear; fsetdec ] ].
    assert (HΨ'e : Ψ' [=] empty)
      by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
    assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact H ]).
    assert (HΨie : Ψi [=] empty)
      by (eapply ad_ppre_mono_tags_empty with (τ := ptyp_var_f α);
            [ exact HwfΘ | exact Hpre | reflexivity | apply mono_ptyp__var ]).
    destruct (IHHconsis NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr empty empty Ψi empty
                (ptyp_to_uskl_syn τ) Pi P0
                HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                HwfΘ HwfΘ0 HwfPi HwfP0 Hκ
                ltac:(apply urho__refl;
                        [ apply mono_ptyp_to_uskl_syn_lc; exact Hmd
                        | fsetdec ])
                ltac:(apply a_tags_sort_mono_paint; exact Hmd)
                ltac:(clear - HΨie; fsetdec)
                ltac:(clear; fsetdec)
                Hfresh Hdelta Hshield Hdfresh
                ltac:(apply fa_clean;
                        rewrite ftvar_in_uskl_ptyp_to_uskl_syn;
                        apply atoms_inter_empty_pointwise;
                        intros y Hy HyΔρ;
                        match goal with
                        | Hb : binds _ (abind_flex_mono_def _) _ |- _ =>
                            exact (proj2 (proj2 (Hfresh y HyΔρ)) _ _ Hb Hy)
                        end)
                ltac:(eapply ad_ppre_flexdef_target_unfold;
                        [ exact HwfΘ | exact Hdfresh | exact Hpre
                        | reflexivity | eassumption ])
                ltac:(clear - Hsubeq1 HΨρ HΨae; fsetdec)
                ltac:(clear; fsetdec)
                Hrefine)
      as (Pa & Hsolve & Hprec).
    exists Pa; split; [ exact Hsolve | ].
    intros Δ' HS1 HS2 HS3.
    eapply ad_partial_precise_psi_cong;
      [ eapply ad_ppre__flex_r;
          [ eassumption | exact (Hprec Δ' HS1 HS2 HS3) ]
      | clear - HΨae; fsetdec ].
  - (* flex_r: unfold the counterpart-side definition in the PRIMARY
       refinement (the defined flexible lives in Θr) *)
    assert (HwfΘr2 := HwfΘr).
    assert (Hbdef : binds α (abind_flex_mono_def τ) Θr).
    { eapply aenv_split_binds_def_r;
        [ exact HspΘ | exact Htvs | eassumption ]. }
    eapply IHHconsis; try eassumption.
    eapply ad_refine_flexdef_target_unfold;
      [ exact HwfΘr | exact Hrefine | reflexivity | exact Hbdef ].
Qed.

(* ===================================================================== *)
(*  THE PAPER STATEMENT — P6-Cv,                                          *)
(*  [lemma:complete-consistency-constraint-collection-solving-var]        *)
(*  (consistency-proofs.tex:1180), via _gen at Θtv := [] / Δr := ∅ /      *)
(*  R := ∅.  Premises are annotated inline; the MECH-ONLY ones, and what  *)
(*  callers (P6-Cs consistency-proofs.tex:993; P6-Rv subtyping-proofs     *)
(*  .tex:1778/1965/2035) owe for them:                                    *)
(*   1. (REMOVED 2026-07-27) an earlier closure carried a MECH-ONLY       *)
(*      [pskl_no_hole P0] premise: with the LIST split Θ = Θtv ++ Θr the  *)
(*      ForallSyn binder was forced into Θtv, so the tophole_fill body    *)
(*      had to be transported aenv→Δr — false for □-sources whose fill    *)
(*      mentions the binder (inh(□→1) ⊳ β→1, fill β).  The BAG split     *)
(*      [aenv_split] lets that binder join Θr instead, the body is the   *)
(*      IH's refinement premise verbatim, and holey P0 flows through the  *)
(*      recursion to the per-row SolE-VacuousR columns — exactly the      *)
(*      paper's per-node "P0 = Hole" dispatch.  The statement is now      *)
(*      PREMISE-FAITHFUL to the paper on this point.                      *)
(*   2. delta_def_fresh Δ Θ — the paper's implicit wf of the Δ-extended   *)
(*      context; machine-checked necessary; free at call sites            *)
(*      (WF-SIDE-CONDITIONS §7: binders postdate definitions).            *)
(*   3. flex_apart Θ0 Δρ P0 ψa — the LE-FlexR freshening invariant (a     *)
(*      raw Θ0-flex of P0 never faces a ρ-replaced part of ψa); NOT       *)
(*      derivable from the other premises (cex_p6_flex_freshened.v);      *)
(*      vacuous (fa_clean) at every ρ = id call site, e.g. P6-Cs's,       *)
(*      since Δρ = ∅ — only the P6-Rv ForallL descent maintains it.       *)
(*   4. the rho_fresh / Δρ ⊆ Δ / shielded pack — replaces the paper's     *)
(*      positional "Pi has the same rigid variable at every ρ-position"   *)
(*      side condition ([paper-gap], see the prop_look_complete.v         *)
(*      header); established at the one leaf-creating call site, P6-Rv    *)
(*      ForallL.                                                          *)
(*  CONCLUSION vs paper: κa is instantiated to κ itself (a strengthening  *)
(*  — the paper's κa-inc and κ ≡ κa conjuncts become trivial); Θ0 ⊢ Pa    *)
(*  is omitted (recover by solve-output wf preservation when P6-Cs        *)
(*  needs it).                                                            *)
(*  PROOF/CASE MAP (the _gen induction is on the ad_pat_consis            *)
(*  derivation of the subject ψsub = ρ(ψa), as the paper prescribes):     *)
(*  unit/var/ghostg ↔ Case Unit/Var/GhostG; arrow ↔ Case Arrow (+ the     *)
(*  flexible-P0 subcase repair, DESIGN §6(g)); forall_inh_tagged ↔        *)
(*  ForallInh; forall_syn_tagged ↔ ForallSyn; topholeg ↔ UnivGhostG;      *)
(*  hole ↔ Ghost (impossible); tophole ↔ UnivGhost; tophole_inh ↔         *)
(*  UnivGhost1; tophole_drop ↔ UnivGhost2; forall_inh_untagged/           *)
(*  forall_syn ↔ the β1 = · instances of C-ForallInh/C-ForallSyn (the      *)
(*  paper's ∀^β1 subject carries a POTENTIAL tag β1 ::= · | ε,              *)
(*  declarative.tex:884 — one paper rule per target = two mech            *)
(*  constructors), absurd here since the tags-sorted target forces        *)
(*  β1 = ε; flex_l/flex_r ↔ paper C-FlexL/C-FlexR                          *)
(*  (full-algo-spec.tex:183/190) — real paper rules, merely OMITTED from  *)
(*  the paper proof's case list (routine definition-unfolding).  The      *)
(*  paper's upfront special case "ψa is a ρ-replaced rigid variable" is   *)
(*  handled per-case via the uskl_rho_*_l_inv leaf disjunct +             *)
(*  p6cv_close_leaf_mono; its "P0 = Hole" special case is the per-case    *)
(*  SolE-VacuousR columns (P0-grids of the arrow/∀/∀◇ cases and the       *)
(*  leaf-closer lemmas), re-dispatched inside every IH exactly as the     *)
(*  paper's proof does.                                                   *)
(* ===================================================================== *)
Theorem a_solve_eq_complete_var :
  forall NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->      (* paper: prose "all inputs wf" *)
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->   (* Θ0 ⊢ Pi, Θ0 ⊢ P0 *)
  κ ∷ Θ0 ⊑ Θ ->                       (* κ : Θ0 ⊑ Θ *)
  uskl_rho NM Θ Δρ Ψρ ψsub ψa ->      (* ρ: ψsub = ρ(ψa), Ψρ = its Ψ *)
  a_tags_sort NM Ψ' ψa ->             (* Θ ⊢^N Ψ'{syn ψa} *)
  Ψi `union` Ψa [<=] Ψ' ->            (* Ψi, Ψa ⊆ Ψ' *)
  Ψρ ∩ Ψ' [=] empty ->   (* the fresh{Ψ'} instance used *)
  rho_fresh Δρ Θ κ -> Δρ [<=] Δ ->    (* MECH-ONLY (4): the ρ-freshness *)
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->              (* MECH-ONLY (2) *)
  flex_apart Θ0 Δρ P0 ψa ->           (* MECH-ONLY (3) *)
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->   (* Δ|Θ ⊢ κPi ⊑ᵖ[Ψi] ψa *)
  Ψsub [<=] Ψρ `union` Ψa ->          (* the consistency index is the *)
  Ψa [<=] Ψsub ->                     (*   paper's "Ψ,Ψa", as bounds *)
  Ψsub ⨟ Θ ⊢ₛᵃ ψsub ∼ Q ->            (* Θ ⊨[Ψ,Ψa] syn(ρψa) ∼ Q *)
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
                                      (* Θ ⊢ inh(κP0) ⊳ Q *)
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\    (* solveeq{Pi}{P0}{Pa} *)
             Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
                                      (* Δ|Θ ⊢ κPa ⊑ᵖ[Ψi,Ψa] ψa, κa := κ *)
Proof.
  intros NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hrho Htags Hsub Hinter Hfresh Hdelta
         Hshield Hdfresh Hapart Hpre Hsubeq1 Hsubeq2 Hconsis Hrefine.
  destruct (@a_solve_eq_complete_var_gen NM Θ Θ0 nil Θ Θ0 κ Δ Δρ empty
              Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0
              (aenv_split_nil Θ) (aenv_split_nil Θ0) HwfΘ
              ltac:(intros x b Hb; destruct Hb)
              ltac:(simpl; clear; fsetdec)
              ltac:(clear; fsetdec)
              HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hrho Htags Hsub Hinter Hfresh
              Hdelta Hshield Hdfresh Hapart Hpre Hsubeq1 Hsubeq2 Hconsis
              Hrefine)
    as (Pa & Hs & Hfam).
  exists Pa; split; [ exact Hs | ].
  eapply ad_partial_precise_delta_cong;
    [ apply (Hfam empty);
      [ clear; fsetdec | clear; fsetdec
      | intros β α τ Hβ Hb; exfalso; clear - Hβ; fsetdec ]
    | clear; fsetdec ].
Qed.

Print Assumptions a_solve_eq_complete_var.
