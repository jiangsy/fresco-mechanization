(** RIGIDITY PRESERVATION — what an algorithmic run does NOT disturb.  Two
    families of pure structural facts about the ALGORITHM that theorem 4
    (thm:complete-type-inference, [prop_typing.v]) consumes.  This is the TY
    sort discipline paying out:

    (1) [a_rigid_only] PRESERVATION: an atom that is rigid and nowhere
        flexible stays so through every algorithmic judgement.  Pure — every
        entry a run drops or invents is governed by a rule-level Barendregt /
        [a_suffix] / [uniq] premise, so no well-formedness threading is
        needed.

    (2) The TC-CORE of a run's input is returned VERBATIM when it is rigid
        ([a_typing_tc_rigid_output]) — what [AT-Anno]'s body premise (the
        run at the annotation returns the annotation ITSELF) needs from
        completeness.  The paper writes this as a metavariable pun
        (proofs.tex Anno case: "IH gives ⊢[TC;A] M ⦂ A ⊣ Θ1").

    Also here, same theme: a TY-sorted subtyping run's OUTPUT is ghost-free
    given a ghost-free subject ([a_sub_ty_ghost_free_output]), with the
    consistency companion — so the output IS a painted [ptyp]
    ([pskl_ghost_free_to_ptyp]) and the [a_typing] rules' [⌈A⌉]-shaped
    premises are satisfiable. *)
Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_pat_sub.

Set Implicit Arguments.

(* ===================================================================== *)
(*  [a_rigid_only Θ γ] — γ is RIGID in Θ and nowhere flexible.  This is    *)
(*  what "the annotation's variables are rigid" must mean for the walks:   *)
(*  an assignment can never target γ, and a substitution by a flexible's   *)
(*  definition can never rewrite γ.                                        *)
(* ===================================================================== *)

Definition a_rigid_only (Θ : aenv) (γ : atom) : Prop :=
  binds γ abind_tvar Θ /\
  ~ binds γ abind_flex_mono Θ /\
  (forall τ, ~ binds γ (abind_flex_mono_def τ) Θ).

Lemma a_rigid_only_in_dom : forall Θ γ,
  a_rigid_only Θ γ -> γ `in` dom Θ.
Proof. intros Θ γ [Hb _]; eapply binds_In; exact Hb. Qed.

(** Cons by anything non-flexible (a rigid tvar or a term entry). *)
Lemma a_rigid_only_cons_nonsuffix : forall c (b : abind) Θ γ,
  ~ a_suffix_binding b ->
  a_rigid_only Θ γ -> a_rigid_only ((c ~ b) ++ Θ) γ.
Proof.
  intros c b Θ γ Hnb [Hb [Hnm Hnd]].
  split; [ apply binds_cons_3; exact Hb | ].
  split.
  - intros Hc; destruct (binds_cons_1 _ _ _ _ _ _ Hc) as [[_ Heq] | Hc'];
      [ subst; apply Hnb; apply a_suffix_binding__flex_mono
      | apply Hnm; exact Hc' ].
  - intros τ Hc; destruct (binds_cons_1 _ _ _ _ _ _ Hc) as [[_ Heq] | Hc'];
      [ subst; apply Hnb; apply a_suffix_binding__flex_mono_def
      | eapply Hnd; exact Hc' ].
Qed.

(** Cons by anything at a DIFFERENT atom. *)
Lemma a_rigid_only_cons_other : forall c (b : abind) Θ γ,
  c <> γ ->
  a_rigid_only Θ γ -> a_rigid_only ((c ~ b) ++ Θ) γ.
Proof.
  intros c b Θ γ Hne [Hb [Hnm Hnd]].
  split; [ apply binds_cons_3; exact Hb | ].
  split.
  - intros Hc; destruct (binds_cons_1 _ _ _ _ _ _ Hc) as [[Heq _] | Hc'];
      [ subst; apply Hne; reflexivity | apply Hnm; exact Hc' ].
  - intros τ Hc; destruct (binds_cons_1 _ _ _ _ _ _ Hc) as [[Heq _] | Hc'];
      [ subst; apply Hne; reflexivity | eapply Hnd; exact Hc' ].
Qed.

(** Strip a head whose payload is not [abind_tvar]. *)
Lemma a_rigid_only_strip_head_nonrigid : forall c (b : abind) Θ γ,
  b <> abind_tvar ->
  a_rigid_only ((c ~ b) ++ Θ) γ -> a_rigid_only Θ γ.
Proof.
  intros c b Θ γ Hnb [Hb [Hnm Hnd]].
  split.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
      [ exfalso; apply Hnb; symmetry; exact Heq | exact Hb' ].
  - split;
      [ intros Hc; apply Hnm; apply binds_cons_3; exact Hc
      | intros τ Hc; eapply Hnd; apply binds_cons_3; exact Hc ].
Qed.

(** Strip a head at a DIFFERENT atom. *)
Lemma a_rigid_only_strip_head_other : forall c (b : abind) Θ γ,
  c <> γ ->
  a_rigid_only ((c ~ b) ++ Θ) γ -> a_rigid_only Θ γ.
Proof.
  intros c b Θ γ Hne [Hb [Hnm Hnd]].
  split.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
      [ exfalso; apply Hne; symmetry; exact Heq | exact Hb' ].
  - split;
      [ intros Hc; apply Hnm; apply binds_cons_3; exact Hc
      | intros τ Hc; eapply Hnd; apply binds_cons_3; exact Hc ].
Qed.

(** Strip a whole flexible-only prefix. *)
Lemma a_rigid_only_strip_suffix : forall Ξ Θ γ,
  a_suffix Ξ ->
  a_rigid_only (Ξ ++ Θ) γ -> a_rigid_only Θ γ.
Proof.
  intros Ξ Θ γ Hs; induction Hs; intros Hro; [ exact Hro | ].
  apply IHHs. simpl_env in Hro.
  eapply a_rigid_only_strip_head_nonrigid; [ | exact Hro ].
  match goal with
  | Hb : a_suffix_binding _ |- _ => inversion Hb; discriminate
  end.
Qed.

(** Weaken by any prefix that avoids γ. *)
Lemma a_rigid_only_weaken_app_fresh : forall Ξ Θ γ,
  γ `notin` dom Ξ ->
  a_rigid_only Θ γ -> a_rigid_only (Ξ ++ Θ) γ.
Proof.
  intros Ξ; induction Ξ as [ | [c b] Ξ' IH ]; intros Θ γ Hd H;
    [ exact H | ].
  simpl in Hd. simpl_env.
  apply a_rigid_only_cons_other;
    [ intros ->; clear - Hd; fsetdec
    | apply IH; [ clear - Hd; fsetdec | exact H ] ].
Qed.

(** Strip a MID entry whose payload is not [abind_tvar]. *)
Lemma a_rigid_only_strip_mid_nonrigid : forall Θa c (b : abind) Θb γ,
  b <> abind_tvar ->
  a_rigid_only (Θa ++ (c ~ b) ++ Θb) γ -> a_rigid_only (Θa ++ Θb) γ.
Proof.
  intros Θa c b Θb γ Hnb [Hb [Hnm Hnd]].
  split.
  - apply binds_app_1 in Hb as [Hb | Hb];
      [ apply binds_app_2; exact Hb | ].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
      [ exfalso; apply Hnb; symmetry; exact Heq
      | apply binds_app_3; exact Hb' ].
  - split;
      [ intros Hc; apply Hnm | intros τ Hc; eapply Hnd ];
      apply binds_weaken; exact Hc.
Qed.

(** Strip a MID entry at a DIFFERENT atom. *)
Lemma a_rigid_only_strip_mid_other : forall Θa c (b : abind) Θb γ,
  c <> γ ->
  a_rigid_only (Θa ++ (c ~ b) ++ Θb) γ -> a_rigid_only (Θa ++ Θb) γ.
Proof.
  intros Θa c b Θb γ Hne [Hb [Hnm Hnd]].
  split.
  - apply binds_app_1 in Hb as [Hb | Hb];
      [ apply binds_app_2; exact Hb | ].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
      [ exfalso; apply Hne; symmetry; exact Heq
      | apply binds_app_3; exact Hb' ].
  - split;
      [ intros Hc; apply Hnm | intros τ Hc; eapply Hnd ];
      apply binds_weaken; exact Hc.
Qed.

(** Insert a MID entry at a DIFFERENT atom. *)
Lemma a_rigid_only_insert_mid : forall Θa c (b : abind) Θb γ,
  c <> γ ->
  a_rigid_only (Θa ++ Θb) γ -> a_rigid_only (Θa ++ (c ~ b) ++ Θb) γ.
Proof.
  intros Θa c b Θb γ Hne [Hb [Hnm Hnd]].
  split; [ apply binds_weaken; exact Hb | ].
  split.
  - intros Hc; apply binds_app_1 in Hc as [Hc | Hc];
      [ apply Hnm; apply binds_app_2; exact Hc | ].
    destruct (binds_cons_1 _ _ _ _ _ _ Hc) as [[Heq _] | Hc'];
      [ apply Hne; symmetry; exact Heq
      | apply Hnm; apply binds_app_3; exact Hc' ].
  - intros τ Hc; apply binds_app_1 in Hc as [Hc | Hc];
      [ eapply Hnd; apply binds_app_2; exact Hc | ].
    destruct (binds_cons_1 _ _ _ _ _ _ Hc) as [[Heq _] | Hc'];
      [ apply Hne; symmetry; exact Heq
      | eapply Hnd; apply binds_app_3; exact Hc' ].
Qed.

(** γ bound in the tail of a uniq split cannot be in the prefix's domain. *)
Lemma a_rigid_only_notin_prefix : forall (Ξ Θ : aenv) γ,
  uniq (Ξ ++ Θ) ->
  γ `in` dom Θ ->
  γ `notin` dom Ξ.
Proof. intros Ξ Θ γ Hu Hd. solve_uniq. Qed.

(* ===================================================================== *)
(*  Preservation, judgement by judgement                                  *)
(* ===================================================================== *)

Lemma a_assign_unify_consis_rigid_only :
  (forall Θ0 Ξ α P Θ1,
     a_assign Θ0 Ξ α P Θ1 ->
     forall γ, a_rigid_only (Ξ ++ Θ0) γ -> a_rigid_only Θ1 γ) /\
  (forall Θ0 α β Θ1,
     a_unify Θ0 α β Θ1 ->
     forall γ, a_rigid_only Θ0 γ -> a_rigid_only Θ1 γ) /\
  (forall Δ1 Δ2 Θ0 P0 P Q Θ1,
     a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 ->
     forall γ, a_rigid_only Θ0 γ -> a_rigid_only Θ1 γ).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun Θ0 Ξ α P Θ1 _ =>
              forall γ, a_rigid_only (Ξ ++ Θ0) γ -> a_rigid_only Θ1 γ)
           (fun Θ0 α β Θ1 _ =>
              forall γ, a_rigid_only Θ0 γ -> a_rigid_only Θ1 γ)
           (fun Δ1 Δ2 Θ0 P0 P Q Θ1 _ =>
              forall γ, a_rigid_only Θ0 γ -> a_rigid_only Θ1 γ)).
  - (* Assign-UnivGhost-Id *)
    intros Θ0 α γ H; exact H.
  - (* Assign-SolveM : upgrade α̂, deposit fresh β̄s *)
    intros Θ0 Ξ α P βs τ Hα Hg Hm Huq Hfr γ H.
    assert (Hγα : α <> γ).
    { intros ->. destruct H as [_ [Hnm _]].
      apply Hnm. apply binds_app_3. apply binds_app_2.
      unfold binds; simpl; auto. }
    assert (H' : a_rigid_only (Ξ ++ Θ0) γ)
      by (eapply a_rigid_only_strip_mid_nonrigid;
          [ | exact H ]; discriminate).
    assert (Hγd : γ `in` dom (Ξ ++ Θ0))
      by (apply a_rigid_only_in_dom; exact H').
    apply a_rigid_only_cons_other; [ exact Hγα | ].
    apply a_rigid_only_weaken_app_fresh; [ | exact H' ].
    intros Hin. pose proof (Hfr γ Hin) as Hc. clear - Hc Hγd. fsetdec.
  - (* Assign-Assign : walk into β̂'s definition *)
    intros Θ0 Θ1 Ξ α β τ P Q Hflex Hβ Hc IH γ H.
    assert (Hγβ : β <> γ).
    { intros ->. destruct H as [_ [_ Hnd]].
      eapply Hnd. apply binds_app_3. apply binds_app_2.
      unfold binds; simpl; eauto. }
    apply a_rigid_only_cons_other; [ exact Hγβ | ].
    apply IH.
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact H ]; discriminate.
  - (* Assign-Depend : β̂ moves from the context head to Ξ's tail *)
    intros Θ0 Θ1 Ξ α β P Hne Hβ Ha IH γ H.
    apply IH. rewrite app_assoc. exact H.
  - (* Assign-Skip *)
    intros Θ0 Θ1 Ξ α β P Hne Hβ Hβd Ha IH γ H.
    assert (Hγβ : β <> γ).
    { intros ->. destruct H as [_ [Hnm _]].
      apply Hnm. apply binds_app_3. apply binds_app_2.
      unfold binds; simpl; auto. }
    apply a_rigid_only_cons_other; [ exact Hγβ | ].
    apply IH.
    eapply a_rigid_only_strip_mid_other; [ exact Hγβ | exact H ].
  - (* Assign-SkipRigid *)
    intros Θ0 Θ1 Ξ α β P Hβ Hβd Ha IH γ H.
    destruct (γ == β) as [-> | Hne].
    + (* the walked rigid IS γ: it is re-attached, and the run below it
         deposits only fresh names (β ∉ dom Θ1, the rule's Barendregt) *)
      split; [ apply binds_app_2; unfold binds; simpl; auto | ].
      split;
        [ intros Hc | intros τ Hc ];
        destruct (binds_cons_1 _ _ _ _ _ _ Hc) as [[_ Heq] | Hc'];
        try discriminate;
        apply binds_In in Hc'; clear - Hβd Hc'; fsetdec.
    + apply a_rigid_only_cons_other; [ intros ->; apply Hne; reflexivity | ].
      apply IH.
      eapply a_rigid_only_strip_mid_other; [ | exact H ]; intros ->; apply Hne; reflexivity.
  - (* Assign-SkipTmVar *)
    intros Θ0 Θ1 Ξ α x A P Hx Ha IH γ H.
    apply a_rigid_only_cons_nonsuffix; [ intros Hs; inversion Hs | ].
    apply IH.
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact H ]; discriminate.
  - (* Assign-SkipTmSkl *)
    intros Θ0 Θ1 Ξ α x Q P Hx Ha IH γ H.
    apply a_rigid_only_cons_nonsuffix; [ intros Hs; inversion Hs | ].
    apply IH.
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact H ]; discriminate.
  - (* Flex-Flex-Id *)
    intros Θ0 α Hf γ H; exact H.
  - (* Flex-Flex-L *)
    intros Θ0 α β Hne Hf γ H.
    assert (Hγα : α <> γ).
    { intros ->. destruct H as [_ [Hnm _]].
      apply Hnm. unfold binds; simpl; auto. }
    apply a_rigid_only_cons_other; [ exact Hγα | ].
    eapply a_rigid_only_strip_head_other; [ exact Hγα | exact H ].
  - (* Flex-Flex-R *)
    intros Θ0 α β Hne Hf γ H.
    assert (Hγβ : β <> γ).
    { intros ->. destruct H as [_ [Hnm _]].
      apply Hnm. unfold binds; simpl; auto. }
    apply a_rigid_only_cons_other; [ exact Hγβ | ].
    eapply a_rigid_only_strip_head_other; [ exact Hγβ | exact H ].
  - (* Flex-Flex-Assign *)
    intros Θ0 Θ1 α1 τ α β Q Hfα Hfβ Hα1 Hc IH γ H.
    assert (Hγα1 : α1 <> γ).
    { intros ->. destruct H as [_ [_ Hnd]].
      eapply Hnd. unfold binds; simpl; eauto. }
    apply a_rigid_only_cons_other; [ exact Hγα1 | ].
    apply IH.
    eapply a_rigid_only_strip_head_other; [ exact Hγα1 | exact H ].
  - (* Flex-Flex-Skip *)
    intros Θ0 Θ1 α1 α β Hn1 Hn2 Hα1 Hu IH γ H.
    assert (Hγα1 : α1 <> γ).
    { intros ->. destruct H as [_ [Hnm _]].
      apply Hnm. unfold binds; simpl; auto. }
    apply a_rigid_only_cons_other; [ exact Hγα1 | ].
    apply IH.
    eapply a_rigid_only_strip_head_other; [ exact Hγα1 | exact H ].
  - (* Flex-Flex-Skip' (rigid or term entry) *)
    intros Θ0 Θ1 c b α β Hb Hcd Hu IH γ H.
    destruct (γ == c) as [-> | Hne].
    + destruct Hb as [-> | [[A ->] | [Q ->]]].
      * (* the walked entry is the rigid γ itself *)
        split; [ apply binds_app_2; unfold binds; simpl; auto | ].
        split;
          [ intros Hc | intros τ Hc ];
          destruct (binds_cons_1 _ _ _ _ _ _ Hc) as [[_ Heq] | Hc'];
          try discriminate;
          apply binds_In in Hc'; clear - Hcd Hc'; fsetdec.
      * apply a_rigid_only_cons_nonsuffix; [ intros Hs; inversion Hs | ].
        apply IH.
        eapply a_rigid_only_strip_head_nonrigid; [ | exact H ]; discriminate.
      * apply a_rigid_only_cons_nonsuffix; [ intros Hs; inversion Hs | ].
        apply IH.
        eapply a_rigid_only_strip_head_nonrigid; [ | exact H ]; discriminate.
    + apply a_rigid_only_cons_other; [ intros ->; apply Hne; reflexivity | ].
      apply IH.
      eapply a_rigid_only_strip_head_other; [ | exact H ]; intros ->; apply Hne; reflexivity.
  - (* C-Ghost *) intros; assumption.
  - (* C-Unit *) intros; assumption.
  - (* C-Rigid *) intros; assumption.
  - (* C-Arrow *) intros * Hc1 IH1 Hc2 IH2 γ H. apply IH2, IH1, H.
  - (* C-ForallInh *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH γ H.
    assert (Hγα : α <> γ).
    { pose proof (a_rigid_only_in_dom H) as Hd.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hsub.
      intros ->. clear - Hfr Hd Hsub. fsetdec. }
    eapply a_rigid_only_strip_head_other; [ exact Hγα | ].
    apply IH.
    apply a_rigid_only_cons_nonsuffix; [ intros Hs; inversion Hs | exact H ].
  - (* C-ForallSyn *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH γ H.
    assert (Hγα : α <> γ).
    { pose proof (a_rigid_only_in_dom H) as Hd.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hsub.
      intros ->. clear - Hfr Hd Hsub. fsetdec. }
    eapply a_rigid_only_strip_head_other; [ exact Hγα | ].
    apply IH.
    apply a_rigid_only_cons_nonsuffix; [ intros Hs; inversion Hs | exact H ].
  - (* C-UnivGhost *) intros * Hc IH γ H. apply IH, H.
  - (* C-UnivGhost1 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH γ H.
    assert (Hγα : α <> γ).
    { pose proof (a_rigid_only_in_dom H) as Hd.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hsub.
      intros ->. clear - Hfr Hd Hsub. fsetdec. }
    eapply a_rigid_only_strip_head_other; [ exact Hγα | ].
    apply IH.
    apply a_rigid_only_cons_nonsuffix; [ intros Hs; inversion Hs | exact H ].
  - (* C-UnivGhost2 *) intros * Hg Hnf Hc IH γ H. apply IH, H.
  - (* C-Flex *) intros Δ1 Δ2 Θ0 Θ1 α β Hu IH γ H. exact (IH γ H).
  - (* C-FlexL *) intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Ha IH γ H. exact (IH γ H).
  - (* C-FlexR *) intros Δ1 Δ2 Θ0 Θ1 α P Hnf Ha IH γ H. exact (IH γ H).
  - (* C-GhostR *) intros; assumption.
  - (* C-UnivGhostR *) intros * Hg Hnf Hc IH γ H. apply IH, H.
Qed.

Definition a_consis_rigid_only := proj2 (proj2 a_assign_unify_consis_rigid_only).

Lemma a_split_rigid_only : forall Θ0 P0 P Q Θ1,
  Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 ->
  forall γ, a_rigid_only Θ0 γ -> a_rigid_only Θ1 γ.
Proof.
  intros Θ0 P0 P Q Θ1 H; inversion H; subst; intros γ Hr;
    [ exact Hr | exact Hr | ].
  pose proof (a_rigid_only_in_dom Hr) as Hd.
  pose proof (dom_subset_ftvar_in_aenv Θ0) as Hsub.
  eapply a_consis_rigid_only; [ eassumption | ].
  apply a_rigid_only_cons_other; [ intros ->; clear - H1 Hd Hsub; fsetdec | ].
  apply a_rigid_only_cons_other; [ intros ->; clear - H0 Hd Hsub; fsetdec | ].
  exact Hr.
Qed.

Lemma a_sub_sub_flex_rigid_only :
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 ->
     forall γ, a_rigid_only Θ0 γ -> a_rigid_only Θ1 γ) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     forall γ, a_rigid_only (Ξ ++ Θ0) γ -> a_rigid_only Θ1 γ).
Proof.
  apply (a_sub_sub_flex_tm_mutind
           (fun NM M P0 Θ0 P Q Θ1 _ =>
              forall γ, a_rigid_only Θ0 γ -> a_rigid_only Θ1 γ)
           (fun NM M P0 Θ0 Ξ α Q Θ1 _ =>
              forall γ, a_rigid_only (Ξ ++ Θ0) γ -> a_rigid_only Θ1 γ)).
  - (* Infer *) intros; assumption.
  - (* Check *)
    intros Θ0 Θ1 A B Hgfa Hgfb Hga Hgb [Qc Hc] γ H.
    eapply a_consis_rigid_only; [ exact Hc | exact H ].
  - (* ForallR *)
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huq Hfr Hs IH γ H.
    pose proof (a_rigid_only_in_dom H) as Hd.
    assert (Hbig : a_rigid_only (Ξ ++ (α ~ abind_tvar) ++ Θ1) γ).
    { apply IH.
      apply a_rigid_only_cons_nonsuffix;
        [ intros Hb; inversion Hb | exact H ]. }
    apply a_rigid_only_strip_suffix in Hbig; [ | exact Hsuf ].
    eapply a_rigid_only_strip_head_other; [ | exact Hbig ].
    rewrite dom_app in Hfr. intros ->. clear - Hfr Hd. fsetdec.
  - (* UnivGhostR *) intros; assumption.
  - (* FlexMono *)
    intros * Hf IH γ H. apply IH. simpl. exact H.
  - (* Arrow *)
    intros * Hc Hs IH γ H.
    apply IH. eapply a_consis_rigid_only; [ exact Hc | exact H ].
  - (* ForallL *)
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hm Hgd Hfr Hex Huq HwfP1 Hs IH γ H.
    apply IH.
    apply a_rigid_only_weaken_app_fresh; [ | exact H ].
    eapply a_rigid_only_notin_prefix;
      [ exact Huq | apply a_rigid_only_in_dom; exact H ].
  - (* Ghost *) intros; assumption.
  - (* UnivGhostL *) intros * Hm Hs IH γ H. apply IH, H.
  - (* Flex-Solve *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hα Hβ Hs IH γ H.
    assert (Hγα0 : α0 <> γ).
    { intros ->. destruct H as [_ [Hnm _]].
      apply Hnm. apply binds_app_3. apply binds_app_2.
      unfold binds; simpl; auto. }
    assert (H' : a_rigid_only (Ξ ++ Θ0) γ)
      by (eapply a_rigid_only_strip_mid_nonrigid;
          [ | exact H ]; discriminate).
    pose proof (a_rigid_only_in_dom H') as Hd.
    apply IH.
    apply a_rigid_only_insert_mid; [ exact Hγα0 | ].
    apply a_rigid_only_insert_mid; [ intros ->; clear - Hβ Hd; fsetdec | ].
    apply a_rigid_only_insert_mid; [ intros ->; clear - Hα Hd; fsetdec | ].
    exact H'.
  - (* Flex-Assign *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβ Hs IH γ H.
    assert (Hγβ : β <> γ).
    { intros ->. destruct H as [_ [_ Hnd]].
      eapply Hnd. apply binds_app_3. apply binds_app_2.
      unfold binds; simpl; eauto. }
    apply a_rigid_only_cons_other; [ exact Hγβ | ].
    apply IH.
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact H ]; discriminate.
  - (* Flex-Depend *)
    intros * Hne Hβ Hf IH γ H.
    apply IH. rewrite app_assoc. exact H.
  - (* Flex-Skip *)
    intros * Hne Hβ Hβd Hf IH γ H.
    assert (Hγβ : β <> γ).
    { intros ->. destruct H as [_ [Hnm _]].
      apply Hnm. apply binds_app_3. apply binds_app_2.
      unfold binds; simpl; auto. }
    apply a_rigid_only_cons_other; [ exact Hγβ | ].
    apply IH.
    eapply a_rigid_only_strip_mid_other; [ exact Hγβ | exact H ].
  - (* Flex-SkipRigid *)
    intros * Hne Hβ Hβd Hf IH γ H.
    destruct (γ == β) as [-> | Hγβ].
    + split; [ apply binds_app_2; unfold binds; simpl; auto | ].
      split;
        [ intros Hc | intros τ Hc ];
        destruct (binds_cons_1 _ _ _ _ _ _ Hc) as [[_ Heq] | Hc'];
        try discriminate;
        apply binds_In in Hc'; clear - Hβd Hc'; fsetdec.
    + apply a_rigid_only_cons_other;
        [ intros ->; apply Hγβ; reflexivity | ].
      apply IH.
      eapply a_rigid_only_strip_mid_other; [ | exact H ]; intros ->; apply Hγβ; reflexivity.
  - (* Flex-SkipTmVar *)
    intros * H1 Hf IH γ H.
    apply a_rigid_only_cons_nonsuffix; [ intros Hb; inversion Hb | ].
    apply IH.
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact H ]; discriminate.
  - (* Flex-SkipTmSkl *)
    intros * H1 Hf IH γ H.
    apply a_rigid_only_cons_nonsuffix; [ intros Hb; inversion Hb | ].
    apply IH.
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact H ]; discriminate.
Qed.

Definition a_sub_rigid_only := proj1 a_sub_sub_flex_rigid_only.

Lemma a_pat_rigid_only : forall m Θ0 P0 e Q Θ1,
  Θ0 ⊢ₐ[ m ; P0 ] e ⇨ Q ⊣ Θ1 ->
  forall γ, a_rigid_only Θ0 γ -> a_rigid_only Θ1 γ.
Proof.
  intros m Θ0 P0 e Q Θ1 H; induction H; intros γ Hr.
  - (* unit *) eapply a_sub_rigid_only; eassumption.
  - (* var *) eapply a_sub_rigid_only; eassumption.
  - (* var_skl *) eapply a_sub_rigid_only; eassumption.
  - (* anno *) eapply a_sub_rigid_only; eassumption.
  - (* freeze *) apply IHa_pat, Hr.
  - (* abs *)
    destruct (atom_fresh L) as [x Hx].
    assert (Hr1 : a_rigid_only Θ1 γ)
      by (eapply a_split_rigid_only; [ eassumption | exact Hr ]).
    assert (Hbig : a_rigid_only (Ξ ++ (x ~ abind_var_skl P) ++ Θ2) γ).
    { match goal with
      | IHf : forall y, y `notin` _ -> forall δ, a_rigid_only _ δ -> a_rigid_only _ δ |- _ =>
          apply (IHf x Hx)
      end.
      apply a_rigid_only_cons_nonsuffix;
        [ intros Hb; inversion Hb | exact Hr1 ]. }
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact Hbig ]; discriminate.
  - (* abs_anno *)
    destruct (atom_fresh L) as [x Hx].
    assert (Hr1 : a_rigid_only Θ1 γ)
      by (eapply a_split_rigid_only; [ eassumption | exact Hr ]).
    destruct H1 as [Qc Hc].
    assert (Hr2 : a_rigid_only Θ2 γ)
      by (eapply a_consis_rigid_only; [ exact Hc | exact Hr1 ]).
    assert (Hbig : a_rigid_only (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) γ).
    { match goal with
      | IHf : forall y, y `notin` _ -> forall δ, a_rigid_only _ δ -> a_rigid_only _ δ |- _ =>
          apply (IHf x Hx)
      end.
      apply a_rigid_only_cons_nonsuffix;
        [ intros Hb; inversion Hb | exact Hr2 ]. }
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact Hbig ]; discriminate.
  - (* abs_check *)
    destruct (atom_fresh L) as [x Hx].
    assert (Hbig : a_rigid_only (Ξ ++ (x ~ abind_var_skl pskl_hole) ++ Θ1) γ).
    { match goal with
      | IHf : forall y, y `notin` _ -> forall δ, a_rigid_only _ δ -> a_rigid_only _ δ |- _ =>
          apply (IHf x Hx)
      end.
      apply a_rigid_only_cons_nonsuffix;
        [ intros Hb; inversion Hb | exact Hr ]. }
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact Hbig ]; discriminate.
  - (* abs_anno_check *)
    destruct (atom_fresh L) as [x Hx].
    assert (Hbig : a_rigid_only (Ξ ++ (x ~ abind_var_typ A) ++ Θ1) γ).
    { match goal with
      | IHf : forall y, y `notin` _ -> forall δ, a_rigid_only _ δ -> a_rigid_only _ δ |- _ =>
          apply (IHf x Hx)
      end.
      apply a_rigid_only_cons_nonsuffix;
        [ intros Hb; inversion Hb | exact Hr ]. }
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact Hbig ]; discriminate.
  - (* app *) apply IHa_pat2, IHa_pat1, Hr.
Qed.

Lemma a_typing_rigid_only : forall m Θ0 P0 e A Θ1,
  Θ0 ⊢ₐ[ m ; P0 ] e ⦂ A ⊣ Θ1 ->
  forall γ, a_rigid_only Θ0 γ -> a_rigid_only Θ1 γ.
Proof.
  intros m Θ0 P0 e A Θ1 H; induction H; intros γ Hr.
  - (* unit *) eapply a_sub_rigid_only; eassumption.
  - (* var *) eapply a_sub_rigid_only; eassumption.
  - (* anno *) eapply a_sub_rigid_only; [ eassumption | apply IHa_typing, Hr ].
  - (* freeze *)
    destruct H0 as [Qc Hc].
    eapply a_consis_rigid_only; [ exact Hc | apply IHa_typing, Hr ].
  - (* abs *)
    assert (Hr1 : a_rigid_only Θ1 γ)
      by (eapply a_split_rigid_only; [ eassumption | exact Hr ]).
    pose proof (a_rigid_only_in_dom Hr1) as Hd.
    assert (Hbig : a_rigid_only (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) γ).
    { apply IHa_typing.
      apply a_rigid_only_cons_nonsuffix; [ intros Hb; inversion Hb | ].
      apply a_rigid_only_weaken_app_fresh; [ | exact Hr1 ].
      eapply a_rigid_only_notin_prefix; [ exact H2 | exact Hd ]. }
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact Hbig ]; discriminate.
  - (* abs_anno *)
    assert (Hr1 : a_rigid_only Θ1 γ)
      by (eapply a_split_rigid_only; [ eassumption | exact Hr ]).
    destruct H1 as [Qc Hc].
    assert (Hr2 : a_rigid_only Θ2 γ)
      by (eapply a_consis_rigid_only; [ exact Hc | exact Hr1 ]).
    assert (Hbig : a_rigid_only (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) γ).
    { apply IHa_typing.
      apply a_rigid_only_cons_nonsuffix;
        [ intros Hb; inversion Hb | exact Hr2 ]. }
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact Hbig ]; discriminate.
  - (* abs_check_step — the rule's own α: γ ∈ dom Θ0 keeps them apart *)
    pose proof (a_rigid_only_in_dom Hr) as Hd.
    assert (Hbig : a_rigid_only (Ξ ++ (α ~ abind_tvar) ++ Θ1) γ).
    { apply IHa_typing.
      apply a_rigid_only_cons_nonsuffix;
        [ intros Hb; inversion Hb | exact Hr ]. }
    apply a_rigid_only_strip_suffix in Hbig; [ | assumption ].
    eapply a_rigid_only_strip_head_other; [ | exact Hbig ];
      intros ->; clear - H2 Hd; rewrite dom_app in H2; fsetdec.
  - (* abs_check_base *)
    assert (Hr1 : a_rigid_only Θ1 γ)
      by (eapply a_split_rigid_only; [ eassumption | exact Hr ]).
    assert (Hbig : a_rigid_only (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) γ).
    { apply IHa_typing.
      apply a_rigid_only_cons_nonsuffix;
        [ intros Hb; inversion Hb | exact Hr1 ]. }
    eapply a_rigid_only_strip_suffix; [ eassumption | ].
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact Hbig ]; discriminate.
  - (* abs_anno_check_step *)
    pose proof (a_rigid_only_in_dom Hr) as Hd.
    assert (Hbig : a_rigid_only (Ξ ++ (α ~ abind_tvar) ++ Θ1) γ).
    { apply IHa_typing.
      apply a_rigid_only_cons_nonsuffix;
        [ intros Hb; inversion Hb | exact Hr ]. }
    apply a_rigid_only_strip_suffix in Hbig; [ | assumption ].
    eapply a_rigid_only_strip_head_other; [ | exact Hbig ];
      intros ->; clear - H2 Hd; rewrite dom_app in H2; fsetdec.
  - (* abs_anno_check_base *)
    assert (Hr1 : a_rigid_only Θ1 γ)
      by (eapply a_split_rigid_only; [ eassumption | exact Hr ]).
    destruct H0 as [Qc Hc].
    assert (Hr2 : a_rigid_only Θ2 γ)
      by (eapply a_consis_rigid_only; [ exact Hc | exact Hr1 ]).
    assert (Hbig : a_rigid_only (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) γ).
    { apply IHa_typing.
      apply a_rigid_only_cons_nonsuffix;
        [ intros Hb; inversion Hb | exact Hr2 ]. }
    eapply a_rigid_only_strip_suffix; [ eassumption | ].
    eapply a_rigid_only_strip_mid_nonrigid; [ | exact Hbig ]; discriminate.
  - (* app *)
    apply IHa_typing2, IHa_typing1.
    eapply a_pat_rigid_only; [ eassumption | exact Hr ].
Qed.

(* ===================================================================== *)
(*  T4 cluster B — a run RETURNS its input's TC-core verbatim when that   *)
(*  core is rigid.  [AT-Anno]'s body premise demands exactly this: the    *)
(*  run at the annotation returns the annotation ITSELF.                   *)
(* ===================================================================== *)

(** The TC-core of a (mode, input skeleton) pair — the type the paper's
    metavariable sorting says a run at that mode must hand back.  No TI
    row: inference constrains nothing. *)
Inductive pskl_ty_core : mode -> pskl -> ptyp -> Prop :=
| pskl_ty_core__tc : forall A,
    pskl_ty_core mode_tc (ptyp_to_pskl A) A
| pskl_ty_core__fn : forall M P Q A,
    pskl_ty_core M Q A ->
    pskl_ty_core (mode_fn M) (pskl_arrow P Q) A.

(** …and of an output TYPE. *)
Inductive ptyp_ty_core : mode -> ptyp -> ptyp -> Prop :=
| ptyp_ty_core__tc : forall A,
    ptyp_ty_core mode_tc A A
| ptyp_ty_core__fn : forall M A B C,
    ptyp_ty_core M B C ->
    ptyp_ty_core (mode_fn M) (ptyp_arrow A B) C.

Lemma pskl_ty_core_ftv : forall M P C,
  pskl_ty_core M P C -> ftvar_in_ptyp C [<=] ftvar_in_pskl P.
Proof.
  intros M P C H; induction H; simpl.
  - rewrite ftvar_ptyp_to_pskl. fsetdec.
  - fsetdec.
Qed.

Lemma pskl_ty_core_of_painting : forall M A C,
  pskl_ty_core M (ptyp_to_pskl A) C -> ptyp_ty_core M A C.
Proof.
  intros M A C H.
  remember (ptyp_to_pskl A) as P eqn:HP.
  revert A HP; induction H; intros A0 HP.
  - apply ptyp_to_pskl_inj in HP. subst. apply ptyp_ty_core__tc.
  - destruct A0; simpl in HP; try discriminate.
    inversion HP; subst.
    apply ptyp_ty_core__fn. apply IHpskl_ty_core. reflexivity.
Qed.

(** Substitution leaves a core it does not mention in place. *)
Lemma pskl_ty_core_subst : forall M P C ψ β,
  pskl_ty_core M P C ->
  β `notin` ftvar_in_ptyp C ->
  pskl_ty_core M (subst_pskl_in_pskl ψ β P) C.
Proof.
  intros M P C ψ β H; induction H; intros Hβ; simpl.
  - rewrite subst_pskl_in_pskl_fresh_eq;
      [ apply pskl_ty_core__tc
      | rewrite ftvar_ptyp_to_pskl; exact Hβ ].
  - apply pskl_ty_core__fn. apply IHpskl_ty_core. exact Hβ.
Qed.

(** An assignment's target is flexible in the walk's context. *)
Lemma a_assign_flex_tvar : forall Θ Ξ α P Θ',
  a_assign Θ Ξ α P Θ' -> a_flex_tvar Θ α.
Proof.
  intros Θ Ξ α P Θ' H; induction H; unfold a_flex_tvar in *.
  - left. unfold binds; simpl; auto.
  - left. unfold binds; simpl; auto.
  - assumption.
  - destruct IHa_assign as [Hm | [τ' Hd]];
      [ left; apply binds_cons_3; exact Hm
      | right; exists τ'; apply binds_cons_3; exact Hd ].
  - destruct IHa_assign as [Hm | [τ' Hd]];
      [ left; apply binds_cons_3; exact Hm
      | right; exists τ'; apply binds_cons_3; exact Hd ].
  - destruct IHa_assign as [Hm | [τ' Hd]];
      [ left; apply binds_cons_3; exact Hm
      | right; exists τ'; apply binds_cons_3; exact Hd ].
  - destruct IHa_assign as [Hm | [τ' Hd]];
      [ left; apply binds_cons_3; exact Hm
      | right; exists τ'; apply binds_cons_3; exact Hd ].
  - destruct IHa_assign as [Hm | [τ' Hd]];
      [ left; apply binds_cons_3; exact Hm
      | right; exists τ'; apply binds_cons_3; exact Hd ].
Qed.

(** The flexible-split row cannot fire on a RIGID-only variable. *)
Lemma a_split_rigid_var_absurd : forall Θ0 α P Q Θ1,
  Θ0 ⊲ (pskl_var_f α) ▹ P ⇢ Q ⊣ Θ1 ->
  a_rigid_only Θ0 α ->
  False.
Proof.
  intros Θ0 α P Q Θ1 H Hr; inversion H; subst.
  pose proof (a_rigid_only_in_dom Hr) as Hd.
  pose proof (dom_subset_ftvar_in_aenv Θ0) as Hsub.
  match goal with
  | Hc : a_consis _ _ _ _ _ _ _ |- _ => inversion Hc; subst
  end.
  match goal with
  | Ha : a_assign _ _ _ _ _ |- _ =>
      pose proof (a_assign_flex_tvar Ha) as Hf
  end.
  unfold a_flex_tvar in Hf.
  destruct Hr as [_ [Hnm Hnd]].
  destruct Hf as [Hm | [τ' Hdd]].
  - destruct (binds_cons_1 _ _ _ _ _ _ Hm) as [[Heq _] | Hm'];
      [ subst;
        match goal with
        | Hfr : _ `notin` add _ _ |- _ => clear - Hfr Hd Hsub; fsetdec
        end | ].
    destruct (binds_cons_1 _ _ _ _ _ _ Hm') as [[Heq _] | Hm''];
      [ subst;
        match goal with
        | Hfr : _ `notin` ftvar_in_aenv _ |- _ => clear - Hfr Hd Hsub; fsetdec
        end | ].
    apply Hnm; exact Hm''.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hdd) as [[Heq _] | Hd'];
      [ subst;
        match goal with
        | Hfr : _ `notin` add _ _ |- _ => clear - Hfr Hd Hsub; fsetdec
        end | ].
    destruct (binds_cons_1 _ _ _ _ _ _ Hd') as [[Heq _] | Hd''];
      [ subst;
        match goal with
        | Hfr : _ `notin` ftvar_in_aenv _ |- _ => clear - Hfr Hd Hsub; fsetdec
        end | ].
    eapply Hnd; exact Hd''.
Qed.

(** The pointwise rigidity transports the core lemmas thread. *)
Definition core_rigid (Θ : aenv) (C : ptyp) : Prop :=
  forall α, α `in` ftvar_in_ptyp C -> a_rigid_only Θ α.

Lemma a_sub_sub_flex_ty_core :
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 ->
     NM = a_sub_mode_ty ->
     forall C, pskl_ty_core M P0 C ->
     core_rigid Θ0 C ->
     pskl_ty_core M Q C) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     NM = a_sub_mode_ty ->
     forall C, pskl_ty_core (mode_fn M) P0 C ->
     core_rigid (Ξ ++ Θ0) C ->
     pskl_ty_core (mode_fn M) Q C).
Proof.
  apply (a_sub_sub_flex_tm_mutind
           (fun NM M P0 Θ0 P Q Θ1 _ =>
              NM = a_sub_mode_ty ->
              forall C, pskl_ty_core M P0 C ->
              core_rigid Θ0 C ->
              pskl_ty_core M Q C)
           (fun NM M P0 Θ0 Ξ α Q Θ1 _ =>
              NM = a_sub_mode_ty ->
              forall C, pskl_ty_core (mode_fn M) P0 C ->
              core_rigid (Ξ ++ Θ0) C ->
              pskl_ty_core (mode_fn M) Q C)).
  - (* Infer : TI has no core *)
    intros NM P Θ0 Heq C Hcore Hr; inversion Hcore.
  - (* Check : output = input *)
    intros Θ0 Θ1 A B Hgfa Hgfb Hga Hgb Hc Heq C Hcore Hr; exact Hcore.
  - (* ForallR : output = input *)
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huq Hfr Hs IH Heq C Hcore Hr; exact Hcore.
  - (* UnivGhostR : SK *)
    intros Θ0 P Hg Heq; discriminate Heq.
  - (* FlexMono *)
    intros NM M P0 Θ0 Θ1 α Q Hf IH Heq C Hcore Hr.
    apply (IH Heq C Hcore). simpl. exact Hr.
  - (* Arrow : the core lives in the codomain *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH Heq C Hcore Hr.
    inversion Hcore; subst.
    apply pskl_ty_core__fn.
    match goal with
    | Hcore' : pskl_ty_core M P0b _ |- _ => apply (IH eq_refl _ Hcore')
    end.
    intros α Hα. eapply a_consis_rigid_only; [ exact Hc | ].
    apply Hr. exact Hα.
  - (* ForallL : same input, same mode *)
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hm Hgd Hfr Hex Huq HwfP1 Hs IH
           Heq C Hcore Hr.
    apply (IH Heq C Hcore).
    intros α' Hα'.
    apply a_rigid_only_weaken_app_fresh;
      [ eapply a_rigid_only_notin_prefix;
          [ exact Huq | apply a_rigid_only_in_dom; apply Hr; exact Hα' ]
      | apply Hr; exact Hα' ].
  - (* Ghost : SK *)
    intros M Θ0 P0 Heq; discriminate Heq.
  - (* UnivGhostL : SK *)
    intros M Θ0 Θ1 P0 P Q Hm Hs IH Heq; discriminate Heq.
  - (* Flex-Solve *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hα Hβ Hs IH Heq C Hcore Hr.
    apply (IH Heq C Hcore).
    intros α' Hα'.
    pose proof (Hr α' Hα') as Hro.
    assert (Hα'α0 : α0 <> α').
    { intros ->. destruct Hro as [_ [Hnm _]].
      apply Hnm. apply binds_app_3. apply binds_app_2.
      unfold binds; simpl; auto. }
    assert (Hro' : a_rigid_only (Ξ ++ Θ0) α')
      by (eapply a_rigid_only_strip_mid_nonrigid; [ | exact Hro ];
          discriminate).
    pose proof (a_rigid_only_in_dom Hro') as Hd.
    apply a_rigid_only_insert_mid; [ exact Hα'α0 | ].
    apply a_rigid_only_insert_mid; [ intros ->; clear - Hβ Hd; fsetdec | ].
    apply a_rigid_only_insert_mid; [ intros ->; clear - Hα Hd; fsetdec | ].
    exact Hro'.
  - (* Flex-Assign : the walked definition misses a rigid core *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβd Hs IH Heq C Hcore Hr.
    assert (HβC : β `notin` ftvar_in_ptyp C).
    { intros HβC. destruct (Hr β HβC) as [_ [_ Hnd]].
      eapply Hnd. apply binds_app_3. apply binds_app_2.
      unfold binds; simpl; eauto. }
    apply (IH Heq C (pskl_ty_core_subst _ Hcore HβC)).
    intros α' Hα'.
    pose proof (Hr α' Hα') as Hro.
    assert (Hα'β : β <> α').
    { intros ->. destruct Hro as [_ [_ Hnd]].
      eapply Hnd. apply binds_app_3. apply binds_app_2.
      unfold binds; simpl; eauto. }
    eapply a_rigid_only_strip_mid_other; [ exact Hα'β | exact Hro ].
  - (* Flex-Depend *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hβ Hf IH Heq C Hcore Hr.
    apply (IH Heq C Hcore).
    intros α' Hα'. rewrite app_assoc. apply Hr. exact Hα'.
  - (* Flex-Skip *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hβ Hβd Hf IH Heq C Hcore Hr.
    apply (IH Heq C Hcore).
    intros α' Hα'.
    pose proof (Hr α' Hα') as Hro.
    assert (Hα'β : β <> α').
    { intros ->. destruct Hro as [_ [Hnm _]].
      apply Hnm. apply binds_app_3. apply binds_app_2.
      unfold binds; simpl; auto. }
    eapply a_rigid_only_strip_mid_other; [ exact Hα'β | exact Hro ].
  - (* Flex-SkipRigid : the rule itself keeps the core away from β *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hβ Hβd Hf IH Heq C Hcore Hr.
    apply (IH Heq C Hcore).
    intros α' Hα'.
    assert (Hα'β : β <> α').
    { intros ->.
      pose proof (pskl_ty_core_ftv Hcore) as Hsub.
      clear - Hβ Hα' Hsub. fsetdec. }
    eapply a_rigid_only_strip_mid_other; [ exact Hα'β | ].
    apply Hr. exact Hα'.
  - (* Flex-SkipTmVar *)
    intros NM M P0 Θ0 Θ1 Ξ α x Apay Q Hxd Hf IH Heq C Hcore Hr.
    apply (IH Heq C Hcore).
    intros α' Hα'.
    eapply a_rigid_only_strip_mid_nonrigid; [ | apply Hr; exact Hα' ];
      discriminate.
  - (* Flex-SkipTmSkl *)
    intros NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hxd Hf IH Heq C Hcore Hr.
    apply (IH Heq C Hcore).
    intros α' Hα'.
    eapply a_rigid_only_strip_mid_nonrigid; [ | apply Hr; exact Hα' ];
      discriminate.
  Unshelve.
  all: exact ptyp_unit.
Qed.

Definition a_sub_ty_core := proj1 a_sub_sub_flex_ty_core.

Lemma a_typing_ty_core : forall M Θ0 P0 e A' Θ1,
  Θ0 ⊢ₐ[ M ; P0 ] e ⦂ A' ⊣ Θ1 ->
  forall C, pskl_ty_core M P0 C ->
  core_rigid Θ0 C ->
  ptyp_ty_core M A' C.
Proof.
  intros M Θ0 P0 e A' Θ1 H; induction H; intros C Hcore Hr.
  - (* AT-Unit *)
    apply pskl_ty_core_of_painting.
    eapply a_sub_ty_core; [ exact H | reflexivity | exact Hcore | exact Hr ].
  - (* AT-Var *)
    apply pskl_ty_core_of_painting.
    eapply a_sub_ty_core; [ exact H0 | reflexivity | exact Hcore | exact Hr ].
  - (* AT-Anno *)
    apply pskl_ty_core_of_painting.
    eapply a_sub_ty_core; [ exact H0 | reflexivity | exact Hcore | ].
    intros α Hα.
    eapply a_typing_rigid_only; [ exact H | apply Hr; exact Hα ].
  - (* AT-Freeze : output = the input type *)
    inversion Hcore; subst.
    match goal with
    | Heq : ptyp_to_pskl _ = ptyp_to_pskl _ |- _ =>
        apply ptyp_to_pskl_inj in Heq; subst
    end.
    apply ptyp_ty_core__tc.
  - (* AT-Abs *)
    inversion Hcore; subst; [ exfalso; apply H; reflexivity | ].
    match goal with
    | Hs : a_split _ (pskl_arrow _ _) _ _ _ |- _ =>
        inversion Hs; subst
    end.
    cbn [decr_mode] in *.
    apply ptyp_ty_core__fn.
    apply IHa_typing; [ assumption | ].
    intros α Hα.
    apply a_rigid_only_cons_nonsuffix; [ intros Hb; inversion Hb | ].
    apply a_rigid_only_weaken_app_fresh;
      [ eapply a_rigid_only_notin_prefix;
          [ eassumption
          | apply a_rigid_only_in_dom; apply Hr; exact Hα ]
      | apply Hr; exact Hα ].
  - (* AT-AbsAnno *)
    inversion Hcore; subst; [ exfalso; apply H; reflexivity | ].
    match goal with
    | Hs : a_split _ (pskl_arrow _ _) _ _ _ |- _ =>
        inversion Hs; subst
    end.
    cbn [decr_mode] in *.
    apply ptyp_ty_core__fn.
    destruct H1 as [Qc Hc].
    apply IHa_typing; [ assumption | ].
    intros α Hα.
    apply a_rigid_only_cons_nonsuffix; [ intros Hb; inversion Hb | ].
    eapply a_consis_rigid_only; [ exact Hc | apply Hr; exact Hα ].
  - (* AT-AbsCheckStep : the rule's own α; the body IH pins A = A0 *)
    inversion Hcore; subst.
    match goal with
    | Heq : ptyp_to_pskl ?CC = pskl_all_syn _ |- _ =>
        destruct CC as [ | | | | C0 ]; simpl in Heq; try discriminate;
        inversion Heq as [Heq0];
        apply ptyp_to_pskl_inj in Heq0; subst
    end.
    assert (Hbody : ptyp_ty_core mode_tc
                      (open_ptyp_wrt_ptyp A (ptyp_var_f α))
                      (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))).
    { apply IHa_typing; [ apply pskl_ty_core__tc | ].
      intros β' Hβ'.
      pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A0 (ptyp_var_f α))
        as Hup.
      simpl in Hup.
      destruct (β' == α) as [-> | Hne].
      - split; [ unfold binds; simpl; auto | ].
        split;
          [ intros Hcb | intros τ Hcb ];
          destruct (binds_cons_1 _ _ _ _ _ _ Hcb) as [[_ Heqb] | Hcb'];
          try discriminate;
          apply binds_In in Hcb'; clear - H2 Hcb';
          rewrite dom_app in H2; fsetdec.
      - apply a_rigid_only_cons_nonsuffix; [ intros Hb; inversion Hb | ].
        apply Hr. simpl. clear - Hβ' Hup Hne. fsetdec. }
    inversion Hbody; subst.
    match goal with
    | Heq : open_ptyp_wrt_ptyp _ _ = open_ptyp_wrt_ptyp _ _ |- _ =>
        apply open_ptyp_wrt_ptyp_inj in Heq;
          [ | clear - H2; fsetdec | clear - H2; fsetdec ]
    end.
    subst. apply ptyp_ty_core__tc.
  - (* AT-AbsCheckBase : the body IH pins B1 = the split codomain *)
    inversion Hcore; subst.
    match goal with
    | Heq : ptyp_to_pskl _ = ptyp_to_pskl _ |- _ =>
        apply ptyp_to_pskl_inj in Heq
    end.
    subst.
    match goal with
    | Hs : a_split _ (ptyp_to_pskl ?X) _ _ _ |- _ =>
        destruct X as [ | n | α | C1 C2 | C0 ]; simpl in Hs
    end.
    + inversion H.
    + inversion H.
    + exfalso.
      eapply a_split_rigid_var_absurd; [ exact H | ].
      apply Hr. simpl. clear; fsetdec.
    + inversion H; subst.
      repeat match goal with
      | Heq : ptyp_to_pskl _ = ptyp_to_pskl _ |- _ =>
          apply ptyp_to_pskl_inj in Heq
      end.
      subst.
      assert (Hbody : ptyp_ty_core mode_tc B1 B).
      { apply IHa_typing; [ apply pskl_ty_core__tc | ].
        intros β' Hβ'.
        apply a_rigid_only_cons_nonsuffix; [ intros Hb; inversion Hb | ].
        apply Hr. simpl. clear - Hβ'. fsetdec. }
      inversion Hbody; subst.
      apply ptyp_ty_core__tc.
    + inversion H.
  - (* AT-AbsAnnoCheckStep *)
    inversion Hcore; subst.
    match goal with
    | Heq : ptyp_to_pskl ?CC = pskl_all_syn _ |- _ =>
        destruct CC as [ | | | | C0 ]; simpl in Heq; try discriminate;
        inversion Heq as [Heq0];
        apply ptyp_to_pskl_inj in Heq0; subst
    end.
    assert (Hbody : ptyp_ty_core mode_tc
                      (open_ptyp_wrt_ptyp A (ptyp_var_f α))
                      (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))).
    { apply IHa_typing; [ apply pskl_ty_core__tc | ].
      intros β' Hβ'.
      pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A0 (ptyp_var_f α))
        as Hup.
      simpl in Hup.
      destruct (β' == α) as [-> | Hne].
      - split; [ unfold binds; simpl; auto | ].
        split;
          [ intros Hcb | intros τ Hcb ];
          destruct (binds_cons_1 _ _ _ _ _ _ Hcb) as [[_ Heqb] | Hcb'];
          try discriminate;
          apply binds_In in Hcb'; clear - H2 Hcb';
          rewrite dom_app in H2; fsetdec.
      - apply a_rigid_only_cons_nonsuffix; [ intros Hb; inversion Hb | ].
        apply Hr. simpl. clear - Hβ' Hup Hne. fsetdec. }
    inversion Hbody; subst.
    match goal with
    | Heq : open_ptyp_wrt_ptyp _ _ = open_ptyp_wrt_ptyp _ _ |- _ =>
        apply open_ptyp_wrt_ptyp_inj in Heq;
          [ | clear - H2; fsetdec | clear - H2; fsetdec ]
    end.
    subst. apply ptyp_ty_core__tc.
  - (* AT-AbsAnnoCheckBase *)
    inversion Hcore; subst.
    match goal with
    | Heq : ptyp_to_pskl _ = ptyp_to_pskl _ |- _ =>
        apply ptyp_to_pskl_inj in Heq
    end.
    subst.
    match goal with
    | Hs : a_split _ (ptyp_to_pskl ?X) _ _ _ |- _ =>
        destruct X as [ | n | α | C1 C2 | C0 ]; simpl in Hs
    end.
    + inversion H.
    + inversion H.
    + exfalso.
      eapply a_split_rigid_var_absurd; [ exact H | ].
      apply Hr. simpl. clear; fsetdec.
    + inversion H; subst.
      repeat match goal with
      | Heq : ptyp_to_pskl _ = ptyp_to_pskl _ |- _ =>
          apply ptyp_to_pskl_inj in Heq
      end.
      subst.
      destruct H0 as [Qc Hc].
      assert (Hbody : ptyp_ty_core mode_tc B1 B).
      { apply IHa_typing; [ apply pskl_ty_core__tc | ].
        intros β' Hβ'.
        apply a_rigid_only_cons_nonsuffix; [ intros Hb; inversion Hb | ].
        eapply a_consis_rigid_only; [ exact Hc | ].
        apply Hr. simpl. clear - Hβ'. fsetdec. }
      inversion Hbody; subst.
      apply ptyp_ty_core__tc.
    + inversion H.
  - (* AT-App *)
    assert (Hfn : ptyp_ty_core (mode_fn m) (ptyp_arrow A B) C).
    { apply IHa_typing1; [ apply pskl_ty_core__fn; exact Hcore | ].
      intros α Hα.
      eapply a_pat_rigid_only; [ exact H | apply Hr; exact Hα ]. }
    inversion Hfn; subst. assumption.
Qed.

(** ⭐ The consumer AT-Anno needs: a TC run at a RIGID-only type returns
    that type SYNTACTICALLY. *)
Lemma a_typing_tc_rigid_output : forall Θ0 (A : ptyp) e A' Θ1,
  Θ0 ⊢ₐ[ mode_tc ; (ptyp_to_pskl A) ] e ⦂ A' ⊣ Θ1 ->
  (forall α, α `in` ftvar_in_ptyp A -> a_rigid_only Θ0 α) ->
  A' = A.
Proof.
  intros Θ0 A e A' Θ1 H Hr.
  assert (Hc : ptyp_ty_core mode_tc A' A)
    by (eapply a_typing_ty_core;
        [ exact H | apply pskl_ty_core__tc | exact Hr ]).
  inversion Hc; subst; reflexivity.
Qed.

(* ===================================================================== *)
(*  T4-K1 — the TY sort discipline pays out: a TY-sorted run's OUTPUT is  *)
(*  ghost-free (given a ghost-free subject), so it IS a painted [ptyp]    *)
(*  ([pskl_ghost_free_to_ptyp]) and the [a_typing] rules' [⌈A⌉]-shaped    *)
(*  subtyping premises are satisfiable.                                    *)
(* ===================================================================== *)

(** Consistency: a ghost-free subject forces a ghost-free output (the
    ghost-subject rows cannot fire; every other row is structural or
    returns a variable). *)
Lemma a_consis_ghost_free_output : forall Δ1 Δ2 Θ0 P0 P Q Θ1,
  a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 ->
  pskl_ghost_free P ->
  pskl_ghost_free Q.
Proof.
  intros Δ1 Δ2 Θ0 P0 P Q Θ1 H; induction H; intros Hg; simpl in Hg;
    try contradiction; try exact I; auto.
  - (* arrow *) destruct Hg as [Hg1 Hg2]; split; auto.
  - (* forall_inh *)
    simpl. apply pskl_ghost_free_close.
    apply IHa_consis. apply pskl_ghost_free_open. exact Hg.
  - (* forall_syn *)
    simpl. apply pskl_ghost_free_close.
    apply IHa_consis. apply pskl_ghost_free_open. exact Hg.
Qed.

(** Subtyping at the TY sort, mutually with the flexible walk (whose
    re-entry subjects are all ghost-free by construction). *)
Lemma a_sub_ty_ghost_free_output_bundle :
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 ->
     NM = a_sub_mode_ty -> pskl_ghost_free P -> pskl_ghost_free Q) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     NM = a_sub_mode_ty -> pskl_ghost_free Q).
Proof.
  apply (a_sub_sub_flex_tm_mutind
           (fun NM M P0 Θ0 P Q Θ1 _ =>
              NM = a_sub_mode_ty -> pskl_ghost_free P -> pskl_ghost_free Q)
           (fun NM M P0 Θ0 Ξ α Q Θ1 _ =>
              NM = a_sub_mode_ty -> pskl_ghost_free Q));
    intros;
    (* the SK-only rows *)
    try match goal with
        | H : a_sub_mode_sk = a_sub_mode_ty |- _ => discriminate H
        end;
    (* Infer / Check / ForallR: the output's sort is a hypothesis *)
    try assumption;
    (* FlexMono + the five pass-through flex walks: a single-premise IH *)
    try match goal with
        | IH : _ = a_sub_mode_ty -> pskl_ghost_free _ |- _ =>
            apply IH; assumption
        end.
  - (* Arrow : domain by the consis companion, codomain by the IH *)
    match goal with
    | Hg : pskl_ghost_free (pskl_arrow _ _) |- _ => destruct Hg as [Hg1 Hg2]
    end.
    split.
    + match goal with
      | Hc : a_consis _ _ _ _ _ _ _ |- _ =>
          exact (a_consis_ghost_free_output Hc Hg1)
      end.
    + match goal with
      | IH : _ = _ -> pskl_ghost_free _ -> pskl_ghost_free _ |- _ =>
          apply IH; assumption
      end.
  - (* ForallL : the TY extraction is guess^TY, ghost-free by construction *)
    subst.
    match goal with
    | IH : _ = _ -> pskl_ghost_free _ -> pskl_ghost_free _ |- _ =>
        apply IH; [ reflexivity | ]
    end.
    apply pskl_ghost_free_open_gen;
      [ assumption
      | match goal with
        | Hex : a_extract _ _ _ _ _ _ _ _ |- _ =>
            exact (a_extract_ty_ghost_free Hex)
        end ].
  - (* Flex-Solve : the re-entry subject is an arrow of variables *)
    match goal with
    | IH : _ = _ -> pskl_ghost_free _ -> pskl_ghost_free _ |- _ =>
        apply IH; [ assumption | split; exact I ]
    end.
  - (* Flex-Assign : the re-entry subject is a substituted variable *)
    match goal with
    | IH : _ = _ -> pskl_ghost_free _ -> pskl_ghost_free _ |- _ =>
        apply IH; [ assumption | ]
    end.
    apply pskl_ghost_free_subst; [ exact I | apply ptyp_to_pskl_ghost_free ].
Qed.

Lemma a_sub_ty_ghost_free_output : forall M P0 Θ0 P Q Θ1,
  a_sub a_sub_mode_ty M P0 Θ0 P Q Θ1 ->
  pskl_ghost_free P ->
  pskl_ghost_free Q.
Proof.
  intros M P0 Θ0 P Q Θ1 H Hg.
  exact (proj1 a_sub_ty_ghost_free_output_bundle _ _ _ _ _ _ _ H eq_refl Hg).
Qed.

(* ===================================================================== *)
(*  T4-K2 — two coercion composites                                       *)
(* ===================================================================== *)

(** A [btyp]'s colour erasure is the embedding of its type erasure. *)
Lemma bskl_to_pskl_btyp : forall B,
  bskl_to_pskl (btyp_to_bskl B) = ptyp_to_pskl (btyp_to_ptyp B).
Proof. induction B; simpl; f_equal; auto. Qed.

(** The inherited painting of an embedded type is the [bskl] of its
    all-inh colouring. *)
Lemma pskl_to_bskl_inh_ptyp : forall A,
  pskl_to_bskl_inh (ptyp_to_pskl A) = btyp_to_bskl (ptyp_to_btyp_inh A).
Proof. induction A; simpl; f_equal; auto. Qed.

(* ⚙ THE FN-MODE OUTPUT SHAPE ([fn_arrow_shape_pskl] / [fn_arrow_shape],
   [a_sub_ty_fn_arrow_shape], [a_typing_fn_arrow_shape]) MOVED OUT 2026-08-09
   to algo/completeness_typing/prop_shape.v (cleanup audit §6).  It is a structural fact about
   arrow spines, not about rigidity or the TC-core, so it did not belong at the
   tail of this file.  completeness_typing/prop_typing.v — its only consumer — imports
   the new file directly. *)
