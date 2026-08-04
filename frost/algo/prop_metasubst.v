Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_inc_strengthen.
Set Implicit Arguments.

(* =====================================================================
   COMPLETENESS-SIDE METASUBSTITUTION THEORY

   The pure metasubst / a_inc_equiv / downarrow (⇓) / msubst-compose lemmas
   used by the optimality development.  Extracted from prop_consis_complete.v
   (which kept only the optimality defs, the consis<->metasubst bridge, and the
   theorem).  Imports NO consistency definitions (def_decl_algo/def_decorated),
   so the module graph enforces the layering:
     def_meta -> prop_inc/prop_compose/prop_normal -> prop_metasubst -> consis.
   ===================================================================== *)

(** Reflexivity of metasubstitution equivalence: every increment is
    equivalent to itself (each flexible image is [≡ᵗ]-reflexive). *)
Lemma a_inc_equiv_refl : forall Θ0 κ Θ,
  κ ∷ Θ0 ⊑ Θ ->
  a_inc_equiv Θ0 κ κ Θ.
Proof.
  intros Θ0 κ Θ H; induction H.
  - apply a_inc_equiv__empty; auto.
  - apply a_inc_equiv__flex; auto.
    apply a_tyequiv__refl. apply mono_ptyp_lc; auto.
  - apply a_inc_equiv__flex_def; auto.
    apply a_tyequiv__refl. apply mono_ptyp_lc; auto.
  - apply a_inc_equiv__var; auto.
  - apply a_inc_equiv__var_skl; auto.
  - apply a_inc_equiv__tvar; auto.
Qed.

(** [dom κ ⊆ dom Θ0] for any increment [κ ∷ Θ0 ⊑ Θ]. *)
Lemma a_inc_dom_sub : forall Θ0 κ Θ,
  κ ∷ Θ0 ⊑ Θ ->
  dom κ [<=] dom Θ0.
Proof.
  intros Θ0 κ Θ H α Hα.
  destruct (a_inc_dom_flex H Hα) as [Hb | [τ Hb]]; apply binds_In in Hb; exact Hb.
Qed.

(** Prepending an entry outside the RIGHT (identity) multiplicand's domain
    does not change the composition. *)
Lemma msubst_compose_cons_l_id : forall α τ ζ κ1,
  is_id_msubst κ1 ->
  α `notin` dom κ1 ->
  msubst_compose ((α, τ) :: ζ) κ1 = msubst_compose ζ κ1.
Proof.
  induction κ1 as [ | [β b] κ1' IH ]; intros Hid Hni; simpl; auto.
  apply is_id_msubst_inv in Hid as [Heq Hid']; subst.
  simpl in Hni. simpl.
  rewrite IH by (first [ exact Hid' | clear - Hni; fsetdec ]).
  destruct (β == α) as [->|Hne]; [ exfalso; clear - Hni; fsetdec | reflexivity ].
Qed.

(** When [κ1] is an IDENTITY increment on the same source, composing any
    increment [κ] with it on the right is the identity: [κ ∘ κ1 = κ] as
    lists.  Both increments track [Θ0]'s flexibles in the same order. *)
Lemma msubst_compose_is_id_r : forall Θ0 κ1 Θ1 κ Θ,
  a_wf_aenv Θ0 ->
  is_id_msubst κ1 ->
  κ1 ∷ Θ0 ⊑ Θ1 ->
  κ ∷ Θ0 ⊑ Θ ->
  msubst_compose κ κ1 = κ.
Proof.
  intros Θ0 κ1 Θ1 κ Θ Hwf Hid Hinc1 Hinc; revert κ1 Θ1 Hid Hinc1.
  induction Hinc; intros κ1 Θ1 Hid Hinc1.
  - (* source nil : κ1 = nil *)
    inversion Hinc1; subst. reflexivity.
  - (* flex α *)
    inversion Hwf as [ | αh Θh Hnd Hwa | | | | ]; subst.
    inversion Hinc1 as [ | Θa κa Θb αa τa Hi1 Hw1 Hm1 | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    simpl. destruct (α == α) as [_ | Hne]; [ | contradiction ].
    assert (Hnid : α `notin` dom κa)
      by (pose proof (a_inc_dom_sub Hi1) as Hs; clear - Hs Hnd; fsetdec).
    rewrite (msubst_compose_cons_l_id _ _ Hid' Hnid).
    rewrite (IHHinc Hwa _ _ Hid' Hi1). reflexivity.
  - (* flex_def α := τ *)
    inversion Hwf as [ | | αh τh Θh Hnd Hwp Hm Hwa | | | ]; subst.
    inversion Hinc1 as [ | | Θa κa Θb αa τd τa He1 Hw1 Hm1 Heq1 | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    simpl. destruct (α == α) as [_ | Hne]; [ | contradiction ].
    assert (Hnid : α `notin` dom κa)
      by (pose proof (a_inc_dom_sub He1) as Hs; clear - Hs Hnd; fsetdec).
    rewrite (msubst_compose_cons_l_id _ _ Hid' Hnid).
    rewrite (IHHinc Hwa _ _ Hid' He1). reflexivity.
  - (* var typ *)
    inversion Hwf as [ | | | | xh Ah Θh Hnd Hwp Hwa | ]; subst.
    inversion Hinc1 as [ | | | Θa κa Θb Ξa xa Aa Hi1 Hs1 | | ]; subst.
    eapply IHHinc; eauto.
  - (* var skl *)
    inversion Hwf as [ | | | xh Ph Θh Hnd Hwp Hwa | | ]; subst.
    inversion Hinc1 as [ | | | | Θa κa Θb Ξa xa Pa Hi1 Hs1 | ]; subst.
    eapply IHHinc; eauto.
  - (* tvar *)
    inversion Hwf as [ | | | | | αh Θh Hnd Hwa ]; subst.
    inversion Hinc1 as [ | | | | | Θa κa Θb Ξa αa Hi1 Hs1 ]; subst.
    eapply IHHinc; eauto.
Qed.

(** An IDENTITY increment is determined by its SOURCE alone: two id-increments
    out of the same [Θ0] are equal as lists (the target is irrelevant — every
    image is the identity, and both track [Θ0]'s flexibles in the same order).
    This is what lets a sub-node's soundness [⊴]-witness stand in for the
    algorithm's own id-witness on the walk cases. *)
Lemma is_id_inc_unique : forall Θ0 κ1 Θ1,
  κ1 ∷ Θ0 ⊑ Θ1 -> is_id_msubst κ1 ->
  forall κ2 Θ2, κ2 ∷ Θ0 ⊑ Θ2 -> is_id_msubst κ2 -> κ1 = κ2.
Proof.
  intros Θ0 κ1 Θ1 Hinc1; induction Hinc1; intros Hid1 κ2 Θ2 Hinc2 Hid2.
  - inversion Hinc2; subst; reflexivity.
  - apply is_id_msubst_inv in Hid1 as [Heq1 Hid1']; subst.
    inversion Hinc2 as [ | Θa κa Θb αa τa Hinca Hwfa Hma [Heqα Heqκ2] Heqt
                       | | | | ]; subst.
    apply is_id_msubst_inv in Hid2 as [Heq2 Hid2']; subst.
    f_equal. eapply IHHinc1; eauto.
  - apply is_id_msubst_inv in Hid1 as [Heq1 Hid1']; subst.
    inversion Hinc2 as [ | | Θa κa Θb αa τd τa Hinca Hwfa Hma Heqda [Heqα Heqκ2] Heqt
                       | | | ]; subst.
    apply is_id_msubst_inv in Hid2 as [Heq2 Hid2']; subst.
    f_equal. eapply IHHinc1; eauto.
  - inversion Hinc2 as [ | | | Θa κa Θb Ξa xa Aa Hinca Hsa Heqsrc Heqt | | ]; subst.
    eapply IHHinc1; eauto.
  - inversion Hinc2 as [ | | | | Θa κa Θb Ξa xa Pa Hinca Hsa Heqsrc Heqt | ]; subst.
    eapply IHHinc1; eauto.
  - inversion Hinc2 as [ | | | | | Θa κa Θb Ξa αa Hinca Hsa Heqsrc Heqt ]; subst.
    eapply IHHinc1; eauto.
Qed.

(** The complete AXIOM-node factoring: at a node that leaves the context
    unchanged ([Θ1 = Θ0]) the competing solution's own substitution [κ]
    serves as the factoring [ζ]. *)
Lemma opt_axiom_factor : forall Θ0 κ1 κ Θ,
  a_wf_aenv Θ0 ->
  is_id_msubst κ1 ->
  κ1 ∷ Θ0 ⊑ Θ0 ->
  κ ∷ Θ0 ⊑ Θ ->
  κ ∷ Θ0 ⊑ Θ /\ a_inc_equiv Θ0 κ (msubst_compose κ κ1) Θ.
Proof.
  intros Θ0 κ1 κ Θ Hwf Hid Hinc1 Hinc.
  split; [ exact Hinc | ].
  rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
  apply a_inc_equiv_refl; exact Hinc.
Qed.

(** Two equivalent metasubstitutions act [≡ᵗ]-equivalently on a wf MONOtype.
    (Monotypes have no [∀], so no binder/opening obligation arises — this is
    why the congruence below can stay first-order.) *)
Lemma a_inc_equiv_msubst_mono : forall Θmid κ1 κ2 Θ τ,
  a_inc_equiv Θmid κ1 κ2 Θ ->
  a_wf_aenv Θmid ->
  a_wf_ptyp Θmid τ ->
  mono_ptyp τ ->
  Θ ⊢ (msubst_ptyp κ1 τ) ≡ᵗ (msubst_ptyp κ2 τ).
Proof.
  intros Θmid κ1 κ2 Θ τ Hie Hwf Hwt Hm; revert Hwt; induction Hm; intros Hwt.
  - (* unit *) simpl. apply a_tyequiv__refl. constructor.
  - (* var α *) simpl. inversion Hwt; subst.
    eapply prop_normal.a_inc_equiv_lookup; [ exact Hie | exact Hwf | assumption ].
  - (* arrow A1 A2 *) simpl. inversion Hwt; subst.
    apply a_tyequiv__arrow; [ apply IHHm1 | apply IHHm2 ]; assumption.
Qed.

Lemma a_tyequiv_strengthen_tvar_cons : forall Θ0 A A',
  Θ0 ⊢ A ≡ᵗ A' ->
  forall α Θ, Θ0 = (α ~ abind_tvar) ++ Θ ->
  Θ ⊢ A ≡ᵗ A'.
Proof.
  intros Θ0 A A' Heq; induction Heq; intros α0 Θ0' HΘ; subst.
  - apply a_tyequiv__refl; assumption.
  - apply a_tyequiv__sym; eauto.
  - eapply a_tyequiv__trans; eauto.
  - apply a_tyequiv__flex_def.
    destruct (binds_cons_1 _ _ _ _ _ _ H) as [[Heqx Heqb] | Hb'];
      [ discriminate | exact Hb' ].
  - apply a_tyequiv__arrow; eauto.
  - apply a_tyequiv__all with (L := L); intros α Hα; eauto.
Qed.

Lemma a_pskl_tyequiv_strengthen_tvar_cons : forall Θ0 P P',
  Θ0 ⊢ P ≡ˢ P' ->
  forall α Θ, Θ0 = (α ~ abind_tvar) ++ Θ ->
  Θ ⊢ P ≡ˢ P'.
Proof.
  intros Θ0 P P' Heq; induction Heq; intros α0 Θ0' HΘ; subst.
  - apply a_pskl_tyequiv__refl; assumption.
  - apply a_pskl_tyequiv__sym; eauto.
  - eapply a_pskl_tyequiv__trans; eauto.
  - apply a_pskl_tyequiv__flex_def.
    destruct (binds_cons_1 _ _ _ _ _ _ H) as [[Heqx Heqb] | Hb'];
      [ discriminate | exact Hb' ].
  - apply a_pskl_tyequiv__arrow; eauto.
  - apply a_pskl_tyequiv__all with (L := L); intros α Hα; eauto.
  - apply a_pskl_tyequiv__tophole; eauto.
Qed.

(** An [a_inc]'s images are locally closed (they are monotypes). *)
Lemma a_inc_msubst_lc : forall Θ0 κ Θ,
  κ ∷ Θ0 ⊑ Θ -> msubst_lc κ.
Proof.
  intros Θ0 κ Θ Hinc α. apply mono_ptyp_lc.
  eapply a_inc_lookup_mono; exact Hinc.
Qed.

(** Identity metasubstitutions have locally-closed (variable) images. *)
Lemma is_id_msubst_values_lc : forall κ,
  is_id_msubst κ -> forall α τ, In (α, τ) κ -> lc_ptyp τ.
Proof.
  induction κ as [ | [β b] κ' IH ]; intros Hid α τ Hin; [ inversion Hin | ].
  apply is_id_msubst_inv in Hid as [Heq Hid']; subst.
  destruct Hin as [Heqe | Hin'].
  - inversion Heqe; subst. apply lc_ptyp_var_f.
  - exact (IH Hid' α τ Hin').
Qed.

(** Composition under a locally-closed metasubst is locally closed. *)
Lemma msubst_lc_compose : forall ζ κ,
  msubst_lc ζ ->
  (forall α τ, In (α, τ) κ -> lc_ptyp τ) ->
  msubst_lc (msubst_compose ζ κ).
Proof.
  intros ζ κ Hζ. unfold msubst_compose.
  induction κ as [ | [α τ] κ' IH ]; intros Hlc α0; simpl.
  - apply lc_ptyp_var_f.
  - destruct (α0 == α) as [-> | Hne].
    + apply msubst_ptyp_lc_lc; [ exact Hζ | apply (Hlc α τ); left; reflexivity ].
    + apply IH; [ intros a t Hin; apply (Hlc a t); right; exact Hin ].
Qed.

(** [msubst_pskl] commutes with opening under a locally-closed metasubst.
    (Local copies of [prop_consis_exist]'s lemmas, which cannot be imported
    here — that file imports this one.) *)
Lemma msubst_pskl_open_rec_lc_local : forall κ,
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
    apply lc_ptyp_to_pskl. apply Hlc.
Qed.

Lemma msubst_pskl_open_lc_local : forall κ P α,
  msubst_lc κ ->
  α `notin` dom κ ->
  msubst_pskl κ (open_pskl_wrt_pskl P (pskl_var_f α))
  = open_pskl_wrt_pskl (msubst_pskl κ P) (pskl_var_f α).
Proof.
  intros κ P α Hlc Hα. unfold open_pskl_wrt_pskl.
  rewrite (msubst_pskl_open_rec_lc_local Hlc P (pskl_var_f α) 0).
  cbn [msubst_pskl]. rewrite msubst_lookup_notin by exact Hα.
  reflexivity.
Qed.

(** The type lift of [a_inc_equiv_lookup] to arbitrary well-formed types. *)
Lemma a_inc_equiv_msubst_ptyp : forall A Θ0 κ1 κ2 Θ,
  a_wf_ptyp Θ0 A ->
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  a_wf_aenv Θ0 ->
  msubst_lc κ1 -> msubst_lc κ2 ->
  Θ ⊢ (msubst_ptyp κ1 A) ≡ᵗ (msubst_ptyp κ2 A).
Proof.
  intros A Θ0 κ1 κ2 Θ Hwf; revert κ1 κ2 Θ.
  induction Hwf as [ Θ0 | Θ0 α Hbt | Θ0 A1 A2 Hwf1 IH1 Hwf2 IH2 | L Θ0 A0 Hwf0 IH0 ];
    intros κ1 κ2 Θ Hie Hwf Hlc1 Hlc2; simpl.
  - apply a_tyequiv__refl; apply lc_ptyp_unit.
  - eapply prop_normal.a_inc_equiv_lookup; eauto.
  - apply a_tyequiv__arrow; [ apply IH1 | apply IH2 ]; auto.
  - apply a_tyequiv__all
      with (L := L `union` dom κ1 `union` dom κ2 `union` dom Θ0).
    intros α Hα.
    rewrite <- (msubst_ptyp_open_lc A0 Hlc1) by (clear - Hα; fsetdec).
    rewrite <- (msubst_ptyp_open_lc A0 Hlc2) by (clear - Hα; fsetdec).
    eapply a_tyequiv_strengthen_tvar_cons with (α := α) (Θ := Θ); [ | reflexivity ].
    apply IH0 with (α := α); [ clear - Hα; fsetdec | | | exact Hlc1 | exact Hlc2 ].
    + apply a_inc_equiv__tvar with (Ξ := (@nil (atom * abind)));
        [ exact Hie | apply a_suffix__nil ].
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ].
Qed.

(** The skeleton mirror. *)
Lemma a_inc_equiv_msubst_pskl : forall P Θ0 κ1 κ2 Θ,
  a_scope_pskl Θ0 P ->
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  a_wf_aenv Θ0 ->
  msubst_lc κ1 -> msubst_lc κ2 ->
  Θ ⊢ (msubst_pskl κ1 P) ≡ˢ (msubst_pskl κ2 P).
Proof.
  intros P Θ0 κ1 κ2 Θ Hwf; revert κ1 κ2 Θ.
  induction Hwf as [ Θ0 | Θ0 α Hbt | Θ0 P1 P2 Hwf1 IH1 Hwf2 IH2
                   | L Θ0 P0 Hwf0 IH0 | Θ0 | Θ0 P0 Hwf0 IH0 ];
    intros κ1 κ2 Θ Hie Hwf Hlc1 Hlc2; simpl.
  - apply a_pskl_tyequiv__refl; apply lc_pskl_unit.
  - apply a_tyequiv_pskl. eapply prop_normal.a_inc_equiv_lookup; eauto.
  - apply a_pskl_tyequiv__arrow; [ apply IH1 | apply IH2 ]; auto.
  - apply a_pskl_tyequiv__all
      with (L := L `union` dom κ1 `union` dom κ2 `union` dom Θ0).
    intros α Hα.
    rewrite <- (msubst_pskl_open_lc_local P0 Hlc1) by (clear - Hα; fsetdec).
    rewrite <- (msubst_pskl_open_lc_local P0 Hlc2) by (clear - Hα; fsetdec).
    eapply a_pskl_tyequiv_strengthen_tvar_cons with (α := α) (Θ := Θ); [ | reflexivity ].
    apply IH0 with (α := α); [ clear - Hα; fsetdec | | | exact Hlc1 | exact Hlc2 ].
    + apply a_inc_equiv__tvar with (Ξ := (@nil (atom * abind)));
        [ exact Hie | apply a_suffix__nil ].
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ].
  - apply a_pskl_tyequiv__refl; apply lc_pskl_hole.
  - apply a_pskl_tyequiv__tophole; apply IH0; auto.
Qed.

(** Composing with an IDENTITY increment on the right is invisible to
    [msubst] on a well-formed type/skeleton (every free variable is either
    a source flexible in [dom κ1] or a rigid untouched by [ζ]). *)
Lemma msubst_compose_id_ptyp : forall Θ0 κ1 Θ1 ζ Θ2 A,
  a_wf_aenv Θ0 -> a_wf_aenv Θ1 ->
  is_id_msubst κ1 ->
  κ1 ∷ Θ0 ⊑ Θ1 ->
  ζ ∷ Θ1 ⊑ Θ2 ->
  a_wf_ptyp Θ0 A ->
  msubst_ptyp (msubst_compose ζ κ1) A = msubst_ptyp ζ A.
Proof.
  intros Θ0 κ1 Θ1 ζ Θ2 A Hwf0 Hwf1 Hid Hinc1 Hζ HA.
  rewrite msubst_ptyp_compose;
    [ rewrite (msubst_ptyp_id (κ:=κ1) A Hid); reflexivity | ].
  intros α Hα.
  destruct (a_wf_ptyp_ftv_tvarish HA Hα) as [Hrig | [Hflex | [τ Hdef]]].
  - right. intros Hin.
    apply (a_inc_dom_flex Hζ) in Hin.
    assert (Hbt1 : binds α abind_tvar Θ1)
      by (eapply a_inc_binds_tvar; [ exact Hinc1 | exact Hrig ]).
    pose proof (a_wf_aenv_uniq Hwf1) as Hu.
    destruct Hin as [Hb | [τ Hb]];
      pose proof (binds_unique _ _ _ _ _ Hbt1 Hb Hu) as Hc; discriminate.
  - left. eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | left; exact Hflex ].
  - left. eapply a_inc_flex_dom;
      [ exact Hinc1 | exact Hwf0 | right; exists τ; exact Hdef ].
Qed.

Lemma msubst_compose_id_pskl : forall Θ0 κ1 Θ1 ζ Θ2 P,
  a_wf_aenv Θ0 -> a_wf_aenv Θ1 ->
  is_id_msubst κ1 ->
  κ1 ∷ Θ0 ⊑ Θ1 ->
  ζ ∷ Θ1 ⊑ Θ2 ->
  a_scope_pskl Θ0 P ->
  msubst_pskl (msubst_compose ζ κ1) P = msubst_pskl ζ P.
Proof.
  intros Θ0 κ1 Θ1 ζ Θ2 P Hwf0 Hwf1 Hid Hinc1 Hζ HP.
  rewrite msubst_pskl_compose;
    [ rewrite (msubst_pskl_id (κ:=κ1) P Hid); reflexivity | ].
  intros α Hα.
  destruct (a_scope_pskl_ftv_tvarish HP Hα) as [Hrig | [Hflex | [τ Hdef]]].
  - right. intros Hin.
    apply (a_inc_dom_flex Hζ) in Hin.
    assert (Hbt1 : binds α abind_tvar Θ1)
      by (eapply a_inc_binds_tvar; [ exact Hinc1 | exact Hrig ]).
    pose proof (a_wf_aenv_uniq Hwf1) as Hu.
    destruct Hin as [Hb | [τ Hb]];
      pose proof (binds_unique _ _ _ _ _ Hbt1 Hb Hu) as Hc; discriminate.
  - left. eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | left; exact Hflex ].
  - left. eapply a_inc_flex_dom;
      [ exact Hinc1 | exact Hwf0 | right; exists τ; exact Hdef ].
Qed.

(** The identity-increment through a NON-flexible middle strengthens
    directly: the competing target's suffix is forced empty (a suffix is
    all-flexible, but the head [c ~ b] here is a rigid / term binding). *)
Lemma a_inc_id_mid_strip : forall c b Θ0 κ1 Θ1,
  (b = abind_tvar \/
   (exists Q, b = abind_var_typ Q) \/ (exists Q, b = abind_var_skl Q)) ->
  κ1 ∷ ((c ~ b) ++ Θ0) ⊑ ((c ~ b) ++ Θ1) ->
  κ1 ∷ Θ0 ⊑ Θ1.
Proof.
  intros c b Θ0 κ1 Θ1 Hb Hinc.
  destruct Hb as [-> | [[Q ->] | [Q ->]]].
  - apply a_inc_tvar_inv in Hinc as [Ξ [Θ2 [Heq [HΞ Hinc']]]].
    destruct Ξ as [ | [α2 bz] Ξ' ]; simpl in Heq.
    + inversion Heq; subst. exact Hinc'.
    + inversion Heq; subst. inversion HΞ; subst.
      match goal with H : a_suffix_binding abind_tvar |- _ => inversion H end.
  - apply a_inc_var_inv in Hinc as [Ξ [A' [Θ2 [Heq [Heqv [HΞ Hinc']]]]]].
    destruct Ξ as [ | [α2 bz] Ξ' ]; simpl in Heq.
    + inversion Heq; subst. exact Hinc'.
    + inversion Heq; subst. inversion HΞ; subst.
      match goal with H : a_suffix_binding (abind_var_typ _) |- _ => inversion H end.
  - apply a_inc_var_skl_inv in Hinc as [Ξ [P' [Θ2 [Heq [Heqv [HΞ Hinc']]]]]].
    destruct Ξ as [ | [α2 bz] Ξ' ]; simpl in Heq.
    + inversion Heq; subst. exact Hinc'.
    + inversion Heq; subst. inversion HΞ; subst.
      match goal with H : a_suffix_binding (abind_var_skl _) |- _ => inversion H end.
Qed.

(** An [a_inc_equiv]'s metasubstitutions inherit the source's key
    distinctness (each flexible entry is source-fresh; the term/rigid
    entries leave the metasubstitution untouched). *)
Lemma a_inc_equiv_uniq_l : forall E κ σ Θ,
  a_inc_equiv E κ σ Θ -> uniq E -> uniq κ.
Proof.
  intros E κ σ Θ Hie; induction Hie; intros Hu; simpl in *.
  - constructor.
  - destruct_uniq. constructor; [ apply IHHie; solve_uniq | ].
    destruct (prop_normal.a_inc_equiv_dom Hie) as [Hd _]. fsetdec.
  - destruct_uniq. constructor; [ apply IHHie; solve_uniq | ].
    destruct (prop_normal.a_inc_equiv_dom Hie) as [Hd _]. fsetdec.
  - apply IHHie. solve_uniq.
  - apply IHHie. solve_uniq.
  - apply IHHie. solve_uniq.
Qed.

Lemma a_inc_equiv_uniq_r : forall E κ σ Θ,
  a_inc_equiv E κ σ Θ -> uniq E -> uniq σ.
Proof.
  intros E κ σ Θ Hie; induction Hie; intros Hu; simpl in *.
  - constructor.
  - destruct_uniq. constructor; [ apply IHHie; solve_uniq | ].
    destruct (prop_normal.a_inc_equiv_dom Hie) as [_ Hd]. fsetdec.
  - destruct_uniq. constructor; [ apply IHHie; solve_uniq | ].
    destruct (prop_normal.a_inc_equiv_dom Hie) as [_ Hd]. fsetdec.
  - apply IHHie. solve_uniq.
  - apply IHHie. solve_uniq.
  - apply IHHie. solve_uniq.
Qed.

(** A metasubstitution with empty domain is [nil] ([dom nil] on the RHS is
    cross-type-opaque to [fsetdec], hence the membership detour). *)
Lemma metasubst_dom_empty : forall (r : metasubst),
  dom r [=] empty -> r = nil.
Proof.
  destruct r as [ | [a t] r' ]; intros H; [ reflexivity | exfalso ].
  assert (Ha : a `in` dom ((a, t) :: r')) by (simpl; fsetdec).
  rewrite H in Ha. clear - Ha. fsetdec.
Qed.

Lemma a_inc_equiv_mid_insert_flex :
  forall Ξ β Θ0 Θ κ1 κ2 σ1 σ2 τ1 τ2,
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom κ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  Θ ⊢ τ1 ≡ᵗ τ2 ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ ->
  a_inc_equiv (Ξ ++ (β ~ abind_flex_mono) ++ Θ0)
              (κ1 ++ (β, τ1) :: κ2) (σ1 ++ (β, τ2) :: σ2) Θ.
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros β Θ0 Θ κ1 κ2 σ1 σ2 τ1 τ2 Hdec Huq Hdκ Hdσ Heqτ Hie.
  - rewrite dom_nil in Hdκ, Hdσ.
    apply metasubst_dom_empty in Hdκ; apply metasubst_dom_empty in Hdσ; subst.
    simpl in Hie |- *.
    apply a_inc_equiv__flex; [ exact Hie | exact Heqτ ].
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Huκ : uniq (κ1 ++ κ2))
      by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
    assert (Huσ : uniq (σ1 ++ σ2))
      by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
    assert (HaΞ : a `notin` dom Ξ') by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ Θ0)) by (clear - Huq; simpl_env in Huq; solve_uniq).
    destruct κ1 as [ | [ar tr] κ1' ];
      [ exfalso; rewrite dom_nil in Hdκ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ')) by (simpl; fsetdec);
        rewrite <- Hdκ in Hin; clear - Hin; fsetdec | ].
    destruct σ1 as [ | [asg ts] σ1' ];
      [ exfalso; rewrite dom_nil in Hdσ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ')) by (simpl; fsetdec);
        rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
    assert (Harκ : ar `notin` dom κ1') by (clear - Huκ; simpl_env in Huκ; solve_uniq).
    assert (Hasσ : asg `notin` dom σ1') by (clear - Huσ; simpl_env in Huσ; solve_uniq).
    simpl in Hie.
    inversion Hie as [ | R q1 q2 T aa u1 u2 Hie' Hequ | | | | ]; subst.
    simpl_env in Hdκ; simpl_env in Hdσ.
    simpl. apply a_inc_equiv__flex; [ | exact Hequ ].
    apply IH; auto.
    + clear - Hdκ Harκ HaΞ. simpl_env in *. fsetdec.
    + clear - Hdσ Hasσ HaΞ. simpl_env in *. fsetdec.
Qed.

(** Looking up a variable other than the mid-inserted key ignores that entry. *)
Lemma msubst_lookup_mid_drop : forall κa β τ κb α,
  α <> β ->
  msubst_lookup (κa ++ (β, τ) :: κb) α = msubst_lookup (κa ++ κb) α.
Proof.
  induction κa as [ | [a t] κa' IH ]; intros β τ κb α Hne; simpl.
  - destruct (α == β) as [-> | _]; [ contradiction | reflexivity ].
  - destruct (α == a) as [-> | _]; [ reflexivity | apply IH; exact Hne ].
Qed.

(** Composition distributes over an append of the RIGHT multiplicand. *)
Lemma msubst_compose_app : forall ζ κ1 κ2,
  msubst_compose ζ (κ1 ++ κ2) = msubst_compose ζ κ1 ++ msubst_compose ζ κ2.
Proof.
  intros ζ κ1 κ2. unfold msubst_compose.
  induction κ1 as [ | e κ1' IH ]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

(** Peel a declaration-only (all-flexible) PREFIX off a competing increment:
    the [Ξ]-part of [κ] has domain [dom Ξ] and the tail increment survives.
    (Mirror of [a_inc_mid_strip_flex] for a prefix rather than a mid.  This is
    the first step of the Assign-SkipRigid / SkipTmVar walk-case decomposition;
    the remaining wiring is blocked on the walked-past middle's competing
    suffix [Ξv] — see [remech-optimality-bundle-progress] memory.) *)
Lemma a_inc_strip_decls_prefix : forall Ξ E κ Θ,
  a_decls Ξ ->
  κ ∷ (Ξ ++ E) ⊑ Θ ->
  exists κ1 κ2, κ = κ1 ++ κ2 /\ dom κ1 [=] dom Ξ /\ κ2 ∷ E ⊑ Θ.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros E κ Θ Hdec Hinc.
  - exists (@nil (atom * ptyp)), κ. simpl.
    split; [ reflexivity | split; [ clear; fsetdec | exact Hinc ] ].
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heq HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θt αs τ Hinc' Hwfτ Hmτ [Heqα Heqκ] Heqt | | | | ];
      subst.
    destruct (IH E κs Θ Hdec' Hinc') as [κ1 [κ2 [Heqr [Hdom Hincr]]]].
    exists ((a, τ) :: κ1), κ2. simpl.
    split; [ rewrite Heqr; reflexivity
           | split; [ rewrite Hdom; clear; fsetdec | exact Hincr ] ].
Qed.

(* msubst preserves mono when every image is mono. *)
Lemma msubst_ptyp_mono_pointwise : forall ζ A,
  (forall β, mono_ptyp (msubst_lookup ζ β)) ->
  mono_ptyp A ->
  mono_ptyp (msubst_ptyp ζ A).
Proof.
  intros ζ A Himg Hm; induction Hm; simpl.
  - apply mono_ptyp__unit.
  - apply Himg.
  - apply mono_ptyp__arrow; auto.
Qed.

(* Every image of the downarrow metasubst is a monotype. *)
Lemma aenv_msubst_image_mono : forall Θ,
  a_wf_aenv Θ ->
  forall α0, mono_ptyp (msubst_lookup (aenv_msubst Θ) α0).
Proof.
  intros Θ Hwf; induction Hwf; intros α0; simpl.
  - apply mono_ptyp__var.
  - (* flex_mono β *) destruct (α0 == α) as [-> | Hne];
      [ apply mono_ptyp__var | apply IHHwf ].
  - (* flex_mono_def β ≔ τ *) destruct (α0 == α) as [-> | Hne].
    + apply msubst_ptyp_mono_pointwise; [ apply IHHwf | exact H1 ].
    + apply IHHwf.
  - (* var_skl *) apply IHHwf.
  - (* var_typ *) apply IHHwf.
  - (* tvar *) apply IHHwf.
Qed.

(* wf-preservation of msubst on a MONOTYPE (no ∀-case). *)
Lemma a_wf_ptyp_msubst_mono : forall Θ ζ A,
  mono_ptyp A -> a_wf_ptyp Θ A ->
  (forall β, a_binds_tvar β Θ -> a_wf_ptyp Θ (msubst_lookup ζ β)) ->
  a_wf_ptyp Θ (msubst_ptyp ζ A).
Proof.
  intros Θ ζ A Hm; induction Hm; intros Hwa Himg; simpl.
  - apply a_wf_ptyp__unit.
  - inversion Hwa; subst. apply Himg; assumption.
  - inversion Hwa; subst. apply a_wf_ptyp__arrow; auto.
Qed.

Ltac wk := eapply a_wf_ptyp_weaken;
  [ intros ? ? Hb; unfold binds; simpl; right; exact Hb | ].

(* Every downarrow image (of a type var of Θ) is wf in Θ. *)
Lemma aenv_msubst_image_wf : forall Θ,
  a_wf_aenv Θ ->
  forall β, a_binds_tvar β Θ ->
  a_wf_ptyp Θ (msubst_lookup (aenv_msubst Θ) β).
Proof.
  intros Θ Hwf; induction Hwf; intros β Hbt; simpl.
  - destruct Hbt as [Hb|[Hb|[t Hb]]]; inversion Hb.
  - (* flex_mono α *) destruct (β == α) as [-> | Hne].
    + apply a_wf_ptyp__var. right; left. unfold binds; left; reflexivity.
    + wk. apply IHHwf.
      destruct Hbt as [Hb|[Hb|[t Hb]]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He ?]|Hb'];
        try (exfalso; apply Hne; exact He);
        [ left | right;left | right;right;exists t ]; exact Hb'.
  - (* flex_mono_def α ≔ τ *) destruct (β == α) as [-> | Hne].
    + wk. apply a_wf_ptyp_msubst_mono; [ exact H1 | exact H0 | ].
      intros α2 Hz. apply IHHwf; exact Hz.
    + wk. apply IHHwf.
      destruct Hbt as [Hb|[Hb|[t Hb]]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He ?]|Hb'];
        try (exfalso; apply Hne; exact He);
        [ left | right;left | right;right;exists t ]; exact Hb'.
  - (* var_skl *) wk. apply IHHwf.
    destruct Hbt as [Hb|[Hb|[t Hb]]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He Hc]|Hb'];
      try discriminate; [ left | right;left | right;right;exists t ]; exact Hb'.
  - (* var_typ *) wk. apply IHHwf.
    destruct Hbt as [Hb|[Hb|[t Hb]]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He Hc]|Hb'];
      try discriminate; [ left | right;left | right;right;exists t ]; exact Hb'.
  - (* tvar α *) destruct (β == α) as [-> | Hne].
    + rewrite msubst_lookup_notin.
      * apply a_wf_ptyp__var. left. unfold binds; left; reflexivity.
      * pose proof (dom_aenv_msubst Θ). simpl.
        assert (α `notin` dom Θ) by exact H. clear - H0 H1. fsetdec.
    + wk. apply IHHwf.
      destruct Hbt as [Hb|[Hb|[t Hb]]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He ?]|Hb'];
        try (exfalso; apply Hne; exact He);
        [ left | right;left | right;right;exists t ]; exact Hb'.
Qed.

(* TOP-LEVEL downarrow preservation on a monotype. *)
Lemma mono_downarrow : forall Θ τ,
  a_wf_aenv Θ -> a_wf_ptyp Θ τ -> mono_ptyp τ ->
  mono_ptyp (⇓ᵗ[ Θ ] τ).
Proof.
  intros Θ τ Hwf Hwp Hm.
  apply msubst_ptyp_mono_pointwise; [ | exact Hm ].
  intros β. apply aenv_msubst_image_mono; exact Hwf.
Qed.

Lemma a_wf_ptyp_downarrow_mono : forall Θ τ,
  a_wf_aenv Θ -> a_wf_ptyp Θ τ -> mono_ptyp τ ->
  a_wf_ptyp Θ (⇓ᵗ[ Θ ] τ).
Proof.
  intros Θ τ Hwf Hwp Hm.
  apply a_wf_ptyp_msubst_mono; [ exact Hm | exact Hwp | ].
  intros β Hy. apply aenv_msubst_image_wf; assumption.
Qed.

Lemma msubst_ptyp_ftv : forall ζ A α',
  α' `in` ftvar_in_ptyp (msubst_ptyp ζ A) ->
  exists β, β `in` ftvar_in_ptyp A /\ α' `in` ftvar_in_ptyp (msubst_lookup ζ β).
Proof.
  intros ζ A; induction A as [ | n | α2 | A1 IHA1 A2 IHA2 | A0 IHA0 ];
    intros α' Hα; simpl in *.
  - clear - Hα; fsetdec.
  - clear - Hα; fsetdec.
  - exists α2. split; [ fsetdec | exact Hα ].
  - apply union_1 in Hα. destruct Hα as [H1 | H2].
    + destruct (IHA1 α' H1) as [β [HY1 HY2]]. exists β; split; [ fsetdec | exact HY2 ].
    + destruct (IHA2 α' H2) as [β [HY1 HY2]]. exists β; split; [ fsetdec | exact HY2 ].
  - destruct (IHA0 α' Hα) as [β [HY1 HY2]]. exists β; split; [ fsetdec | exact HY2 ].
Qed.

(* Every downarrow image of a var in a def-closed set D stays in D. *)
Lemma aenv_msubst_image_ftv_closed : forall Θ,
  a_wf_aenv Θ ->
  forall D,
  (forall α τ, binds α (abind_flex_mono_def τ) Θ -> α `in` D -> ftvar_in_ptyp τ [<=] D) ->
  forall α', α' `in` D ->
  ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) α') [<=] D.
Proof.
  intros Θ Hwf; induction Hwf; intros D Hcl α' HXD; simpl.
  - (* nil *) clear - HXD; fsetdec.
  - (* flex_mono α *) destruct (α' == α) as [-> | Hne].
    + simpl. clear - HXD; fsetdec.
    + apply IHHwf; [ | exact HXD ].
      intros β σ Hb Hβ. eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ].
  - (* flex_mono_def α ≔ τ *) destruct (α' == α) as [-> | Hne].
    + (* image = msubst (aenv_msubst Θ) τ ; ftv τ ⊆ D by closure *)
      assert (Hτ : ftvar_in_ptyp τ [<=] D)
        by (eapply Hcl; [ unfold binds; left; reflexivity | exact HXD ]).
      intros α2 Hα2.
      destruct (msubst_ptyp_ftv _ _ Hα2) as [β2 [HW1 HW2]].
      assert (HWD : β2 `in` D) by (clear - Hτ HW1; fsetdec).
      assert (Hsub : ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) β2) [<=] D).
      { apply IHHwf; [ | exact HWD ].
        intros β σ Hb Hβ. eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ]. }
      clear - HW2 Hsub. fsetdec.
    + apply IHHwf; [ | exact HXD ].
      intros β σ Hb Hβ. eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ].
  - (* var_skl *) apply IHHwf; [ | exact HXD ].
    intros β σ Hb Hβ.
    eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ].
  - (* var_typ *) apply IHHwf; [ | exact HXD ].
    intros β σ Hb Hβ.
    eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ].
  - (* tvar α *) destruct (α' == α) as [-> | Hne].
    + rewrite msubst_lookup_notin.
      * simpl. clear - HXD; fsetdec.
      * pose proof (dom_aenv_msubst Θ). assert (α `notin` dom Θ) by exact H.
        clear - H0 H1; fsetdec.
    + apply IHHwf; [ | exact HXD ].
      intros β σ Hb Hβ.
      eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ].
Qed.

Lemma downarrow_ftv_closed : forall Θ A D,
  a_wf_aenv Θ ->
  ftvar_in_ptyp A [<=] D ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ -> α `in` D -> ftvar_in_ptyp τ [<=] D) ->
  ftvar_in_ptyp (⇓ᵗ[ Θ ] A) [<=] D.
Proof.
  intros Θ A D Hwf HA Hcl α Hα.
  destruct (msubst_ptyp_ftv _ _ Hα) as [β [HY1 HY2]].
  assert (HYD : β `in` D) by (clear - HA HY1; fsetdec).
  eapply (aenv_msubst_image_ftv_closed Hwf Hcl HYD); exact HY2.
Qed.

Lemma a_binds_tvar_strengthen : forall α Θ Θ',
  a_binds_tvar α Θ -> uniq Θ ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  α `in` dom Θ' -> a_binds_tvar α Θ'.
Proof.
  intros α Θ Θ' Hbt Hu Hsub Hin.
  apply binds_In_inv in Hin as [b' Hb'].
  pose proof (Hsub _ _ Hb') as HbΘ.
  destruct Hbt as [Hb | [Hb | [τ Hb]]];
    pose proof (binds_unique _ _ _ _ _ HbΘ Hb Hu) as ->;
    [ left | right; left | right; right; exists τ ]; exact Hb'.
Qed.

Lemma binds_strengthen : forall (α:atom) (b:abind) (Θ Θ':aenv),
  binds α b Θ -> uniq Θ ->
  (forall x b0, binds x b0 Θ' -> binds x b0 Θ) ->
  α `in` dom Θ' -> binds α b Θ'.
Proof.
  intros α b Θ Θ' Hb Hu Hsub Hin.
  apply binds_In_inv in Hin as [b' Hb'].
  pose proof (Hsub _ _ Hb') as HbΘ.
  pose proof (binds_unique _ _ _ _ _ HbΘ Hb Hu) as ->. exact Hb'.
Qed.

Lemma binds_sub_cons : forall (e:aenv) Θ Θ',
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  forall x b, binds x b (e ++ Θ') -> binds x b (e ++ Θ).
Proof.
  intros e Θ Θ' Hsub x b Hb.
  apply binds_app_1 in Hb. destruct Hb as [H1 | H2];
    [ apply binds_app_2 | apply binds_app_3; apply Hsub ]; assumption.
Qed.

(** A unique middle binding forces the two flanking decompositions to agree
    (Metalib [uniq_mid], spelled with explicit arguments). *)
Lemma aenv_mid_split : forall (E1 : aenv) x b1 F1 E2 b2 F2,
  uniq (E1 ++ (x ~ b1) ++ F1) ->
  E1 ++ (x ~ b1) ++ F1 = E2 ++ (x ~ b2) ++ F2 ->
  E1 = E2 /\ b1 = b2 /\ F1 = F2.
Proof.
  intros E1 x b1 F1 E2 b2 F2 Hu Heq.
  eapply uniq_mid; eauto.
Qed.

(** Head inversions for [a_inc_equiv] at the three binder entries: they carry
    [κ1]/[κ2] over unchanged and split the target at a suffix. *)
Lemma a_inc_equiv_tvar_inv : forall α Θ0 κ1 κ2 Θ,
  a_inc_equiv ((α ~ abind_tvar) ++ Θ0) κ1 κ2 Θ ->
  exists Ξ Θ', Θ = Ξ ++ (α ~ abind_tvar) ++ Θ'
             /\ a_suffix Ξ /\ a_inc_equiv Θ0 κ1 κ2 Θ'.
Proof. intros * H; inversion H; subst; eauto 8. Qed.

Lemma a_inc_equiv_var_typ_inv : forall x A Θ0 κ1 κ2 Θ,
  a_inc_equiv ((x ~ abind_var_typ A) ++ Θ0) κ1 κ2 Θ ->
  exists Ξ A' Θ', Θ = Ξ ++ (x ~ abind_var_typ A') ++ Θ'
             /\ (Θ' ⊢ A' ≡ᵗ (msubst_ptyp κ1 A))
             /\ a_suffix Ξ /\ a_inc_equiv Θ0 κ1 κ2 Θ'.
Proof. intros * H; inversion H; subst; eauto 10. Qed.

Lemma a_inc_equiv_var_skl_inv : forall x P Θ0 κ1 κ2 Θ,
  a_inc_equiv ((x ~ abind_var_skl P) ++ Θ0) κ1 κ2 Θ ->
  exists Ξ P' Θ', Θ = Ξ ++ (x ~ abind_var_skl P') ++ Θ'
             /\ (Θ' ⊢ P' ≡ˢ (msubst_pskl κ1 P))
             /\ a_suffix Ξ /\ a_inc_equiv Θ0 κ1 κ2 Θ'.
Proof. intros * H; inversion H; subst; eauto 10. Qed.

(** An all-flexible source maps, under [a_inc_equiv], to an all-flexible target
    (mirror of [a_inc_suffix_target]). *)
Lemma a_inc_equiv_suffix_target : forall Θ κ1 κ2 Θ',
  a_inc_equiv Θ κ1 κ2 Θ' -> a_suffix Θ -> a_suffix Θ'.
Proof.
  intros Θ κ1 κ2 Θ' Hie; induction Hie; intros Hsuf; auto;
    inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst; auto; inversion Hb.
Qed.

(** Peel an all-flexible suffix [Ξ] off the source of an [a_inc_equiv] and its
    two witnessing increments simultaneously — the three list-heads coincide
    (one shared [κ1]/[κ2]), so the splits stay consistent for free.  Mirrors
    [a_inc_peel_suffix] (prop_compose.v:629) + [a_inc_strengthen_suffix_src]. *)
Lemma a_inc_equiv_inc_peel_suffix : forall Ξ Θ κ1 κ2 Θ',
  a_suffix Ξ ->
  a_inc_equiv (Ξ ++ Θ) κ1 κ2 Θ' ->
  κ1 ∷ (Ξ ++ Θ) ⊑ Θ' ->
  κ2 ∷ (Ξ ++ Θ) ⊑ Θ' ->
  exists κ1b κ2b,
    a_inc_equiv Θ κ1b κ2b Θ' /\ κ1b ∷ Θ ⊑ Θ' /\ κ2b ∷ Θ ⊑ Θ'
    /\ (exists p1, κ1 = p1 ++ κ1b /\ dom p1 [=] dom Ξ)
    /\ (exists p2, κ2 = p2 ++ κ2b /\ dom p2 [=] dom Ξ).
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ]; intros Θ κ1 κ2 Θ' Hsuf Hie Hi1 Hi2.
  - simpl in *. exists κ1, κ2.
    repeat split; auto;
      [ exists (@nil (atom * ptyp)) | exists (@nil (atom * ptyp)) ];
      simpl; split; solve [ reflexivity | clear; fsetdec ].
  - inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst.
    inversion Hb; subst; simpl in Hie, Hi1, Hi2.
    + (* flex_mono head *)
      inversion Hie as [ | R t1 t2 T aa u1 u2 Hie' Heq | | | | ]; subst.
      inversion Hi1; subst. inversion Hi2; subst.
      match goal with H : a_inc (Ξ' ++ Θ) t1 Θ' |- _ => rename H into Hi1' end.
      match goal with H : a_inc (Ξ' ++ Θ) t2 Θ' |- _ => rename H into Hi2' end.
      destruct (IH _ _ _ _ Hsuf' Hie' Hi1' Hi2')
        as [κ1b [κ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hd1]] [p2 [Hp2 Hd2]]]]]]]].
      exists κ1b, κ2b. repeat split; auto.
      * exists ((a, u1) :: p1). rewrite Hp1. simpl.
        split; [ reflexivity | rewrite Hd1; clear; fsetdec ].
      * exists ((a, u2) :: p2). rewrite Hp2. simpl.
        split; [ reflexivity | rewrite Hd2; clear; fsetdec ].
    + (* flex_mono_def head *)
      inversion Hie as [ | | R t1 t2 T aa td u1 u2 Hie' Heq Hdf | | | ]; subst.
      inversion Hi1; subst. inversion Hi2; subst.
      match goal with H : a_inc (Ξ' ++ Θ) t1 Θ' |- _ => rename H into Hi1' end.
      match goal with H : a_inc (Ξ' ++ Θ) t2 Θ' |- _ => rename H into Hi2' end.
      destruct (IH _ _ _ _ Hsuf' Hie' Hi1' Hi2')
        as [κ1b [κ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hd1]] [p2 [Hp2 Hd2]]]]]]]].
      exists κ1b, κ2b. repeat split; auto.
      * exists ((a, u1) :: p1). rewrite Hp1. simpl.
        split; [ reflexivity | rewrite Hd1; clear; fsetdec ].
      * exists ((a, u2) :: p2). rewrite Hp2. simpl.
        split; [ reflexivity | rewrite Hd2; clear; fsetdec ].
Qed.

(** TRANSITIVITY of metasubstitution equivalence (through a fixed target).
    The [var]/[var_skl] cases use [aenv_mid_split] to realign the two
    target decompositions at the unique term-variable position. *)
Lemma a_inc_equiv_trans : forall Θ0 κa κb Θ,
  a_inc_equiv Θ0 κa κb Θ ->
  forall κc,
  a_wf_aenv Θ ->
  a_inc_equiv Θ0 κb κc Θ ->
  a_inc_equiv Θ0 κa κc Θ.
Proof.
  intros Θ0 κa κb Θ Hab; induction Hab; intros κc Hwf Hbc.
  - (* empty *)
    inversion Hbc; subst. apply a_inc_equiv__empty; auto.
  - (* flex α *)
    match goal with He : _ ⊢ _ ≡ᵗ _ |- _ => rename He into Hab_eq end.
    inversion Hbc as [ | Rb tb tc Tb ac t2b t3 Hbc' Heqc | | | | ]; subst.
    apply a_inc_equiv__flex.
    + apply IHHab; auto.
    + eapply a_tyequiv__trans; [ exact Hab_eq | exact Heqc ].
  - (* flex_def α := τ *)
    match goal with Hd : _ ⊢ _ ≡ᵗ (msubst_ptyp _ _) |- _ => rename Hd into Hab_def end.
    match goal with He : _ ⊢ _ ≡ᵗ _ |- _ =>
      lazymatch type of He with
      | _ ⊢ _ ≡ᵗ (msubst_ptyp _ _) => fail
      | _ => rename He into Hab_eq
      end end.
    inversion Hbc as [ | | Rb tb tc Tb ac td t2b t3 Hbc' Heqc Hdefc | | | ]; subst.
    apply a_inc_equiv__flex_def.
    + apply IHHab; auto.
    + eapply a_tyequiv__trans; [ exact Hab_eq | exact Heqc ].
    + exact Hab_def.
  - (* var_typ x : realign, then rebuild (the first equivalence's semantic
       middle premise is reused verbatim) *)
    destruct (a_inc_equiv_var_typ_inv Hbc)
      as [Xic [Ac' [Tc [Heqt [Heqvc [Hsc Hrec]]]]]].
    pose proof (a_wf_aenv_uniq_local Hwf) as Hu.
    destruct (aenv_mid_split _ _ _ _ _ _ _ Hu Heqt) as [HeqΞ [Heqb HeqΘ]].
    injection Heqb as HeqA. subst.
    apply a_wf_aenv_strip_prefix_local in Hwf.
    inversion Hwf; subst.
    apply a_inc_equiv__var;
      [ apply IHHab; assumption | assumption | assumption ].
  - (* var_skl x *)
    destruct (a_inc_equiv_var_skl_inv Hbc)
      as [Xic [Pc' [Tc [Heqt [Heqvc [Hsc Hrec]]]]]].
    pose proof (a_wf_aenv_uniq_local Hwf) as Hu.
    destruct (aenv_mid_split _ _ _ _ _ _ _ Hu Heqt) as [HeqΞ [Heqb HeqΘ]].
    injection Heqb as HeqP. subst.
    apply a_wf_aenv_strip_prefix_local in Hwf.
    inversion Hwf; subst.
    apply a_inc_equiv__var_skl;
      [ apply IHHab; assumption | assumption | assumption ].
  - (* tvar α *)
    destruct (a_inc_equiv_tvar_inv Hbc) as [Xic [Tc [Heqt [Hsc Hrec]]]].
    pose proof (a_wf_aenv_uniq_local Hwf) as Hu.
    destruct (aenv_mid_split _ _ _ _ _ _ _ Hu Heqt) as [HeqΞ [Heqb HeqΘ]].
    subst.
    apply a_wf_aenv_strip_prefix_local in Hwf.
    inversion Hwf; subst.
    apply a_inc_equiv__tvar; [ apply IHHab; assumption | assumption ].
Qed.

(** RIGHT-COMPOSITION CONGRUENCE: applying a fixed source-increment [σ] to two
    equivalent metasubstitutions preserves the equivalence.  Induction on [σ],
    mirroring [a_inc_compose] (prop_compose.v:695); the binder cases peel the
    suffix off the [a_inc_equiv] and its two witnessing increments together
    ([a_inc_equiv_inc_peel_suffix]) and realign the three target
    decompositions at the unique term-variable via [aenv_mid_split]. *)
Lemma a_inc_equiv_compose : forall Θ0 κ Θmid,
  κ ∷ Θ0 ⊑ Θmid ->
  a_wf_aenv Θ0 -> a_wf_aenv Θmid ->
  forall κ1 κ2 Θ,
  a_wf_aenv Θ ->
  a_inc_equiv Θmid κ1 κ2 Θ ->
  κ1 ∷ Θmid ⊑ Θ -> κ2 ∷ Θmid ⊑ Θ ->
  a_inc_equiv Θ0 (msubst_compose κ1 κ) (msubst_compose κ2 κ) Θ.
Proof.
  intros Θ0 κ Θmid Hκ; induction Hκ;
    intros Hwf0 Hwf1 κ1 κ2 Θt HwfT Hie Hi1 Hi2.
  - (* empty : source all-flexible, so target all-flexible *)
    simpl. apply a_inc_equiv__empty.
    eapply a_inc_equiv_suffix_target; [ exact Hie | assumption ].
  - (* flex α *)
    inversion Hwf0 as [ | αh Θh Hnd Hwa | | | | ]; subst.
    simpl. apply a_inc_equiv__flex.
    + apply IHHκ; auto.
    + eapply a_inc_equiv_msubst_mono;
        [ exact Hie | exact Hwf1 | eassumption | assumption ].
  - (* flex_def α := τ *)
    inversion Hwf0 as [ | | αh τh Θh Hnd Hwp Hm Hwa | | | ]; subst.
    simpl. apply a_inc_equiv__flex_def.
    + apply IHHκ; auto.
    + eapply a_inc_equiv_msubst_mono;
        [ exact Hie | exact Hwf1 | eassumption | assumption ].
    + rewrite msubst_ptyp_compose.
      * eapply a_tyequiv_msubst; [ eassumption | exact Hwf1 | exact Hi1 ].
      * intros α0 Hα0.
        eapply a_inc_compose_vis;
          [ exact Hκ | exact Hi1 | exact Hwa | exact Hwf1
          | eapply a_wf_ptyp_ftv_tvarish; eauto ].
  - (* var_typ x *)
    inversion Hwf0 as [ | | | | xh Ah Θh Hnd Hwp Hwa | ]; subst.
    assert (Hwf1t : a_wf_aenv Θ') by
      (apply a_wf_aenv_strip_prefix_local in Hwf1;
       inversion Hwf1; subst; assumption).
    assert (Hdisj : forall α0, α0 `in` dom Ξ -> α0 `notin` dom Θ').
    { intros α0 Hα0. pose proof (a_wf_aenv_uniq_local Hwf1) as Hu1.
      clear - Hu1 Hα0. solve_uniq. }
    edestruct a_inc_equiv_inc_peel_suffix
      as [κ1b [κ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hdp1]] [p2 [Hp2 Hdp2]]]]]]]];
      [ exact H0 | exact Hie | exact Hi1 | exact Hi2 | ].
    destruct (a_inc_equiv_var_typ_inv Hie2)
      as [Ξe [Ae' [Te [Heqe [Heqve [Hse Hie3]]]]]].
    destruct (a_inc_var_inv Hib1) as [Ξ1 [A1' [T1 [Heq1 [Heqv1 [Hs1 Hib1']]]]]].
    destruct (a_inc_var_inv Hib2) as [Ξ2 [A2' [T2 [Heq2 [Heqv2 [Hs2 Hib2']]]]]].
    pose proof (a_wf_aenv_uniq_local HwfT) as HuT.
    rewrite Heqe in HuT.
    assert (HeqE1 : Ξe ++ (x ~ abind_var_typ Ae') ++ Te
                  = Ξ1 ++ (x ~ abind_var_typ A1') ++ T1)
      by (rewrite <- Heqe; exact Heq1).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE1) as [HE1 [HB1 HT1]].
    injection HB1 as HB1. subst A1' T1.
    assert (HeqE2 : Ξe ++ (x ~ abind_var_typ Ae') ++ Te
                  = Ξ2 ++ (x ~ abind_var_typ A2') ++ T2)
      by (rewrite <- Heqe; exact Heq2).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE2) as [HE2 [HB2 HT2]].
    injection HB2 as HB2. subst A2' T2.
    assert (Hc1 : msubst_compose κ1 κ = msubst_compose κ1b κ)
      by (rewrite Hp1; eapply msubst_compose_peel;
          [ exact Hκ | intros α0 Hα0; apply Hdisj; rewrite <- Hdp1; exact Hα0 ]).
    assert (Hc2 : msubst_compose κ2 κ = msubst_compose κ2b κ)
      by (rewrite Hp2; eapply msubst_compose_peel;
          [ exact Hκ | intros α0 Hα0; apply Hdisj; rewrite <- Hdp2; exact Hα0 ]).
    rewrite Hc1, Hc2, Heqe.
    assert (HwfTe : a_wf_aenv Te).
    { rewrite Heqe in HwfT. apply a_wf_aenv_strip_prefix_local in HwfT.
      inversion HwfT; subst; assumption. }
    apply a_inc_equiv__var; [ | | exact Hse ].
    { apply IHHκ; auto. }
    (* the composed semantic middle *)
    assert (HA : msubst_ptyp (msubst_compose κ1b κ) A
               = msubst_ptyp κ1b (msubst_ptyp κ A)).
    { apply msubst_ptyp_compose. intros α0 Hα0.
      eapply a_inc_compose_vis;
        [ exact Hκ | exact Hib1' | exact Hwa | exact Hwf1t
        | eapply a_wf_ptyp_ftv_tvarish; eauto ]. }
    rewrite HA.
    eapply a_tyequiv__trans; [ exact Heqve | ].
    eapply a_tyequiv_msubst; [ exact H | exact Hwf1t | exact Hib1' ].
  - (* var_skl x *)
    inversion Hwf0 as [ | | | xh Ph Θh Hnd Hwp Hwa | | ]; subst.
    assert (Hwf1t : a_wf_aenv Θ') by
      (apply a_wf_aenv_strip_prefix_local in Hwf1;
       inversion Hwf1; subst; assumption).
    assert (Hdisj : forall α0, α0 `in` dom Ξ -> α0 `notin` dom Θ').
    { intros α0 Hα0. pose proof (a_wf_aenv_uniq_local Hwf1) as Hu1.
      clear - Hu1 Hα0. solve_uniq. }
    edestruct a_inc_equiv_inc_peel_suffix
      as [κ1b [κ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hdp1]] [p2 [Hp2 Hdp2]]]]]]]];
      [ exact H0 | exact Hie | exact Hi1 | exact Hi2 | ].
    destruct (a_inc_equiv_var_skl_inv Hie2)
      as [Ξe [Pe' [Te [Heqe [Heqve [Hse Hie3]]]]]].
    destruct (a_inc_var_skl_inv Hib1) as [Ξ1 [P1' [T1 [Heq1 [Heqv1 [Hs1 Hib1']]]]]].
    destruct (a_inc_var_skl_inv Hib2) as [Ξ2 [P2' [T2 [Heq2 [Heqv2 [Hs2 Hib2']]]]]].
    pose proof (a_wf_aenv_uniq_local HwfT) as HuT.
    rewrite Heqe in HuT.
    assert (HeqE1 : Ξe ++ (x ~ abind_var_skl Pe') ++ Te
                  = Ξ1 ++ (x ~ abind_var_skl P1') ++ T1)
      by (rewrite <- Heqe; exact Heq1).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE1) as [HE1 [HB1 HT1]].
    injection HB1 as HB1. subst P1' T1.
    assert (HeqE2 : Ξe ++ (x ~ abind_var_skl Pe') ++ Te
                  = Ξ2 ++ (x ~ abind_var_skl P2') ++ T2)
      by (rewrite <- Heqe; exact Heq2).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE2) as [HE2 [HB2 HT2]].
    injection HB2 as HB2. subst P2' T2.
    assert (Hc1 : msubst_compose κ1 κ = msubst_compose κ1b κ)
      by (rewrite Hp1; eapply msubst_compose_peel;
          [ exact Hκ | intros α0 Hα0; apply Hdisj; rewrite <- Hdp1; exact Hα0 ]).
    assert (Hc2 : msubst_compose κ2 κ = msubst_compose κ2b κ)
      by (rewrite Hp2; eapply msubst_compose_peel;
          [ exact Hκ | intros α0 Hα0; apply Hdisj; rewrite <- Hdp2; exact Hα0 ]).
    rewrite Hc1, Hc2, Heqe.
    assert (HwfTe : a_wf_aenv Te).
    { rewrite Heqe in HwfT. apply a_wf_aenv_strip_prefix_local in HwfT.
      inversion HwfT; subst; assumption. }
    apply a_inc_equiv__var_skl; [ | | exact Hse ].
    { apply IHHκ; auto. }
    assert (HP : msubst_pskl (msubst_compose κ1b κ) P
               = msubst_pskl κ1b (msubst_pskl κ P)).
    { apply msubst_pskl_compose. intros α0 Hα0.
      eapply a_inc_compose_vis;
        [ exact Hκ | exact Hib1' | exact Hwa | exact Hwf1t
        | eapply a_scope_pskl_ftv_tvarish; eauto ]. }
    rewrite HP.
    eapply a_pskl_tyequiv__trans; [ exact Heqve | ].
    eapply a_pskl_tyequiv_msubst; [ exact H | exact Hwf1t | exact Hib1' ].
  - (* tvar α *)
    inversion Hwf0 as [ | | | | | αh Θh Hnd Hwa ]; subst.
    assert (Hwf1t : a_wf_aenv Θ') by
      (apply a_wf_aenv_strip_prefix_local in Hwf1;
       inversion Hwf1; subst; assumption).
    edestruct a_inc_equiv_inc_peel_suffix
      as [κ1b [κ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hdp1]] [p2 [Hp2 Hdp2]]]]]]]];
      [ exact H | exact Hie | exact Hi1 | exact Hi2 | ].
    assert (Hdisj : forall α0, α0 `in` dom Ξ -> α0 `notin` dom Θ').
    { intros α0 Hα0. pose proof (a_wf_aenv_uniq_local Hwf1) as Hu1.
      clear - Hu1 Hα0. solve_uniq. }
    destruct (a_inc_equiv_tvar_inv Hie2) as [Ξe [Te [Heqe [Hse Hie3]]]].
    destruct (a_inc_tvar_inv Hib1) as [Ξ1 [T1 [Heq1 [Hs1 Hib1']]]].
    destruct (a_inc_tvar_inv Hib2) as [Ξ2 [T2 [Heq2 [Hs2 Hib2']]]].
    pose proof (a_wf_aenv_uniq_local HwfT) as HuT.
    rewrite Heqe in HuT.
    assert (HeqE1 : Ξe ++ (α ~ abind_tvar) ++ Te = Ξ1 ++ (α ~ abind_tvar) ++ T1)
      by (rewrite <- Heqe; exact Heq1).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE1) as [HE1 [_ HT1]]; subst T1.
    assert (HeqE2 : Ξe ++ (α ~ abind_tvar) ++ Te = Ξ2 ++ (α ~ abind_tvar) ++ T2)
      by (rewrite <- Heqe; exact Heq2).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE2) as [HE2 [_ HT2]]; subst T2.
    assert (Hc1 : msubst_compose κ1 κ = msubst_compose κ1b κ)
      by (rewrite Hp1; eapply msubst_compose_peel;
          [ exact Hκ | intros α0 Hα0; apply Hdisj; rewrite <- Hdp1; exact Hα0 ]).
    assert (Hc2 : msubst_compose κ2 κ = msubst_compose κ2b κ)
      by (rewrite Hp2; eapply msubst_compose_peel;
          [ exact Hκ | intros α0 Hα0; apply Hdisj; rewrite <- Hdp2; exact Hα0 ]).
    rewrite Hc1, Hc2, Heqe.
    apply a_inc_equiv__tvar; [ | exact Hse ].
    assert (HwfTe : a_wf_aenv Te).
    { rewrite Heqe in HwfT. apply a_wf_aenv_strip_prefix_local in HwfT.
      inversion HwfT; subst; assumption. }
    apply IHHκ; auto.
Qed.

(** With [κ1a], [κ1b] both identity metasubstitutions and every [κ1a]-flexible
    still [κ1b]-flexible, an inner id-composition on the right collapses:
    [(ζ∘κ1b)∘κ1a = ζ∘κ1a].  (The domain side condition rules out a [κ1a]-flex
    that was rigidified by [κ1b]'s source-extension; in the bundle it is the
    flex-preservation carried by [Θ0 ⊴ Θmid ⊴ Θfin].) *)
Lemma msubst_compose_id_compose : forall κ1a κ1b ζ,
  is_id_msubst κ1a -> is_id_msubst κ1b ->
  (forall α, α `in` dom κ1a -> α `in` dom κ1b) ->
  msubst_compose (msubst_compose ζ κ1b) κ1a = msubst_compose ζ κ1a.
Proof.
  intros κ1a κ1b ζ Hida Hidb Hdom.
  apply List.map_ext_in.
  intros [α τ] Hin. simpl. f_equal.
  assert (Hτ : τ = ptyp_var_f α).
  { unfold is_id_msubst in Hida. rewrite Forall_forall in Hida.
    specialize (Hida _ Hin). unfold is_id_entry in Hida. exact Hida. }
  subst τ. simpl.
  rewrite msubst_lookup_compose
    by (left; apply Hdom; eapply binds_In; exact Hin).
  rewrite msubst_lookup_id by exact Hidb. reflexivity.
Qed.

(** THE GLUE.  Two adjacent sub-node factorings (a consistency Arrow, a Forall,
    a UnivGhost split) compose into the whole node's factoring.  [κ1a]/[κ1b] are
    the two sub-nodes' identity solution-witnesses. *)
Lemma a_inc_equiv_glue : forall Θ0 Θmid Θfin Θ κ κ1a κ1b ζ1 ζ2,
  a_wf_aenv Θ0 -> a_wf_aenv Θmid -> a_wf_aenv Θfin -> a_wf_aenv Θ ->
  is_id_msubst κ1a -> is_id_msubst κ1b ->
  (forall α, α `in` dom κ1a -> α `in` dom κ1b) ->
  κ1a ∷ Θ0 ⊑ Θmid ->
  κ1b ∷ Θmid ⊑ Θfin ->
  ζ1 ∷ Θmid ⊑ Θ ->
  ζ2 ∷ Θfin ⊑ Θ ->
  a_inc_equiv Θ0 κ (msubst_compose ζ1 κ1a) Θ ->
  a_inc_equiv Θmid ζ1 (msubst_compose ζ2 κ1b) Θ ->
  a_inc_equiv Θ0 κ (msubst_compose ζ2 κ1a) Θ.
Proof.
  intros Θ0 Θmid Θfin Θ κ κ1a κ1b ζ1 ζ2
         Hwf0 Hwfm Hwff HwfT Hida Hidb Hdom Ha Hb Hζ1 Hζ2 Hsub1 Hsub2.
  (* the second increment through Θfin *)
  assert (Hζ2b : msubst_compose ζ2 κ1b ∷ Θmid ⊑ Θ)
    by (eapply a_inc_compose; [ exact Hb | exact Hwfm | exact Hwff | exact Hζ2 ]).
  (* congruence: push σ = κ1a onto sub2 *)
  pose proof (a_inc_equiv_compose Ha Hwf0 Hwfm HwfT Hsub2 Hζ1 Hζ2b) as Hcong.
  (* simplify the inner id-composition *)
  rewrite (msubst_compose_id_compose ζ2 Hida Hidb Hdom) in Hcong.
  (* transitivity with sub1 *)
  eapply a_inc_equiv_trans; [ exact Hsub1 | exact HwfT | exact Hcong ].
Qed.

(** Entries ABOVE a suffix do not change the normal form of a type whose free
    variables all live in the suffix. *)
Lemma downarrow_app_agree_ptyp : forall Θp Θs A,
  uniq (Θp ++ Θs) ->
  ftvar_in_ptyp A [<=] dom Θs ->
  ⇓ᵗ[ Θp ++ Θs ] A = ⇓ᵗ[ Θs ] A.
Proof.
  intros Θp Θs A Hu; induction A; intros Hsub; simpl in *.
  - reflexivity.
  - reflexivity.
  - apply aenv_msubst_lookup_app; [ exact Hu | clear - Hsub; fsetdec ].
  - f_equal; [ apply IHA1 | apply IHA2 ]; clear - Hsub; fsetdec.
  - f_equal; apply IHA; clear - Hsub; fsetdec.
Qed.

(** A wf type's free variables live in the context's domain. *)
Lemma a_wf_ptyp_ftv_dom : forall Θ A,
  a_wf_ptyp Θ A -> ftvar_in_ptyp A [<=] dom Θ.
Proof.
  intros Θ A H α Hα.
  apply (a_wf_ptyp_ftv_tvarish H) in Hα.
  destruct Hα as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

(** [aenv_msubst] on a flex / flex-def head (reflexivity, exposing the cons so
    that [msubst_lookup_cons_eq]/[_neq] can fire). *)
Lemma aenv_msubst_flex_head : forall α Θ,
  aenv_msubst ((α ~ abind_flex_mono) ++ Θ) = (α, ptyp_var_f α) :: aenv_msubst Θ.
Proof. reflexivity. Qed.

Lemma aenv_msubst_flex_def_head : forall α τ Θ,
  aenv_msubst ((α ~ abind_flex_mono_def τ) ++ Θ)
    = (α, ⇓ᵗ[ Θ ] τ) :: aenv_msubst Θ.
Proof. reflexivity. Qed.

(** Given the var-leaf equivalence, every wf MONOtype is [≡ᵗ] its normal form. *)
Lemma mono_downarrow_from_var : forall Θ,
  (forall α, a_binds_tvar α Θ -> Θ ⊢ (ptyp_var_f α) ≡ᵗ ⇓ᵗ[Θ] (ptyp_var_f α)) ->
  forall τ, a_wf_ptyp Θ τ -> mono_ptyp τ -> Θ ⊢ τ ≡ᵗ ⇓ᵗ[Θ] τ.
Proof.
  intros Θ Hvar τ Hwfτ Hmono; revert Hwfτ; induction Hmono; intros Hwfτ.
  - simpl. apply a_tyequiv__refl. constructor.
  - apply Hvar. inversion Hwfτ; subst. auto.
  - inversion Hwfτ; subst. simpl.
    apply a_tyequiv__arrow; [ apply IHHmono1 | apply IHHmono2 ]; auto.
Qed.

(** Every wf MONOtype is [≡ᵗ]-equivalent to its own normal form. *)
Lemma a_tyequiv_to_downarrow_mono : forall Θ,
  a_wf_aenv Θ ->
  forall τ, a_wf_ptyp Θ τ -> mono_ptyp τ -> Θ ⊢ τ ≡ᵗ ⇓ᵗ[Θ] τ.
Proof.
  intros Θ Hwf; induction Hwf as
    [ | α Θ' Hnd Hwf IH
      | α σ Θ' Hnd Hwpσ Hmσ Hwf IH
      | x P Θ' Hnd Hwp Hwf IH
      | x A0 Θ' Hnd Hwp Hwf IH
      | α Θ' Hnd Hwf IH ];
    apply mono_downarrow_from_var; intros α0 Hα0.
  - (* nil: no tvar binding *)
    exfalso. destruct Hα0 as [Hb | [Hb | [t Hb]]]; inversion Hb.
  - (* head = undefined flex α *)
    cbn [msubst_ptyp]. rewrite aenv_msubst_flex_head.
    destruct (α0 == α) as [Heq | Hne].
    + subst α0. rewrite msubst_lookup_cons_eq. apply a_tyequiv__refl. constructor.
    + rewrite msubst_lookup_cons_neq by auto.
      assert (HbΘ' : a_binds_tvar α0 Θ').
      { destruct Hα0 as [Hb | [Hb | [t Hb]]];
          [ left | right; left | right; right; exists t ];
          (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
           [ congruence | exact Hb' ]). }
      apply a_tyequiv_weaken_cons.
      apply (IH (ptyp_var_f α0)); [ apply a_wf_ptyp__var; exact HbΘ' | constructor ].
  - (* head = definition α := σ *)
    cbn [msubst_ptyp]. rewrite aenv_msubst_flex_def_head.
    destruct (α0 == α) as [Heq | Hne].
    + subst α0. rewrite msubst_lookup_cons_eq.
      eapply a_tyequiv__trans.
      * apply a_tyequiv__flex_def. unfold binds; simpl; left; reflexivity.
      * apply a_tyequiv_weaken_cons. apply (IH σ Hwpσ Hmσ).
    + rewrite msubst_lookup_cons_neq by auto.
      assert (HbΘ' : a_binds_tvar α0 Θ').
      { destruct Hα0 as [Hb | [Hb | [t Hb]]];
          [ left | right; left | right; right; exists t ];
          (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
           [ congruence | exact Hb' ]). }
      apply a_tyequiv_weaken_cons.
      apply (IH (ptyp_var_f α0)); [ apply a_wf_ptyp__var; exact HbΘ' | constructor ].
  - (* head = term skeleton x : P (⇓ drops it) *)
    assert (HbΘ' : a_binds_tvar α0 Θ').
    { destruct Hα0 as [Hb | [Hb | [t Hb]]];
        [ left | right; left | right; right; exists t ];
        (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
         [ discriminate | exact Hb' ]). }
    change (⇓ᵗ[ (x ~ abind_var_skl P) ++ Θ' ] (ptyp_var_f α0))
      with (⇓ᵗ[ Θ' ] (ptyp_var_f α0)).
    apply a_tyequiv_weaken_cons.
    apply (IH (ptyp_var_f α0)); [ apply a_wf_ptyp__var; exact HbΘ' | constructor ].
  - (* head = term type x : A0 (⇓ drops it) *)
    assert (HbΘ' : a_binds_tvar α0 Θ').
    { destruct Hα0 as [Hb | [Hb | [t Hb]]];
        [ left | right; left | right; right; exists t ];
        (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
         [ discriminate | exact Hb' ]). }
    change (⇓ᵗ[ (x ~ abind_var_typ A0) ++ Θ' ] (ptyp_var_f α0))
      with (⇓ᵗ[ Θ' ] (ptyp_var_f α0)).
    apply a_tyequiv_weaken_cons.
    apply (IH (ptyp_var_f α0)); [ apply a_wf_ptyp__var; exact HbΘ' | constructor ].
  - (* head = rigid α (⇓ drops it) *)
    change (⇓ᵗ[ (α ~ abind_tvar) ++ Θ' ] (ptyp_var_f α0))
      with (⇓ᵗ[ Θ' ] (ptyp_var_f α0)).
    destruct (α0 == α) as [Heq | Hne].
    + subst α0. cbn [msubst_ptyp]. rewrite aenv_msubst_notin by auto.
      apply a_tyequiv__refl. constructor.
    + assert (HbΘ' : a_binds_tvar α0 Θ').
      { destruct Hα0 as [Hb | [Hb | [t Hb]]];
          [ left | right; left | right; right; exists t ];
          (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
           [ congruence | exact Hb' ]). }
      apply a_tyequiv_weaken_cons.
      apply (IH (ptyp_var_f α0)); [ apply a_wf_ptyp__var; exact HbΘ' | constructor ].
Qed.

(* Poly generalization of a_tyequiv_to_downarrow_mono: any wf type (incl. ∀) is
   ≡ᵗ its downarrow.  Needed for a_inc_self_downarrow's var/flex_def middle
   re-proof, where the middle type may be a polytype. *)
Lemma a_tyequiv_to_downarrow : forall Θ A,
  a_wf_ptyp Θ A -> a_wf_aenv Θ -> Θ ⊢ A ≡ᵗ (⇓ᵗ[ Θ ] A).
Proof.
  intros Θ A Hwp; induction Hwp; intros Hwf.
  - simpl. apply a_tyequiv__refl. constructor.
  - apply a_tyequiv_to_downarrow_mono;
      [ exact Hwf | apply a_wf_ptyp__var; assumption | constructor ].
  - simpl. apply a_tyequiv__arrow; [ apply IHHwp1 | apply IHHwp2 ]; exact Hwf.
  - simpl. apply a_tyequiv__all with (L := L `union` dom Θ). intros α Hα.
    assert (HxΘ : α `notin` dom Θ) by (clear - Hα; fsetdec).
    assert (Hwfx : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ exact HxΘ | exact Hwf ]).
    specialize (H0 α ltac:(clear - Hα; fsetdec) Hwfx).
    assert (Hcomm : ⇓ᵗ[ (α ~ abind_tvar) ++ Θ ] (open_ptyp_wrt_ptyp A (ptyp_var_f α))
                    = open_ptyp_wrt_ptyp (⇓ᵗ[ Θ ] A) (ptyp_var_f α)).
    { replace (aenv_msubst ((α ~ abind_tvar) ++ Θ)) with (aenv_msubst Θ)
        by (symmetry; apply aenv_msubst_tvar).
      apply msubst_ptyp_open_lc;
        [ apply aenv_msubst_lc; exact Hwf
        | rewrite dom_aenv_msubst; exact HxΘ ]. }
    rewrite Hcomm in H0.
    eapply a_tyequiv_strengthen_tvar_cons; [ exact H0 | reflexivity ].
Qed.

(* The middle-≡ adjustment for a_inc_self_downarrow: msubst κ A ≡ its ⇓-composed
   form, when msubst κ A is wf in the (suffix) sub-target Θt of Θ. *)
Lemma msubst_downarrow_tyequiv : forall Θ Θpre Θt A,
  Θ = Θpre ++ Θt -> uniq Θ -> a_wf_aenv Θt ->
  a_wf_ptyp Θt A ->
  Θt ⊢ A ≡ᵗ (⇓ᵗ[ Θ ] A).
Proof.
  intros Θ Θpre Θt A HeqΘ Huq Hwfaenv HwfB. subst Θ.
  rewrite (downarrow_app_agree_ptyp Θpre Θt A Huq (a_wf_ptyp_ftv_dom HwfB)).
  apply a_tyequiv_to_downarrow; [ exact HwfB | exact Hwfaenv ].
Qed.

Lemma a_wf_aenv_app_r : forall Θp Θs,
  a_wf_aenv (Θp ++ Θs) -> a_wf_aenv Θs.
Proof.
  induction Θp as [ | [a b] Θp' IH ]; intros Θs Hwf; simpl in Hwf.
  - exact Hwf.
  - inversion Hwf; subst; apply IH; assumption.
Qed.

Lemma msubst_compose_downarrow_tyequiv : forall Θ Θpre Θt κ A,
  Θ = Θpre ++ Θt -> uniq Θ -> a_wf_aenv Θ -> a_wf_aenv Θt ->
  msubst_lc κ ->
  (forall α, α `in` dom κ -> a_wf_ptyp Θt (msubst_lookup κ α)) ->
  lc_ptyp A ->
  Θt ⊢ (msubst_ptyp (msubst_compose (aenv_msubst Θ) κ) A) ≡ᵗ (msubst_ptyp κ A).
Proof.
  intros Θ Θpre Θt κ A HeqΘ Huq HwfΘ Hwft Hlcκ Himg Hlc;
    revert Θpre Θt HeqΘ Huq Hwft Himg.
  induction Hlc; intros Θpre Θt HeqΘ Huq Hwft Himg; simpl.
  - apply a_tyequiv__refl. constructor.
  - (* var α *)
    destruct (AtomSetProperties.In_dec α (dom κ)) as [Hin | Hni].
    + rewrite msubst_lookup_compose by (left; exact Hin).
      apply a_tyequiv__sym.
      eapply msubst_downarrow_tyequiv;
        [ exact HeqΘ | exact Huq | exact Hwft | apply Himg; exact Hin ].
    + rewrite (msubst_lookup_notin κ Hni).
      assert (Hnic : α `notin` dom (msubst_compose (aenv_msubst Θ) κ)).
      { rewrite dom_msubst_compose. exact Hni. }
      rewrite (msubst_lookup_notin _ Hnic).
      apply a_tyequiv__refl. constructor.
  - apply a_tyequiv__arrow;
      [ apply (IHHlc1 Θpre Θt HeqΘ Huq Hwft Himg)
      | apply (IHHlc2 Θpre Θt HeqΘ Huq Hwft Himg) ].
  - apply a_tyequiv__all
      with (L := dom κ `union` dom Θt `union` dom Θpre
                 `union` dom (msubst_compose (aenv_msubst Θ) κ)).
    intros α Hα.
    rewrite <- (@msubst_ptyp_open_lc (msubst_compose (aenv_msubst Θ) κ) A α);
      [ | intros β; destruct (AtomSetProperties.In_dec β (dom κ)) as [Hyi | Hyn];
          [ rewrite msubst_lookup_compose by (left; exact Hyi);
            apply msubst_ptyp_lc_lc; [ apply aenv_msubst_lc; exact HwfΘ | apply Hlcκ ]
          | assert (Hync : β `notin` dom (msubst_compose (aenv_msubst Θ) κ))
              by (rewrite dom_msubst_compose; exact Hyn);
            rewrite (msubst_lookup_notin _ Hync); apply lc_ptyp_var_f ]
        | clear - Hα; fsetdec ].
    rewrite <- (@msubst_ptyp_open_lc κ A α); [ | exact Hlcκ | clear - Hα; fsetdec ].
    apply (H0 α Θpre Θt HeqΘ Huq Hwft Himg).
Qed.

(* pskl mirror of msubst_compose_downarrow_tyequiv (var_skl middle adjustment). *)
Lemma msubst_pskl_compose_downarrow_tyequiv : forall Θ Θpre Θt κ P,
  Θ = Θpre ++ Θt -> uniq Θ -> a_wf_aenv Θ -> a_wf_aenv Θt ->
  msubst_lc κ ->
  (forall α, α `in` dom κ -> a_wf_ptyp Θt (msubst_lookup κ α)) ->
  lc_pskl P ->
  Θt ⊢ (msubst_pskl (msubst_compose (aenv_msubst Θ) κ) P) ≡ˢ (msubst_pskl κ P).
Proof.
  intros Θ Θpre Θt κ P HeqΘ Huq HwfΘ Hwft Hlcκ Himg Hlc;
    revert Θpre Θt HeqΘ Huq Hwft Himg.
  induction Hlc; intros Θpre Θt HeqΘ Huq Hwft Himg; simpl.
  - apply a_pskl_tyequiv__refl. constructor.
  - destruct (AtomSetProperties.In_dec α (dom κ)) as [Hin | Hni].
    + rewrite msubst_lookup_compose by (left; exact Hin).
      apply a_tyequiv_pskl. apply a_tyequiv__sym.
      eapply msubst_downarrow_tyequiv;
        [ exact HeqΘ | exact Huq | exact Hwft | apply Himg; exact Hin ].
    + rewrite (msubst_lookup_notin κ Hni).
      assert (Hnic : α `notin` dom (msubst_compose (aenv_msubst Θ) κ))
        by (rewrite dom_msubst_compose; exact Hni).
      rewrite (msubst_lookup_notin _ Hnic).
      apply a_pskl_tyequiv__refl. constructor.
  - apply a_pskl_tyequiv__arrow;
      [ apply (IHHlc1 Θpre Θt HeqΘ Huq Hwft Himg)
      | apply (IHHlc2 Θpre Θt HeqΘ Huq Hwft Himg) ].
  - apply a_pskl_tyequiv__all
      with (L := dom κ `union` dom Θt `union` dom Θpre
                 `union` dom (msubst_compose (aenv_msubst Θ) κ)).
    intros α Hα.
    rewrite <- (@msubst_pskl_open_lc_local (msubst_compose (aenv_msubst Θ) κ) P1 α);
      [ | intros β; destruct (AtomSetProperties.In_dec β (dom κ)) as [Hyi | Hyn];
          [ rewrite msubst_lookup_compose by (left; exact Hyi);
            apply msubst_ptyp_lc_lc; [ apply aenv_msubst_lc; exact HwfΘ | apply Hlcκ ]
          | assert (Hync : β `notin` dom (msubst_compose (aenv_msubst Θ) κ))
              by (rewrite dom_msubst_compose; exact Hyn);
            rewrite (msubst_lookup_notin _ Hync); apply lc_ptyp_var_f ]
        | clear - Hα; fsetdec ].
    rewrite <- (@msubst_pskl_open_lc_local κ P1 α); [ | exact Hlcκ | clear - Hα; fsetdec ].
    apply (H0 α Θpre Θt HeqΘ Huq Hwft Himg).
  - apply a_pskl_tyequiv__refl. constructor.
  - apply a_pskl_tyequiv__tophole. apply (IHHlc Θpre Θt HeqΘ Huq Hwft Himg).
Qed.

(* Normalize an a_inc by its own (suffix-of-Θ) target's flex_defs: the metasubst
   images are ⇓ᵗ[Θ]-collapsed while the target Θt is kept.  Makes the metasubst
   equal ⇓κ = compose(aenv_msubst Θ)κ, matching the ⇓-normalized join subject
   (consis_downarrow_subject).  The κb′-vs-⇓κb′ reconciliation. *)
(* Bundled self-downarrow.  One induction proves BOTH the a_inc reconstruction
   with the ⇓-composed metasubst AND its a_inc_equiv twin: they share the entire
   6-case skeleton (wf inversions, the ⇓-agrees-on-suffix rewrite [Hdd], and the
   Θpre-extension plumbing for the inert middles); only the per-case tails differ.
   [a_inc_self_downarrow] / [a_inc_equiv_self_downarrow] are its projections. *)
Lemma a_inc_self_downarrow_bundle : forall Θ0 κ Θt,
  κ ∷ Θ0 ⊑ Θt ->
  forall Θpre,
  a_wf_aenv (Θpre ++ Θt) -> uniq (Θpre ++ Θt) -> a_wf_aenv Θ0 ->
  msubst_compose (aenv_msubst (Θpre ++ Θt)) κ ∷ Θ0 ⊑ Θt
  /\ a_inc_equiv Θ0 κ (msubst_compose (aenv_msubst (Θpre ++ Θt)) κ) Θt.
Proof.
  intros Θ0 κ Θt Hinc; induction Hinc; intros Θpre HwfW Huq Hwf0.
  - (* empty *)
    split; [ apply a_inc__empty | apply a_inc_equiv__empty ]; assumption.
  - (* flex α τ : target Θ' unchanged, Θpre unchanged *)
    simpl.
    inversion Hwf0 as [ | α0 Θ0x Hnd0 Hwf0' | | | | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ') by (eapply a_wf_aenv_app_r; exact HwfW).
    assert (Hdd : ⇓ᵗ[ Θpre ++ Θ' ] τ = ⇓ᵗ[ Θ' ] τ)
      by (apply downarrow_app_agree_ptyp; [ exact Huq | apply a_wf_ptyp_ftv_dom; exact H ]).
    destruct (IHHinc Θpre HwfW Huq Hwf0') as [IHa IHe].
    split.
    + apply a_inc__flex.
      * exact IHa.
      * rewrite Hdd. apply a_wf_ptyp_downarrow_mono; [ exact HwfΘ' | exact H | exact H0 ].
      * rewrite Hdd. apply mono_downarrow; [ exact HwfΘ' | exact H | exact H0 ].
    + apply a_inc_equiv__flex.
      * exact IHe.
      * rewrite Hdd. apply a_tyequiv_to_downarrow_mono; [ exact HwfΘ' | exact H | exact H0 ].
  - (* flex_def α ≔ τ : image τ', premise τ'≡msubst κ τ *)
    simpl.
    inversion Hwf0 as [ | | α0 τ0 Θ0x Hnd0 Hwpτ0 Hmτ0 Hwf0' | | | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ') by (eapply a_wf_aenv_app_r; exact HwfW).
    assert (Hdd : ⇓ᵗ[ Θpre ++ Θ' ] τ' = ⇓ᵗ[ Θ' ] τ')
      by (apply downarrow_app_agree_ptyp; [ exact Huq | apply a_wf_ptyp_ftv_dom; exact H ]).
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    destruct (IHHinc Θpre HwfW Huq Hwf0') as [IHa IHe].
    split.
    + apply a_inc__flex_def.
      * exact IHa.
      * rewrite Hdd. apply a_wf_ptyp_downarrow_mono; [ exact HwfΘ' | exact H | exact H0 ].
      * rewrite Hdd. apply mono_downarrow; [ exact HwfΘ' | exact H | exact H0 ].
      * eapply a_tyequiv__trans.
        -- apply a_tyequiv__sym.
           eapply msubst_downarrow_tyequiv;
             [ reflexivity | exact Huq | exact HwfΘ' | exact H ].
        -- eapply a_tyequiv__trans; [ exact H1 | ].
           apply a_tyequiv__sym.
           eapply msubst_compose_downarrow_tyequiv;
             [ reflexivity | exact Huq | exact HwfW | exact HwfΘ' | exact Hlcκ | | ].
           ++ intros α0 Hα0. eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf0' | ].
              destruct (a_inc_dom_flex Hinc Hα0) as [Hb | [t0 Hb]];
                [ right; left | right; right; exists t0 ]; exact Hb.
           ++ eapply a_wf_ptyp_lc; exact Hwpτ0.
    + apply a_inc_equiv__flex_def.
      * exact IHe.
      * rewrite Hdd. apply a_tyequiv_to_downarrow_mono; [ exact HwfΘ' | exact H | exact H0 ].
      * exact H1.
  - (* var A : κ unchanged, target Ξ++(x~var A')++Θ' *)
    inversion Hwf0 as [ | | | | x0 A0 Θ0x Hnd0 HwpA Hwf0' | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ').
    { eapply a_wf_aenv_app_r with (Θp := Θpre ++ Ξ ++ (x ~ abind_var_typ A')).
      simpl_env. simpl_env in HwfW. exact HwfW. }
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (HW' : a_wf_aenv ((Θpre ++ Ξ ++ x ~ abind_var_typ A') ++ Θ'))
      by (simpl_env; simpl_env in HwfW; exact HwfW).
    assert (HU' : uniq ((Θpre ++ Ξ ++ x ~ abind_var_typ A') ++ Θ'))
      by (simpl_env; simpl_env in Huq; exact Huq).
    destruct (IHHinc (Θpre ++ Ξ ++ (x ~ abind_var_typ A')) HW' HU' Hwf0') as [IHa IHe].
    split.
    + apply a_inc__var; [ | | exact H0 ].
      * replace (Θpre ++ Ξ ++ x ~ abind_var_typ A' ++ Θ')
           with ((Θpre ++ Ξ ++ x ~ abind_var_typ A') ++ Θ') by (simpl_env; reflexivity).
        exact IHa.
      * eapply a_tyequiv__trans; [ exact H | ].
        apply a_tyequiv__sym.
        eapply msubst_compose_downarrow_tyequiv with
          (Θpre := Θpre ++ Ξ ++ (x ~ abind_var_typ A'));
          [ simpl_env; reflexivity | simpl_env; simpl_env in Huq; exact Huq
          | simpl_env; simpl_env in HwfW; exact HwfW | exact HwfΘ' | exact Hlcκ | | ].
        -- intros α0 Hα0. eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf0' | ].
           destruct (a_inc_dom_flex Hinc Hα0) as [Hb | [t0 Hb]];
             [ right; left | right; right; exists t0 ]; exact Hb.
        -- eapply a_wf_ptyp_lc; exact HwpA.
    + apply a_inc_equiv__var; [ | exact H | exact H0 ].
      replace (Θpre ++ Ξ ++ x ~ abind_var_typ A' ++ Θ')
         with ((Θpre ++ Ξ ++ x ~ abind_var_typ A') ++ Θ') by (simpl_env; reflexivity).
      exact IHe.
  - (* var_skl P : κ unchanged, target Ξ++(x~var_skl P')++Θ' *)
    inversion Hwf0 as [ | | | x0 P0 Θ0x Hnd0 HwpP Hwf0' | | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ').
    { eapply a_wf_aenv_app_r with (Θp := Θpre ++ Ξ ++ (x ~ abind_var_skl P')).
      simpl_env. simpl_env in HwfW. exact HwfW. }
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (HW' : a_wf_aenv ((Θpre ++ Ξ ++ x ~ abind_var_skl P') ++ Θ'))
      by (simpl_env; simpl_env in HwfW; exact HwfW).
    assert (HU' : uniq ((Θpre ++ Ξ ++ x ~ abind_var_skl P') ++ Θ'))
      by (simpl_env; simpl_env in Huq; exact Huq).
    destruct (IHHinc (Θpre ++ Ξ ++ (x ~ abind_var_skl P')) HW' HU' Hwf0') as [IHa IHe].
    split.
    + apply a_inc__var_skl; [ | | exact H0 ].
      * replace (Θpre ++ Ξ ++ x ~ abind_var_skl P' ++ Θ')
           with ((Θpre ++ Ξ ++ x ~ abind_var_skl P') ++ Θ') by (simpl_env; reflexivity).
        exact IHa.
      * eapply a_pskl_tyequiv__trans; [ exact H | ].
        apply a_pskl_tyequiv__sym.
        eapply msubst_pskl_compose_downarrow_tyequiv with
          (Θpre := Θpre ++ Ξ ++ (x ~ abind_var_skl P'));
          [ simpl_env; reflexivity | simpl_env; simpl_env in Huq; exact Huq
          | simpl_env; simpl_env in HwfW; exact HwfW | exact HwfΘ' | exact Hlcκ | | ].
        -- intros α0 Hα0. eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf0' | ].
           destruct (a_inc_dom_flex Hinc Hα0) as [Hb | [t0 Hb]];
             [ right; left | right; right; exists t0 ]; exact Hb.
        -- eapply a_scope_pskl_lc; exact HwpP.
    + apply a_inc_equiv__var_skl; [ | exact H | exact H0 ].
      replace (Θpre ++ Ξ ++ x ~ abind_var_skl P' ++ Θ')
         with ((Θpre ++ Ξ ++ x ~ abind_var_skl P') ++ Θ') by (simpl_env; reflexivity).
      exact IHe.
  - (* tvar α : target Ξ++(α~tvar)++Θ' *)
    inversion Hwf0 as [ | | | | | α0 Θ0x Hnd0 Hwf0' ]; subst.
    assert (HW' : a_wf_aenv ((Θpre ++ Ξ ++ α ~ abind_tvar) ++ Θ'))
      by (simpl_env; simpl_env in HwfW; exact HwfW).
    assert (HU' : uniq ((Θpre ++ Ξ ++ α ~ abind_tvar) ++ Θ'))
      by (simpl_env; simpl_env in Huq; exact Huq).
    destruct (IHHinc (Θpre ++ Ξ ++ (α ~ abind_tvar)) HW' HU' Hwf0') as [IHa IHe].
    split.
    + apply a_inc__tvar; [ | exact H ].
      replace (Θpre ++ Ξ ++ α ~ abind_tvar ++ Θ')
         with ((Θpre ++ Ξ ++ α ~ abind_tvar) ++ Θ') by (simpl_env; reflexivity).
      exact IHa.
    + apply a_inc_equiv__tvar; [ | exact H ].
      replace (Θpre ++ Ξ ++ α ~ abind_tvar ++ Θ')
         with ((Θpre ++ Ξ ++ α ~ abind_tvar) ++ Θ') by (simpl_env; reflexivity).
      exact IHe.
Qed.

Lemma a_inc_self_downarrow : forall Θ0 κ Θt,
  κ ∷ Θ0 ⊑ Θt ->
  forall Θpre,
  a_wf_aenv (Θpre ++ Θt) -> uniq (Θpre ++ Θt) -> a_wf_aenv Θ0 ->
  msubst_compose (aenv_msubst (Θpre ++ Θt)) κ ∷ Θ0 ⊑ Θt.
Proof.
  intros Θ0 κ Θt Hinc Θpre HwfW Huq Hwf0.
  exact (proj1 (a_inc_self_downarrow_bundle Hinc Θpre HwfW Huq Hwf0)).
Qed.

(* a_inc_equiv twin of a_inc_self_downarrow: an increment is ≡-equivalent to its
   own downarrow.  Used to adjust the factoring's competing metasubst ⇓κ→κ. *)
Lemma a_inc_equiv_self_downarrow : forall Θ0 κ Θt,
  κ ∷ Θ0 ⊑ Θt ->
  forall Θpre,
  a_wf_aenv (Θpre ++ Θt) -> uniq (Θpre ++ Θt) -> a_wf_aenv Θ0 ->
  a_inc_equiv Θ0 κ (msubst_compose (aenv_msubst (Θpre ++ Θt)) κ) Θt.
Proof.
  intros Θ0 κ Θt Hinc Θpre HwfW Huq Hwf0.
  exact (proj2 (a_inc_self_downarrow_bundle Hinc Θpre HwfW Huq Hwf0)).
Qed.

(* Strip a term-var middle (x:Q) from an ID increment, dropping it from both
   source and target (id ⟹ no suffix added, so Ξv=nil, A'=Q).  The id-side
   plumbing of the SkipTmVar walk case: recovers the (Ξ++Θ0) id-increment. *)
Lemma a_inc_var_mid_strip_id : forall Ξ x A Θ0 κ Θ1,
  a_decls Ξ ->
  is_id_msubst κ ->
  κ ∷ (Ξ ++ (x ~ abind_var_typ A) ++ Θ0) ⊑ ((x ~ abind_var_typ A) ++ Θ1) ->
  κ ∷ (Ξ ++ Θ0) ⊑ Θ1.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros x A Θ0 κ Θ1 Hdec Hid Hinc.
  - simpl in Hinc.
    destruct (a_inc_var_inv Hinc) as [Ξv [A' [Θ2 [Heqt [Heqv [Hsuf Hinc']]]]]].
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
          (c := x) (b := abind_var_typ A) (Ξ := (@nil (atom * abind)));
          [ simpl; exact Hbt
          | intro Hc; inversion Hc
          | intro Hc; inversion Hc
          | intros ? Hc; inversion Hc ]. }
    eapply IH; [ exact Hdec' | exact Hid' | exact Hinc' ].
Qed.

Lemma aenv_msubst_dom_inv : forall Θ α,
  α `in` dom (aenv_msubst Θ) -> a_flex_tvar Θ α.
Proof.
  induction Θ as [ | [a b] Θ' IH ]; intros α Hα; simpl in Hα.
  - clear - Hα; fsetdec.
  - assert (Hstep : forall β, a_flex_tvar Θ' β -> a_flex_tvar ((a, b) :: Θ') β).
    { intros β [Hb | [τ Hb]]; [ left | right; exists τ ];
        unfold binds; simpl; right; exact Hb. }
    destruct b; simpl in Hα.
    + apply Hstep. apply IH. exact Hα.
    + apply Hstep. apply IH. exact Hα.
    + apply Hstep. apply IH. exact Hα.
    + destruct (α == a) as [-> | Hne].
      * left. unfold binds; simpl; left; reflexivity.
      * apply Hstep. apply IH. clear - Hα Hne; fsetdec.
    + destruct (α == a) as [-> | Hne].
      * right. eexists. unfold binds; simpl; left; reflexivity.
      * apply Hstep. apply IH. clear - Hα Hne; fsetdec.
Qed.

Lemma msubst_pskl_ftv_lower : forall κ P α',
  α' `in` ftvar_in_pskl P ->
  ftvar_in_ptyp (msubst_lookup κ α') [<=] ftvar_in_pskl (msubst_pskl κ P).
Proof.
  induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros α' Hα; simpl in Hα |- *.
  - clear - Hα; fsetdec.
  - clear - Hα; fsetdec.
  - assert (α' = β) by (clear - Hα; fsetdec); subst.
    rewrite ftvar_in_ptyp_to_pskl. clear; fsetdec.
  - apply union_1 in Hα; destruct Hα as [HXa | HXb];
      [ pose proof (IHa α' HXa) | pose proof (IHb α' HXb) ]; clear - H; fsetdec.
  - pose proof (IHall α' Hα). clear - H; fsetdec.
  - clear - Hα; fsetdec.
  - pose proof (IHt α' Hα). clear - H; fsetdec.
Qed.

Lemma a_assign_subject_flex_local : forall Θ0 Ξ α P Θ1,
  Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 ->
  a_flex_tvar Θ0 α.
Proof.
  intros Θ0 Ξ α P Θ1 H; induction H.
  - left. unfold binds; simpl; left; reflexivity.
  - left. unfold binds; simpl; left; reflexivity.
  - exact H.
  - apply a_flex_tvar_weaken_prefix. exact IHa_assign.
  - apply a_flex_tvar_weaken_prefix. exact IHa_assign.
  - apply a_flex_tvar_weaken_prefix. exact IHa_assign.
  - apply a_flex_tvar_weaken_prefix. exact IHa_assign.
  - apply a_flex_tvar_weaken_prefix. exact IHa_assign.
Qed.

Lemma msubst_lookup_app_in : forall ζ1 ζ2 α,
  α `in` dom ζ1 -> msubst_lookup (ζ1 ++ ζ2) α = msubst_lookup ζ1 α.
Proof.
  induction ζ1 as [ | [a t] ζ1' IH ]; intros ζ2 α Hα; simpl in *.
  - clear - Hα; fsetdec.
  - destruct (α == a) as [-> | Hne];
      [ reflexivity | apply IH; clear - Hα Hne; fsetdec ].
Qed.

(** THE ≡ᵗ STRENGTHENING.  Strip a middle binding [c~b] and an [a_decls]-free
    prefix [Ξ] off both sides of a MONOtype equivalence whose endpoints are wf
    in the tail [Θt]. *)
Lemma a_tyequiv_strengthen_mono_mid : forall Ξ c b Θt A A',
  a_wf_aenv (Ξ ++ (c ~ b) ++ Θt) ->
  a_wf_ptyp Θt A -> mono_ptyp A ->
  a_wf_ptyp Θt A' -> mono_ptyp A' ->
  (Ξ ++ (c ~ b) ++ Θt) ⊢ A ≡ᵗ A' ->
  Θt ⊢ A ≡ᵗ A'.
Proof.
  intros Ξ c b Θt A A' Hwf HwfA HmA HwfB HmB Heq.
  rewrite <- app_assoc in Hwf, Heq.
  assert (Hwft : a_wf_aenv Θt) by (apply a_wf_aenv_strip_prefix_local in Hwf; exact Hwf).
  assert (Huniq : uniq ((Ξ ++ (c ~ b)) ++ Θt)) by (apply a_wf_aenv_uniq; exact Hwf).
  pose proof (a_tyequiv_downarrow Hwf Heq) as Hd.
  assert (HdA : ⇓ᵗ[ (Ξ ++ (c ~ b)) ++ Θt ] A = ⇓ᵗ[ Θt ] A)
    by (apply downarrow_app_agree_ptyp;
        [ exact Huniq | apply a_wf_ptyp_ftv_dom; exact HwfA ]).
  assert (HdB : ⇓ᵗ[ (Ξ ++ (c ~ b)) ++ Θt ] A' = ⇓ᵗ[ Θt ] A')
    by (apply downarrow_app_agree_ptyp;
        [ exact Huniq | apply a_wf_ptyp_ftv_dom; exact HwfB ]).
  rewrite HdA, HdB in Hd.
  eapply a_tyequiv__trans;
    [ apply (a_tyequiv_to_downarrow_mono Hwft HwfA HmA) | ].
  rewrite Hd. apply a_tyequiv__sym.
  apply (a_tyequiv_to_downarrow_mono Hwft HwfB HmB).
Qed.

(** Metasubstitution preserves guarded skeleton shape.  The only interesting
    leaf is a flexible variable: every image of an information increase is a
    monotype, hence guarded. *)
Lemma guarded_pskl_msubst_inc : forall Θ0 κ Θ P,
  κ ∷ Θ0 ⊑ Θ ->
  guarded_pskl P ->
  guarded_pskl (msubst_pskl κ P).
Proof.
  intros Θ0 κ Θ P Hinc Hg. inversion Hg; subst; simpl.
  - apply guarded_pskl__unit.
  - apply mono_ptyp_to_pskl_guarded. eapply a_inc_lookup_mono; eauto.
  - apply guarded_pskl__arrow;
      eapply msubst_pskl_lc; eauto.
Qed.

(* A monotype whose free type variables are all tvar-ish in Θ is well-formed
   there — used to place a ⇓-normalized image in a sub-target. *)
Lemma mono_ftv_wf : forall Θ τ,
  mono_ptyp τ ->
  (forall α, α `in` ftvar_in_ptyp τ -> a_binds_tvar α Θ) ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ τ Hm; induction Hm; intros Hftv; simpl in *.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply Hftv. fsetdec.
  - apply a_wf_ptyp__arrow;
      [ apply IHHm1 | apply IHHm2 ]; intros α Hα; apply Hftv; fsetdec.
Qed.

(* Normalize the decls-prefix images of a competing a_inc into a sub-target Θ'
   (below the walked binder): the Θ0-part increment is already into Θ' and the
   Ξ-prefix flex images ⇓-collapse into Θ' once they are join-grounded. *)
Lemma a_inc_downarrow_prefix : forall Ξ κa T Θ0 κb σb Θ Θ',
  a_decls Ξ ->
  κa ++ κb ∷ (Ξ ++ T) ⊑ Θ ->
  uniq (Ξ ++ T) ->
  dom κa [=] dom Ξ ->
  σb ∷ Θ0 ⊑ Θ' ->
  a_wf_aenv Θ -> uniq Θ ->
  (forall x c, binds x c Θ' -> binds x c Θ) ->
  (forall α, α `in` dom κa ->
     ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup κa α)) [<=] dom Θ') ->
  (msubst_compose (aenv_msubst Θ) κa) ++ σb ∷ (Ξ ++ Θ0) ⊑ Θ'.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ];
    intros κa T Θ0 κb σb Θ Θ' Hdec Hinc Huq Hdom Hincb Hwf Huqt Hsub Hgr.
  - rewrite dom_nil in Hdom.
    destruct κa as [ | [c t] κa' ];
      [ simpl; exact Hincb
      | exfalso; simpl in Hdom;
        assert (c `in` dom ((c,t)::κa')) by (simpl; fsetdec);
        rewrite Hdom in H; clear - H; fsetdec ].
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    destruct κa as [ | [c t] κa' ];
      [ exfalso; simpl in Hdom;
        assert (a `in` dom ((a~abind_flex_mono)++Ξ')) by (simpl; fsetdec);
        rewrite <- Hdom in H; clear - H; fsetdec | ].
    simpl in Hinc.
    inversion Hinc as [ | R κs Tt aa τ0 Hinc' Hwfτ Hmτ | | | | ]; subst.
    simpl.
    assert (Huq' : uniq (Ξ' ++ T)) by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (HanΞΘ : c `notin` dom (Ξ' ++ T))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Hanκa : c `notin` dom κa').
    { pose proof (a_inc_dom_sub Hinc') as Hs.
      clear - Hs HanΞΘ. repeat rewrite dom_app in *. fsetdec. }
    assert (Hlkc : msubst_lookup ((c, t) :: κa') c = t)
      by (simpl; destruct (c == c); [ reflexivity | contradiction ]).
    assert (Hgrc : ftvar_in_ptyp (⇓ᵗ[ Θ ] t) [<=] dom Θ').
    { pose proof (Hgr c ltac:(simpl; clear; fsetdec)) as Hg.
      rewrite Hlkc in Hg. exact Hg. }
    assert (Hwfd : a_wf_ptyp Θ' (⇓ᵗ[ Θ ] t)).
    { apply mono_ftv_wf; [ apply mono_downarrow; auto | ].
      intros α Hα.
      assert (HXd : α `in` dom Θ') by (clear - Hgrc Hα; fsetdec).
      eapply a_binds_tvar_strengthen;
        [ | exact Huqt | exact Hsub | exact HXd ].
      eapply a_wf_ptyp_ftv_tvarish;
        [ apply a_wf_ptyp_downarrow_mono; eauto | exact Hα ]. }
    apply a_inc__flex; [ | exact Hwfd | apply mono_downarrow; auto ].
    eapply IH; [ exact Hdec' | exact Hinc' | exact Huq' | | exact Hincb
               | exact Hwf | exact Huqt | exact Hsub | ].
    + clear - Hdom Hanκa HanΞΘ. simpl in Hdom.
      repeat rewrite dom_app in *. fsetdec.
    + intros α Hα. destruct (α == c) as [-> | Hne].
      * exfalso. clear - Hα Hanκa. fsetdec.
      * assert (HXin : α `in` dom ((c, t) :: κa'))
          by (simpl; clear - Hα; fsetdec).
        pose proof (Hgr α HXin) as Hg.
        rewrite (msubst_lookup_cons_neq t κa' Hne) in Hg.
        exact Hg.
Qed.

Lemma a_inc_equiv_mid_insert_var :
  forall Ξ x Θ0 Θ' Ξv κ1 κ2 σ1 σ2 A A',
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom κ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  Θ' ⊢ A' ≡ᵗ (msubst_ptyp κ2 A) ->
  a_suffix Ξv ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ' ->
  a_inc_equiv (Ξ ++ (x ~ abind_var_typ A) ++ Θ0)
              (κ1 ++ κ2) (σ1 ++ σ2)
              (Ξv ++ (x ~ abind_var_typ A') ++ Θ').
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros x Θ0 Θ' Ξv κ1 κ2 σ1 σ2 A A' Hdec Huq Hdκ Hdσ Heqm Hsuf Hie.
  - rewrite dom_nil in Hdκ, Hdσ.
    apply metasubst_dom_empty in Hdκ; apply metasubst_dom_empty in Hdσ; subst.
    simpl in Hie |- *.
    apply a_inc_equiv__var; [ exact Hie | exact Heqm | exact Hsuf ].
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Huκ : uniq (κ1 ++ κ2))
      by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
    assert (Huσ : uniq (σ1 ++ σ2))
      by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
    assert (HaΞ : a `notin` dom Ξ') by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ Θ0)) by (clear - Huq; simpl_env in Huq; solve_uniq).
    destruct κ1 as [ | [ar tr] κ1' ];
      [ exfalso; rewrite dom_nil in Hdκ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ')) by (simpl; fsetdec);
        rewrite <- Hdκ in Hin; clear - Hin; fsetdec | ].
    destruct σ1 as [ | [asg ts] σ1' ];
      [ exfalso; rewrite dom_nil in Hdσ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ')) by (simpl; fsetdec);
        rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
    assert (Harκ : ar `notin` dom κ1') by (clear - Huκ; simpl_env in Huκ; solve_uniq).
    assert (Hasσ : asg `notin` dom σ1') by (clear - Huσ; simpl_env in Huσ; solve_uniq).
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


(* ===================================================================== *)
(*  ⭐ THE κ-EXTENSION PACKAGE (moved here 2026-08-04).                     *)
(*                                                                        *)
(*  These lived in prop_look_complete_cstr.v and prop_look_complete_       *)
(*  extract.v, where the ONLY consumer used to be the final guess's block. *)
(*  The SolE-FlexR repair makes the SOLVE emit a flexible block too, so    *)
(*  every P6 statement from prop_look_complete.v onwards has to extend its *)
(*  metasubstitution over one — and that file sits ABOVE both of the old   *)
(*  homes.  Nothing here is specific to the collection or extract layer:   *)
(*  it is list algebra plus "msubst only reads free variables".           *)
(* ===================================================================== *)

Definition keys {A : Type} (l : list (atom * A)) : list atom := List.map fst l.

Lemma keys_app : forall (A : Type) (l1 l2 : list (atom * A)),
  keys (l1 ++ l2) = keys l1 ++ keys l2.
Proof.
  intros A l1 l2; induction l1 as [ | p l1' IH ]; unfold keys in *; simpl;
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma keys_eq_dom : forall (A B : Type) (l1 : list (atom * A)) (l2 : list (atom * B)),
  keys l1 = keys l2 -> dom l1 [=] dom l2.
Proof.
  induction l1 as [ | [x a] l1' IH ]; intros [ | [y b] l2' ] Hk;
    unfold keys in *; simpl in *; try discriminate; try reflexivity.
  injection Hk as Hxy Hk'; subst y.
  pose proof (IH l2' Hk') as Hd. simpl_env in *. fsetdec.
Qed.

Definition all_flex_mono (Ξ : aenv) : Prop :=
  Forall (fun p => snd p = abind_flex_mono) Ξ.

Lemma all_flex_mono_app : forall A B,
  all_flex_mono A -> all_flex_mono B -> all_flex_mono (A ++ B).
Proof. intros A B HA HB. apply Forall_app; split; assumption. Qed.

(** [msubst_pskl] only reads its argument's FREE variables, so entries keyed
    outside them are invisible.  The arrow case needs exactly this: the two
    branches' extensions are appended in one order but each branch's IH was
    proved against its own extension alone. *)
Lemma msubst_pskl_lookup_congr_ftv : forall κ σ P,
  (forall α, α `in` ftvar_in_pskl P ->
     msubst_lookup κ α = msubst_lookup σ α) ->
  msubst_pskl κ P = msubst_pskl σ P.
Proof.
  intros κ σ P; revert κ σ;
    induction P as [ | n | α | P1 IHP1 P2 IHP2 | P0 IHP0 | | P0 IHP0 ];
    intros κ σ Heq; cbn in *; try reflexivity.
  - rewrite Heq by (clear; fsetdec); reflexivity.
  - rewrite (IHP1 κ σ), (IHP2 κ σ);
      [ reflexivity | intros α Hα; apply Heq; clear - Hα; fsetdec
      | intros α Hα; apply Heq; clear - Hα; fsetdec ].
  - rewrite (IHP0 κ σ); [ reflexivity | exact Heq ].
  - rewrite (IHP0 κ σ); [ reflexivity | exact Heq ].
Qed.

Lemma msubst_lookup_mid_skip : forall κa κm κb α,
  α `notin` dom κm ->
  msubst_lookup (κa ++ κm ++ κb) α = msubst_lookup (κa ++ κb) α.
Proof.
  intros κa κm κb α Hα.
  destruct (AtomSetProperties.In_dec α (dom κa)) as [Hin | Hnin].
  - rewrite (@msubst_lookup_app_in κa (κm ++ κb) α Hin).
    rewrite (@msubst_lookup_app_in κa κb α Hin). reflexivity.
  - rewrite (@msubst_lookup_app_notin κa (κm ++ κb) α Hnin).
    rewrite (@msubst_lookup_app_notin κa κb α Hnin).
    rewrite (@msubst_lookup_app_notin κm κb α Hα). reflexivity.
Qed.

Lemma msubst_pskl_mid_skip : forall κa κm κb P,
  (forall α, α `in` dom κm -> α `notin` ftvar_in_pskl P) ->
  msubst_pskl (κa ++ κm ++ κb) P = msubst_pskl (κa ++ κb) P.
Proof.
  intros κa κm κb P Hdisj.
  apply msubst_pskl_lookup_congr_ftv; intros α Hα.
  apply msubst_lookup_mid_skip.
  intro Hc. apply (Hdisj α Hc). exact Hα.
Qed.

