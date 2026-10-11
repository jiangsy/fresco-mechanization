(** SCOPING OF RUN RESULTS (paper §6.3 #2) — the invariant that discharges
    the four suffix-discarding check rows' premise (2).

    [a_typing]'s check rows (algo/def_rules.v, [a_typing__abs_check_step]
    and the three beside it) DROP the suffix [Ξ] their body run deposited,
    and carry as a premise that the run's RESULT does not mention it:

      (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp <result>)

    That premise is a real invariant of the algorithm — thm:complete-type-
    inference has to DISCHARGE it when it builds those rows — but no
    scoping theorem local to the rule supplies it, so it stays a premise
    and is proved here.

    ⭐ THE SHAPE OF THE INVARIANT.  Thread a MARKER: a context entry every
    judgement keeps in place (a rigid type variable or either term-variable
    entry — [abind_marker]).  Relative to a marker [m], [above_dom m Θ] is
    the region a run may grow; the invariant says a run's TC-core never
    reaches into it beyond the binders the run itself peeled.  The peeled
    binders are RIGID, so the side condition needed on the way in is
    [core_rigid_above]: a core atom bound above the marker is rigid.  That
    is [core_rigid] (typing/prop_typing_rigidity.v) relativized to the above-marker
    region, and it is exactly what the Flex-Assign row needs — see
    [core_rigid_above_head_flex].

    Both discharge instances put the marker at the TOP of the input
    ([Ξ0 = nil]), where [above_dom m] is empty and the hypothesis is
    vacuous: the [_step] rows split at their peeled [(α ~ abind_tvar)],
    the [_base] rows at their binder [(x ~ abind_var_typ A)].

    The two walks: at the SUB level [a_sub_sub_flex_scope], and at the
    TYPING level [a_typing_scope] — both SCOPE PROPAGATION rather than core
    preservation, which is FALSE under [core_rigid_above] (see the ⚠️ note
    before [a_sub_sub_flex_scope]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_mod_compat.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.basic.prop_wf_preservation.
Require Import src.fresco.algo.typing.prop_typing_rigidity.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_gen.
Require Import src.fresco.algo_decl.prop_renaming.
Require Import src.fresco.algo.typing.prop_soundness_typing.

Set Implicit Arguments.

(** The atoms bound STRICTLY ABOVE the marker [m] — flat, so the walk needs
    no positional split machinery ([Ξ ++ (m ~ b) ++ Θ'] existentials). *)
Fixpoint above_dom (m : atom) (Θ : aenv) : atoms :=
  match Θ with
  | nil => empty
  | (y, _) :: Θ' => if y == m then empty else add y (above_dom m Θ')
  end.

Lemma above_dom_app_notin : forall m Ξ Θ,
  m `notin` dom Ξ ->
  above_dom m (Ξ ++ Θ) [=] dom Ξ `union` above_dom m Θ.
Proof.
  intros m Ξ; induction Ξ as [ | [y b] Ξ' IH ]; intros Θ Hm; simpl.
  - clear; fsetdec.
  - destruct (y == m) as [-> | Hne].
    + simpl in Hm. exfalso. clear - Hm; fsetdec.
    + simpl in Hm.
      rewrite (IH Θ ltac:(clear - Hm; solve_notin_auto)).
      clear; fsetdec.
Qed.

Lemma above_dom_cons_marker : forall m b Θ,
  above_dom m ((m ~ b) ++ Θ) [=] empty.
Proof.
  intros m b Θ; simpl.
  destruct (m == m) as [_ | Hc]; [ clear; fsetdec | exfalso; auto ].
Qed.

Lemma above_dom_cons_other : forall m y b Θ,
  y <> m ->
  above_dom m ((y ~ b) ++ Θ) [=] add y (above_dom m Θ).
Proof.
  intros m y b Θ Hne; simpl.
  destruct (y == m) as [-> | _]; [ exfalso; auto | clear; fsetdec ].
Qed.

Lemma above_dom_sub_dom : forall m Θ, above_dom m Θ [<=] dom Θ.
Proof.
  intros m Θ; induction Θ as [ | [y b] Θ' IH ]; simpl;
    [ clear; fsetdec | ].
  destruct (y == m) as [-> | Hne]; clear - IH; fsetdec.
Qed.

(** A MARKER is an entry kind every information increase (and every
    context-walking rule of the algorithm) keeps IN PLACE: rigid type
    variables and the two term-variable entries.  Flexibles are not
    markers — the walks move and consume them. *)
Definition abind_marker (b : abind) : Prop :=
  match b with
  | abind_tvar | abind_var_typ _ | abind_var_skl _ => True
  | abind_flex_mono | abind_flex_mono_def _ => False
  end.

(** An identity increase drops nothing from the domain: flex images are
    variables wf in the target (hence in its dom), and the rigid/term rows
    carry their entry over BY RULE.  (⚙ There is no such lemma for a
    general increase — solved flexes drop — hence the [is_id] guard.) *)
Lemma a_inc_id_dom_sub_scope : forall Θ0 κ Θ,
  κ ∷ Θ0 ⊑ Θ ->
  is_id_msubst κ ->
  dom Θ0 [<=] dom Θ.
Proof.
  intros Θ0 κ Θ H; induction H; intros Hid.
  - simpl. clear; fsetdec.
  - destruct (is_id_msubst_inv Hid) as [-> Hid'].
    match goal with
    | Hw : a_wf_ptyp Θ' (ptyp_var_f α) |- _ => inversion Hw; subst
    end.
    match goal with
    | Hb : a_binds_tvar α Θ' |- _ =>
        assert (Hin : α `in` dom Θ')
          by (destruct Hb as [Hb1 | [Hb1 | [τ1 Hb1]]]; eapply binds_In; eauto)
    end.
    pose proof (IHa_inc Hid') as Hrec.
    simpl. clear - Hin Hrec; fsetdec.
  - destruct (is_id_msubst_inv Hid) as [-> Hid'].
    match goal with
    | Hw : a_wf_ptyp Θ' (ptyp_var_f α) |- _ => inversion Hw; subst
    end.
    match goal with
    | Hb : a_binds_tvar α Θ' |- _ =>
        assert (Hin : α `in` dom Θ')
          by (destruct Hb as [Hb1 | [Hb1 | [τ1 Hb1]]]; eapply binds_In; eauto)
    end.
    pose proof (IHa_inc Hid') as Hrec.
    simpl. clear - Hin Hrec; fsetdec.
  - pose proof (IHa_inc Hid) as Hrec.
    rewrite !dom_app. simpl. clear - Hrec; fsetdec.
  - pose proof (IHa_inc Hid) as Hrec.
    rewrite !dom_app. simpl. clear - Hrec; fsetdec.
  - pose proof (IHa_inc Hid) as Hrec.
    rewrite !dom_app. simpl. clear - Hrec; fsetdec.
Qed.

(** THE MID-MARKER INVERSION: an increase whose source carries a marker
    entry produces a target that carries it too, same constructor, with
    the below-marker increase split off (its witness a suffix of κ). *)
Lemma a_inc_marker_mid : forall Θs κ Θt,
  κ ∷ Θs ⊑ Θt ->
  forall Ξ0 m b Θ0',
  Θs = Ξ0 ++ (m ~ b) ++ Θ0' ->
  abind_marker b ->
  exists Ξ1 b' Θ1' κ',
    Θt = Ξ1 ++ (m ~ b') ++ Θ1' /\
    abind_marker b' /\
    κ' ∷ Θ0' ⊑ Θ1' /\
    (is_id_msubst κ -> is_id_msubst κ').
Proof.
  intros Θs κ Θt H.
  induction H; intros Ξ0 m bm Θ0' Heq Hm.
  - (* empty : source nil cannot carry the marker *)
    exfalso. destruct Ξ0; simpl in Heq; discriminate Heq.
  - (* flex : peel one source entry *)
    destruct Ξ0 as [ | [y c] Ξ0' ]; simpl in Heq; inversion Heq; subst.
    + (* the marker would be the flex entry — not a marker *)
      simpl in Hm. contradiction.
    + destruct (IHa_inc _ _ _ _ eq_refl Hm)
        as [Ξ1 [b' [Θ1' [κ' [-> [Hm' [Hinc' Hid']]]]]]].
      exists Ξ1, b', Θ1', κ'.
      repeat split; auto.
      intros Hid. apply Hid'.
      eapply proj2, is_id_msubst_inv; eauto.
  - (* flex_def *)
    destruct Ξ0 as [ | [y c] Ξ0' ]; simpl in Heq; inversion Heq; subst.
    + simpl in Hm. contradiction.
    + destruct (IHa_inc _ _ _ _ eq_refl Hm)
        as [Ξ1 [b' [Θ1' [κ' [-> [Hm' [Hinc' Hid']]]]]]].
      exists Ξ1, b', Θ1', κ'.
      repeat split; auto.
      intros Hid. apply Hid'.
      eapply proj2, is_id_msubst_inv; eauto.
  - (* var : source head is a term-typ entry *)
    destruct Ξ0 as [ | [y c] Ξ0' ]; simpl in Heq; inversion Heq; subst.
    + (* the marker IS this entry: the rule's shape is the split *)
      exists Ξ, (abind_var_typ A'), Θ', κ.
      repeat split; simpl; auto.
    + (* marker below: recurse, then extend the above-region *)
      destruct (IHa_inc _ _ _ _ eq_refl Hm)
        as [Ξ1 [b' [Θ1' [κ' [Heq' [Hm' [Hinc' Hid']]]]]]].
      rewrite Heq'.
      exists (Ξ ++ (y ~ abind_var_typ A') ++ Ξ1), b', Θ1', κ'.
      simpl_env. repeat split; auto.
  - (* var_skl *)
    destruct Ξ0 as [ | [y c] Ξ0' ]; simpl in Heq; inversion Heq; subst.
    + exists Ξ, (abind_var_skl P'), Θ', κ.
      repeat split; simpl; auto.
    + destruct (IHa_inc _ _ _ _ eq_refl Hm)
        as [Ξ1 [b' [Θ1' [κ' [Heq' [Hm' [Hinc' Hid']]]]]]].
      rewrite Heq'.
      exists (Ξ ++ (y ~ abind_var_skl P') ++ Ξ1), b', Θ1', κ'.
      simpl_env. repeat split; auto.
  - (* tvar *)
    destruct Ξ0 as [ | [y c] Ξ0' ]; simpl in Heq; inversion Heq; subst.
    + exists Ξ, abind_tvar, Θ', κ.
      repeat split; simpl; auto.
    + destruct (IHa_inc _ _ _ _ eq_refl Hm)
        as [Ξ1 [b' [Θ1' [κ' [Heq' [Hm' [Hinc' Hid']]]]]]].
      rewrite Heq'.
      exists (Ξ ++ (y ~ abind_tvar) ++ Ξ1), b', Θ1', κ'.
      simpl_env. repeat split; auto.
Qed.

(** The transport that carries most cases of the walk: under an IDENTITY
    increase, an atom of the SOURCE that surfaces above the marker in the
    target was already above the marker in the source. *)
Lemma a_inc_marker_transport : forall Θs κ Θt Ξ0 m b Θ0' Ξ1 b' Θ1' γ,
  κ ∷ Θs ⊑ Θt ->
  is_id_msubst κ ->
  Θs = Ξ0 ++ (m ~ b) ++ Θ0' ->
  abind_marker b ->
  Θt = Ξ1 ++ (m ~ b') ++ Θ1' ->
  uniq Θt ->
  γ `in` dom Θs ->
  γ `in` dom Ξ1 ->
  γ `in` dom Ξ0.
Proof.
  intros Θs κ Θt Ξ0 m b Θ0' Ξ1 b' Θ1' γ Hinc Hid Heqs Hm Heqt Huq Hs Ht.
  subst Θs.
  destruct (a_inc_marker_mid Hinc _ _ _ _ eq_refl Hm)
    as [Ξ1x [bx [Θ1x [κ' [Heqtx [Hmx [Hinc' Hid']]]]]]].
  (* the two target splits agree: the marker occurs once (uniq) *)
  rewrite Heqtx in Heqt.
  destruct (uniq_mid_eq Heqt ltac:(rewrite <- Heqtx; exact Huq))
    as [-> [-> ->]].
  pose proof (a_inc_id_dom_sub_scope Hinc' (Hid' Hid)) as Hsub.
  rewrite !dom_app in Hs. simpl in Hs.
  rewrite Heqtx in Huq.
  (* γ above in the target: γ ∉ dom((m)++Θ1') by uniq *)
  assert (Hnb : γ `notin` add m (dom Θ1')).
  { clear - Huq Ht.
    destruct_uniq. unfold disjoint in *. simpl_env in *. fsetdec. }
  (* so γ is not m and not below in the source either *)
  assert (Hn0 : γ `notin` dom Θ0')
    by (clear - Hnb Hsub; fsetdec).
  clear - Hs Hnb Hn0. fsetdec.
Qed.

(** THE RELATIVIZED RIGIDITY: every core atom bound ABOVE the marker is a
    rigid type variable.  ([core_rigid] is this at [m] below everything.)
    Flex-Assign is the one row that needs it: the walked definition's
    variable sits at the context head — above any marker — so a core atom
    there would have to be BOTH rigid and flexibly defined. *)
Definition core_rigid_above (m : atom) (Θ : aenv) (C : ptyp) : Prop :=
  forall γ, γ `in` ftvar_in_ptyp C ->
            γ `in` above_dom m Θ ->
            binds γ abind_tvar Θ.

(* ===================================================================== *)
(*  Suffixes carry no rigid variable — the fact that turns the scope      *)
(*  conclusion into the check rows' premise (2).                          *)
(* ===================================================================== *)

(** A rigid atom of the OUTPUT that lies in the discarded suffix is
    impossible: the suffix binds it flexibly, and [uniq] makes that its
    only binding. *)
Lemma suffix_no_rigid_mid : forall Ξ m (b : abind) Θ γ,
  a_suffix Ξ ->
  uniq (Ξ ++ (m ~ b) ++ Θ) ->
  γ `in` dom Ξ ->
  ~ binds γ abind_tvar (Ξ ++ (m ~ b) ++ Θ).
Proof.
  intros Ξ m b Θ γ Hsuf Hu Hd Hb.
  destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | Hbrest].
  - eapply a_suffix_no_tvar; eassumption.
  - (* γ is in dom Ξ AND bound below it — [uniq] forbids that *)
    apply binds_In in Hbrest.
    clear - Hu Hd Hbrest.
    destruct_uniq. unfold disjoint in *. simpl_env in *. fsetdec.
Qed.

(** ⊴ versions of the marker kit (the witness is the identity increase
    [a_isub] packages). *)
Lemma a_isub_marker_mid : forall Θs Θt Ξ0 m (b : abind) Θ0',
  Θs ⊴ Θt ->
  Θs = Ξ0 ++ (m ~ b) ++ Θ0' ->
  abind_marker b ->
  exists Ξ1 b' Θ1',
    Θt = Ξ1 ++ (m ~ b') ++ Θ1' /\ abind_marker b'.
Proof.
  intros Θs Θt Ξ0 m b Θ0' [[κ [Hid Hinc]] _] Heqs Hm.
  destruct (a_inc_marker_mid Hinc _ _ _ _ Heqs Hm)
    as [Ξ1 [b' [Θ1' [κ' [-> [Hm' _]]]]]].
  eauto.
Qed.

Lemma a_isub_marker_transport : forall Θs Θt Ξ0 m (b : abind) Θ0' Ξ1 b' Θ1' γ,
  Θs ⊴ Θt ->
  Θs = Ξ0 ++ (m ~ b) ++ Θ0' ->
  abind_marker b ->
  Θt = Ξ1 ++ (m ~ b') ++ Θ1' ->
  uniq Θt ->
  γ `in` dom Θs ->
  γ `in` dom Ξ1 ->
  γ `in` dom Ξ0.
Proof.
  intros Θs Θt Ξ0 m b Θ0' Ξ1 b' Θ1' γ [[κ [Hid Hinc]] _] Heqs Hm Heqt
         Huq Hs Ht.
  eapply a_inc_marker_transport;
    [ exact Hinc | exact Hid | exact Heqs | exact Hm | exact Heqt
    | exact Huq | exact Hs | exact Ht ].
Qed.

(** THE BRIDGE: the flat region IS the positional prefix. *)
Lemma above_dom_split : forall Θ m (b : abind),
  binds m b Θ ->
  uniq Θ ->
  exists Ξ Θ', Θ = Ξ ++ (m ~ b) ++ Θ' /\ dom Ξ [=] above_dom m Θ.
Proof.
  intros Θ; induction Θ as [ | [y c] Θ' IH ]; intros m b Hb Hu;
    [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Hey Heb] | Hb'].
  - subst y c. exists nil, Θ'. simpl.
    destruct (m == m) as [_ | Hc]; [ | exfalso; auto ].
    split; [ reflexivity | clear; fsetdec ].
  - assert (Hne : y <> m).
    { intros ->. apply binds_In in Hb'.
      clear - Hu Hb'. solve_uniq. }
    inversion Hu; subst.
    destruct (IH _ _ Hb' ltac:(assumption)) as [Ξ [Θ'' [-> Hdom]]].
    exists ((y ~ c) ++ Ξ), Θ''.
    split; [ reflexivity | ].
    simpl. destruct (y == m) as [-> | _]; [ exfalso; auto | ].
    clear - Hdom; fsetdec.
Qed.

(** ⊴ carries [core_rigid_above] forward: an old core atom that is above
    the marker in the target was above it in the source (marker
    transport), where the hypothesis makes it rigid — and rigidity itself
    survives ⊴ ([a_isub_binds_tvar]). *)
Lemma core_rigid_above_isub : forall m (b : abind) Θ0 Θ1 C,
  Θ0 ⊴ Θ1 ->
  binds m b Θ0 ->
  abind_marker b ->
  uniq Θ0 ->
  uniq Θ1 ->
  ftvar_in_ptyp C [<=] dom Θ0 ->
  core_rigid_above m Θ0 C ->
  core_rigid_above m Θ1 C.
Proof.
  intros m b Θ0 Θ1 C Hle Hbm Hmk Hu0 Hu1 Hftv Hcr.
  intros γ Hγ Hab1.
  (* the marker persists, and the target's region is a positional prefix *)
  destruct (@above_dom_split Θ0 m b Hbm Hu0) as [Ξ0 [Θ0' [Heq0 Hdom0]]].
  destruct (@a_isub_marker_mid Θ0 Θ1 Ξ0 m b Θ0' Hle Heq0 Hmk)
    as [Ξ1 [b' [Θ1' [Heq1 Hmk']]]].
  assert (Hd1 : dom Ξ1 [=] above_dom m Θ1).
  { assert (Hbm1 : binds m b' Θ1)
      by (rewrite Heq1; apply binds_app_3; apply binds_app_2;
          unfold binds; simpl; auto).
    destruct (@above_dom_split Θ1 m b' Hbm1 Hu1) as [Ξ1x [Θ1x [Heq1x Hdom1x]]].
    rewrite Heq1 in Heq1x.
    destruct (uniq_mid_eq Heq1x ltac:(rewrite <- Heq1; exact Hu1))
      as [HeqΞ [_ _]].
    rewrite HeqΞ. exact Hdom1x. }
  (* transport the atom back to the source's region *)
  assert (Hab0 : γ `in` dom Ξ0).
  { eapply a_isub_marker_transport;
      [ exact Hle | exact Heq0 | exact Hmk | exact Heq1 | exact Hu1
      | clear - Hγ Hftv; fsetdec
      | clear - Hab1 Hd1; fsetdec ]. }
  eapply a_isub_binds_tvar; [ exact Hle | ].
  apply Hcr; [ exact Hγ | clear - Hab0 Hdom0; fsetdec ].
Qed.

(** A marker entry survives ⊴ as a BINDING (the [binds] form the walk's
    recursive calls need, beside the positional [a_isub_marker_mid]). *)
Lemma a_isub_binds_marker : forall Θ0 Θ1 m (b : abind),
  Θ0 ⊴ Θ1 ->
  binds m b Θ0 ->
  abind_marker b ->
  uniq Θ0 ->
  exists b', binds m b' Θ1 /\ abind_marker b'.
Proof.
  intros Θ0 Θ1 m b Hle Hbm Hmk Hu.
  destruct (@above_dom_split Θ0 m b Hbm Hu) as [Ξ0 [Θ0' [Heq0 _]]].
  destruct (@a_isub_marker_mid Θ0 Θ1 Ξ0 m b Θ0' Hle Heq0 Hmk)
    as [Ξ1 [b' [Θ1' [Heq1 Hmk']]]].
  exists b'. split; [ | exact Hmk' ].
  rewrite Heq1. apply binds_app_3. apply binds_app_2.
  unfold binds; simpl; auto.
Qed.

(** The OUTPUT core's atoms are the result's. *)
Lemma ptyp_ty_core_ftv : forall M A C,
  ptyp_ty_core M A C -> ftvar_in_ptyp C [<=] ftvar_in_ptyp A.
Proof.
  intros M A C H; induction H; simpl;
    [ clear; fsetdec | clear - IHptyp_ty_core; fsetdec ].
Qed.

(** A core atom of the input skeleton lives in the input context. *)
Lemma core_ftv_dom : forall M P0 C Θ,
  pskl_ty_core M P0 C ->
  {{ Θ ⨟ empty ⊢ₚₛ P0 }}a ->
  ftvar_in_ptyp C [<=] dom Θ.
Proof.
  intros M P0 C Θ Hcore Hwf.
  pose proof (pskl_ty_core_ftv Hcore) as H1.
  pose proof (prop_soundness_consis.a_wf_pskl_ftv_dom Hwf) as H2.
  clear - H1 H2; fsetdec.
Qed.

(** Growing the context with FRESH entries on top leaves the condition
    intact (a core atom is old, so the region it sits in is unchanged). *)
Lemma core_rigid_above_weaken_fresh : forall m Ξ Θ C,
  core_rigid_above m Θ C ->
  ftvar_in_ptyp C [<=] dom Θ ->
  m `notin` dom Ξ ->
  (forall γ, γ `in` dom Ξ -> γ `notin` dom Θ) ->
  core_rigid_above m (Ξ ++ Θ) C.
Proof.
  intros m Ξ Θ C Hcr Hftv Hm Hfr γ Hγ Hab.
  assert (HγΘ : γ `in` dom Θ) by (clear - Hγ Hftv; fsetdec).
  rewrite (@above_dom_app_notin m Ξ Θ Hm) in Hab.
  assert (HγΞ : γ `notin` dom Ξ) by (intros Hc; exact (Hfr γ Hc HγΘ)).
  apply binds_app_3.
  apply Hcr; [ exact Hγ | clear - Hab HγΞ; fsetdec ].
Qed.

(** Dropping a whole PREFIX the core cannot reach — the form the check
    rows' discarded suffix needs (their premise (2) is exactly the third
    hypothesis). *)
Lemma core_rigid_above_strip_prefix : forall m Ξ Θ C,
  core_rigid_above m (Ξ ++ Θ) C ->
  m `notin` dom Ξ ->
  (forall γ, γ `in` ftvar_in_ptyp C -> γ `notin` dom Ξ) ->
  core_rigid_above m Θ C.
Proof.
  intros m Ξ Θ C Hcr Hm Hd γ Hγ Hab.
  assert (Hab' : γ `in` above_dom m (Ξ ++ Θ))
    by (rewrite (@above_dom_app_notin m Ξ Θ Hm); clear - Hab; fsetdec).
  pose proof (Hcr γ Hγ Hab') as Hb.
  destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | Hb'];
    [ exfalso; apply binds_In in HbΞ; exact (Hd γ Hγ HbΞ) | exact Hb' ].
Qed.

(** The two components of an arrow core. *)
Lemma core_rigid_above_arrow : forall m Θ A B,
  core_rigid_above m Θ A ->
  core_rigid_above m Θ B ->
  core_rigid_above m Θ (ptyp_arrow A B).
Proof.
  intros m Θ A B HA HB γ Hγ Hab. simpl in Hγ.
  destruct (union_1 Hγ) as [Hc | Hc]; [ apply HA | apply HB ]; assumption.
Qed.

(** The marker's OWN region is empty: when the walk re-attaches the very
    entry the marker names, nothing sits above it. *)
Lemma core_rigid_above_head_marker : forall m (b : abind) Θ C,
  core_rigid_above m ((m ~ b) ++ Θ) C.
Proof.
  intros m b Θ C γ Hγ Hab.
  rewrite (@above_dom_cons_marker m b Θ) in Hab.
  exfalso. clear - Hab; fsetdec.
Qed.

(** Re-attaching a NON-marker head: the atoms above the marker grow by
    that head only, so a core atom that misses it is unaffected. *)
Lemma core_rigid_above_cons_other : forall m y (b : abind) Θ C,
  core_rigid_above m Θ C ->
  y <> m ->
  y `notin` ftvar_in_ptyp C ->
  core_rigid_above m ((y ~ b) ++ Θ) C.
Proof.
  intros m y b Θ C Hcr Hne Hy γ Hγ Hab.
  rewrite (@above_dom_cons_other m y b Θ Hne) in Hab.
  assert (Hγy : γ <> y) by (intros ->; clear - Hy Hγ; fsetdec).
  apply binds_cons_3.
  apply Hcr; [ exact Hγ | clear - Hab Hγy; fsetdec ].
Qed.

(** Dropping middle entries the marker is not among can only shrink the
    region — the converse of [above_dom_insert_sub], and the direction the
    walk's peeling rows consume. *)
Lemma above_dom_drop_sub : forall m Θa E Θb,
  m `notin` dom E ->
  above_dom m (Θa ++ Θb) [<=] above_dom m (Θa ++ E ++ Θb).
Proof.
  intros m Θa; induction Θa as [ | [y c] Θa' IH ]; intros E Θb Hm; simpl.
  - induction E as [ | [z d] E' IHE ]; simpl.
    + clear; fsetdec.
    + simpl in Hm.
      destruct (z == m) as [-> | Hne]; [ exfalso; clear - Hm; fsetdec | ].
      pose proof (IHE ltac:(clear - Hm; solve_notin_auto)) as Hrec.
      clear - Hrec; fsetdec.
  - destruct (y == m) as [-> | Hne]; [ clear; fsetdec | ].
    pose proof (IH E Θb Hm) as Hrec. clear - Hrec; fsetdec.
Qed.

(** The marker is never the entry a flex row peels: a peeled entry is
    flexible, and [uniq] makes the marker's binding unique. *)
Lemma marker_neq_nonmarker_mid : forall Ξ y (c : abind) Θ m (b : abind),
  binds m b (Ξ ++ (y ~ c) ++ Θ) ->
  abind_marker b ->
  ~ abind_marker c ->
  uniq (Ξ ++ (y ~ c) ++ Θ) ->
  y <> m.
Proof.
  intros Ξ y c Θ m b Hbm Hmk Hnc Hu ->.
  assert (Hbc : binds m c (Ξ ++ (m ~ c) ++ Θ))
    by (apply binds_app_3; apply binds_app_2; unfold binds; simpl; auto).
  assert (b = c) by (eapply binds_unique; [ exact Hbm | exact Hbc | exact Hu ]).
  subst c. exact (Hnc Hmk).
Qed.

(** Peeling a MIDDLE entry — the form the flex walk's five [Skip]/[Depend]
    rows need ([core_rigid_above_strip_head] is the [Ξ = nil] case).  The
    region can only shrink ([above_dom_drop_sub]); rigidity survives as
    long as no CORE atom is the peeled entry itself, which is what the
    third premise says.  At a flexible or term entry that is automatic (the
    bindings differ by constructor); at [Flex-SkipRigid] it is the rule's
    own [β ∉ ftvar_in_pskl P0]. *)
Lemma core_rigid_above_strip_mid : forall m Ξ y (b : abind) Θ C,
  core_rigid_above m (Ξ ++ (y ~ b) ++ Θ) C ->
  y <> m ->
  (forall γ, γ `in` ftvar_in_ptyp C ->
             binds γ abind_tvar (Ξ ++ (y ~ b) ++ Θ) ->
             (γ, abind_tvar) <> (y, b)) ->
  core_rigid_above m (Ξ ++ Θ) C.
Proof.
  intros m Ξ y b Θ C Hcr Hne Hd γ Hγ Hab.
  assert (Hab' : γ `in` above_dom m (Ξ ++ (y ~ b) ++ Θ)).
  { assert (Hsub : above_dom m (Ξ ++ Θ)
                     [<=] above_dom m (Ξ ++ (y ~ b) ++ Θ))
      by (apply above_dom_drop_sub; simpl; clear - Hne; fsetdec).
    clear - Hab Hsub; fsetdec. }
  pose proof (Hcr γ Hγ Hab') as Hb.
  eapply binds_strip_mid; [ exact Hb | exact (Hd γ Hγ Hb) ].
Qed.

(** The core follows a substitution of the input skeleton.  ([pskl_ty_core_subst]
    is the special case where the substituted variable misses the core;
    [Flex-Assign] needs the general form, because under
    [core_rigid_above] a core atom BELOW the marker may legitimately be a
    defined flexible.) *)
Lemma pskl_ty_core_subst_gen : forall M P C τ β,
  pskl_ty_core M P C ->
  pskl_ty_core M (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
                 (subst_ptyp_in_ptyp τ β C).
Proof.
  intros M P C τ β H; induction H; simpl.
  - rewrite <- ptyp_to_pskl_subst. apply pskl_ty_core__tc.
  - apply pskl_ty_core__fn. exact IHpskl_ty_core.
Qed.

(** When the marker lies in the PREFIX, the region is confined to it. *)
Lemma above_dom_app_in : forall m Ξ Θ,
  m `in` dom Ξ ->
  above_dom m (Ξ ++ Θ) [<=] dom Ξ.
Proof.
  intros m Ξ; induction Ξ as [ | [y c] Ξ' IH ]; intros Θ Hm; simpl in *.
  - exfalso. clear - Hm; fsetdec.
  - destruct (y == m) as [-> | Hne]; [ clear; fsetdec | ].
    assert (Hm' : m `in` dom Ξ') by (clear - Hm Hne; fsetdec).
    pose proof (IH Θ Hm') as Hrec. clear - Hrec; fsetdec.
Qed.

(* ===================================================================== *)
(*  ⭐ THE REGION WALK over assignment / unification / consistency.        *)
(* ===================================================================== *)

(** WHY THIS IS NEEDED — the fact [a_split__flex] needs, and the one place
    output well-formedness is NOT enough.

    The [_base] check rows split their input TYPE, and [a_split__flex] IS
    reachable at TC ([a_split_ty_shape], pat/prop_soundness_pat.v): it
    invents TWO FRESH FLEXIBLES on TOP of the context — hence ABOVE any
    marker — and only the assignment brings them back down
    ([Assign-Depend] parks them in the pending suffix, which
    [Assign-SolveM] deposits AT THE SUBJECT'S ENTRY).  When the subject is
    at-or-below the marker, so is everything deposited there.

    ⚠️ Output well-formedness alone does NOT see this.  It covers only the
    [Assign-SolveM] shape, where the subject's new definition IS the
    invented pair and wf scopes a definition below its own entry.  The
    moment the walk meets an already DEFINED flexible, [a_assign__assign]
    merges the pending suffix into a recursive CONSISTENCY run and the
    subject's binding never mentions the pair at all — so their position
    has to be proved, not read off the context.

    THE INVARIANT, and why almost every row is vacuous.  Fix a marker [m]
    and require the assignment's SUBJECT to be at-or-below it.  Then
      (1) the above-marker region never grows, and
      (2) every UNDEFINED flexible the payload names ends up at-or-below
          the marker.
    (2) is exactly what discharges (1) in the [Assign-Assign] row, where
    the pending suffix has been merged into the context.  The rows that
    match the subject's own entry at the context head are EXCLUDED — with
    the marker still in the context, a head subject is above it — and the
    rows that peel the marker itself are VACUOUS, because the output
    re-attaches [m] at the head where [above_dom m] is empty.

    ⭐ AND THE CONSISTENCY MOTIVE IS SPECIALIZED TO A VARIABLE SUBJECT
    WITH A NON-VARIABLE PAYLOAD — the only shape [a_assign__assign] can
    hand it.  Thirteen of the fourteen consistency rows then die on the
    subject's shape, on the payload's, or on their own [a_non_flex]
    premise, and [a_unify] is never reached at all (its motive is [True]). *)

Definition pskl_nonvar (P : pskl) : Prop := forall γ, P <> pskl_var_f γ.

Lemma pskl_nonvar_subst : forall ψ β P,
  pskl_nonvar P -> pskl_nonvar (subst_pskl_in_pskl ψ β P).
Proof.
  intros ψ β P Hne γ; destruct P; simpl; try discriminate.
  exfalso; exact (Hne _ eq_refl).
Qed.

(** The marker is never the entry at the context HEAD when that entry is
    not a marker — the [Ξ = nil] instance of [marker_neq_nonmarker_mid],
    which every peeling row of the walk uses. *)
Lemma marker_neq_head : forall y (c : abind) Θ m (b : abind),
  binds m b ((y ~ c) ++ Θ) ->
  abind_marker b ->
  ~ abind_marker c ->
  uniq ((y ~ c) ++ Θ) ->
  y <> m.
Proof.
  intros y c Θ m b Hbm Hmk Hnc Hu ->.
  destruct (binds_cons_1 _ _ _ _ _ _ Hbm) as [[_ ->] | Hb'];
    [ exact (Hnc Hmk) | ].
  apply binds_In in Hb'. clear - Hu Hb'. solve_uniq.
Qed.

(** A non-marker head IS above the marker — the exclusion the two
    subject-at-the-head rows ([Assign-SolveM], [Assign-UnivGhost-Id]) rest
    on. *)
Lemma above_dom_head_in : forall m y (b : abind) Θ,
  y <> m -> y `in` above_dom m ((y ~ b) ++ Θ).
Proof.
  intros m y b Θ Hne.
  rewrite (@above_dom_cons_other m y b Θ Hne). clear; fsetdec.
Qed.

(** Re-attaching the same non-marker head on both sides is monotone. *)
Lemma above_dom_cons_mono : forall m y (b : abind) Θa Θb,
  y <> m ->
  above_dom m Θa [<=] above_dom m Θb ->
  above_dom m ((y ~ b) ++ Θa) [<=] above_dom m ((y ~ b) ++ Θb).
Proof.
  intros m y b Θa Θb Hne Hsub.
  rewrite (@above_dom_cons_other m y b Θa Hne).
  rewrite (@above_dom_cons_other m y b Θb Hne).
  clear - Hsub; fsetdec.
Qed.

Definition assign_region_concl (Θ0 Ξ : aenv) (α : atom) (P : pskl)
    (Θ1 : aenv) : Prop :=
  forall m (b : abind),
    binds m b Θ0 -> abind_marker b ->
    uniq (Ξ ++ Θ0) ->
    a_decls Ξ ->
    (forall γ, γ `in` dom Ξ -> γ `in` ftvar_in_pskl P) ->
    α `notin` above_dom m Θ0 ->
    pskl_nonvar P ->
    above_dom m Θ1 [<=] above_dom m Θ0 /\
    (forall γ, γ `in` ftvar_in_pskl P -> binds γ abind_flex_mono Θ0 ->
               γ `notin` above_dom m Θ1).

Definition consis_region_concl (Θ0 : aenv) (P0 P : pskl) (Θ1 : aenv) : Prop :=
  forall m (b : abind) α,
    binds m b Θ0 -> abind_marker b ->
    uniq Θ0 ->
    P = pskl_var_f α ->
    a_flex_tvar Θ0 α ->
    α `notin` above_dom m Θ0 ->
    pskl_nonvar P0 ->
    above_dom m Θ1 [<=] above_dom m Θ0 /\
    (forall γ, γ `in` ftvar_in_pskl P0 -> binds γ abind_flex_mono Θ0 ->
               γ `notin` above_dom m Θ1).

Lemma a_assign_unify_consis_region :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> assign_region_concl Θ0 Ξ α P Θ1) /\
  (forall Θ0 α β Θ1, {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> True) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
     consis_region_concl Θ0 P0 P Θ1).
Proof.
  apply a_assign_unify_consis_mutind;
    unfold assign_region_concl, consis_region_concl.
  - (* Assign-UnivGhost-Id : the subject IS the head, hence ABOVE [m] *)
    intros Θ0 α m b Hbm Hmk Huq Hdec HdΞ Hnab Hnv.
    exfalso. apply Hnab. apply above_dom_head_in.
    eapply marker_neq_head;
      [ exact Hbm | exact Hmk | simpl; auto
      | simpl_env in Huq; exact Huq ].
  - (* Assign-SolveM : same exclusion *)
    intros Θ0 Ξ α P βs τ Hnα Hg Hm Hu Hfr m b Hbm Hmk Huq Hdec HdΞ Hnab Hnv.
    exfalso. apply Hnab. apply above_dom_head_in.
    eapply marker_neq_head;
      [ exact Hbm | exact Hmk | simpl; auto
      | clear - Huq; simpl_env in Huq; solve_uniq ].
  - (* ⭐ Assign-Assign : the pending suffix is MERGED into a recursive
       consistency run, and part (2) is what expels it again *)
    intros Θ0 Θ1 Ξ α β τ P Q Hflex Hβ1 Hc IH m b Hbm Hmk Huq Hdec HdΞ
           Hnab Hnv.
    assert (Huq0 : uniq ((β ~ abind_flex_mono_def τ) ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Hβm : β <> m)
      by (eapply marker_neq_head;
            [ exact Hbm | exact Hmk | simpl; auto | exact Huq0 ]).
    assert (Hbm0 : binds m b Θ0)
      by (destruct (binds_cons_1 _ _ _ _ _ _ Hbm) as [[Hem _] | Hb'];
            [ exfalso; apply Hβm; symmetry; exact Hem | exact Hb' ]).
    rewrite (@above_dom_cons_other m β (abind_flex_mono_def τ) Θ0 Hβm)
      in Hnab.
    assert (Hαβ : α <> β) by (intros ->; clear - Hnab; fsetdec).
    assert (HuqΞ : uniq (Ξ ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (HβΞ : β `notin` dom Ξ)
      by (clear - Huq; simpl_env in Huq; destruct_uniq;
          unfold disjoint in *; simpl_env in *; fsetdec).
    assert (HmΞ : m `notin` dom Ξ)
      by (apply binds_In in Hbm0; clear - Huq Hbm0; simpl_env in Huq;
          destruct_uniq; unfold disjoint in *; simpl_env in *; fsetdec).
    assert (Hαdom : α `in` dom Θ0).
    { destruct Hflex as [Hb | [τ0 Hb]];
        (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Hem _] | Hb'];
           [ exfalso; apply Hαβ; exact Hem
           | apply binds_In in Hb'; exact Hb' ]). }
    assert (Hflex' : a_flex_tvar (Ξ ++ Θ0) α).
    { destruct Hflex as [Hb | [τ0 Hb]];
        [ left | right; exists τ0 ];
        (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Hem _] | Hb'];
           [ exfalso; apply Hαβ; exact Hem | apply binds_app_3; exact Hb' ]). }
    assert (HαΞ : α `notin` dom Ξ)
      by (clear - HuqΞ Hαdom; destruct_uniq; unfold disjoint in *; fsetdec).
    assert (Hnab' : α `notin` above_dom m (Ξ ++ Θ0))
      by (rewrite (@above_dom_app_notin m Ξ Θ0 HmΞ);
          clear - Hnab HαΞ; fsetdec).
    assert (Hsubj : subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)
                      = pskl_var_f α)
      by (apply subst_pskl_in_pskl_fresh_eq; simpl; clear - Hαβ; fsetdec).
    destruct (IH m b α ltac:(apply binds_app_3; exact Hbm0) Hmk HuqΞ Hsubj
                Hflex' Hnab' (pskl_nonvar_subst _ _ Hnv))
      as [Hreg Hsafe].
    (* the deposited names occur in the payload and are undefined
       flexibles, so part (2) puts them at-or-below the marker *)
    assert (HΞsafe : forall γ, γ `in` dom Ξ ->
                       γ `notin` above_dom m Θ1).
    { intros γ Hγ.
      assert (HγP : γ `in` ftvar_in_pskl P) by (exact (HdΞ γ Hγ)).
      apply Hsafe.
      - pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower
                      P (ptyp_to_pskl τ) β) as Hlow.
        assert (Hγβ : γ <> β) by (intros ->; clear - Hγ HβΞ; fsetdec).
        clear - HγP Hγβ Hlow; fsetdec.
      - assert (Hγd : γ `in` dom Ξ) by exact Hγ.
        apply binds_In_inv in Hγd. destruct Hγd as [c Hbc].
        rewrite (@a_decls_binds_flex Ξ γ c Hdec Hbc) in Hbc.
        apply binds_app_2; exact Hbc. }
    assert (Hreg0 : above_dom m Θ1 [<=] above_dom m Θ0).
    { intros γ Hγ.
      rewrite (@above_dom_app_notin m Ξ Θ0 HmΞ) in Hreg.
      destruct (AtomSetProperties.In_dec γ (dom Ξ)) as [Hi | Hi];
        [ exfalso; exact (HΞsafe γ Hi Hγ) | clear - Hγ Hreg Hi; fsetdec ]. }
    split.
    + apply above_dom_cons_mono; [ exact Hβm | exact Hreg0 ].
    + intros γ Hγ Hbγ.
      assert (Hγβ : γ <> β)
        by (intros ->;
            destruct (binds_cons_1 _ _ _ _ _ _ Hbγ) as [[_ He] | Hb'];
              [ discriminate He
              | apply binds_In in Hb'; clear - Huq0 Hb'; solve_uniq ]).
      assert (Hbγ0 : binds γ abind_flex_mono (Ξ ++ Θ0))
        by (destruct (binds_cons_1 _ _ _ _ _ _ Hbγ) as [[Hem _] | Hb'];
              [ exfalso; apply Hγβ; exact Hem
              | apply binds_app_3; exact Hb' ]).
      assert (Hnot : γ `notin` above_dom m Θ1).
      { apply Hsafe; [ | exact Hbγ0 ].
        pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower
                      P (ptyp_to_pskl τ) β) as Hlow.
        clear - Hγ Hγβ Hlow; fsetdec. }
      rewrite (@above_dom_cons_other m β (abind_flex_mono_def τ) Θ1 Hβm).
      clear - Hnot Hγβ; fsetdec.
  - (* Assign-Depend : the head joins the pending suffix; the recursion's
       region lives in the TAIL, where the head no longer occurs *)
    intros Θ0 Θ1 Ξ α β P Hne Hin Ha IH m b Hbm Hmk Huq Hdec HdΞ Hnab Hnv.
    assert (Huq0 : uniq ((β ~ abind_flex_mono) ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Hβm : β <> m)
      by (eapply marker_neq_head;
            [ exact Hbm | exact Hmk | simpl; auto | exact Huq0 ]).
    assert (Hbm0 : binds m b Θ0)
      by (destruct (binds_cons_1 _ _ _ _ _ _ Hbm) as [[Hem _] | Hb'];
            [ exfalso; apply Hβm; symmetry; exact Hem | exact Hb' ]).
    rewrite (@above_dom_cons_other m β abind_flex_mono Θ0 Hβm) in Hnab.
    destruct (IH m b Hbm0 Hmk
                ltac:(clear - Huq; simpl_env in *; solve_uniq)
                ltac:(apply a_decls_app;
                        [ exact Hdec
                        | apply (a_decls__cons β); apply a_decls__nil ])
                ltac:(intros γ Hγ; rewrite dom_app in Hγ; simpl in Hγ;
                      destruct (AtomSetProperties.In_dec γ (dom Ξ))
                        as [Hi | Hi];
                        [ exact (HdΞ γ Hi)
                        | assert (Heγ : γ = β) by (clear - Hγ Hi; fsetdec);
                          subst γ; exact Hin ])
                ltac:(clear - Hnab; solve_notin_auto)
                Hnv)
      as [Hreg Hsafe].
    split.
    + rewrite (@above_dom_cons_other m β abind_flex_mono Θ0 Hβm).
      clear - Hreg; fsetdec.
    + intros γ Hγ Hbγ.
      destruct (γ == β) as [-> | Hγβ].
      * intros Hc.
        pose proof (above_dom_sub_dom m Θ0) as Hsd.
        assert (Hβdom : β `in` dom Θ0) by (clear - Hc Hreg Hsd; fsetdec).
        clear - Huq0 Hβdom. solve_uniq.
      * apply Hsafe; [ exact Hγ | ].
        destruct (binds_cons_1 _ _ _ _ _ _ Hbγ) as [[Hem _] | Hb'];
          [ exfalso; apply Hγβ; exact Hem | exact Hb' ].
  - (* Assign-Skip : the head is re-attached on both sides *)
    intros Θ0 Θ1 Ξ α β P Hne Hni Hβ1 Ha IH m b Hbm Hmk Huq Hdec HdΞ Hnab Hnv.
    assert (Huq0 : uniq ((β ~ abind_flex_mono) ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Hβm : β <> m)
      by (eapply marker_neq_head;
            [ exact Hbm | exact Hmk | simpl; auto | exact Huq0 ]).
    assert (Hbm0 : binds m b Θ0)
      by (destruct (binds_cons_1 _ _ _ _ _ _ Hbm) as [[Hem _] | Hb'];
            [ exfalso; apply Hβm; symmetry; exact Hem | exact Hb' ]).
    rewrite (@above_dom_cons_other m β abind_flex_mono Θ0 Hβm) in Hnab.
    destruct (IH m b Hbm0 Hmk
                ltac:(clear - Huq; simpl_env in *; solve_uniq)
                Hdec HdΞ ltac:(clear - Hnab; solve_notin_auto) Hnv)
      as [Hreg Hsafe].
    split; [ apply above_dom_cons_mono; [ exact Hβm | exact Hreg ] | ].
    intros γ Hγ Hbγ.
    assert (Hγβ : γ <> β) by (intros ->; clear - Hγ Hni; fsetdec).
    rewrite (@above_dom_cons_other m β abind_flex_mono Θ1 Hβm).
    assert (Hnot : γ `notin` above_dom m Θ1).
    { apply Hsafe; [ exact Hγ | ].
      destruct (binds_cons_1 _ _ _ _ _ _ Hbγ) as [[Hem _] | Hb'];
        [ exfalso; apply Hγβ; exact Hem | exact Hb' ]. }
    clear - Hnot Hγβ; fsetdec.
  - (* Assign-SkipRigid : the ONE row that can peel the marker — and then
       the output re-attaches it at the HEAD, where the region is empty *)
    intros Θ0 Θ1 Ξ α β P Hni Hβ1 Ha IH m b Hbm Hmk Huq Hdec HdΞ Hnab Hnv.
    destruct (β == m) as [-> | Hβm].
    { split;
        [ rewrite (@above_dom_cons_marker m abind_tvar Θ1);
          clear; fsetdec
        | intros γ Hγ Hbγ;
          rewrite (@above_dom_cons_marker m abind_tvar Θ1);
          clear; fsetdec ]. }
    assert (Hbm0 : binds m b Θ0)
      by (destruct (binds_cons_1 _ _ _ _ _ _ Hbm) as [[Hem _] | Hb'];
            [ exfalso; apply Hβm; symmetry; exact Hem | exact Hb' ]).
    rewrite (@above_dom_cons_other m β abind_tvar Θ0 Hβm) in Hnab.
    destruct (IH m b Hbm0 Hmk
                ltac:(clear - Huq; simpl_env in *; solve_uniq)
                Hdec HdΞ ltac:(clear - Hnab; solve_notin_auto) Hnv)
      as [Hreg Hsafe].
    split; [ apply above_dom_cons_mono; [ exact Hβm | exact Hreg ] | ].
    intros γ Hγ Hbγ.
    assert (Hγβ : γ <> β) by (intros ->; clear - Hγ Hni; fsetdec).
    rewrite (@above_dom_cons_other m β abind_tvar Θ1 Hβm).
    assert (Hnot : γ `notin` above_dom m Θ1).
    { apply Hsafe; [ exact Hγ | ].
      destruct (binds_cons_1 _ _ _ _ _ _ Hbγ) as [[Hem _] | Hb'];
        [ exfalso; apply Hγβ; exact Hem | exact Hb' ]. }
    clear - Hnot Hγβ; fsetdec.
  - (* Assign-SkipTmVar : a term marker — same two cases; a core atom can
       never BE it (the bindings differ by constructor) *)
    intros Θ0 Θ1 Ξ α x A P Hx1 Ha IH m b Hbm Hmk Huq Hdec HdΞ Hnab Hnv.
    destruct (x == m) as [-> | Hxm].
    { split;
        [ rewrite (@above_dom_cons_marker m (abind_var_typ A) Θ1);
          clear; fsetdec
        | intros γ Hγ Hbγ;
          rewrite (@above_dom_cons_marker m (abind_var_typ A) Θ1);
          clear; fsetdec ]. }
    assert (Hbm0 : binds m b Θ0)
      by (destruct (binds_cons_1 _ _ _ _ _ _ Hbm) as [[Hem _] | Hb'];
            [ exfalso; apply Hxm; symmetry; exact Hem | exact Hb' ]).
    rewrite (@above_dom_cons_other m x (abind_var_typ A) Θ0 Hxm) in Hnab.
    destruct (IH m b Hbm0 Hmk
                ltac:(clear - Huq; simpl_env in *; solve_uniq)
                Hdec HdΞ ltac:(clear - Hnab; solve_notin_auto) Hnv)
      as [Hreg Hsafe].
    split; [ apply above_dom_cons_mono; [ exact Hxm | exact Hreg ] | ].
    intros γ Hγ Hbγ.
    assert (Hγx : γ <> x)
      by (intros ->;
          destruct (binds_cons_1 _ _ _ _ _ _ Hbγ) as [[_ He] | Hb'];
            [ discriminate He
            | apply binds_In in Hb'; clear - Huq Hb'; simpl_env in Huq;
              solve_uniq ]).
    rewrite (@above_dom_cons_other m x (abind_var_typ A) Θ1 Hxm).
    assert (Hnot : γ `notin` above_dom m Θ1).
    { apply Hsafe; [ exact Hγ | ].
      destruct (binds_cons_1 _ _ _ _ _ _ Hbγ) as [[Hem _] | Hb'];
        [ exfalso; apply Hγx; exact Hem | exact Hb' ]. }
    clear - Hnot Hγx; fsetdec.
  - (* Assign-SkipTmVar (skeleton entry) : verbatim the previous row *)
    intros Θ0 Θ1 Ξ α x Q P Hx1 Ha IH m b Hbm Hmk Huq Hdec HdΞ Hnab Hnv.
    destruct (x == m) as [-> | Hxm].
    { split;
        [ rewrite (@above_dom_cons_marker m (abind_var_skl Q) Θ1);
          clear; fsetdec
        | intros γ Hγ Hbγ;
          rewrite (@above_dom_cons_marker m (abind_var_skl Q) Θ1);
          clear; fsetdec ]. }
    assert (Hbm0 : binds m b Θ0)
      by (destruct (binds_cons_1 _ _ _ _ _ _ Hbm) as [[Hem _] | Hb'];
            [ exfalso; apply Hxm; symmetry; exact Hem | exact Hb' ]).
    rewrite (@above_dom_cons_other m x (abind_var_skl Q) Θ0 Hxm) in Hnab.
    destruct (IH m b Hbm0 Hmk
                ltac:(clear - Huq; simpl_env in *; solve_uniq)
                Hdec HdΞ ltac:(clear - Hnab; solve_notin_auto) Hnv)
      as [Hreg Hsafe].
    split; [ apply above_dom_cons_mono; [ exact Hxm | exact Hreg ] | ].
    intros γ Hγ Hbγ.
    assert (Hγx : γ <> x)
      by (intros ->;
          destruct (binds_cons_1 _ _ _ _ _ _ Hbγ) as [[_ He] | Hb'];
            [ discriminate He
            | apply binds_In in Hb'; clear - Huq Hb'; simpl_env in Huq;
              solve_uniq ]).
    rewrite (@above_dom_cons_other m x (abind_var_skl Q) Θ1 Hxm).
    assert (Hnot : γ `notin` above_dom m Θ1).
    { apply Hsafe; [ exact Hγ | ].
      destruct (binds_cons_1 _ _ _ _ _ _ Hbγ) as [[Hem _] | Hb'];
        [ exfalso; apply Hγx; exact Hem | exact Hb' ]. }
    clear - Hnot Hγx; fsetdec.
  (* ---- [a_unify] : never reached, the motive is [True] ---- *)
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  (* ---- [a_consis] : a VARIABLE subject with a NON-VARIABLE payload ---- *)
  - (* Ghost : subject [◇] *)
    intros Δ1 Δ2 Θ0 P0 Hd m b α Hbm Hmk Huq Heq; discriminate Heq.
  - (* Unit *)
    intros Δ1 Δ2 Θ0 m b α Hbm Hmk Huq Heq; discriminate Heq.
  - (* Rigid : the PAYLOAD is a variable *)
    intros Δ1 Δ2 Θ0 α Hb m b α0 Hbm Hmk Huq Heq Hflex Hnab Hnv.
    exfalso; exact (Hnv α eq_refl).
  - (* Arrow *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2
           m b α Hbm Hmk Huq Heq; discriminate Heq.
  - (* ForallInh *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH m b α0 Hbm Hmk Huq Heq;
      discriminate Heq.
  - (* ForallSyn *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH m b α0 Hbm Hmk Huq Heq;
      discriminate Heq.
  - (* UnivGhost *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hc IH m b α Hbm Hmk Huq Heq; discriminate Heq.
  - (* UnivGhost1 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH m b α0 Hbm Hmk Huq Heq;
      discriminate Heq.
  - (* UnivGhost2 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH m b α Hbm Hmk Huq Heq;
      discriminate Heq.
  - (* Flex : the PAYLOAD is a variable *)
    intros Δ1 Δ2 Θ0 Θ1 α β Hu IHu m b α0 Hbm Hmk Huq Heq Hflex Hnab Hnv.
    exfalso; exact (Hnv β eq_refl).
  - (* ⭐ FlexL : the only live row — hand over to the assignment *)
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hnhole Ha IH m b α0 Hbm Hmk Huq Heq Hflex Hnab Hnv.
    inversion Heq; subst α0.
    apply (IH m b Hbm Hmk);
      [ simpl_env; exact Huq
      | apply a_decls__nil
      | intros γ Hγ; simpl in Hγ; clear - Hγ; fsetdec
      | exact Hnab
      | exact Hnv ].
  - (* FlexR : the PAYLOAD is a variable *)
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hnhole Ha IHa m b α0 Hbm Hmk Huq Heq Hflex Hnab Hnv.
    exfalso; exact (Hnv α eq_refl).
  - (* GhostR : the payload is [◇], with no atoms at all *)
    intros Δ1 Δ2 Θ0 P Hd m b α Hbm Hmk Huq Heq Hflex Hnab Hnv.
    split; [ clear; fsetdec | ].
    intros γ Hγ Hbγ. simpl in Hγ. exfalso; clear - Hγ; fsetdec.
  - (* UnivGhostR : the rule's own [a_non_flex] contradicts the subject's
       flexibility *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH m b α Hbm Hmk Huq Heq Hflex
           Hnab Hnv.
    subst P. exfalso. destruct Hnf as [_ Hnf]. apply Hnf.
    destruct Hflex as [Hb | [τ Hb]];
      [ apply a_flex__var; exact Hb | eapply a_flex__var_def; exact Hb ].
Qed.

(** ⭐ THE SPLIT'S SCOPE STEP — what the [_base] check rows need.

    At TC the split's input may be a bare FLEXIBLE ([a_split_ty_shape],
    pat/prop_soundness_pat.v — "at TC the row IS reachable … the whole
    asymmetry"), and then the rule invents two fresh flexibles ON TOP of
    the context, i.e. above every marker.  They are nevertheless
    at-or-below the marker in the OUTPUT: the hypothesis puts the split
    subject [α̂] at-or-below it (a core atom above the marker would be
    RIGID, and [α̂] is flexible), and the assignment deposits everything it
    parked at [α̂]'s own entry — which is what
    [a_assign_unify_consis_region] says. *)
Lemma a_split_scope : forall Θ0 A0 A B Θ1 m (b : abind),
  {{ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A) ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl A0) }}a ->
  binds m b Θ0 ->
  abind_marker b ->
  core_rigid_above m Θ0 A0 ->
  core_rigid_above m Θ1 A /\ core_rigid_above m Θ1 B.
Proof.
  intros Θ0 A0 A B Θ1 m b Hs Hwf HwfP0 Hbm Hmk Hcr.
  assert (Huq : uniq Θ0) by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HftvA0 : ftvar_in_ptyp A0 [<=] dom Θ0).
  { pose proof (prop_soundness_consis.a_wf_pskl_ftv_dom HwfP0) as Hd.
    rewrite ftvar_ptyp_to_pskl in Hd. clear - Hd; fsetdec. }
  destruct A0 as [ | n | α | A1 A2 | A1 ]; simpl in Hs; simpl in HftvA0.
  - inversion Hs.
  - inversion Hs.
  - (* ⭐ the FLEX row *)
    inversion Hs; subst.
    match goal with
    | Hc : a_consis _ _ ((?α1x ~ _) ++ (?βx ~ _) ++ _) _ _ _ _,
      HeA : _ = ptyp_to_pskl A, HeB : _ = ptyp_to_pskl B |- _ =>
        rename α1x into α1; rename βx into β;
        rename Hc into Hcons; rename HeA into HeqA; rename HeB into HeqB
    | Hc : a_consis _ _ ((?α1x ~ _) ++ (?βx ~ _) ++ _) _ _ _ _,
      HeA : ptyp_to_pskl A = _, HeB : ptyp_to_pskl B = _ |- _ =>
        rename α1x into α1; rename βx into β;
        rename Hc into Hcons; rename HeA into HeqA; rename HeB into HeqB
    end.
    match goal with
    | Hfr : β `notin` ftvar_in_aenv Θ0 |- _ => rename Hfr into Hβfr
    end.
    match goal with
    | Hfr : α1 `notin` add β (ftvar_in_aenv Θ0) |- _ => rename Hfr into Hα1fr
    end.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
    assert (Hβd : β `notin` dom Θ0) by (clear - Hβfr Hds; fsetdec).
    assert (Hα1d : α1 `notin` add β (dom Θ0)) by (clear - Hα1fr Hds; fsetdec).
    (* the split's context, and the marker inside it *)
    assert (HuqIn : uniq ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono)
                            ++ Θ0))
      by (clear - Huq Hβd Hα1d; solve_uniq).
    assert (HbmIn : binds m b ((α1 ~ abind_flex_mono)
                                ++ (β ~ abind_flex_mono) ++ Θ0))
      by (apply binds_app_3; apply binds_app_3; exact Hbm).
    (* the subject is FLEXIBLE, so the hypothesis puts it at-or-below [m] *)
    assert (Hfl : a_flex_tvar ((α1 ~ abind_flex_mono)
                                ++ (β ~ abind_flex_mono) ++ Θ0) α).
    { inversion Hcons; subst;
        match goal with
        | Ha : a_assign _ _ _ _ _ |- _ =>
            exact (a_assign_flex_tvar Ha)
        end. }
    assert (Hαd : α `in` dom Θ0) by (clear - HftvA0; fsetdec).
    assert (Hαα1 : α <> α1) by (intros ->; clear - Hαd Hα1d; fsetdec).
    assert (Hαβ : α <> β) by (intros ->; clear - Hαd Hβd; fsetdec).
    assert (Hfl0 : a_flex_tvar Θ0 α).
    { destruct Hfl as [Hb0 | [τ0 Hb0]]; [ left | right; exists τ0 ];
        (destruct (binds_cons_1 _ _ _ _ _ _ Hb0) as [[He _] | Hb1];
           [ exfalso; apply Hαα1; exact He | ];
         destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[He _] | Hb2];
           [ exfalso; apply Hαβ; exact He | exact Hb2 ]). }
    assert (Hαnab : α `notin` above_dom m Θ0).
    { intros Hc0.
      assert (Hbt : binds α abind_tvar Θ0)
        by (apply Hcr; [ simpl; clear; fsetdec | exact Hc0 ]).
      destruct Hfl0 as [Hb0 | [τ0 Hb0]];
        pose proof (binds_unique _ _ _ _ _ Hbt Hb0 Huq) as Hce;
        discriminate Hce. }
    assert (HmIn : m <> α1 /\ m <> β).
    { apply binds_In in Hbm. split; intros ->;
        [ clear - Hbm Hα1d | clear - Hbm Hβd ]; fsetdec. }
    destruct HmIn as [Hmα1 Hmβ].
    assert (HnabIn : α `notin` above_dom m ((α1 ~ abind_flex_mono)
                                              ++ (β ~ abind_flex_mono) ++ Θ0)).
    { rewrite (@above_dom_cons_other m α1 abind_flex_mono
                 ((β ~ abind_flex_mono) ++ Θ0) ltac:(auto)).
      rewrite (@above_dom_cons_other m β abind_flex_mono Θ0 ltac:(auto)).
      clear - Hαnab Hαα1 Hαβ; fsetdec. }
    destruct (proj2 (proj2 a_assign_unify_consis_region)
                _ _ _ _ _ _ _ Hcons m b α HbmIn Hmk HuqIn eq_refl Hfl
                HnabIn ltac:(intros γ; discriminate))
      as [_ Hsafe].
    (* both invented flexibles are named by the payload and undefined *)
    assert (Hβsafe : β `notin` above_dom m Θ1)
      by (apply Hsafe; [ simpl; clear; fsetdec
                       | apply binds_app_3; unfold binds; simpl; auto ]).
    assert (Hα1safe : α1 `notin` above_dom m Θ1)
      by (apply Hsafe; [ simpl; clear; fsetdec
                       | unfold binds; simpl; auto ]).
    assert (HftvA : ftvar_in_ptyp A [<=] singleton β).
    { rewrite <- ftvar_ptyp_to_pskl.
      rewrite <- HeqA. simpl. clear; fsetdec. }
    assert (HftvB : ftvar_in_ptyp B [<=] singleton α1).
    { rewrite <- ftvar_ptyp_to_pskl.
      rewrite <- HeqB. simpl. clear; fsetdec. }
    split; intros γ Hγ Hab; exfalso;
      [ assert (Heγ : γ = β) by (clear - Hγ HftvA; fsetdec)
      | assert (Heγ : γ = α1) by (clear - Hγ HftvB; fsetdec) ];
      subst γ; [ exact (Hβsafe Hab) | exact (Hα1safe Hab) ].
  - (* the ARROW row : the identity split, and both pieces are old *)
    inversion Hs; subst.
    repeat match goal with
    | Heq : ptyp_to_pskl _ = ptyp_to_pskl _ |- _ =>
        apply prop_coercions.ptyp_to_pskl_inj in Heq
    end.
    subst.
    split; intros γ Hγ Hab; apply Hcr;
      first [ exact Hab | simpl; clear - Hγ; fsetdec ].
  - inversion Hs.
Qed.

(* ===================================================================== *)
(*  ⭐ THE SUB-LEVEL SCOPE WALK.                                           *)
(* ===================================================================== *)

(** ⚠️ WHY THIS IS SCOPE PROPAGATION AND NOT CORE PRESERVATION.  The shape
    [a_sub_sub_flex_ty_core] uses (typing/prop_typing_rigidity.v:746) — the OUTPUT's core
    IS the input's — is FALSE once [core_rigid] is relaxed to
    [core_rigid_above]: [a_sub_flex__assign] SUBSTITUTES the input skeleton
    ([subst_pskl_in_pskl ⌈τ⌉ β P0], algo/def_rules.v:1300), so when the
    walked [β] is itself a core atom the core MOVES to [C[τ/β]].  The full
    [core_rigid] rules that out (a core atom is never flexible);
    [core_rigid_above] rules it out only ABOVE the marker, and a core atom
    that is a flexible BELOW the marker can legitimately be assigned
    (subject a flexible [α̂], [P0 = β̂] with [β̂ ≔ τ] bound below the marker).

    ⚠️ AND WHY THE CORE'S EXISTENCE IS MARKER-FREE, with the scope
    obligation NESTED under [forall m].  The flex walk DESCENDS PAST
    MARKERS: [a_sub_flex__skip_rigid] and [a_sub_flex__skip_tm_var/skl]
    (:1319, :1339, :1344) drop a rigid resp. term entry from the recursive
    context and re-attach it to the OUTPUT, so a marker-indexed hypothesis
    does not thread unchanged through the walk.  With the quantifier
    nested, those rows take their core from the IH (which needs no marker
    at all) and the scope goal at [m = β] is VACUOUS — the output
    re-attaches [β] at the head, where [above_dom β = ∅]
    ([core_rigid_above_head_marker]).

    Flex-Assign is then DISCHARGED, not dodged: [C' = C[τ/β]]; the atoms
    of [ftv C] other than [β] travel by [core_rigid_above_strip_mid], and
    those of [ftv τ] are harmless because [β] is at-or-below the marker
    (above it the hypothesis would make it rigid, contradicting its
    flexible binding), which confines the whole region to [dom Ξ]
    ([above_dom_app_in]) while [τ] is well-formed in [Θ0]. *)

Definition sub_scope_concl (NM : a_sub_mode) (M : mode) (P0 : pskl)
    (Θ0 : aenv) (P Q : pskl) (Θ1 : aenv) : Prop :=
  NM = a_sub_mode_ty ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  forall C, pskl_ty_core M P0 C ->
  exists C', pskl_ty_core M Q C' /\
    (forall m (b : abind),
       binds m b Θ0 -> abind_marker b ->
       core_rigid_above m Θ0 C -> core_rigid_above m Θ1 C').

Definition sub_flex_scope_concl (NM : a_sub_mode) (M : mode) (P0 : pskl)
    (Θ0 Ξ : aenv) (α : atom) (Q : pskl) (Θ1 : aenv) : Prop :=
  NM = a_sub_mode_ty ->
  {{ ⊢ (Ξ ++ Θ0) }}a ->
  a_decls Ξ ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_binds_tvar α (Ξ ++ Θ0) ->
  forall C, pskl_ty_core (mode_fn M) P0 C ->
  exists C', pskl_ty_core (mode_fn M) Q C' /\
    (forall m (b : abind),
       binds m b (Ξ ++ Θ0) -> abind_marker b ->
       core_rigid_above m (Ξ ++ Θ0) C -> core_rigid_above m Θ1 C').

(** The two Flex-SkipTmVar rows (type and skeleton entry): a marker again,
    but a TERM one — the core cannot name it (its binding is not tvarish),
    so the strip's side conditions are a binding mismatch. *)
Lemma sub_flex_scope_skip_tm : forall {NM M P0 Θ0 Θ1 Ξ α x} {bx : abind} {Q},
  x `notin` dom Θ1 ->
  a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
  sub_flex_scope_concl NM M P0 Θ0 Ξ α Q Θ1 ->
  abind_is_tm bx ->
  sub_flex_scope_concl NM M P0 ((x ~ bx) ++ Θ0) Ξ α Q ((x ~ bx) ++ Θ1).
Proof.
  intros NM M P0 Θ0 Θ1 Ξ α x bx Q Hxout Hs IH Htm Heq Hwf Hdecls HwfP0 Hbα
         C Hcore.
  assert (Hxfr : x `notin` ftvar_in_pskl P0)
    by (eapply a_wf_pskl_tm_entry_fresh; [ exact Hwf | exact Htm | exact HwfP0 ]).
  assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; eauto).
  assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hxfr ]).
  assert (Hbα' : a_binds_tvar α (Ξ ++ Θ0))
    by (eapply a_binds_tvar_strip_mid;
          [ exact Hbα
          | intros He; inversion He; subst; exact Htm
          | intros He; inversion He; subst; exact Htm
          | intros τ1 He; inversion He; subst; exact Htm ]).
  destruct (IH Heq Hwf' Hdecls HwfP0' Hbα' C Hcore)
    as [C' [Hcore' Hsc']].
  exists C'. split; [ exact Hcore' | ].
  intros m b Hbm Hmk Hcr.
  destruct (x == m) as [-> | Hxm];
    [ apply core_rigid_above_head_marker | ].
  destruct (proj2 a_sub_output_wf_bundle _ _ _ _ _ _ _ _ Hs
              Hwf' Hdecls HwfP0' Hbα') as [_ [_ HwfQ]].
  apply core_rigid_above_cons_other;
    [ eapply Hsc';
        [ eapply binds_strip_mid;
            [ exact Hbm | intros Hc; inversion Hc; subst; auto ]
        | exact Hmk
        | eapply core_rigid_above_strip_mid;
            [ exact Hcr | exact Hxm
            | intros γ0 _ _ Hc; inversion Hc; subst; exact Htm ] ]
    | exact Hxm
    | pose proof (core_ftv_dom Hcore' HwfQ) as Hsub;
      clear - Hxout Hsub; fsetdec ].
Qed.

Lemma a_sub_sub_flex_scope :
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 -> sub_scope_concl NM M P0 Θ0 P Q Θ1) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     sub_flex_scope_concl NM M P0 Θ0 Ξ α Q Θ1).
Proof.
  apply a_sub_sub_flex_tm_mutind;
    unfold sub_scope_concl, sub_flex_scope_concl.
  - (* Infer : TI has no core *)
    intros; match goal with H : pskl_ty_core _ _ _ |- _ => inversion H end.
  - (* Check : output = input, context moved by the consis run *)
    intros Θ0 Θ1 A B Hgfa Hgfb Hga Hgb Hc Heq Hwf HwfP0 HwfP C Hcore.
    exists C. split; [ exact Hcore | ]. intros m b Hbm Hmk Hcr.
    destruct Hc as [Qc Hc].
    destruct (a_consis_isub_wf_nil Hc Hwf HwfP0 HwfP) as [Hle Hwf1].
    eapply core_rigid_above_isub;
      [ exact Hle | exact Hbm | exact Hmk
      | apply a_wf_aenv_uniq; exact Hwf
      | apply a_wf_aenv_uniq; exact Hwf1
      | eapply core_ftv_dom; [ exact Hcore | exact HwfP0 ]
      | exact Hcr ].
  - (* ForallR : output = input; the run's own ⊴ strips to [Θ0 ⊴ Θ1] *)
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huq Hfr Hprem IH Heq Hwf HwfP0 HwfP
           C Hcore.
    exists C. split; [ exact Hcore | ]. intros m b Hbm Hmk Hcr.
    rewrite dom_app in Hfr.
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Hfr; fsetdec).
    destruct (proj1 a_sub_output_wf_bundle _ _ _ _ _ _ _ Hprem
                ltac:(apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ])
                ltac:(eapply a_wf_pskl_all_syn_open_tvar;
                        [ exact HwfP0
                        | clear - Hfr HαΘ0; simpl in Hfr; solve_notin_auto ])
                ltac:(eapply a_wf_pskl_delta_mono;
                        [ apply (a_wf_pskl_reassoc HwfP α) | clear; solve_notin_auto ]))
      as [Hle [Hwf1 _]].
    assert (HuqT : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ1))
      by (apply a_wf_aenv_uniq; exact Hwf1).
    assert (Hwf1' : {{ ⊢ Θ1 }}a)
      by (eapply a_wf_aenv_strip_prefix_suffix_local; exact Hwf1).
    assert (Hle0 : Θ0 ⊴ Θ1)
      by (eapply a_isub_strip_tvar_mid with (Ξ := Ξ);
            [ exact HuqT | exact Huq | exact HαΘ0 | exact Hle ]).
    eapply core_rigid_above_isub;
      [ exact Hle0 | exact Hbm | exact Hmk
      | apply a_wf_aenv_uniq; exact Hwf
      | apply a_wf_aenv_uniq; exact Hwf1'
      | eapply core_ftv_dom; [ exact Hcore | exact HwfP0 ]
      | exact Hcr ].
  - (* UnivGhostR : SK *)
    intros Θ0 P Hg Heq; discriminate Heq.
  - (* FlexMono : hand over to the flex walk at [Ξ = nil] *)
    intros NM M P0 Θ0 Θ1 α Q Hf IH Heq Hwf HwfP0 HwfP C Hcore.
    assert (Hbα : a_binds_tvar α (nil ++ Θ0)).
    { simpl_env. inversion HwfP; subst. assumption. }
    assert (Hres : exists C',
               pskl_ty_core (mode_fn M) Q C' /\
               (forall m (b : abind),
                  binds m b (nil ++ Θ0) -> abind_marker b ->
                  core_rigid_above m (nil ++ Θ0) C ->
                  core_rigid_above m Θ1 C')).
    { apply IH; try assumption. apply a_decls__nil. }
    destruct Hres as [C' [Hcore' Hsc']].
    exists C'. split; [ exact Hcore' | ].
    intros m b Hbm Hmk Hcr.
    eapply Hsc'; [ exact Hbm | exact Hmk | simpl_env; exact Hcr ].
  - (* Arrow : the core lives in the CODOMAIN; cross the consis premise *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH Heq Hwf HwfP0 HwfP
           C Hcore.
    inversion Hcore as [ | Mx Px Qx Ax Hcoreb ]; subst.
    inversion HwfP0; subst. inversion HwfP; subst.
    destruct (a_consis_isub_wf_nil Hc Hwf ltac:(eassumption) ltac:(eassumption))
      as [Hle Hwf1].
    destruct (IH eq_refl Hwf1
                ltac:(eapply a_wf_pskl_isub; [ eassumption | exact Hle ])
                ltac:(eapply a_wf_pskl_isub; [ eassumption | exact Hle ])
                C Hcoreb)
      as [C' [Hcore2 Hsc2]].
    exists C'. split; [ apply pskl_ty_core__fn; exact Hcore2 | ].
    intros m b Hbm Hmk Hcr.
    destruct (@a_isub_binds_marker Θ0 Θ1 m b Hle Hbm Hmk
                ltac:(apply a_wf_aenv_uniq; exact Hwf))
      as [b1 [Hbm1 Hmk1]].
    eapply Hsc2; [ exact Hbm1 | exact Hmk1 | ].
    eapply core_rigid_above_isub;
      [ exact Hle | exact Hbm | exact Hmk
      | apply a_wf_aenv_uniq; exact Hwf
      | apply a_wf_aenv_uniq; exact Hwf1
      | eapply core_ftv_dom; [ exact Hcoreb | eassumption ]
      | exact Hcr ].
  - (* ForallL : same [P0] and same OUTPUT; the context grows by the
       fresh [Ξ], which no old core atom can reach *)
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hne Hgor Hfr Hex Huq HwfP1 Hs IH
           Heq Hwf HwfP0 HwfP C Hcore.
    assert (Hdecls : a_decls Ξ) by (eapply a_extract_decls; eauto).
    assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a).
    { apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros γ Hγ. clear - Huq Hγ. destruct_uniq.
        unfold disjoint in *. fsetdec. }
    assert (Hmono : forall x (c : abind),
               binds x c Θ0 -> binds x c (Ξ ++ Θ0))
      by (intros x c Hb; unfold binds in *; apply in_or_app; auto).
    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
    assert (HwfSo : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ (open_pskl_wrt_pskl P P1) }}a).
    { inversion HwfP as [ | | | Lb Θb Δb Pb Hbody | | ]; subst.
      apply a_wf_pskl_open with (L := Lb);
        [ intros α0 Hα0;
          eapply a_wf_pskl_weaken; [ | apply Hbody; auto ];
          intros x c Hb; apply binds_app_iff in Hb as [Hb | Hb];
          [ apply binds_app_iff; left; exact Hb
          | apply binds_app_iff; right; exact (Hmono _ _ Hb) ]
        | exact HwfP1 ]. }
    destruct (IH Heq HwfΞΘ HwfP0' HwfSo C Hcore) as [C' [Hcore' Hsc']].
    exists C'. split; [ exact Hcore' | ].
    intros m b Hbm Hmk Hcr.
    eapply Hsc'; [ exact (Hmono _ _ Hbm) | exact Hmk | ].
    apply core_rigid_above_weaken_fresh;
      [ exact Hcr
      | eapply core_ftv_dom; [ exact Hcore | exact HwfP0 ]
      | clear - Huq Hbm; apply binds_In in Hbm; solve_uniq
      | clear - Huq; intros γ Hγ Hc; solve_uniq ].
  - (* Ghost : SK *)
    intros M Θ0 P0 Hmghost Heq; discriminate Heq.
  - (* UnivGhostL : SK *)
    intros M Θ0 Θ1 P0 P Q Hm Hs IH Heq; discriminate Heq.
  - (* Flex-Solve : three FRESH entries go on top and [α0] is re-bound to
       its new definition.  The region grows only by the fresh names
       ([above_dom_insert_sub]) and the binding change is invisible to it
       ([above_dom_rebind]); an old core atom misses the fresh names by the
       rule's own freshness premises. *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hα Hβ Hs IH Heq Hwf Hdecls HwfP0
           Hbα0 C Hcore.
    assert (Hα0m : forall m (b : abind),
               binds m b (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0) ->
               abind_marker b -> α0 <> m)
      by (intros m b Hbm Hmk;
          eapply marker_neq_nonmarker_mid;
          [ exact Hbm | exact Hmk | simpl; auto
          | apply a_wf_aenv_uniq; exact Hwf ]).
    (* the extended context, and the ⊴ INTO it — the same construction
       [a_sub_output_wf_bundle]'s own Flex-Solve case performs; with that
       ⊴ in hand the region and rigidity steps are one
       [core_rigid_above_isub]. *)
    set (τab := ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)).
    set (Θmid := (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0).
    set (Θ' := Ξ ++ (α0 ~ abind_flex_mono_def τab) ++ Θmid).
    destruct (@a_flex_arrow_context Ξ Θ0 α0 α β
                Hwf Hdecls Hne Hα Hβ) as [HwfΘ' Hlift].
    assert (Huq : uniq (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    destruct (IH Heq HwfΘ'
                ltac:(eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hlift ])
                ltac:(apply a_wf_pskl__arrow; apply a_wf_pskl__var;
                        right; left;
                        (unfold Θ'; unfold binds; apply in_or_app; right;
                         simpl; right; auto))
                C Hcore)
      as [C' [Hcore' Hsc']].
    exists C'. split; [ exact Hcore' | ].
    intros m b Hbm Hmk Hcr.
    destruct (@a_isub_binds_marker _ Θ' m b Hlift Hbm Hmk Huq)
      as [b1 [Hbm1 Hmk1]].
    eapply Hsc'; [ exact Hbm1 | exact Hmk1 | ].
    eapply core_rigid_above_isub;
      [ exact Hlift | exact Hbm | exact Hmk | exact Huq
      | apply a_wf_aenv_uniq; exact HwfΘ'
      | eapply core_ftv_dom; [ exact Hcore | exact HwfP0 ]
      | exact Hcr ].
  - (* ⭐ Flex-Assign : THE crux.  The rule SUBSTITUTES the input skeleton,
       so the core MOVES to [C[τ/β]] — under [core_rigid_above] (unlike
       under the full [core_rigid]) a core atom below the marker may
       legitimately be a defined flexible.  The new atoms come from [τ],
       and they are harmless: if [β] were ABOVE the marker the hypothesis
       would make it rigid, contradicting its [flex_mono_def] binding, so
       [β] is at-or-below the marker, [τ] is well-formed BELOW [β]'s own
       entry, and [above_dom_downward] carries "below" to "not above". *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβ1 Hs IH Heq Hwf Hdecls HwfP0 Hbα
           C Hcore.
    assert (Hwfcons : {{ ⊢ ((β ~ abind_flex_mono_def τ) ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_prefix; eauto).
    inversion Hwfcons as [ | | βz τz Θz HβΘ0 Hwfτ Hm Hwf0 | | | ]; subst.
    assert (Huq : uniq (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfΞΘ0 : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).

    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β P0 }}a).
    { eapply a_wf_pskl_subst_mid_def; [ exact Hwf | exact HwfP0 ]. }
    assert (Hwfvarsub : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α) }}a).
    { eapply a_wf_pskl_subst_mid_def; [ exact Hwf | apply a_wf_pskl__var; exact Hbα ]. }
    destruct (IH eq_refl HwfΞΘ0 HwfP0' Hwfvarsub
                (subst_ptyp_in_ptyp τ β C)
                (pskl_ty_core_subst_gen τ β Hcore))
      as [C' [Hcore' Hsc']].
    exists C'. split; [ exact Hcore' | ].
    intros m b Hbm Hmk Hcr.
    assert (Hβm : β <> m)
      by (eapply marker_neq_nonmarker_mid;
          [ exact Hbm | exact Hmk | simpl; auto | exact Huq ]).
    (* the rule's OUTPUT re-attaches [β], and [β] misses the output's core
       (the rule's own [β ∉ dom Θ1] + output wf) *)
    destruct (proj1 a_sub_output_wf_bundle _ _ _ _ _ _ _ Hs
                HwfΞΘ0 HwfP0' Hwfvarsub) as [_ [Hwf1 HwfQ]].
    (* the OLD-ATOM step, shared by both branches below: peeling [β]'s
       definition entry is invisible to an old core atom *)
    assert (Hold : core_rigid_above m (Ξ ++ Θ0) C).
    { eapply core_rigid_above_strip_mid;
        [ exact Hcr | exact Hβm | intros γ0 _ _ Hc; inversion Hc ]. }
    (* ⭐ THE CRUX.  An atom of the substituted core is either one of [τ]'s
       or an old core atom other than [β].  [τ]'s atoms live in [Θ0], i.e.
       BELOW [β]'s entry, so they are not above the marker at all; the old
       ones come straight from [Hcr]. *)
    assert (Hfinal : core_rigid_above m (Ξ ++ Θ0)
                       (subst_ptyp_in_ptyp τ β C)).
    { intros γ Hγ Hab.
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper C τ β) as Hup.
      destruct (AtomSetProperties.In_dec β (ftvar_in_ptyp C))
        as [HβC | HβC].
      - (* [β] IS a core atom.  [Hcr] would then make it RIGID if it were
           above the marker — it is flexibly DEFINED, so it is not; but [β]
           HEADS the non-[Ξ] part, so that forces the marker itself into
           [Ξ], confining the whole region to [dom Ξ]. *)
        assert (Hβnab : β `notin` above_dom m
                          (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0)).
        { intros Hab2.
          pose proof (Hcr β HβC Hab2) as Hbt.
          assert (Hbf : binds β (abind_flex_mono_def τ)
                          (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
            by (apply binds_app_3; apply binds_app_2;
                unfold binds; simpl; auto).
          assert (Heqb : abind_tvar = abind_flex_mono_def τ)
            by (eapply binds_unique; [ exact Hbt | exact Hbf | exact Huq ]).
          discriminate Heqb. }
        assert (HmΞ : m `in` dom Ξ).
        { destruct (AtomSetProperties.In_dec m (dom Ξ)) as [Hin | Hno];
            [ exact Hin | ].
          exfalso. apply Hβnab.
          rewrite (@above_dom_app_notin m Ξ
                     ((β ~ abind_flex_mono_def τ) ++ Θ0) Hno).
          rewrite (@above_dom_cons_other m β (abind_flex_mono_def τ) Θ0 Hβm).
          clear; fsetdec. }
        pose proof (@above_dom_app_in m Ξ Θ0 HmΞ) as Hconf.
        destruct (union_1 (Hup γ Hγ)) as [Hτγ | HCγ'].
        + (* an atom of [τ] : it lives in [Θ0], the region lives in [Ξ] *)
          exfalso.
          pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hsubτ.
          assert (HγΘ0 : γ `in` dom Θ0) by (clear - Hτγ Hsubτ; fsetdec).
          assert (HγΞ : γ `in` dom Ξ) by (clear - Hab Hconf; fsetdec).
          clear - Huq HγΘ0 HγΞ. simpl_env in Huq. destruct_uniq.
          unfold disjoint in *. simpl_env in *. fsetdec.
        + apply Hold; [ clear - HCγ'; fsetdec | exact Hab ].
      - (* [β] is NOT a core atom : the substitution is vacuous *)
        rewrite subst_ptyp_in_ptyp_fresh_eq in Hγ; [ | exact HβC ].
        apply Hold; [ exact Hγ | exact Hab ]. }
    assert (Hbm0 : binds m b (Ξ ++ Θ0))
      by (eapply binds_strip_mid;
            [ exact Hbm | intros Hc; inversion Hc; subst; auto ]).
    apply core_rigid_above_cons_other;
      [ eapply Hsc'; [ exact Hbm0 | exact Hmk | exact Hfinal ]
      | exact Hβm
      | pose proof (core_ftv_dom Hcore' HwfQ) as Hsub;
        clear - Hβ1 Hsub; fsetdec ].
  - (* Flex-Depend : [β̂] joins the pending suffix — the context, the output
       and the region are all the SAME modulo association *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hin Hs IH Heq Hwf Hdecls HwfP0 Hbα
           C Hcore.
    assert (Hdecls' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app;
          [ exact Hdecls | apply (a_decls__cons β); apply a_decls__nil ]).
    destruct (IH Heq ltac:(simpl_env; simpl_env in Hwf; exact Hwf) Hdecls'
                ltac:(simpl_env; simpl_env in HwfP0; exact HwfP0)
                ltac:(simpl_env; simpl_env in Hbα; exact Hbα)
                C Hcore)
      as [C' [Hcore' Hsc']].
    exists C'. split; [ exact Hcore' | ].
    intros m b Hbm Hmk Hcr.
    eapply Hsc';
      [ simpl_env; simpl_env in Hbm; exact Hbm
      | exact Hmk
      | simpl_env; simpl_env in Hcr; exact Hcr ].
  - (* Flex-Skip : peel a FLEXIBLE head — never the marker, and never a
       rigid binding, so both halves of the strip are free *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hs IH Heq Hwf Hdecls HwfP0 Hbα
           C Hcore.
    assert (Huq : uniq (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_strip_mid; eauto).
    assert (Hbα' : a_binds_tvar α (Ξ ++ Θ0))
      by (eapply a_binds_tvar_strip_mid;
            [ exact Hbα
            | intro He; inversion He; subst; exact (Hne eq_refl)
            | intro He; inversion He; subst; exact (Hne eq_refl)
            | intros τ1 He; inversion He; subst; exact (Hne eq_refl) ]).
    destruct (IH Heq Hwf' Hdecls HwfP0' Hbα' C Hcore)
      as [C' [Hcore' Hsc']].
    exists C'. split; [ exact Hcore' | ].
    intros m b Hbm Hmk Hcr.
    assert (Hβm : β <> m)
      by (eapply marker_neq_nonmarker_mid;
          [ exact Hbm | exact Hmk | simpl; auto | exact Huq ]).
    destruct (proj2 a_sub_output_wf_bundle _ _ _ _ _ _ _ _ Hs
                Hwf' Hdecls HwfP0' Hbα') as [_ [_ HwfQ]].
    apply core_rigid_above_cons_other;
      [ eapply Hsc';
          [ eapply binds_strip_mid;
              [ exact Hbm | intros Hc; inversion Hc; subst; auto ]
          | exact Hmk
          | eapply core_rigid_above_strip_mid;
              [ exact Hcr | exact Hβm | intros γ0 _ _ Hc; inversion Hc ] ]
      | exact Hβm
      | pose proof (core_ftv_dom Hcore' HwfQ) as Hsub;
        clear - Hβ1 Hsub; fsetdec ].
  - (* ⭐ Flex-SkipRigid : the peeled entry IS a marker, so the walk may pass
       the very [m] the hypothesis names.  When it does, the OUTPUT
       re-attaches [m] at the head and the region above it is EMPTY — the
       goal is vacuous.  Otherwise the strip needs [β] to miss the core,
       which is the rule's own [β ∉ ftvar_in_pskl P0]. *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hs IH Heq Hwf Hdecls HwfP0 Hbα
           C Hcore.
    assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_strip_mid; eauto).
    assert (Hbα' : a_binds_tvar α (Ξ ++ Θ0))
      by (eapply a_binds_tvar_strip_mid;
            [ exact Hbα
            | intro He; inversion He; subst; exact (Hne eq_refl)
            | intro He; inversion He; subst; exact (Hne eq_refl)
            | intros τ1 He; inversion He; subst; exact (Hne eq_refl) ]).
    destruct (IH Heq Hwf' Hdecls HwfP0' Hbα' C Hcore)
      as [C' [Hcore' Hsc']].
    exists C'. split; [ exact Hcore' | ].
    intros m b Hbm Hmk Hcr.
    destruct (β == m) as [-> | Hβm];
      [ apply core_rigid_above_head_marker | ].
    destruct (proj2 a_sub_output_wf_bundle _ _ _ _ _ _ _ _ Hs
                Hwf' Hdecls HwfP0' Hbα') as [_ [_ HwfQ]].
    apply core_rigid_above_cons_other;
      [ eapply Hsc';
          [ eapply binds_strip_mid;
              [ exact Hbm | intros Hc; inversion Hc; subst; auto ]
          | exact Hmk
          | eapply core_rigid_above_strip_mid;
              [ exact Hcr | exact Hβm
              | intros γ0 Hγ0 _ Hc; inversion Hc; subst;
                pose proof (pskl_ty_core_ftv Hcore) as Hft;
                clear - Hni Hγ0 Hft; fsetdec ] ]
      | exact Hβm
      | pose proof (core_ftv_dom Hcore' HwfQ) as Hsub;
        clear - Hβ1 Hsub; fsetdec ].
  - (* Flex-SkipTmVar (type entry) *)
    intros NM M P0 Θ0 Θ1 Ξ α x Apay Q Hxout Hs IH.
    apply (sub_flex_scope_skip_tm Hxout Hs IH). exact I.
  - (* Flex-SkipTmVar (skeleton entry) *)
    intros NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hxout Hs IH.
    apply (sub_flex_scope_skip_tm Hxout Hs IH). exact I.
Qed.

(* ===================================================================== *)
(*  ⭐ THE TYPING-LEVEL SCOPE WALK, and the two discharge corollaries.     *)
(* ===================================================================== *)

(** [a_typing_scope]'s two [_check_step] rows (AT-AbsCheck (∀) and
    AT-AbsAnnoCheck (∀)), which are verbatim the same: the peeled binder is
    RIGID, which is exactly why the side condition is
    rigidity-above-the-marker.  The arguments are the row's own names. *)
Local Ltac scope_check_step_row Hcore H0 H1 H2 IH Hwf HwfP0 Hexp
    A0 A α Ξ Θ0 Θ1 :=
  let Hpc := fresh "Hpc" in
  pose proof (@pskl_ty_core_of_painting _ _ _ Hcore) as Hpc;
  inversion Hpc; subst;
  let HwfA0 := fresh "HwfA0" in let Hα := fresh "Hα" in
  let Hwfα := fresh "Hwfα" in let HwfA0α := fresh "HwfA0α" in
  assert (HwfA0 : a_wf_ptyp Θ0 (ptyp_all A0))
    by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfP0);
  assert (Hα : α `notin` dom Ξ `union` dom Θ0 `union` dom Θ1
                 `union` ftvar_in_ptyp A0 `union` ftvar_in_ptyp A)
    by (clear - H2; rewrite !dom_app in H2; fsetdec);
  assert (Hwfα : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
    by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]);
  assert (HwfA0α : a_wf_ptyp ((α ~ abind_tvar) ++ Θ0)
                     (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
    by (apply a_wf_ptyp_all_open_at; exact HwfA0);
  let Cα := fresh "Cα" in let HcoreA := fresh "HcoreA" in
  let Hsc' := fresh "Hsc'" in let HcoreA' := fresh "HcoreA'" in
  destruct (IH Hwfα
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA0α)
              (a_ty_mode_compat__tc _)
              (a_wf_exp_weaken_cons α abind_tvar Hexp)
              (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))
              (pskl_ty_core__tc _))
    as [Cα [HcoreA Hsc']];
  pose proof HcoreA as HcoreA'; inversion HcoreA'; subst;
  exists (ptyp_all A); split; [ apply ptyp_ty_core__tc | ];
  let m0 := fresh "m0" in let b0 := fresh "b0" in
  let Hbm := fresh "Hbm" in let Hmk := fresh "Hmk" in
  let Hcr := fresh "Hcr" in let Hm0d := fresh "Hm0d" in
  let Hαm0 := fresh "Hαm0" in let HmΞ := fresh "HmΞ" in
  let Hin := fresh "Hin" in let Hout := fresh "Hout" in
  intros m0 b0 Hbm Hmk Hcr;
  assert (Hm0d : m0 `in` dom Θ0) by (apply binds_In in Hbm; exact Hbm);
  assert (Hαm0 : α <> m0) by (intros ->; clear - Hα Hm0d; fsetdec);
  assert (HmΞ : m0 `notin` dom Ξ)
    by (clear - H0 Hm0d; destruct_uniq; unfold disjoint in *; fsetdec);
  (* the input direction: the peeled [α] is rigid AT THE HEAD *)
  assert (Hin : core_rigid_above m0 ((α ~ abind_tvar) ++ Θ0)
                  (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
    by (let γ := fresh "γ" in let Hγ := fresh "Hγ" in
        let Hab := fresh "Hab" in let Hγα := fresh "Hγα" in
        let Hup := fresh "Hup" in
        intros γ Hγ Hab;
        destruct (γ == α) as [-> | Hγα]; [ unfold binds; simpl; auto | ];
        apply binds_cons_3; apply Hcr;
        [ pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A0
                        (ptyp_var_f α)) as Hup;
          simpl in Hup; simpl; clear - Hγ Hup Hγα; fsetdec
        | rewrite (@above_dom_cons_other m0 α abind_tvar Θ0 Hαm0) in Hab;
          clear - Hab Hγα; fsetdec ]);
  pose proof (Hsc' m0 b0 ltac:(apply binds_cons_3; exact Hbm) Hmk Hin)
    as Hout;
  (* the output direction: strip the suffix by premise (2), then [α] *)
  let γ := fresh "γ" in let Hγ := fresh "Hγ" in let Hab := fresh "Hab" in
  let HγopA := fresh "HγopA" in let HabF := fresh "HabF" in
  let Hb := fresh "Hb" in let HbΞ := fresh "HbΞ" in
  let Hb' := fresh "Hb'" in let Hb'' := fresh "Hb''" in
  let He := fresh "He" in
  intros γ Hγ Hab; simpl in Hγ;
  assert (HγopA : γ `in` ftvar_in_ptyp
                    (open_ptyp_wrt_ptyp A (ptyp_var_f α)))
    by (let Hlow := fresh "Hlow" in
        pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A
                      (ptyp_var_f α)) as Hlow; clear - Hγ Hlow; fsetdec);
  assert (HabF : γ `in` above_dom m0 (Ξ ++ (α ~ abind_tvar) ++ Θ1))
    by (let Hd := fresh "Hd" in
        pose proof (@above_dom_drop_sub m0 nil (Ξ ++ (α ~ abind_tvar)) Θ1
                      ltac:(simpl_env; simpl; clear - HmΞ Hαm0; solve_notin_auto))
          as Hd;
        simpl_env in Hd; clear - Hab Hd; fsetdec);
  pose proof (Hout γ HγopA HabF) as Hb;
  destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | Hb'];
    [ exfalso; apply binds_In in HbΞ; exact (H1 γ HbΞ Hγ) | ];
  destruct (binds_cons_1 _ _ _ _ _ _ Hb') as [[He _] | Hb''];
    [ exfalso; subst γ; clear - Hα Hγ; fsetdec | exact Hb'' ].

(** ⚠️ AT THE TYPING LEVEL THE CONCLUSION IS SCOPE PROPAGATION, NOT CORE
    PRESERVATION — see the counterexample recorded with [a_split_scope]. *)
Definition typing_scope_concl (M : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) (A' : ptyp) (Θ1 : aenv) : Prop :=
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  {{ Θ0 ⊢ᵉ e }}a ->
  forall C, pskl_ty_core M P0 C ->
  exists C', ptyp_ty_core M A' C' /\
    (forall m0 (b0 : abind),
       binds m0 b0 Θ0 -> abind_marker b0 ->
       core_rigid_above m0 Θ0 C -> core_rigid_above m0 Θ1 C').

Lemma a_typing_scope : forall M Θ0 P0 e A' Θ1,
  {{ Θ0 ⊢[ M ; P0 ] e ⦂ A' ⊣ Θ1 }}a ->
  typing_scope_concl M Θ0 P0 e A' Θ1.
Proof.
  intros M Θ0 P0 e A' Θ1 H; unfold typing_scope_concl in *;
    induction H; intros Hwf HwfP0 Hmod Hexp C Hcore;
    pose proof (fun y Ps Hb =>
                  @prop_inc_strengthen.a_wf_aenv_binds_var_skl_wf
                    _ y Ps Hwf Hb) as Hskl.
  - (* AT-Unit *)
    destruct (proj1 a_sub_sub_flex_scope _ _ _ _ _ _ _ H eq_refl Hwf HwfP0
                ltac:(apply a_wf_pskl__unit) C Hcore)
      as [C' [Hcore' Hsc']].
    exists C'. split;
      [ apply pskl_ty_core_of_painting; exact Hcore' | exact Hsc' ].
  - (* AT-Var *)
    assert (HwfA : a_wf_ptyp Θ0 A)
      by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
    destruct (proj1 a_sub_sub_flex_scope _ _ _ _ _ _ _ H0 eq_refl Hwf HwfP0
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA) C Hcore)
      as [C' [Hcore' Hsc']].
    exists C'. split;
      [ apply pskl_ty_core_of_painting; exact Hcore' | exact Hsc' ].
  - (* AT-Anno : the body run's core is a DIFFERENT core — the input core
       crosses it by the run's own increase, not by the IH *)
    destruct (a_wf_exp_anno_inv Hexp) as [HwfA Hexp0].
    destruct (a_typing_sound H Hwf
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
                (a_ty_mode_compat__tc A) Hexp0)
      as [Hle1 [Hwf1 _]].
    assert (HwfA1 : a_wf_ptyp Θ1 A) by (eapply a_wf_ptyp_isub; eassumption).
    destruct (proj1 a_sub_sub_flex_scope _ _ _ _ _ _ _ H0 eq_refl Hwf1
                ltac:(eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hle1 ])
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA1) C Hcore)
      as [C' [Hcore' Hsc']].
    exists C'. split; [ apply pskl_ty_core_of_painting; exact Hcore' | ].
    intros m0 b0 Hbm Hmk Hcr.
    destruct (@a_isub_binds_marker Θ0 Θ1 m0 b0 Hle1 Hbm Hmk
                ltac:(apply a_wf_aenv_uniq; exact Hwf)) as [b1 [Hbm1 Hmk1]].
    eapply Hsc'; [ exact Hbm1 | exact Hmk1 | ].
    eapply core_rigid_above_isub;
      [ exact Hle1 | exact Hbm | exact Hmk
      | apply a_wf_aenv_uniq; exact Hwf
      | apply a_wf_aenv_uniq; exact Hwf1
      | eapply core_ftv_dom; [ exact Hcore | exact HwfP0 ]
      | exact Hcr ].
  - (* AT-Freeze : the result IS the rule's own input type *)
    destruct (a_typing_sound H Hwf ltac:(apply a_wf_pskl__ghost)
                a_ty_mode_compat__ti (a_wf_exp_freeze_inv Hexp))
      as [Hle1 [Hwf1 [HwfB1 _]]].
    assert (HwfA0 : a_wf_ptyp Θ0 A)
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfP0).
    assert (HwfA1 : a_wf_ptyp Θ1 A) by (eapply a_wf_ptyp_isub; eassumption).
    destruct H0 as [Qc Hc].
    destruct (a_consis_isub_wf_nil Hc Hwf1
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA1)
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfB1))
      as [Hle2 Hwf2].
    pose proof (@pskl_ty_core_of_painting _ _ _ Hcore) as Hpc.
    inversion Hpc; subst.
    exists C. split; [ apply ptyp_ty_core__tc | ].
    intros m0 b0 Hbm Hmk Hcr.
    assert (Hle : Θ0 ⊴ Θ2) by (eapply a_isub_trans; eassumption).
    eapply core_rigid_above_isub;
      [ exact Hle | exact Hbm | exact Hmk
      | apply a_wf_aenv_uniq; exact Hwf
      | apply a_wf_aenv_uniq; exact Hwf2
      | eapply core_ftv_dom; [ exact Hcore | exact HwfP0 ]
      | exact Hcr ].
  - (* AT-Abs : the core lives in the CODOMAIN, so the guessed domain and
       the [guess^TY] block are outside it entirely *)
    destruct (a_split_ty_shape H0 Hmod H) as [HeqΘ Hshape]; subst Θ1.
    destruct (a_split_ty_pieces H0 Hmod H HwfP0) as [HwfPP [HwfQ Hmod']].
    (* the core forces the FN shape, which pins the split's codomain *)
    inversion Hcore; subst; [ exfalso; apply H; reflexivity | ].
    match goal with
    | Hs : a_split _ (pskl_arrow _ _) _ _ _ |- _ => inversion Hs; subst
    end.
    cbn [decr_mode] in *.
    assert (Hdecls : a_decls αs) by (eapply a_guess_mono_decls; eassumption).
    assert (Hwfαs : {{ ⊢ (αs ++ Θ0) }}a)
      by (apply a_wf_aenv_decls_app; assumption).
    assert (HΞtv : forall α1, binds α1 abind_flex_mono αs ->
                     a_binds_tvar α1 (αs ++ Θ0)).
    { intros α1 Hb. unfold a_binds_tvar. right; left.
      unfold binds; apply in_or_app; left; exact Hb. }
    assert (HPtv : forall α1, α1 `in` ftvar_in_pskl P ->
                     a_binds_tvar α1 (αs ++ Θ0)).
    { intros α1 Hα1.
      pose proof (a_wf_pskl_ftv_binds HwfPP Hα1) as Ht;
        apply a_binds_tvar_weaken_cons; exact Ht. }
    assert (HwfAg : a_wf_ptyp (αs ++ Θ0) A)
      by (eapply a_guess_mono_wf; [ exact H1 | exact HPtv | exact HΞtv ]).
    assert (Hx : x `notin` dom Θ0 `union` dom αs `union` dom Ξ
                   `union` dom Θ2 `union` fvar_in_exp e)
      by (clear - H4; rewrite !dom_app in H4; fsetdec).
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ αs ++ Θ0) }}a).
    { apply a_wf_aenv__var_typ;
        [ rewrite dom_app; clear - Hx; fsetdec | exact HwfAg | exact Hwfαs ]. }
    destruct (IHa_typing Hwfx
                ltac:(eapply a_wf_pskl_weaken;
                      [ intros z c Hbz; apply binds_app_3; apply binds_app_3;
                        exact Hbz
                      | exact HwfQ ])
                Hmod'
                ltac:(eapply a_wf_exp_mono;
                      [ exact (a_wf_exp_abs_pick x Hexp)
                      | intros z c Hty Hbz; apply binds_app_3;
                        apply binds_app_3; exact Hbz ])
                C ltac:(assumption))
      as [C' [Hcore' Hsc']].
    exists C'. split; [ apply ptyp_ty_core__fn; exact Hcore' | ].
    intros m0 b0 Hbm Hmk Hcr.
    assert (Hm0d : m0 `in` dom Θ0) by (apply binds_In in Hbm; exact Hbm).
    assert (Hxm0 : x <> m0) by (intros ->; clear - Hx Hm0d; fsetdec).
    assert (Hαsm0 : m0 `notin` dom αs)
      by (clear - H2 Hm0d; destruct_uniq; unfold disjoint in *; fsetdec).
    assert (Hin : core_rigid_above m0
                    (((x ~ abind_var_typ A) ++ αs) ++ Θ0) C).
    { apply core_rigid_above_weaken_fresh;
        [ exact Hcr
        | eapply core_ftv_dom; [ eassumption | exact HwfQ ]
        | simpl_env; simpl; clear - Hx Hαsm0 Hm0d; fsetdec
        | intros γ Hγ; simpl_env in Hγ; simpl in Hγ;
          clear - Hγ Hx H2; destruct_uniq; unfold disjoint in *; fsetdec ]. }
    simpl_env in Hin.
    apply (@core_rigid_above_strip_mid m0 Ξ x (abind_var_typ A) Θ2 C');
      [ | exact Hxm0 | intros γ0 _ _ Hc0; inversion Hc0 ].
    eapply Hsc';
      [ apply binds_app_3; apply binds_app_3; exact Hbm | exact Hmk
      | exact Hin ].
  - (* AT-AbsAnno : as AT-Abs, with the consistency run in place of the
       guess block *)
    destruct (a_split_ty_shape H0 Hmod H) as [HeqΘ Hshape]; subst Θ1.
    pose proof (a_wf_exp_abs_anno_inv Hexp) as HwfA.
    destruct (a_split_ty_pieces H0 Hmod H HwfP0) as [HwfPP [HwfQ Hmod']].
    inversion Hcore; subst; [ exfalso; apply H; reflexivity | ].
    match goal with
    | Hs : a_split _ (pskl_arrow _ _) _ _ _ |- _ => inversion Hs; subst
    end.
    cbn [decr_mode] in *.
    destruct H1 as [Qc Hc].
    destruct (a_consis_isub_wf_nil Hc Hwf HwfPP
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA))
      as [Hlec Hwfc].
    assert (HwfAc : a_wf_ptyp Θ2 A) by (eapply a_wf_ptyp_isub; eassumption).
    assert (Hx : x `notin` dom Θ2 `union` dom Ξ `union` dom Θ3
                   `union` fvar_in_exp e)
      by (clear - H3; rewrite !dom_app in H3; fsetdec).
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ2) }}a)
      by (apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfAc | exact Hwfc ]).
    destruct (IHa_typing Hwfx
                (a_wf_pskl_weaken_cons x (abind_var_typ A)
                   ltac:(eapply a_wf_pskl_isub; [ exact HwfQ | exact Hlec ]))
                Hmod'
                (a_wf_exp_weaken_cons x (abind_var_typ A)
                   (a_wf_exp_isub (a_wf_exp_abs_anno_pick x Hexp) Hlec))
                C ltac:(assumption))
      as [C' [Hcore' Hsc']].
    exists C'. split; [ apply ptyp_ty_core__fn; exact Hcore' | ].
    intros m0 b0 Hbm Hmk Hcr.
    assert (Hm0d : m0 `in` dom Θ0) by (apply binds_In in Hbm; exact Hbm).
    assert (Huq0 : uniq Θ0) by (apply a_wf_aenv_uniq; exact Hwf).
    destruct (@a_isub_binds_marker Θ0 Θ2 m0 b0 Hlec Hbm Hmk Huq0)
      as [b2 [Hbm2 Hmk2]].
    assert (Hcr2 : core_rigid_above m0 Θ2 C).
    { eapply core_rigid_above_isub;
        [ exact Hlec | exact Hbm | exact Hmk | exact Huq0
        | apply a_wf_aenv_uniq; exact Hwfc
        | eapply core_ftv_dom; [ eassumption | exact HwfQ ]
        | exact Hcr ]. }
    assert (Hxm0 : x <> m0) by (intros ->; apply binds_In in Hbm2;
                                clear - Hx Hbm2; fsetdec).
    apply (@core_rigid_above_strip_mid m0 Ξ x (abind_var_typ A) Θ3 C');
      [ | exact Hxm0 | intros γ0 _ _ Hc0; inversion Hc0 ].
    eapply Hsc'; [ apply binds_app_3; exact Hbm2 | exact Hmk2 | ].
    apply core_rigid_above_cons_other;
      [ exact Hcr2 | exact Hxm0 | ].
    intros Hc0.
    pose proof (core_ftv_dom ltac:(eassumption)
                  ltac:(eapply a_wf_pskl_isub; [ exact HwfQ | exact Hlec ]))
      as Hsub.
    clear - Hc0 Hsub Hx; fsetdec.
  - (* AT-AbsCheck (∀) *)
    scope_check_step_row Hcore H0 H1 H2 IHa_typing Hwf HwfP0 Hexp
      A0 A α Ξ Θ0 Θ1.
  - (* AT-AbsCheck (→) : the split's pieces, then the body run's suffix *)
    pose proof (@pskl_ty_core_of_painting _ _ _ Hcore) as Hpc.
    inversion Hpc; subst.
    destruct (a_split_wf H Hwf HwfP0) as [Hles [Hwfs [HwfPA HwfPB]]].
    assert (HwfAs : a_wf_ptyp Θ1 A)
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfPA).
    assert (HwfBs : a_wf_ptyp Θ1 B)
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfPB).
    assert (Hx : x `notin` dom Θ1 `union` dom Ξ `union` dom Θ2
                   `union` fvar_in_exp e)
      by (clear - H3; rewrite !dom_app in H3; fsetdec).
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ1) }}a)
      by (apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfAs | exact Hwfs ]).
    assert (Hexpx : {{ Θ1 ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a)
      by (apply (a_wf_exp_isub (a_wf_exp_abs_pick x Hexp) Hles)).
    destruct (IHa_typing Hwfx
                (a_wf_pskl_weaken_cons x (abind_var_typ A) HwfPB)
                (a_ty_mode_compat__tc B)
                (a_wf_exp_weaken_cons x (abind_var_typ A) Hexpx)
                B (pskl_ty_core__tc _))
      as [Cb [HcoreB Hsc']].
    assert (HeqCb : Cb = B1) by (inversion HcoreB; subst; reflexivity).
    subst Cb.
    (* the body run's own increase, for the domain piece *)
    destruct (a_typing_sound H4 Hwfx
                (a_wf_pskl_weaken_cons x (abind_var_typ A) HwfPB)
                (a_ty_mode_compat__tc B)
                (a_wf_exp_weaken_cons x (abind_var_typ A) Hexpx))
      as [Hle [Hwfout _]].
    assert (Huniq2 : uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfout).
    assert (Hisub1 : Θ1 ⊴ Θ2)
      by (eapply a_isub_strip_var_typ_mid;
          [ exact Huniq2 | exact H1 | exact Hle ]).
    assert (Hwf2 : {{ ⊢ Θ2 }}a).
    { eapply a_wf_aenv_strip_prefix.
      eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []. }
    exists (ptyp_arrow A B1). split; [ apply ptyp_ty_core__tc | ].
    intros m0 b0 Hbm Hmk Hcr.
    assert (Huq0 : uniq Θ0) by (apply a_wf_aenv_uniq; exact Hwf).
    destruct (@a_split_scope _ _ _ _ _ _ _ H Hwf HwfP0 Hbm Hmk Hcr)
      as [HcrA HcrB].
    destruct (@a_isub_binds_marker Θ0 Θ1 m0 b0 Hles Hbm Hmk Huq0)
      as [b1 [Hbm1 Hmk1]].
    assert (Hm1d : m0 `in` dom Θ1) by (apply binds_In in Hbm1; exact Hbm1).
    assert (Hxm0 : x <> m0) by (intros ->; clear - Hx Hm1d; fsetdec).
    assert (HmΞ : m0 `notin` dom Ξ)
      by (clear - H1 Hm1d; destruct_uniq; unfold disjoint in *; fsetdec).
    assert (HxB : x `notin` ftvar_in_ptyp B)
      by (pose proof (a_wf_ptyp_ftv_dom HwfBs) as Hd;
          clear - Hd Hx; fsetdec).
    apply core_rigid_above_arrow.
    + eapply core_rigid_above_isub;
        [ exact Hisub1 | exact Hbm1 | exact Hmk1
        | apply a_wf_aenv_uniq; exact Hwfs
        | apply a_wf_aenv_uniq; exact Hwf2
        | apply a_wf_ptyp_ftv_dom; exact HwfAs
        | exact HcrA ].
    + apply (@core_rigid_above_strip_prefix m0 Ξ Θ2 B1);
        [ | exact HmΞ | intros γ Hγ Hc0; exact (H2 γ Hc0 Hγ) ].
      apply (@core_rigid_above_strip_mid m0 Ξ x (abind_var_typ A) Θ2 B1);
        [ | exact Hxm0 | intros γ0 _ _ Hc0; inversion Hc0 ].
      eapply Hsc'; [ apply binds_cons_3; exact Hbm1 | exact Hmk1 | ].
      apply core_rigid_above_cons_other;
        [ exact HcrB | exact Hxm0 | exact HxB ].
  - (* AT-AbsAnnoCheck (∀) : verbatim the AbsCheck ∀ row *)
    scope_check_step_row Hcore H0 H1 H2 IHa_typing Hwf HwfP0 Hexp
      A0 A α Ξ Θ0 Θ1.
  - (* AT-AbsAnnoCheck (→) : the AbsCheck → row with the consistency run
       between the split and the body *)
    pose proof (@pskl_ty_core_of_painting _ _ _ Hcore) as Hpc.
    inversion Hpc; subst.
    destruct (a_split_wf H Hwf HwfP0) as [Hles [Hwfs [HwfPA HwfPB]]].
    assert (HwfAs : a_wf_ptyp Θ1 A')
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfPA).
    assert (HwfBs : a_wf_ptyp Θ1 B)
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfPB).
    pose proof (a_wf_exp_abs_anno_inv Hexp) as HwfAan.
    assert (HwfAan1 : a_wf_ptyp Θ1 A)
      by (eapply a_wf_ptyp_isub; [ exact HwfAan | exact Hles ]).
    destruct H0 as [Qc Hc].
    destruct (a_consis_isub_wf_nil Hc Hwfs
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAan1) HwfPA)
      as [Hlec Hwfc].
    assert (HwfAan2 : a_wf_ptyp Θ2 A)
      by (eapply a_wf_ptyp_isub; [ exact HwfAan1 | exact Hlec ]).
    assert (Hx : x `notin` dom Θ2 `union` dom Ξ `union` dom Θ3
                   `union` fvar_in_exp e)
      by (clear - H4; rewrite !dom_app in H4; fsetdec).
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ2) }}a)
      by (apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfAan2 | exact Hwfc ]).
    assert (Hexpx : {{ Θ2 ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a)
      by (apply (a_wf_exp_isub (a_wf_exp_abs_anno_pick x Hexp)
                   (a_isub_trans Hles Hlec))).
    assert (HwfPB2 : {{ Θ2 ⨟ empty ⊢ₚₛ (ptyp_to_pskl B) }}a)
      by (eapply a_wf_pskl_isub; [ exact HwfPB | exact Hlec ]).
    destruct (IHa_typing Hwfx
                (a_wf_pskl_weaken_cons x (abind_var_typ A) HwfPB2)
                (a_ty_mode_compat__tc B)
                (a_wf_exp_weaken_cons x (abind_var_typ A) Hexpx)
                B (pskl_ty_core__tc _))
      as [Cb [HcoreB Hsc']].
    assert (HeqCb : Cb = B1) by (inversion HcoreB; subst; reflexivity).
    subst Cb.
    destruct (a_typing_sound H5 Hwfx
                (a_wf_pskl_weaken_cons x (abind_var_typ A) HwfPB2)
                (a_ty_mode_compat__tc B)
                (a_wf_exp_weaken_cons x (abind_var_typ A) Hexpx))
      as [Hle [Hwfout _]].
    assert (Huniq3 : uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ3))
      by (apply a_wf_aenv_uniq; exact Hwfout).
    assert (Hisub2 : Θ2 ⊴ Θ3)
      by (eapply a_isub_strip_var_typ_mid;
          [ exact Huniq3 | exact H2 | exact Hle ]).
    assert (Hwf3 : {{ ⊢ Θ3 }}a).
    { eapply a_wf_aenv_strip_prefix.
      eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []. }
    exists (ptyp_arrow A' B1). split; [ apply ptyp_ty_core__tc | ].
    intros m0 b0 Hbm Hmk Hcr.
    assert (Huq0 : uniq Θ0) by (apply a_wf_aenv_uniq; exact Hwf).
    destruct (@a_split_scope _ _ _ _ _ _ _ H Hwf HwfP0 Hbm Hmk Hcr)
      as [HcrA HcrB].
    destruct (@a_isub_binds_marker Θ0 Θ1 m0 b0 Hles Hbm Hmk Huq0)
      as [b1 [Hbm1 Hmk1]].
    destruct (@a_isub_binds_marker Θ1 Θ2 m0 b1 Hlec Hbm1 Hmk1
                ltac:(apply a_wf_aenv_uniq; exact Hwfs)) as [b2 [Hbm2 Hmk2]].
    assert (Hm2d : m0 `in` dom Θ2) by (apply binds_In in Hbm2; exact Hbm2).
    assert (Hxm0 : x <> m0) by (intros ->; clear - Hx Hm2d; fsetdec).
    assert (HmΞ : m0 `notin` dom Ξ)
      by (clear - H2 Hm2d; destruct_uniq; unfold disjoint in *; fsetdec).
    assert (HcrA2 : core_rigid_above m0 Θ2 A').
    { eapply core_rigid_above_isub;
        [ exact Hlec | exact Hbm1 | exact Hmk1
        | apply a_wf_aenv_uniq; exact Hwfs
        | apply a_wf_aenv_uniq; exact Hwfc
        | apply a_wf_ptyp_ftv_dom; exact HwfAs
        | exact HcrA ]. }
    assert (HcrB2 : core_rigid_above m0 Θ2 B).
    { eapply core_rigid_above_isub;
        [ exact Hlec | exact Hbm1 | exact Hmk1
        | apply a_wf_aenv_uniq; exact Hwfs
        | apply a_wf_aenv_uniq; exact Hwfc
        | apply a_wf_ptyp_ftv_dom; exact HwfBs
        | exact HcrB ]. }
    assert (HxB : x `notin` ftvar_in_ptyp B).
    { pose proof (a_wf_ptyp_ftv_dom
                    ltac:(eapply a_wf_ptyp_isub;
                            [ exact HwfBs | exact Hlec ])) as Hd.
      clear - Hd Hx; fsetdec. }
    apply core_rigid_above_arrow.
    + eapply core_rigid_above_isub;
        [ exact Hisub2 | exact Hbm2 | exact Hmk2
        | apply a_wf_aenv_uniq; exact Hwfc
        | apply a_wf_aenv_uniq; exact Hwf3
        | apply a_wf_ptyp_ftv_dom;
          eapply a_wf_ptyp_isub; [ exact HwfAs | exact Hlec ]
        | exact HcrA2 ].
    + apply (@core_rigid_above_strip_prefix m0 Ξ Θ3 B1);
        [ | exact HmΞ | intros γ Hγ Hc0; exact (H3 γ Hc0 Hγ) ].
      apply (@core_rigid_above_strip_mid m0 Ξ x (abind_var_typ A) Θ3 B1);
        [ | exact Hxm0 | intros γ0 _ _ Hc0; inversion Hc0 ].
      eapply Hsc'; [ apply binds_cons_3; exact Hbm2 | exact Hmk2 | ].
      apply core_rigid_above_cons_other;
        [ exact HcrB2 | exact Hxm0 | exact HxB ].
  - (* AT-App : the core is threaded through the FUNCTION premise; the
       argument runs only move the context *)
    destruct (a_wf_exp_app_inv Hexp) as [Hexp1 Hexp2].
    destruct (a_pat_sound H Hwf ltac:(apply a_wf_pskl__ghost)
                a_sk_mode_compat__tc Hexp2)
      as [Hle1 [Hwf1 [Qt1 [HeQt1 [Hpat1 Href1]]]]].
    destruct (ad_refine_syn_syn_l Href1 pskl_ghost eq_refl) as [P' HQt1].
    subst Qt1. rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt1. subst P.
    assert (HwfPin : {{ Θ1 ⨟ empty ⊢ₚₛ P' }}a)
      by (pose proof (ad_pat_target_wf Hpat1 Hwf1) as Hw;
          rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw; exact Hw).
    assert (HwfArr : {{ Θ1 ⨟ empty ⊢ₚₛ (pskl_arrow P' Q) }}a)
      by (apply a_wf_pskl__arrow;
          [ exact HwfPin
          | eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hle1 ] ]).
    destruct (IHa_typing1 Hwf1 HwfArr
                ltac:(apply a_ty_mode_compat__fn; exact Hmod)
                (a_wf_exp_isub Hexp1 Hle1)
                C ltac:(apply pskl_ty_core__fn; exact Hcore))
      as [C' [HcoreF Hsc']].
    pose proof HcoreF as HcoreF'. inversion HcoreF'; subst.
    (* the two increases the argument premises contribute *)
    destruct (a_typing_sound H0 Hwf1 HwfArr
                ltac:(apply a_ty_mode_compat__fn; exact Hmod)
                (a_wf_exp_isub Hexp1 Hle1))
      as [Hle2 [Hwf2 [HwfAB _]]].
    destruct (a_wf_ptyp_arrow_inv HwfAB) as [HwfAdom HwfBcod].
    destruct (a_typing_sound H1 Hwf2
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAdom)
                (a_ty_mode_compat__tc A)
                ltac:(eapply a_wf_exp_isub;
                      [ eapply a_wf_exp_isub; [ exact Hexp2 | exact Hle1 ]
                      | exact Hle2 ]))
      as [Hle3 [Hwf3 _]].
    exists C'. split; [ assumption | ].
    intros m0 b0 Hbm Hmk Hcr.
    assert (Huq0 : uniq Θ0) by (apply a_wf_aenv_uniq; exact Hwf).
    destruct (@a_isub_binds_marker Θ0 Θ1 m0 b0 Hle1 Hbm Hmk Huq0)
      as [b1 [Hbm1 Hmk1]].
    assert (Hftv : ftvar_in_ptyp C [<=] dom Θ0)
      by (eapply core_ftv_dom; [ exact Hcore | exact HwfP0 ]).
    assert (Hcr1 : core_rigid_above m0 Θ1 C).
    { eapply core_rigid_above_isub;
        [ exact Hle1 | exact Hbm | exact Hmk | exact Huq0
        | apply a_wf_aenv_uniq; exact Hwf1 | exact Hftv | exact Hcr ]. }
    pose proof (Hsc' m0 b1 Hbm1 Hmk1 Hcr1) as Hcr2.
    destruct (@a_isub_binds_marker Θ1 Θ2 m0 b1 Hle2 Hbm1 Hmk1
                ltac:(apply a_wf_aenv_uniq; exact Hwf1)) as [b2 [Hbm2 Hmk2]].
    eapply core_rigid_above_isub;
      [ exact Hle3 | exact Hbm2 | exact Hmk2
      | apply a_wf_aenv_uniq; exact Hwf2
      | apply a_wf_aenv_uniq; exact Hwf3
      | | exact Hcr2 ].
    (* the fn premise's core lives in the codomain [B], which is wf at Θ2 *)
    pose proof (ptyp_ty_core_ftv HcoreF) as Hsub.
    pose proof (a_wf_ptyp_ftv_dom HwfAB) as Hd.
    simpl in Hsub, Hd. clear - Hsub Hd; fsetdec.
Qed.

(* ===================================================================== *)
(*  ⭐ THE TWO DISCHARGE COROLLARIES (the check rows' premise (2)).        *)
(* ===================================================================== *)

(** With the marker at the TOP of the input the hypothesis is VACUOUS
    ([above_dom m ((m ~ b) ++ Θ) = ∅]), and the conclusion says a result
    atom lying in the discarded suffix would have to be RIGID — which
    [suffix_no_rigid_mid] forbids.  That IS premise (2). *)
Lemma a_typing_scope_head_nil : forall m (b : abind) Θ0 A0 e A1 Ξ Θ2,
  abind_marker b ->
  {{ ((m ~ b) ++ Θ0) ⊢[ mode_tc ; (ptyp_to_pskl A0) ] e ⦂ A1
    ⊣ (Ξ ++ (m ~ b) ++ Θ2) }}a ->
  {{ ⊢ ((m ~ b) ++ Θ0) }}a ->
  {{ ((m ~ b) ++ Θ0) ⨟ empty ⊢ₚₛ (ptyp_to_pskl A0) }}a ->
  {{ ((m ~ b) ++ Θ0) ⊢ᵉ e }}a ->
  {{ ⊢ (Ξ ++ (m ~ b) ++ Θ2) }}a ->
  a_suffix Ξ ->
  forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A1.
Proof.
  intros m b Θ0 A0 e A1 Ξ Θ2 Hmk Hrun Hwf HwfP0 Hexp HwfOut Hsuf γ Hγ HγA1.
  destruct (a_typing_scope Hrun Hwf HwfP0 (a_ty_mode_compat__tc _) Hexp
              (pskl_ty_core__tc A0)) as [C' [Hcore' Hsc']].
  assert (HeqC' : C' = A1) by (inversion Hcore'; subst; reflexivity).
  subst C'.
  pose proof (Hsc' m b ltac:(unfold binds; simpl; auto) Hmk
                (@core_rigid_above_head_marker m b Θ0 A0)) as Hout.
  assert (Huq : uniq (Ξ ++ (m ~ b) ++ Θ2))
    by (apply a_wf_aenv_uniq; exact HwfOut).
  assert (HmΞ : m `notin` dom Ξ)
    by (clear - Huq; destruct_uniq; unfold disjoint in *; simpl_env in *;
        fsetdec).
  assert (Hab : γ `in` above_dom m (Ξ ++ (m ~ b) ++ Θ2))
    by (rewrite (@above_dom_app_notin m Ξ ((m ~ b) ++ Θ2) HmΞ);
        clear - Hγ; fsetdec).
  exact (@suffix_no_rigid_mid Ξ m b Θ2 γ Hsuf Huq Hγ (Hout γ HγA1 Hab)).
Qed.

(** The [_step] rows' instance: the marker is the peeled rigid binder. *)
Corollary a_typing_scope_tvar_nil : forall α Θ0 A0 e A1 Ξ Θ2,
  {{ ((α ~ abind_tvar) ++ Θ0) ⊢[ mode_tc ; (ptyp_to_pskl A0) ] e ⦂ A1
    ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ2) }}a ->
  {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a ->
  {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (ptyp_to_pskl A0) }}a ->
  {{ ((α ~ abind_tvar) ++ Θ0) ⊢ᵉ e }}a ->
  {{ ⊢ (Ξ ++ (α ~ abind_tvar) ++ Θ2) }}a ->
  a_suffix Ξ ->
  forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A1.
Proof. intros. eapply a_typing_scope_head_nil; [ | eassumption .. ]; exact I. Qed.

(** The [_base] rows' instance: the marker is the TERM binder. *)
Corollary a_typing_scope_tm_nil : forall x Apay Θ0 A0 e A1 Ξ Θ2,
  {{ ((x ~ abind_var_typ Apay) ++ Θ0) ⊢[ mode_tc ; (ptyp_to_pskl A0) ] e ⦂ A1
    ⊣ (Ξ ++ (x ~ abind_var_typ Apay) ++ Θ2) }}a ->
  {{ ⊢ ((x ~ abind_var_typ Apay) ++ Θ0) }}a ->
  {{ ((x ~ abind_var_typ Apay) ++ Θ0) ⨟ empty ⊢ₚₛ (ptyp_to_pskl A0) }}a ->
  {{ ((x ~ abind_var_typ Apay) ++ Θ0) ⊢ᵉ e }}a ->
  {{ ⊢ (Ξ ++ (x ~ abind_var_typ Apay) ++ Θ2) }}a ->
  a_suffix Ξ ->
  forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A1.
Proof. intros. eapply a_typing_scope_head_nil; [ | eassumption .. ]; exact I. Qed.
