(** Enablers for the completeness ∀-cases (design doc §7.3, L8/L9):

    - L8 [a_assign_unify_consis_tvar_prefix]: an all-rigid prefix of the
      input context survives VERBATIM into the output.  The algorithm only
      touches flexible entries; rigid binders are skipped and re-attached
      (SkipRigid / Flex-Flex-Skip'), and every deposit (Solve-M's [β̄ ++ Ξ])
      lands BELOW the walked prefix.  This is what shapes the recursive
      call's output as [(α ~ tvar) ++ Θ1], as [a_consis__forall_inh] et al
      demand.

    - [a_assign_unify_consis_delta_compat]: [Δ1]/[Δ2] are only read
      through set predicates, so they transport along [=].  Needed to
      normalize the [rn_set] images at binder reassembly.  (Until the
      [F]-deletion this lemma also swapped the used-name index; see
      DESIGN.md §4.3.)

    - L9 [a_assign_unify_consis_rename_tvar]: renaming a rigid mid entry
      [α] to a fresh [β] across a whole algorithmic run.  The key
      observation making this tractable: under an ALL-RIGID prefix
      (which is the only shape the ∀-cases produce), every flex-headed
      rule is impossible above [α] — the walk can only skip rigid
      binders until it CROSSES [α], and below the crossing [α ∉ ftv]
      of everything in sight (SkipRigid's own side condition), so the
      sub-derivation is reused VERBATIM. *)

Require Import src.fresco.prop_shapes.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.fresco.prop_coercions.
Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo.basic.prop_context.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §0  Small helpers                                                     *)
(* ===================================================================== *)

(** A context slice made of rigid binders only. *)
Definition tvar_prefix (Ξ : aenv) : Prop :=
  forall x (b : abind), binds x b Ξ -> b = abind_tvar.

Lemma tvar_prefix_nil : tvar_prefix nil.
Proof. intros x b Hb. inversion Hb. Qed.

Lemma tvar_prefix_head : forall x (b : abind) Ξ,
  tvar_prefix ((x, b) :: Ξ) -> b = abind_tvar.
Proof. intros * H. apply (H x b). left. reflexivity. Qed.

Lemma tvar_prefix_tail : forall x (b : abind) Ξ,
  tvar_prefix ((x, b) :: Ξ) -> tvar_prefix Ξ.
Proof. intros * H y c Hb. apply (H y c). right. exact Hb. Qed.

Lemma tvar_prefix_cons : forall x Ξ,
  tvar_prefix Ξ -> tvar_prefix ((x, abind_tvar) :: Ξ).
Proof.
  intros * H y c Hb. destruct Hb as [Heq | Hb];
    [ inversion Heq; reflexivity | apply (H y c); exact Hb ].
Qed.

(** Dispatch: a cons-headed input against a prefix split.  Either the
    prefix is nil (trivial output tail), or its head equals the input's
    head — and if the input head's binding is NOT [abind_tvar] the
    prefix hypothesis refutes the case. *)
Ltac tvp_dispatch :=
  match goal with
  | Heq : _ = ?Ξr ++ _ |- _ =>
      destruct Ξr as [ | [?x ?bx] ?Ξr' ];
      [ eexists; reflexivity
      | simpl in Heq; inversion Heq; subst;
        try match goal with
        | Htv : tvar_prefix ((_, ?b) :: _) |- _ =>
            solve [ pose proof (tvar_prefix_head Htv); discriminate ]
        end ]
  end.

(* ===================================================================== *)
(*  §1  Domain monotonicity (hypothesis-free)                             *)
(* ===================================================================== *)

(** Strip a rigid head off both sides of a domain inclusion.  Needed since
    cluster 4: the ∀ rows' IH is now a SINGLE instance under the rule's own
    binder, so there is no representative to pick — the binder is stripped
    instead, which is legal exactly because the rule's avoid-input keeps it
    out of [dom Θ0] ([ftvar_in_aenv] ⊇ [dom]). *)
Lemma dom_sub_strip_tvar : forall α (Θ0 Θ1 : aenv),
  α `notin` dom Θ0 ->
  dom ((α ~ abind_tvar) ++ Θ0) [<=] dom ((α ~ abind_tvar) ++ Θ1) ->
  dom Θ0 [<=] dom Θ1.
Proof.
  intros α Θ0 Θ1 Hna Hsub. simpl_env in Hsub. simpl dom in Hsub.
  clear - Hna Hsub. fsetdec.
Qed.

Lemma a_assign_unify_consis_dom_mono :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> dom (Ξ ++ Θ0) [<=] dom Θ1) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> dom Θ0 [<=] dom Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a -> dom Θ0 [<=] dom Θ1).
Proof.
  apply a_assign_unify_consis_mutind;
    intros;
    (* the three ∀ rows first — strip the rule's own binder (see
       [dom_sub_strip_tvar]); the rewriting below would destroy the shape *)
    try (match goal with
         | IH : dom ((?α ~ abind_tvar) ++ ?A) [<=] dom ((?α ~ abind_tvar) ++ ?B)
             |- dom ?A [<=] dom ?B =>
             apply dom_sub_strip_tvar with (α := α);
               [ pose proof (dom_subset_ftvar_in_aenv A); fsetdec | exact IH ]
         end);
    repeat (rewrite dom_app in * || simpl dom in * );
    fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  L8: the all-rigid prefix is preserved verbatim                    *)
(* ===================================================================== *)

Lemma a_assign_unify_consis_tvar_prefix :
  (forall Θi Ξ α P Θo,
     {{ Θi ⊲[ Ξ ] α ≔ P ⊣ Θo }}a ->
     forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
     exists Θt', Θo = Ξr ++ Θt') /\
  (forall Θi α β Θo,
     {{ Θi ⊲ α ≈ᵘ β ⊣ Θo }}a ->
     forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
     exists Θt', Θo = Ξr ++ Θt') /\
  (forall Δ1 Δ2 Θi P0 P P' Θo,
     {{ Θi ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θo }}a ->
     forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
     exists Θt', Θo = Ξr ++ Θt').
Proof.
  apply a_assign_unify_consis_mutind.
  - (* univ_ghost_id : flex head *)
    intros Θ0 α Ξr Θt Heq Htv. tvp_dispatch.
  - (* solve_m : flex head *)
    intros Θ0 Ξ α P βs τ Hnα Hg Hm Hu Hfr Ξr Θt Heq Htv. tvp_dispatch.
  - (* assign : defined-flex head *)
    intros Θ0 Θ1 Ξ α β τ P P' Hf Hbar Hc IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* depend : flex head *)
    intros Θ0 Θ1 Ξ α β P Hne Hin Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* skip : flex head *)
    intros Θ0 Θ1 Ξ α β P Hne Hni Hbar Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* skip_rigid : tvar head — the real walk case *)
    intros Θ0 Θ1 Ξ α β P Hni Hbar Ha IH Ξr Θt Heq Htv. tvp_dispatch.
    destruct (IH Ξr' Θt eq_refl (tvar_prefix_tail Htv)) as [Θt' ->].
    exists Θt'. reflexivity.
  - (* skip_tm_var : term head *)
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* skip_tm_skl : term head *)
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* flex_id : output = input *)
    intros Θ0 α Hf Ξr Θt Heq Htv. exists Θt. assumption.
  - (* flex_l : flex head *)
    intros Θ0 α β Hne Hf Ξr Θt Heq Htv. tvp_dispatch.
  - (* flex_r : flex head *)
    intros Θ0 α β Hne Hf Ξr Θt Heq Htv. tvp_dispatch.
  - (* flex_assign : defined-flex head *)
    intros Θ0 Θ1 α1 τ α β P' Hfα Hfβ Hbar Hc IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* flex_skip : flex head *)
    intros Θ0 Θ1 α1 α β Hne1 Hne2 Hbar Hu IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* skip_other : rigid/term head — the real walk case *)
    intros Θ0 Θ1 c b α β Hb Hbar Hu IH Ξr Θt Heq Htv. tvp_dispatch.
    destruct (IH Ξr' Θt eq_refl (tvar_prefix_tail Htv)) as [Θt' ->].
    exists Θt'. reflexivity.
  - (* ghost : output = input *)
    intros Δ1 Δ2 Θ0 P0 Hi Ξr Θt Heq Htv. exists Θt. assumption.
  - (* unit *)
    intros Δ1 Δ2 Θ0 Ξr Θt Heq Htv. exists Θt. assumption.
  - (* rigid *)
    intros Δ1 Δ2 Θ0 α Hb Ξr Θt Heq Htv. exists Θt. assumption.
  - (* arrow : thread the two components *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2
      Ξr Θt Heq Htv.
    destruct (IH1 Ξr Θt Heq Htv) as [Θt1 ->].
    destruct (IH2 Ξr Θt1 eq_refl Htv) as [Θt2 ->].
    exists Θt2. reflexivity.
  - (* forall_inh : instantiate the cofinite premise once *)
    (* cluster 4: the premise is a single instance at the rule's own binder,
       so the [atom_fresh L] dance is gone — the IH applies directly *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Ξr Θt Heq Htv.
    destruct (IH ((α, abind_tvar) :: Ξr) Θt
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)) as [Θt' HeqO].
    simpl in HeqO. inversion HeqO. exists Θt'. congruence.
  - (* forall_syn *)
    (* cluster 4: the premise is a single instance at the rule's own binder,
       so the [atom_fresh L] dance is gone — the IH applies directly *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Ξr Θt Heq Htv.
    destruct (IH ((α, abind_tvar) :: Ξr) Θt
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)) as [Θt' HeqO].
    simpl in HeqO. inversion HeqO. exists Θt'. congruence.
  - (* univ_ghost *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hc IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  - (* univ_ghost1 *)
    (* cluster 4: the premise is a single instance at the rule's own binder,
       so the [atom_fresh L] dance is gone — the IH applies directly *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Ξr Θt Heq Htv.
    destruct (IH ((α, abind_tvar) :: Ξr) Θt
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)) as [Θt' HeqO].
    simpl in HeqO. inversion HeqO. exists Θt'. congruence.
  - (* univ_ghost2 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  - (* flex *)
    intros Δ1 Δ2 Θ0 Θ1 α β Hu IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  - (* flex_l *)
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hnhole Ha IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  - (* flex_r *)
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hnhole Ha IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  - (* ghost_r *)
    intros Δ1 Δ2 Θ0 P Hi Ξr Θt Heq Htv. exists Θt. assumption.
  - (* univ_ghost_r *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
Qed.

(* ===================================================================== *)
(*  §3  Compatibility: F-change + Δ-transport along [=]                   *)
(* ===================================================================== *)

Definition auc_dom_mono_consis := proj2 (proj2 a_assign_unify_consis_dom_mono).

(** [Δ1]/[Δ2] are read only through set predicates, so they transport along
    [=].  This USED to be a three-way [F]-swapping lemma: the used-name set
    was an index of all three judgments, and consumers needed to move a
    derivation from one [F] to another.  [F] is gone (DESIGN.md §4.3), so
    only the Δ-transport survives, and it concerns consistency alone —
    [a_assign] / [a_unify] carry no set index at all.  The two trivial
    motives are still needed: the three judgments are MUTUAL. *)
Lemma a_assign_unify_consis_delta_compat :
  (forall Θ0 Ξ α P Θ1, {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> True) /\
  (forall Θ0 α β Θ1, {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> True) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
     forall Δ1' Δ2', Δ1 [=] Δ1' -> Δ2 [=] Δ2' ->
     {{ Θ0 ⊢[ Δ1' | Δ2' | P0 ] P ∼ P' ⊣ Θ1 }}a).
Proof.
  apply a_assign_unify_consis_mutind;
    (* the assign / unify motives are trivial — but their cases still
       quantify over the rule's variables, so [exact I] needs the intros *)
    try (intros; exact I).
  - (* ghost *)
    intros Δ1 Δ2 Θ0 P0 Hi Δ1' Δ2' H1 H2.
    apply a_consis__ghost. clear - Hi H2. fsetdec.
  - (* unit *)
    intros. apply a_consis__unit.
  - (* rigid *)
    intros Δ1 Δ2 Θ0 α Hb Δ1' Δ2' H1 H2. apply a_consis__rigid; exact Hb.
  - (* arrow *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2 Δ1' Δ2' H1 H2.
    eapply a_consis__arrow; [ apply IH1 | apply IH2 ]; assumption.
  - (* forall_inh *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH Δ1' Δ2' H1 H2.
    apply a_consis__forall_inh with (α := α);
      [ clear - Hfr H1 H2; fsetdec
      | apply IH; [ clear - H1; fsetdec | clear - H2; fsetdec ] ].
  - (* forall_syn *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH Δ1' Δ2' H1 H2.
    apply a_consis__forall_syn with (α := α);
      [ clear - Hfr H1 H2; fsetdec
      | apply IH; [ exact H1 | clear - H2; fsetdec ] ].
  - (* univ_ghost *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hc IH Δ1' Δ2' H1 H2.
    apply a_consis__univ_ghost. apply IH; assumption.
  - (* univ_ghost1 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH Δ1' Δ2' H1 H2.
    apply a_consis__univ_ghost1 with (α := α);
      [ clear - Hfr H1 H2; fsetdec
      | apply IH; [ clear - H1; fsetdec | exact H2 ] ].
  - (* univ_ghost2 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH Δ1' Δ2' H1 H2.
    apply a_consis__univ_ghost2; [ exact Hg | exact Hnf | apply IH; assumption ].
  - (* flex : the premise is a unification, no Δ *)
    intros Δ1 Δ2 Θ0 Θ1 α β Hu _ Δ1' Δ2' H1 H2. apply a_consis__flex; exact Hu.
  - (* flex_l *)
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hnhole Ha _ Δ1' Δ2' H1 H2.
    apply a_consis__flex_l; assumption.
  - (* flex_r *)
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hnhole Ha _ Δ1' Δ2' H1 H2.
    apply a_consis__flex_r; assumption.
  - (* ghost_r *)
    intros Δ1 Δ2 Θ0 P Hi Δ1' Δ2' H1 H2.
    apply a_consis__ghost_r. clear - Hi H1. fsetdec.
  - (* univ_ghost_r *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH Δ1' Δ2' H1 H2.
    apply a_consis__univ_ghost_r;
      [ exact Hg | exact Hnf | apply IH; assumption ].
Qed.

(* ===================================================================== *)
(*  §4  Subjects are flexible variables of the input                      *)
(* ===================================================================== *)

(** An assignment's subject is a flexible variable of its merged input
    [Ξ ++ Θ0]; a unification's two subjects are flexible variables of its
    input.  (Rules whose own shape does not show it thread it from their
    premise.) *)
Lemma a_assign_unify_subject_flex :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> a_flex_tvar (Ξ ++ Θ0) α) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a -> True).
Proof.
  apply a_assign_unify_consis_mutind;
    try solve [ intros; exact I ].
  - (* univ_ghost_id *)
    intros Θ0 α. simpl. left. left. reflexivity.
  - (* solve_m *)
    intros Θ0 Ξ α P βs τ Hnα Hg Hm Hu Hfr.
    left. unfold binds. apply in_or_app. right. left. reflexivity.
  - (* assign *)
    intros Θ0 Θ1 Ξ α β τ P P' Hfl Hbar Hc _.
    apply a_flex_tvar_weaken_app. exact Hfl.
  - (* depend *)
    intros Θ0 Θ1 Ξ α β P Hne Hin Ha IH.
    simpl_env in IH. exact IH.
  - (* skip *)
    intros Θ0 Θ1 Ξ α β P Hne Hni Hbar Ha IH.
    apply (a_flex_tvar_weaken_mid Ξ (β ~ abind_flex_mono) Θ0). exact IH.
  - (* skip_rigid *)
    intros Θ0 Θ1 Ξ α β P Hni Hbar Ha IH.
    apply (a_flex_tvar_weaken_mid Ξ (β ~ abind_tvar) Θ0). exact IH.
  - (* skip_tm_var *)
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH.
    apply (a_flex_tvar_weaken_mid Ξ (x ~ abind_var_typ P') Θ0). exact IH.
  - (* skip_tm_skl *)
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH.
    apply (a_flex_tvar_weaken_mid Ξ (x ~ abind_var_skl P') Θ0). exact IH.
  - (* flex_id *)
    intros Θ0 α Hf. split; assumption.
  - (* flex_l *)
    intros Θ0 α β Hne Hf. split.
    + left. left. reflexivity.
    + apply (a_flex_tvar_weaken_app (α ~ abind_flex_mono)). exact Hf.
  - (* flex_r *)
    intros Θ0 α β Hne Hf. split.
    + apply (a_flex_tvar_weaken_app (β ~ abind_flex_mono)). exact Hf.
    + left. left. reflexivity.
  - (* flex_assign *)
    intros Θ0 Θ1 α1 τ α β P' Hfα Hfβ Hbar Hc _. split; assumption.
  - (* flex_skip *)
    intros Θ0 Θ1 α1 α β Hne1 Hne2 Hbar Hu [IHα IHβ]. split;
      apply (a_flex_tvar_weaken_app (α1 ~ abind_flex_mono)); assumption.
  - (* skip_other *)
    intros Θ0 Θ1 c b α β Hb Hbar Hu [IHα IHβ]. split;
      apply (a_flex_tvar_weaken_app (c ~ b)); assumption.
Qed.

(* ===================================================================== *)
(*  §5  Uniqueness preservation + F-protection (joint)                    *)
(* ===================================================================== *)

Lemma disjoint_from_pointwise : forall (E G : aenv),
  (forall α1, α1 `in` dom E -> α1 `notin` dom G) -> disjoint E G.
Proof.
  intros * H. unfold disjoint.
  intros x Hx.
  apply inter_iff in Hx. destruct Hx as [H1 H2].
  exfalso. exact (H x H1 H2).
Qed.

(** Uniqueness is preserved.  This USED to carry a second conjunct — every
    [F]-name of the output's domain was already in the input's — which is
    what made the re-attaching rows' [uniq_push] go through.  The Barendregt
    output premise now states that fact directly at each of those rows, so
    the conjunct is gone and the proof is a third of its length. *)
Lemma a_assign_unify_consis_uniq :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> uniq (Ξ ++ Θ0) -> uniq Θ1) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> uniq Θ0 -> uniq Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a -> uniq Θ0 -> uniq Θ1).
Proof.
  apply a_assign_unify_consis_mutind.
  (* ---------- a_assign ---------- *)
  - (* univ_ghost_id : output = input *)
    intros Θ0 α Hu. simpl_env in Hu. exact Hu.
  - (* solve_m : the guessed block avoids the whole merged input *)
    intros Θ0 Ξ α P βs τ Hnα Hg Hm Huβ Hfr Hu.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by solve_uniq.
    assert (HαΞΘ : α `notin` dom (Ξ ++ Θ0)) by solve_uniq.
    assert (Hdβ : disjoint βs (Ξ ++ Θ0)).
    { apply disjoint_from_pointwise. intros α1 Hα1.
      pose proof (Hfr α1 Hα1) as Hf. rewrite dom_app in *.
      clear - Hf. fsetdec. }
    assert (Hαβ : α `notin` dom βs).
    { intro Hαβ. pose proof (Hfr α Hαβ) as Hf. clear - Hf. fsetdec. }
    apply uniq_push; [ apply uniq_app_4; assumption | ].
    rewrite dom_app. clear - HαΞΘ Hαβ. fsetdec.
  - (* assign : the re-attached head is the rule's own premise *)
    intros Θ0 Θ1 Ξ α β τ P P' Hfl Hbar Hc IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  - (* depend : re-association *)
    intros Θ0 Θ1 Ξ α β P Hne Hin Ha IH Hu.
    apply IH. simpl_env; solve_uniq.
  - (* skip *)
    intros Θ0 Θ1 Ξ α β P Hne Hni Hbar Ha IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  - (* skip_rigid *)
    intros Θ0 Θ1 Ξ α β P Hni Hbar Ha IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  - (* skip_tm_var *)
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  - (* skip_tm_skl *)
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  (* ---------- a_unify ---------- *)
  - (* flex_id : output = input *)
    intros Θ0 α Hfα Hu. exact Hu.
  - (* flex_l : the head is only DEFINED *)
    intros Θ0 α β Hne Hfβ Hu. solve_uniq.
  - (* flex_r *)
    intros Θ0 α β Hne Hfα Hu. solve_uniq.
  - (* flex_assign *)
    intros Θ0 Θ1 α1 τ α β Q Hfα Hfβ Hbar Hc IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  - (* flex_skip *)
    intros Θ0 Θ1 α1 α β Hne1 Hne2 Hbar Hu0 IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  - (* skip_other *)
    intros Θ0 Θ1 c b α β Hb Hbar Hu0 IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  (* ---------- a_consis ---------- *)
  - (* ghost *) intros Δ1 Δ2 Θ0 P0 Hi Hu. exact Hu.
  - (* unit *) intros Δ1 Δ2 Θ0 Hu. exact Hu.
  - (* rigid *) intros Δ1 Δ2 Θ0 α Hb Hu. exact Hu.
  - (* arrow *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2 Hu.
    apply IH2, IH1, Hu.
  - (* forall_inh : the binder enters the premise and is stripped again *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH Hu.
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0)).
    { apply uniq_push; [ exact Hu | ].
      pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec. }
    pose proof (IH Hu') as Hu1. solve_uniq.
  - (* forall_syn *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH Hu.
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0)).
    { apply uniq_push; [ exact Hu | ].
      pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec. }
    pose proof (IH Hu') as Hu1. solve_uniq.
  - (* univ_ghost *) intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hc IH Hu. apply IH, Hu.
  - (* univ_ghost1 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH Hu.
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0)).
    { apply uniq_push; [ exact Hu | ].
      pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec. }
    pose proof (IH Hu') as Hu1. solve_uniq.
  - (* univ_ghost2 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH Hu. apply IH, Hu.
  - (* flex *) intros Δ1 Δ2 Θ0 Θ1 α β Hu0 IH Hu. apply IH, Hu.
  - (* flex_l *)
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hnhole Ha IH Hu. apply IH. simpl_env. exact Hu.
  - (* flex_r *)
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hnhole Ha IH Hu. apply IH. simpl_env. exact Hu.
  - (* ghost_r *) intros Δ1 Δ2 Θ0 P Hi Hu. exact Hu.
  - (* univ_ghost_r *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH Hu. apply IH, Hu.
Qed.

(* ===================================================================== *)
(*  §6  Rename support: set-rename, var-subst computation, transports     *)
(* ===================================================================== *)

(** Renaming inside an atom set: [α ↦ β], other atoms unchanged. *)
Definition rn_set (β α : atom) (s : atoms) : atoms :=
  if mem α s then add β (remove α s) else s.

Lemma rn_set_notin : forall β α s,
  α `notin` s -> rn_set β α s [=] s.
Proof.
  intros. unfold rn_set.
  destruct (mem α s) eqn:Hm.
  - apply mem_iff in Hm. contradiction.
  - reflexivity.
Qed.

Lemma rn_set_add_same : forall β α s,
  α `notin` s -> rn_set β α (add α s) [=] add β s.
Proof.
  intros. unfold rn_set.
  destruct (mem α (add α s)) eqn:Hm.
  - clear - H. fsetdec.
  - apply not_mem_iff in Hm. exfalso. apply Hm. fsetdec.
Qed.

Lemma rn_set_add_other : forall β' α β s,
  β <> α -> rn_set β' α (add β s) [=] add β (rn_set β' α s).
Proof.
  intros. unfold rn_set.
  destruct (mem α (add β s)) eqn:Hm1;
    destruct (mem α s) eqn:Hm2.
  - clear - H. fsetdec.
  - apply mem_iff in Hm1.
    apply not_mem_iff in Hm2.
    exfalso. clear - Hm1 Hm2 H. fsetdec.
  - apply not_mem_iff in Hm1.
    apply mem_iff in Hm2.
    exfalso. clear - Hm1 Hm2. fsetdec.
  - reflexivity.
Qed.

Lemma rn_set_upper : forall β α s, rn_set β α s [<=] add β s.
Proof.
  intros. unfold rn_set. destruct (mem α s); fsetdec.
Qed.

Lemma rn_set_inter_subst_empty : forall β α Δ P,
  Δ ∩ ftvar_in_pskl P [=] empty ->
  β `notin` Δ ->
  β `notin` ftvar_in_pskl P ->
  (rn_set β α Δ) ∩
    (ftvar_in_pskl (subst_pskl_in_pskl (pskl_var_f β) α P)) [=] empty.
Proof.
  intros * Hi HβΔ HYP.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P)) as [HαP | HαP].
  - (* α occurs in P: then α ∉ Δ, so rn Δ [=] Δ; the substituted ftv is
       bounded by {β} ∪ (ftv P \ {α}) *)
    assert (HαΔ : α `notin` Δ) by (clear - Hi HαP; fsetdec).
    pose proof (rn_set_notin β HαΔ) as Hrn.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  P (pskl_var_f β) α) as Hup.
    simpl in Hup. clear - Hi Hrn Hup HβΔ. fsetdec.
  - (* α does not occur: the substitution is the identity *)
    rewrite subst_pskl_in_pskl_fresh_eq; [ | exact HαP ].
    unfold rn_set.
    destruct (mem α Δ) eqn:Hm.
    + apply mem_iff in Hm.
      clear - Hi HYP. fsetdec.
    + exact Hi.
Qed.

(** Substitution on a variable, computed. *)
Lemma subst_pskl_var_eq : forall P α,
  subst_pskl_in_pskl P α (pskl_var_f α) = P.
Proof.
  intros. simpl.
  destruct_if;
    [ reflexivity | congruence ].
Qed.

Lemma subst_pskl_var_neq : forall P α s,
  s <> α ->
  subst_pskl_in_pskl P α (pskl_var_f s) = pskl_var_f s.
Proof.
  intros. simpl.
  destruct_if;
    [ subst; congruence | reflexivity ].
Qed.

(** The [<> ◇] guard the consistency FlexL/FlexR rows carry (algo/def_rules.v)
    survives a RIGID RENAME: the replacement is a variable, so no constructor
    can turn into a ghost.  ⚠️ It does NOT survive an arbitrary substitution —
    [subst ◇ α (pskl_var_f α)] is a ghost — which is why this is stated for a
    variable replacement only. *)
Lemma subst_pskl_var_not_ghost : forall (β α : atom) P,
  P <> pskl_ghost ->
  subst_pskl_in_pskl (pskl_var_f β) α P <> pskl_ghost.
Proof.
  intros * H. destruct P; simpl; try discriminate; [ | congruence ].
  destruct_if; discriminate.
Qed.

(** Swapping the name of a rigid mid entry under a binding NOT at it. *)
Lemma binds_mid_swap : forall (Ξ Θ : aenv) α β (b bm : abind) x,
  binds x b (Ξ ++ (α ~ bm) ++ Θ) ->
  x <> α ->
  binds x b (Ξ ++ (β ~ bm) ++ Θ).
Proof.
  unfold binds. intros * Hb Hne.
  apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb | Hb]; [ left; assumption | right ].
  apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb | Hb]; [ | right; assumption ].
  destruct Hb as [Hb | []]. inversion Hb; subst. congruence.
Qed.

Lemma a_flex_tvar_mid_swap : forall (Ξ Θ : aenv) α β β1 (bm : abind),
  a_flex_tvar (Ξ ++ (α ~ bm) ++ Θ) β1 ->
  β1 <> α ->
  a_flex_tvar (Ξ ++ (β ~ bm) ++ Θ) β1.
Proof.
  intros * H Hne. destruct H as [Hb | [τ Hb]];
    [ left | right; exists τ ]; eapply binds_mid_swap; eassumption.
Qed.

(** The fresh mid name [β] has only its rigid entry in the renamed
    context. *)
Lemma no_flex_at_fresh_mid : forall (Ξ Θ : aenv) β (b' : abind),
  β `notin` dom (Ξ ++ Θ) ->
  binds β b' (Ξ ++ (β ~ abind_tvar) ++ Θ) ->
  b' = abind_tvar.
Proof.
  intros * Hβ Hb. unfold binds in Hb.
  apply in_app_or in Hb. rewrite dom_app in Hβ.
  destruct Hb as [Hb | Hb].
  - assert (Hd : β `in` dom Ξ) by (eapply binds_In; exact Hb).
    clear - Hβ Hd. fsetdec.
  - apply in_app_or in Hb. destruct Hb as [Hb | Hb].
    + destruct Hb as [Hb | []]. inversion Hb. reflexivity.
    + assert (Hd : β `in` dom Θ) by (eapply binds_In; exact Hb).
      clear - Hβ Hd. fsetdec.
Qed.

(** [a_non_flex] transports through the rename of a rigid mid entry. *)
Lemma a_non_flex_rename : forall (Ξ Θ : aenv) α β P,
  β `notin` dom (Ξ ++ Θ) ->
  a_non_flex (Ξ ++ (α ~ abind_tvar) ++ Θ) P ->
  a_non_flex (Ξ ++ (β ~ abind_tvar) ++ Θ)
    (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros * Hβ [Hlc Hnf]. split.
  - apply subst_pskl_in_pskl_lc_pskl; [ exact Hlc | apply lc_pskl_var_f ].
  - intro Hfl.
    destruct P as [ | n | β1 | | | | ]; simpl in Hfl;
      try solve [ inversion Hfl ].
    revert Hfl.
    destruct_if as [Heqδ | Hneδ]; intro Hfl.
    + (* β1 = α : the image is β, whose only entry is rigid *)
      inversion Hfl; subst.
      * assert (Hcon : abind_flex_mono = abind_tvar)
          by (eapply no_flex_at_fresh_mid; eassumption).
        discriminate.
      * match goal with
        | Hb : binds _ (abind_flex_mono_def ?τ) _ |- _ =>
            assert (Hcon : abind_flex_mono_def τ = abind_tvar)
              by (eapply no_flex_at_fresh_mid; eassumption)
        end. discriminate.
    + (* β1 ≠ α : the entry mirrors back into the original context *)
      destruct (β1 == β) as [-> | HneY].
      * inversion Hfl; subst.
        -- assert (Hcon : abind_flex_mono = abind_tvar)
             by (eapply no_flex_at_fresh_mid; eassumption).
           discriminate.
        -- match goal with
           | Hb : binds _ (abind_flex_mono_def ?τ) _ |- _ =>
               assert (Hcon : abind_flex_mono_def τ = abind_tvar)
                 by (eapply no_flex_at_fresh_mid; eassumption)
           end. discriminate.
      * apply Hnf. inversion Hfl; subst.
        -- apply a_flex__var.
           eapply binds_mid_swap; try exact HneY; eassumption.
        -- eapply a_flex__var_def.
           eapply binds_mid_swap; try exact HneY; eassumption.
Qed.

(* ===================================================================== *)
(*  §7  Last small helpers for the rename                                 *)
(* ===================================================================== *)

(** A flexible variable is distinct from the rigid mid entry (uniqueness)
    and from any name outside the domain. *)
Lemma flex_ne_rigid_mid : forall (Ξr Θb : aenv) α β1 Θi,
  Θi = Ξr ++ (α ~ abind_tvar) ++ Θb ->
  uniq Θi ->
  a_flex_tvar Θi β1 ->
  β1 <> α.
Proof.
  intros * Heq Hu Hf ->.
  assert (Hbα : binds α abind_tvar Θi)
    by (subst; unfold binds; apply in_or_app; right; left; reflexivity).
  destruct Hf as [Hb | [τ Hb]];
    pose proof (binds_unique _ _ _ _ _ Hb Hbα Hu) as Hcon; discriminate.
Qed.

Lemma flex_ne_fresh : forall (Θi : aenv) β1 β,
  a_flex_tvar Θi β1 ->
  β `notin` dom Θi ->
  β1 <> β.
Proof.
  intros * Hf Hβ ->.
  destruct Hf as [Hb | [τ Hb]]; apply binds_In in Hb; contradiction.
Qed.

(** Vacuous rename cases: a non-rigid head against the all-rigid split. *)
Ltac rn_vacuous :=
  match goal with
  | Heq : _ = ?Ξr ++ _ |- _ =>
      destruct Ξr as [ | [?x ?bx] ?Ξr' ]; simpl in Heq; inversion Heq;
      subst;
      match goal with
      | Htv : tvar_prefix ((_, _) :: _) |- _ =>
          solve [ pose proof (tvar_prefix_head Htv); discriminate ]
      end
  end.

Definition auc_uniq_consis :=
  proj2 (proj2 a_assign_unify_consis_uniq).
Definition auc_delta_consis :=
  proj2 (proj2 a_assign_unify_consis_delta_compat).
Definition auc_subject_assign := proj1 a_assign_unify_subject_flex.
Definition auc_subject_unify  := proj1 (proj2 a_assign_unify_subject_flex).

(* ===================================================================== *)
(*  §8  L9: renaming a rigid mid entry under an all-rigid prefix          *)
(* ===================================================================== *)

Lemma a_assign_unify_consis_rename_tvar : forall (α : atom),
  (forall Θi Ξ s P Θo,
     {{ Θi ⊲[ Ξ ] s ≔ P ⊣ Θo }}a ->
     exists L, forall (β0 : atom), β0 `notin` L ->
     forall Ξr Θb, Θi = Ξr ++ (α ~ abind_tvar) ++ Θb ->
     tvar_prefix Ξr ->
     uniq (Ξ ++ Θi) ->
     β0 `notin` dom (Ξ ++ Θi) ->
     β0 `notin` dom Θo ->
     β0 `notin` ftvar_in_pskl P ->
     s <> α -> s <> β0 ->
     exists Θt,
       Θo = Ξr ++ (α ~ abind_tvar) ++ Θt /\
       {{ (Ξr ++ (β0 ~ abind_tvar) ++ Θb) ⊲[ Ξ ] s ≔
         (subst_pskl_in_pskl (pskl_var_f β0) α P)
         ⊣ (Ξr ++ (β0 ~ abind_tvar) ++ Θt) }}a) /\
  (forall Θi s1 s2 Θo,
     {{ Θi ⊲ s1 ≈ᵘ s2 ⊣ Θo }}a ->
     exists L, forall (β0 : atom), β0 `notin` L ->
     forall Ξr Θb, Θi = Ξr ++ (α ~ abind_tvar) ++ Θb ->
     tvar_prefix Ξr ->
     uniq Θi ->
     β0 `notin` dom Θi ->
     β0 `notin` dom Θo ->
     s1 <> α -> s1 <> β0 -> s2 <> α -> s2 <> β0 ->
     exists Θt,
       Θo = Ξr ++ (α ~ abind_tvar) ++ Θt /\
       {{ (Ξr ++ (β0 ~ abind_tvar) ++ Θb) ⊲ s1 ≈ᵘ s2
         ⊣ (Ξr ++ (β0 ~ abind_tvar) ++ Θt) }}a) /\
  (forall Δ1 Δ2 Θi P0 P P' Θo,
     {{ Θi ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θo }}a ->
     exists L, forall (β0 : atom), β0 `notin` L ->
     forall Ξr Θb, Θi = Ξr ++ (α ~ abind_tvar) ++ Θb ->
     tvar_prefix Ξr ->
     uniq Θi ->
     β0 `notin` dom Θi ->
     β0 `notin` dom Θo ->
     β0 `notin` ftvar_in_pskl P0 ->
     β0 `notin` ftvar_in_pskl P ->
     β0 `notin` ftvar_in_pskl P' ->
     β0 `notin` Δ1 ->
     β0 `notin` Δ2 ->
     exists Θt,
       Θo = Ξr ++ (α ~ abind_tvar) ++ Θt /\
       {{ (Ξr ++ (β0 ~ abind_tvar) ++ Θb)
         ⊢[ (rn_set β0 α Δ1) | (rn_set β0 α Δ2)
         | (subst_pskl_in_pskl (pskl_var_f β0) α P0) ]
         (subst_pskl_in_pskl (pskl_var_f β0) α P)
         ∼ (subst_pskl_in_pskl (pskl_var_f β0) α P')
         ⊣ (Ξr ++ (β0 ~ abind_tvar) ++ Θt) }}a).
Proof.
  intros α.
  apply a_assign_unify_consis_mutind.
  - (* univ_ghost_id : flex head, vacuous under the all-rigid split *)
    intros Θ0 s. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* solve_m : flex head, vacuous *)
    intros Θ0 Ξ s P βs τ Hnα Hg Hm Huβ Hfr. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* assign : defined-flex head, vacuous *)
    intros Θ0 Θ1 Ξ s β τ P P' Hfl Hbar Hc IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* depend : flex head, vacuous *)
    intros Θ0 Θ1 Ξ s β P Hne Hin Ha IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* skip : flex head, vacuous *)
    intros Θ0 Θ1 Ξ s β P Hne Hni Hbar Ha IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* skip_rigid : the walk case — crossing at Ξr = nil *)
    intros Θ0 Θ1 Ξ s β P Hni Hbar Ha IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP Hsα HsY.
    destruct Ξr as [ | [x bx] Ξr' ]; simpl in Heq.
    + inversion Heq; subst.
      (* CROSSING : β = α; below is reused verbatim, F swaps α ↦ β0 *)
      exists Θ1. split; [ reflexivity | ].
      rewrite subst_pskl_in_pskl_fresh_eq; [ | exact Hni ].
      simpl. apply a_assign__skip_rigid;
        [ exact HYP
        | simpl dom in HYo; clear - HYo; fsetdec
        | ].
      exact Ha.
    + (* RECURSION : the head is a prefix rigid *)
      injection Heq. intros.
      subst x. subst bx. subst Θ0.
      assert (Hu' : uniq (Ξ ++ Ξr' ++ (α ~ abind_tvar) ++ Θb))
        by (simpl_env in *; solve_uniq).
      assert (HYi' : β0 `notin` dom (Ξ ++ Ξr' ++ (α ~ abind_tvar) ++ Θb))
        by (repeat rewrite dom_app in *; simpl dom in *;
            clear - HYi; fsetdec).
      assert (HYo' : β0 `notin` dom Θ1)
        by (simpl dom in HYo; clear - HYo; fsetdec).
      destruct (IH β0 HL Ξr' Θb eq_refl (tvar_prefix_tail Htv) Hu' HYi' HYo'
                  HYP Hsα HsY) as [Θt [-> Hren]].
      exists Θt. split; [ reflexivity | ].
      assert (Hββ0 : β <> β0).
      { intros ->. repeat rewrite dom_app in HYi. simpl dom in HYi.
        clear - HYi. fsetdec. }
      apply a_assign__skip_rigid; [ | | exact Hren ].
      * pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                      P (pskl_var_f β0) α) as Hup.
        simpl in Hup.
        clear - Hni Hup Hββ0. fsetdec.
      * (* the walked β misses the RENAMED output too: the rename moves
           α ↦ β0 only, and β is neither *)
        clear - Hbar Hββ0.
        repeat rewrite dom_app in *. simpl dom in *. fsetdec.
  - (* skip_tm_var : term head, vacuous *)
    intros Θ0 Θ1 Ξ s x P' P Hbar Ha IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* skip_tm_skl : term head, vacuous *)
    intros Θ0 Θ1 Ξ s x P' P Hbar Ha IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* flex_id : identity node *)
    intros Θ0 s Hf. exists empty.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo Hs1α Hs1Y Hs2α Hs2Y.
    subst Θ0.
    exists Θb. split; [ reflexivity | ].
    apply a_unify__flex_id.
    eapply a_flex_tvar_mid_swap; [ exact Hf | exact Hs1α ].
  - (* flex_l : flex head, vacuous *)
    intros Θ0 s1 s2 Hne Hf. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* flex_r : flex head, vacuous *)
    intros Θ0 s1 s2 Hne Hf. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* flex_assign : defined-flex head, vacuous *)
    intros Θ0 Θ1 α1 τ s1 s2 P' Hfα Hfβ Hbar Hc IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* flex_skip : flex head, vacuous *)
    intros Θ0 Θ1 α1 s1 s2 Hne1 Hne2 Hbar Hun IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* skip_other : the walk case — crossing at Ξr = nil *)
    intros Θ0 Θ1 c b s1 s2 Hb Hbar Hun IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo Hs1α Hs1Y Hs2α Hs2Y.
    destruct Ξr as [ | [x bx] Ξr' ]; simpl in Heq.
    + inversion Heq; subst.
      (* CROSSING : c = α, b = tvar *)
      exists Θ1. split; [ reflexivity | ].
      apply a_unify__skip_other;
        [ left; reflexivity
        | simpl dom in HYo; clear - HYo; fsetdec
        | ].
      exact Hun.
    + (* RECURSION *)
      injection Heq. intros.
      subst x. subst bx. subst Θ0.
      assert (Hu' : uniq (Ξr' ++ (α ~ abind_tvar) ++ Θb)) by solve_uniq.
      assert (HYi' : β0 `notin` dom (Ξr' ++ (α ~ abind_tvar) ++ Θb))
        by (simpl dom in HYi; clear - HYi; fsetdec).
      assert (HYo' : β0 `notin` dom Θ1)
        by (simpl dom in HYo; clear - HYo; fsetdec).
      destruct (IH β0 HL Ξr' Θb eq_refl (tvar_prefix_tail Htv) Hu' HYi' HYo'
                  Hs1α Hs1Y Hs2α Hs2Y) as [Θt [-> Hren]].
      exists Θt. split; [ reflexivity | ].
      assert (Hcβ0 : c <> β0).
      { intros ->. simpl dom in HYi. clear - HYi. fsetdec. }
      apply a_unify__skip_other;
        [ exact Hb
        | clear - Hbar Hcβ0;
          repeat rewrite dom_app in *; simpl dom in *; fsetdec
        | exact Hren ].
  - (* ghost : axiom node *)
    intros Δ1 Δ2 Θ0 P0 Hi. exists empty.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    subst Θ0. exists Θb. split; [ reflexivity | ].
    simpl. apply a_consis__ghost.
    apply rn_set_inter_subst_empty; assumption.
  - (* unit : axiom node *)
    intros Δ1 Δ2 Θ0. exists empty.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    subst Θ0. exists Θb. split; [ reflexivity | ].
    simpl. apply a_consis__unit.
  - (* rigid : axiom node, β1 = α or not *)
    intros Δ1 Δ2 Θ0 β1 Hbδ. exists empty.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    subst Θ0. exists Θb. split; [ reflexivity | ].
    destruct (β1 == α) as [-> | Hne].
    + rewrite subst_pskl_var_eq.
      apply a_consis__rigid.
      unfold binds. apply in_or_app. right. left. reflexivity.
    + rewrite subst_pskl_var_neq; [ | exact Hne ].
      apply a_consis__rigid.
      eapply binds_mid_swap; [ exact Hbδ | exact Hne ].
  - (* arrow : thread the two components *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2.
    destruct IH1 as [L1 IH1]. destruct IH2 as [L2 IH2].
    exists (L1 `union` L2).
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP0, HYP, HYQ.
    assert (HYo1 : β0 `notin` dom Θ1).
    { pose proof (auc_dom_mono_consis Hc2) as Hd.
      clear - HYo Hd. fsetdec. }
    destruct (IH1 β0 ltac:(clear - HL; solve_notin_auto) Ξr Θb Heq Htv Hu HYi HYo1
                ltac:(clear - HYP0; solve_notin_auto)
                ltac:(clear - HYP; solve_notin_auto)
                ltac:(clear - HYQ; solve_notin_auto)
                Hβ0Δ1 Hβ0Δ2) as [Θm [HeqΘ1 Hren1]].
    assert (Hu1 : uniq Θ1)
      by (apply (auc_uniq_consis Hc1); subst; exact Hu).
    assert (HYi1 : β0 `notin` dom Θ1) by exact HYo1.
    destruct (IH2 β0 ltac:(clear - HL; solve_notin_auto) Ξr Θm HeqΘ1 Htv Hu1 HYi1 HYo
                ltac:(clear - HYP0; solve_notin_auto)
                ltac:(clear - HYP; solve_notin_auto)
                ltac:(clear - HYQ; solve_notin_auto)
                Hβ0Δ1 Hβ0Δ2) as [Θt [HeqΘ2 Hren2]].
    exists Θt. split; [ exact HeqΘ2 | ].
    simpl. eapply a_consis__arrow; [ exact Hren1 | exact Hren2 ].
  - (* forall_inh : the rule's own binder joins the avoid-set *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α0 Hfr Hprem IH.
    (* ⚙ TWO INDEPENDENT GENERATORS.  [β0] and the rule's own binder [α0]
       are both merely fresh for [Θ0], so no side condition on the lemma's
       variables can separate them — and if they collide the rebuilt
       conclusion binds [β0] twice.  The derivation is the only thing that
       knows [α0], so the lemma HANDS BACK its avoid-set. *)
    destruct IH as [Lih IH].
    exists (Lih `union` singleton α0).
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP0, HYP, HYQ.
    assert (Hα0β0 : α0 <> β0) by (clear - HL; fsetdec).
    assert (Hβ0α0 : β0 <> α0) by (clear - Hα0β0; congruence).
    assert (HinΘ0 : α `in` ftvar_in_aenv Θ0)
      by (rewrite Heq; rewrite ftvar_in_aenv_app; simpl; clear; fsetdec).
    assert (Hαα0 : α <> α0)
      by (intro Hbad; subst; clear - Hfr HinΘ0; fsetdec).
    assert (Hα0Θ0 : α0 `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec).
    (* the conclusion's output is [close α0 Q], so [β0] misses [Q] itself *)
    assert (HYQ' : β0 `notin` ftvar_in_pskl Q).
    { rewrite ftvar_in_pskl_close_pskl_wrt_pskl in HYQ.
      clear - HYQ Hβ0α0. fsetdec. }
    destruct (IH β0 ltac:(clear - HL; solve_notin_auto)
                ((α0, abind_tvar) :: Ξr) Θb
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)
                ltac:(apply uniq_push; [ exact Hu | exact Hα0Θ0 ])
                ltac:(simpl dom; clear - HYi Hβ0α0; solve_notin_auto)
                ltac:(simpl dom; clear - HYo Hβ0α0; solve_notin_auto)
                ltac:(apply notin_ftvar_open_pskl_var;
                      [ exact Hβ0α0 | exact HYP0 ])
                ltac:(apply notin_ftvar_open_pskl_var;
                      [ exact Hβ0α0 | exact HYP ])
                ltac:(exact HYQ')
                ltac:(clear - Hβ0Δ1 Hβ0α0; solve_notin_auto)
                ltac:(clear - Hβ0Δ2 Hβ0α0; solve_notin_auto))
      as [Θt [HeqO Hren]].
    simpl in HeqO. inversion HeqO as [HeqO'].
    exists Θt.
    split; [ solve [ exact HeqO' | reflexivity | simpl_env; reflexivity ] | ].
    (* normalize the IH's substituted opens and renamed Δs *)
    assert (Ho0 : subst_pskl_in_pskl (pskl_var_f β0) α
                    (open_pskl_wrt_pskl P0 (pskl_var_f α0))
                  = open_pskl_wrt_pskl
                      (subst_pskl_in_pskl (pskl_var_f β0) α P0)
                      (pskl_var_f α0))
      by (symmetry; apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
          [ exact Hαα0 | apply lc_pskl_var_f ]).
    assert (Ho1 : subst_pskl_in_pskl (pskl_var_f β0) α
                    (open_pskl_wrt_pskl P (pskl_var_f α0))
                  = open_pskl_wrt_pskl
                      (subst_pskl_in_pskl (pskl_var_f β0) α P)
                      (pskl_var_f α0))
      by (symmetry; apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
          [ exact Hαα0 | apply lc_pskl_var_f ]).
    rewrite Ho0, Ho1 in Hren.
    simpl.
    rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl Q (pskl_var_f β0) α α0
               (lc_pskl_var_f β0) Hαα0
               ltac:(simpl; clear - Hα0β0; solve_notin_auto)).
    simpl_env in Hren. simpl_env.
    apply a_consis__forall_inh with (α := α0).
    + (* the rule's side condition, transported across the rename *)
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P0 (pskl_var_f β0) α)
        as Hu0.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f β0) α)
        as Hu1.
      simpl in Hu0, Hu1.
      pose proof (rn_set_upper β0 α Δ1) as Hr1.
      pose proof (rn_set_upper β0 α Δ2) as Hr2.
      assert (HfrA : α0 `notin` ftvar_in_aenv (Ξr ++ (β0 ~ abind_tvar) ++ Θb)).
      { rewrite Heq in Hfr.
        repeat rewrite ftvar_in_aenv_app in Hfr |- *.
        simpl in Hfr |- *. clear - Hfr Hα0β0. fsetdec. }
      repeat apply notin_union_3.
      * exact HfrA.
      * clear - Hfr Hu0 Hα0β0. fsetdec.
      * clear - Hfr Hu1 Hα0β0. fsetdec.
      * clear - Hfr Hr1 Hα0β0. fsetdec.
      * clear - Hfr Hr2 Hα0β0. fsetdec.
    + eapply auc_delta_consis;
        [ exact Hren
        | apply rn_set_add_other; clear - Hαα0; congruence
        | apply rn_set_add_other; clear - Hαα0; congruence ].
  - (* forall_syn : as ForallInh; the input skeleton is carried unchanged *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α0 Hfr Hprem IH.
    (* ⚙ TWO INDEPENDENT GENERATORS.  [β0] and the rule's own binder [α0]
       are both merely fresh for [Θ0], so no side condition on the lemma's
       variables can separate them — and if they collide the rebuilt
       conclusion binds [β0] twice.  The derivation is the only thing that
       knows [α0], so the lemma HANDS BACK its avoid-set. *)
    destruct IH as [Lih IH].
    exists (Lih `union` singleton α0).
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP0, HYP, HYQ.
    assert (Hα0β0 : α0 <> β0) by (clear - HL; fsetdec).
    assert (Hβ0α0 : β0 <> α0) by (clear - Hα0β0; congruence).
    assert (HinΘ0 : α `in` ftvar_in_aenv Θ0)
      by (rewrite Heq; rewrite ftvar_in_aenv_app; simpl; clear; fsetdec).
    assert (Hαα0 : α <> α0)
      by (intro Hbad; subst; clear - Hfr HinΘ0; fsetdec).
    assert (Hα0Θ0 : α0 `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec).
    (* the conclusion's output is [close α0 Q], so [β0] misses [Q] itself *)
    assert (HYQ' : β0 `notin` ftvar_in_pskl Q).
    { rewrite ftvar_in_pskl_close_pskl_wrt_pskl in HYQ.
      clear - HYQ Hβ0α0. fsetdec. }
    destruct (IH β0 ltac:(clear - HL; solve_notin_auto)
                ((α0, abind_tvar) :: Ξr) Θb
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)
                ltac:(apply uniq_push; [ exact Hu | exact Hα0Θ0 ])
                ltac:(simpl dom; clear - HYi Hβ0α0; solve_notin_auto)
                ltac:(simpl dom; clear - HYo Hβ0α0; solve_notin_auto)
                ltac:(simpl; exact HYP0)
                ltac:(apply notin_ftvar_open_pskl_var;
                      [ exact Hβ0α0 | exact HYP ])
                ltac:(exact HYQ')
                ltac:(clear - Hβ0Δ1; solve_notin_auto)
                ltac:(clear - Hβ0Δ2 Hβ0α0; solve_notin_auto))
      as [Θt [HeqO Hren]].
    simpl in HeqO. inversion HeqO as [HeqO'].
    exists Θt.
    split; [ solve [ exact HeqO' | reflexivity | simpl_env; reflexivity ] | ].
    assert (Ho1 : subst_pskl_in_pskl (pskl_var_f β0) α
                    (open_pskl_wrt_pskl P (pskl_var_f α0))
                  = open_pskl_wrt_pskl
                      (subst_pskl_in_pskl (pskl_var_f β0) α P)
                      (pskl_var_f α0))
      by (symmetry; apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
          [ exact Hαα0 | apply lc_pskl_var_f ]).
    rewrite Ho1 in Hren.
    simpl.
    rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl Q (pskl_var_f β0) α α0
               (lc_pskl_var_f β0) Hαα0
               ltac:(simpl; clear - Hα0β0; solve_notin_auto)).
    simpl_env in Hren. simpl_env.
    apply a_consis__forall_syn with (α := α0).
    + (* the rule's side condition, transported across the rename *)
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P0 (pskl_var_f β0) α)
        as Hu0.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f β0) α)
        as Hu1.
      simpl in Hu0, Hu1.
      pose proof (rn_set_upper β0 α Δ1) as Hr1.
      pose proof (rn_set_upper β0 α Δ2) as Hr2.
      assert (HfrA : α0 `notin` ftvar_in_aenv (Ξr ++ (β0 ~ abind_tvar) ++ Θb)).
      { rewrite Heq in Hfr.
        repeat rewrite ftvar_in_aenv_app in Hfr |- *.
        simpl in Hfr |- *. clear - Hfr Hα0β0. fsetdec. }
      repeat apply notin_union_3.
      * exact HfrA.
      * clear - Hfr Hu0 Hα0β0. fsetdec.
      * clear - Hfr Hu1 Hα0β0. fsetdec.
      * clear - Hfr Hr1 Hα0β0. fsetdec.
      * clear - Hfr Hr2 Hα0β0. fsetdec.
    + eapply auc_delta_consis;
        [ exact Hren
        | reflexivity
        | apply rn_set_add_other; clear - Hαα0; congruence ].
  - (* univ_ghost : pass-through *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hc IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP0, HYP, HYQ.
    destruct (IH β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2)
      as [Θt [HeqO Hren]].
    exists Θt. split; [ exact HeqO | ].
    simpl. apply a_consis__univ_ghost. exact Hren.
  - (* univ_ghost1 : as ForallInh; the subject is carried unchanged *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α0 Hfr Hprem IH.
    (* ⚙ TWO INDEPENDENT GENERATORS.  [β0] and the rule's own binder [α0]
       are both merely fresh for [Θ0], so no side condition on the lemma's
       variables can separate them — and if they collide the rebuilt
       conclusion binds [β0] twice.  The derivation is the only thing that
       knows [α0], so the lemma HANDS BACK its avoid-set. *)
    destruct IH as [Lih IH].
    exists (Lih `union` singleton α0).
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP0, HYP, HYQ.
    assert (Hα0β0 : α0 <> β0) by (clear - HL; fsetdec).
    assert (Hβ0α0 : β0 <> α0) by (clear - Hα0β0; congruence).
    assert (HinΘ0 : α `in` ftvar_in_aenv Θ0)
      by (rewrite Heq; rewrite ftvar_in_aenv_app; simpl; clear; fsetdec).
    assert (Hαα0 : α <> α0)
      by (intro Hbad; subst; clear - Hfr HinΘ0; fsetdec).
    assert (Hα0Θ0 : α0 `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec).
    (* the conclusion's output is [close α0 Q], so [β0] misses [Q] itself *)
    assert (HYQ' : β0 `notin` ftvar_in_pskl Q).
    { rewrite ftvar_in_pskl_close_pskl_wrt_pskl in HYQ.
      clear - HYQ Hβ0α0. fsetdec. }
    destruct (IH β0 ltac:(clear - HL; solve_notin_auto)
                ((α0, abind_tvar) :: Ξr) Θb
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)
                ltac:(apply uniq_push; [ exact Hu | exact Hα0Θ0 ])
                ltac:(simpl dom; clear - HYi Hβ0α0; solve_notin_auto)
                ltac:(simpl dom; clear - HYo Hβ0α0; solve_notin_auto)
                ltac:(apply notin_ftvar_open_pskl_var;
                      [ exact Hβ0α0 | exact HYP0 ])
                ltac:(simpl; exact HYP)
                ltac:(exact HYQ')
                ltac:(clear - Hβ0Δ1 Hβ0α0; solve_notin_auto)
                ltac:(clear - Hβ0Δ2; solve_notin_auto))
      as [Θt [HeqO Hren]].
    simpl in HeqO. inversion HeqO as [HeqO'].
    exists Θt.
    split; [ solve [ exact HeqO' | reflexivity | simpl_env; reflexivity ] | ].
    assert (Ho0 : subst_pskl_in_pskl (pskl_var_f β0) α
                    (open_pskl_wrt_pskl P0 (pskl_var_f α0))
                  = open_pskl_wrt_pskl
                      (subst_pskl_in_pskl (pskl_var_f β0) α P0)
                      (pskl_var_f α0))
      by (symmetry; apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
          [ exact Hαα0 | apply lc_pskl_var_f ]).
    rewrite Ho0 in Hren.
    simpl.
    rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl Q (pskl_var_f β0) α α0
               (lc_pskl_var_f β0) Hαα0
               ltac:(simpl; clear - Hα0β0; solve_notin_auto)).
    simpl_env in Hren. simpl_env.
    apply a_consis__univ_ghost1 with (α := α0).
    + (* the rule's side condition, transported across the rename *)
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P0 (pskl_var_f β0) α)
        as Hu0.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f β0) α)
        as Hu1.
      simpl in Hu0, Hu1.
      pose proof (rn_set_upper β0 α Δ1) as Hr1.
      pose proof (rn_set_upper β0 α Δ2) as Hr2.
      assert (HfrA : α0 `notin` ftvar_in_aenv (Ξr ++ (β0 ~ abind_tvar) ++ Θb)).
      { rewrite Heq in Hfr.
        repeat rewrite ftvar_in_aenv_app in Hfr |- *.
        simpl in Hfr |- *. clear - Hfr Hα0β0. fsetdec. }
      repeat apply notin_union_3.
      * exact HfrA.
      * clear - Hfr Hu0 Hα0β0. fsetdec.
      * clear - Hfr Hu1 Hα0β0. fsetdec.
      * clear - Hfr Hr1 Hα0β0. fsetdec.
      * clear - Hfr Hr2 Hα0β0. fsetdec.
    + eapply auc_delta_consis;
        [ exact Hren
        | apply rn_set_add_other; clear - Hαα0; congruence
        | reflexivity ].
  - (* univ_ghost2 : pass-through with guarded/non-flex transports *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP.
    destruct (IH β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0
                ltac:(clear - HYP; solve_notin_auto) HYQ Hβ0Δ1 Hβ0Δ2)
      as [Θt [HeqO Hren]].
    exists Θt. split; [ exact HeqO | ].
    simpl. apply a_consis__univ_ghost2.
    + apply guarded_pskl_subst_var. exact Hg.
    + subst Θ0. apply a_non_flex_rename;
        [ | exact Hnf ].
      rewrite dom_app in *. simpl dom in HYi. clear - HYi. fsetdec.
    + exact Hren.
  - (* flex : the unify back-edge *)
    intros Δ1 Δ2 Θ0 Θ1 β11 β12 Hun IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    destruct (auc_subject_unify Hun) as [Hf1 Hf2].
    assert (Hne1α : β11 <> α) by (eapply flex_ne_rigid_mid; eassumption).
    assert (Hne2α : β12 <> α)
      by (eapply flex_ne_rigid_mid; [ exact Heq | exact Hu | exact Hf2 ]).
    assert (Hne1Y : β11 <> β0) by (eapply flex_ne_fresh; eassumption).
    assert (Hne2Y : β12 <> β0)
      by (eapply flex_ne_fresh; [ exact Hf2 | exact HYi ]).
    destruct (IH β0 HL Ξr Θb Heq Htv Hu HYi HYo Hne1α Hne1Y Hne2α Hne2Y)
      as [Θt [HeqO Hren]].
    exists Θt. split; [ exact HeqO | ].
    rewrite (subst_pskl_var_neq (pskl_var_f β0) Hne2α).
    rewrite (subst_pskl_var_neq (pskl_var_f β0) Hne1α).
    apply a_consis__flex. exact Hren.
  - (* flex_l : the assign back-edge *)
    intros Δ1 Δ2 Θ0 Θ1 β1 P0 Hnf Hnhole Ha IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    pose proof (auc_subject_assign Ha) as Hf. simpl in Hf.
    assert (Hneα : β1 <> α) by (eapply flex_ne_rigid_mid; eassumption).
    assert (HneY : β1 <> β0) by (eapply flex_ne_fresh; eassumption).
    destruct (IH β0 HL Ξr Θb Heq Htv
                ltac:(simpl; exact Hu)
                ltac:(simpl; exact HYi)
                HYo HYP0 Hneα HneY)
      as [Θt [HeqO Hren]].
    exists Θt. split; [ exact HeqO | ].
    rewrite (subst_pskl_var_neq (pskl_var_f β0) Hneα).
    apply a_consis__flex_l.
    + subst Θ0. apply a_non_flex_rename; [ | exact Hnf ].
      clear - HYi. rewrite dom_app in *. simpl dom in HYi. fsetdec.
    + apply subst_pskl_var_not_ghost. exact Hnhole.
    + exact Hren.
  - (* flex_r : the assign back-edge, mirrored *)
    intros Δ1 Δ2 Θ0 Θ1 β1 P Hnf Hnhole Ha IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    pose proof (auc_subject_assign Ha) as Hf. simpl in Hf.
    assert (Hneα : β1 <> α) by (eapply flex_ne_rigid_mid; eassumption).
    assert (HneY : β1 <> β0) by (eapply flex_ne_fresh; eassumption).
    destruct (IH β0 HL Ξr Θb Heq Htv
                ltac:(simpl; exact Hu)
                ltac:(simpl; exact HYi)
                HYo HYP Hneα HneY)
      as [Θt [HeqO Hren]].
    exists Θt. split; [ exact HeqO | ].
    rewrite (subst_pskl_var_neq (pskl_var_f β0) Hneα).
    apply a_consis__flex_r.
    + subst Θ0. apply a_non_flex_rename; [ | exact Hnf ].
      clear - HYi. rewrite dom_app in *. simpl dom in HYi. fsetdec.
    + apply subst_pskl_var_not_ghost. exact Hnhole.
    + exact Hren.
  - (* ghost_r : axiom node *)
    intros Δ1 Δ2 Θ0 P Hi. exists empty.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    subst Θ0. exists Θb. split; [ reflexivity | ].
    simpl. apply a_consis__ghost_r.
    apply rn_set_inter_subst_empty; assumption.
  - (* univ_ghost_r : pass-through with guarded/non-flex transports *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP0.
    destruct (IH β0 HL Ξr Θb Heq Htv Hu HYi HYo
                ltac:(clear - HYP0; solve_notin_auto) HYP HYQ Hβ0Δ1 Hβ0Δ2)
      as [Θt [HeqO Hren]].
    exists Θt. split; [ exact HeqO | ].
    simpl. apply a_consis__univ_ghost_r.
    + apply guarded_pskl_subst_var. exact Hg.
    + subst Θ0. apply a_non_flex_rename; [ | exact Hnf ].
      rewrite dom_app in *. simpl dom in HYi. clear - HYi. fsetdec.
    + exact Hren.
Qed.

(* ===================================================================== *)
(*  §9  Cofinite admissibility of the three exists-fresh ∀ rows           *)
(* ===================================================================== *)

(** The freshness campaign's cluster 4 converted [a_consis]'s three ∀ rows
    to exists-fresh + explicit close (DESIGN.md §4.3).  Unlike the look /
    solve / guess clusters this was NOT a repair: these rows CLOSE, so the
    cofinite rendering was already faithful.  These three lemmas are the
    machine-checked half of that claim — the cofinite rule is ADMISSIBLE —
    and they are also the tool for any consumer that wants a family: pick
    one sufficiently fresh α and the [close]/[open] round-trip does the
    rest, no renaming needed in this direction.

    The converse direction (one instance ⟹ the whole family) is
    [a_assign_unify_consis_rename_tvar] above, applied at [Ξr = nil]; it is
    what §10's decoration lemma uses. *)

Lemma a_consis_forall_inh_cofinite : forall L Δ1 Δ2 Θ0 Θ1 P0 P Q,
  (forall α, α `notin` L ->
     {{ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | (add α Δ2)
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼
       (open_pskl_wrt_pskl Q (pskl_var_f α))
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}a) ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
    (pskl_all_syn P) ∼ (pskl_all_syn Q) ⊣ Θ1 }}a.
Proof.
  intros L Δ1 Δ2 Θ0 Θ1 P0 P Q Hbody.
  pick fresh α for (L `union` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
                    `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                    `union` Δ1 `union` Δ2).
  replace Q with
    (close_pskl_wrt_pskl α (open_pskl_wrt_pskl Q (pskl_var_f α)))
    by (apply close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        clear - Fr; fsetdec).
  apply a_consis__forall_inh with (α := α);
    [ clear - Fr; fsetdec | apply Hbody; clear - Fr; fsetdec ].
Qed.

Lemma a_consis_forall_syn_cofinite : forall L Δ1 Δ2 Θ0 Θ1 P0 P Q,
  (forall α, α `notin` L ->
     {{ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ Δ1 | (add α Δ2) | (pskl_univ_ghost P0) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼
       (open_pskl_wrt_pskl Q (pskl_var_f α))
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}a) ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
    (pskl_all_syn P) ∼ (pskl_all_syn Q) ⊣ Θ1 }}a.
Proof.
  intros L Δ1 Δ2 Θ0 Θ1 P0 P Q Hbody.
  pick fresh α for (L `union` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
                    `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                    `union` Δ1 `union` Δ2).
  replace Q with
    (close_pskl_wrt_pskl α (open_pskl_wrt_pskl Q (pskl_var_f α)))
    by (apply close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        clear - Fr; fsetdec).
  apply a_consis__forall_syn with (α := α);
    [ clear - Fr; fsetdec | apply Hbody; clear - Fr; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §10  Lemma [Decorating algorithmic consistency]                       *)
(* ===================================================================== *)

(** If [aconsis[Δ1|Δ2][P0]{Θ0}{P}{Q}{Θ1}] then
    [aconsistag[Δ1|Δ2][P0][·]{Θ0}{P}{Q}{Θ1}]
    (consistency-proofs.tex, lemma:decorating-algorithmic-consistency).

    A SIZE induction, not a structural one.  The decorated [a_consistag] ∀ rows
    are (rightly) still COFINITE while [a_consis]'s are now exists-fresh, so
    each ∀ row must rebuild a whole family from the run's ONE binder — which
    means MOVING that binder with §8's rename, and the moved premise is no
    sub-derivation.  Cluster 3 forced the same shape one layer up
    ([a_consistag_decoration_size], prop_decorate_sub.v §7).

    The measure is [size_pskl P + size_pskl P0]: the SUBJECT alone does not
    work, because UnivGhost1 leaves it fixed at [pskl_univ_ghost P] and shrinks
    only the input, while ForallSyn does the opposite.

    (Until the [F]-deletion this lemma was additionally generalized over the
    used-name set, so that the induction's indices stayed VARIABLES; with [F]
    gone there is nothing left to generalize.) *)

Lemma a_consis_decorate_size : forall n Δ1 Δ2 Θ0 P0 P P' Θ1,
  size_pskl P + size_pskl P0 <= n ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
  uniq Θ0 ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | empty ] (pskl_to_uskl P) ∼ P' ⊣ Θ1 }}da.
Proof.
  induction n as [ | n IHn ];
    intros Δ1 Δ2 Θ0 P0 P P' Θ1 Hsz Hc Hu.
  { pose proof (size_pskl_min P); pose proof (size_pskl_min P0); lia. }
  revert Hsz Hu.
  destruct Hc as
    [ Δ1 Δ2 Θ0 P0 Hi
    | Δ1 Δ2 Θ0
    | Δ1 Δ2 Θ0 α Hb
    | Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hca Hcb
    | Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc
    | Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc
    | Δ1 Δ2 Θ0 Θ1 P0 P Q Hc
    | Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc
    | Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc
    | Δ1 Δ2 Θ0 Θ1 α β Hun
    | Δ1 Δ2 Θ0 Θ1 α P0 Hnf Ha
    | Δ1 Δ2 Θ0 Θ1 α P Hnf Ha
    | Δ1 Δ2 Θ0 P Hi
    | Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc ];
    intros Hsz Hu; simpl in Hsz |- *.
  - (* Ghost *)
    apply a_consistag__ghost; auto. fsetdec.
  - (* Unit *)
    apply a_consistag__unit. fsetdec.
  - (* Rigid *)
    apply a_consistag__rigid; auto. fsetdec.
  - (* Arrow *)
    eapply a_consistag__arrow;
      [ eapply IHn; [ | exact Hca | exact Hu ]; lia
      | eapply IHn;
        [ | exact Hcb | exact (auc_uniq_consis Hca Hu) ]; lia
      | fsetdec ].
  - (* ForallInh (untagged) — rebuild the cofinite family by renaming *)
    (* the rename hands back its own avoid-set (§8): union it into
       the cofinite bound this row was already computing *)
    destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α))
                _ _ _ _ _ _ _ Hc) as [Lrn Hrn].
    apply a_consistag__forall_inh_untagged with
      (L := Lrn `union` singleton α `union` dom Θ0 `union` dom Θ1
            `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
            `union` ftvar_in_pskl Q `union` Δ1 `union` Δ2).
    intros β Hβ.
    assert (Hβα : β <> α) by (apply notin_singleton_1; clear - Hβ; fsetdec).
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfr; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - Hfr; fsetdec).
    assert (HαΔ1 : α `notin` Δ1) by (clear - Hfr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Hfr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec).
    assert (HuΘ : uniq ((α ~ abind_tvar) ++ Θ0)) by solve_uniq.
    assert (Hb1 : β `notin` dom ((α ~ abind_tvar) ++ Θ0))
      by (simpl; clear - Hβ; fsetdec).
    assert (Hb2 : β `notin` dom ((α ~ abind_tvar) ++ Θ1))
      by (simpl; clear - Hβ; fsetdec).
    assert (Hb3 : β `notin`
              ftvar_in_pskl (open_pskl_wrt_pskl P0 (pskl_var_f α)))
      by (apply notin_ftvar_open_pskl_var;
          [ exact Hβα | clear - Hβ; fsetdec ]).
    assert (Hb4 : β `notin`
              ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α)))
      by (apply notin_ftvar_open_pskl_var;
          [ exact Hβα | clear - Hβ; fsetdec ]).
    assert (Hb5 : β `notin` ftvar_in_pskl Q) by (clear - Hβ; fsetdec).
    assert (Hb6 : β `notin` add α Δ1) by (clear - Hβ Hβα; fsetdec).
    assert (Hb7 : β `notin` add α Δ2) by (clear - Hβ Hβα; fsetdec).
    destruct (Hrn β ltac:(clear - Hβ; solve_notin_auto) nil Θ0 eq_refl
                tvar_prefix_nil HuΘ
                Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7) as [Θt [Heq Hren]].
    simpl in Heq. inversion Heq. subst Θt. clear Heq. simpl in Hren.
    rewrite <- (subst_pskl_in_pskl_intro α P0 (pskl_var_f β) HαP0) in Hren.
    rewrite <- (subst_pskl_in_pskl_intro α P (pskl_var_f β) HαP) in Hren.
    rewrite (subst_pskl_in_pskl_spec Q (pskl_var_f β) α) in Hren.
    pose proof (auc_delta_consis Hren
                  (rn_set_add_same β HαΔ1) (rn_set_add_same β HαΔ2)) as Hren'.
    rewrite <- pskl_to_uskl_open_var.
    eapply IHn; [ | exact Hren' | solve_uniq ].
    rewrite ! size_pskl_open_pskl_wrt_pskl_var. lia.
  - (* ForallSyn (untagged) *)
    (* the rename hands back its own avoid-set (§8): union it into
       the cofinite bound this row was already computing *)
    destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α))
                _ _ _ _ _ _ _ Hc) as [Lrn Hrn].
    apply a_consistag__forall_syn_untagged with
      (L := Lrn `union` singleton α `union` dom Θ0 `union` dom Θ1
            `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
            `union` ftvar_in_pskl Q `union` Δ1 `union` Δ2).
    intros β Hβ.
    assert (Hβα : β <> α) by (apply notin_singleton_1; clear - Hβ; fsetdec).
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfr; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - Hfr; fsetdec).
    assert (HαΔ1 : α `notin` Δ1) by (clear - Hfr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Hfr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec).
    assert (HuΘ : uniq ((α ~ abind_tvar) ++ Θ0)) by solve_uniq.
    assert (Hb1 : β `notin` dom ((α ~ abind_tvar) ++ Θ0))
      by (simpl; clear - Hβ; fsetdec).
    assert (Hb2 : β `notin` dom ((α ~ abind_tvar) ++ Θ1))
      by (simpl; clear - Hβ; fsetdec).
    assert (Hb3 : β `notin` ftvar_in_pskl (pskl_univ_ghost P0))
      by (simpl; clear - Hβ; fsetdec).
    assert (Hb4 : β `notin`
              ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α)))
      by (apply notin_ftvar_open_pskl_var;
          [ exact Hβα | clear - Hβ; fsetdec ]).
    assert (Hb5 : β `notin` ftvar_in_pskl Q) by (clear - Hβ; fsetdec).
    assert (Hb6 : β `notin` Δ1) by (clear - Hβ; fsetdec).
    assert (Hb7 : β `notin` add α Δ2) by (clear - Hβ Hβα; fsetdec).
    destruct (Hrn β ltac:(clear - Hβ; solve_notin_auto) nil Θ0 eq_refl
                tvar_prefix_nil HuΘ
                Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7) as [Θt [Heq Hren]].
    simpl in Heq. inversion Heq. subst Θt. clear Heq. simpl in Hren.
    rewrite (subst_pskl_in_pskl_fresh_eq P0 (pskl_var_f β) α HαP0) in Hren.
    rewrite <- (subst_pskl_in_pskl_intro α P (pskl_var_f β) HαP) in Hren.
    rewrite (subst_pskl_in_pskl_spec Q (pskl_var_f β) α) in Hren.
    pose proof (auc_delta_consis Hren
                  (rn_set_notin β HαΔ1) (rn_set_add_same β HαΔ2)) as Hren'.
    rewrite <- pskl_to_uskl_open_var.
    eapply IHn; [ | exact Hren' | solve_uniq ].
    rewrite size_pskl_open_pskl_wrt_pskl_var. simpl. lia.
  - (* UnivGhost *)
    apply a_consistag__univ_ghost.
    eapply IHn; [ | exact Hc | exact Hu ]; lia.
  - (* UnivGhost1 *)
    (* the rename hands back its own avoid-set (§8): union it into
       the cofinite bound this row was already computing *)
    destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α))
                _ _ _ _ _ _ _ Hc) as [Lrn Hrn].
    apply a_consistag__univ_ghost1 with
      (L := Lrn `union` singleton α `union` dom Θ0 `union` dom Θ1
            `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
            `union` ftvar_in_pskl Q `union` Δ1 `union` Δ2).
    intros β Hβ.
    assert (Hβα : β <> α) by (apply notin_singleton_1; clear - Hβ; fsetdec).
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfr; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - Hfr; fsetdec).
    assert (HαΔ1 : α `notin` Δ1) by (clear - Hfr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Hfr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec).
    assert (HuΘ : uniq ((α ~ abind_tvar) ++ Θ0)) by solve_uniq.
    assert (Hb1 : β `notin` dom ((α ~ abind_tvar) ++ Θ0))
      by (simpl; clear - Hβ; fsetdec).
    assert (Hb2 : β `notin` dom ((α ~ abind_tvar) ++ Θ1))
      by (simpl; clear - Hβ; fsetdec).
    assert (Hb3 : β `notin`
              ftvar_in_pskl (open_pskl_wrt_pskl P0 (pskl_var_f α)))
      by (apply notin_ftvar_open_pskl_var;
          [ exact Hβα | clear - Hβ; fsetdec ]).
    assert (Hb4 : β `notin` ftvar_in_pskl (pskl_univ_ghost P))
      by (simpl; clear - Hβ; fsetdec).
    assert (Hb5 : β `notin` ftvar_in_pskl Q) by (clear - Hβ; fsetdec).
    assert (Hb6 : β `notin` add α Δ1) by (clear - Hβ Hβα; fsetdec).
    assert (Hb7 : β `notin` Δ2) by (clear - Hβ; fsetdec).
    destruct (Hrn β ltac:(clear - Hβ; solve_notin_auto) nil Θ0 eq_refl
                tvar_prefix_nil HuΘ
                Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7) as [Θt [Heq Hren]].
    simpl in Heq. inversion Heq. subst Θt. clear Heq. simpl in Hren.
    rewrite <- (subst_pskl_in_pskl_intro α P0 (pskl_var_f β) HαP0) in Hren.
    rewrite (subst_pskl_in_pskl_fresh_eq P (pskl_var_f β) α HαP) in Hren.
    rewrite (subst_pskl_in_pskl_spec Q (pskl_var_f β) α) in Hren.
    pose proof (auc_delta_consis Hren
                  (rn_set_add_same β HαΔ1) (rn_set_notin β HαΔ2)) as Hren'.
    change (uskl_univ_ghost (pskl_to_uskl P))
      with (pskl_to_uskl (pskl_univ_ghost P)).
    eapply IHn; [ | exact Hren' | solve_uniq ].
    rewrite size_pskl_open_pskl_wrt_pskl_var. simpl. lia.
  - (* UnivGhost2 *)
    apply a_consistag__univ_ghost2; auto.
    eapply IHn; [ | exact Hc | exact Hu ]; lia.
  - (* Flex *)
    apply a_consistag__flex; auto. fsetdec.
  - (* FlexL *)
    eapply a_consistag__flex_l; eauto. fsetdec.
  - (* FlexR *)
    apply a_consistag__flex_r;
      try rewrite uskl_to_pskl_pskl_to_uskl; auto; try fsetdec.
  - (* GhostR *)
    replace P with (uskl_to_pskl (pskl_to_uskl P)) at 2
      by apply uskl_to_pskl_pskl_to_uskl.
    apply a_consistag__ghost_r;
      try rewrite uskl_to_pskl_pskl_to_uskl; auto; try fsetdec.
  - (* UnivGhostR *)
    apply a_consistag__univ_ghost_r; auto using pskl_to_uskl_guarded;
      try rewrite uskl_to_pskl_pskl_to_uskl; auto.
    eapply IHn; [ | exact Hc | exact Hu ]; lia.
Qed.

Lemma a_consis_decorate : forall Δ1 Δ2 Θ0 P0 P P' Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
  uniq Θ0 ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | empty ] (pskl_to_uskl P) ∼ P' ⊣ Θ1 }}da.
Proof.
  intros * Hc Hu.
  eapply a_consis_decorate_size; [ | exact Hc | exact Hu ].
  reflexivity.
Qed.
