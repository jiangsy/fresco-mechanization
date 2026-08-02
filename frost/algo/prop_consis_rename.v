(** Enablers for the completeness ∀-cases (design doc §7.3, L8/L9):

    - L8 [a_assign_unify_consis_tvar_prefix]: an all-rigid prefix of the
      input context survives VERBATIM into the output.  The algorithm only
      touches flexible entries; rigid binders are skipped and re-attached
      (SkipRigid / Flex-Flex-Skip'), and every deposit (Solve-M's [β̄ ++ Ξ])
      lands BELOW the walked prefix.  This is what shapes the recursive
      call's output as [(α ~ tvar) ++ Θ1], as [a_consis__forall_inh] et al
      demand.

    - [a_assign_unify_consis_compat]: the judgments only READ the
      used-name set [F] through freshness side conditions, so [F] may be
      replaced by any [F'] whose new names avoid the output's domain
      (Solve-M's guesses are the only names checked against [F], and they
      end up in the output).  [Δ1]/[Δ2] are only read through set
      predicates, so they transport along [=].  Needed to re-route the
      walked name [α ∈ F] to its rename [β] at the SkipRigid crossing,
      and to normalize the [rn_set] images at binder reassembly.

    - L9 [a_assign_unify_consis_rename_tvar]: renaming a rigid mid entry
      [α] to a fresh [β] across a whole algorithmic run.  The key
      observation making this tractable: under an ALL-RIGID prefix
      (which is the only shape the ∀-cases produce), every flex-headed
      rule is impossible above [α] — the walk can only skip rigid
      binders until it CROSSES [α], and below the crossing [α ∉ ftv]
      of everything in sight (SkipRigid's own side condition), so the
      sub-derivation is reused VERBATIM modulo the [F]-compat swap
      [add α F ↦ add β F]. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_decorate.

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
  (forall F Θ0 Ξ α P Θ1,
     Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 -> dom (Ξ ++ Θ0) [<=] dom Θ1) /\
  (forall F Θ0 α β Θ1,
     Θ0 ⊲[ F ] α ≈ᵘ β ⊣ Θ1 -> dom Θ0 [<=] dom Θ1) /\
  (forall F Δ1 Δ2 Θ0 P0 P P' Θ1,
     Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 -> dom Θ0 [<=] dom Θ1).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun F Θ0 Ξ α P Θ1 _ => dom (Ξ ++ Θ0) [<=] dom Θ1)
           (fun F Θ0 α β Θ1 _ => dom Θ0 [<=] dom Θ1)
           (fun F Δ1 Δ2 Θ0 P0 P P' Θ1 _ => dom Θ0 [<=] dom Θ1));
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
  (forall F Θi Ξ α P Θo,
     Θi ⊲[ F ][ Ξ ] α ≔ P ⊣ Θo ->
     forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
     exists Θt', Θo = Ξr ++ Θt') /\
  (forall F Θi α β Θo,
     Θi ⊲[ F ] α ≈ᵘ β ⊣ Θo ->
     forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
     exists Θt', Θo = Ξr ++ Θt') /\
  (forall F Δ1 Δ2 Θi P0 P P' Θo,
     Θi ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θo ->
     forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
     exists Θt', Θo = Ξr ++ Θt').
Proof.
  apply (a_assign_unify_consis_mutind
           (fun F Θi Ξ α P Θo _ =>
              forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
              exists Θt', Θo = Ξr ++ Θt')
           (fun F Θi α β Θo _ =>
              forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
              exists Θt', Θo = Ξr ++ Θt')
           (fun F Δ1 Δ2 Θi P0 P P' Θo _ =>
              forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
              exists Θt', Θo = Ξr ++ Θt')).
  - (* univ_ghost_id : flex head *)
    intros F Θ0 α Ξr Θt Heq Htv. tvp_dispatch.
  - (* solve_m : flex head *)
    intros F Θ0 Ξ α P βs τ Hnα Hg Hm Hu Hfr Ξr Θt Heq Htv. tvp_dispatch.
  - (* assign : defined-flex head *)
    intros F Θ0 Θ1 Ξ α β τ P P' Hf Hc IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* depend : flex head *)
    intros F Θ0 Θ1 Ξ α β P Hne Hin Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* skip : flex head *)
    intros F Θ0 Θ1 Ξ α β P Hne Hni Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* skip_rigid : tvar head — the real walk case *)
    intros F Θ0 Θ1 Ξ α β P Hni Ha IH Ξr Θt Heq Htv. tvp_dispatch.
    destruct (IH Ξr' Θt eq_refl (tvar_prefix_tail Htv)) as [Θt' ->].
    exists Θt'. reflexivity.
  - (* skip_tm_var : term head *)
    intros F Θ0 Θ1 Ξ α x P' P Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* skip_tm_skl : term head *)
    intros F Θ0 Θ1 Ξ α x P' P Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* flex_id : output = input *)
    intros F Θ0 α Hf Ξr Θt Heq Htv. exists Θt. assumption.
  - (* flex_l : flex head *)
    intros F Θ0 α β Hne Hf Ξr Θt Heq Htv. tvp_dispatch.
  - (* flex_r : flex head *)
    intros F Θ0 α β Hne Hf Ξr Θt Heq Htv. tvp_dispatch.
  - (* flex_assign : defined-flex head *)
    intros F Θ0 Θ1 α1 τ α β P' Hfα Hfβ Hc IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* flex_skip : flex head *)
    intros F Θ0 Θ1 α1 α β Hne1 Hne2 Hu IH Ξr Θt Heq Htv. tvp_dispatch.
  - (* skip_other : rigid/term head — the real walk case *)
    intros F Θ0 Θ1 c b α β Hb Hu IH Ξr Θt Heq Htv. tvp_dispatch.
    destruct (IH Ξr' Θt eq_refl (tvar_prefix_tail Htv)) as [Θt' ->].
    exists Θt'. reflexivity.
  - (* ghost : output = input *)
    intros F Δ1 Δ2 Θ0 P0 Hi Ξr Θt Heq Htv. exists Θt. assumption.
  - (* unit *)
    intros F Δ1 Δ2 Θ0 Ξr Θt Heq Htv. exists Θt. assumption.
  - (* rigid *)
    intros F Δ1 Δ2 Θ0 α Hb Ξr Θt Heq Htv. exists Θt. assumption.
  - (* arrow : thread the two components *)
    intros F Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2
      Ξr Θt Heq Htv.
    destruct (IH1 Ξr Θt Heq Htv) as [Θt1 ->].
    destruct (IH2 Ξr Θt1 eq_refl Htv) as [Θt2 ->].
    exists Θt2. reflexivity.
  - (* forall_inh : instantiate the cofinite premise once *)
    (* cluster 4: the premise is a single instance at the rule's own binder,
       so the [atom_fresh L] dance is gone — the IH applies directly *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Ξr Θt Heq Htv.
    destruct (IH ((α, abind_tvar) :: Ξr) Θt
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)) as [Θt' HeqO].
    simpl in HeqO. inversion HeqO. exists Θt'. congruence.
  - (* forall_syn *)
    (* cluster 4: the premise is a single instance at the rule's own binder,
       so the [atom_fresh L] dance is gone — the IH applies directly *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Ξr Θt Heq Htv.
    destruct (IH ((α, abind_tvar) :: Ξr) Θt
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)) as [Θt' HeqO].
    simpl in HeqO. inversion HeqO. exists Θt'. congruence.
  - (* univ_ghost *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hc IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  - (* univ_ghost1 *)
    (* cluster 4: the premise is a single instance at the rule's own binder,
       so the [atom_fresh L] dance is gone — the IH applies directly *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Ξr Θt Heq Htv.
    destruct (IH ((α, abind_tvar) :: Ξr) Θt
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)) as [Θt' HeqO].
    simpl in HeqO. inversion HeqO. exists Θt'. congruence.
  - (* univ_ghost2 *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  - (* flex *)
    intros F Δ1 Δ2 Θ0 Θ1 α β Hu IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  - (* flex_l *)
    intros F Δ1 Δ2 Θ0 Θ1 α P0 Hnf Ha IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  - (* flex_r *)
    intros F Δ1 Δ2 Θ0 Θ1 α P Hnf Ha IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  - (* ghost_r *)
    intros F Δ1 Δ2 Θ0 P Hi Ξr Θt Heq Htv. exists Θt. assumption.
  - (* univ_ghost_r *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
Qed.

(* ===================================================================== *)
(*  §3  Compatibility: F-change + Δ-transport along [=]                   *)
(* ===================================================================== *)

Definition auc_dom_mono_assign := proj1 a_assign_unify_consis_dom_mono.
Definition auc_dom_mono_unify  := proj1 (proj2 a_assign_unify_consis_dom_mono).
Definition auc_dom_mono_consis := proj2 (proj2 a_assign_unify_consis_dom_mono).

(** The used-name set [F] is only read through freshness side conditions
    (Solve-M's guesses), and every guessed name lands in the output's
    domain; so [F] may be swapped for any [F'] whose atoms are either old
    [F]-atoms, or names of the INPUT context, or avoid the output.
    [Δ1]/[Δ2] are only read through set predicates, so they transport
    along [=].

    The middle disjunct ([α1 ∈ dom of the input context]) is cluster 4's
    doing.  With cofinite ∀ rows the binder could be chosen outside [F'],
    so the two-disjunct condition transported into the premise; exists-fresh
    fixes the binder, and for [α1 = α] neither remaining disjunct holds —
    [α] IS in [dom ((α ~ tvar) ++ Θ1)].  Re-picking the binder would need
    §8's rename, which is proved USING this lemma, so the repair has to be
    in the statement.  It is sound at Solve-M for the same reason the
    original was: a guessed name lands in [dom Θ1] and avoids
    [dom (Ξ ++ Θ0)], so all three disjuncts refute [α1 ∈ F']. *)
Lemma a_assign_unify_consis_compat :
  (forall F Θ0 Ξ α P Θ1,
     Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
     forall F', (forall α1, α1 `in` F' -> α1 `in` F \/ α1 `in` dom (Ξ ++ Θ0) \/ α1 `notin` dom Θ1) ->
     Θ0 ⊲[ F' ][ Ξ ] α ≔ P ⊣ Θ1) /\
  (forall F Θ0 α β Θ1,
     Θ0 ⊲[ F ] α ≈ᵘ β ⊣ Θ1 ->
     forall F', (forall α1, α1 `in` F' -> α1 `in` F \/ α1 `in` dom Θ0 \/ α1 `notin` dom Θ1) ->
     Θ0 ⊲[ F' ] α ≈ᵘ β ⊣ Θ1) /\
  (forall F Δ1 Δ2 Θ0 P0 P P' Θ1,
     Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 ->
     forall F' Δ1' Δ2',
       (forall α1, α1 `in` F' -> α1 `in` F \/ α1 `in` dom Θ0 \/ α1 `notin` dom Θ1) ->
       Δ1 [=] Δ1' -> Δ2 [=] Δ2' ->
       Θ0 ⊢ₐ[ F' ][ Δ1' | Δ2' | P0 ] P ∼ P' ⊣ Θ1).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun F Θ0 Ξ α P Θ1 _ =>
              forall F', (forall α1, α1 `in` F' -> α1 `in` F \/ α1 `in` dom (Ξ ++ Θ0) \/ α1 `notin` dom Θ1) ->
              Θ0 ⊲[ F' ][ Ξ ] α ≔ P ⊣ Θ1)
           (fun F Θ0 α β Θ1 _ =>
              forall F', (forall α1, α1 `in` F' -> α1 `in` F \/ α1 `in` dom Θ0 \/ α1 `notin` dom Θ1) ->
              Θ0 ⊲[ F' ] α ≈ᵘ β ⊣ Θ1)
           (fun F Δ1 Δ2 Θ0 P0 P P' Θ1 _ =>
              forall F' Δ1' Δ2',
              (forall α1, α1 `in` F' -> α1 `in` F \/ α1 `in` dom Θ0 \/ α1 `notin` dom Θ1) ->
              Δ1 [=] Δ1' -> Δ2 [=] Δ2' ->
              Θ0 ⊢ₐ[ F' ][ Δ1' | Δ2' | P0 ] P ∼ P' ⊣ Θ1)).
  - (* univ_ghost_id *)
    intros F Θ0 α F' Hcond. apply a_assign__univ_ghost_id.
  - (* solve_m *)
    intros F Θ0 Ξ α P βs τ Hnα Hg Hm Hu Hfr F' Hcond.
    apply a_assign__solve_m; try assumption.
    intros α1 Hα1.
    pose proof (Hfr α1 Hα1) as Hfr'.
    assert (HγF' : α1 `notin` F').
    { intro HγF'. destruct (Hcond α1 HγF') as [HinF | [Hin0 | Hnd]];
        [ clear - Hfr' HinF; fsetdec | | ].
      - (* input-context disjunct: refuted by [Hfr']'s own avoid-set *)
        apply Hfr'.
        repeat (rewrite dom_app in Hin0 || simpl dom in Hin0).
        repeat (rewrite dom_app || simpl dom).
        clear - Hin0. fsetdec.
      - apply Hnd. repeat (rewrite dom_app || simpl dom).
        clear - Hα1. fsetdec. }
    clear - Hfr' HγF'. fsetdec.
  - (* assign *)
    intros F Θ0 Θ1 Ξ α β τ P P' Hfl Hc IH F' Hcond.
    eapply a_assign__assign; [ exact Hfl | ].
    apply (IH (add β F') empty empty); [ | reflexivity | reflexivity ].
    intros α1 Hα1. apply add_iff in Hα1.
    destruct Hα1 as [-> | HγF'].
    + left. clear; fsetdec.
    + destruct (Hcond α1 HγF') as [HinF | [Hin0 | Hnd]].
      * left; clear - HinF; fsetdec.
      * (* the input-context disjunct may still name the WALKED head, and
           then it is the [add h F] disjunct that applies *)
        repeat (rewrite dom_app in Hin0 || simpl dom in Hin0).
        match goal with
        | |- α1 `in` add ?h _ \/ _ =>
            destruct (α1 == h) as [-> | Hne']
        end;
          [ left; clear; fsetdec | right; left ].
        repeat (rewrite dom_app). clear - Hin0 Hne'. fsetdec.
      * right; right. simpl dom in Hnd. clear - Hnd. fsetdec.
  - (* depend *)
    intros F Θ0 Θ1 Ξ α β P Hne Hin Ha IH F' Hcond.
    apply a_assign__depend; try assumption.
    (* [Ξ] grows at its tail, so the input-context disjunct only needs
       re-associating *)
    apply IH. intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinF | [Hin0 | Hnd]];
      [ left; exact HinF | right; left | right; right; exact Hnd ].
    repeat (rewrite dom_app in Hin0 || simpl dom in Hin0).
    repeat (rewrite dom_app || simpl dom). clear - Hin0. fsetdec.
  - (* skip *)
    intros F Θ0 Θ1 Ξ α β P Hne Hni Ha IH F' Hcond.
    apply a_assign__skip; try assumption.
    apply IH.
    intros α1 Hα1. apply add_iff in Hα1.
    destruct Hα1 as [-> | HγF'].
    + left. clear; fsetdec.
    + destruct (Hcond α1 HγF') as [HinF | [Hin0 | Hnd]].
      * left; clear - HinF; fsetdec.
      * (* the input-context disjunct may still name the WALKED head, and
           then it is the [add h F] disjunct that applies *)
        repeat (rewrite dom_app in Hin0 || simpl dom in Hin0).
        match goal with
        | |- α1 `in` add ?h _ \/ _ =>
            destruct (α1 == h) as [-> | Hne']
        end;
          [ left; clear; fsetdec | right; left ].
        repeat (rewrite dom_app). clear - Hin0 Hne'. fsetdec.
      * right; right. simpl dom in Hnd. clear - Hnd. fsetdec.
  - (* skip_rigid *)
    intros F Θ0 Θ1 Ξ α β P Hni Ha IH F' Hcond.
    apply a_assign__skip_rigid; try assumption.
    apply IH.
    intros α1 Hα1. apply add_iff in Hα1.
    destruct Hα1 as [-> | HγF'].
    + left. clear; fsetdec.
    + destruct (Hcond α1 HγF') as [HinF | [Hin0 | Hnd]].
      * left; clear - HinF; fsetdec.
      * (* the input-context disjunct may still name the WALKED head, and
           then it is the [add h F] disjunct that applies *)
        repeat (rewrite dom_app in Hin0 || simpl dom in Hin0).
        match goal with
        | |- α1 `in` add ?h _ \/ _ =>
            destruct (α1 == h) as [-> | Hne']
        end;
          [ left; clear; fsetdec | right; left ].
        repeat (rewrite dom_app). clear - Hin0 Hne'. fsetdec.
      * right; right. simpl dom in Hnd. clear - Hnd. fsetdec.
  - (* skip_tm_var *)
    intros F Θ0 Θ1 Ξ α x P' P Ha IH F' Hcond.
    apply a_assign__skip_tm_var.
    apply IH.
    intros α1 Hα1. apply add_iff in Hα1.
    destruct Hα1 as [-> | HγF'].
    + left. clear; fsetdec.
    + destruct (Hcond α1 HγF') as [HinF | [Hin0 | Hnd]].
      * left; clear - HinF; fsetdec.
      * (* the input-context disjunct may still name the WALKED head, and
           then it is the [add h F] disjunct that applies *)
        repeat (rewrite dom_app in Hin0 || simpl dom in Hin0).
        match goal with
        | |- α1 `in` add ?h _ \/ _ =>
            destruct (α1 == h) as [-> | Hne']
        end;
          [ left; clear; fsetdec | right; left ].
        repeat (rewrite dom_app). clear - Hin0 Hne'. fsetdec.
      * right; right. simpl dom in Hnd. clear - Hnd. fsetdec.
  - (* skip_tm_skl *)
    intros F Θ0 Θ1 Ξ α x P' P Ha IH F' Hcond.
    apply a_assign__skip_tm_skl.
    apply IH.
    intros α1 Hα1. apply add_iff in Hα1.
    destruct Hα1 as [-> | HγF'].
    + left. clear; fsetdec.
    + destruct (Hcond α1 HγF') as [HinF | [Hin0 | Hnd]].
      * left; clear - HinF; fsetdec.
      * (* the input-context disjunct may still name the WALKED head, and
           then it is the [add h F] disjunct that applies *)
        repeat (rewrite dom_app in Hin0 || simpl dom in Hin0).
        match goal with
        | |- α1 `in` add ?h _ \/ _ =>
            destruct (α1 == h) as [-> | Hne']
        end;
          [ left; clear; fsetdec | right; left ].
        repeat (rewrite dom_app). clear - Hin0 Hne'. fsetdec.
      * right; right. simpl dom in Hnd. clear - Hnd. fsetdec.
  - (* flex_id *)
    intros F Θ0 α Hf F' Hcond. apply a_unify__flex_id; assumption.
  - (* flex_l *)
    intros F Θ0 α β Hne Hf F' Hcond. apply a_unify__flex_l; assumption.
  - (* flex_r *)
    intros F Θ0 α β Hne Hf F' Hcond. apply a_unify__flex_r; assumption.
  - (* flex_assign *)
    intros F Θ0 Θ1 α1 τ α β P' Hfα Hfβ Hc IH F' Hcond.
    eapply a_unify__flex_assign; try eassumption.
    apply (IH (add α1 F') empty empty); [ | reflexivity | reflexivity ].
    intros β1 Hβ1. apply add_iff in Hβ1.
    destruct Hβ1 as [-> | HδF'].
    + left. clear; fsetdec.
    + destruct (Hcond β1 HδF') as [HinF | [Hin0 | Hnd]].
      * left; clear - HinF; fsetdec.
      * repeat (rewrite dom_app in Hin0 || simpl dom in Hin0).
        match goal with
        | |- β1 `in` add ?h _ \/ _ => destruct (β1 == h) as [-> | Hne']
        end;
          [ left; clear; fsetdec | right; left ].
        repeat (rewrite dom_app). clear - Hin0 Hne'. fsetdec.
      * right; right. simpl dom in Hnd. clear - Hnd. fsetdec.
  - (* flex_skip *)
    intros F Θ0 Θ1 α1 α β Hne1 Hne2 Hu IH F' Hcond.
    apply a_unify__flex_skip; try assumption.
    apply IH.
    intros β1 Hβ1. apply add_iff in Hβ1.
    destruct Hβ1 as [-> | HδF'].
    + left. clear; fsetdec.
    + destruct (Hcond β1 HδF') as [HinF | [Hin0 | Hnd]].
      * left; clear - HinF; fsetdec.
      * repeat (rewrite dom_app in Hin0 || simpl dom in Hin0).
        match goal with
        | |- β1 `in` add ?h _ \/ _ => destruct (β1 == h) as [-> | Hne']
        end;
          [ left; clear; fsetdec | right; left ].
        repeat (rewrite dom_app). clear - Hin0 Hne'. fsetdec.
      * right; right. simpl dom in Hnd. clear - Hnd. fsetdec.
  - (* skip_other *)
    intros F Θ0 Θ1 c b α β Hb Hu IH F' Hcond.
    apply a_unify__skip_other; try assumption.
    apply IH.
    intros β1 Hβ1. apply add_iff in Hβ1.
    destruct Hβ1 as [-> | HδF'].
    + left. clear; fsetdec.
    + destruct (Hcond β1 HδF') as [HinF | [Hin0 | Hnd]].
      * left; clear - HinF; fsetdec.
      * repeat (rewrite dom_app in Hin0 || simpl dom in Hin0).
        match goal with
        | |- β1 `in` add ?h _ \/ _ => destruct (β1 == h) as [-> | Hne']
        end;
          [ left; clear; fsetdec | right; left ].
        repeat (rewrite dom_app). clear - Hin0 Hne'. fsetdec.
      * right; right. simpl dom in Hnd. clear - Hnd. fsetdec.
  - (* ghost *)
    intros F Δ1 Δ2 Θ0 P0 Hi F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__ghost. clear - Hi HΔ2. fsetdec.
  - (* unit *)
    intros F Δ1 Δ2 Θ0 F' Δ1' Δ2' Hcond HΔ1 HΔ2. apply a_consis__unit.
  - (* rigid *)
    intros F Δ1 Δ2 Θ0 α Hb F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__rigid; assumption.
  - (* arrow *)
    intros F Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2
      F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    pose proof (auc_dom_mono_consis Hc2) as Hd2.
    pose proof (auc_dom_mono_consis Hc1) as Hd1.
    eapply a_consis__arrow.
    + apply IH1; [ | exact HΔ1 | exact HΔ2 ].
      intros α1 Hα1. destruct (Hcond α1 Hα1) as [HinF | [Hin0 | Hnd]];
        [ left; exact HinF | right; left; exact Hin0
        | right; right; clear - Hnd Hd2; fsetdec ].
    + apply IH2; [ | exact HΔ1 | exact HΔ2 ].
      intros α1 Hα1. destruct (Hcond α1 Hα1) as [HinF | [Hin0 | Hnd]];
        [ left; exact HinF | right; left; clear - Hin0 Hd1; fsetdec
        | right; right; exact Hnd ].
  - (* forall_inh *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__forall_inh with (α := α).
    + clear - Hfr HΔ1 HΔ2. fsetdec.
    + apply IH.
      * (* relay the three-disjunct condition under the rule's own binder;
           for [α1 = α] it is the INPUT-CONTEXT disjunct that applies, which
           is exactly why cluster 4 had to widen this lemma *)
        intros α1 Hα1. destruct (Hcond α1 Hα1) as [HinF | [Hin0 | Hnd]].
        -- left; exact HinF.
        -- right; left. simpl dom. clear - Hin0. fsetdec.
        -- destruct (α1 == α) as [-> | Hne'];
             [ right; left; simpl dom; clear; fsetdec | right; right ].
           simpl dom. clear - Hnd Hne'. fsetdec.
      * clear - HΔ1. fsetdec.
      * clear - HΔ2. fsetdec.
  - (* forall_syn *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__forall_syn with (α := α).
    + clear - Hfr HΔ1 HΔ2. fsetdec.
    + apply IH.
      * (* relay the three-disjunct condition under the rule's own binder;
           for [α1 = α] it is the INPUT-CONTEXT disjunct that applies, which
           is exactly why cluster 4 had to widen this lemma *)
        intros α1 Hα1. destruct (Hcond α1 Hα1) as [HinF | [Hin0 | Hnd]].
        -- left; exact HinF.
        -- right; left. simpl dom. clear - Hin0. fsetdec.
        -- destruct (α1 == α) as [-> | Hne'];
             [ right; left; simpl dom; clear; fsetdec | right; right ].
           simpl dom. clear - Hnd Hne'. fsetdec.
      * clear - HΔ1. fsetdec.
      * clear - HΔ2. fsetdec.
  - (* univ_ghost *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hc IH F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__univ_ghost. apply IH; assumption.
  - (* univ_ghost1 *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__univ_ghost1 with (α := α).
    + clear - Hfr HΔ1 HΔ2. fsetdec.
    + apply IH.
      * (* relay the three-disjunct condition under the rule's own binder;
           for [α1 = α] it is the INPUT-CONTEXT disjunct that applies, which
           is exactly why cluster 4 had to widen this lemma *)
        intros α1 Hα1. destruct (Hcond α1 Hα1) as [HinF | [Hin0 | Hnd]].
        -- left; exact HinF.
        -- right; left. simpl dom. clear - Hin0. fsetdec.
        -- destruct (α1 == α) as [-> | Hne'];
             [ right; left; simpl dom; clear; fsetdec | right; right ].
           simpl dom. clear - Hnd Hne'. fsetdec.
      * clear - HΔ1. fsetdec.
      * clear - HΔ2. fsetdec.
  - (* univ_ghost2 *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__univ_ghost2; try assumption.
    apply IH; assumption.
  - (* flex *)
    intros F Δ1 Δ2 Θ0 Θ1 α β Hu IH F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__flex. apply IH; assumption.
  - (* flex_l *)
    intros F Δ1 Δ2 Θ0 Θ1 α P0 Hnf Ha IH F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__flex_l; try assumption.
    apply IH; assumption.
  - (* flex_r *)
    intros F Δ1 Δ2 Θ0 Θ1 α P Hnf Ha IH F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__flex_r; try assumption.
    apply IH; assumption.
  - (* ghost_r *)
    intros F Δ1 Δ2 Θ0 P Hi F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__ghost_r. clear - Hi HΔ1. fsetdec.
  - (* univ_ghost_r *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH F' Δ1' Δ2' Hcond HΔ1 HΔ2.
    apply a_consis__univ_ghost_r; try assumption.
    apply IH; assumption.
Qed.

(* ===================================================================== *)
(*  §4  Subjects are flexible variables of the input                      *)
(* ===================================================================== *)

Lemma a_flex_tvar_weaken_app : forall Ξ Θ α,
  a_flex_tvar Θ α -> a_flex_tvar (Ξ ++ Θ) α.
Proof.
  intros * [Hb | [τ Hb]]; [ left | right; exists τ ];
    unfold binds in *; apply in_or_app; right; assumption.
Qed.

Lemma a_flex_tvar_insert_mid : forall Ξ mid Θ α,
  a_flex_tvar (Ξ ++ Θ) α -> a_flex_tvar (Ξ ++ mid ++ Θ) α.
Proof.
  intros * H.
  destruct H as [Hb | [τ Hb]].
  - left. unfold binds in *. apply in_app_or in Hb. apply in_or_app.
    destruct Hb as [Hb | Hb];
      [ left; assumption | right; apply in_or_app; right; assumption ].
  - right. exists τ. unfold binds in *.
    apply in_app_or in Hb. apply in_or_app.
    destruct Hb as [Hb | Hb];
      [ left; assumption | right; apply in_or_app; right; assumption ].
Qed.

(** An assignment's subject is a flexible variable of its merged input
    [Ξ ++ Θ0]; a unification's two subjects are flexible variables of its
    input.  (Rules whose own shape does not show it thread it from their
    premise.) *)
Lemma a_assign_unify_subject_flex :
  (forall F Θ0 Ξ α P Θ1,
     Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 -> a_flex_tvar (Ξ ++ Θ0) α) /\
  (forall F Θ0 α β Θ1,
     Θ0 ⊲[ F ] α ≈ᵘ β ⊣ Θ1 -> a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β) /\
  (forall F Δ1 Δ2 Θ0 P0 P P' Θ1,
     Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 -> True).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun F Θ0 Ξ α P Θ1 _ => a_flex_tvar (Ξ ++ Θ0) α)
           (fun F Θ0 α β Θ1 _ => a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β)
           (fun F Δ1 Δ2 Θ0 P0 P P' Θ1 _ => True));
    try solve [ intros; exact I ].
  - (* univ_ghost_id *)
    intros F Θ0 α. simpl. left. left. reflexivity.
  - (* solve_m *)
    intros F Θ0 Ξ α P βs τ Hnα Hg Hm Hu Hfr.
    left. unfold binds. apply in_or_app. right. left. reflexivity.
  - (* assign *)
    intros F Θ0 Θ1 Ξ α β τ P P' Hfl Hc _.
    apply a_flex_tvar_weaken_app. exact Hfl.
  - (* depend *)
    intros F Θ0 Θ1 Ξ α β P Hne Hin Ha IH.
    simpl_env in IH. exact IH.
  - (* skip *)
    intros F Θ0 Θ1 Ξ α β P Hne Hni Ha IH.
    apply (a_flex_tvar_insert_mid Ξ (β ~ abind_flex_mono) Θ0). exact IH.
  - (* skip_rigid *)
    intros F Θ0 Θ1 Ξ α β P Hni Ha IH.
    apply (a_flex_tvar_insert_mid Ξ (β ~ abind_tvar) Θ0). exact IH.
  - (* skip_tm_var *)
    intros F Θ0 Θ1 Ξ α x P' P Ha IH.
    apply (a_flex_tvar_insert_mid Ξ (x ~ abind_var_typ P') Θ0). exact IH.
  - (* skip_tm_skl *)
    intros F Θ0 Θ1 Ξ α x P' P Ha IH.
    apply (a_flex_tvar_insert_mid Ξ (x ~ abind_var_skl P') Θ0). exact IH.
  - (* flex_id *)
    intros F Θ0 α Hf. split; assumption.
  - (* flex_l *)
    intros F Θ0 α β Hne Hf. split.
    + left. left. reflexivity.
    + apply (a_flex_tvar_weaken_app (α ~ abind_flex_mono)). exact Hf.
  - (* flex_r *)
    intros F Θ0 α β Hne Hf. split.
    + apply (a_flex_tvar_weaken_app (β ~ abind_flex_mono)). exact Hf.
    + left. left. reflexivity.
  - (* flex_assign *)
    intros F Θ0 Θ1 α1 τ α β P' Hfα Hfβ Hc _. split; assumption.
  - (* flex_skip *)
    intros F Θ0 Θ1 α1 α β Hne1 Hne2 Hu [IHα IHβ]. split;
      apply (a_flex_tvar_weaken_app (α1 ~ abind_flex_mono)); assumption.
  - (* skip_other *)
    intros F Θ0 Θ1 c b α β Hb Hu [IHα IHβ]. split;
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

(** Names checked against [F] (Solve-M's guesses) are exactly the names
    the run ADDS to the context, so: the output is uniq whenever the
    merged input is, and every [F]-name of the output's domain was
    already in the input's. *)
Lemma a_assign_unify_consis_uniq_fprotect :
  (forall F Θ0 Ξ α P Θ1,
     Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
     uniq (Ξ ++ Θ0) ->
     uniq Θ1 /\
     (forall α1, α1 `in` F -> α1 `in` dom Θ1 -> α1 `in` dom (Ξ ++ Θ0))) /\
  (forall F Θ0 α β Θ1,
     Θ0 ⊲[ F ] α ≈ᵘ β ⊣ Θ1 ->
     uniq Θ0 ->
     uniq Θ1 /\
     (forall α1, α1 `in` F -> α1 `in` dom Θ1 -> α1 `in` dom Θ0)) /\
  (forall F Δ1 Δ2 Θ0 P0 P P' Θ1,
     Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 ->
     uniq Θ0 ->
     uniq Θ1 /\
     (forall α1, α1 `in` F -> α1 `in` dom Θ1 -> α1 `in` dom Θ0)).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun F Θ0 Ξ α P Θ1 _ =>
              uniq (Ξ ++ Θ0) ->
              uniq Θ1 /\
              (forall α1, α1 `in` F -> α1 `in` dom Θ1 ->
                 α1 `in` dom (Ξ ++ Θ0)))
           (fun F Θ0 α β Θ1 _ =>
              uniq Θ0 ->
              uniq Θ1 /\
              (forall α1, α1 `in` F -> α1 `in` dom Θ1 -> α1 `in` dom Θ0))
           (fun F Δ1 Δ2 Θ0 P0 P P' Θ1 _ =>
              uniq Θ0 ->
              uniq Θ1 /\
              (forall α1, α1 `in` F -> α1 `in` dom Θ1 -> α1 `in` dom Θ0))).
  - (* univ_ghost_id *)
    intros F Θ0 α Hu. simpl_env in Hu. split; [ exact Hu | ].
    intros α1 _ Hα1. simpl_env in *. fsetdec.
  - (* solve_m *)
    intros F Θ0 Ξ α P βs τ Hnα Hg Hm Huβ Hfr Hu.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by solve_uniq.
    assert (HαΞΘ : α `notin` dom (Ξ ++ Θ0)) by solve_uniq.
    assert (Hdβ : disjoint βs (Ξ ++ Θ0)).
    { apply disjoint_from_pointwise. intros α1 Hα1.
      pose proof (Hfr α1 Hα1) as Hf. rewrite dom_app in *.
      clear - Hf. fsetdec. }
    assert (Hαβ : α `notin` dom βs).
    { intro Hαβ. pose proof (Hfr α Hαβ) as Hf. clear - Hf. fsetdec. }
    split.
    + assert (Huβt : uniq (βs ++ Ξ ++ Θ0))
        by (apply uniq_app_4; assumption).
      apply uniq_push; [ exact Huβt | ].
      rewrite dom_app. clear - HαΞΘ Hαβ. fsetdec.
    + intros α1 HγF Hγd.
      simpl dom in Hγd. repeat rewrite dom_app in *.
      assert (Hα1β : α1 `notin` dom βs)
        by (intro Hα1β; pose proof (Hfr α1 Hα1β) as Hf; clear - Hf HγF;
            fsetdec).
      simpl dom in *. clear - Hγd Hα1β. fsetdec.
  - (* assign *)
    intros F Θ0 Θ1 Ξ α β τ P P' Hfl Hc IH Hu.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by solve_uniq.
    assert (Hβni : β `notin` dom (Ξ ++ Θ0)) by solve_uniq.
    destruct (IH HuΞΘ) as [Hu1 Hprot].
    split.
    + apply uniq_push; [ exact Hu1 | ].
      intro Hβ1. pose proof (Hprot β ltac:(clear; fsetdec) Hβ1) as Hin.
      clear - Hin Hβni. fsetdec.
    + intros α1 HγF Hγd. simpl dom in Hγd.
      rewrite dom_app. simpl dom.
      assert (Hd : α1 `in` dom Θ1 -> α1 `in` dom (Ξ ++ Θ0)).
      { intro Hg1. apply Hprot; [ clear - HγF; fsetdec | exact Hg1 ]. }
      rewrite dom_app in Hd. clear - Hγd Hd.
      apply add_iff in Hγd.
      destruct Hγd as [-> | Hγd]; [ fsetdec | ].
      pose proof (Hd Hγd). fsetdec.
  - (* depend *)
    intros F Θ0 Θ1 Ξ α β P Hne Hin Ha IH Hu.
    assert (Hu' : uniq ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0))
      by (simpl_env; solve_uniq).
    destruct (IH Hu') as [Hu1 Hprot].
    split; [ exact Hu1 | ].
    intros α1 HγF Hγd.
    pose proof (Hprot α1 HγF Hγd) as Hin'.
    repeat rewrite dom_app in *. simpl dom in *.
    clear - Hin'. fsetdec.
  - (* skip *)
    intros F Θ0 Θ1 Ξ α β P Hne Hni Ha IH Hu.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by solve_uniq.
    assert (Hβni : β `notin` dom (Ξ ++ Θ0)) by solve_uniq.
    destruct (IH HuΞΘ) as [Hu1 Hprot].
    split.
    + apply uniq_push; [ exact Hu1 | ].
      intro Hβ1. pose proof (Hprot β ltac:(clear; fsetdec) Hβ1) as Hin.
      clear - Hin Hβni. fsetdec.
    + intros α1 HγF Hγd. simpl dom in Hγd.
      repeat rewrite dom_app in *. simpl dom in *.
      apply add_iff in Hγd.
      destruct Hγd as [-> | Hγd]; [ fsetdec | ].
      pose proof (Hprot α1 ltac:(clear - HγF; fsetdec) Hγd) as Hin'.
      rewrite dom_app in Hin'. clear - Hin'. fsetdec.
  - (* skip_rigid *)
    intros F Θ0 Θ1 Ξ α β P Hni Ha IH Hu.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by solve_uniq.
    assert (Hβni : β `notin` dom (Ξ ++ Θ0)) by solve_uniq.
    destruct (IH HuΞΘ) as [Hu1 Hprot].
    split.
    + apply uniq_push; [ exact Hu1 | ].
      intro Hβ1. pose proof (Hprot β ltac:(clear; fsetdec) Hβ1) as Hin.
      clear - Hin Hβni. fsetdec.
    + intros α1 HγF Hγd. simpl dom in Hγd.
      repeat rewrite dom_app in *. simpl dom in *.
      apply add_iff in Hγd.
      destruct Hγd as [-> | Hγd]; [ fsetdec | ].
      pose proof (Hprot α1 ltac:(clear - HγF; fsetdec) Hγd) as Hin'.
      rewrite dom_app in Hin'. clear - Hin'. fsetdec.
  - (* skip_tm_var *)
    intros F Θ0 Θ1 Ξ α x P' P Ha IH Hu.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by solve_uniq.
    assert (Hxni : x `notin` dom (Ξ ++ Θ0)) by solve_uniq.
    destruct (IH HuΞΘ) as [Hu1 Hprot].
    split.
    + apply uniq_push; [ exact Hu1 | ].
      intro Hx1. pose proof (Hprot x ltac:(clear; fsetdec) Hx1) as Hin.
      clear - Hin Hxni. fsetdec.
    + intros α1 HγF Hγd. simpl dom in Hγd.
      repeat rewrite dom_app in *. simpl dom in *.
      apply add_iff in Hγd.
      destruct Hγd as [-> | Hγd]; [ fsetdec | ].
      pose proof (Hprot α1 ltac:(clear - HγF; fsetdec) Hγd) as Hin'.
      rewrite dom_app in Hin'. clear - Hin'. fsetdec.
  - (* skip_tm_skl *)
    intros F Θ0 Θ1 Ξ α x P' P Ha IH Hu.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by solve_uniq.
    assert (Hxni : x `notin` dom (Ξ ++ Θ0)) by solve_uniq.
    destruct (IH HuΞΘ) as [Hu1 Hprot].
    split.
    + apply uniq_push; [ exact Hu1 | ].
      intro Hx1. pose proof (Hprot x ltac:(clear; fsetdec) Hx1) as Hin.
      clear - Hin Hxni. fsetdec.
    + intros α1 HγF Hγd. simpl dom in Hγd.
      repeat rewrite dom_app in *. simpl dom in *.
      apply add_iff in Hγd.
      destruct Hγd as [-> | Hγd]; [ fsetdec | ].
      pose proof (Hprot α1 ltac:(clear - HγF; fsetdec) Hγd) as Hin'.
      rewrite dom_app in Hin'. clear - Hin'. fsetdec.
  - (* flex_id *)
    intros F Θ0 α Hf Hu. split; [ exact Hu | ]. intros; assumption.
  - (* flex_l *)
    intros F Θ0 α β Hne Hf Hu.
    split; [ solve_uniq | ].
    intros α1 _ Hα1. simpl dom in *. exact Hα1.
  - (* flex_r *)
    intros F Θ0 α β Hne Hf Hu.
    split; [ solve_uniq | ].
    intros α1 _ Hα1. simpl dom in *. exact Hα1.
  - (* flex_assign *)
    intros F Θ0 Θ1 α10 τ α β P' Hfα Hfβ Hc IH Hu.
    assert (HuΘ : uniq Θ0) by solve_uniq.
    assert (Hγni : α10 `notin` dom Θ0) by solve_uniq.
    destruct (IH HuΘ) as [Hu1 Hprot].
    split.
    + apply uniq_push; [ exact Hu1 | ].
      intro Hγ1. pose proof (Hprot α10 ltac:(clear; fsetdec) Hγ1) as Hin.
      clear - Hin Hγni. fsetdec.
    + intros α1 HγF Hγd. simpl dom in *.
      apply add_iff in Hγd.
      destruct Hγd as [-> | Hγd]; [ fsetdec | ].
      pose proof (Hprot α1 ltac:(clear - HγF; fsetdec) Hγd) as Hin'.
      clear - Hin'. fsetdec.
  - (* flex_skip *)
    intros F Θ0 Θ1 α10 α β Hne1 Hne2 Hun IH Hu.
    assert (HuΘ : uniq Θ0) by solve_uniq.
    assert (Hγni : α10 `notin` dom Θ0) by solve_uniq.
    destruct (IH HuΘ) as [Hu1 Hprot].
    split.
    + apply uniq_push; [ exact Hu1 | ].
      intro Hγ1. pose proof (Hprot α10 ltac:(clear; fsetdec) Hγ1) as Hin.
      clear - Hin Hγni. fsetdec.
    + intros α1 HγF Hγd. simpl dom in *.
      apply add_iff in Hγd.
      destruct Hγd as [-> | Hγd]; [ fsetdec | ].
      pose proof (Hprot α1 ltac:(clear - HγF; fsetdec) Hγd) as Hin'.
      clear - Hin'. fsetdec.
  - (* skip_other *)
    intros F Θ0 Θ1 c b α β Hb Hun IH Hu.
    assert (HuΘ : uniq Θ0) by solve_uniq.
    assert (Hcni : c `notin` dom Θ0) by solve_uniq.
    destruct (IH HuΘ) as [Hu1 Hprot].
    split.
    + apply uniq_push; [ exact Hu1 | ].
      intro Hc1. pose proof (Hprot c ltac:(clear; fsetdec) Hc1) as Hin.
      clear - Hin Hcni. fsetdec.
    + intros α1 HγF Hγd. simpl dom in *.
      apply add_iff in Hγd.
      destruct Hγd as [-> | Hγd]; [ fsetdec | ].
      pose proof (Hprot α1 ltac:(clear - HγF; fsetdec) Hγd) as Hin'.
      clear - Hin'. fsetdec.
  - (* ghost *)
    intros F Δ1 Δ2 Θ0 P0 Hi Hu. split; [ exact Hu | ]. intros; assumption.
  - (* unit *)
    intros F Δ1 Δ2 Θ0 Hu. split; [ exact Hu | ]. intros; assumption.
  - (* rigid *)
    intros F Δ1 Δ2 Θ0 α Hb Hu. split; [ exact Hu | ]. intros; assumption.
  - (* arrow *)
    intros F Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2 Hu.
    destruct (IH1 Hu) as [Hu1 Hprot1].
    destruct (IH2 Hu1) as [Hu2 Hprot2].
    split; [ exact Hu2 | ].
    intros α1 HγF Hγd. exact (Hprot1 α1 HγF (Hprot2 α1 HγF Hγd)).
  - (* forall_inh *)
    (* cluster 4: the binder is the RULE's, so it is no longer chosen away
       from [F].  For [α1 = α] the refutation comes from [Hu1] instead —
       the premise's own output context is uniq, so [α ∉ dom Θ1]. *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Hu.
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec).
    destruct (IH ltac:(apply uniq_push; [ exact Hu | exact HαΘ0 ]))
      as [Hu1 Hprot].
    assert (Hna : α `notin` dom Θ1) by (inversion Hu1; assumption).
    split.
    + inversion Hu1; assumption.
    + intros α1 HγF Hγd.
      assert (HneX : α1 <> α) by (clear - Hγd Hna; fsetdec).
      assert (Hγd' : α1 `in` dom ((α ~ abind_tvar) ++ Θ1))
        by (simpl dom; clear - Hγd; fsetdec).
      pose proof (Hprot α1 HγF Hγd') as Hin'.
      simpl dom in Hin'.
      clear - Hin' HneX. fsetdec.
  - (* forall_syn *)
    (* cluster 4: the binder is the RULE's, so it is no longer chosen away
       from [F].  For [α1 = α] the refutation comes from [Hu1] instead —
       the premise's own output context is uniq, so [α ∉ dom Θ1]. *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Hu.
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec).
    destruct (IH ltac:(apply uniq_push; [ exact Hu | exact HαΘ0 ]))
      as [Hu1 Hprot].
    assert (Hna : α `notin` dom Θ1) by (inversion Hu1; assumption).
    split.
    + inversion Hu1; assumption.
    + intros α1 HγF Hγd.
      assert (HneX : α1 <> α) by (clear - Hγd Hna; fsetdec).
      assert (Hγd' : α1 `in` dom ((α ~ abind_tvar) ++ Θ1))
        by (simpl dom; clear - Hγd; fsetdec).
      pose proof (Hprot α1 HγF Hγd') as Hin'.
      simpl dom in Hin'.
      clear - Hin' HneX. fsetdec.
  - (* univ_ghost *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hc IH Hu. exact (IH Hu).
  - (* univ_ghost1 *)
    (* cluster 4: the binder is the RULE's, so it is no longer chosen away
       from [F].  For [α1 = α] the refutation comes from [Hu1] instead —
       the premise's own output context is uniq, so [α ∉ dom Θ1]. *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Hu.
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec).
    destruct (IH ltac:(apply uniq_push; [ exact Hu | exact HαΘ0 ]))
      as [Hu1 Hprot].
    assert (Hna : α `notin` dom Θ1) by (inversion Hu1; assumption).
    split.
    + inversion Hu1; assumption.
    + intros α1 HγF Hγd.
      assert (HneX : α1 <> α) by (clear - Hγd Hna; fsetdec).
      assert (Hγd' : α1 `in` dom ((α ~ abind_tvar) ++ Θ1))
        by (simpl dom; clear - Hγd; fsetdec).
      pose proof (Hprot α1 HγF Hγd') as Hin'.
      simpl dom in Hin'.
      clear - Hin' HneX. fsetdec.
  - (* univ_ghost2 *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH Hu. exact (IH Hu).
  - (* flex *)
    intros F Δ1 Δ2 Θ0 Θ1 α β Hun IH Hu. exact (IH Hu).
  - (* flex_l *)
    intros F Δ1 Δ2 Θ0 Θ1 α P0 Hnf Ha IH Hu.
    apply IH. simpl_env. exact Hu.
  - (* flex_r *)
    intros F Δ1 Δ2 Θ0 Θ1 α P Hnf Ha IH Hu.
    apply IH. simpl_env. exact Hu.
  - (* ghost_r *)
    intros F Δ1 Δ2 Θ0 P Hi Hu. split; [ exact Hu | ]. intros; assumption.
  - (* univ_ghost_r *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH Hu. exact (IH Hu).
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

(** The [Ghost]/[GhostR] side condition transports through the rename:
    if [Δ] avoids [ftv P] then the renamed [Δ] avoids the renamed [ftv]. *)
(** [ftvar_in_pskl_open_pskl_wrt_pskl_upper] is stated as a [<=]; the
    [rewrite]s above need it as a set-level bound, so use it by [pose]. *)
Lemma notin_ftvar_open_pskl_var : forall β α P,
  β <> α -> β `notin` ftvar_in_pskl P ->
  β `notin` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof.
  intros β α P Hne HβP.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hs.
  simpl in Hs. clear - Hs Hne HβP. fsetdec.
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

Lemma app_mid_inv : forall (Ξ : aenv) (a : atom) (b : abind) (A B : aenv),
  Ξ ++ (a ~ b) ++ A = Ξ ++ (a ~ b) ++ B -> A = B.
Proof.
  intros * H. apply app_inv_head in H. apply app_inv_head in H. exact H.
Qed.

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

(** Guardedness survives variable-for-variable substitution
    (local copy of prop_consis_sound's [guarded_pskl_subst_var], kept
    here to avoid importing the soundness file). *)
Lemma guarded_pskl_subst_var' : forall β α P,
  guarded_pskl P ->
  guarded_pskl (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros * H; inversion H; subst; simpl.
  - constructor.
  - destruct_if;
      constructor.
  - constructor; apply subst_pskl_in_pskl_lc_pskl;
      auto using lc_pskl_var_f.
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

Definition auc_uniq_assign := proj1 a_assign_unify_consis_uniq_fprotect.
Definition auc_uniq_unify  :=
  proj1 (proj2 a_assign_unify_consis_uniq_fprotect).
Definition auc_uniq_consis :=
  proj2 (proj2 a_assign_unify_consis_uniq_fprotect).
Definition auc_compat_assign := proj1 a_assign_unify_consis_compat.
Definition auc_compat_unify  := proj1 (proj2 a_assign_unify_consis_compat).
Definition auc_compat_consis := proj2 (proj2 a_assign_unify_consis_compat).
Definition auc_subject_assign := proj1 a_assign_unify_subject_flex.
Definition auc_subject_unify  := proj1 (proj2 a_assign_unify_subject_flex).

(* ===================================================================== *)
(*  §8  L9: renaming a rigid mid entry under an all-rigid prefix          *)
(* ===================================================================== *)

Lemma a_assign_unify_consis_rename_tvar : forall (α : atom),
  (forall F Θi Ξ s P Θo,
     Θi ⊲[ F ][ Ξ ] s ≔ P ⊣ Θo ->
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
       (Ξr ++ (β0 ~ abind_tvar) ++ Θb) ⊲[ F ][ Ξ ] s ≔
         (subst_pskl_in_pskl (pskl_var_f β0) α P)
         ⊣ (Ξr ++ (β0 ~ abind_tvar) ++ Θt)) /\
  (forall F Θi s1 s2 Θo,
     Θi ⊲[ F ] s1 ≈ᵘ s2 ⊣ Θo ->
     exists L, forall (β0 : atom), β0 `notin` L ->
     forall Ξr Θb, Θi = Ξr ++ (α ~ abind_tvar) ++ Θb ->
     tvar_prefix Ξr ->
     uniq Θi ->
     β0 `notin` dom Θi ->
     β0 `notin` dom Θo ->
     s1 <> α -> s1 <> β0 -> s2 <> α -> s2 <> β0 ->
     exists Θt,
       Θo = Ξr ++ (α ~ abind_tvar) ++ Θt /\
       (Ξr ++ (β0 ~ abind_tvar) ++ Θb) ⊲[ F ] s1 ≈ᵘ s2
         ⊣ (Ξr ++ (β0 ~ abind_tvar) ++ Θt)) /\
  (forall F Δ1 Δ2 Θi P0 P P' Θo,
     Θi ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θo ->
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
       (Ξr ++ (β0 ~ abind_tvar) ++ Θb)
         ⊢ₐ[ F ][ (rn_set β0 α Δ1) | (rn_set β0 α Δ2)
         | (subst_pskl_in_pskl (pskl_var_f β0) α P0) ]
         (subst_pskl_in_pskl (pskl_var_f β0) α P)
         ∼ (subst_pskl_in_pskl (pskl_var_f β0) α P')
         ⊣ (Ξr ++ (β0 ~ abind_tvar) ++ Θt)).
Proof.
  intros α.
  apply (a_assign_unify_consis_mutind
           (fun F Θi Ξ s P Θo _ =>
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
                (Ξr ++ (β0 ~ abind_tvar) ++ Θb) ⊲[ F ][ Ξ ] s ≔
                  (subst_pskl_in_pskl (pskl_var_f β0) α P)
                  ⊣ (Ξr ++ (β0 ~ abind_tvar) ++ Θt))
           (fun F Θi s1 s2 Θo _ =>
              exists L, forall (β0 : atom), β0 `notin` L ->
              forall Ξr Θb, Θi = Ξr ++ (α ~ abind_tvar) ++ Θb ->
              tvar_prefix Ξr ->
              uniq Θi ->
              β0 `notin` dom Θi ->
              β0 `notin` dom Θo ->
              s1 <> α -> s1 <> β0 -> s2 <> α -> s2 <> β0 ->
              exists Θt,
                Θo = Ξr ++ (α ~ abind_tvar) ++ Θt /\
                (Ξr ++ (β0 ~ abind_tvar) ++ Θb) ⊲[ F ] s1 ≈ᵘ s2
                  ⊣ (Ξr ++ (β0 ~ abind_tvar) ++ Θt))
           (fun F Δ1 Δ2 Θi P0 P P' Θo _ =>
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
                (Ξr ++ (β0 ~ abind_tvar) ++ Θb)
                  ⊢ₐ[ F ][ (rn_set β0 α Δ1) | (rn_set β0 α Δ2)
                  | (subst_pskl_in_pskl (pskl_var_f β0) α P0) ]
                  (subst_pskl_in_pskl (pskl_var_f β0) α P)
                  ∼ (subst_pskl_in_pskl (pskl_var_f β0) α P')
                  ⊣ (Ξr ++ (β0 ~ abind_tvar) ++ Θt))).
  - (* univ_ghost_id : flex head, vacuous under the all-rigid split *)
    intros F Θ0 s. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* solve_m : flex head, vacuous *)
    intros F Θ0 Ξ s P βs τ Hnα Hg Hm Huβ Hfr. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* assign : defined-flex head, vacuous *)
    intros F Θ0 Θ1 Ξ s β τ P P' Hfl Hc IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* depend : flex head, vacuous *)
    intros F Θ0 Θ1 Ξ s β P Hne Hin Ha IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* skip : flex head, vacuous *)
    intros F Θ0 Θ1 Ξ s β P Hne Hni Ha IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* skip_rigid : the walk case — crossing at Ξr = nil *)
    intros F Θ0 Θ1 Ξ s β P Hni Ha IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP Hsα HsY.
    destruct Ξr as [ | [x bx] Ξr' ]; simpl in Heq.
    + inversion Heq; subst.
      (* CROSSING : β = α; below is reused verbatim, F swaps α ↦ β0 *)
      exists Θ1. split; [ reflexivity | ].
      rewrite subst_pskl_in_pskl_fresh_eq; [ | exact Hni ].
      simpl. apply a_assign__skip_rigid; [ exact HYP | ].
      eapply (auc_compat_assign Ha).
      intros α1 Hα1. apply add_iff in Hα1.
      destruct Hα1 as [-> | HγF].
      * right. clear - HYo. simpl dom in HYo. fsetdec.
      * left. clear - HγF. fsetdec.
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
      apply a_assign__skip_rigid; [ | exact Hren ].
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    P (pskl_var_f β0) α) as Hup.
      simpl in Hup.
      assert (Hββ0 : β <> β0).
      { intros ->. repeat rewrite dom_app in HYi. simpl dom in HYi.
        clear - HYi. fsetdec. }
      clear - Hni Hup Hββ0. fsetdec.
  - (* skip_tm_var : term head, vacuous *)
    intros F Θ0 Θ1 Ξ s x P' P Ha IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* skip_tm_skl : term head, vacuous *)
    intros F Θ0 Θ1 Ξ s x P' P Ha IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* flex_id : identity node *)
    intros F Θ0 s Hf. exists empty.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo Hs1α Hs1Y Hs2α Hs2Y.
    subst Θ0.
    exists Θb. split; [ reflexivity | ].
    apply a_unify__flex_id.
    eapply a_flex_tvar_mid_swap; [ exact Hf | exact Hs1α ].
  - (* flex_l : flex head, vacuous *)
    intros F Θ0 s1 s2 Hne Hf. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* flex_r : flex head, vacuous *)
    intros F Θ0 s1 s2 Hne Hf. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* flex_assign : defined-flex head, vacuous *)
    intros F Θ0 Θ1 α1 τ s1 s2 P' Hfα Hfβ Hc IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* flex_skip : flex head, vacuous *)
    intros F Θ0 Θ1 α1 s1 s2 Hne1 Hne2 Hun IH. exists empty.
    intros β0 HL Ξr Θb Heq Htv. rn_vacuous.
  - (* skip_other : the walk case — crossing at Ξr = nil *)
    intros F Θ0 Θ1 c b s1 s2 Hb Hun IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo Hs1α Hs1Y Hs2α Hs2Y.
    destruct Ξr as [ | [x bx] Ξr' ]; simpl in Heq.
    + inversion Heq; subst.
      (* CROSSING : c = α, b = tvar *)
      exists Θ1. split; [ reflexivity | ].
      apply a_unify__skip_other; [ left; reflexivity | ].
      eapply (auc_compat_unify Hun).
      intros α1 Hα1. apply add_iff in Hα1.
      destruct Hα1 as [-> | HγF].
      * right. clear - HYo. simpl dom in HYo. fsetdec.
      * left. clear - HγF. fsetdec.
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
      apply a_unify__skip_other; [ exact Hb | exact Hren ].
  - (* ghost : axiom node *)
    intros F Δ1 Δ2 Θ0 P0 Hi. exists empty.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    subst Θ0. exists Θb. split; [ reflexivity | ].
    simpl. apply a_consis__ghost.
    apply rn_set_inter_subst_empty; assumption.
  - (* unit : axiom node *)
    intros F Δ1 Δ2 Θ0. exists empty.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    subst Θ0. exists Θb. split; [ reflexivity | ].
    simpl. apply a_consis__unit.
  - (* rigid : axiom node, β1 = α or not *)
    intros F Δ1 Δ2 Θ0 β1 Hbδ. exists empty.
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
    intros F Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2.
    destruct IH1 as [L1 IH1]. destruct IH2 as [L2 IH2].
    exists (L1 `union` L2).
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP0, HYP, HYQ.
    assert (HYo1 : β0 `notin` dom Θ1).
    { pose proof (auc_dom_mono_consis Hc2) as Hd.
      clear - HYo Hd. fsetdec. }
    destruct (IH1 β0 ltac:(clear - HL; fsetdec) Ξr Θb Heq Htv Hu HYi HYo1
                ltac:(clear - HYP0; fsetdec)
                ltac:(clear - HYP; fsetdec)
                ltac:(clear - HYQ; fsetdec)
                Hβ0Δ1 Hβ0Δ2) as [Θm [HeqΘ1 Hren1]].
    assert (Hu1 : uniq Θ1)
      by (destruct (auc_uniq_consis Hc1 ltac:(subst; exact Hu)); assumption).
    assert (HYi1 : β0 `notin` dom Θ1) by exact HYo1.
    destruct (IH2 β0 ltac:(clear - HL; fsetdec) Ξr Θm HeqΘ1 Htv Hu1 HYi1 HYo
                ltac:(clear - HYP0; fsetdec)
                ltac:(clear - HYP; fsetdec)
                ltac:(clear - HYQ; fsetdec)
                Hβ0Δ1 Hβ0Δ2) as [Θt [HeqΘ2 Hren2]].
    exists Θt. split; [ exact HeqΘ2 | ].
    simpl. eapply a_consis__arrow; [ exact Hren1 | exact Hren2 ].
  - (* forall_inh : the rule's own binder joins the avoid-set *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P Q α0 Hfr Hprem IH.
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
    destruct (IH β0 ltac:(clear - HL; fsetdec)
                ((α0, abind_tvar) :: Ξr) Θb
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)
                ltac:(apply uniq_push; [ exact Hu | exact Hα0Θ0 ])
                ltac:(simpl dom; clear - HYi Hβ0α0; fsetdec)
                ltac:(simpl dom; clear - HYo Hβ0α0; fsetdec)
                ltac:(apply notin_ftvar_open_pskl_var;
                      [ exact Hβ0α0 | exact HYP0 ])
                ltac:(apply notin_ftvar_open_pskl_var;
                      [ exact Hβ0α0 | exact HYP ])
                ltac:(exact HYQ')
                ltac:(clear - Hβ0Δ1 Hβ0α0; fsetdec)
                ltac:(clear - Hβ0Δ2 Hβ0α0; fsetdec))
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
               ltac:(simpl; clear - Hα0β0; fsetdec)).
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
    + eapply auc_compat_consis;
        [ exact Hren
        | intros α1 Hα1; left; exact Hα1
        | apply rn_set_add_other; clear - Hαα0; congruence
        | apply rn_set_add_other; clear - Hαα0; congruence ].
  - (* forall_syn : as ForallInh; the input skeleton is carried unchanged *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P Q α0 Hfr Hprem IH.
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
    destruct (IH β0 ltac:(clear - HL; fsetdec)
                ((α0, abind_tvar) :: Ξr) Θb
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)
                ltac:(apply uniq_push; [ exact Hu | exact Hα0Θ0 ])
                ltac:(simpl dom; clear - HYi Hβ0α0; fsetdec)
                ltac:(simpl dom; clear - HYo Hβ0α0; fsetdec)
                ltac:(simpl; exact HYP0)
                ltac:(apply notin_ftvar_open_pskl_var;
                      [ exact Hβ0α0 | exact HYP ])
                ltac:(exact HYQ')
                ltac:(clear - Hβ0Δ1; fsetdec)
                ltac:(clear - Hβ0Δ2 Hβ0α0; fsetdec))
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
               ltac:(simpl; clear - Hα0β0; fsetdec)).
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
    + eapply auc_compat_consis;
        [ exact Hren
        | intros α1 Hα1; left; exact Hα1
        | reflexivity
        | apply rn_set_add_other; clear - Hαα0; congruence ].
  - (* univ_ghost : pass-through *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hc IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP0, HYP, HYQ.
    destruct (IH β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2)
      as [Θt [HeqO Hren]].
    exists Θt. split; [ exact HeqO | ].
    simpl. apply a_consis__univ_ghost. exact Hren.
  - (* univ_ghost1 : as ForallInh; the subject is carried unchanged *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P Q α0 Hfr Hprem IH.
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
    destruct (IH β0 ltac:(clear - HL; fsetdec)
                ((α0, abind_tvar) :: Ξr) Θb
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)
                ltac:(apply uniq_push; [ exact Hu | exact Hα0Θ0 ])
                ltac:(simpl dom; clear - HYi Hβ0α0; fsetdec)
                ltac:(simpl dom; clear - HYo Hβ0α0; fsetdec)
                ltac:(apply notin_ftvar_open_pskl_var;
                      [ exact Hβ0α0 | exact HYP0 ])
                ltac:(simpl; exact HYP)
                ltac:(exact HYQ')
                ltac:(clear - Hβ0Δ1 Hβ0α0; fsetdec)
                ltac:(clear - Hβ0Δ2; fsetdec))
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
               ltac:(simpl; clear - Hα0β0; fsetdec)).
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
    + eapply auc_compat_consis;
        [ exact Hren
        | intros α1 Hα1; left; exact Hα1
        | apply rn_set_add_other; clear - Hαα0; congruence
        | reflexivity ].
  - (* univ_ghost2 : pass-through with guarded/non-flex transports *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP.
    destruct (IH β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0
                ltac:(clear - HYP; fsetdec) HYQ Hβ0Δ1 Hβ0Δ2)
      as [Θt [HeqO Hren]].
    exists Θt. split; [ exact HeqO | ].
    simpl. apply a_consis__univ_ghost2.
    + apply guarded_pskl_subst_var'. exact Hg.
    + subst Θ0. apply a_non_flex_rename;
        [ | exact Hnf ].
      rewrite dom_app in *. simpl dom in HYi. clear - HYi. fsetdec.
    + exact Hren.
  - (* flex : the unify back-edge *)
    intros F Δ1 Δ2 Θ0 Θ1 β11 β12 Hun IH.
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
    intros F Δ1 Δ2 Θ0 Θ1 β1 P0 Hnf Ha IH.
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
    + exact Hren.
  - (* flex_r : the assign back-edge, mirrored *)
    intros F Δ1 Δ2 Θ0 Θ1 β1 P Hnf Ha IH.
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
    + exact Hren.
  - (* ghost_r : axiom node *)
    intros F Δ1 Δ2 Θ0 P Hi. exists empty.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    subst Θ0. exists Θb. split; [ reflexivity | ].
    simpl. apply a_consis__ghost_r.
    apply rn_set_inter_subst_empty; assumption.
  - (* univ_ghost_r : pass-through with guarded/non-flex transports *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH.
    destruct IH as [Lih IH]. exists Lih.
    intros β0 HL Ξr Θb Heq Htv Hu HYi HYo HYP0 HYP HYQ Hβ0Δ1 Hβ0Δ2.
    simpl in HYP0.
    destruct (IH β0 HL Ξr Θb Heq Htv Hu HYi HYo
                ltac:(clear - HYP0; fsetdec) HYP HYQ Hβ0Δ1 Hβ0Δ2)
      as [Θt [HeqO Hren]].
    exists Θt. split; [ exact HeqO | ].
    simpl. apply a_consis__univ_ghost_r.
    + apply guarded_pskl_subst_var'. exact Hg.
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

Lemma a_consis_forall_inh_cofinite : forall L F Δ1 Δ2 Θ0 Θ1 P0 P Q,
  (forall α, α `notin` L ->
     ((α ~ abind_tvar) ++ Θ0)
       ⊢ₐ[ F ][ (add α Δ1) | (add α Δ2)
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼
       (open_pskl_wrt_pskl Q (pskl_var_f α))
       ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
  Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | (pskl_all_syn P0) ]
    (pskl_all_syn P) ∼ (pskl_all_syn Q) ⊣ Θ1.
Proof.
  intros L F Δ1 Δ2 Θ0 Θ1 P0 P Q Hbody.
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

Lemma a_consis_forall_syn_cofinite : forall L F Δ1 Δ2 Θ0 Θ1 P0 P Q,
  (forall α, α `notin` L ->
     ((α ~ abind_tvar) ++ Θ0)
       ⊢ₐ[ F ][ Δ1 | (add α Δ2) | (pskl_tophole P0) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼
       (open_pskl_wrt_pskl Q (pskl_var_f α))
       ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
  Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | (pskl_tophole P0) ]
    (pskl_all_syn P) ∼ (pskl_all_syn Q) ⊣ Θ1.
Proof.
  intros L F Δ1 Δ2 Θ0 Θ1 P0 P Q Hbody.
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

Lemma a_consis_univ_ghost1_cofinite : forall L F Δ1 Δ2 Θ0 Θ1 P0 P Q,
  (forall α, α `notin` L ->
     ((α ~ abind_tvar) ++ Θ0)
       ⊢ₐ[ F ][ (add α Δ1) | Δ2
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (pskl_tophole P) ∼ (open_pskl_wrt_pskl Q (pskl_var_f α))
       ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
  Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | (pskl_all_syn P0) ]
    (pskl_tophole P) ∼ (pskl_all_syn Q) ⊣ Θ1.
Proof.
  intros L F Δ1 Δ2 Θ0 Θ1 P0 P Q Hbody.
  pick fresh α for (L `union` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
                    `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                    `union` Δ1 `union` Δ2).
  replace Q with
    (close_pskl_wrt_pskl α (open_pskl_wrt_pskl Q (pskl_var_f α)))
    by (apply close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        clear - Fr; fsetdec).
  apply a_consis__univ_ghost1 with (α := α);
    [ clear - Fr; fsetdec | apply Hbody; clear - Fr; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §10  Lemma [Decorating algorithmic consistency]                       *)
(* ===================================================================== *)

(** If [aconsis[Δ1|Δ2][P0]{Θ0}{P}{Q}{Θ1}] then
    [aconsistag[Δ1|Δ2][P0][·]{Θ0}{P}{Q}{Θ1}]
    (consistency-proofs.tex, lemma:decorating-algorithmic-consistency).

    MOVED here from prop_decorate.v by the freshness campaign's cluster 4,
    and re-proved as a SIZE induction.  The decorated [a_consistag] ∀ rows
    are (rightly) still COFINITE while [a_consis]'s are now exists-fresh, so
    each ∀ row must rebuild a whole family from the run's ONE binder — which
    means MOVING that binder with §8's rename, and the moved premise is no
    sub-derivation.  Cluster 3 forced the same shape one layer up
    ([a_consistag_decoration_size], prop_decorate_sub.v §7).

    The measure is [size_pskl P + size_pskl P0]: the SUBJECT alone does not
    work, because UnivGhost1 leaves it fixed at [pskl_tophole P] and shrinks
    only the input, while ForallSyn does the opposite.

    Generalized over the used-name set [F] so the induction's indices stay
    VARIABLES (a bare induction on the [F = ∅] instance would capture the
    goal's [Ψ = ∅] literal).  [a_consis]'s own premises all share the root's
    [F], and the decorated rules store the paper-shaped [F = ∅] premises, so
    Leibniz [F = empty] transports through every case. *)

Lemma a_consis_decorate_size : forall n F Δ1 Δ2 Θ0 P0 P P' Θ1,
  size_pskl P + size_pskl P0 <= n ->
  Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 ->
  F = empty ->
  uniq Θ0 ->
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | empty ] (pskl_to_uskl P) ∼˙ P' ⊣ Θ1.
Proof.
  induction n as [ | n IHn ];
    intros F Δ1 Δ2 Θ0 P0 P P' Θ1 Hsz Hc HF Hu.
  { pose proof (size_pskl_min P); pose proof (size_pskl_min P0); lia. }
  revert Hsz HF Hu.
  destruct Hc as
    [ F Δ1 Δ2 Θ0 P0 Hi
    | F Δ1 Δ2 Θ0
    | F Δ1 Δ2 Θ0 α Hb
    | F Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hca Hcb
    | F Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc
    | F Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc
    | F Δ1 Δ2 Θ0 Θ1 P0 P Q Hc
    | F Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc
    | F Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc
    | F Δ1 Δ2 Θ0 Θ1 α β Hun
    | F Δ1 Δ2 Θ0 Θ1 α P0 Hnf Ha
    | F Δ1 Δ2 Θ0 Θ1 α P Hnf Ha
    | F Δ1 Δ2 Θ0 P Hi
    | F Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc ];
    intros Hsz HF Hu; subst; simpl in Hsz |- *.
  - (* Ghost *)
    apply a_consistag__ghost; auto. fsetdec.
  - (* Unit *)
    apply a_consistag__unit. fsetdec.
  - (* Rigid *)
    apply a_consistag__rigid; auto. fsetdec.
  - (* Arrow *)
    eapply a_consistag__arrow;
      [ eapply IHn; [ | exact Hca | reflexivity | exact Hu ]; lia
      | eapply IHn;
        [ | exact Hcb | reflexivity
        | exact (proj1 (auc_uniq_consis Hca Hu)) ]; lia
      | fsetdec ].
  - (* ForallInh (untagged) — rebuild the cofinite family by renaming *)
    (* the rename hands back its own avoid-set (§8): union it into
       the cofinite bound this row was already computing *)
    destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α))
                _ _ _ _ _ _ _ _ Hc) as [Lrn Hrn].
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
    destruct (Hrn β ltac:(clear - Hβ; fsetdec) nil Θ0 eq_refl
                tvar_prefix_nil HuΘ
                Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7) as [Θt [Heq Hren]].
    simpl in Heq. inversion Heq. subst Θt. clear Heq. simpl in Hren.
    rewrite <- (subst_pskl_in_pskl_intro α P0 (pskl_var_f β) HαP0) in Hren.
    rewrite <- (subst_pskl_in_pskl_intro α P (pskl_var_f β) HαP) in Hren.
    rewrite (subst_pskl_in_pskl_spec Q (pskl_var_f β) α) in Hren.
    pose proof (auc_compat_consis Hren
                  (fun α1 Hα1 => or_introl Hα1)
                  (rn_set_add_same β HαΔ1) (rn_set_add_same β HαΔ2)) as Hren'.
    rewrite <- pskl_to_uskl_open_var.
    eapply IHn; [ | exact Hren' | reflexivity | solve_uniq ].
    rewrite ! size_pskl_open_pskl_wrt_pskl_var. lia.
  - (* ForallSyn (untagged) *)
    (* the rename hands back its own avoid-set (§8): union it into
       the cofinite bound this row was already computing *)
    destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α))
                _ _ _ _ _ _ _ _ Hc) as [Lrn Hrn].
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
    assert (Hb3 : β `notin` ftvar_in_pskl (pskl_tophole P0))
      by (simpl; clear - Hβ; fsetdec).
    assert (Hb4 : β `notin`
              ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α)))
      by (apply notin_ftvar_open_pskl_var;
          [ exact Hβα | clear - Hβ; fsetdec ]).
    assert (Hb5 : β `notin` ftvar_in_pskl Q) by (clear - Hβ; fsetdec).
    assert (Hb6 : β `notin` Δ1) by (clear - Hβ; fsetdec).
    assert (Hb7 : β `notin` add α Δ2) by (clear - Hβ Hβα; fsetdec).
    destruct (Hrn β ltac:(clear - Hβ; fsetdec) nil Θ0 eq_refl
                tvar_prefix_nil HuΘ
                Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7) as [Θt [Heq Hren]].
    simpl in Heq. inversion Heq. subst Θt. clear Heq. simpl in Hren.
    rewrite (subst_pskl_in_pskl_fresh_eq P0 (pskl_var_f β) α HαP0) in Hren.
    rewrite <- (subst_pskl_in_pskl_intro α P (pskl_var_f β) HαP) in Hren.
    rewrite (subst_pskl_in_pskl_spec Q (pskl_var_f β) α) in Hren.
    pose proof (auc_compat_consis Hren
                  (fun α1 Hα1 => or_introl Hα1)
                  (rn_set_notin β HαΔ1) (rn_set_add_same β HαΔ2)) as Hren'.
    rewrite <- pskl_to_uskl_open_var.
    eapply IHn; [ | exact Hren' | reflexivity | solve_uniq ].
    rewrite size_pskl_open_pskl_wrt_pskl_var. simpl. lia.
  - (* UnivGhost *)
    apply a_consistag__univ_ghost.
    eapply IHn; [ | exact Hc | reflexivity | exact Hu ]; lia.
  - (* UnivGhost1 *)
    (* the rename hands back its own avoid-set (§8): union it into
       the cofinite bound this row was already computing *)
    destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α))
                _ _ _ _ _ _ _ _ Hc) as [Lrn Hrn].
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
    assert (Hb4 : β `notin` ftvar_in_pskl (pskl_tophole P))
      by (simpl; clear - Hβ; fsetdec).
    assert (Hb5 : β `notin` ftvar_in_pskl Q) by (clear - Hβ; fsetdec).
    assert (Hb6 : β `notin` add α Δ1) by (clear - Hβ Hβα; fsetdec).
    assert (Hb7 : β `notin` Δ2) by (clear - Hβ; fsetdec).
    destruct (Hrn β ltac:(clear - Hβ; fsetdec) nil Θ0 eq_refl
                tvar_prefix_nil HuΘ
                Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7) as [Θt [Heq Hren]].
    simpl in Heq. inversion Heq. subst Θt. clear Heq. simpl in Hren.
    rewrite <- (subst_pskl_in_pskl_intro α P0 (pskl_var_f β) HαP0) in Hren.
    rewrite (subst_pskl_in_pskl_fresh_eq P (pskl_var_f β) α HαP) in Hren.
    rewrite (subst_pskl_in_pskl_spec Q (pskl_var_f β) α) in Hren.
    pose proof (auc_compat_consis Hren
                  (fun α1 Hα1 => or_introl Hα1)
                  (rn_set_add_same β HαΔ1) (rn_set_notin β HαΔ2)) as Hren'.
    change (uskl_tophole (pskl_to_uskl P))
      with (pskl_to_uskl (pskl_tophole P)).
    eapply IHn; [ | exact Hren' | reflexivity | solve_uniq ].
    rewrite size_pskl_open_pskl_wrt_pskl_var. simpl. lia.
  - (* UnivGhost2 *)
    apply a_consistag__univ_ghost2; auto.
    eapply IHn; [ | exact Hc | reflexivity | exact Hu ]; lia.
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
    eapply IHn; [ | exact Hc | reflexivity | exact Hu ]; lia.
Qed.

Lemma a_consis_decorate_gen : forall F Δ1 Δ2 Θ0 P0 P P' Θ1,
  Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 ->
  F = empty ->
  uniq Θ0 ->
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | empty ] (pskl_to_uskl P) ∼˙ P' ⊣ Θ1.
Proof.
  intros * Hc HF Hu.
  eapply a_consis_decorate_size; [ | exact Hc | exact HF | exact Hu ].
  reflexivity.
Qed.

(** The paper-shaped instance (no used names at the root). *)
Lemma a_consis_decorate : forall Δ1 Δ2 Θ0 P0 P P' Θ1,
  Θ0 ⊢ₐ[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 ->
  uniq Θ0 ->
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | empty ] (pskl_to_uskl P) ∼˙ P' ⊣ Θ1.
Proof.
  intros * Hc Hu; eapply a_consis_decorate_gen; eauto.
Qed.
