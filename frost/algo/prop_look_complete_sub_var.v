(** P6-Sv — completeness of constraint collection and solving FOR VARIABLES,
    subtyping side ([lemma:complete-constraint-collection-solving-var],
    subtyping-proofs.tex:1696).

    ⚠️  READ FIRST: the paper's statement is FALSE as given —
    `frost/algo/cex/cex_p6sv_forall_flex.v` refutes it (Qed, axiom-free) at
    ρ = IDENTITY, with the full premise set that closes the consistency twin
    P6-Cv.  This file builds the REPAIRED statement, whose one extra premise
    is [flex_shield] below.  Rationale, call-site analysis and the
    implementation experiments behind it: docs/PAPER-GAPS.md (final entries)
    and docs/DESIGN-completeness-subtyping.md §6 (x)/(y)/(z).

    THE REPAIR IN ONE LINE.  Wherever the constraint payload [P0] has a raw
    Θ0-FLEXIBLE, the facing part of the guess [ψa] must be Δρ-CLEAN *and*
    TAG-FREE.  The Δρ half is P6-Cv's [flex_apart] (a ρ-replaced rigid
    variable opposite a flexible payload is unreachable — LE-FlexR
    freshening).  The TAG half is what the subtyping level adds, and it is
    forced: [Sub-ForallL] turns a TAGGED quantifier of ψa into a ρ-replaced
    variable one step later, so "clean now" is worthless unless "no tags
    now" keeps it clean later.

    TWO FAILURE SHAPES (why the premise must be POSITIONAL and TAG-AWARE):

      (1) machine-checked, cex_p6sv_forall_flex.v — the payload is the whole
          flexible:  Pi = ∀β.β→β,  P0 = α̂,  ψa = ∀^ε β.β→β.
          SolS-ForallL, then SolE-FlexR at the body, gives Pa = ∀β.α̂ and
          the obligation ⟨⟩ ⊑ᵖ β.

      (2) hand-verified (NOT yet machine-checked) — the flexible sits at an
          ARROW-LEFT, i.e. at a CONSISTENCY position, under the same
          ForallL:  Pi = ∀β.((β→β)→⟨⟩),  P0 = α̂→⟨⟩,
          ψa = ∀^ε β.((β→β)→⟨⟩),  M = FN TC,  θα̂ = ⟨⟩→⟨⟩.
          SolS-ForallL, SolS-Arrow, then SolE-FlexR on the left (Pi's left
          component is an ARROW, so SolE-Var does not shield it) gives
          Pa = ∀β.(α̂→⟨⟩) and again ⟨⟩ ⊑ᵖ β.
          ⇒ a premise guarding only the RESULT SPINE of P0 is TOO WEAK, and
            a global "P0 flex-free ∨ ψa tag-free" is TOO STRONG (it would
            reject the legitimate arrow shape α̂→⟨⟩ against ⟨⟩→∀^ε β.…).

    Hence [flex_shield]: positional, with the non-aligned base case
    demanding BOTH conditions.  Its rules are chosen so that every descent
    of THIS induction (arrow = both sides, Sub-ForallR = P0 only,
    Sub-ForallL = ψa only, Sub-UnivGhostL/LG = ψa only) pushes it down —
    see the descent lemmas, whose one-sided cases go through precisely
    because the induction hypothesis re-derives the OPPOSITE-sided rule. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_sub_complete.
Require Import src.frost.algo.prop_look_complete.
Require Import src.frost.algo.prop_look_complete_var.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Raw-flexible-freedom of a payload                                     *)
(* ===================================================================== *)

(** [pskl_flex_free Θ0 P]: no free variable of [P] is a FLEXIBLE of [Θ0]
    (declared or defined).  Stated over [ftvar_in_pskl] rather than
    structurally, so the opening / weakening facts below are set algebra
    instead of inductions. *)
Definition pskl_flex_free (Θ0 : aenv) (P : pskl) : Prop :=
  forall α, α `in` ftvar_in_pskl P -> ~ a_flex_tvar Θ0 α.

Lemma pskl_flex_free_arrow_inv : forall Θ0 P1 P2,
  pskl_flex_free Θ0 (pskl_arrow P1 P2) ->
  pskl_flex_free Θ0 P1 /\ pskl_flex_free Θ0 P2.
Proof.
  intros Θ0 P1 P2 H; split; intros α Hα; apply H; simpl; clear - Hα; fsetdec.
Qed.

Lemma pskl_flex_free_tophole_inv : forall Θ0 P,
  pskl_flex_free Θ0 (pskl_tophole P) -> pskl_flex_free Θ0 P.
Proof. intros Θ0 P H α Hα; apply H; simpl; exact Hα. Qed.

(** Substituting a NON-flexible variable preserves flex-freedom. *)
Lemma pskl_flex_free_subst : forall Θ0 P α1 α2,
  pskl_flex_free Θ0 P ->
  ~ a_flex_tvar Θ0 α2 ->
  pskl_flex_free Θ0 (subst_pskl_in_pskl (pskl_var_f α2) α1 P).
Proof.
  intros Θ0 P α1 α2 H H2 α Hα.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f α2) α1)
    as Hup.
  simpl in Hup.
  destruct (α == α2) as [-> | Hne]; [ exact H2 | ].
  apply H. clear - Hα Hup Hne; fsetdec.
Qed.

(** Opening a ∀-body with a fresh RIGID binder, in the context extended by
    that binder. *)
Lemma pskl_flex_free_open_tvar : forall Θ0 P γ,
  pskl_flex_free Θ0 (pskl_all_syn P) ->
  γ `notin` dom Θ0 ->
  pskl_flex_free ((γ ~ abind_tvar) ++ Θ0)
    (open_pskl_wrt_pskl P (pskl_var_f γ)).
Proof.
  intros Θ0 P γ H Hγ α Hα Hflex.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f γ)) as Hup.
  simpl in Hup.
  destruct (α == γ) as [-> | Hne].
  - (* the fresh binder is RIGID in the extended context *)
    destruct Hflex as [Hb | [τ Hb]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
      solve [ discriminate Habs
            | exfalso; apply Hγ; eapply binds_In; exact Hb' ].
  - apply (H α); [ simpl; clear - Hα Hup Hne; fsetdec | ].
    destruct Hflex as [Hb | [τ Hb]];
      [ left | right; exists τ ];
      (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
       [ contradiction | exact Hb' ]).
Qed.

Lemma pskl_flex_free_weaken_tvar : forall Θ0 P γ,
  pskl_flex_free Θ0 P ->
  pskl_flex_free ((γ ~ abind_tvar) ++ Θ0) P.
Proof.
  intros Θ0 P γ H α Hα Hflex.
  apply (H α Hα).
  destruct Hflex as [Hb | [τ Hb]];
    [ left | right; exists τ ];
    (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
     [ discriminate Habs | exact Hb' ]).
Qed.

(* ===================================================================== *)
(*  [flex_shield Θ0 Ψ' Δρ P0 ψa]  — THE REPAIR PREMISE                    *)
(* ===================================================================== *)

(** Positionally: every raw-Θ0-flexible position of [P0] faces a part of
    [ψa] that is both Δρ-clean and Ψ'-tag-free.

    - [fsh_clean] is the only rule for a NON-ALIGNED pair, and it demands
      BOTH conditions — this is what refutes counterexample (1) (P0 = α̂
      faces a Ψ'-tagged ∀^ε) and (2) (the pair (arrow, ∀) is non-aligned
      and ψa is tagged).
    - [fsh_flexfree] is the other base case: nothing to protect.  It is
      what makes the ForallL descent maintainable — at a TAGGED ψa the
      clean rule is impossible, so a surviving derivation is flex-free or
      structural.
    - [fsh_all_r] BAKES IN the ρ-growth [add α Δρ]: the tagged quantifier
      that Sub-ForallL instantiates is exactly the one whose binder joins
      Δρ, so the descent is an instantiation rather than an argument.
    - [ψa] is [is_tskl], whose shapes are unit / var / arrow / ∀^ε / ⟨⟩̇ /
      ⊤̇◇ — hence no plain-[tophole] row on the right. *)
Inductive flex_shield (Θ0 : aenv) (Ψ' : atoms) : atoms -> pskl -> uskl -> Prop :=
| fsh_clean : forall Δρ P0 ψa,
    (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
    (ftag_in_uskl ψa) ∩ Ψ' [=] empty ->
    flex_shield Θ0 Ψ' Δρ P0 ψa
| fsh_flexfree : forall Δρ P0 ψa,
    pskl_flex_free Θ0 P0 ->
    flex_shield Θ0 Ψ' Δρ P0 ψa
| fsh_arrow : forall Δρ P1 P2 ψ1 ψ2,
    flex_shield Θ0 Ψ' Δρ P1 ψ1 ->
    flex_shield Θ0 Ψ' Δρ P2 ψ2 ->
    flex_shield Θ0 Ψ' Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2)
| fsh_all_l : forall L Δρ P0 ψa,           (* Sub-ForallR descends P0 only *)
    (forall α, α `notin` L ->
       flex_shield Θ0 Ψ' Δρ (open_pskl_wrt_pskl P0 (pskl_var_f α)) ψa) ->
    flex_shield Θ0 Ψ' Δρ (pskl_all_syn P0) ψa
| fsh_all_r : forall L Δρ ε P0 ψ,          (* Sub-ForallL descends ψa only *)
    (forall α, α `notin` L ->
       flex_shield Θ0 Ψ' (add α Δρ) P0 (open_uskl_wrt_uskl ψ (uskl_var_f α))) ->
    flex_shield Θ0 Ψ' Δρ P0 (uskl_all_etag ε ψ)
| fsh_tophole_l : forall Δρ P0 ψa,
    flex_shield Θ0 Ψ' Δρ P0 ψa ->
    flex_shield Θ0 Ψ' Δρ (pskl_tophole P0) ψa
| fsh_topholeg_r : forall Δρ P0 ψ,
    flex_shield Θ0 Ψ' Δρ P0 ψ ->
    flex_shield Θ0 Ψ' Δρ P0 (uskl_topholeg ψ).

(* ===================================================================== *)
(*  Basic kit                                                             *)
(* ===================================================================== *)

(** Δρ is only a "dirty set" upper bound on the clean rule: antitone. *)
Lemma flex_shield_delta_anti : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall Δρ', Δρ' [<=] Δρ ->
  flex_shield Θ0 Ψ' Δρ' P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros Δρ' Hsub.
  - apply fsh_clean; [ clear - H Hsub; fsetdec | exact H0 ].
  - apply fsh_flexfree; exact H.
  - apply fsh_arrow; [ apply IHflex_shield1 | apply IHflex_shield2 ]; exact Hsub.
  - apply fsh_all_l with (L := L); intros α Hα; apply H0; assumption.
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα.
    apply H0; [ exact Hα | clear - Hsub; fsetdec ].
  - apply fsh_tophole_l; apply IHflex_shield; exact Hsub.
  - apply fsh_topholeg_r; apply IHflex_shield; exact Hsub.
Qed.

(** Weakening by a rigid binder (the ForallR descent runs at [Θ0, γ]). *)
Lemma flex_shield_weaken_tvar : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall γ,
  flex_shield ((γ ~ abind_tvar) ++ Θ0) Ψ' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros γ.
  - apply fsh_clean; assumption.
  - apply fsh_flexfree; apply pskl_flex_free_weaken_tvar; exact H.
  - apply fsh_arrow; [ apply IHflex_shield1 | apply IHflex_shield2 ].
  - apply fsh_all_l with (L := L); intros α Hα; apply H0; exact Hα.
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα; apply H0; exact Hα.
  - apply fsh_tophole_l; apply IHflex_shield.
  - apply fsh_topholeg_r; apply IHflex_shield.
Qed.

(** Rigid renaming.  Needed by both binder descents: the derivation's
    cofinite set is existential, so the binder the INDUCTION picks is not
    the one the rule's family offers.  Renaming on the [P0] side leaves
    [ψa] and [Δρ] untouched; on the [ψa] side it moves the Δρ-element too.

    [paper-gap: none — pure mech bookkeeping.] *)
Lemma flex_shield_delta_cong : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall Δρ', Δρ' [=] Δρ ->
  flex_shield Θ0 Ψ' Δρ' P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H Δρ' Heq.
  eapply flex_shield_delta_anti; [ exact H | clear - Heq; fsetdec ].
Qed.

Lemma flex_shield_rename_l : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall α1 α2,
  ~ a_flex_tvar Θ0 α2 ->
  flex_shield Θ0 Ψ' Δρ (subst_pskl_in_pskl (pskl_var_f α2) α1 P0) ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros α1 α2 H2.
  - apply fsh_clean; assumption.
  - apply fsh_flexfree; apply pskl_flex_free_subst; assumption.
  - simpl; apply fsh_arrow;
      [ apply IHflex_shield1 | apply IHflex_shield2 ]; exact H2.
  - simpl. apply fsh_all_l with (L := L `union` singleton α1); intros α Hα.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα; fsetdec | apply lc_pskl_var_f ].
    apply H0; [ clear - Hα; fsetdec | exact H2 ].
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα.
    apply H0; [ exact Hα | exact H2 ].
  - simpl; apply fsh_tophole_l; apply IHflex_shield; exact H2.
  - apply fsh_topholeg_r; apply IHflex_shield; exact H2.
Qed.

(** On the target side the renamed variable is a Δρ ELEMENT — the binder
    that [fsh_all_r] added — so it moves in [Δρ] as well as in [ψa]. *)
Lemma flex_shield_rename_r_gen : forall Θ0 Ψ' Δρ' P0 ψa,
  flex_shield Θ0 Ψ' Δρ' P0 ψa ->
  forall Δρ α1 α2,
  Δρ' [=] add α1 Δρ ->
  α1 `notin` Δρ -> α2 `notin` Δρ -> α2 `notin` ftvar_in_uskl ψa ->
  flex_shield Θ0 Ψ' (add α2 Δρ) P0
    (subst_bskl_in_uskl (uskl_var_f α2) α1 ψa).
Proof.
  intros Θ0 Ψ' Δρ' P0 ψa H; induction H;
    intros Δρ0 α1 α2 Heq Hα1 Hα2 Hα2ψ.
  - (* clean: α1 is not free in ψa (it is in the dirty set), so the
       renaming is the identity *)
    assert (Hfr : α1 `notin` ftvar_in_uskl ψa)
      by (clear - H Heq; fsetdec).
    rewrite (@subst_bskl_in_uskl_fresh_eq ψa (uskl_var_f α2) α1 Hfr).
    apply fsh_clean; [ clear - H Heq Hα2ψ; fsetdec | exact H0 ].
  - apply fsh_flexfree; exact H.
  - simpl in Hα2ψ |- *. apply fsh_arrow;
      [ apply IHflex_shield1 | apply IHflex_shield2 ];
      solve [ exact Heq | exact Hα1 | exact Hα2 | clear - Hα2ψ; fsetdec ].
  - apply fsh_all_l with (L := L); intros α Hα.
    apply H0; solve [ exact Hα | exact Heq | exact Hα1 | exact Hα2
                    | exact Hα2ψ ].
  - (* all_r: the rule's binder joins the dirty set, so the equation is
       re-associated under it *)
    simpl in Hα2ψ |- *.
    apply fsh_all_r with (L := L `union` singleton α1 `union` singleton α2
                            `union` Δρ0) (ε := ε);
      intros α Hα.
    (* extract the pieces of the pick-fresh union ONCE: a [fsetdec] that
       still sees the 4-way union is the known quadratic pattern *)
    assert (HαL : α `notin` L) by (clear - Hα; solve_notin).
    assert (HαΔ : α `notin` Δρ0) by (clear - Hα; solve_notin).
    assert (Hα1' : α <> α1)
      by (apply notin_singleton_1; clear - Hα; solve_notin).
    assert (Hα2' : α <> α2)
      by (apply notin_singleton_1; clear - Hα; solve_notin).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | apply not_eq_sym; exact Hα1' | apply lc_uskl_var_f ].
    eapply flex_shield_delta_cong;
      [ eapply (H0 α HαL (add α Δρ0) α1 α2);
          [ clear - Heq; fsetdec
          | clear - Hα1 Hα1'; fsetdec
          | clear - Hα2 Hα2'; fsetdec
          | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                          (uskl_var_f α)) as Hup;
            simpl in Hup; clear - Hup Hα2ψ Hα2'; fsetdec ]
      | clear; fsetdec ].
  - simpl; apply fsh_tophole_l; apply IHflex_shield;
      solve [ exact Heq | exact Hα1 | exact Hα2 | exact Hα2ψ ].
  - simpl in Hα2ψ |- *. apply fsh_topholeg_r; apply IHflex_shield;
      solve [ exact Heq | exact Hα1 | exact Hα2 | exact Hα2ψ ].
Qed.

Lemma flex_shield_rename_r : forall Θ0 Ψ' Δρ P0 ψa α1 α2,
  flex_shield Θ0 Ψ' (add α1 Δρ) P0 ψa ->
  α1 `notin` Δρ -> α2 `notin` Δρ -> α2 `notin` ftvar_in_uskl ψa ->
  flex_shield Θ0 Ψ' (add α2 Δρ) P0
    (subst_bskl_in_uskl (uskl_var_f α2) α1 ψa).
Proof.
  intros Θ0 Ψ' Δρ P0 ψa α1 α2 H Hα1 Hα2 Hα2ψ.
  eapply flex_shield_rename_r_gen;
    [ exact H | clear; fsetdec | exact Hα1 | exact Hα2 | exact Hα2ψ ].
Qed.

(* ===================================================================== *)
(*  THE DESCENT LEMMAS — one per descent of the P6-Sv induction           *)
(* ===================================================================== *)

(** Sub-Arrow: both sides decompose. *)
Lemma flex_shield_arrow_inv : forall Θ0 Ψ' Δρ P1 P2 ψ1 ψ2,
  flex_shield Θ0 Ψ' Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2) ->
  flex_shield Θ0 Ψ' Δρ P1 ψ1 /\ flex_shield Θ0 Ψ' Δρ P2 ψ2.
Proof.
  intros Θ0 Ψ' Δρ P1 P2 ψ1 ψ2 H.
  remember (pskl_arrow P1 P2) as P0 eqn:HeqP.
  remember (uskl_arrow ψ1 ψ2) as ψa eqn:Heqψ.
  revert P1 P2 ψ1 ψ2 HeqP Heqψ.
  induction H; intros P1' P2' ψ1' ψ2' HeqP Heqψ;
    try discriminate HeqP; try discriminate Heqψ.
  - (* clean: both components inherit both conditions *)
    subst; simpl in H, H0.
    split; apply fsh_clean; clear - H H0; fsetdec.
  - (* flexfree *)
    subst.
    destruct (pskl_flex_free_arrow_inv H) as [Hf1 Hf2].
    split; apply fsh_flexfree; assumption.
  - (* arrow *)
    inversion HeqP; inversion Heqψ; subst; split; assumption.
Qed.

(** Sub-UnivGhostLG: the target loses a dotted ghost, [P0] is kept. *)
Lemma flex_shield_topholeg_r_inv : forall Θ0 Ψ' Δρ P0 ψ,
  flex_shield Θ0 Ψ' Δρ P0 (uskl_topholeg ψ) ->
  flex_shield Θ0 Ψ' Δρ P0 ψ.
Proof.
  intros Θ0 Ψ' Δρ P0 ψ H.
  remember (uskl_topholeg ψ) as ψa eqn:Heqψ.
  revert ψ Heqψ; induction H; intros ψ' Heqψ; try discriminate Heqψ.
  - subst; simpl in H, H0. apply fsh_clean; clear - H H0; fsetdec.
  - apply fsh_flexfree; exact H.
  - (* all_l : push the descent under the P0-binder by the IH *)
    apply fsh_all_l with (L := L); intros α Hα; apply H0; [ exact Hα | exact Heqψ ].
  - (* tophole_l *) apply fsh_tophole_l; apply IHflex_shield; exact Heqψ.
  - (* topholeg_r *) inversion Heqψ; subst; assumption.
Qed.

(** The [P0]-side ⊤◇ strip (SolS-UnivGhostL / SolE-GhostGuarded keep the
    target and strip the payload's ghost). *)
Lemma flex_shield_tophole_l_inv : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ (pskl_tophole P0) ψa ->
  flex_shield Θ0 Ψ' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H.
  remember (pskl_tophole P0) as P eqn:HeqP.
  revert P0 HeqP; induction H; intros P0' HeqP; try discriminate HeqP.
  - apply fsh_clean; assumption.
  - subst; apply fsh_flexfree; apply pskl_flex_free_tophole_inv; exact H.
  - (* all_r : push under the ψa-binder by the IH *)
    apply fsh_all_r with (L := L) (ε := ε); intros α Hα;
      apply H0; [ exact Hα | exact HeqP ].
  - (* tophole_l *) inversion HeqP; subst; assumption.
  - (* topholeg_r *) apply fsh_topholeg_r; apply IHflex_shield; exact HeqP.
Qed.

(** **Sub-ForallR**: [P0 = ∀.P0₀] descends, the target is kept, and the
    context gains the rigid binder.  The [fsh_all_r] case is where the two
    one-sided rules would fail to commute — they do not, because the
    induction hypothesis re-derives the opposite-sided rule. *)
Lemma flex_shield_descend_l : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ (pskl_all_syn P0) ψa ->
  forall γ, γ `notin` dom Θ0 ->
  flex_shield ((γ ~ abind_tvar) ++ Θ0) Ψ' Δρ
    (open_pskl_wrt_pskl P0 (pskl_var_f γ)) ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H.
  remember (pskl_all_syn P0) as P eqn:HeqP.
  revert P0 HeqP; induction H; intros P0' HeqP γ Hγ;
    try discriminate HeqP.
  - (* clean: the target is untouched *)
    apply fsh_clean; assumption.
  - (* flexfree *)
    subst; apply fsh_flexfree; apply pskl_flex_free_open_tvar; assumption.
  - (* all_l: rename the family's binder to γ, then weaken the context *)
    inversion HeqP; subst.
    apply flex_shield_weaken_tvar.
    pick fresh α for (L `union` ftvar_in_pskl P0' `union` singleton γ).
    rewrite (subst_pskl_in_pskl_intro α P0' (pskl_var_f γ));
      [ | clear - Fr; fsetdec ].
    eapply flex_shield_rename_l;
      [ apply (H α ltac:(clear - Fr; fsetdec))
      | intros Hflex;
        (* γ is fresh for Θ0, hence not one of its flexibles *)
        destruct Hflex as [Hb | [τ Hb]];
        apply Hγ; eapply binds_In; eassumption ].
  - (* all_r: rebuild the ψa-side rule from the IH *)
    apply fsh_all_r with (L := L) (ε := ε); intros α Hα.
    apply H0; [ exact Hα | exact HeqP | exact Hγ ].
  - (* topholeg_r *)
    apply fsh_topholeg_r; apply IHflex_shield; [ exact HeqP | exact Hγ ].
Qed.

(** **Sub-ForallL**: the target's TAGGED quantifier is instantiated, so its
    binder joins Δρ.  The clean rule is IMPOSSIBLE here — [ε ∈ Ψ'] and
    [ε ∈ ftag(∀^ε.ψ)] — which is exactly why the premise excludes the two
    counterexamples, and why a surviving derivation is flex-free or
    structural and therefore pushes down. *)
Lemma flex_shield_descend_r : forall Θ0 Ψ' Δρ ε P0 ψ,
  flex_shield Θ0 Ψ' Δρ P0 (uskl_all_etag ε ψ) ->
  ε `in` Ψ' ->
  forall β, β `notin` Δρ -> β `notin` ftvar_in_uskl ψ ->
  flex_shield Θ0 Ψ' (add β Δρ) P0 (open_uskl_wrt_uskl ψ (uskl_var_f β)).
Proof.
  intros Θ0 Ψ' Δρ ε P0 ψ H.
  remember (uskl_all_etag ε ψ) as ψa eqn:Heqψ.
  revert ε ψ Heqψ; induction H; intros ε' ψ' Heqψ Hε β HβΔ Hβ;
    try discriminate Heqψ.
  - (* clean: IMPOSSIBLE — the instantiated tag is in Ψ' *)
    exfalso; subst; simpl in H0. clear - H0 Hε; fsetdec.
  - (* flexfree: nothing to protect, at any Δρ *)
    apply fsh_flexfree; exact H.
  - (* all_l: rebuild the P0-side rule from the IH *)
    apply fsh_all_l with (L := L); intros α Hα.
    eapply H0; [ exact Hα | exact Heqψ | exact Hε | exact HβΔ | exact Hβ ].
  - (* all_r: rename the family's binder to β *)
    inversion Heqψ; subst.
    pick fresh α for (L `union` ftvar_in_uskl ψ' `union` singleton β
                        `union` Δρ).
    rewrite (subst_bskl_in_uskl_intro α ψ' (uskl_var_f β));
      [ | clear - Fr; fsetdec ].
    assert (HαL : α `notin` L) by (clear - Fr; solve_notin).
    assert (HαΔ : α `notin` Δρ) by (clear - Fr; solve_notin).
    assert (Hαψ : α `notin` ftvar_in_uskl ψ') by (clear - Fr; solve_notin).
    eapply flex_shield_rename_r;
      [ apply (H α HαL)
      | exact HαΔ
      | exact HβΔ
      | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ'
                      (uskl_var_f α)) as Hup;
        simpl in Hup;
        assert (Hαβ : α <> β)
          by (apply notin_singleton_1; clear - Fr; solve_notin);
        clear - Hup Hβ Hαβ; fsetdec ].
  - (* tophole_l *)
    apply fsh_tophole_l;
      eapply IHflex_shield; [ exact Heqψ | exact Hε | exact HβΔ | exact Hβ ].
Qed.

(* ===================================================================== *)
(*  Leaf use, and the regression test for the counterexample               *)
(* ===================================================================== *)

(** What the flexible-payload rows of the induction consume.  At a target
    that is neither a tagged ∀ nor a dotted ghost (the shapes with their
    own cases), only [fsh_clean] can justify a flexible [P0] — the
    structural rows need a compound payload and [fsh_flexfree] contradicts
    flexibility — so both conditions come out. *)
Lemma flex_shield_flex_leaf : forall Θ0 Ψ' Δρ α ψa,
  flex_shield Θ0 Ψ' Δρ (pskl_var_f α) ψa ->
  a_flex_tvar Θ0 α ->
  (forall ε ψ, ψa <> uskl_all_etag ε ψ) ->
  (forall ψ, ψa <> uskl_topholeg ψ) ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty /\ (ftag_in_uskl ψa) ∩ Ψ' [=] empty.
Proof.
  intros Θ0 Ψ' Δρ α ψa H.
  remember (pskl_var_f α) as P eqn:HeqP.
  revert α HeqP; induction H; intros α' HeqP Hflex Hnall Hntg;
    try discriminate HeqP.
  - (* clean *) split; assumption.
  - (* flexfree: contradicts the flexibility of α *)
    exfalso; subst. apply (H α'); [ simpl; clear; fsetdec | exact Hflex ].
  - (* all_r: excluded by the shape side condition *)
    exfalso; eapply Hnall; reflexivity.
  - (* topholeg_r: likewise *)
    exfalso; eapply Hntg; reflexivity.
Qed.

(** REGRESSION TEST for the repair: the premise EXCLUDES the configuration
    of the machine-checked counterexample — a raw-flexible payload facing a
    Ψ'-tagged quantifier whose binder is USED in the body.  (When the
    binder is UNUSED the configuration is harmless and correctly allowed:
    ρ replaces nothing, so no dirt reaches the flexible.) *)
Theorem flex_shield_excludes_cex : forall Θ0 Ψ' Δρ α ε ψ,
  a_flex_tvar Θ0 α ->
  ε `in` Ψ' ->
  (forall β, β `notin` ftvar_in_uskl ψ ->
     open_uskl_wrt_uskl ψ (uskl_var_f β)
     = uskl_arrow (uskl_var_f β) (uskl_var_f β)) ->
  ~ flex_shield Θ0 Ψ' Δρ (pskl_var_f α) (uskl_all_etag ε ψ).
Proof.
  intros Θ0 Ψ' Δρ α ε ψ Hflex Hε Hbody H.
  pick fresh β for (Δρ `union` ftvar_in_uskl ψ).
  pose proof (flex_shield_descend_r H Hε (β := β)
                ltac:(clear - Fr; fsetdec) ltac:(clear - Fr; fsetdec)) as Hd.
  rewrite (Hbody β ltac:(clear - Fr; fsetdec)) in Hd.
  destruct (flex_shield_flex_leaf Hd Hflex
              ltac:(intros ε0 ψ0 Hc; discriminate Hc)
              ltac:(intros ψ0 Hc; discriminate Hc)) as [Hclean _].
  cbn [ftvar_in_uskl] in Hclean.
  assert (Hin : β `in` empty) by (rewrite <- Hclean; clear; fsetdec).
  clear - Hin; fsetdec.
Qed.

(* ===================================================================== *)
(*  P6-Sv — THE REPAIRED STATEMENT                                        *)
(*  [lemma:complete-constraint-collection-solving-var]                    *)
(*  (subtyping-proofs.tex:1696)                                           *)
(* ===================================================================== *)

(** Premises are the paper's, threaded exactly as in the CLOSED consistency
    twin [a_solve_eq_complete_var] (prop_look_complete_var.v:3070) —
    ρ/[uskl_rho], the tag bookkeeping, the freshness pack, [flex_apart] —
    with three differences:

    1. the mode [M] and the paper's [skmod{N}{P0}{M}], in the two-implication
       form used by [a_sub_sound_thm] (prop_decorate_key.v:3331);
    2. the subtyping premise [ad_pat_sub_g] (the tag-hygienic fuel mirror)
       in place of consistency — the fuel rides inertly here, since ForallL's
       premise is a structural sub-derivation of [ad_pat_sub_g]; the fuel is
       what P7b's measure consumes;
    3. **[flex_shield] — the repair.**  Without it the statement is FALSE
       (cex_p6sv_forall_flex.v); [flex_shield_excludes_cex] above is the
       regression test that this premise rules the counterexample out.

    Also carried, as in P6-Cs: well-formedness of the consistency SUBJECT
    (⌊ψsub⌋ˢ), the premise whose absence made P6-Cs false.

    CASE MAP for the induction on [ad_pat_sub_g] (paper's own case list at
    :1749, plus the mech-only rows):
      infer/univ_ghost_r/ghostg  ↔ Infer / UnivGhostR / GhostG — leaves with
                                   Ψ = ∅, so Ψa = ∅ and Pa := Pi
      check                      ↔ Case Check — delegates to P6-Cv
                                   [a_solve_eq_complete_var] (flex_apart is
                                   passed straight through), then the four
                                   Pi-subcases guarded / □ / ∀ (impossible)
                                   / ⊤◇ with SolS-Check / GhostL / UnivGhostL
      forall_r                   ↔ Case ForallR — refinement inversion gives
                                   P0 = ∀.P0', descend with
                                   [flex_shield_descend_l]; strip β from the
                                   outputs with P6-Cs's ∀-binder kit
      arrow                      ↔ Case Arrow — [flex_shield_arrow_inv];
                                   left premise → P6-Cv, right → IH
      forall_l_{tagged,untagged} ↔ Case ForallL — ε ∈ Ψi forces Pi = ∀β.P1;
                                   descend with [flex_shield_descend_r]
                                   (whose clean-rule exclusion is exactly
                                   the counterexample's death)
      univ_ghost_l/lg            ↔ Case UnivGhostLG — [flex_shield_tophole_l_inv]
                                   / [flex_shield_topholeg_r_inv]
      ghost                      ↔ Case Ghost — impossible (ψa has no □)
      flex_mono                  ↔ the mech's defined-flexible unfolding *)
Theorem a_solve_sub_complete_var :
  forall n NM M Θ0 Θ θ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  θ ∷ Θ0 ⊑ Θ ->
  uskl_rho NM Θ Δρ Ψρ ψsub ψa ->                    (* ψsub = ρ(ψa) *)
  a_tags_sort NM Ψ' ψa ->
  Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψsub ⌋ˢ ->                       (* subject wf (P6-Cs) *)
  Ψi `union` Ψa [=] Ψ' ->                           (* the paper's Ψi,Ψa = Ψ' *)
  Ψρ ∩ Ψ' [=] empty ->                              (* the paper's fresh{Ψ'} *)
  rho_fresh Δρ Θ θ -> Δρ [<=] Δ ->
  (forall α, α `in` Δρ ->
     α `notin` pskl_shielded_ftv (msubst_pskl θ Pi)) ->
  delta_def_fresh Δ Θ ->
  flex_apart Θ0 Δρ P0 ψa ->                         (* P6-Cv's invariant *)
  flex_shield Θ0 Ψ' Δρ P0 ψa ->                     (* ⇐ THE REPAIR *)
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] ψa ->
  Ψsub [<=] Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  ad_pat_sub_g n NM M Ψsub Θ ψsub Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl θ P0)) ⊳ Q ->
  exists Pa, Θ0 ⊢ₛ Pi ≼[ M ] P0 ⤳ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl θ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
Admitted.  (* TODO[P6-Sv]: the main induction on [ad_pat_sub_g] — case map
              above.  The statement is settled (the repair premise is proved
              to exclude the counterexample by [flex_shield_excludes_cex])
              and every descent it needs is Qed above; what remains is the
              per-case work, which follows the paper's proof text. *)
