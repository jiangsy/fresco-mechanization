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

    …and one row in the OTHER direction, which keeps the premise from being
    too strong: a ρ-REPLACED RIGID VARIABLE ([fsh_rho_var]) is safe opposite
    ANY payload.  With [ψa = ∀^ε β.β] and [P0 = α̂] the algorithm SUCCEEDS
    (precision forces [Pi = ∀β.β]; SolS-ForallL then SolS-Var — the body is
    a VARIABLE — returns [Pa = ∀β.β]); it is only a COMPOUND body like the
    counterexample's [β→β] that sends the solve to SolE-FlexR.  See
    [flex_shield_admits_var_body] against [flex_shield_excludes_cex].

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
Require Import src.frost.algo.prop_consis_precise.  (* d_tags_skl_var_inv *)
Require Import src.frost.algo.prop_consis_sound.    (* a_wf_pskl_lc *)
Require Import src.frost.algo.prop_decorate_sub.    (* lc_uskl_to_pskl_local *)
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
    flex_shield Θ0 Ψ' Δρ P0 (uskl_topholeg ψ)
(* A ρ-REPLACED RIGID VARIABLE is safe opposite ANY payload, flexible or
   not — this is P6-Cv's leaf: the precision premise forces [Pi] to be that
   very variable ([ad_ppre_delta_var_inv] + [msubst_pskl_var_inv]), SolS-Var
   / SolE-Var keep it, and the conclusion's precision is the var rule.  So
   no dirt reaches the payload however dirty the position is.
   WITHOUT this rule the premise is TOO STRONG: it would reject
   [ψa = ∀^ε β.β] against [P0 = α̂] with [Pi = ∀β.β] — where the algorithm
   SUCCEEDS (SolS-ForallL then SolS-Var gives [Pa = ∀β.β], whose precision
   against [∀^ε β.β] holds).  Contrast the counterexample, whose body is
   [β→β]: a compound body sends the solve to SolE-FlexR instead, which is
   what destroys the information. *)
| fsh_rho_var : forall Δρ P0 α,
    α `in` Δρ ->
    flex_shield Θ0 Ψ' Δρ P0 (uskl_var_f α).

(* ===================================================================== *)
(*  Basic kit                                                             *)
(* ===================================================================== *)

(** Δρ is a "dirty set" the clean rule bounds and the ρ-var rule inhabits,
    so the relation is congruent — but NOT antitone — in it. *)
Lemma flex_shield_delta_cong : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall Δρ', Δρ' [=] Δρ ->
  flex_shield Θ0 Ψ' Δρ' P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros Δρ' Heq.
  - apply fsh_clean; [ clear - H Heq; fsetdec | exact H0 ].
  - apply fsh_flexfree; exact H.
  - apply fsh_arrow; [ apply IHflex_shield1 | apply IHflex_shield2 ]; exact Heq.
  - apply fsh_all_l with (L := L); intros α Hα; apply H0; assumption.
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα.
    apply H0; [ exact Hα | clear - Heq; fsetdec ].
  - apply fsh_tophole_l; apply IHflex_shield; exact Heq.
  - apply fsh_topholeg_r; apply IHflex_shield; exact Heq.
  - apply fsh_rho_var; clear - H Heq; fsetdec.
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
  - apply fsh_rho_var; exact H.
Qed.

(** Rigid renaming.  Needed by both binder descents: the derivation's
    cofinite set is existential, so the binder the INDUCTION picks is not
    the one the rule's family offers.  Renaming on the [P0] side leaves
    [ψa] and [Δρ] untouched; on the [ψa] side it moves the Δρ-element too.

    [paper-gap: none — pure mech bookkeeping.] *)
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
  - apply fsh_rho_var; exact H.
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
  - (* rho_var: the renamed variable may BE the ρ-replaced one *)
    simpl.
    match goal with |- context [if ?c then _ else _] => destruct c as [-> | Hne] end.
    + apply fsh_rho_var; clear; fsetdec.
    + apply fsh_rho_var. clear - H Heq Hne; fsetdec.
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
  - (* rho_var: the target is untouched by stripping the payload's ghost *)
    apply fsh_rho_var; exact H.
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
  - (* rho_var: the target is untouched by the ForallR descent *)
    apply fsh_rho_var; exact H.
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
  ((ftvar_in_uskl ψa) ∩ Δρ [=] empty /\ (ftag_in_uskl ψa) ∩ Ψ' [=] empty)
  \/ (exists α0, ψa = uskl_var_f α0 /\ α0 `in` Δρ).
Proof.
  intros Θ0 Ψ' Δρ α ψa H.
  remember (pskl_var_f α) as P eqn:HeqP.
  revert α HeqP; induction H; intros α' HeqP Hflex Hnall Hntg;
    try discriminate HeqP.
  - (* clean *) left; split; assumption.
  - (* flexfree: contradicts the flexibility of α *)
    exfalso; subst. apply (H α'); [ simpl; clear; fsetdec | exact Hflex ].
  - (* all_r: excluded by the shape side condition *)
    exfalso; eapply Hnall; reflexivity.
  - (* topholeg_r: likewise *)
    exfalso; eapply Hntg; reflexivity.
  - (* rho_var: the DIRTY-but-safe row — P6-Cv's leaf closes it *)
    right; eexists; split; [ reflexivity | exact H ].
Qed.

(** ⚠️ SCAFFOLDING — delete once [a_solve_sub_complete_var] is closed, unless
    the proof itself comes to use it.  It exists to justify the shape of the
    repair premise, not to support the development.

    REGRESSION TEST for the repair: the premise EXCLUDES the configuration
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
              ltac:(intros ψ0 Hc; discriminate Hc))
    as [[Hclean _] | (α0 & Hc & _)]; [ | discriminate Hc ].
  cbn [ftvar_in_uskl] in Hclean.
  assert (Hin : β `in` empty) by (rewrite <- Hclean; clear; fsetdec).
  clear - Hin; fsetdec.
Qed.

(** A GUARDED payload skeleton is never precise to a dotted universal ghost:
    its θ-image is unit / a mono paint / an arrow, and the ⊤̇◇ target has no
    matching rule (the mono-paint chain is [ad_ppre_mono_paint_topholeg_absurd]).
    This is what rules out [P-UnivGhostRemove] wherever well-formedness has
    already made the body guarded. *)
Lemma ad_ppre_guarded_topholeg_absurd : forall Θ0 Θ θ Δ Ψ P ψ0,
  a_wf_aenv Θ ->
  θ ∷ Θ0 ⊑ Θ ->
  guarded_pskl P ->
  Θ ⨟ Δ ⊢ (msubst_pskl θ P) ⊑ᵖ[ Ψ ] (uskl_topholeg ψ0) ->
  False.
Proof.
  intros Θ0 Θ θ Δ Ψ P ψ0 HwfΘ Hθ Hg Hpre.
  destruct Hg as [ | α | P1 P2 Hlc1 Hlc2 ]; cbn [msubst_pskl] in Hpre.
  - inversion Hpre.
  - eapply ad_ppre_mono_paint_topholeg_absurd;
      [ exact HwfΘ | exact Hpre | reflexivity | reflexivity
      | eapply a_inc_lookup_mono; exact Hθ ].
  - inversion Hpre.
Qed.

(** ρ transports GUARDEDNESS of the erasure from the subject to the guess.
    The congruence rows need local closure of the guess — which is free:
    [is_tskl] gives it ([is_tskl_lc]).  The ∀/ghost congruences are vacuous,
    since their SUBJECT already erases to a non-guarded skeleton. *)
Lemma uskl_rho_guarded_erase : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  lc_uskl R ->
  guarded_pskl ⌊ R' ⌋ˢ ->
  guarded_pskl ⌊ R ⌋ˢ.
Proof.
  intros NM Θ Δρ Ψρ R' R H Hlc Hg; destruct H; cbn [uskl_to_pskl] in Hg |- *;
    try assumption; try solve [ inversion Hg ].
  - (* leaf: the guess is a variable *) apply guarded_pskl__var.
  - (* arrow: both sides are arrows; lc comes from the guess *)
    inversion Hlc; subst.
    apply guarded_pskl__arrow; apply lc_uskl_to_pskl_local; assumption.
Qed.

(** A □ input skeleton solves to □ or to a universal ghost — the only rules
    with a [□] left-hand side are SolS-Vacuous, SolS-GhostL and
    SolS-GhostLF (SolS-ForallR just threads the output through). *)
Lemma a_solve_sub_hole_output : forall Θ0 m P0 Pa,
  Θ0 ⊢ₛ pskl_hole ≼[ m ] P0 ⤳ Pa ->
  Pa = pskl_hole \/ exists B, Pa = pskl_tophole B.
Proof.
  intros Θ0 m P0 Pa H.
  remember pskl_hole as Ph eqn:HeqP.
  (* surviving rows: SolS-Vacuous (output = the □ input), SolS-Check (□ is
     not guarded), SolS-ForallR (output = the body's), SolS-GhostLF and
     SolS-GhostL (output = a ⊤◇) *)
  induction H; try discriminate HeqP; subst;
    solve [ left; reflexivity
          | right; eexists; reflexivity
          | match goal with Hg : guarded_pskl pskl_hole |- _ => inversion Hg end
          | match goal with
              IH : forall β : atom,
                     β `notin` ?L0 -> pskl_hole = pskl_hole -> _ |- _ =>
                pick fresh β for L0;
                exact (IH β ltac:(clear - Fr; fsetdec) eq_refl)
            end ].
Qed.

(** A □ subject solves no tags: the only rules with a hole subject are
    [P-Ghost] and the target-side flexible unfolding. *)
Lemma ad_ppre_hole_subject_tags : forall Θ Δ Ψ ψ,
  Θ ⨟ Δ ⊢ pskl_hole ⊑ᵖ[ Ψ ] ψ ->
  Ψ [=] empty.
Proof.
  intros Θ Δ Ψ ψ H.
  remember pskl_hole as P eqn:HeqP.
  induction H; try discriminate HeqP; subst;
    solve [ assumption | apply IHad_partial_precise; reflexivity ].
Qed.

(** Stripping a ⊤◇ from the SUBJECT against a GUARDED guess: only
    [P-UnivGhostRemove] applies — [Fill] and [Keep] need a ∀^ε / ⊤̇◇ guess,
    whose erasure is not guarded — and the target-side flexible unfolding is
    rebuilt after recursing through the (monotype) definition. *)
Lemma ad_ppre_tophole_strip : forall Θ Δ Ψ B ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ (pskl_tophole B) ⊑ᵖ[ Ψ ] ψ ->
  guarded_pskl ⌊ ψ ⌋ˢ ->
  Θ ⨟ Δ ⊢ B ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θ Δ Ψ B ψ HwfΘ H.
  remember (pskl_tophole B) as P eqn:HeqP.
  revert B HeqP; induction H; intros B' HeqP Hg;
    try discriminate HeqP; inversion HeqP; subst.
  - (* remove *) assumption.
  - (* fill: the guess is a ∀^ε, whose erasure is a ∀ — not guarded *)
    cbn [uskl_to_pskl] in Hg; inversion Hg.
  - (* keep: the guess is a ⊤̇◇ — likewise *)
    cbn [uskl_to_pskl] in Hg; inversion Hg.
  - (* flex_r: recurse through the definition, then rebuild *)
    eapply ad_ppre__flex_r; [ eassumption | ].
    apply (IHad_partial_precise HwfΘ B' eq_refl).
    match goal with |- guarded_pskl ⌊ ptyp_to_uskl_syn ?τ ⌋ˢ =>
      replace (uskl_to_pskl (ptyp_to_uskl_syn τ)) with (ptyp_to_pskl τ)
        by (symmetry; apply uskl_to_pskl_ptyp)
    end.
    apply mono_ptyp_to_pskl_guarded.
    eapply a_wf_aenv_binds_def_mono; eassumption.
Qed.

(** Lifting a precision judgment under a dotted universal ghost on the
    TARGET.  Only the two subject shapes a □-input solve can produce are
    needed ([a_solve_sub_hole_output]). *)
Lemma ad_ppre_lift_topholeg : forall Θ Δ Ψ P ψ0,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ0 ->
  Δ ∩ ftvar_in_uskl ψ0 [=] empty ->
  guarded_pskl ⌊ ψ0 ⌋ˢ ->
  (P = pskl_hole \/ exists B, P = pskl_tophole B) ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] (uskl_topholeg ψ0).
Proof.
  intros Θ Δ Ψ P ψ0 HwfΘ Hpre HΔ Hg Hshape.
  destruct Hshape as [-> | (B & ->)].
  - (* □ : re-apply P-Ghost; the ghost adds no free variable *)
    apply ad_ppre__hole;
      [ eapply ad_ppre_hole_subject_tags; exact Hpre
      | cbn [ftvar_in_uskl]; exact HΔ ].
  - (* ⊤◇B : strip the subject's ghost, then keep it against the ⊤̇◇ *)
    apply ad_ppre__tophole_keep.
    eapply ad_ppre_tophole_strip; [ exact HwfΘ | exact Hpre | exact Hg ].
Qed.

(* ===================================================================== *)
(*  The ρ-LEAF CLOSER — used by every case of the main induction           *)
(* ===================================================================== *)

(** When the guess at this position is a ρ-REPLACED RIGID VARIABLE, the
    freshness pack forces [Pi] to be that very variable, SolS-Var solves
    with [Pa := Pi], and the conclusion's precision is the var rule.  This
    is the subtyping twin of [p6cv_close_leaf] (prop_look_complete.v:1134):
    same argument, [a_solve_sub__var] in place of [a_solve_eq__var].

    It serves BOTH leaf sources: the [rho_leaf] disjunct of the [uskl_rho]
    inversions, and the [fsh_rho_var] branch of [flex_shield_flex_leaf]. *)
Lemma a_solve_sub_complete_rho_var :
  forall NM m Θ0 Θ θ Δ Δρ Ψ' Ψi Ψa α Pi P0,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ' (uskl_var_f α) ->
  Ψi `union` Ψa [<=] Ψ' ->
  rho_fresh Δρ Θ θ ->
  Δρ [<=] Δ ->
  α `in` Δρ ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl θ Pi)) ->
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f α) ->
  exists Pa, Θ0 ⊢ₛ Pi ≼[ m ] P0 ⤳ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl θ Pa) ⊑ᵖ[ Ψi `union` Ψa ] (uskl_var_f α).
Proof.
  intros NM m Θ0 Θ θ Δ Δρ Ψ' Ψi Ψa α Pi P0
    HwfΘ Htags Hsub Hfresh Hdelta HαΔρ Hshield Hpre.
  pose proof (Hfresh α HαΔρ) as (HXb & Hθav & Hdef).
  assert (HαΔ : α `in` Δ) by (clear - Hdelta HαΔρ; fsetdec).
  pose proof (Hshield α HαΔρ) as Hsh.
  destruct (ad_ppre_delta_var_inv Hpre eq_refl HwfΘ HαΔ HXb Hdef Hsh)
    as (Heqm & HΨie).
  assert (HeqPi : Pi = pskl_var_f α)
    by (eapply msubst_pskl_var_inv; eassumption).
  assert (HΨ'e : Ψ' [=] empty)
    by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
  assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
  exists Pi; split.
  - rewrite HeqPi. apply a_solve_sub__var.
  - rewrite Heqm.
    apply ad_ppre__var; [ clear - HΨie HΨae; fsetdec | left; exact HαΔ ].
Qed.

(** ⚠️ SCAFFOLDING — same status as [flex_shield_excludes_cex]: delete once
    the main theorem is closed, unless the proof uses it.

    The COUNTERPART of the exclusion test, and the reason [fsh_rho_var]
    exists: the premise ADMITS a raw-flexible payload facing a TAGGED ∀
    whose body is the binder itself — [ψa = ∀^ε β.β] — because there the
    algorithm SUCCEEDS.  Precision forces [Pi = ∀β.β]; SolS-ForallL then
    SolS-Var (the body is a VARIABLE) returns [Pa = ∀β.β], whose precision
    against [∀^ε β.β] holds.  Only a COMPOUND body — the counterexample's
    [β→β] — sends the solve to SolE-FlexR and destroys the information.
    Without this row the repair premise would have been strictly stronger
    than the truth, and unusable at such call sites. *)
Theorem flex_shield_admits_var_body : forall Θ0 Ψ' Δρ α ε,
  flex_shield Θ0 Ψ' Δρ (pskl_var_f α) (uskl_all_etag ε (uskl_var_b 0)).
Proof.
  intros Θ0 Ψ' Δρ α ε.
  apply fsh_all_r with (L := empty) (ε := ε); intros α0 Hα0.
  unfold open_uskl_wrt_uskl; simpl.
  apply fsh_rho_var; clear; fsetdec.
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
  intros n NM M Θ0 Θ θ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HwfΘ HwfΘ0 HwfPi HwfP0 HmodSK HmodTY Hθ Hrho Htags HwfSub
         Htageq Hinter Hrhof Hdelta Hshield Hdfresh Hapart Hfsh Hpre
         HΨs1 HΨs2 Hsub Hrefine.
  (* everything except the derivation is generalized: ForallR/ForallL both
     extend Θ0 and Θ, ForallL grows Δρ/Δ and rewrites the tag split, and
     Arrow splits P0/Pi/ψa — so no premise may stay fixed *)
  revert Θ0 θ Δ Δρ Ψρ Ψ' Ψi Ψa ψa Pi P0
         HwfΘ HwfΘ0 HwfPi HwfP0 HmodSK HmodTY Hθ Hrho Htags HwfSub
         Htageq Hinter Hrhof Hdelta Hshield Hdfresh Hapart Hfsh Hpre
         HΨs1 HΨs2 Hrefine.
  (* ⚠️ the lemma's [Ψ'] is re-introduced as [Ψt]: [Ψ'] is a BINDER NAME of
     the ForallL rules, so [induction] has already claimed it *)
  induction Hsub; intros
    Θ0 θ Δ Δρ Ψρ Ψt Ψi Ψa ψa Pi P0
    HwfΘ HwfΘ0 HwfPi HwfP0 HmodSK HmodTY Hθ Hrho Htags HwfSub
    Htageq Hinter Hrhof Hdelta Hshield Hdfresh Hapart Hfsh Hpre
    HΨs1 HΨs2 Hrefine.
  - (* Infer : M = TI, so [skmod] forces P0 = □ and SolS-Vacuous applies
       with Pa := Pi; the rule's [Ψ = ∅] collapses the tag conclusion *)
    assert (HP0 : P0 = pskl_hole).
    { destruct NM;
        [ pose proof (HmodTY eq_refl) as Hm | pose proof (HmodSK eq_refl) as Hm ];
        inversion Hm; reflexivity. }
    subst P0.
    exists Pi; split; [ apply a_solve_sub__vacuous | ].
    eapply ad_partial_precise_psi_cong; [ exact Hpre | ].
    assert (HΨae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
    clear - HΨae; fsetdec.
  - (* Check (TY/TC) : delegate to P6-Cv, then dispatch on Pi *)
    admit.
  - (* ForallR (TY/TC) : refinement gives P0 = ∀.P0'; descend P0 *)
    admit.
  - (* UnivGhostR (SK) : M = TC at sort SK, so [skmod] again forces P0 = □
       and the case closes exactly like Infer *)
    assert (HP0 : P0 = pskl_hole)
      by (pose proof (HmodSK eq_refl) as Hm; inversion Hm; reflexivity).
    subst P0.
    exists Pi; split; [ apply a_solve_sub__vacuous | ].
    eapply ad_partial_precise_psi_cong; [ exact Hpre | ].
    assert (HΨae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
    clear - HΨae; fsetdec.
  - (* Arrow : skmod forces P0 = P01→P02; left → P6-Cv, right → IH *)
    admit.
  - (* ForallL, tagged : ε ∈ Ψi forces Pi = ∀β.P1; descend ψa *)
    admit.
  - (* ForallL, untagged : IMPOSSIBLE.  The subject is an UNTAGGED ∀, and a
       decorated skeleton carries a tag on EVERY quantifier ([is_tskl] has
       only [all_etag]) — so neither ψa nor a ρ-image has this shape.  This
       is the mech's second constructor for the paper's single ForallL rule
       (its ∀^β1 subject has a POTENTIAL tag, declarative.tex:884); the
       tags-sorted target forces β1 = ε, i.e. the tagged row. *)
    exfalso.
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rho_all_syn_l_inv Hrho) as [[Heq _] | [Hleaf | Hcong]].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_tskl (uskl_all_syn R)) by (inversion Htagsub; assumption).
      inversion Htsk'.
    + destruct Hcong as (L0 & R0 & Heq & _); subst ψa; inversion Htsk.
  - (* Ghost (SK) : IMPOSSIBLE — ψa cannot contain a plain □.
       The subject is [uskl_hole]; [uskl_rho_hole_l_inv] leaves either
       ψa = □ (refuted by [is_tskl], which admits only the DOTTED ⟨⟩̇) or a
       ρ-leaf whose image □ would have to be tags-sorted (same refutation). *)
    exfalso.
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rho_hole_l_inv Hrho) as [[Heq _] | Hleaf].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_tskl uskl_hole) by (inversion Htagsub; assumption).
      inversion Htsk'.
  - (* GhostG (SK) : the dotted ⟨⟩̇ subject.  [mod_comp_sk ⟨⟩ M] rules out
       [FN], so M ∈ {TI, TC} and [skmod{SK}] forces P0 = □ once more *)
    assert (HP0 : P0 = pskl_hole).
    { pose proof (HmodSK eq_refl) as Hm; inversion Hm; subst;
        solve [ reflexivity | inversion H0 ]. }
    subst P0.
    exists Pi; split; [ apply a_solve_sub__vacuous | ].
    eapply ad_partial_precise_psi_cong; [ exact Hpre | ].
    assert (HΨae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
    clear - HΨae; fsetdec.
  - (* UnivGhostL (SK) : IMPOSSIBLE for the same reason as Ghost — the
       subject is a PLAIN ⊤◇, and [is_tskl] admits only the DOTTED ⊤̇◇, so
       neither ψa itself nor a ρ-image can have this shape *)
    exfalso.
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rho_tophole_l_inv Hrho) as [[Heq _] | [Hleaf | Hcong]].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_tskl (uskl_tophole R)) by (inversion Htagsub; assumption).
      inversion Htsk'.
    + destruct Hcong as (R0 & Heq & _); subst ψa; inversion Htsk.
  - (* UnivGhostLG (SK) : the DOTTED ⊤̇◇ subject.  ψa is either a ρ-leaf
       (closed by [a_solve_sub_complete_rho_var]) or itself a ⊤̇◇; in the
       latter case the precision premise forces Pi = ⊤◇Pi' or Pi = □, and
       the ⊤◇ row is IH + SolS-UnivGhostL + P-UnivGhostKeep. *)
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    (* the ⊤̇◇-shaped rows share a body; state it once, then dispatch *)
    assert (KEY : forall ψ0,
      uskl_rho a_sub_mode_sk Θ Δρ Ψρ R ψ0 ->
      a_tags_sort a_sub_mode_sk Ψt (uskl_topholeg ψ0) ->
      flex_apart Θ0 Δρ P0 (uskl_topholeg ψ0) ->
      flex_shield Θ0 Ψt Δρ P0 (uskl_topholeg ψ0) ->
      Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] (uskl_topholeg ψ0) ->
      exists Pa, Θ0 ⊢ₛ Pi ≼[ M ] P0 ⤳ Pa /\
        Θ ⨟ Δ ⊢ (msubst_pskl θ Pa) ⊑ᵖ[ Ψi `union` Ψa ] (uskl_topholeg ψ0)).
    { intros ψ0 Hrho0 Htags0 Hapart0 Hfsh0 Hpre0.
      assert (Htags0' : a_tags_sort a_sub_mode_sk Ψt ψ0)
        by (eapply a_tags_sort_topholeg_inv; exact Htags0).
      assert (HwfSub' : Θ ⨟ empty ⊢ₚₛᵃ ⌊ R ⌋ˢ)
        by (cbn [uskl_to_pskl] in HwfSub;
            eapply a_wf_pskl_tophole_inv; exact HwfSub).
      assert (Hapart0' : flex_apart Θ0 Δρ P0 ψ0)
        by (eapply flex_apart_topholeg_target_inv; exact Hapart0).
      assert (Hfsh0' : flex_shield Θ0 Ψt Δρ P0 ψ0)
        by (eapply flex_shield_topholeg_r_inv; exact Hfsh0).
      (* Pi's shape is pinned by the precision premise: only a ⊤◇ or a □
         can be precise to a dotted universal ghost *)
      destruct Pi as [ | nPi | β | Pi1 Pi2 | Pi' | | Pi' ].
      - exfalso; eapply ad_ppre_guarded_topholeg_absurd;
          [ exact HwfΘ | exact Hθ | apply guarded_pskl__unit | exact Hpre0 ].
      - inversion HwfPi.
      - exfalso; eapply ad_ppre_guarded_topholeg_absurd;
          [ exact HwfΘ | exact Hθ | apply guarded_pskl__var | exact Hpre0 ].
      - exfalso.
        assert (Hg : guarded_pskl (pskl_arrow Pi1 Pi2)).
        { pose proof (a_wf_pskl_lc HwfPi) as Hlcarr.
          inversion Hlcarr; subst; apply guarded_pskl__arrow; assumption. }
        eapply ad_ppre_guarded_topholeg_absurd;
          [ exact HwfΘ | exact Hθ | exact Hg | exact Hpre0 ].
      - (* ∀: no precision rule reaches a ⊤̇◇ from a quantifier *)
        cbn [msubst_pskl] in Hpre0; inversion Hpre0.
      - (* □ : the ghost row.  [paper-gap] The paper's UnivGhostLG case says
           "we know that P_i must have a top-level ⊤◇" (subtyping-proofs.tex
           :2196), reading the precision premise as if only P-UnivGhostKeep
           could target a ⊤̇◇.  But P-Ghost is TARGET-AGNOSTIC — [□ ⊑ᵖ[∅] ψ]
           for any ψ — so a hole input is precise to a ⊤̇◇ too, and this row
           is real.  The consistency twin's proof DOES spell out its
           "Subcase P_i = □"; the subtyping write-up simply omits it.
           Nothing is decomposed here (a □ input stays □), so the IH's own
           solve is the one we need; only its precision has to be lifted
           back under the ghost. *)
        cbn [msubst_pskl] in Hpre0.
        pose proof (ad_ppre_hole_subject_tags Hpre0) as HΨie.
        (* the Δ-disjointness the IH needs, read off the SAME premise: the
           ⊤̇◇ adds no free variable, so [P-Ghost]'s side condition at
           [⊤̇◇ψ0] IS the one at ψ0 *)
        assert (HΔψ0 : Δ ∩ ftvar_in_uskl ψ0 [=] empty).
        { (* only [P-Ghost] can conclude with a ⊤̇◇ target from a □ subject:
             the target-side flexible unfolding needs a VARIABLE target *)
          inversion Hpre0; subst; cbn [ftvar_in_uskl] in *; assumption. }
        assert (Hpre0' : Θ ⨟ Δ ⊢ (msubst_pskl θ pskl_hole) ⊑ᵖ[ Ψi ] ψ0)
          by (cbn [msubst_pskl]; apply ad_ppre__hole; assumption).
        edestruct (IHHsub Θ0 θ Δ Δρ Ψρ Ψt Ψi Ψa ψ0 pskl_hole P0
                     HwfΘ HwfΘ0 HwfPi HwfP0 HmodSK HmodTY Hθ Hrho0
                     Htags0' HwfSub' Htageq Hinter Hrhof Hdelta Hshield
                     Hdfresh Hapart0' Hfsh0' Hpre0' HΨs1 HΨs2 Hrefine)
          as (Pa' & Hs' & Hp').
        exists Pa'; split; [ exact Hs' | ].
        eapply ad_ppre_lift_topholeg;
          [ exact HwfΘ | exact Hp' | exact HΔψ0
          | (* the guess erases to a guarded skeleton: ρ transports it from
               the subject, whose ⊤̇◇-body wf makes it guarded *)
            eapply uskl_rho_guarded_erase;
              [ exact Hrho0
              | apply is_tskl_lc; inversion Htags0'; assumption
              | cbn [uskl_to_pskl] in HwfSub;
                inversion HwfSub; assumption ]
          | (* the shape of the output, pushed through the metasubstitution *)
            destruct (a_solve_sub_hole_output Hs') as [-> | (B & ->)];
              [ left; reflexivity
              | right; eexists; cbn [msubst_pskl]; reflexivity ] ].
      - (* ⊤◇Pi' : the main row — IH, then SolS-UnivGhostL *)
        assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi')
          by (eapply a_wf_pskl_tophole_inv; exact HwfPi).
        assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
        cbn [msubst_pskl] in Hpre0.
        inversion Hpre0; subst.
        + (* P-UnivGhostRemove: EXCLUDED — wf makes the ⊤◇-body guarded *)
          exfalso; eapply ad_ppre_guarded_topholeg_absurd;
            [ exact HwfΘ | exact Hθ | exact HgPi' | eassumption ].
        + (* P-UnivGhostKeep *)
          match goal with Hbody : _ ⨟ _ ⊢ _ ⊑ᵖ[ _ ] ψ0 |- _ =>
            rename Hbody into Hpre' end.
          assert (Hshield' : forall α0, α0 `in` Δρ ->
                    α0 `notin` pskl_shielded_ftv (msubst_pskl θ Pi')).
          { intros α0 Hα0. pose proof (Hshield α0 Hα0) as Hsh.
            cbn [msubst_pskl pskl_shielded_ftv] in Hsh.
            pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl θ Pi')) as Hle.
            clear - Hsh Hle; fsetdec. }
          edestruct (IHHsub Θ0 θ Δ Δρ Ψρ Ψt Ψi Ψa ψ0 Pi' P0
                       HwfΘ HwfΘ0 HwfPi' HwfP0 HmodSK HmodTY Hθ Hrho0
                       Htags0' HwfSub' Htageq Hinter Hrhof Hdelta Hshield'
                       Hdfresh Hapart0' Hfsh0' Hpre' HΨs1 HΨs2 Hrefine)
            as (Pa' & Hs' & Hp').
          exists (pskl_tophole Pa'); split.
          * apply a_solve_sub__univ_ghost_l; exact Hs'.
          * cbn [msubst_pskl]; apply ad_ppre__tophole_keep; exact Hp'. }
    destruct (uskl_rho_topholeg_l_inv Hrho) as [[Heq HΨρe] | [Hleaf | Hcong]].
    + (* refl: ρ is the identity here, so ψ0 := R *)
      subst ψa.
      assert (Hlc : lc_uskl R) by (inversion Htsk; apply is_tskl_lc; assumption).
      apply KEY; solve [ apply urho__refl; assumption | assumption ].
    + (* ρ-leaf: ψa is a replaced rigid variable *)
      destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa.
      eapply a_solve_sub_complete_rho_var;
        solve [ exact HwfΘ | exact Htags | clear - Htageq; fsetdec
              | exact Hrhof | exact Hdelta | exact HαΔρ | exact Hshield
              | exact Hpre ].
    + (* congruence: ψa = ⊤̇◇ψ0 with R ρ-related to ψ0 *)
      destruct Hcong as (ψ0 & Heq & Hrho0); subst ψa.
      apply KEY; assumption.
  - (* FlexMono : the subject is a defined flexible; unfold it *)
    admit.
Admitted.  (* TODO[P6-Sv]: 7 of 12 cases are CLOSED; 5 remain (Check,
    ForallR, Arrow, ForallL-tagged, FlexMono), each needing its own P0 × Pi
    grid.  UnivGhostLG is the TEMPLATE they follow: a KEY assertion shared
    by the refl/congruence rows, the ρ-leaf dispatched to
    [a_solve_sub_complete_rho_var], a [destruct Pi] whose guarded rows are
    refuted by [ad_ppre_guarded_topholeg_absurd], the ⊤◇ row running
    IH + SolS-UnivGhostL + P-UnivGhostKeep, and the □ row running the IH
    unchanged and lifting its precision back with [ad_ppre_lift_topholeg].

    Previously closed: Infer, UnivGhostR,
    UnivGhostLG is done except its Pi = □ row (see the note there): its
    ρ-leaf branch goes to [a_solve_sub_complete_rho_var], and its main row
    (Pi = ⊤◇Pi') runs IH + SolS-UnivGhostL + P-UnivGhostKeep, with
    P-UnivGhostRemove excluded by [ad_ppre_guarded_topholeg_absurd].  That
    shape — KEY assertion over the ⊤̇◇-rows, ρ-leaf dispatch, Pi-shape
    destruct with the guarded rows refuted — is the template the remaining
    cases follow.

    Previously closed: Infer, UnivGhostR,
    GhostG (all three: [skmod] forces P0 = □, so SolS-Vacuous returns Pi and
    the rule's [Ψ = ∅] collapses the tag conclusion), and Ghost, UnivGhostL,
    ForallL-untagged (all three IMPOSSIBLE: their subject shape — plain □,
    plain ⊤◇, untagged ∀ — is not [is_tskl], so it is neither ψa's nor a
    ρ-image's).

    The 6 that remain are the ones that need a P0 × Pi case grid, in the
    order they should be attempted:
      1. UnivGhostLG — ψa = ⊤̇◇ψ0; precision inversion gives Pi = ⊤◇Pi' /
         □ / defined-flex; the ⊤◇ row is IH + SolS-UnivGhostL + P-UnivGhostKeep.
         Smallest grid; do it first as the template.
      2. ForallR   — refinement inversion gives P0 = ∀.P0'; descend with
         [flex_shield_descend_l]; strip the binder with P6-Cs's ∀-kit.
      3. ForallL (tagged) — ε ∈ Ψi forces Pi = ∀β.P1 (the paper's argument
         from [Ψi,Ψa = Ψ'] and ε ∉ Ψa); descend with [flex_shield_descend_r].
      4. Check     — delegate to P6-Cv [a_solve_eq_complete_var], then the
         four Pi-subcases guarded / □ / ∀ (impossible) / ⊤◇.
      5. Arrow     — [flex_shield_arrow_inv]; left premise → P6-Cv, right →
         IH; the P0-flexible row is where the repair premise pays off.
      6. FlexMono  — unfold the definition; mirrors P6-Cv's flex_l row.

    All the [flex_shield] descents these consume are Qed above. *)
