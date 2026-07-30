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
          ψa = ∀^ε β.((β→β)→⟨⟩),  M = FN TC,  κα̂ = ⟨⟩→⟨⟩.
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
    [flex_shield_excludes_cex]; this direction is recorded in
    [fsh_rho_var]'s own comment, which is what keeps the premise from
    being made too strong.

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
Require Import src.frost.algo.prop_refine.       (* ad_refine_syn_weaken *)
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_sub_sound.    (* a_wf_pskl_open *)
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_consis_complete.  (* a_wf_pskl_ftv_dom *)
Require Import src.frost.algo.prop_sub_complete.
Require Import src.frost.algo.prop_look_complete.
Require Import src.frost.algo.prop_look_complete_var.
Require Import src.frost.algo.prop_look_complete_cstr.  (* the ∀-binder kit,
    [mono_ptyp_to_uskl_syn_tskl], [ftag_in_uskl_ptyp_to_uskl_syn], … *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  Raw-flexible-freedom of a payload                                     *)
(* ===================================================================== *)

(** [pskl_flex_free] and its kit MOVED UP to prop_look_complete.v — it is
    now a base rule of [flex_apart] too ([fa_flexfree]), so it must be in
    scope before P6-Cv.  See DESIGN §10. *)

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
    - [ψa] is [is_tskl], whose shapes are unit / var / arrow / ∀^ε / ◈ /
      ∀◈ — hence no plain-[tophole] row on the right. *)
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

(** The tag index is a "to be solved" upper bound read only by the clean
    row, so shrinking it only weakens the requirement — which is what the
    Arrow case needs, since each branch carries its OWN tag set. *)
Lemma flex_shield_psi_anti : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall Ψ'', Ψ'' [<=] Ψ' ->
  flex_shield Θ0 Ψ'' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros Ψ'' Hsub.
  - apply fsh_clean; [ exact H | clear - H0 Hsub; fsetdec ].
  - apply fsh_flexfree; exact H.
  - apply fsh_arrow; [ apply IHflex_shield1 | apply IHflex_shield2 ]; exact Hsub.
  - apply fsh_all_l with (L := L); intros α Hα; apply H0; assumption.
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα; apply H0; assumption.
  - apply fsh_tophole_l; apply IHflex_shield; exact Hsub.
  - apply fsh_topholeg_r; apply IHflex_shield; exact Hsub.
  - apply fsh_rho_var; exact H.
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

(** Weakening by a FLEXIBLE prefix (P6-Ss's Sub-Arrow runs its right branch
    at [Ξc1,Θ0], where Ξc1 holds the flexibles the left branch collected).

    This one needs a side condition, and [flex_shield_weaken_tvar] does
    not: [fsh_flexfree] is ANTI-monotone in the context — it asserts that no
    variable of P0 is a Θ0-FLEXIBLE, and a prefix of flexibles could make one
    so.  Requiring the prefix to avoid [ftv P0] is exactly enough, and it is
    what the call site has (Ξc1's names are fresh for Θ0, while P0 is
    Θ0-scoped).  The [fsh_all_l] descent opens a binder, so its cofinite set
    grows by [dom Ξ] to keep the condition. *)
Lemma flex_shield_weaken_flex_prefix : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall Ξ, (ftvar_in_pskl P0) ∩ (dom Ξ) [=] empty ->
  flex_shield (Ξ ++ Θ0) Ψ' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros Ξ Hfr.
  - apply fsh_clean; assumption.
  - (* flexfree: a P0-variable is outside dom Ξ, so its binding is Θ0's *)
    apply fsh_flexfree. intros α Hα Hflex.
    assert (HαΞ : α `notin` dom Ξ) by (clear - Hfr Hα; fsetdec).
    apply (H α Hα).
    destruct Hflex as [Hb | [τ Hb]];
      [ left | right; exists τ ];
      (destruct (binds_app_1 _ _ _ _ _ Hb) as [Hb' | Hb'];
        [ exfalso; apply HαΞ; eapply binds_In; exact Hb' | exact Hb' ]).
  - simpl in Hfr. apply fsh_arrow;
      [ apply IHflex_shield1 | apply IHflex_shield2 ];
      clear - Hfr; fsetdec.
  - (* the opened binder must miss dom Ξ too *)
    apply fsh_all_l with (L := L `union` dom Ξ); intros α Hα.
    apply H0; [ clear - Hα; solve_notin | ].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as Hup.
    simpl in Hup, Hfr. clear - Hup Hfr Hα; fsetdec.
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα; apply H0; assumption.
  - simpl in Hfr. apply fsh_tophole_l; apply IHflex_shield; exact Hfr.
  - apply fsh_topholeg_r; apply IHflex_shield; exact Hfr.
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

(** The [P0]-side ∀◇ strip (SolS-UnivGhostL / SolE-GhostGuarded keep the
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

(** The TWO-SIDED descent — consistency's ForallInh opens BOTH sides at the
    same binder — is just the two one-sided descents composed.  So the
    two-sided row is not a separate obligation: the guess's binder joins Δρ
    (it IS ρ-replaced from the subtyping side's point of view) and the
    payload's binder is a fresh rigid of the context, which is exactly what
    the two descents already deliver. *)
Lemma flex_shield_descend_both : forall Θ0 Ψ' Δρ ε P0 ψ,
  flex_shield Θ0 Ψ' Δρ (pskl_all_syn P0) (uskl_all_etag ε ψ) ->
  ε `in` Ψ' ->
  forall α, α `notin` Δρ -> α `notin` ftvar_in_uskl ψ -> α `notin` dom Θ0 ->
  flex_shield ((α ~ abind_tvar) ++ Θ0) Ψ' (add α Δρ)
    (open_pskl_wrt_pskl P0 (pskl_var_f α))
    (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros Θ0 Ψ' Δρ ε P0 ψ H Hε α HαΔ Hαψ HαΘ.
  apply flex_shield_descend_l;
    [ eapply flex_shield_descend_r; [ exact H | exact Hε | exact HαΔ | exact Hαψ ]
    | exact HαΘ ].
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

(** REGRESSION TEST for the repair — kept (like the [cex/] files) because it
    is what ties the mech-only premise to the machine-checked counterexample;
    the main theorem itself does not use it.

    The premise EXCLUDES the configuration
    of [cex_p6sv_forall_flex.v] — a raw-flexible payload facing a
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
    its κ-image is unit / a mono paint / an arrow, and the ∀◈ target has no
    matching rule (the mono-paint chain is [ad_ppre_mono_paint_topholeg_absurd]).
    This is what rules out [P-UnivGhostRemove] wherever well-formedness has
    already made the body guarded. *)
Lemma ad_ppre_guarded_topholeg_absurd : forall Θ0 Θ κ Δ Ψ P ψ0,
  a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  guarded_pskl P ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ P) ⊑ᵖ[ Ψ ] (uskl_topholeg ψ0) ->
  False.
Proof.
  intros Θ0 Θ κ Δ Ψ P ψ0 HwfΘ Hκ Hg Hpre.
  destruct Hg as [ | α | P1 P2 Hlc1 Hlc2 ]; cbn [msubst_pskl] in Hpre.
  - inversion Hpre.
  - eapply ad_ppre_mono_paint_topholeg_absurd;
      [ exact HwfΘ | exact Hpre | reflexivity | reflexivity
      | eapply a_inc_lookup_mono; exact Hκ ].
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
     SolS-GhostL (output = a ∀◇) *)
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

(** Stripping a ∀◇ from the SUBJECT against a GUARDED guess: only
    [P-UnivGhostRemove] applies — [Fill] and [Keep] need a ∀^ε / ∀◈ guess,
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
  - (* keep: the guess is a ∀◈ — likewise *)
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
  - (* ∀◇B : strip the subject's ghost, then keep it against the ∀◈ *)
    apply ad_ppre__tophole_keep.
    eapply ad_ppre_tophole_strip; [ exact HwfΘ | exact Hpre | exact Hg ].
Qed.

(** The SUBJECT's free variables of a partial-precision derivation come from
    the guess, from Δ, or from Θ's own definitions.  This is what the ∀
    cases use to strip their binder from the OUTPUT — the paper's "by the
    precision conclusion, β ∉ ftv(κa P_a), and thus β ∉ ftv(P_a)"
    (subtyping-proofs.tex:1898). *)
(** A variable the GUESS avoids, that is not a Δ-binder, not a DEFINED
    flexible of Θ and not mentioned by any of Θ's definitions, is avoided by
    the precision's SUBJECT too.  This is what the ∀ cases use to strip
    their binder from the OUTPUT — the paper's "by the precision conclusion,
    β ∉ ftv(κa P_a), and thus β ∉ ftv(P_a)" (subtyping-proofs.tex:1898).
    NB the last two conditions are real: the [flex_l] row puts a defined
    flexible of Θ into the subject, and [flex_r] unfolds a definition, so a
    definition's own variables can surface there. *)
Lemma ad_partial_precise_src_ftv_avoid : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall α, α `notin` ftvar_in_uskl ψ ->
  α `notin` Δ ->
  (forall τ, ~ binds α (abind_flex_mono_def τ) Θ) ->
  α `notin` def_ftv Θ ->
  α `notin` ftvar_in_pskl P.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros α0 Hψ HΔ Hnf Hdf;
    cbn [ftvar_in_pskl ftvar_in_uskl] in *.
  - clear; fsetdec.
  - (* var: the same variable on both sides *) clear - Hψ; fsetdec.
  - (* arrow *)
    pose proof (IHad_partial_precise1 α0 ltac:(clear - Hψ; fsetdec) HΔ Hnf Hdf).
    pose proof (IHad_partial_precise2 α0 ltac:(clear - Hψ; fsetdec) HΔ Hnf Hdf).
    clear - H2 H3; fsetdec.
  - (* ∀ *)
    pick fresh α for (L `union` ftvar_in_pskl P `union` ftvar_in_uskl ψ
                        `union` singleton α0).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α)) as Hup.
    cbn in Hup.
    assert (Hαα0 : α <> α0)
      by (apply not_eq_sym; apply notin_singleton_1; clear - Fr; solve_notin).
    pose proof (H0 α ltac:(clear - Fr; solve_notin) α0
                  ltac:(clear - Hup Hψ Hαα0; fsetdec)
                  ltac:(clear - HΔ Hαα0; fsetdec) Hnf Hdf) as Hα.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α)) as Hlo.
    clear - Hα Hlo; fsetdec.
  - (* □ *) clear; fsetdec.
  - apply IHad_partial_precise; assumption.
  - (* fill: the binder joins Θ as a TVAR, adding no definition *)
    pick fresh α for (L `union` ftvar_in_pskl P `union` ftvar_in_uskl ψ
                        `union` singleton α0 `union` dom Θ).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α)) as Hup.
    cbn in Hup.
    assert (Hαα0 : α <> α0)
      by (apply not_eq_sym; apply notin_singleton_1; clear - Fr; solve_notin).
    pose proof (H0 α ltac:(clear - Fr; solve_notin) α0
                  ltac:(clear - Hup Hψ Hαα0; fsetdec)
                  HΔ
                  ltac:(intros τ0 Hb;
                        destruct (binds_cons_1 _ _ _ _ _ _ Hb)
                          as [[_ Habs] | Hb']; [ discriminate Habs | ];
                        exact (Hnf τ0 Hb'))
                  ltac:(cbn [def_ftv]; exact Hdf)) as Hα.
    cbn [ftvar_in_pskl] in Hα. clear - Hα; fsetdec.
  - apply IHad_partial_precise; assumption.
  - (* flex_l: the subject is a DEFINED flexible of Θ *)
    intros Hin.
    assert (Heq : α0 = α) by (clear - Hin; fsetdec); subst.
    exact (Hnf τ H).
  - (* flex_r: the guess unfolds to a definition, whose variables are
       covered by [def_ftv] *)
    apply IHad_partial_precise; try assumption.
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
    intros Hin. apply Hdf.
    pose proof (@def_ftv_binds Θ α τ H) as Hsub. clear - Hsub Hin; fsetdec.
Qed.

(** Deciding [a_non_flex] on a GUARDED skeleton: it fails only for a
    flexible variable. *)
Lemma a_non_flex_guarded_dec : forall Θ0 P,
  guarded_pskl P ->
  a_non_flex Θ0 P \/ (exists α, P = pskl_var_f α /\ a_flex_tvar Θ0 α).
Proof.
  intros Θ0 P Hg; destruct Hg as [ | α | P1 P2 Hlc1 Hlc2 ].
  - left; split; [ apply lc_pskl_unit | intros Hf; inversion Hf ].
  - destruct (a_flex_tvar_dec Θ0 α) as [Hf | Hf];
      [ right; exists α; split; [ reflexivity | exact Hf ]
      | left; split;
          [ apply lc_pskl_var_f
          | intros Hfl; apply Hf; inversion Hfl; subst;
            [ left | right; eexists ]; eassumption ] ].
  - left; split;
      [ apply lc_pskl_arrow; assumption | intros Hf; inversion Hf ].
Qed.

(* ===================================================================== *)
(*  ρ-EXTENSION — what Sub-ForallL does to the ρ-relation                  *)
(* ===================================================================== *)

(** Sub-ForallL instantiates the guess's tagged quantifier, so the binder it
    opens becomes a ρ-REPLACED variable and the instantiation becomes its
    image: the paper's [ρ_b = ρ ∘ [ψ_b/β]] (subtyping-proofs.tex:1876).
    Mechanically that is a SUBSTITUTION on the subject side of [uskl_rho],
    which turns every β-position into a [urho__leaf].

    The tag set can only be bounded, not computed: if β does NOT occur in
    the guess, the instantiation contributes nothing, so the conclusion
    carries [Ψρ' ⊆ Ψρ ∪ Ψb] plus the two facts callers need — that Ψρ' still
    covers Ψρ, and that it covers Ψb whenever β really occurs.  (At the call
    site the missing case is harmless: [ad_pat_sub_g_ftag_sub] and the
    ForallL rule's hygiene premise force Ψb = ∅ when β is unused.) *)
(** Erasure preserves free variables. *)
Lemma uskl_to_pskl_ftv : forall R,
  ftvar_in_pskl ⌊ R ⌋ˢ [=] ftvar_in_uskl R.
Proof.
  induction R; cbn [uskl_to_pskl ftvar_in_pskl ftvar_in_uskl];
    solve [ clear; fsetdec | fsetdec ].
Qed.

(** Rigid renaming for [uskl_rho], applied to BOTH sides at once — the
    binder rows open both, so this is what turns a single fresh instance
    into a cofinite family (per the standing method rule: binder NAMES never
    obstruct anything).  [α1 ∉ dom Θ] is what keeps the ρ-images fixed: they
    are Θ-scoped, so they cannot mention α1. *)
Lemma uskl_rho_rename : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  forall α1 α2,
  α1 `notin` dom Θ -> α1 `notin` Δρ ->
  uskl_rho NM Θ Δρ Ψρ (subst_bskl_in_uskl (uskl_var_f α2) α1 R')
                      (subst_bskl_in_uskl (uskl_var_f α2) α1 R).
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros α1 α2 HαΘ HαΔ.
  - (* refl *)
    apply urho__refl;
      [ apply subst_bskl_in_uskl_lc_uskl; [ exact H | apply lc_uskl_var_f ]
      | exact H0 ].
  - (* leaf: the replaced variable is in Δρ (so not α1), and the image is
       Θ-scoped (so α1-free) *)
    assert (Hne : α <> α1) by (intros ->; contradiction).
    assert (Hfr : α1 `notin` ftvar_in_uskl ψ'').
    { pose proof (a_wf_pskl_ftv_dom H1) as Hd.
      rewrite uskl_to_pskl_ftv in Hd. clear - Hd HαΘ; fsetdec. }
    rewrite (@subst_bskl_in_uskl_fresh_eq ψ'' (uskl_var_f α2) α1 Hfr).
    cbn [subst_bskl_in_uskl].
    match goal with |- context [if ?c then _ else _] =>
      destruct c as [Heq | _]; [ subst; contradiction | ] end.
    eapply urho__leaf; [ exact H | exact H0 | exact H1 | exact H2 ].
  - (* arrow *)
    cbn [subst_bskl_in_uskl].
    eapply urho__arrow; [ apply IHuskl_rho1 | apply IHuskl_rho2 | exact H1 ];
      assumption.
  - (* ∀ *)
    cbn [subst_bskl_in_uskl].
    apply urho__all_syn with (L := L `union` singleton α1); intros α Hα.
    assert (Hne : α1 <> α) by (apply notin_singleton_1; clear - Hα; solve_notin).
    repeat rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      solve [ apply H0; solve [ clear - Hα; solve_notin | assumption ]
            | exact Hne | apply lc_uskl_var_f ].
  - (* ∀^ε *)
    cbn [subst_bskl_in_uskl].
    apply urho__all_etag with (L := L `union` singleton α1) (ε := ε);
      intros α Hα.
    assert (Hne : α1 <> α) by (apply notin_singleton_1; clear - Hα; solve_notin).
    repeat rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      solve [ apply H0; solve [ clear - Hα; solve_notin | assumption ]
            | exact Hne | apply lc_uskl_var_f ].
  - (* ∀◇ *) cbn [subst_bskl_in_uskl]; apply urho__tophole; auto.
  - (* ∀◈ *) cbn [subst_bskl_in_uskl]; apply urho__topholeg; auto.
Qed.

Lemma uskl_rho_subst_refl : forall NM Θ Δρ R β ψb Ψb,
  lc_uskl R ->
  a_tags_sort NM Ψb ψb ->
  Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψb ⌋ˢ ->
  lc_uskl ψb ->
  exists Ψρ',
    Ψρ' [<=] Ψb /\
    (β `in` ftvar_in_uskl R -> Ψb [<=] Ψρ') /\
    uskl_rho NM Θ (add β Δρ) Ψρ' (subst_bskl_in_uskl ψb β R) R.
Proof.
  intros NM Θ Δρ R β ψb Ψb Hlc Htags Hwf Hlcb.
  induction Hlc; cbn [subst_bskl_in_uskl ftvar_in_uskl].
  - (* ⟨⟩ *)
    exists empty; repeat split;
      [ clear; fsetdec | intros Hin; clear - Hin; fsetdec
      | apply urho__refl; [ apply lc_uskl_unit | clear; fsetdec ] ].
  - (* a variable: the substituted one becomes a ρ-LEAF *)
    match goal with |- context [if ?c then _ else _] =>
      destruct c as [-> | Hne] end.
    + exists Ψb; repeat split;
        [ clear; fsetdec | intros _; clear; fsetdec
        | eapply urho__leaf;
            [ clear; fsetdec | exact Htags | exact Hwf | clear; fsetdec ] ].
    + exists empty; repeat split;
        [ clear; fsetdec
        | intros Hin; exfalso; clear - Hin Hne; fsetdec
        | apply urho__refl; [ apply lc_uskl_var_f | clear; fsetdec ] ].
  - (* arrow *)
    destruct IHHlc1 as (Ψ1 & Hs1 & Hocc1 & Hr1).
    destruct IHHlc2 as (Ψ2 & Hs2 & Hocc2 & Hr2).
    exists (Ψ1 `union` Ψ2); repeat split;
      [ clear - Hs1 Hs2; fsetdec
      | intros Hin;
        destruct (AtomSetProperties.In_dec β (ftvar_in_uskl R1)) as [Hi | Hi];
          [ pose proof (Hocc1 Hi); clear - H; fsetdec
          | assert (Hi2 : β `in` ftvar_in_uskl R2) by (clear - Hin Hi; fsetdec);
            pose proof (Hocc2 Hi2); clear - H; fsetdec ]
      | eapply urho__arrow; [ exact Hr1 | exact Hr2 | clear; fsetdec ] ].
  - (* ∀ (untagged): the IH at ONE fresh binder, renamed into the family *)
    match goal with IH : forall α, _ |- _ =>
      pick fresh α0 for (dom Θ `union` ftvar_in_uskl R `union` singleton β
                           `union` ftvar_in_uskl ψb `union` Δρ);
      destruct (IH α0) as (Ψ1 & Hs1 & Hocc1 & Hr1)
    end.
    exists Ψ1; repeat split.
    + exact Hs1.
    + (* β occurs in the ∀ iff it occurs in any opening *)
      intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      clear - Hin Hlo; fsetdec.
    + apply urho__all_syn with (L := dom Θ `union` singleton α0
                                      `union` ftvar_in_uskl R
                                      `union` ftvar_in_uskl ψb
                                      `union` singleton β);
        intros α Hα.
      assert (Hα0 : α0 `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (Hα0Δ : α0 `notin` add β Δρ)
        by (assert (Hd : α0 `notin` Δρ) by (clear - Fr; solve_notin);
            assert (Hb : α0 <> β)
              by (apply notin_singleton_1; clear - Fr; solve_notin);
            clear - Hd Hb; fsetdec).
      pose proof (uskl_rho_rename Hr1 (α1 := α0) α Hα0 Hα0Δ) as Hren.
      assert (Hα0ψb : α0 `notin` ftvar_in_uskl ψb)
        by (clear - Fr; solve_notin).
      assert (Hα0β : α0 <> β)
        by (apply notin_singleton_1; clear - Fr; solve_notin).
      assert (Hα0R : α0 `notin` ftvar_in_uskl R) by (clear - Fr; solve_notin).
      assert (Hβα : β <> α)
        by (apply not_eq_sym; apply notin_singleton_1;
            clear - Hα; solve_notin).
      (* push the rename PAST the instantiation (α0 avoids ψb), then read
         both sides back as openings at α *)
      rewrite (@subst_bskl_in_uskl_subst_bskl_in_uskl
                 (open_uskl_wrt_uskl R (uskl_var_f α0)) (uskl_var_f α) ψb
                 β α0
                 ltac:(cbn [ftvar_in_uskl]; clear - Hβα; fsetdec)
                 ltac:(apply not_eq_sym; exact Hα0β)) in Hren.
      rewrite (@subst_bskl_in_uskl_fresh_eq ψb (uskl_var_f α) α0 Hα0ψb)
        in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R (uskl_var_f α) Hα0R)
        in Hren.
      rewrite (@subst_bskl_in_uskl_open_uskl_wrt_uskl_var R ψb β α Hβα Hlcb).
      exact Hren.
  - (* ∀^ε : the same, with the tag carried through *)
    match goal with IH : forall α, _ |- _ =>
      pick fresh α0 for (dom Θ `union` ftvar_in_uskl R `union` singleton β
                           `union` ftvar_in_uskl ψb `union` Δρ);
      destruct (IH α0) as (Ψ1 & Hs1 & Hocc1 & Hr1)
    end.
    exists Ψ1; repeat split.
    + exact Hs1.
    + (* β occurs in the ∀ iff it occurs in any opening *)
      intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      clear - Hin Hlo; fsetdec.
    + apply urho__all_etag with (ε := ε) (L := dom Θ `union` singleton α0
                                      `union` ftvar_in_uskl R
                                      `union` ftvar_in_uskl ψb
                                      `union` singleton β);
        intros α Hα.
      assert (Hα0 : α0 `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (Hα0Δ : α0 `notin` add β Δρ)
        by (assert (Hd : α0 `notin` Δρ) by (clear - Fr; solve_notin);
            assert (Hb : α0 <> β)
              by (apply notin_singleton_1; clear - Fr; solve_notin);
            clear - Hd Hb; fsetdec).
      pose proof (uskl_rho_rename Hr1 (α1 := α0) α Hα0 Hα0Δ) as Hren.
      assert (Hα0ψb : α0 `notin` ftvar_in_uskl ψb)
        by (clear - Fr; solve_notin).
      assert (Hα0β : α0 <> β)
        by (apply notin_singleton_1; clear - Fr; solve_notin).
      assert (Hα0R : α0 `notin` ftvar_in_uskl R) by (clear - Fr; solve_notin).
      assert (Hβα : β <> α)
        by (apply not_eq_sym; apply notin_singleton_1;
            clear - Hα; solve_notin).
      (* push the rename PAST the instantiation (α0 avoids ψb), then read
         both sides back as openings at α *)
      rewrite (@subst_bskl_in_uskl_subst_bskl_in_uskl
                 (open_uskl_wrt_uskl R (uskl_var_f α0)) (uskl_var_f α) ψb
                 β α0
                 ltac:(cbn [ftvar_in_uskl]; clear - Hβα; fsetdec)
                 ltac:(apply not_eq_sym; exact Hα0β)) in Hren.
      rewrite (@subst_bskl_in_uskl_fresh_eq ψb (uskl_var_f α) α0 Hα0ψb)
        in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R (uskl_var_f α) Hα0R)
        in Hren.
      rewrite (@subst_bskl_in_uskl_open_uskl_wrt_uskl_var R ψb β α Hβα Hlcb).
      exact Hren.
  - (* ⟨⟩ hole *)
    exists empty; repeat split;
      [ clear; fsetdec | intros Hin; clear - Hin; fsetdec
      | apply urho__refl; [ apply lc_uskl_hole | clear; fsetdec ] ].
  - (* ∀◇ *)
    destruct IHHlc as (Ψ1 & Hs1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hocc1 | apply urho__tophole; exact Hr1 ].
  - (* ◈ *)
    exists empty; repeat split;
      [ clear; fsetdec | intros Hin; clear - Hin; fsetdec
      | apply urho__refl; [ apply lc_uskl_holeg | clear; fsetdec ] ].
  - (* ∀◈ *)
    destruct IHHlc as (Ψ1 & Hs1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hocc1 | apply urho__topholeg; exact Hr1 ].
Qed.

(** [uskl_rho_subst_refl] is the [ρ = id] component of the ρ-extension the
    ForallL case needs.  The general form recurses on the [uskl_rho]
    derivation and calls this at its [urho__refl] nodes, maps [urho__leaf]
    to itself (the images are Θ-scoped, hence β-free) and the congruences to
    themselves — with the same tag BOUND, since a binder the guess does not
    use contributes nothing. *)

(** The Arrow case's TAG SPLIT.  The guess's tags are partitioned by the
    arrow ([d_tags_skl__arrow] is a DISJOINT union), the already-solved ones
    split with the precision, and each branch's newly-solved set is then
    just the intersection — no choice is involved. *)
Lemma arrow_tag_split : forall Ψt Ψt1 Ψt2 Ψi Ψi1 Ψi2 Ψa,
  Ψt [=] Ψt1 `union` Ψt2 ->
  Ψt1 ∩ Ψt2 [=] empty ->
  Ψi [=] Ψi1 `union` Ψi2 ->
  Ψi1 [<=] Ψt1 -> Ψi2 [<=] Ψt2 ->
  Ψi `union` Ψa [=] Ψt ->
  Ψi1 `union` (Ψa ∩ Ψt1) [=] Ψt1 /\
  Ψi2 `union` (Ψa ∩ Ψt2) [=] Ψt2.
Proof.
  intros Ψt Ψt1 Ψt2 Ψi Ψi1 Ψi2 Ψa Ht Hd Hi Hs1 Hs2 Heq.
  split; clear - Ht Hd Hi Hs1 Hs2 Heq; fsetdec.
Qed.

(** ρ preserves decoratedness: images are tags-sorted and the congruences
    keep the shape. *)
(* [uskl_rho_is_tskl] MOVED to prop_look_complete.v (P6-Cs needs it under
   the ρ-generalization, and this file is downstream of P6-Cs). *)

(** THE ρ-EXTENSION.  Sub-ForallL's [ρ_b = ρ ∘ [ψ_b/β]] in full: recurse on
    the ρ-derivation, use the [ρ = id] lemma at its reflexive nodes, keep
    the leaves (their images are Θ-scoped, hence β-free) and the
    congruences.  The binder rows go through the same way as there — one
    fresh instance, renamed into the family. *)
Lemma uskl_rho_subst : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  forall β ψb Ψb,
  a_tags_sort NM Ψb ψb ->
  Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψb ⌋ˢ ->
  lc_uskl ψb ->
  β `notin` dom Θ ->
  β `notin` Δρ ->
  exists Ψρ',
    Ψρ' [<=] Ψρ `union` Ψb /\
    Ψρ [<=] Ψρ' /\
    (β `in` ftvar_in_uskl R -> Ψb [<=] Ψρ') /\
    uskl_rho NM Θ (add β Δρ) Ψρ' (subst_bskl_in_uskl ψb β R') R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H;
    intros β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ.
  - (* refl : the ρ = id lemma *)
    destruct (@uskl_rho_subst_refl NM Θ Δρ R β ψb Ψb H Htags Hwfb Hlcb)
      as (Ψ1 & Hs1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ clear - Hs1; fsetdec | clear - H0; fsetdec | exact Hocc1 | exact Hr1 ].
  - (* leaf : the image is Θ-scoped, so β does not occur in it *)
    assert (Hfr : β `notin` ftvar_in_uskl ψ'').
    { pose proof (a_wf_pskl_ftv_dom H1) as Hd.
      rewrite uskl_to_pskl_ftv in Hd. clear - Hd HβΘ; fsetdec. }
    rewrite (@subst_bskl_in_uskl_fresh_eq ψ'' ψb β Hfr).
    exists Ψρ; repeat split;
      [ clear; fsetdec | clear; fsetdec
      | (* β is not a ρ-replaced variable, so it is not THIS one *)
        intros Hin; exfalso; cbn [ftvar_in_uskl] in Hin;
        assert (Heq : β = α) by (clear - Hin; fsetdec); subst;
        contradiction
      | eapply urho__leaf;
          [ clear - H; fsetdec | exact H0 | exact H1 | exact H2 ] ].
  - (* arrow *)
    destruct (IHuskl_rho1 β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψa1 & Hs1 & Hm1 & Hocc1 & Hr1).
    destruct (IHuskl_rho2 β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψa2 & Hs2 & Hm2 & Hocc2 & Hr2).
    exists (Ψa1 `union` Ψa2); repeat split.
    + clear - Hs1 Hs2 H1; fsetdec.
    + clear - Hm1 Hm2 H1; fsetdec.
    + intros Hin; cbn [ftvar_in_uskl] in Hin.
      destruct (AtomSetProperties.In_dec β (ftvar_in_uskl R1)) as [Hi | Hi];
        [ pose proof (Hocc1 Hi); clear - H2; fsetdec
        | assert (Hi2 : β `in` ftvar_in_uskl R2) by (clear - Hin Hi; fsetdec);
          pose proof (Hocc2 Hi2); clear - H2; fsetdec ].
    + cbn [subst_bskl_in_uskl].
      eapply urho__arrow; [ exact Hr1 | exact Hr2 | clear; fsetdec ].
  - (* ∀ : one fresh instance, renamed into the family *)
    pick fresh α0 for (L `union` dom Θ `union` Δρ `union` singleton β
                         `union` ftvar_in_uskl R `union` ftvar_in_uskl R'
                         `union` ftvar_in_uskl ψb).
    destruct (H0 α0 ltac:(clear - Fr; solve_notin) β ψb Ψb
                Htags Hwfb Hlcb HβΘ HβΔ) as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split.
    + exact Hs1.
    + exact Hm1.
    + intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      cbn [ftvar_in_uskl] in Hin. clear - Hin Hlo; fsetdec.
    + cbn [subst_bskl_in_uskl].
      apply urho__all_syn with (L := L `union` dom Θ `union` Δρ
                                       `union` singleton α0
                                       `union` singleton β
                                       `union` ftvar_in_uskl R
                                       `union` ftvar_in_uskl R'
                                       `union` ftvar_in_uskl ψb);
        intros α Hα.
      assert (Hα0Θ : α0 `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (Hα0Δ : α0 `notin` add β Δρ)
        by (assert (Hd : α0 `notin` Δρ) by (clear - Fr; solve_notin);
            assert (Hb : α0 <> β)
              by (apply notin_singleton_1; clear - Fr; solve_notin);
            clear - Hd Hb; fsetdec).
      pose proof (uskl_rho_rename Hr1 (α1 := α0) α Hα0Θ Hα0Δ) as Hren.
      assert (Hα0ψb : α0 `notin` ftvar_in_uskl ψb)
        by (clear - Fr; solve_notin).
      assert (Hα0β : α0 <> β)
        by (apply notin_singleton_1; clear - Fr; solve_notin).
      assert (Hβα : β <> α)
        by (apply not_eq_sym; apply notin_singleton_1;
            clear - Hα; solve_notin).
      rewrite (@subst_bskl_in_uskl_subst_bskl_in_uskl
                 (open_uskl_wrt_uskl R' (uskl_var_f α0)) (uskl_var_f α) ψb
                 β α0
                 ltac:(cbn [ftvar_in_uskl]; clear - Hβα; fsetdec)
                 ltac:(apply not_eq_sym; exact Hα0β)) in Hren.
      rewrite (@subst_bskl_in_uskl_fresh_eq ψb (uskl_var_f α) α0 Hα0ψb)
        in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R' (uskl_var_f α)
                    ltac:(clear - Fr; solve_notin)) in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R (uskl_var_f α)
                    ltac:(clear - Fr; solve_notin)) in Hren.
      rewrite (@subst_bskl_in_uskl_open_uskl_wrt_uskl_var R' ψb β α Hβα Hlcb).
      exact Hren.
  - (* ∀^ε : the same, with the tag carried through *)
    pick fresh α0 for (L `union` dom Θ `union` Δρ `union` singleton β
                         `union` ftvar_in_uskl R `union` ftvar_in_uskl R'
                         `union` ftvar_in_uskl ψb).
    destruct (H0 α0 ltac:(clear - Fr; solve_notin) β ψb Ψb
                Htags Hwfb Hlcb HβΘ HβΔ) as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split.
    + exact Hs1.
    + exact Hm1.
    + intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      cbn [ftvar_in_uskl] in Hin. clear - Hin Hlo; fsetdec.
    + cbn [subst_bskl_in_uskl].
      apply urho__all_etag with (ε := ε)
        (L := L `union` dom Θ `union` Δρ `union` singleton α0
                `union` singleton β `union` ftvar_in_uskl R
                `union` ftvar_in_uskl R' `union` ftvar_in_uskl ψb);
        intros α Hα.
      assert (Hα0Θ : α0 `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (Hα0Δ : α0 `notin` add β Δρ)
        by (assert (Hd : α0 `notin` Δρ) by (clear - Fr; solve_notin);
            assert (Hb : α0 <> β)
              by (apply notin_singleton_1; clear - Fr; solve_notin);
            clear - Hd Hb; fsetdec).
      pose proof (uskl_rho_rename Hr1 (α1 := α0) α Hα0Θ Hα0Δ) as Hren.
      assert (Hα0ψb : α0 `notin` ftvar_in_uskl ψb)
        by (clear - Fr; solve_notin).
      assert (Hα0β : α0 <> β)
        by (apply notin_singleton_1; clear - Fr; solve_notin).
      assert (Hβα : β <> α)
        by (apply not_eq_sym; apply notin_singleton_1;
            clear - Hα; solve_notin).
      rewrite (@subst_bskl_in_uskl_subst_bskl_in_uskl
                 (open_uskl_wrt_uskl R' (uskl_var_f α0)) (uskl_var_f α) ψb
                 β α0
                 ltac:(cbn [ftvar_in_uskl]; clear - Hβα; fsetdec)
                 ltac:(apply not_eq_sym; exact Hα0β)) in Hren.
      rewrite (@subst_bskl_in_uskl_fresh_eq ψb (uskl_var_f α) α0 Hα0ψb)
        in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R' (uskl_var_f α)
                    ltac:(clear - Fr; solve_notin)) in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R (uskl_var_f α)
                    ltac:(clear - Fr; solve_notin)) in Hren.
      rewrite (@subst_bskl_in_uskl_open_uskl_wrt_uskl_var R' ψb β α Hβα Hlcb).
      exact Hren.
  - (* ∀◇ *)
    destruct (IHuskl_rho β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hm1 | exact Hocc1
      | cbn [subst_bskl_in_uskl]; apply urho__tophole; exact Hr1 ].
  - (* ∀◈ *)
    destruct (IHuskl_rho β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hm1 | exact Hocc1
      | cbn [subst_bskl_in_uskl]; apply urho__topholeg; exact Hr1 ].
Qed.

(* [fa_step] / [fa_walk] / [flex_apart_walk] and its three lemmas MOVED to
   prop_look_complete.v, next to [flex_apart] itself: P6-Cs needs them too
   under the ρ-generalization, and this file is DOWNSTREAM of P6-Cs. *)

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
  forall NM m Θ0 Θ κ Δ Δρ Ψ' Ψi Ψa α Pi P0,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ' (uskl_var_f α) ->
  Ψi `union` Ψa [<=] Ψ' ->
  rho_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  α `in` Δρ ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f α) ->
  exists Pa, Θ0 ⊢ₛ Pi ≼[ m ] P0 ⤳ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] (uskl_var_f α).
Proof.
  intros NM m Θ0 Θ κ Δ Δρ Ψ' Ψi Ψa α Pi P0
    HwfΘ Htags Hsub Hfresh Hdelta HαΔρ Hshield Hpre.
  pose proof (Hfresh α HαΔρ) as (HXb & Hκav & Hdef).
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

(* ===================================================================== *)
(*  Sub-ForallL kit                                                        *)
(* ===================================================================== *)

(** ρ only ever REPLACES a variable by a decorated skeleton, so the source's
    tags all survive into the image.  (The converse bound, with the
    replacement tags added, is [uskl_rho_ftag_sub].) *)
Lemma uskl_rho_ftag_target_sub : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  ftag_in_uskl R [<=] ftag_in_uskl R'.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; cbn [ftag_in_uskl];
    try solve [ clear; fsetdec | clear - IHuskl_rho; fsetdec
              | clear - IHuskl_rho1 IHuskl_rho2; fsetdec ].
  - (* ∀ (untagged) : opening with a variable adds no tag *)
    pick fresh α for L.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    rewrite (ftag_in_uskl_open_var R α) in Hα.
    rewrite (ftag_in_uskl_open_var R' α) in Hα.
    exact Hα.
  - (* ∀^ε *)
    pick fresh α for L.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    rewrite (ftag_in_uskl_open_var R α) in Hα.
    rewrite (ftag_in_uskl_open_var R' α) in Hα.
    clear - Hα; fsetdec.
Qed.

(** The mirror of [uskl_rho_ftv_target_bound]: ρ's images are Θ-scoped, so
    the IMAGE's free variables are the source's plus the context's.  Sub-
    ForallL needs it to know that a source binder unused under ρ is unused
    in the image too. *)
(* [uskl_rho_ftv_subject_bound] MOVED to prop_look_complete.v — P6-Cs needs
   it under the ρ-generalization, and this file is downstream of P6-Cs. *)

(** A ∀◇ body is well-formed at the EMPTY Δ ([a_wf_pskl__tophole]), so no
    SHIELDED variable of a well-formed skeleton can be a locally bound one:
    they are all in [dom Θ].  This is the discipline DESIGN §7 names when it
    says the freshly opened binder "stays out of ∀◇ bodies" — it is what
    lets Sub-ForallL add its binder to Δρ. *)
Lemma a_wf_pskl_shielded_dom : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  pskl_shielded_ftv P [<=] dom Θ.
Proof.
  intros Θ Δ P H; induction H; cbn [pskl_shielded_ftv];
    try solve [ clear; fsetdec | clear - IHa_wf_pskl1 IHa_wf_pskl2; fsetdec ].
  - (* ∀ : the shielded variables of a body are already the binder's *)
    pick fresh α for (L `union` pskl_shielded_ftv P).
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    pose proof (pskl_shielded_ftv_open_lower P (pskl_var_f α)) as Hlo.
    clear - Hα Hlo; fsetdec.
  - (* ∀◇ : the body is well-formed at Δ = ∅ *)
    pose proof (a_wf_pskl_ftv_dom H0) as Hd. clear - Hd; fsetdec.
Qed.

(** The converse of [a_wf_pskl_delta_to_tvar_mid], for PRECISION: a rigid
    binder that ALREADY sits in Δ may be dropped from the aenv.  Sub-ForallL
    needs exactly this — the recursive call runs at [Θ,β] because
    [rho_fresh] insists every ρ-replaced variable be a rigid of the context,
    while the precision the case must REBUILD lives at Θ with β only in Δ.
    (The [strip] version in prop_look_complete_cstr.v instead demands β free
    in NEITHER side; here β is free in both, and Δ-membership is what keeps
    the var rule alive.) *)
Lemma ad_partial_precise_tvar_to_delta_mid : forall Θf Δ Ψ P ψ,
  Θf ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall β Θ1 Θ2, Θf = Θ1 ++ (β ~ abind_tvar) ++ Θ2 ->
  β `notin` dom Θ1 -> β `notin` dom Θ2 ->
  β `in` Δ ->
  (Θ1 ++ Θ2) ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θf Δ Ψ P ψ H; induction H;
    intros β Θ1 Θ2 Heq Hd1 Hd2 HβΔ; subst.
  - apply ad_ppre__unit; assumption.
  - (* var : if the variable IS β, Δ-membership takes over *)
    match goal with Hor : _ \/ a_binds_tvar ?α0 _ |- _ =>
      destruct (α0 == β) as [-> | Hne];
        [ apply ad_ppre__var; [ assumption | left; exact HβΔ ] | ];
      apply ad_ppre__var; [ assumption | ];
      destruct Hor as [HΔ | Hb]; [ left; exact HΔ | right ];
      eapply a_binds_tvar_strip_mid;
        [ exact Hb | intro Hc; congruence | intro Hc; congruence
        | intros τ0 Hc; congruence ]
    end.
  - eapply ad_ppre__arrow;
      [ eapply IHad_partial_precise1 | eapply IHad_partial_precise2 | ];
      solve [ reflexivity | assumption ].
  - eapply ad_ppre__forall with (L := L `union` singleton β); [ | eassumption ].
    intros α0 Hα0.
    eapply H0;
      [ clear - Hα0; fsetdec | reflexivity | exact Hd1 | exact Hd2
      | clear - HβΔ; fsetdec ].
  - apply ad_ppre__hole; assumption.
  - apply ad_ppre__tophole_remove;
      eapply IHad_partial_precise; solve [ reflexivity | assumption ].
  - eapply ad_ppre__tophole_fill
      with (L := L `union` singleton β `union` dom Θ1 `union` dom Θ2).
    intros α0 Hα0.
    eapply (H0 α0 ltac:(clear - Hα0; fsetdec) β ((α0 ~ abind_tvar) ++ Θ1) Θ2);
      [ reflexivity
      | simpl; clear - Hα0 Hd1; solve_notin
      | exact Hd2 | exact HβΔ ].
  - apply ad_ppre__tophole_keep;
      eapply IHad_partial_precise; solve [ reflexivity | assumption ].
  - (* flex_l / flex_r : β is bound as a RIGID, so a defined variable of the
       context is never β (the context has no second β entry) *)
    match goal with Hb : binds ?α0 (abind_flex_mono_def ?τ0) _ |- _ =>
      assert (Hαβ : α0 <> β) by
        (intro Heqα; subst α0;
         destruct (binds_app_1 _ _ _ _ _ Hb) as [Hb1 | Hb2];
           [ apply Hd1; eapply binds_In; exact Hb1
           | destruct (binds_cons_1 _ _ _ _ _ _ Hb2) as [[_ Habs] | Hb3];
               [ discriminate Habs | apply Hd2; eapply binds_In; exact Hb3 ] ])
    end.
    eapply ad_ppre__flex_l;
      [ eapply binds_strengthen_mid;
          [ eassumption | simpl; clear - Hαβ; fsetdec ]
      | eapply IHad_partial_precise; solve [ reflexivity | assumption ] ].
  - match goal with Hb : binds ?α0 (abind_flex_mono_def ?τ0) _ |- _ =>
      assert (Hαβ : α0 <> β) by
        (intro Heqα; subst α0;
         destruct (binds_app_1 _ _ _ _ _ Hb) as [Hb1 | Hb2];
           [ apply Hd1; eapply binds_In; exact Hb1
           | destruct (binds_cons_1 _ _ _ _ _ _ Hb2) as [[_ Habs] | Hb3];
               [ discriminate Habs | apply Hd2; eapply binds_In; exact Hb3 ] ])
    end.
    eapply ad_ppre__flex_r;
      [ eapply binds_strengthen_mid;
          [ eassumption | simpl; clear - Hαβ; fsetdec ]
      | eapply IHad_partial_precise; solve [ reflexivity | assumption ] ].
Qed.

(** The ∀^ε analogue of [ad_ppre_guarded_topholeg_absurd]: no GUARDED input
    skeleton is partially precise to a tagged quantifier.  The variable row
    is the only live one, and there the κ-image is a MONOTYPE, whose target
    must therefore be tag-free — while a tagged ∀ carries ε. *)
Lemma ad_ppre_guarded_all_etag_absurd : forall Θ0 Θ κ Δ Ψ Ψd P ε ψ,
  a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  guarded_pskl P ->
  d_tags_skl Ψd (uskl_all_etag ε ψ) ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ P) ⊑ᵖ[ Ψ ] (uskl_all_etag ε ψ) ->
  False.
Proof.
  intros Θ0 Θ κ Δ Ψ Ψd P ε ψ HwfΘ Hκ Hg Hd Hpre.
  destruct Hg as [ | α | P1 P2 Hlc1 Hlc2 ]; cbn [msubst_pskl] in Hpre.
  - inversion Hpre.
  - assert (HΨde : Ψd [=] empty)
      by (eapply ad_ppre_mono_subject_target_tags_empty;
            [ exact HwfΘ | exact Hpre | reflexivity
            | eapply a_inc_lookup_mono; exact Hκ | exact Hd ]).
    destruct (d_tags_skl_all_etag_inv Hd) as (Ld & Ψ0 & _ & _ & Heq).
    assert (Hin : ε `in` empty) by (clear - HΨde Heq; fsetdec).
    clear - Hin; fsetdec.
  - inversion Hpre.
Qed.

(** The Arrow case's Pi GRID.  Everything about the two branches is packed
    into the [KEY] hypothesis (the left premise's P6-Cv call and the right
    one's induction hypothesis), so this is purely the case analysis on the
    input skeleton: arrow / □ / ∀◇ / a variable, with unit and ∀ refuted by
    the precision against an arrow guess.  The ∀◇ row recurses STRUCTURALLY
    on Pi — no measure needed, since well-formedness makes the ghost's body
    guarded. *)
Lemma arrow_grid : forall NM M Θ0 Θ κ Δ Δρ Ψt Ψi Ψa ψ1 ψ2 Pi P01 P02,
  a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  a_tags_sort NM Ψt (uskl_arrow ψ1 ψ2) ->
  Ψi `union` Ψa [=] Ψt ->
  (forall Pi1 Pi2 Ψi1 Ψi2,
     Θ0 ⨟ empty ⊢ₚₛᵃ Pi1 -> Θ0 ⨟ empty ⊢ₚₛᵃ Pi2 ->
     (forall α, α `in` Δρ ->
        α `notin` pskl_shielded_ftv (msubst_pskl κ Pi1)) ->
     (forall α, α `in` Δρ ->
        α `notin` pskl_shielded_ftv (msubst_pskl κ Pi2)) ->
     Ψi [=] Ψi1 `union` Ψi2 ->
     Θ ⨟ Δ ⊢ (msubst_pskl κ Pi1) ⊑ᵖ[ Ψi1 ] ψ1 ->
     Θ ⨟ Δ ⊢ (msubst_pskl κ Pi2) ⊑ᵖ[ Ψi2 ] ψ2 ->
     exists Pa1 Pa2,
       Θ0 ⊢ₑ Pi1 ∼ P01 ⤳ Pa1 /\
       Θ0 ⊢ₛ Pi2 ≼[ M ] P02 ⤳ Pa2 /\
       Θ ⨟ Δ ⊢ (msubst_pskl κ (pskl_arrow Pa1 Pa2))
         ⊑ᵖ[ Ψi `union` Ψa ] (uskl_arrow ψ1 ψ2)) ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_arrow ψ1 ψ2) ->
  exists Pa, Θ0 ⊢ₛ Pi ≼[ mode_fn M ] (pskl_arrow P01 P02) ⤳ Pa /\
    Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] (uskl_arrow ψ1 ψ2).
Proof.
  intros NM M Θ0 Θ κ Δ Δρ Ψt Ψi Ψa ψ1 ψ2 Pi P01 P02
         HwfΘ Hκ Htags Htageq KEY.
  revert Ψi Ψa Htageq KEY.
  induction Pi as [ | nPi | β | Pi1 IH1 Pi2 IH2 | Pi0 IH0 | | Pi0 IH0 ];
    intros Ψi Ψa Htageq KEY HwfPi Hshield Hpre;
    cbn [msubst_pskl] in Hpre.
  - (* ⟨⟩ : no rule targets an arrow from unit *) inversion Hpre.
  - (* a bound variable is not well-formed *) inversion HwfPi.
  - (* a variable : SolS-Var keeps it, and a MONOTYPE κ-image forces the
       guess to be tag-free, so there is nothing left to solve *)
    assert (Hml : mono_ptyp (msubst_lookup κ β))
      by (eapply a_inc_lookup_mono; exact Hκ).
    assert (HΨte : Ψt [=] empty)
      by (eapply ad_ppre_mono_subject_target_tags_empty;
            [ exact HwfΘ | exact Hpre | reflexivity | exact Hml
            | exact (a_tags_sort_d_tags Htags) ]).
    exists (pskl_var_f β); split;
      [ apply a_solve_sub__var
      | cbn [msubst_pskl];
        eapply ad_partial_precise_psi_cong;
          [ exact Hpre | clear - Htageq HΨte; fsetdec ] ].
  - (* an arrow : both components recurse through KEY *)
    inversion Hpre; subst.
    match goal with
      Hp1 : _ ⨟ _ ⊢ msubst_pskl κ Pi1 ⊑ᵖ[ ?Ψa1 ] ψ1,
      Hp2 : _ ⨟ _ ⊢ msubst_pskl κ Pi2 ⊑ᵖ[ ?Ψa2 ] ψ2,
      Hun : Ψi [=] _ |- _ =>
      destruct (KEY Pi1 Pi2 Ψa1 Ψa2
                  ltac:(inversion HwfPi; assumption)
                  ltac:(inversion HwfPi; assumption)
                  ltac:(intros α0 Hα0; pose proof (Hshield α0 Hα0) as Hs;
                        cbn [msubst_pskl pskl_shielded_ftv] in Hs;
                        clear - Hs; fsetdec)
                  ltac:(intros α0 Hα0; pose proof (Hshield α0 Hα0) as Hs;
                        cbn [msubst_pskl pskl_shielded_ftv] in Hs;
                        clear - Hs; fsetdec)
                  Hun Hp1 Hp2)
        as (Pa1 & Pa2 & Hs1 & Hs2 & Hp)
    end.
    exists (pskl_arrow Pa1 Pa2); split;
      [ apply a_solve_sub__arrow; [ exact Hs1 | exact Hs2 ] | exact Hp ].
  - (* ∀ : no rule targets an arrow from a quantifier *) inversion Hpre.
  - (* □ : SolS-GhostLF, with both branches run at input □ *)
    inversion Hpre; subst.
    match goal with Hd : Δ ∩ ftvar_in_uskl (uskl_arrow ψ1 ψ2) [=] empty,
                    He : Ψi [=] empty |- _ =>
      destruct (KEY pskl_hole pskl_hole empty empty
                  (a_wf_pskl__hole Θ0 empty) (a_wf_pskl__hole Θ0 empty)
                  ltac:(intros α0 Hα0; cbn; clear; fsetdec)
                  ltac:(intros α0 Hα0; cbn; clear; fsetdec)
                  ltac:(clear - He; fsetdec)
                  ltac:(cbn [msubst_pskl]; apply ad_ppre__hole;
                        [ clear; fsetdec
                        | cbn [ftvar_in_uskl] in Hd; clear - Hd; fsetdec ])
                  ltac:(cbn [msubst_pskl]; apply ad_ppre__hole;
                        [ clear; fsetdec
                        | cbn [ftvar_in_uskl] in Hd; clear - Hd; fsetdec ]))
        as (Pa1 & Pa2 & Hs1 & Hs2 & Hp)
    end.
    exists (pskl_tophole (pskl_arrow Pa1 Pa2)); split;
      [ apply a_solve_sub__ghost_l_fn; [ exact Hs1 | exact Hs2 ]
      | cbn [msubst_pskl] in Hp |- *; apply ad_ppre__tophole_remove; exact Hp ].
  - (* ∀◇Pi0 : strip the ghost (the FILL and KEEP rows need a ∀^ε / ∀◈
       guess), recurse, and wrap the output *)
    inversion Hpre; subst.
    match goal with Hbody : _ ⨟ _ ⊢ msubst_pskl κ Pi0 ⊑ᵖ[ Ψi ] _ |- _ =>
      destruct (IH0 Ψi Ψa Htageq KEY
                  ltac:(eapply a_wf_pskl_tophole_inv; exact HwfPi)
                  ltac:(intros α0 Hα0; pose proof (Hshield α0 Hα0) as Hs;
                        cbn [msubst_pskl pskl_shielded_ftv] in Hs;
                        pose proof (pskl_shielded_ftv_sub_ftv
                                      (msubst_pskl κ Pi0)) as Hle;
                        clear - Hs Hle; fsetdec)
                  Hbody)
        as (Pa & Hs & Hp)
    end.
    exists (pskl_tophole Pa); split;
      [ apply a_solve_sub__univ_ghost_l; exact Hs
      | cbn [msubst_pskl]; apply ad_ppre__tophole_remove; exact Hp ].
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
                                   / ∀◇ with SolS-Check / GhostL / UnivGhostL
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
  forall n NM M Θ0 Θs Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  κ ∷ Θ0 ⊑ Θ ->
  uskl_rho NM Θ Δρ Ψρ ψsub ψa ->                    (* ψsub = ρ(ψa) *)
  a_tags_sort NM Ψ' ψa ->
  Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψsub ⌋ˢ ->                       (* subject wf (P6-Cs) *)
  Ψi `union` Ψa [=] Ψ' ->                           (* the paper's Ψi,Ψa = Ψ' *)
  Ψρ ∩ Ψ' [=] empty ->                              (* the paper's fresh{Ψ'} *)
  rho_fresh Δρ Θ κ -> Δρ [<=] Δ ->
  (forall α, α `in` Δρ ->
     α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->
  flex_apart_walk Θ0 Δρ P0 ψa ->    (* P6-Cv's invariant, ALONG THE WALK *)
  flex_shield Θ0 Ψ' Δρ P0 ψa ->                     (* ⇐ THE REPAIR *)
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
  Ψsub [<=] Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  (* the derivation lives in a SMALLER context [Θs]: Sub-ForallL must run
     the IH at [Θ,β] while the derivation's own context is an index and
     cannot move, so the context the rest of the premises talk about is
     generalized and only related to [Θs] by [binds]-monotonicity.  This is
     the mech's reading of the paper's "by weakening \refn[9] to Θ,β"
     (subtyping-proofs.tex:2153); at the top level [Θs = Θ]. *)
  (forall x b, binds x b Θs -> binds x b Θ) ->
  ad_pat_sub_g n NM M Ψsub Θs ψsub Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  exists Pa, Θ0 ⊢ₛ Pi ≼[ M ] P0 ⤳ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  intros n NM M Θ0 Θs Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HwfΘ HwfΘ0 HwfPi HwfP0 HmodSK HmodTY Hκ Hrho Htags HwfSub
         Htageq Hinter Hrhof Hdelta Hshield Hdfresh Hapart Hfsh Hpre
         HΨs1 HΨs2 Hext Hsub Hrefine.
  (* everything except the derivation is generalized: ForallR/ForallL both
     extend Θ0 and Θ, ForallL grows Δρ/Δ and rewrites the tag split, and
     Arrow splits P0/Pi/ψa — so no premise may stay fixed *)
  revert Θ Θ0 κ Δ Δρ Ψρ Ψ' Ψi Ψa ψa Pi P0
         HwfΘ HwfΘ0 HwfPi HwfP0 HmodSK HmodTY Hκ Hrho Htags HwfSub
         Htageq Hinter Hrhof Hdelta Hshield Hdfresh Hapart Hfsh Hpre
         HΨs1 HΨs2 Hext Hrefine.
  (* the lemma's [Ψ'] is re-introduced as [Ψt]: [Ψ'] is a BINDER NAME of
     the ForallL rules, so [induction] has already claimed it *)
  induction Hsub; intros
    Θe Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa ψa Pi P0
    HwfΘ HwfΘ0 HwfPi HwfP0 HmodSK HmodTY Hκ Hrho Htags HwfSub
    Htageq Hinter Hrhof Hdelta Hshield Hdfresh Hapart Hfsh Hpre
    HΨs1 HΨs2 Hext Hrefine;
    (* the derivation's own context is the rule binder [Θ]; the generalized
       one comes back in as [Θe].  Renaming it back keeps every closed case
       textually unchanged: each rule premise that mentions the SMALL
       context is weakened on the spot. *)
    rename Θ into Θsm; rename Θe into Θ.
  (* each rule premise stated in the SMALL context is weakened on the spot,
     so every closed case below reads exactly as before *)
  all: match goal with
       | Hx : forall x b, binds x b ?S -> binds x b _ |- _ =>
         repeat match goal with
         | H : _ ⨟ S ⊢ₛᵃ _ ∼ _ |- _ =>
             let H' := fresh "Hw" in
             pose proof (ad_pat_consis_weaken H _ Hx) as H';
             clear H; rename H' into H
         | H : S ⨟ _ ⊢ₚₛᵃ _ |- _ =>
             let H' := fresh "Hw" in
             pose proof (a_wf_pskl_weaken Hx H) as H';
             clear H; rename H' into H
         | H : binds _ _ S |- _ => apply Hx in H
         end
       end.
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
  - (* Check (TY/TC).  The premise IS a consistency judgment, so P6-Cv
       ([a_solve_eq_complete_var]) applies verbatim — every premise of this
       lemma is one of its premises, with [flex_apart] read off the walk.
       It returns the EQUALITY solve; SolS-Check then lifts it, after a
       case analysis on Pi.  P0 is GUARDED here: [skmod{TY}] makes it a
       type, and a ∀ is excluded because a [bskl_all_inh] target cannot be
       the inherited painting of a GUARDED B. *)
    assert (HgP0 : guarded_pskl P0).
    { pose proof (HmodTY eq_refl) as Hmod.
      inversion Hmod as [ | A HeqA | ]; subst.
      destruct A as [ | nA | αA | A1 A2 | A0 ]; cbn [ptyp_to_pskl] in *.
      - apply guarded_pskl__unit.
      - inversion HwfP0.
      - apply guarded_pskl__var.
      - pose proof (a_wf_pskl_lc HwfP0) as Hlc; inversion Hlc; subst.
        apply guarded_pskl__arrow; assumption.
      - (* ∀ : its inherited painting is a [bskl_all_inh], and the target is
           the inherited painting of a GUARDED B — which is never one *)
        exfalso.
        assert (HgQ : guarded_bskl (pskl_to_bskl_inh B))
          by (apply guarded_pskl_to_bskl_inh; exact H0).
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        (* [inversion] leaves the target as an EQUATION against
           [pskl_to_bskl_inh B]; expose B's shape first *)
        destruct B; cbn [pskl_to_bskl_inh] in Hrefine, HgQ;
          try solve [ inversion HgQ ];
          inversion Hrefine; subst;
          solve [ (* an inherited ∀ never refines to a monotype paint *)
                  eapply ad_refine_allinh_lhs_mono_absurd;
                    [ exact HwfΘ | eassumption | reflexivity | reflexivity
                    | eapply a_wf_aenv_binds_def_mono;
                        [ exact HwfΘ | eassumption ] ] ]. }
    (* the subject is the RULE's [T] here, not the statement's ψsub *)
    destruct (@a_solve_eq_complete_var a_sub_mode_ty Θ0 Θ κ Δ Δρ Ψρ Ψt Ψi Ψa
                Ψ T ψa (pskl_to_bskl_inh B) Pi P0
                HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hrho Htags
                ltac:(clear - Htageq; fsetdec) Hinter Hrhof Hdelta Hshield
                Hdfresh (flex_apart_walk_here Hapart) Hpre HΨs1 HΨs2 H1
                Hrefine)
      as (Pa & Hs & Hp).
    (* now lift the equality solve to a subtyping one, by Pi's shape *)
    destruct Pi as [ | nPi | β | Pi1 Pi2 | Pi' | | Pi' ].
    + (* ⟨⟩ : guarded *)
      exists Pa; split;
        [ apply a_solve_sub__check;
            [ apply guarded_pskl__unit | exact HgP0 | exact Hs ]
        | exact Hp ].
    + inversion HwfPi.
    + (* a variable : guarded *)
      exists Pa; split;
        [ apply a_solve_sub__check;
            [ apply guarded_pskl__var | exact HgP0 | exact Hs ]
        | exact Hp ].
    + (* an arrow : guarded *)
      assert (Hg : guarded_pskl (pskl_arrow Pi1 Pi2)).
      { pose proof (a_wf_pskl_lc HwfPi) as Hlc; inversion Hlc; subst.
        apply guarded_pskl__arrow; assumption. }
      exists Pa; split;
        [ apply a_solve_sub__check; [ exact Hg | exact HgP0 | exact Hs ]
        | exact Hp ].
    + (* ∀ : IMPOSSIBLE — precision forces a ∀-shaped GUESS, and ρ maps a ∀
         to a ∀ (or to a variable at a leaf), never to the GUARDED subject
         this rule requires *)
      exfalso.
      cbn [msubst_pskl] in Hpre.
      inversion Hpre; subst.
      * (* P-Forall : the guess is a ∀^ε, so ρ makes the subject one too *)
        inversion Hrho; subst;
          match goal with Hg : guarded_uskl _ |- _ => inversion Hg end.
      * (* P-FlexR : the guess is a defined flexible; unfolding it leaves a
           ∀ subject against a MONOTYPE painting *)
        eapply ad_ppre_allsyn_subject_mono_absurd;
          [ exact HwfΘ | eassumption | reflexivity | reflexivity
          | eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ] ].
    + (* □ : SolS-GhostL wraps P0, and inversion on the equality solve gives
         Pa = P0 *)
      assert (HeqPa : Pa = P0)
        by (eapply a_solve_eq_hole_subject_inv; exact Hs).
      subst Pa.
      exists (pskl_tophole P0); split;
        [ apply a_solve_sub__ghost_l; exact HgP0
        | cbn [msubst_pskl]; apply ad_ppre__tophole_remove; exact Hp ].
    + (* ∀◇Pi' : strip the ghost, solve the body, wrap the output.  This is
         where the paper says "by congruence of constraint solving, we
         ASSUME refb is derived by SolEq-GhostGuarded"
         (subtyping-proofs.tex:1810) — the WLOG that hazard H3 predicted.
         Mechanically both derivations must be handled, because P6-Cv
         returns whichever it built. *)
      assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
      assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi')
        by (eapply a_wf_pskl_tophole_inv; exact HwfPi).
      cbn [msubst_pskl] in Hp.
      (* the payload is GUARDED, which kills the □-, ∀◇- and ∀-payload rows;
         [SolEq-FlexR] and [SolEq-GhostGuarded] remain, in that order *)
      inversion Hs; subst; try solve [ inversion HgP0 ].
      * (* SolEq-FlexR : the payload is a flexible and survives whole.  If
           the ∀◇-body is NOT itself a flexible variable, the same rule
           applies one level down and the output is unchanged. *)
        match goal with
          Hflx : a_flex_tvar Θ0 ?α0 |- _ =>
          destruct (a_non_flex_guarded_dec Θ0 HgPi') as [Hnf' | Hf'];
          [ exists (pskl_tophole (pskl_var_f α0)); split;
              [ apply a_solve_sub__univ_ghost_l;
                apply a_solve_sub__check;
                  [ exact HgPi' | exact HgP0
                  | apply a_solve_eq__flex_r; [ exact Hflx | exact Hnf' ] ]
              | cbn [msubst_pskl]; apply ad_ppre__tophole_remove; exact Hp ]
          | ]
        end.
        (* the ∀◇-body IS a flexible: SolEq-Var keeps IT instead, so the
           output is [∀◇Pi'] and its precision is the INPUT premise itself
           — which needs Ψa = ∅.  That holds by the flexible-payload
           argument, exactly as in P6-Cv's own FLEX row: κP0 is a MONOTYPE,
           so the refinement makes Q mono-ish and the consistency then
           solves no tag at all. *)
        destruct Hf' as (α' & -> & Hflx').
        assert (Hml : mono_ptyp (msubst_lookup κ α))
          by (eapply a_inc_lookup_mono; exact Hκ).
        assert (HΨe : Ψ [=] empty).
        { cbn [msubst_pskl] in Hrefine.
          rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
          assert (Hmi : bskl_monoish (pskl_to_bskl_inh B))
            by (eapply ad_refine_mono_paint_rhs_monoish;
                  [ exact HwfΘ | exact Hrefine | reflexivity | exact Hml ]).
          assert (Hts : is_tskl T)
            by (eapply uskl_rho_is_tskl;
                  [ exact Hrho | inversion Htags; assumption ]).
          destruct (ad_pat_consis_monoish_counterpart H1 HwfΘ Hts Hmi)
            as (HΨ0 & _); exact HΨ0. }
        assert (HΨae : Ψa [=] empty) by (clear - HΨs2 HΨe; fsetdec).
        exists (pskl_tophole (pskl_var_f α')); split.
        -- apply a_solve_sub__univ_ghost_l.
           apply a_solve_sub__check;
             [ apply guarded_pskl__var | exact HgP0 | apply a_solve_eq__var ].
        -- eapply ad_partial_precise_psi_cong;
             [ exact Hpre | clear - HΨae; fsetdec ].
      * (* SolEq-GhostGuarded : the body's equality solve lifts directly *)
        match goal with Hbody : Θ0 ⊢ₑ Pi' ∼ _ ⤳ ?Pb |- _ =>
          exists (pskl_tophole Pb); split;
            [ apply a_solve_sub__univ_ghost_l;
              apply a_solve_sub__check;
                [ exact HgPi' | exact HgP0 | exact Hbody ]
            | cbn [msubst_pskl]; apply ad_ppre__tophole_remove; exact Hp ]
        end.
  - (* ForallR (TY/TC).  [skmod{TY}] makes P0 a TYPE, so the refinement's
       inherited-∀ target forces P0 = ∀.P0' (every other type shape is
       GUARDED, and a guarded source refines only to a guarded target).
       Then descend the payload — the guess is untouched — and strip the
       binder from the outputs with P6-Cs's ∀-kit. *)
    pose proof (HmodTY eq_refl) as Hmod.
    inversion Hmod as [ | A HeqA | ]; subst.
    destruct A as [ | nA | αA | A1 A2 | A0 ];
      cbn [ptyp_to_pskl] in HwfP0, Hrefine, Hshield, Hpre, Hfsh, Hapart |- *.
    + (* ⟨⟩ : guarded *)
      exfalso;
        assert (Hbad : guarded_bskl (bskl_all_inh B));
        [ eapply ad_refine_syn_guarded_r;
            [ exact HwfΘ | exact Hrefine
            | apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc;
                [ exact Hκ | apply guarded_pskl__unit ] ]
        | inversion Hbad ].
    + (* a bound variable is not well-formed *) inversion HwfP0.
    + (* a variable : guarded *)
      exfalso;
        assert (Hbad : guarded_bskl (bskl_all_inh B));
        [ eapply ad_refine_syn_guarded_r;
            [ exact HwfΘ | exact Hrefine
            | apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc;
                [ exact Hκ | apply guarded_pskl__var ] ]
        | inversion Hbad ].
    + (* an arrow : guarded *)
      exfalso.
      assert (Hg : guarded_pskl (pskl_arrow (ptyp_to_pskl A1) (ptyp_to_pskl A2))).
      { pose proof (a_wf_pskl_lc HwfP0) as Hlc; inversion Hlc; subst.
        apply guarded_pskl__arrow; assumption. }
      assert (Hbad : guarded_bskl (bskl_all_inh B));
        [ eapply ad_refine_syn_guarded_r;
            [ exact HwfΘ | exact Hrefine
            | apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact Hg ] ]
        | inversion Hbad ].
    + (* P0 = ∀.P0' : the real row *)
      cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
      inversion Hrefine; subst.
      match goal with Hr : forall α, α `notin` ?Lr -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ _ |- _ =>
        rename Hr into Hrbody; remember Lr as Lr0 eqn:HeqLr; clear HeqLr end.
      inversion HwfP0; subst.
      match goal with Hw : forall α, α `notin` ?Lw -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
        rename Hw into Hw0body; remember Lw as Lw0 eqn:HeqLw; clear HeqLw end.
      pick fresh β for
        (L `union` Lr0 `union` Lw0 `union` dom Θ `union` dom Θ0
           `union` dom κ `union` ftvar_in_uskl ψa `union` ftvar_in_pskl Pi
           `union` ftvar_in_pskl (ptyp_to_pskl A0) `union` def_ftv Θ
           `union` Δ).
      assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
      assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
      assert (Hβψa : β `notin` ftvar_in_uskl ψa) by (clear - Fr; solve_notin).
      assert (Hwfβ : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
        by (apply a_wf_aenv__tvar; assumption).
      assert (Hwfβ0 : a_wf_aenv ((β ~ abind_tvar) ++ Θ0))
        by (apply a_wf_aenv__tvar; assumption).
      assert (Hweak : forall (x : atom) (b : abind),
                binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
        by (intros x b Hb; apply binds_app_3; exact Hb).
      assert (HwfP0β : ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                ⊢ₚₛᵃ (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β))).
      { eapply a_wf_pskl_delta_to_tvar_mid
          with (α1 := β) (Θ1 := nil) (Θ2 := Θ0) (Δ' := empty);
          [ apply (Hw0body β ltac:(clear - Fr; solve_notin))
          | reflexivity | clear; fsetdec ]. }
      assert (HwfPiβ : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi)
        by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfPi ]).
      assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
        by (apply a_inc_cons_tvar; exact Hκ).
      assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ)).
      { intros β0 α0 τ0 Hβ0 Hb. eapply Hdfresh; [ exact Hβ0 | ].
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
          [ discriminate Habs | exact Hb' ]. }
      assert (Hrhofβ : rho_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ).
      { intros α0 Hα0. destruct (Hrhof α0 Hα0) as (Hb & Him & Hdf).
        repeat split;
          [ apply binds_app_3; exact Hb | exact Him | ].
        intros α1 τ1 Hb1. eapply Hdf.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[_ Habs] | Hb'];
          [ discriminate Habs | exact Hb' ]. }
      assert (Hpreβ : ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa)
        by (eapply ad_partial_precise_weaken;
              [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
      assert (Hrefβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                (pskl_to_bskl_inh
                   (msubst_pskl κ (open_pskl_wrt_pskl (ptyp_to_pskl A0)
                                     (pskl_var_f β))))
                ⊳ (open_bskl_wrt_bskl B (bskl_var_f β))).
      { rewrite (@msubst_pskl_open Θ0 κ Θ (ptyp_to_pskl A0) β Hκ Hβκ).
        rewrite pskl_to_bskl_inh_open.
        eapply ad_refine_syn_delta_to_tvar_mid
          with (α1 := β) (Θ1 := nil) (Θ2 := Θ) (Δ' := empty);
          [ apply (Hrbody β ltac:(clear - Fr; solve_notin))
          | reflexivity | clear; fsetdec ]. }
      edestruct (H0 β ltac:(clear - Fr; solve_notin)
                   ((β ~ abind_tvar) ++ Θ)
                   ((β ~ abind_tvar) ++ Θ0) κ Δ Δρ Ψρ Ψt Ψi Ψa ψa Pi
                   (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β))
                   Hwfβ Hwfβ0 HwfPiβ HwfP0β
                   ltac:(intro Hc; discriminate Hc)
                   ltac:(intros _;
                         rewrite <- ptyp_to_pskl_open;
                         apply a_ty_mode_compat__tc)
                   Hκβ
                   ltac:(eapply uskl_rho_weaken;
                         [ exact Hrho
                         | intros x b Hb; apply binds_app_3; exact Hb ])
                   Htags
                   ltac:(eapply a_wf_pskl_weaken;
                         [ intros x b Hb; apply binds_app_3; exact Hb
                         | exact HwfSub ])
                   Htageq Hinter Hrhofβ Hdelta Hshield Hdfreshβ
                   ltac:(apply flex_apart_walk_weaken_tvar;
                         eapply flex_apart_walk_step;
                           [ exact Hapart | apply fastep_all_l; clear - Fr; solve_notin ])
                   ltac:(eapply flex_shield_descend_l;
                         [ exact Hfsh | exact HβΘ0 ])
                   Hpreβ HΨs1 HΨs2
                   ltac:(intros x b Hb;
                         unfold binds in Hb |- *; simpl in Hb |- *;
                         destruct Hb as [Heqb | Hb'];
                           [ left; exact Heqb | right; apply Hext; exact Hb' ])
                   Hrefβ)
        as (Pa & Hs & Hp).
      (* --- strip β from the two outputs --- *)
      (* β is not free in the output: the solve's variables come from its two
         inputs, and β is fresh for Pi — while for the opened payload the
         PRECISION conclusion is what excludes it (see below), so we read
         the bound off the precision instead of the solve. *)
      (* β is not free in the output — read off the PRECISION conclusion, as
         the paper does (subtyping-proofs.tex:1898): its subject's variables
         come from the guess (β-free by choice), from Δ (β is fresh) or from
         Θ (β is not there); and β is not in κ's domain, so it cannot have
         been introduced by the metasubstitution either *)
      assert (HβPa : β `notin` ftvar_in_pskl Pa).
      { assert (HβΔ : β `notin` Δ) by (clear - Fr; solve_notin).
        assert (Hβdef : β `notin` def_ftv Θ) by (clear - Fr; solve_notin).
        assert (Hsrc : β `notin` ftvar_in_pskl (msubst_pskl κ Pa)).
        { eapply ad_partial_precise_src_ftv_avoid;
            [ exact Hp | exact Hβψa | exact HβΔ
            | (* β is bound as a rigid tvar, never as a definition *)
              intros τ0 Hb;
              destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                [ discriminate Habs
                | apply HβΘ; eapply binds_In; exact Hb' ]
            | cbn [def_ftv]; exact Hβdef ]. }
        pose proof (msubst_pskl_ftv_dom_lower κ Pa) as Hlo.
        clear - Hsrc Hlo Hβκ; fsetdec. }
      assert (HsΘ0 : Θ0 ⊢ₛ Pi
                ≼[ mode_tc ] (open_pskl_wrt_pskl (ptyp_to_pskl A0)
                                (pskl_var_f β)) ⤳ Pa)
        by (eapply a_solve_sub_strengthen_tvar; exact Hs).
      exists Pa; split.
      * (* rebuild SolS-ForallR: the single instance at β becomes the
           cofinite family by RIGID RENAMING (β is free in neither Pi nor
           the output, so only the payload moves) *)
        apply a_solve_sub__forall_r
          with (L := dom Θ0 `union` singleton β `union` ftvar_in_pskl Pi
                       `union` ftvar_in_pskl Pa
                       `union` ftvar_in_pskl (ptyp_to_pskl A0)).
        intros α Hα.
        assert (HβΘ0' : β `notin` dom Θ0) by exact HβΘ0.
        assert (HαΘ0 : α `notin` dom Θ0) by (clear - Hα; fsetdec).
        pose proof ((proj1 a_solve_sub_eq_rename) _ _ _ _ _ HsΘ0 β α
                      HβΘ0' HαΘ0) as Hren.
        rewrite (@subst_pskl_in_pskl_fresh_eq Pi (pskl_var_f α) β)
          in Hren; [ | clear - Fr; solve_notin ].
        rewrite (@subst_pskl_in_pskl_fresh_eq Pa (pskl_var_f α) β)
          in Hren; [ | exact HβPa ].
        rewrite <- (@subst_pskl_in_pskl_intro β (ptyp_to_pskl A0)
                      (pskl_var_f α)) in Hren;
          [ | clear - Fr; solve_notin ].
        exact Hren.
      * eapply ad_partial_precise_strip_tvar_mid
          with (β := β) (Θ1 := nil) (Θ2 := Θ);
          [ exact Hp | reflexivity
          | intros α0 τ0 Hb;
            assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
              by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                    [ discriminate Habs | exact Hb' ]);
            pose proof (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb') as Hwfτ;
            pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hftd;
            clear - Hftd HβΘ; fsetdec
          | apply msubst_pskl_ftv_avoid;
              [ intros pp Hpp;
                pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
                clear - Hb HβΘ; fsetdec
              | exact HβPa ]
          | exact Hβψa ].
  - (* UnivGhostR (SK) : M = TC at sort SK, so [skmod] again forces P0 = □
       and the case closes exactly like Infer *)
    assert (HP0 : P0 = pskl_hole)
      by (pose proof (HmodSK eq_refl) as Hm; inversion Hm; reflexivity).
    subst P0.
    exists Pi; split; [ apply a_solve_sub__vacuous | ].
    eapply ad_partial_precise_psi_cong; [ exact Hpre | ].
    assert (HΨae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
    clear - HΨae; fsetdec.
  - (* Arrow.  [skmod] forces P0 = P01→P02, the refinement splits, and the
       ρ-relation splits (or is a leaf).  The LEFT premise is a consistency
       judgment and goes to P6-Cv exactly as in Check; the RIGHT one is the
       IH.  Tags split by [arrow_tag_split]; the per-branch flow facts are
       P6-Cv's own arrow recipe ([ad_pat_sub_g_ftag_sub] /
       [ad_pat_consis_ftag_sub] + [uskl_rho_ftag_sub] + [d_tags_skl_ftag]). *)
    match goal with Hc : _ ⨟ Θ ⊢ₛᵃ R1 ∼ Q1 |- _ => rename Hc into Hcons end.
    match goal with Hu : Ψ [=] _ `union` _ |- _ => rename Hu into Hun end.
    assert (HP0 : exists P01 P02, P0 = pskl_arrow P01 P02 /\
                    (NM = a_sub_mode_sk -> a_sk_mode_compat M P02) /\
                    (NM = a_sub_mode_ty -> a_ty_mode_compat M P02)).
    { destruct NM.
      - pose proof (HmodTY eq_refl) as Hm; inversion Hm; subst.
        match goal with Hc : a_ty_mode_compat M ?Q0 |- _ =>
          exists P, Q0; repeat split;
            [ intro Hd; discriminate Hd | intros _; exact Hc ] end.
      - pose proof (HmodSK eq_refl) as Hm; inversion Hm; subst.
        match goal with Hc : a_sk_mode_compat M ?Q0 |- _ =>
          exists P, Q0; repeat split;
            [ intros _; exact Hc | intro Hd; discriminate Hd ] end. }
    destruct HP0 as (P01 & P02 & -> & HmodSK2 & HmodTY2).
    assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01) by (inversion HwfP0; assumption).
    assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02) by (inversion HwfP0; assumption).
    cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
    inversion Hrefine; subst.
    match goal with
      Hr1 : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P01) ⊳ _,
      Hr2 : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P02) ⊳ _ |- _ =>
      rename Hr1 into Href1; rename Hr2 into Href2
    end.
    (* the two branches, once the guess is known to be an arrow *)
    assert (KEY : forall ψ1 ψ2 Ψρ1 Ψρ2,
      uskl_rho NM Θ Δρ Ψρ1 R1 ψ1 ->
      uskl_rho NM Θ Δρ Ψρ2 R2 ψ2 ->
      Ψρ [=] Ψρ1 `union` Ψρ2 ->
      a_tags_sort NM Ψt (uskl_arrow ψ1 ψ2) ->
      flex_apart_walk Θ0 Δρ (pskl_arrow P01 P02) (uskl_arrow ψ1 ψ2) ->
      flex_shield Θ0 Ψt Δρ (pskl_arrow P01 P02) (uskl_arrow ψ1 ψ2) ->
      forall Pi1 Pi2 Ψi1 Ψi2,
      Θ0 ⨟ empty ⊢ₚₛᵃ Pi1 -> Θ0 ⨟ empty ⊢ₚₛᵃ Pi2 ->
      (forall α, α `in` Δρ ->
         α `notin` pskl_shielded_ftv (msubst_pskl κ Pi1)) ->
      (forall α, α `in` Δρ ->
         α `notin` pskl_shielded_ftv (msubst_pskl κ Pi2)) ->
      Ψi [=] Ψi1 `union` Ψi2 ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi1) ⊑ᵖ[ Ψi1 ] ψ1 ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi2) ⊑ᵖ[ Ψi2 ] ψ2 ->
      exists Pa1 Pa2,
        Θ0 ⊢ₑ Pi1 ∼ P01 ⤳ Pa1 /\
        Θ0 ⊢ₛ Pi2 ≼[ M ] P02 ⤳ Pa2 /\
        Θ ⨟ Δ ⊢ (msubst_pskl κ (pskl_arrow Pa1 Pa2))
          ⊑ᵖ[ Ψi `union` Ψa ] (uskl_arrow ψ1 ψ2)).
    { intros ψ1 ψ2 Ψρ1 Ψρ2 Hrho1 Hrho2 HΨρs Htags0 Hap0 Hfsh0
             Pi1 Pi2 Ψi1 Ψi2 HwfPi1 HwfPi2 Hsh1 Hsh2 HΨis Hpre1 Hpre2.
      destruct (a_tags_sort_arrow_inv Htags0)
        as (Ψt1 & Ψt2 & Htags1 & Htags2 & Htdisj & Htun).
      (* per-branch tag flow, exactly P6-Cv's arrow recipe *)
      assert (Hft1 : Ψ1 [<=] Ψρ1 `union` Ψt1).
      { pose proof (ad_pat_consis_ftag_sub Hcons) as Ha.
        pose proof (uskl_rho_ftag_sub Hrho1) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags1)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hft2 : Ψ2 [<=] Ψρ2 `union` Ψt2).
      { pose proof (ad_pat_sub_g_ftag_sub Hsub) as Ha.
        pose proof (uskl_rho_ftag_sub Hrho2) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags2)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hi1 : Ψi1 [<=] Ψt1)
        by (eapply ad_partial_precise_tags_sub;
              [ exact HwfΘ | exact Hpre1
              | exact (a_tags_sort_d_tags Htags1) ]).
      assert (Hi2 : Ψi2 [<=] Ψt2)
        by (eapply ad_partial_precise_tags_sub;
              [ exact HwfΘ | exact Hpre2
              | exact (a_tags_sort_d_tags Htags2) ]).
      destruct (arrow_tag_split Htun Htdisj HΨis Hi1 Hi2 Htageq)
        as (Hsp1 & Hsp2).
      (* LEFT: the consistency premise goes to P6-Cv *)
      destruct (@a_solve_eq_complete_var NM Θ0 Θ κ Δ Δρ Ψρ1 Ψt1 Ψi1
                  (Ψa ∩ Ψt1) Ψ1 R1 ψ1 Q1 Pi1 P01
                  HwfΘ HwfΘ0 HwfPi1 HwfP01 Hκ Hrho1 Htags1
                  ltac:(clear - Hsp1; fsetdec)
                  ltac:(clear - Hinter HΨρs Htun; fsetdec)
                  Hrhof Hdelta Hsh1 Hdfresh
                  (flex_apart_walk_here
                     (flex_apart_walk_step Hap0 (fastep_arrow_l _ _ _ _ _ _)))
                  Hpre1
                  ltac:(clear - Hft1 HΨs1 Hinter Htun Htdisj Hun HΨρs; fsetdec)
                  ltac:(clear - HΨs2 Hun Htun Hft2 Hinter HΨρs Htdisj; fsetdec)
                  Hcons Href1)
        as (Pa1 & Hs1 & Hp1).
      (* RIGHT: the subtyping premise goes to the IH *)
      destruct (IHHsub Θ Θ0 κ Δ Δρ Ψρ2 Ψt2 Ψi2 (Ψa ∩ Ψt2) ψ2 Pi2 P02
                  HwfΘ HwfΘ0 HwfPi2 HwfP02 HmodSK2 HmodTY2 Hκ Hrho2 Htags2
                  ltac:(inversion HwfSub; assumption)
                  ltac:(clear - Hsp2; fsetdec)
                  ltac:(clear - Hinter HΨρs Htun; fsetdec)
                  Hrhof Hdelta Hsh2 Hdfresh
                  (flex_apart_walk_step Hap0 (fastep_arrow_r _ _ _ _ _ _))
                  ltac:(eapply flex_shield_psi_anti;
                        [ eapply flex_shield_arrow_inv; exact Hfsh0
                        | clear - Htun; fsetdec ])
                  Hpre2
                  ltac:(clear - Hft2 HΨs1 Hinter Htun Htdisj Hun HΨρs; fsetdec)
                  ltac:(clear - HΨs2 Hun Htun Hft1 Hinter HΨρs Htdisj; fsetdec)
                  Hext Href2)
        as (Pa2 & Hs2 & Hp2).
      exists Pa1, Pa2; repeat split; [ exact Hs1 | exact Hs2 | ].
      cbn [msubst_pskl].
      eapply ad_ppre__arrow;
        [ exact Hp1 | exact Hp2
        | clear - HΨis Htun Htdisj Htageq; fsetdec ]. }
    (* now the guess: a ρ-leaf, or an arrow (reflexively or by congruence) *)
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rho_arrow_l_inv Hrho) as [[Heq HΨρe] | [Hleaf | Hcong]];
      [ | (* ρ-leaf *)
        destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa;
        eapply a_solve_sub_complete_rho_var;
          solve [ exact HwfΘ | exact Htags | clear - Htageq; fsetdec
                | exact Hrhof | exact Hdelta | exact HαΔρ | exact Hshield
                | exact Hpre ]
      | ].
    (* REFL: ρ is the identity here, so the guess IS the subject *)
    { subst ψa.
      assert (Hlc1 : lc_uskl R1) by (inversion Htsk; apply is_tskl_lc; assumption).
      assert (Hlc2 : lc_uskl R2) by (inversion Htsk; apply is_tskl_lc; assumption).
      assert (Hrho1 : uskl_rho NM Θ Δρ empty R1 R1)
        by (apply urho__refl; [ exact Hlc1 | clear; fsetdec ]).
      assert (Hrho2 : uskl_rho NM Θ Δρ empty R2 R2)
        by (apply urho__refl; [ exact Hlc2 | clear; fsetdec ]).
      pose proof (KEY R1 R2 empty empty Hrho1 Hrho2
                    ltac:(clear - HΨρe; fsetdec) Htags Hapart Hfsh) as KEY'.
      eapply arrow_grid;
        [ exact HwfΘ | exact Hκ | exact Htags | exact Htageq | exact KEY'
        | exact HwfPi | exact Hshield | exact Hpre ]. }
    (* CONGRUENCE *)
    { destruct Hcong as (ψ1 & ψ2 & Ψρ1 & Ψρ2 & Heq & Hrho1 & Hrho2 & HΨρs);
        subst ψa.
      pose proof (KEY ψ1 ψ2 Ψρ1 Ψρ2 Hrho1 Hrho2 HΨρs Htags Hapart Hfsh)
        as KEY'.
      eapply arrow_grid;
        [ exact HwfΘ | exact Hκ | exact Htags | exact Htageq | exact KEY'
        | exact HwfPi | exact Hshield | exact Hpre ]. }
  - (* ForallL, tagged (subtyping-proofs.tex:2086).  ψa = ∀^ε β.ψ'; the
       instantiation the rule performs is ABSORBED INTO ρ as the paper's
       ρ_b = ρ ∘ [ψ_b/β] ([uskl_rho_subst]), so the recursive call runs at
       Δρ,β — β is the one variable ρ_b replaces and ρ did not, and it is
       the SAME β the precision premise pairs Pi's binder with. *)
    match goal with
      Hd : ad_pat_sub_g _ _ _ _ _ (open_uskl_wrt_uskl R ψ) _ |- _ =>
      rename Hd into Hprem end.
    match goal with Ht : a_tags_sort _ _ ψ |- _ => rename Ht into Htagsg end.
    match goal with Hw : _ ⨟ _ ⊢ₚₛᵃ ⌊ ψ ⌋ˢ |- _ => rename Hw into Hwfg0 end.
    assert (Hwfg : Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ)
      by (eapply a_wf_pskl_weaken; [ exact Hext | exact Hwfg0 ]).
    match goal with
      Hf : _ ∩ (ftag_in_uskl (uskl_all_etag _ R)) [=] empty |- _ =>
      rename Hf into Hgfresh end.
    assert (Hlcg : lc_uskl ψ)
      by (apply is_tskl_lc; inversion Htagsg; assumption).
    (* the ∀^ε-shaped rows share a body; state it once, then dispatch *)
    assert (MAIN : forall L0 ψsrc,
      (forall α, α `notin` L0 ->
         uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl R (uskl_var_f α))
                             (open_uskl_wrt_uskl ψsrc (uskl_var_f α))) ->
      a_tags_sort NM Ψt (uskl_all_etag ε ψsrc) ->
      flex_apart_walk Θ0 Δρ P0 (uskl_all_etag ε ψsrc) ->
      flex_shield Θ0 Ψt Δρ P0 (uskl_all_etag ε ψsrc) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_all_etag ε ψsrc) ->
      exists Pa, Θ0 ⊢ₛ Pi ≼[ M ] P0 ⤳ Pa /\
        Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ]
                 (uskl_all_etag ε ψsrc)).
    { intros L0 ψsrc Hfam Htags0 Hapart0 Hfsh0 Hpre0.
      destruct (a_tags_sort_all_etag_inv Htags0)
        as (Lt & Ψt0 & Htbody & Hεt0 & HΨteq).
      (* --- ε is solved by the INPUT, never by the premise --- *)
      assert (HftagR : ftag_in_uskl ψsrc [<=] ftag_in_uskl R).
      { pick fresh α1 for L0.
        pose proof (uskl_rho_ftag_target_sub
                      (Hfam α1 ltac:(clear - Fr; solve_notin))) as Hb.
        rewrite (ftag_in_uskl_open_var R α1) in Hb.
        rewrite (ftag_in_uskl_open_var ψsrc α1) in Hb. exact Hb. }
      assert (HRtag : ftag_in_uskl R [<=] Ψρ `union` ftag_in_uskl ψsrc).
      { pick fresh α1 for L0.
        pose proof (uskl_rho_ftag_sub
                      (Hfam α1 ltac:(clear - Fr; solve_notin))) as Hb.
        rewrite (ftag_in_uskl_open_var R α1) in Hb.
        rewrite (ftag_in_uskl_open_var ψsrc α1) in Hb. exact Hb. }
      assert (HΨt0eq : Ψt0 [=] ftag_in_uskl ψsrc).
      { pick fresh α1 for Lt.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags
                      (Htbody α1 ltac:(clear - Fr; solve_notin)))) as Hb.
        rewrite (ftag_in_uskl_open_var ψsrc α1) in Hb. exact Hb. }
      assert (HεΨt : ε `in` Ψt) by (clear - HΨteq; fsetdec).
      assert (HεR : ε `notin` ftag_in_uskl R)
        by (clear - HRtag Hinter HεΨt HΨt0eq Hεt0; fsetdec).
      (* the guess's own tags are Ψ', which the rule keeps off ∀^ε R, and the
         premise's solved tags are bounded by ITS subject's — so ε ∉ Ψsub *)
      assert (HεΨsub : ε `notin` Ψ).
      { pose proof (ad_pat_sub_g_ftag_sub Hprem) as Hb.
        pose proof (ftag_in_uskl_open_upper R ψ) as Hup.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htagsg)) as Hg.
        cbn [ftag_in_uskl] in Hgfresh.
        clear - Hb Hup Hg Hgfresh HεR; fsetdec. }
      assert (HεΨi : ε `in` Ψi)
        by (clear - Htageq HΨteq HεΨsub HΨs2; fsetdec).
      (* Pi's shape is pinned by the precision premise: only a ∀ survives —
         every other row would have to solve ε, and ε is already in Ψi *)
      destruct Pi as [ | nPi | β0 | Pi1 Pi2 | Pi0 | | Pi0 ];
        cbn [msubst_pskl] in Hpre0.
      - (* ⟨⟩ *) inversion Hpre0.
      - (* a bound variable is not well-formed *) inversion HwfPi.
      - (* a variable : its κ-image is a MONOTYPE, whose target is tag-free *)
        exfalso.
        assert (HΨte : Ψt [=] empty)
          by (eapply ad_ppre_mono_subject_target_tags_empty;
                [ exact HwfΘ | exact Hpre0 | reflexivity
                | eapply a_inc_lookup_mono; exact Hκ
                | exact (a_tags_sort_d_tags Htags0) ]).
        clear - HΨte HεΨt; fsetdec.
      - (* an arrow *) inversion Hpre0.
      - (* Pi = ∀.Pi0 : THE ROW *)
        assert (Hex : exists Lp Ψi0,
                  (forall α, α `notin` Lp ->
                     Θ ⨟ (add α Δ)
                       ⊢ (open_pskl_wrt_pskl (msubst_pskl κ Pi0)
                            (pskl_var_f α))
                       ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψsrc (uskl_var_f α)))
                  /\ Ψi [=] add ε Ψi0).
        { inversion Hpre0; subst; eexists; eexists; split; eassumption. }
        destruct Hex as (Lp & Ψi0 & Hpbody & HΨieq).
        assert (Hexw : exists Lw,
                  forall α, α `notin` Lw ->
                    Θ0 ⨟ (add α empty)
                      ⊢ₚₛᵃ (open_pskl_wrt_pskl Pi0 (pskl_var_f α))).
        { inversion HwfPi; subst; eexists; eassumption. }
        destruct Hexw as (Lw & Hwbody).
        pick fresh β for
          (L0 `union` Lt `union` Lp `union` Lw `union` dom Θ `union` dom Θ0
             `union` dom κ `union` Δ `union` Δρ `union` def_ftv Θ
             `union` ftvar_in_uskl ψsrc `union` ftvar_in_uskl R
             `union` ftvar_in_uskl ψ `union` ftvar_in_pskl Pi0
             `union` ftvar_in_pskl P0).
        assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
        assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
        assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
        assert (HβΔ : β `notin` Δ) by (clear - Fr; solve_notin).
        assert (HβΔρ : β `notin` Δρ) by (clear - Fr; solve_notin).
        assert (HβR : β `notin` ftvar_in_uskl R) by (clear - Fr; solve_notin).
        (* --- ρ_b = ρ ∘ [ψ/β] --- *)
        destruct (@uskl_rho_subst NM Θ Δρ Ψρ
                    (open_uskl_wrt_uskl R (uskl_var_f β))
                    (open_uskl_wrt_uskl ψsrc (uskl_var_f β))
                    (Hfam β ltac:(clear - Fr; solve_notin))
                    β ψ Ψ' Htagsg Hwfg Hlcg HβΘ HβΔρ)
          as (Ψρ' & HΨρ'sub & HΨρ'mono & HΨρ'occ & Hrho').
        rewrite <- (@subst_bskl_in_uskl_intro β R ψ) in Hrho';
          [ | exact HβR ].
        (* the instantiation's tags are ρ-dirt — unless the binder is UNUSED,
           in which case the instantiation solves nothing at all *)
        assert (HΨ'sub : Ψ' [<=] Ψρ').
        { destruct (AtomSetProperties.In_dec β
                      (ftvar_in_uskl (open_uskl_wrt_uskl ψsrc (uskl_var_f β))))
            as [Hin | Hni]; [ exact (HΨρ'occ Hin) | ].
          assert (HβRo : β `notin` ftvar_in_uskl
                           (open_uskl_wrt_uskl R (uskl_var_f β))).
          { pose proof (uskl_rho_ftv_subject_bound
                          (Hfam β ltac:(clear - Fr; solve_notin))) as Hb.
            clear - Hb Hni HβΘ; fsetdec. }
          assert (Heqo : open_uskl_wrt_uskl R ψ
                         = open_uskl_wrt_uskl R (uskl_var_f β)).
          { rewrite (@subst_bskl_in_uskl_intro β R ψ); [ | exact HβR ].
            apply subst_bskl_in_uskl_fresh_eq; exact HβRo. }
          pose proof (ad_pat_sub_g_ftag_sub Hprem) as Hb.
          rewrite Heqo in Hb. rewrite (ftag_in_uskl_open_var R β) in Hb.
          cbn [ftag_in_uskl] in Hgfresh.
          clear - Hb Hgfresh; fsetdec. }
        (* --- the recursive call's premises at Θ0,β / Θ,β --- *)
        assert (Hwfβ : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
          by (apply a_wf_aenv__tvar; assumption).
        assert (Hwfβ0 : a_wf_aenv ((β ~ abind_tvar) ++ Θ0))
          by (apply a_wf_aenv__tvar; assumption).
        assert (Hweak0 : forall (x : atom) (b : abind),
                  binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
          by (intros x b Hb; apply binds_app_3; exact Hb).
        assert (Hweak : forall (x : atom) (b : abind),
                  binds x b Θ -> binds x b ((β ~ abind_tvar) ++ Θ))
          by (intros x b Hb; apply binds_app_3; exact Hb).
        assert (HwfPiβ : ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                  ⊢ₚₛᵃ (open_pskl_wrt_pskl Pi0 (pskl_var_f β))).
        { eapply a_wf_pskl_delta_to_tvar_mid
            with (α1 := β) (Θ1 := nil) (Θ2 := Θ0) (Δ' := empty);
            [ apply (Hwbody β ltac:(clear - Fr; solve_notin))
            | reflexivity | clear; fsetdec ]. }
        assert (HwfP0β : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
          by (eapply a_wf_pskl_weaken; [ exact Hweak0 | exact HwfP0 ]).
        assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
          by (apply a_inc_cons_tvar; exact Hκ).
        assert (Hrhoβ : uskl_rho NM ((β ~ abind_tvar) ++ Θ) (add β Δρ) Ψρ'
                  (open_uskl_wrt_uskl R ψ)
                  (open_uskl_wrt_uskl ψsrc (uskl_var_f β)))
          by (eapply uskl_rho_weaken; [ exact Hrho' | exact Hweak ]).
        assert (Htagsβ : a_tags_sort NM Ψt0
                  (open_uskl_wrt_uskl ψsrc (uskl_var_f β)))
          by (apply Htbody; clear - Fr; solve_notin).
        assert (HwfSubβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty
                  ⊢ₚₛᵃ ⌊ open_uskl_wrt_uskl R ψ ⌋ˢ).
        { assert (Hexs : exists Lb, forall α, α `notin` Lb ->
                    Θ ⨟ (add α empty) ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f α))).
          { cbn [uskl_to_pskl] in HwfSub;
            inversion HwfSub; subst; eexists; eassumption. }
          destruct Hexs as (Lb & Hbody).
          rewrite uskl_to_pskl_open_gen.
          eapply a_wf_pskl_weaken; [ exact Hweak | ].
          eapply a_wf_pskl_open; [ exact Hbody | exact Hwfg ]. }
        assert (HΨi0sub : Ψi0 [<=] Ψt0)
          by (eapply ad_partial_precise_tags_sub;
                [ exact HwfΘ | apply (Hpbody β ltac:(clear - Fr; solve_notin))
                | exact (a_tags_sort_d_tags Htagsβ) ]).
        assert (Htageqβ : Ψi0 `union` Ψa [=] Ψt0)
          by (clear - Htageq HΨteq HΨieq HΨi0sub Hεt0 HεΨsub HΨs2; fsetdec).
        assert (Hinterβ : Ψρ' ∩ Ψt0 [=] empty).
        { cbn [ftag_in_uskl] in Hgfresh.
          clear - HΨρ'sub Hinter HΨteq HΨt0eq HftagR Hgfresh; fsetdec. }
        assert (Hrhofβ : rho_fresh (add β Δρ) ((β ~ abind_tvar) ++ Θ) κ).
        { intros α0 Hα0.
          destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin | Hni].
          - destruct (Hrhof α0 Hin) as (Hb & Him & Hdf).
            repeat split; [ apply binds_app_3; exact Hb | exact Him | ].
            intros α3 τ3 Hb3. eapply Hdf.
            destruct (binds_cons_1 _ _ _ _ _ _ Hb3) as [[_ Habs] | Hb'];
              [ discriminate Habs | exact Hb' ].
          - assert (Heqβ : α0 = β) by (clear - Hα0 Hni; fsetdec); subst α0.
            repeat split.
            + unfold binds; left; reflexivity.
            + intros pp Hpp.
              pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb.
              clear - Hb HβΘ; fsetdec.
            + intros α3 τ3 Hb3.
              assert (Hb' : binds α3 (abind_flex_mono_def τ3) Θ)
                by (destruct (binds_cons_1 _ _ _ _ _ _ Hb3)
                      as [[_ Habs] | Hb']; [ discriminate Habs | exact Hb' ]).
              pose proof (a_wf_ptyp_ftv_dom
                            (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb')) as Hd.
              clear - Hd HβΘ; fsetdec. }
        assert (Hdeltaβ : add β Δρ [<=] add β Δ)
          by (clear - Hdelta; fsetdec).
        assert (Hshieldβ : forall α0, α0 `in` (add β Δρ) ->
                  α0 `notin` pskl_shielded_ftv
                    (msubst_pskl κ (open_pskl_wrt_pskl Pi0 (pskl_var_f β)))).
        { intros α0 Hα0.
          destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin | Hni].
          - rewrite (@msubst_pskl_open Θ0 κ Θ Pi0 β Hκ Hβκ).
            pose proof (Hshield α0 Hin) as Hs.
            cbn [msubst_pskl pskl_shielded_ftv] in Hs.
            pose proof (pskl_shielded_ftv_open_upper (msubst_pskl κ Pi0)
                          (pskl_var_f β)) as Hup.
            cbn [ftvar_in_pskl] in Hup.
            assert (Hne : α0 <> β) by (clear - Hin HβΔρ; fsetdec).
            clear - Hs Hup Hne; fsetdec.
          - (* the ∀◇-body discipline: a well-formed skeleton's SHIELDED
               variables all live in the aenv, never in Δ — so the freshly
               opened binder is not one of them (DESIGN §7) *)
            assert (Heqβ : α0 = β) by (clear - Hα0 Hni; fsetdec); subst α0.
            apply msubst_pskl_shielded_avoid.
            + intros pp Hpp.
              pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb.
              clear - Hb HβΘ; fsetdec.
            + pose proof (a_wf_pskl_shielded_dom
                            (Hwbody β ltac:(clear - Fr; solve_notin))) as Hd.
              clear - Hd HβΘ0; fsetdec. }
        assert (Hdfreshβ : delta_def_fresh (add β Δ) ((β ~ abind_tvar) ++ Θ)).
        { intros β0 α3 τ3 Hβ0 Hb.
          assert (Hb' : binds α3 (abind_flex_mono_def τ3) Θ)
            by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                  [ discriminate Habs | exact Hb' ]).
          destruct (AtomSetProperties.In_dec β0 Δ) as [Hin | Hni];
            [ eapply Hdfresh; [ exact Hin | exact Hb' ] | ].
          assert (Heqβ : β0 = β) by (clear - Hβ0 Hni; fsetdec); subst β0.
          pose proof (a_wf_ptyp_ftv_dom
                        (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb')) as Hd.
          clear - Hd HβΘ; fsetdec. }
        assert (Hapartβ : flex_apart_walk ((β ~ abind_tvar) ++ Θ0)
                  (add β Δρ) P0 (open_uskl_wrt_uskl ψsrc (uskl_var_f β)))
          by (apply flex_apart_walk_weaken_tvar;
              eapply flex_apart_walk_step;
                [ exact Hapart0 | apply fastep_all_r ]).
        assert (Hfshβ : flex_shield ((β ~ abind_tvar) ++ Θ0) Ψt0 (add β Δρ)
                  P0 (open_uskl_wrt_uskl ψsrc (uskl_var_f β))).
        { apply flex_shield_weaken_tvar.
          eapply flex_shield_psi_anti;
            [ eapply flex_shield_descend_r;
                [ exact Hfsh0 | exact HεΨt | exact HβΔρ
                | clear - Fr; solve_notin ]
            | clear - HΨteq; fsetdec ]. }
        assert (Hpreβ : ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ)
                  ⊢ (msubst_pskl κ (open_pskl_wrt_pskl Pi0 (pskl_var_f β)))
                  ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψsrc (uskl_var_f β))).
        { rewrite (@msubst_pskl_open Θ0 κ Θ Pi0 β Hκ Hβκ).
          eapply ad_partial_precise_weaken;
            [ apply (Hpbody β ltac:(clear - Fr; solve_notin)) | exact Hweak ]. }
        assert (Hrefβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                  (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q)
          by (eapply ad_refine_syn_weaken; [ exact Hrefine | exact Hweak ]).
        edestruct (IHHsub ((β ~ abind_tvar) ++ Θ) ((β ~ abind_tvar) ++ Θ0) κ
                     (add β Δ) (add β Δρ) Ψρ' Ψt0 Ψi0 Ψa
                     (open_uskl_wrt_uskl ψsrc (uskl_var_f β))
                     (open_pskl_wrt_pskl Pi0 (pskl_var_f β)) P0
                     Hwfβ Hwfβ0 HwfPiβ HwfP0β HmodSK HmodTY Hκβ Hrhoβ
                     Htagsβ HwfSubβ Htageqβ Hinterβ Hrhofβ Hdeltaβ Hshieldβ
                     Hdfreshβ Hapartβ Hfshβ Hpreβ
                     ltac:(clear - HΨs1 HΨρ'mono HΨ'sub; fsetdec)
                     ltac:(clear - HΨs2; fsetdec)
                     ltac:(intros x b Hb; apply binds_app_3; apply Hext;
                           exact Hb)
                     Hrefβ)
          as (Pa & Hs & Hp).
        (* --- re-abstract β --- *)
        remember (close_pskl_wrt_pskl β Pa) as Pb eqn:HeqPb.
        assert (HopenPb : open_pskl_wrt_pskl Pb (pskl_var_f β) = Pa)
          by (subst Pb; apply open_pskl_wrt_pskl_close_pskl_wrt_pskl).
        assert (HβPb : β `notin` ftvar_in_pskl Pb)
          by (subst Pb; rewrite ftvar_in_pskl_close_pskl_wrt_pskl;
              clear; fsetdec).
        clear HeqPb.
        assert (HβPbκ : β `notin` ftvar_in_pskl (msubst_pskl κ Pb)).
        { apply msubst_pskl_ftv_avoid;
            [ intros pp Hpp;
              pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
              clear - Hb HβΘ; fsetdec
            | exact HβPb ]. }
        exists (pskl_all_syn Pb); split.
        + (* SolS-ForallL: the single instance at β becomes the cofinite
             family by RIGID RENAMING *)
          assert (HsΘ0 : Θ0 ⊢ₛ (open_pskl_wrt_pskl Pi0 (pskl_var_f β))
                    ≼[ M ] P0 ⤳ Pa)
            by (eapply a_solve_sub_strengthen_tvar; exact Hs).
          apply a_solve_sub__forall_l
            with (L := dom Θ0 `union` singleton β `union` ftvar_in_pskl Pi0
                         `union` ftvar_in_pskl Pb `union` ftvar_in_pskl P0).
          intros α Hα.
          pose proof ((proj1 a_solve_sub_eq_rename) _ _ _ _ _ HsΘ0 β α
                        HβΘ0 ltac:(clear - Hα; fsetdec)) as Hren.
          rewrite (@subst_pskl_in_pskl_fresh_eq P0 (pskl_var_f α) β)
            in Hren; [ | clear - Fr; solve_notin ].
          rewrite <- (@subst_pskl_in_pskl_intro β Pi0 (pskl_var_f α))
            in Hren; [ | clear - Fr; solve_notin ].
          rewrite <- HopenPb in Hren.
          rewrite <- (@subst_pskl_in_pskl_intro β Pb (pskl_var_f α))
            in Hren; [ | exact HβPb ].
          exact Hren.
        + (* precision: β lives in Δ, so it can leave the aenv
             ([ad_partial_precise_tvar_to_delta_mid]); then rename it into
             P-Forall's family *)
          assert (Hp' : Θ ⨟ (add β Δ) ⊢ (msubst_pskl κ Pa)
                    ⊑ᵖ[ Ψi0 `union` Ψa ]
                    (open_uskl_wrt_uskl ψsrc (uskl_var_f β)))
            by (eapply ad_partial_precise_tvar_to_delta_mid
                  with (β := β) (Θ1 := nil) (Θ2 := Θ);
                  [ exact Hp | reflexivity | clear; fsetdec | exact HβΘ
                  | clear; fsetdec ]).
          assert (Heqsub : msubst_pskl κ Pa
                    = open_pskl_wrt_pskl (msubst_pskl κ Pb) (pskl_var_f β)).
          { rewrite <- HopenPb at 1.
            apply (@msubst_pskl_open Θ0 κ Θ Pb β Hκ Hβκ). }
          rewrite Heqsub in Hp'.
          cbn [msubst_pskl].
          (* [Ψ0] must be PINNED: leaving it an evar sends the tag side
             condition's [fsetdec] into a non-terminating search *)
          eapply ad_ppre__forall
            with (L := dom Θ `union` Δ `union` singleton β
                        `union` ftvar_in_uskl ψsrc
                        `union` ftvar_in_pskl (msubst_pskl κ Pb))
                 (Ψ0 := Ψi0 `union` Ψa);
            [ | clear - HΨieq; fsetdec ].
          intros α Hα.
          (* split the pick-fresh union ONCE: a [fsetdec] that has to walk a
             six-way union under a [⊆] hypothesis does not terminate here *)
          assert (HαΘ : α `notin` dom Θ) by (clear - Hα; solve_notin).
          assert (HαΔ : α `notin` Δ) by (clear - Hα; solve_notin).
          assert (Hαβ : α `notin` singleton β) by (clear - Hα; solve_notin).
          assert (Hαψ : α `notin` ftvar_in_uskl ψsrc)
            by (clear - Hα; solve_notin).
          assert (HαPb : α `notin` ftvar_in_pskl (msubst_pskl κ Pb))
            by (clear - Hα; solve_notin).
          assert (Hdefs : forall α3 τ3, binds α3 (abind_flex_mono_def τ3) Θ ->
                    β `notin` ftvar_in_ptyp τ3 /\ α `notin` ftvar_in_ptyp τ3).
          { intros α3 τ3 Hb.
            pose proof (a_wf_ptyp_ftv_dom
                          (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb)) as Hd.
            split; [ clear - Hd HβΘ; fsetdec | clear - Hd HαΘ; fsetdec ]. }
          pose proof (@ad_partial_precise_rename Θ (add β Δ)
                        (Ψi0 `union` Ψa)
                        (open_pskl_wrt_pskl (msubst_pskl κ Pb)
                           (pskl_var_f β))
                        (open_uskl_wrt_uskl ψsrc (uskl_var_f β)) Hp' β α
                        ltac:(clear; fsetdec) HβΘ HαΘ
                        ltac:(clear - HαΔ Hαβ; fsetdec)
                        ltac:(pose proof
                                (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                   (msubst_pskl κ Pb) (pskl_var_f β)) as Hup;
                              cbn [ftvar_in_pskl] in Hup;
                              clear - HαPb Hαβ Hup; fsetdec)
                        ltac:(pose proof
                                (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                                   ψsrc (uskl_var_f β)) as Hup;
                              cbn [ftvar_in_uskl] in Hup;
                              clear - Hαψ Hαβ Hup; fsetdec)
                        Hdefs) as Hrn.
          rewrite <- (@subst_pskl_in_pskl_intro β (msubst_pskl κ Pb)
                        (pskl_var_f α)) in Hrn; [ | exact HβPbκ ].
          rewrite <- (@subst_bskl_in_uskl_intro β ψsrc (uskl_var_f α))
            in Hrn; [ | clear - Fr; solve_notin ].
          eapply ad_partial_precise_delta_cong;
            [ exact Hrn | clear - HβΔ; fsetdec ].
      - (* □ : P-Ghost solves no tag, but ε is already in Ψi *)
        exfalso.
        pose proof (ad_ppre_hole_subject_tags Hpre0) as HΨie.
        clear - HΨie HεΨi; fsetdec.
      - (* ∀◇Pi0 : both rules that could reach a ∀^ε are refuted *)
        exfalso.
        assert (HgPi0 : guarded_pskl Pi0) by (inversion HwfPi; assumption).
        inversion Hpre0; subst.
        + (* P-UnivGhostRemove: wf makes the ∀◇-body guarded *)
          eapply ad_ppre_guarded_all_etag_absurd;
            [ exact HwfΘ | exact Hκ | exact HgPi0
            | exact (a_tags_sort_d_tags Htags0) | eassumption ].
        + (* P-UnivGhostFill: the body carries no ε, so Ψi cannot either *)
          assert (Hexf : exists Lf Pf, forall α, α `notin` Lf ->
                    ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ Pf ⊑ᵖ[ Ψi ]
                      (open_uskl_wrt_uskl ψsrc (uskl_var_f α)))
            by (eexists; eexists; eassumption).
          destruct Hexf as (Lf & Pf & Hfill).
          pick fresh α2 for (Lf `union` Lt `union` dom Θ).
          (* the wf must be BUILT FIRST: as an [eapply] side goal its context
             is still an evar and the freshness cannot be shown *)
          assert (Hwf2 : a_wf_aenv ((α2 ~ abind_tvar) ++ Θ))
            by (apply a_wf_aenv__tvar; [ clear - Fr; solve_notin | exact HwfΘ ]).
          assert (HΨisub : Ψi [<=] Ψt0)
            by (eapply ad_partial_precise_tags_sub;
                  [ exact Hwf2
                  | apply (Hfill α2 ltac:(clear - Fr; solve_notin))
                  | exact (a_tags_sort_d_tags
                             (Htbody α2 ltac:(clear - Fr; solve_notin))) ]).
          clear - HΨisub HεΨi Hεt0; fsetdec. }
    (* dispatch: ψa is ∀^ε itself (ρ = id or a congruence) or a ρ-leaf *)
    destruct (uskl_rho_all_etag_l_inv Hrho) as [[Heq HΨρe] | [Hleaf | Hcong]].
    + (* refl: ρ is the identity here, so ψ' := R *)
      subst ψa.
      assert (Htsk : is_tskl (uskl_all_etag ε R))
        by (inversion Htags; assumption).
      destruct (is_tskl_all_etag_inv Htsk) as (Li & Hti).
      eapply MAIN;
        solve [ intros α Hα; apply urho__refl;
                  [ apply is_tskl_lc; apply Hti; exact Hα
                  | clear - HΨρe; fsetdec ]
              | exact Htags | exact Hapart | exact Hfsh | exact Hpre ].
    + (* ρ-leaf: the guess is a replaced rigid variable *)
      destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa.
      eapply a_solve_sub_complete_rho_var;
        solve [ exact HwfΘ | exact Htags | clear - Htageq; fsetdec
              | exact Hrhof | exact Hdelta | exact HαΔρ | exact Hshield
              | exact Hpre ].
    + (* congruence *)
      destruct Hcong as (L0 & ψsrc & Heq & Hfam); subst ψa.
      eapply MAIN;
        solve [ exact Hfam | exact Htags | exact Hapart | exact Hfsh
              | exact Hpre ].
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
       ψa = □ (refuted by [is_tskl], which admits only the DOTTED ◈) or a
       ρ-leaf whose image □ would have to be tags-sorted (same refutation). *)
    exfalso.
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rho_hole_l_inv Hrho) as [[Heq _] | Hleaf].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_tskl uskl_hole) by (inversion Htagsub; assumption).
      inversion Htsk'.
  - (* GhostG (SK) : the dotted ◈ subject.  [mod_comp_sk ⟨⟩ M] rules out
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
       subject is a PLAIN ∀◇, and [is_tskl] admits only the DOTTED ∀◈, so
       neither ψa itself nor a ρ-image can have this shape *)
    exfalso.
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rho_tophole_l_inv Hrho) as [[Heq _] | [Hleaf | Hcong]].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_tskl (uskl_tophole R)) by (inversion Htagsub; assumption).
      inversion Htsk'.
    + destruct Hcong as (R0 & Heq & _); subst ψa; inversion Htsk.
  - (* UnivGhostLG (SK) : the DOTTED ∀◈ subject.  ψa is either a ρ-leaf
       (closed by [a_solve_sub_complete_rho_var]) or itself a ∀◈; in the
       latter case the precision premise forces Pi = ∀◇Pi' or Pi = □, and
       the ∀◇ row is IH + SolS-UnivGhostL + P-UnivGhostKeep. *)
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    (* the ∀◈-shaped rows share a body; state it once, then dispatch *)
    assert (KEY : forall ψ0,
      uskl_rho a_sub_mode_sk Θ Δρ Ψρ R ψ0 ->
      a_tags_sort a_sub_mode_sk Ψt (uskl_topholeg ψ0) ->
      flex_apart_walk Θ0 Δρ P0 (uskl_topholeg ψ0) ->
      flex_shield Θ0 Ψt Δρ P0 (uskl_topholeg ψ0) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_topholeg ψ0) ->
      exists Pa, Θ0 ⊢ₛ Pi ≼[ M ] P0 ⤳ Pa /\
        Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] (uskl_topholeg ψ0)).
    { intros ψ0 Hrho0 Htags0 Hapart0 Hfsh0 Hpre0.
      assert (Htags0' : a_tags_sort a_sub_mode_sk Ψt ψ0)
        by (eapply a_tags_sort_topholeg_inv; exact Htags0).
      assert (HwfSub' : Θ ⨟ empty ⊢ₚₛᵃ ⌊ R ⌋ˢ)
        by (cbn [uskl_to_pskl] in HwfSub;
            eapply a_wf_pskl_tophole_inv; exact HwfSub).
      assert (Hapart0' : flex_apart_walk Θ0 Δρ P0 ψ0)
        by (eapply flex_apart_walk_step;
              [ exact Hapart0 | apply fastep_topholeg_r ]).
      assert (Hfsh0' : flex_shield Θ0 Ψt Δρ P0 ψ0)
        by (eapply flex_shield_topholeg_r_inv; exact Hfsh0).
      (* Pi's shape is pinned by the precision premise: only a ∀◇ or a □
         can be precise to a dotted universal ghost *)
      destruct Pi as [ | nPi | β | Pi1 Pi2 | Pi' | | Pi' ].
      - exfalso; eapply ad_ppre_guarded_topholeg_absurd;
          [ exact HwfΘ | exact Hκ | apply guarded_pskl__unit | exact Hpre0 ].
      - inversion HwfPi.
      - exfalso; eapply ad_ppre_guarded_topholeg_absurd;
          [ exact HwfΘ | exact Hκ | apply guarded_pskl__var | exact Hpre0 ].
      - exfalso.
        assert (Hg : guarded_pskl (pskl_arrow Pi1 Pi2)).
        { pose proof (a_wf_pskl_lc HwfPi) as Hlcarr.
          inversion Hlcarr; subst; apply guarded_pskl__arrow; assumption. }
        eapply ad_ppre_guarded_topholeg_absurd;
          [ exact HwfΘ | exact Hκ | exact Hg | exact Hpre0 ].
      - (* ∀: no precision rule reaches a ∀◈ from a quantifier *)
        cbn [msubst_pskl] in Hpre0; inversion Hpre0.
      - (* □ : the ghost row.  [paper-gap] The paper's UnivGhostLG case says
           "we know that P_i must have a top-level ∀◇" (subtyping-proofs.tex
           :2196), reading the precision premise as if only P-UnivGhostKeep
           could target a ∀◈.  But P-Ghost is TARGET-AGNOSTIC — [□ ⊑ᵖ[∅] ψ]
           for any ψ — so a hole input is precise to a ∀◈ too, and this row
           is real.  The consistency twin's proof DOES spell out its
           "Subcase P_i = □"; the subtyping write-up simply omits it.
           Nothing is decomposed here (a □ input stays □), so the IH's own
           solve is the one we need; only its precision has to be lifted
           back under the ghost. *)
        cbn [msubst_pskl] in Hpre0.
        pose proof (ad_ppre_hole_subject_tags Hpre0) as HΨie.
        (* the Δ-disjointness the IH needs, read off the SAME premise: the
           ∀◈ adds no free variable, so [P-Ghost]'s side condition at
           [∀◈ψ0] IS the one at ψ0 *)
        assert (HΔψ0 : Δ ∩ ftvar_in_uskl ψ0 [=] empty).
        { (* only [P-Ghost] can conclude with a ∀◈ target from a □ subject:
             the target-side flexible unfolding needs a VARIABLE target *)
          inversion Hpre0; subst; cbn [ftvar_in_uskl] in *; assumption. }
        assert (Hpre0' : Θ ⨟ Δ ⊢ (msubst_pskl κ pskl_hole) ⊑ᵖ[ Ψi ] ψ0)
          by (cbn [msubst_pskl]; apply ad_ppre__hole; assumption).
        edestruct (IHHsub Θ Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa ψ0 pskl_hole P0
                     HwfΘ HwfΘ0 HwfPi HwfP0 HmodSK HmodTY Hκ Hrho0
                     Htags0' HwfSub' Htageq Hinter Hrhof Hdelta Hshield
                     Hdfresh Hapart0' Hfsh0' Hpre0' HΨs1 HΨs2 Hext Hrefine)
          as (Pa' & Hs' & Hp').
        exists Pa'; split; [ exact Hs' | ].
        eapply ad_ppre_lift_topholeg;
          [ exact HwfΘ | exact Hp' | exact HΔψ0
          | (* the guess erases to a guarded skeleton: ρ transports it from
               the subject, whose ∀◈-body wf makes it guarded *)
            eapply uskl_rho_guarded_erase;
              [ exact Hrho0
              | apply is_tskl_lc; inversion Htags0'; assumption
              | cbn [uskl_to_pskl] in HwfSub;
                inversion HwfSub; assumption ]
          | (* the shape of the output, pushed through the metasubstitution *)
            destruct (a_solve_sub_hole_output Hs') as [-> | (B & ->)];
              [ left; reflexivity
              | right; eexists; cbn [msubst_pskl]; reflexivity ] ].
      - (* ∀◇Pi' : the main row — IH, then SolS-UnivGhostL *)
        assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi')
          by (eapply a_wf_pskl_tophole_inv; exact HwfPi).
        assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
        cbn [msubst_pskl] in Hpre0.
        inversion Hpre0; subst.
        + (* P-UnivGhostRemove: EXCLUDED — wf makes the ∀◇-body guarded *)
          exfalso; eapply ad_ppre_guarded_topholeg_absurd;
            [ exact HwfΘ | exact Hκ | exact HgPi' | eassumption ].
        + (* P-UnivGhostKeep *)
          match goal with Hbody : _ ⨟ _ ⊢ _ ⊑ᵖ[ _ ] ψ0 |- _ =>
            rename Hbody into Hpre' end.
          assert (Hshield' : forall α0, α0 `in` Δρ ->
                    α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi')).
          { intros α0 Hα0. pose proof (Hshield α0 Hα0) as Hsh.
            cbn [msubst_pskl pskl_shielded_ftv] in Hsh.
            pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi')) as Hle.
            clear - Hsh Hle; fsetdec. }
          edestruct (IHHsub Θ Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa ψ0 Pi' P0
                       HwfΘ HwfΘ0 HwfPi' HwfP0 HmodSK HmodTY Hκ Hrho0
                       Htags0' HwfSub' Htageq Hinter Hrhof Hdelta Hshield'
                       Hdfresh Hapart0' Hfsh0' Hpre' HΨs1 HΨs2 Hext Hrefine)
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
    + (* congruence: ψa = ∀◈ψ0 with R ρ-related to ψ0 *)
      destruct Hcong as (ψ0 & Heq & Hrho0); subst ψa.
      apply KEY; assumption.
  - (* FlexMono : the subject is a DEFINED flexible.  The guess is either
       that same flexible — unfold it on BOTH sides and rebuild the
       precision with P-FlexR — or a ρ-leaf. *)
    destruct (uskl_rho_var_l_inv Hrho) as [[Heq HΨρe] | Hleaf].
    + (* the guess is the same defined flexible *)
      subst ψa.
      assert (HΨte : Ψt [=] empty)
        by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
      assert (Hmono : mono_ptyp τ)
        by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact H ]).
      assert (Hwfτ : a_wf_ptyp Θ τ)
        by (eapply a_wf_aenv_binds_def_wf; [ exact HwfΘ | exact H ]).
      (* the unfolded guess: a monotype painting, hence tag-free, and
         Δ-clean because a definition never mentions a Δ-variable *)
      assert (Hclean : (ftvar_in_uskl (ptyp_to_uskl_syn τ)) ∩ Δρ [=] empty).
      { rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
        intros α0; split; intros Hin; [ | clear - Hin; fsetdec ].
        exfalso.
        assert (Hα0Δ : α0 `in` Δ) by (clear - Hin Hdelta; fsetdec).
        pose proof (Hdfresh α0 α τ Hα0Δ H) as Hbad.
        clear - Hin Hbad; fsetdec. }
      assert (Hrho' : uskl_rho NM Θ Δρ Ψρ
                        (ptyp_to_uskl_syn τ) (ptyp_to_uskl_syn τ))
        by (apply urho__refl;
            [ apply is_tskl_lc; apply mono_ptyp_to_uskl_syn_tskl; exact Hmono
            | exact HΨρe ]).
      edestruct (IHHsub Θ Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa (ptyp_to_uskl_syn τ) Pi P0
                   HwfΘ HwfΘ0 HwfPi HwfP0 HmodSK HmodTY Hκ Hrho')
        as (Pa & Hs & Hp).
      * (* the painting is tags-sorted, with NO tags *)
        eapply a_tags_sort_psi_cong;
          [ apply a_tags_sort_mono_paint; exact Hmono | clear - HΨte; fsetdec ].
      * (* its erasure is well-formed *)
        match goal with |- _ ⨟ _ ⊢ₚₛᵃ ⌊ ptyp_to_uskl_syn ?τ0 ⌋ˢ =>
          replace (uskl_to_pskl (ptyp_to_uskl_syn τ0)) with (ptyp_to_pskl τ0)
            by (symmetry; apply uskl_to_pskl_ptyp)
        end.
        apply mono_ptyp_wf_to_pskl_wf; assumption.
      * exact Htageq.
      * exact Hinter.
      * exact Hrhof.
      * exact Hdelta.
      * exact Hshield.
      * exact Hdfresh.
      * eapply flex_apart_walk_step;
          [ exact Hapart | apply fastep_flexdef_r; exact Hclean ].
      * apply fsh_clean;
          [ exact Hclean
          | rewrite ftag_in_uskl_ptyp_to_uskl_syn; clear; fsetdec ].
      * (* precision: unfold the definition on the TARGET *)
        eapply ad_ppre_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdfresh | exact Hpre | reflexivity | exact H ].
      * exact HΨs1.
      * exact HΨs2.
      * exact Hext.
      * exact Hrefine.
      * (* rebuild: the guess is the flexible whose definition we unfolded *)
        exists Pa; split; [ exact Hs | ].
        eapply ad_ppre__flex_r; [ exact H | exact Hp ].
    + (* ρ-leaf: the guess is a replaced rigid variable *)
      destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa.
      eapply a_solve_sub_complete_rho_var;
        solve [ exact HwfΘ | exact Htags | clear - Htageq; fsetdec
              | exact Hrhof | exact Hdelta | exact HαΔρ | exact Hshield
              | exact Hpre ].
Qed.
