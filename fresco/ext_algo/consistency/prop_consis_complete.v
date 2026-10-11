(** ext_algo — §8c.10, campaign level 5: COMPLETENESS of the extracted
    [assign] / [unifyvar] / [consistency] block, [e_consis_call_impl].

    The three headlines (§8) hold on GHOST-CARRYING skeletons.  What makes
    the ghost rows ordinary cases is the [<> ◇] guard on [U-FlexL] /
    [U-FlexR] (algo/def_rules.v): every cell with a [◇] on one side admits
    exactly one rule (§2), the one the runner takes.  The level's first
    scoping — relating the two output contexts UP TO A RENAMING — was
    refuted before that guard (cex/probe_consis_ghost_flex.v,
    docs/HANDOFF-close-consis-unrestricted.md). *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.consistency.prop_consis.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.consistency.def_consis_impl.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §2  THE GHOST-ROW INVERSIONS — every ghost cell admits ONE rule       *)
(*                                                                        *)
(*  At a ghost SUBJECT only [U-Ghost] can fire unless the pattern is a     *)
(*  variable, and at a ghost PATTERN only [U-GhostR] can unless the        *)
(*  subject is.  [U-UnivGhostR] is excluded everywhere here because it     *)
(*  demands a GUARDED subject and [◇] is not guarded.  The two variable    *)
(*  cells are mirror images, and each admits exactly one rule as well     *)
(*  because [U-FlexL] / [U-FlexR] carry [P0 <> ◇] / [P <> ◇]               *)
(*  (algo/def_rules.v), which renders the reference implementation's       *)
(*  ghost-first dispatch.  [do_ghost_cell] (§7) consumes these.            *)
(* ===================================================================== *)

(** ⚙ The surviving goals are the rule's own premises plus, at the [(◇,◇)]
    overlap, a disjointness against [ftvar_in_pskl ◇ = ∅]. *)
Local Ltac ghost_close :=
  repeat split;
  first [ assumption | reflexivity | (simpl in *; fsetdec) ].

(** A ghost SUBJECT against a non-variable pattern: only [U-Ghost]. *)
Lemma e_consis_inv_ghost_subject : forall Δ1 Δ2 S0 Θ0 P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] pskl_ghost ∼ Q ⊣ Θ1 }}e ->
  (forall β, P0 <> pskl_var_f β) ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = P0 /\ Δ2 ∩ ftvar_in_pskl P0 [=] empty.
Proof.
  intros * Hd Hnv. inversion Hd; subst;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | match goal with
                | H : guarded_pskl pskl_ghost |- _ => inversion H
                end ].
  all: ghost_close.
Qed.

(** A ghost PATTERN against a non-variable subject: only [U-GhostR].
    ⚙ The subject may itself be [◇]: there [U-Ghost] fires too, but it
    returns the SAME triple, so the cell needs no uniqueness argument —
    the level-5 analogue of [U-Rigid] versus [U-Flex], which [e_unify_refl]
    settled the same way. *)
Lemma e_consis_inv_ghost_pattern : forall Δ1 Δ2 S0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_ghost ] P ∼ Q ⊣ Θ1 }}e ->
  (forall β, P <> pskl_var_f β) ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = P /\ Δ1 ∩ ftvar_in_pskl P [=] empty.
Proof.
  intros * Hd Hnv. inversion Hd; subst;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | match goal with
                | H : guarded_pskl pskl_ghost |- _ => inversion H
                end ].
  all: ghost_close.
Qed.

(** ⭐ FORMERLY DIVERGENT CELL 1 — a ghost subject against a FLEXIBLE
    pattern.  [U-Ghost] leaves the context alone; [U-FlexR] would have
    assigned, and the runner takes the first
    (def_consis_impl.v:807-813).  Since the [<> ◇] dispatch guards landed
    on [U-FlexL]/[U-FlexR] (algo/def_rules.v) the second route is BARRED,
    so this cell now admits exactly ONE rule and the inversion is no
    longer a disjunction — which is what retires the two-context problem
    docs/HANDOFF-close-consis-unrestricted.md was written about. *)
Lemma e_consis_inv_ghost_flex_pattern : forall Δ1 Δ2 S0 Θ0 β Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ] pskl_ghost ∼ Q ⊣ Θ1 }}e ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = pskl_var_f β
    /\ Δ2 ∩ ftvar_in_pskl (pskl_var_f β) [=] empty.
Proof.
  intros * Hd. inversion Hd; subst;
    try solve [ congruence
              | match goal with
                | H : guarded_pskl pskl_ghost |- _ => inversion H
                end ].
  ghost_close.
Qed.

(** ⭐ FORMERLY DIVERGENT CELL 2 — the mirror: a FLEXIBLE subject against
    a ghost pattern.  [U-GhostR] versus [U-FlexL], the runner takes GhostR
    (def_consis_impl.v:759-763, whose ghost-pattern arm is unconditional in
    the subject), and the [<> ◇] guard now bars [U-FlexL] here, so this
    cell too admits exactly one rule. *)
Lemma e_consis_inv_flex_subject_ghost : forall Δ1 Δ2 S0 Θ0 α Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_ghost ] (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = pskl_var_f α
    /\ Δ1 ∩ ftvar_in_pskl (pskl_var_f α) [=] empty.
Proof.
  intros * Hd. inversion Hd; subst;
    try solve [ congruence
              | match goal with
                | H : guarded_pskl pskl_ghost |- _ => inversion H
                end ].
  ghost_close.
Qed.

(* ===================================================================== *)
(*  §3  EQUIVARIANCE ALONG A CHAIN                                        *)
(*                                                                        *)
(*  What [U-Arrow] will consume.  Its second premise runs at the FIRST    *)
(*  premise's output, and the derivation's output differs from the        *)
(*  runner's by the fresh names each side happened to pick — a whole      *)
(*  CHAIN of transpositions, not one.  prop_consis.v §10 iterates: the    *)
(*  Δ-slots stay LITERAL (each step feeds the next its own                *)
(*  [swap_atoms], so no set ever has to be moved across [=]), and only    *)
(*  the supply is carried up to [=], which is where prop_consis.v §9's    *)
(*  supply-respect discharges the empty chain.                            *)
(*                                                                        *)
(*  ⚙ The chain acts as the IDENTITY on anything the caller already held  *)
(*  — that is [swaps_pskl_fresh_id] / [swaps_atom_notin]                  *)
(*  (prop_solve_det.v §1), given that every pair in the chain avoids the  *)
(*  input supply.                                                         *)
(* ===================================================================== *)

(** ⚙ The Δ-slots are taken as [=]-VARIANTS, exactly as [e_consis_swap]
    takes them and for the same reason: a caller that has to hold the
    chain's action on a Δ fixed ([U-Arrow], where every pair dodges the
    input supply and the two Δs live inside it) holds a [swaps_atoms_notin]
    proof, not the term.  prop_consis.v §9's [e_consis_delta_respect] is
    what discharges it at the empty chain. *)
Lemma e_consis_swaps : forall ps Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  forall Δ1' Δ2' S0',
  Δ1' [=] swaps_atoms ps Δ1 -> Δ2' [=] swaps_atoms ps Δ2 ->
  S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0)
       ⊢[ Δ1' | Δ2' | (swaps_pskl ps P0) ]
       (swaps_pskl ps P) ∼ (swaps_pskl ps Q) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ];
    intros * Hd Δ1' Δ2' S0' HD1 HD2 HS; simpl in *.
  - destruct (e_consis_supply_respect Hd HS) as [S1' [HS1 Hd']].
    exists S1'. split; [ exact HS1 | ].
    eapply e_consis_delta_respect; eassumption.
  - assert (H1 : swap_atoms a b Δ1 [=] swap_atoms a b Δ1) by reflexivity.
    assert (H2 : swap_atoms a b Δ2 [=] swap_atoms a b Δ2) by reflexivity.
    assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_consis_swap Hd H1 H2 Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ Hda _ _ _ HD1 HD2 HS)
      as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

(** [guess^TY] along a chain — the same iteration, on the judgement
    [Assign-SolveM] calls. *)
Lemma e_guess_mono_swaps : forall ps S0 P S1 Ξ τ,
  e_guess_mono S0 P S1 Ξ τ ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    e_guess_mono S0' (swaps_pskl ps P) S1' (swaps_aenv ps Ξ)
      (swaps_ptyp ps τ).
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_guess_mono_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_guess_mono_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

(* --------------------------------------------------------------------- *)
(*  §3b  ⭐ [guess^TY] IS DETERMINISTIC UP TO A FRESH RENAMING            *)
(*                                                                        *)
(*  [Assign-SolveM] is the level's one GENERATIVE row: the derivation's    *)
(*  invented block and the runner's are both drawn "fresh for [S0]" and    *)
(*  so differ by a renaming, which is where the induction's pair list      *)
(*  grows.  This is that renaming, and it is the ONE place in the level    *)
(*  where two arbitrary derivations are compared — legitimate here because *)
(*  [guess^TY] is syntax-directed (prop_guess.v §9's inversions are        *)
(*  unconditional), so the runner-sided doctrine has nothing to protect.   *)
(*                                                                        *)
(*  Induct on the SECOND derivation, leaving the first arbitrary.         *)
(*  Each renaming aligns the first derivation with the second's fixed     *)
(*  input supply, so the ordinary recursive hypothesis applies directly.  *)
(* --------------------------------------------------------------------- *)

Lemma e_guess_mono_rel : forall S0 P S1 Ξ A S1' Ξ' A',
  e_guess_mono S0 P S1 Ξ A ->
  e_guess_mono S0 P S1' Ξ' A' ->
  ftvar_in_pskl P [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_ptyp ps A = A'.
Proof.
  intros S0 P S1 Ξ A S1' Ξ' A' Hd Hd'.
  revert S1 Ξ A Hd.
  induction Hd' as
    [S0 α' Hα'
    |S0 S1' P Ξ' A' Dp' IH
    |S0 α
    |S0
    |S0 Sa' S1' P1 P2 Xa' Xb' Aa' Ab' D1' IH1 D2' IH2
    |S0 S1' P Ξ' Aa' β' Hβ' Dp' IH];
    intros S1 Ξ A Hd Hcov.
  - (* ghost — the row that INVENTS *)
    destruct (e_guess_mono_inv_ghost Hd) as [α [Hα [-> [-> ->]]]].
    exists ((α, α') :: nil). repeat apply conj.
    + intros ? ? [Heqp | []]. inversion Heqp; subst. split; assumption.
    + cbn [swaps_atoms]. rewrite swap_atoms_add.
      rewrite (swap_atoms_notin α α' S0 Hα Hα').
      replace (swap_atom α α' α) with α'
        by (unfold swap_atom; destruct (α == α); congruence).
      reflexivity.
    + rewrite swaps_aenv_app_dist, swaps_aenv_one_flex, swaps_aenv_nil.
      cbn [swaps_atom].
      replace (swap_atom α α' α) with α'
        by (unfold swap_atom; destruct (α == α); congruence).
      reflexivity.
    + rewrite swaps_ptyp_var_f. cbn [swaps_atom].
      replace (swap_atom α α' α) with α'
        by (unfold swap_atom; destruct (α == α); congruence).
      reflexivity.
  - (* univ_ghost *)
    pose proof (e_guess_mono_inv_univ_ghost Hd) as Dp.
    simpl in Hcov.
    exact (IH S1 Ξ A Dp Hcov).
  - (* var_f *)
    destruct (e_guess_mono_inv_var Hd) as [-> [-> ->]].
    exists nil. repeat apply conj; simpl; try reflexivity. intros ? ? [].
  - (* unit *)
    destruct (e_guess_mono_inv_unit Hd) as [-> [-> ->]].
    exists nil. repeat apply conj; simpl; try reflexivity. intros ? ? [].
  - (* arrow — the threading row *)
    destruct (e_guess_mono_inv_arrow Hd)
      as [Sa [Xa [Xb [Aa [Ab [-> [-> [D1 D2]]]]]]]].
    simpl in Hcov.
    destruct (IH1 Sa Xa Aa D1 ltac:(clear - Hcov; fsetdec))
      as [ps1 [Hav1 [HS1 [HX1 HA1]]]].
    assert (HP2 : swaps_pskl ps1 P2 = P2)
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (Heq2 : Sa' [=] swaps_atoms ps1 Sa) by (symmetry; exact HS1).
    destruct (e_guess_mono_swaps ps1 D2 Heq2) as [S2t [HS2t D2t]].
    rewrite HP2 in D2t.
    pose proof (e_guess_mono_supply_grows D1') as Hgr1'.
    destruct (IH2 S2t (swaps_aenv ps1 Xb) (swaps_ptyp ps1 Ab)
                  D2t ltac:(clear - Hcov Hgr1'; fsetdec))
      as [ps2 [Hav2 [HS2 [HX2 HA2]]]].
    (* what the SECOND renaming must leave alone: the first half's yield *)
    pose proof (e_guess_mono_generated_in_supply D1') as Hdom1'.
    pose proof (e_guess_mono_generated_ftvar D1') as Hftv1'.
    pose proof (e_guess_mono_ftv D1') as HftA1'.
    assert (HX1' : swaps_aenv ps2 Xa' = Xa')
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hdom1' Hftv1'; fsetdec).
    assert (HA1' : swaps_ptyp ps2 Aa' = Aa')
      by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hdom1' HftA1' Hcov Hgr1'; fsetdec).
    exists (ps1 ++ ps2). repeat apply conj.
    + intros a0 b0 Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exact (Hav1 a0 b0 Hin).
      * destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
        split; clear - Ha0 Hb0 Hgr1'; fsetdec.
    + rewrite swaps_atoms_app. rewrite <- HS2.
      apply swaps_atoms_cong. symmetry. exact HS2t.
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_ptyp_app, !swaps_ptyp_arrow, HA1, HA2, HA1'.
      reflexivity.
  - (* all_syn — the two openers are paired first, by ONE transposition *)
    destruct (e_guess_mono_inv_all_syn Hd) as [β [Aa [Hβ [-> Dp]]]].
    simpl in Hcov.
    assert (Heqs : add β' S0 [=] swap_atoms β β' (add β S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β β' S0 Hβ Hβ').
      unfold swap_atom. destruct (β == β); [ | congruence ]. reflexivity. }
    destruct (e_guess_mono_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_pskl_open_var in Dpt.
    rewrite (swap_pskl_fresh_id β β' P) in Dpt;
      [ | clear - Hcov Hβ; fsetdec | clear - Hcov Hβ'; fsetdec ].
    replace (swap_atom β β' β) with β' in Dpt
      by (unfold swap_atom; destruct (β == β); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β'))
      as Hup.
    destruct (IH S1t (swap_aenv β β' Ξ) (swap_ptyp β β' Aa)
                 Dpt ltac:(clear - Hup Hcov; simpl in *; fsetdec))
      as [ps' [Hav' [HS' [HX' HA']]]].
    exists ((β, β') :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_ptyp swap_ptyp]. rewrite swap_ptyp_close.
      replace (swap_atom β β' β) with β'
        by (unfold swap_atom; destruct (β == β); congruence).
      rewrite swaps_ptyp_all, swaps_ptyp_close, HA'.
      f_equal. f_equal. apply swaps_atom_notin.
      intros a0 b0 Hin. destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; [ clear - Ha0 | clear - Hb0 ]; fsetdec.
Qed.

(* ===================================================================== *)
(*  §4  ROOT INVERSIONS — the case backbone, machine-checked              *)
(*                                                                        *)
(*  §8c.10b settled by INSPECTION that every (pattern, subject) shape     *)
(*  pair but three admits exactly ONE consistency rule, so the runner's   *)
(*  first-match commits to the derivation's root.  These are that audit   *)
(*  as lemmas: one per clause of the runner's dispatch, each turning a    *)
(*  derivation at the clause's shape into that rule's premises.           *)
(*                                                                        *)
(*  ⭐ NONE of them needs ghost-freeness.  [U-Ghost] demands the SUBJECT   *)
(*  be literally [◇] and [U-GhostR] the PATTERN, so at any concrete       *)
(*  shape they cannot fire at all; ghost-freeness is what keeps the        *)
(*  recursion away from the two clauses where they can (§8c.10b's         *)
(*  divergence), not what makes these inversions unique.                  *)
(*                                                                        *)
(*  The three genuinely ambiguous pairs are the ones the runner decides   *)
(*  with a flexibility TEST, and they come out as disjunctions whose      *)
(*  branches are EXCLUSIVE — [e_assign_target_flex] (prop_consis.v §8)    *)
(*  is what makes the assign branch imply the very [a_flex_tvar] the      *)
(*  other branch's [a_non_flex] denies.                                    *)
(* ===================================================================== *)

(** After [inversion], the rows that COULD have matched the shape but
    demand [guarded_pskl] of a ∀ / ⫯ / ◇ leave that demand behind; it is
    never derivable, so one [inversion] each closes them. *)
Local Ltac kill_unguarded :=
  repeat match goal with
         | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
         | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
         | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
         end.

(* --- the UNAMBIGUOUS shape pairs: exactly one rule fires --- *)

Lemma e_consis_inv_arrow : forall Δ1 Δ2 S0 Θ0 P0a P0b P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ]
     (pskl_arrow P1 P2) ∼ Q ⊣ Θ1 }}e ->
  exists Sm Θm Q1 Q2,
    Q = pskl_arrow Q1 Q2 /\
    {{ S0 ↝ Sm ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θm }}e /\
    {{ Sm ↝ S1 ⊨ Θm ⊢[ Δ1 | Δ2 | P0b ] P2 ∼ Q2 ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_unit : forall Δ1 Δ2 S0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ] pskl_unit ∼ Q ⊣ Θ1 }}e ->
  Q = pskl_unit /\ S1 = S0 /\ Θ1 = Θ0.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_forall_inh : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
     (pskl_all_syn P) ∼ Q ⊣ Θ1 }}e ->
  exists α Qb,
    α `notin` S0 /\ Q = pskl_all_syn (close_pskl_wrt_pskl α Qb) /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | (add α Δ2)
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Qb
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_forall_syn : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
     (pskl_all_syn P) ∼ Q ⊣ Θ1 }}e ->
  exists α Qb,
    α `notin` S0 /\ Q = pskl_all_syn (close_pskl_wrt_pskl α Qb) /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ Δ1 | (add α Δ2) | (pskl_univ_ghost P0) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Qb
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_univ_ghost : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
     (pskl_univ_ghost P) ∼ Q ⊣ Θ1 }}e ->
  exists Qb,
    Q = pskl_univ_ghost Qb /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Qb ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto. Qed.

Lemma e_consis_inv_univ_ghost1 : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
     (pskl_univ_ghost P) ∼ Q ⊣ Θ1 }}e ->
  exists α Qb,
    α `notin` S0 /\ Q = pskl_all_syn (close_pskl_wrt_pskl α Qb) /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | Δ2
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (pskl_univ_ghost P) ∼ Qb ⊣ ((α ~ abind_tvar) ++ Θ1) }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_univ_ghost2_unit : forall Δ1 Δ2 S0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ]
     (pskl_univ_ghost P) ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ] P ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_univ_ghost2_arrow : forall Δ1 Δ2 S0 Θ0 P0a P0b P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ]
     (pskl_univ_ghost P) ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ] P ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_univ_ghost_r_unit : forall Δ1 Δ2 S0 Θ0 P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
     pskl_unit ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] pskl_unit ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_univ_ghost_r_arrow : forall Δ1 Δ2 S0 Θ0 P0 P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
     (pskl_arrow P1 P2) ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_arrow P1 P2) ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

(* --- a flexible PATTERN against a non-variable subject: only U-FlexR --- *)

Lemma e_consis_inv_flex_r : forall Δ1 Δ2 S0 Θ0 α P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ] P ∼ Q ⊣ Θ1 }}e ->
  (forall β, P <> pskl_var_f β) -> P <> pskl_ghost ->
  (forall Pb, P <> pskl_univ_ghost Pb) ->
  Q = pskl_var_f α /\ a_non_flex Θ0 P /\
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P ⊣ Θ1 }}e.
Proof.
  intros * Hd Hnv Hnh Hnt. inversion Hd; subst; kill_unguarded;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | exfalso; eapply Hnt; reflexivity ].
  all: (split; [ reflexivity | split; assumption ]).
Qed.

(* --- a flexible SUBJECT against a non-variable pattern: only U-FlexL --- *)

Lemma e_consis_inv_flex_l : forall Δ1 Δ2 S0 Θ0 α P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  (forall β, P0 <> pskl_var_f β) -> P0 <> pskl_ghost ->
  (forall Pb, P0 <> pskl_univ_ghost Pb) ->
  Q = pskl_var_f α /\ a_non_flex Θ0 P0 /\
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P0 ⊣ Θ1 }}e.
Proof.
  intros * Hd Hnv Hnh Hnt. inversion Hd; subst; kill_unguarded;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | exfalso; eapply Hnt; reflexivity ].
  all: (split; [ reflexivity | split; assumption ]).
Qed.

(* --- the three pairs the runner resolves by a flexibility TEST --- *)

Lemma e_consis_inv_var_univ_ghost : forall Δ1 Δ2 S0 Θ0 β P1 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ]
     (pskl_univ_ghost P1) ∼ Q ⊣ Θ1 }}e ->
  (a_flex_tvar Θ0 β /\ Q = pskl_var_f β /\
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] β ≔ (pskl_univ_ghost P1) ⊣ Θ1 }}e)
  \/ (a_non_flex Θ0 (pskl_var_f β) /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ] P1 ∼ Q ⊣ Θ1 }}e).
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded.
  - right; auto.
  - left; repeat split; auto. eapply e_assign_target_flex; eassumption.
Qed.

Lemma e_consis_inv_univ_ghost_var : forall Δ1 Δ2 S0 Θ0 α P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
     (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  (a_flex_tvar Θ0 α /\ Q = pskl_var_f α /\
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ (pskl_univ_ghost P0) ⊣ Θ1 }}e)
  \/ (a_non_flex Θ0 (pskl_var_f α) /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_var_f α) ∼ Q ⊣ Θ1 }}e).
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded.
  - left; repeat split; auto. eapply e_assign_target_flex; eassumption.
  - right; auto.
Qed.

Lemma e_consis_inv_var_var : forall Δ1 Δ2 S0 Θ0 α β Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ]
     (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  (* U-Rigid *)
  (α = β /\ binds α abind_tvar Θ0 /\ Q = pskl_var_f α /\
     S1 = S0 /\ Θ1 = Θ0)
  (* U-Flex *)
  \/ (Q = pskl_var_f α /\ {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e)
  (* U-FlexL — the SUBJECT variable is assigned *)
  \/ (a_non_flex Θ0 (pskl_var_f β) /\ Q = pskl_var_f α /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ (pskl_var_f β) ⊣ Θ1 }}e)
  (* U-FlexR — the PATTERN variable is assigned *)
  \/ (a_non_flex Θ0 (pskl_var_f α) /\ Q = pskl_var_f β /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] β ≔ (pskl_var_f α) ⊣ Θ1 }}e).
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded.
  - left; repeat split; auto.
  - right; left; auto.
  - right; right; left; auto.
  - right; right; right; auto.
Qed.

(* --- the two WALKS: one inversion per head shape --------------------- *)
(*                                                                        *)
(*  The context-walking clauses of the dispatch.  Each is unambiguous     *)
(*  once the head's BINDING SHAPE is fixed, except at a bare flexible     *)
(*  head, where [Assign-Depend] and [Assign-Skip] split on the same       *)
(*  occurrence test the runner performs.                                  *)

(** [Flex-Flex-Skip'] fires at a rigid / term-variable head only; wherever
    the head is a FLEXIBLE its binding-shape premise refutes. *)
Local Ltac kill_skip_other :=
  match goal with
  | H : _ = abind_tvar \/ (exists _, _ = abind_var_typ _) \/
        (exists _, _ = abind_var_skl _) |- _ =>
      solve [ destruct H as [Hb | [[? Hb] | [? Hb]]]; discriminate ]
  end.

Lemma e_assign_inv_nil : forall S0 Ξ α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ nil ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

(** The head IS the target: [Assign-UnivGhost-Id] against
    [Assign-SolveM], and the occurs check separates them. *)
Lemma e_assign_inv_flex_self : forall S0 Θ0 Ξ α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  (Ξ = nil /\ P = pskl_univ_ghost (pskl_var_f α) /\ S1 = S0 /\
     Θ1 = (α ~ abind_flex_mono) ++ Θ0)
  \/ (α `notin` ftvar_in_pskl P /\
      exists βs τ, e_guess_mono S0 P S1 βs τ /\ mono_ptyp τ /\
        Θ1 = (α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0).
Proof.
  intros * Hd. inversion Hd; subst; try congruence.
  - left; split; [ reflexivity
                 | split; [ reflexivity | split; reflexivity ] ].
  - right; split; [ assumption | eauto 10 ].
Qed.

Lemma e_assign_inv_flex_other : forall S0 Θ0 Ξ α β P S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  (β `in` ftvar_in_pskl P /\
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ (Ξ ++ (β ~ abind_flex_mono)) ] α ≔ P ⊣ Θ1 }}e)
  \/ (β `notin` ftvar_in_pskl P /\ exists Θ1',
        Θ1 = (β ~ abind_flex_mono) ++ Θ1' /\
        {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e).
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence.
  - left; split; assumption.
  - right; split; [ assumption | eauto ].
Qed.

Lemma e_assign_inv_def : forall S0 Θ0 Ξ α β τ P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α /\
  exists Θ1' Q, Θ1 = (β ~ abind_flex_mono_def τ) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ (Ξ ++ Θ0) ⊢[ empty | empty
         | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) ]
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ∼ Q
       ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. split; [ assumption | eauto ]. Qed.

Lemma e_assign_inv_tvar : forall S0 Θ0 Ξ α β P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  β `notin` ftvar_in_pskl P /\ exists Θ1',
    Θ1 = (β ~ abind_tvar) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. split; [ assumption | eauto ]. Qed.

Lemma e_assign_inv_var_typ : forall S0 Θ0 Ξ α x A P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((x ~ abind_var_typ A) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (x ~ abind_var_typ A) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma e_assign_inv_var_skl : forall S0 Θ0 Ξ α x Q P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((x ~ abind_var_skl Q) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (x ~ abind_var_skl Q) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

(** The unify walk.  All five are stated at [α <> β]: at [α = β] the
    runner commits to [Flex-Flex-Id] whatever the head is, and what
    answers that arm is §5's reflexivity, not an inversion. *)
Lemma e_unify_inv_nil : forall S0 α β S1 Θ1,
  {{ S0 ↝ S1 ⊨ nil ⊲ α ≈ᵘ β ⊣ Θ1 }}e -> False.
Proof.
  intros * Hd. inversion Hd; subst.
  destruct H as [Hb | [τ Hb]]; inversion Hb.
Qed.

Lemma e_unify_inv_flex_l : forall S0 Θ0 α β S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  a_flex_tvar Θ0 β /\ S1 = S0 /\
  Θ1 = (α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0.
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence; try kill_skip_other.
  split; [ assumption | split; reflexivity ].
Qed.

Lemma e_unify_inv_flex_r : forall S0 Θ0 α β S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  a_flex_tvar Θ0 α /\ S1 = S0 /\
  Θ1 = (β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0.
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence; try kill_skip_other.
  split; [ assumption | split; reflexivity ].
Qed.

Lemma e_unify_inv_flex_skip : forall S0 Θ0 γ α β S1 Θ1,
  α <> β -> γ <> α -> γ <> β ->
  {{ S0 ↝ S1 ⊨ ((γ ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (γ ~ abind_flex_mono) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1' }}e.
Proof.
  intros * Hne H1 H2 Hd.
  inversion Hd; subst; try congruence; try kill_skip_other. eauto.
Qed.

Lemma e_unify_inv_def : forall S0 Θ0 γ τ α β S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((γ ~ abind_flex_mono_def τ) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  a_flex_tvar ((γ ~ abind_flex_mono_def τ) ++ Θ0) α /\
  a_flex_tvar ((γ ~ abind_flex_mono_def τ) ++ Θ0) β /\
  exists Θ1' Q, Θ1 = (γ ~ abind_flex_mono_def τ) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty
         | (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f β))) ]
       (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f α))) ∼ Q
       ⊣ Θ1' }}e.
Proof.
  intros * Hne Hd.
  inversion Hd; subst; try congruence; try kill_skip_other.
  split; [ assumption | split; [ assumption | eauto ] ].
Qed.

Lemma e_unify_inv_other : forall S0 Θ0 c b α β S1 Θ1,
  α <> β ->
  (b = abind_tvar \/ (exists A, b = abind_var_typ A) \/
   (exists Q, b = abind_var_skl Q)) ->
  {{ S0 ↝ S1 ⊨ ((c ~ b) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (c ~ b) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1' }}e.
Proof.
  intros * Hne Hb Hd.
  destruct Hb as [-> | [[A ->] | [Q ->]]];
    inversion Hd; subst; try congruence; eauto.
Qed.

(* ===================================================================== *)
(*  §5  ⭐ [α̂ ≈ᵘ α̂] MOVES NOTHING — under the runner's own discipline     *)
(*                                                                        *)
(*  [Flex-Flex-Id] carries no [α <> β], so at [α̂ ≈ᵘ α̂] it OVERLAPS both   *)
(*  [Flex-Flex-Skip] (at an undefined non-matching head) and              *)
(*  [Flex-Flex-Assign] (at a DEFINED one) — and the runner commits to     *)
(*  [Flex-Flex-Id], returning the supply AND the context untouched        *)
(*  (def_consis_impl.v:619).  So the level needs that overlap to be       *)
(*  BENIGN in both components, which is what this says.                    *)
(*                                                                        *)
(*  ⭐ WHY IT IS TRUE, AND WHY [aenv_defs_mono] IS LOAD-BEARING.           *)
(*  [Flex-Flex-Assign]'s premise is a consistency of a DEFINITION PAYLOAD *)
(*  with itself.  A payload is a [ptyp], so no ◇ and no ⫯ can appear —    *)
(*  which already gives the context.  For the SUPPLY one needs more: a ∀  *)
(*  payload's [ForallInh] draws an opener and the supply grows.  The      *)
(*  context discipline the runner already demands rules that out — a      *)
(*  defined flexible's payload is a MONOTYPE, and a monotype's skeleton   *)
(*  view has no ∀ either, so only Unit / Rigid / Arrow / Flex can fire.   *)
(*                                                                        *)
(*  The motives travel together: the consis motive's [FlexL]/[FlexR] rows *)
(*  are refuted by §8's [e_assign_target_flex], which says the assign     *)
(*  walk can only have reached [α] through a flex-bound head — so the     *)
(*  ASSIGN motive here is [True].                                          *)
(* ===================================================================== *)

Lemma e_unify_consis_refl_mono :
  (forall S0 Θ0 Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e -> True) /\
  (forall S0 Θ0 α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
     α = β -> aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0) /\
  (forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
     P0 = P -> (exists A, P = ptyp_to_pskl A /\ mono_ptyp A) ->
     aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0).
Proof.
  apply e_assign_unify_consis_mutind.
  (* ---- assign: superseded by §8's [e_assign_target_flex] ---- *)
  1-8: intros; exact I.
  (* ---- unify ---- *)
  - (* Flex-Flex-Id *) intros S Θ0 α Hf Heq HD. split; reflexivity.
  - (* Flex-Flex-L: needs α <> β *)
    intros S Θ0 α β Hne Hf Heq HD. contradiction.
  - (* Flex-Flex-R *)
    intros S Θ0 α β Hne Hf Heq HD. contradiction.
  - (* Flex-Flex-Assign — a SELF-consistency of a MONOTYPE payload *)
    intros S0 S1 Θ0 Θ1 α1 τ α β Q Hfa Hfb Hd IH Heq HD. subst.
    destruct (aenv_defs_mono_cons_inv HD) as [Hmτ HD0].
    destruct IH as [-> ->];
      [ reflexivity
      | eexists; split;
        [ reflexivity
        | apply mono_ptyp_subst; [ apply mono_ptyp__var | exact Hmτ ] ]
      | exact HD0
      | ].
    split; reflexivity.
  - (* Flex-Flex-Skip *)
    intros S0 S1 Θ0 Θ1 α1 α β Hne1 Hne2 Hd IH Heq HD. subst.
    destruct (aenv_defs_mono_cons_inv HD) as [_ HD0].
    destruct IH as [-> ->]; [ reflexivity | exact HD0 | ].
    split; reflexivity.
  - (* Flex-Flex-Skip' *)
    intros S0 S1 Θ0 Θ1 c b α β Hb Hd IH Heq HD. subst.
    destruct (aenv_defs_mono_cons_inv HD) as [_ HD0].
    destruct IH as [-> ->]; [ reflexivity | exact HD0 | ].
    split; reflexivity.
  (* ---- consis ---- *)
  - (* Ghost *)
    intros Δ1 Δ2 S Θ0 P0 Hdis Heq Hsh HD. split; reflexivity.
  - (* Unit *) intros Δ1 Δ2 S Θ0 Heq Hsh HD. split; reflexivity.
  - (* Rigid *) intros Δ1 Δ2 S Θ0 α Hb Heq Hsh HD. split; reflexivity.
  - (* Arrow — both halves are self-consistencies of a monotype half *)
    intros Δ1 Δ2 S0 S1 S2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2
           Hd1 IH1 Hd2 IH2 Heq Hsh HD.
    destruct Hsh as [Ash [He Hmo]]; destruct Ash; simpl in He;
      try discriminate.
    inversion He; subst. inversion Heq; subst. inversion Hmo; subst.
    destruct IH1 as [-> ->];
      [ reflexivity
      | eexists; split; [ reflexivity | assumption ] | exact HD | ].
    destruct IH2 as [-> ->];
      [ reflexivity
      | eexists; split; [ reflexivity | assumption ] | exact HD | ].
    split; reflexivity.
  - (* ForallInh — a monotype has no ∀ *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hα Hd IH Heq Hsh HD.
    destruct Hsh as [Ash [He Hmo]]; destruct Ash; simpl in He;
      try discriminate; inversion Hmo.
  - (* ForallSyn — [⫯P0] against [∀P] *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hα Hd IH Heq Hsh HD. discriminate.
  - (* UnivGhost — a ⫯ is no monotype view *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hd IH Heq Hsh HD.
    exfalso. destruct Hsh as [Ash [He Hmo]]; destruct Ash; discriminate.
  - (* UnivGhost1 *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hα Hd IH Heq Hsh HD. discriminate.
  - (* UnivGhost2 — the subject is a ⫯ *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hg Hnf Hd IH Heq Hsh HD.
    exfalso. destruct Hsh as [Ash [He Hmo]]; destruct Ash; discriminate.
  - (* Flex — pattern and subject are the SAME variable *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α β Hd IH Heq Hsh HD.
    inversion Heq; subst.
    destruct IH as [-> ->]; [ reflexivity | exact HD | ].
    split; reflexivity.
  - (* FlexL — [nonflex] against the assign walk's own finding *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P0 Hnf Hnhole Hd IH Heq Hsh HD.
    exfalso. subst. destruct Hnf as [_ Hf]. apply Hf.
    apply a_flex_var_iff_tvar. eapply e_assign_target_flex; eassumption.
  - (* FlexR — the mirror *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P Hnf Hnhole Hd IH Heq Hsh HD.
    exfalso. subst. destruct Hnf as [_ Hf]. apply Hf.
    apply a_flex_var_iff_tvar. eapply e_assign_target_flex; eassumption.
  - (* GhostR *)
    intros Δ1 Δ2 S Θ0 P Hdis Heq Hsh HD. split; reflexivity.
  - (* UnivGhostR *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hg Hnf Hd IH Heq Hsh HD.
    exfalso. subst.
    destruct Hsh as [Ash [He Hmo]]; destruct Ash; discriminate.
Qed.

(** What the runner's [Flex-Flex-Id] arm consumes. *)
Corollary e_unify_refl : forall S0 Θ0 α S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ α ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros. eapply (proj1 (proj2 e_unify_consis_refl_mono));
    [ eassumption | reflexivity | assumption ].
Qed.

(* ===================================================================== *)
(*  §6  THE MOTIVE                                                        *)
(* ===================================================================== *)

Definition consis_call_answer {S0 : supply} {Θ : aenv} {c : consis_call}
    (o : option (sig (consis_call_spec S0 Θ c))) : option consis_result :=
  match o with None => None | Some r => Some (proj1_sig r) end.

Definition consis_call_run (S0 : supply) (Θ : aenv) (c : consis_call)
    (Sd : supply) (Θd : aenv) (Qd : pskl) : Prop :=
  match c with
  | consis_call_assign Ξ α P => {{ S0 ↝ Sd ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θd }}e
  | consis_call_unify α β    => {{ S0 ↝ Sd ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θd }}e
  | consis_call_consis Δ1 Δ2 P0 P =>
      {{ S0 ↝ Sd ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Qd ⊣ Θd }}e
  end.

Definition consis_call_out_rel (c : consis_call) (Qd Qr : pskl) : Prop :=
  match c with
  | consis_call_consis _ _ _ _ => Qd = Qr
  | _                          => True
  end.

Definition consis_call_uniq (Θ : aenv) (c : consis_call) : Prop :=
  match c with
  | consis_call_assign Ξ _ _ => uniq (Ξ ++ Θ)
  | _                        => uniq Θ
  end.

Definition consis_call_cover (Θ : aenv) (c : consis_call) : atoms :=
  match c with
  | consis_call_assign Ξ _ P => ftvar_in_aenv (Ξ ++ Θ) ∪ ftvar_in_pskl P
  | consis_call_unify _ _    => ftvar_in_aenv Θ
  | consis_call_consis Δ1 Δ2 P0 P =>
      ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P ∪ Δ1 ∪ Δ2
  end.

Definition consis_call_complete (S0 : supply) (Θ : aenv) (c : consis_call)
    : Prop :=
  forall (Hlc : consis_call_lc c) (HD : consis_call_defs_mono Θ c)
         (H : e_consis_call_order S0 Θ c),
    consis_call_uniq Θ c ->
    consis_call_cover Θ c [<=] S0 ->
    forall Sd Θd Qd, consis_call_run S0 Θ c Sd Θd Qd ->
    exists r ps,
      consis_call_answer (e_consis_call_impl c S0 Θ Hlc HD H) = Some r
      /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
      /\ swaps_atoms ps Sd [=] cs_supply r
      /\ swaps_aenv ps Θd = cs_ctx r
      /\ consis_call_out_rel c (swaps_pskl ps Qd) (cs_out r).

(* ===================================================================== *)
(*  §7  THE MAIN INDUCTION                                                *)
(* ===================================================================== *)

Local Ltac kill_ccall Hmot Hu Hcov Hder q r Hr ps Hav HS HT HQ :=
  match goal with
  | |- context [ e_consis_call_impl ?c ?S ?T ?hl ?hd ?h ] =>
      let Hx := fresh "Hx" in
      let Hcl := fresh "Hcl" in
      let rr := fresh "rr" in
      destruct (Hmot hl hd h Hu Hcov _ _ q Hder)
        as [r [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_consis_call_impl c S T hl hd h) as [ [rr Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx; cbn [consis_call_answer] in Hx;
      [ inversion Hx; subst; clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

Ltac head_fresh Hav Hcov :=
  apply swaps_aenv_fresh_id; intros a0 b0 Hin;
  let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
  destruct (Hav a0 b0 Hin) as [Ha0 Hb0]; split;
  clear - Ha0 Hb0 Hcov; repeat rewrite ftvar_in_aenv_app in Hcov;
  simpl in *; fsetdec.

(** A [pskl_var_f]-shaped output: the runner answers with the variable it
    was handed, and the chain fixes it because it is in the supply. *)
Local Ltac out_var_id Hav Hcov :=
  cbn [cs_out proj1_sig]; rewrite swaps_pskl_var_f; f_equal;
  apply swaps_atom_notin; intros a0 b0 Hin;
  let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
  let Heq := fresh "Heq" in
  destruct (Hav a0 b0 Hin) as [Ha0 Hb0];
  split; intro Heq; subst; clear - Ha0 Hb0 Hcov; simpl in *; fsetdec.

(** The flexibility test the runner performs, decided by the derivation's
    own assign walk. *)
Local Ltac flex_test_true Hft :=
  let Hfb := fresh "Hfb" in
  lazymatch goal with
  | |- context [ sumbool_of_bool (flex_bound_ck ?T ?a) ] =>
      destruct (sumbool_of_bool (flex_bound_ck T a)) as [Hfb | Hfb];
      [ | exfalso; eapply flex_bound_ck_not_flex_tvar;
          [ exact Hfb | exact Hft ] ]
  end.

(** [Assign-SolveM]'s three leaves — the runner's [Ξ]×[P] dispatch reaches
    the same code from all of them, so the script is one tactic. *)
(** [Assign-SolveM]'s leaves — the runner's [Ξ] × [P] dispatch reaches the
    same code from all of them, so the script is one tactic. *)
Local Ltac do_solve_m Hocc Hg Hmt Hcov rg Hgs ps Hav HSg HXg HAg :=
  match goal with
  | |- context [ sumbool_of_bool (mem ?a (ftvar_in_pskl ?p)) ] =>
      let Hmem := fresh "Hmem" in
      destruct (sumbool_of_bool (mem a (ftvar_in_pskl p))) as [Hmem | Hmem];
      [ exfalso; apply mem_true_in in Hmem; contradiction | ]
  end;
  cbv beta iota;
  match goal with
  | |- context [ e_guess_mono_impl ?s ?p ?h ] =>
      destruct (e_guess_mono_impl s p h) as [rg Hgs];
      unfold guess_spec in Hgs
  end;
  cbv beta iota;
  destruct (e_guess_mono_rel Hg Hgs
              ltac:(clear - Hcov; repeat rewrite ftvar_in_aenv_app in Hcov;
                    simpl in *; fsetdec))
    as [ps [Hav [HSg [HXg HAg]]]];
  match goal with
  | |- context [ sumbool_of_bool (mono_ck (gr_type ?r)) ] =>
      let Hmc := fresh "Hmc" in
      destruct (sumbool_of_bool (mono_ck (gr_type r))) as [Hmc | Hmc];
      [ | exfalso; rewrite <- HAg in Hmc;
          contradict Hmc; apply Bool.not_false_iff_true;
          apply mono_ck_complete; apply mono_ptyp_swaps; exact Hmt ]
  end;
  cbv beta iota;
  let Hain := fresh "Hain" in
  assert (Hain : True) by exact I;
  eexists; exists ps;
  split; [ reflexivity | ];
  repeat apply conj;
  [ exact Hav
  | cbn [cs_supply proj1_sig]; exact HSg
  | cbn [cs_ctx proj1_sig];
    rewrite swaps_aenv_app_dist; rewrite swaps_aenv_app_dist;
    rewrite swaps_aenv_one_def, HXg, HAg;
    rewrite (swaps_atom_notin ps)
      by (intros a0 b0 Hin;
          let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
          let Heq := fresh "Heq" in
          destruct (Hav a0 b0 Hin) as [Ha0 Hb0];
          split; intro Heq; subst;
          clear - Ha0 Hb0 Hcov;
          repeat rewrite ftvar_in_aenv_app in Hcov; simpl in *; fsetdec);
    rewrite (swaps_aenv_fresh_id ps)
      by (intros a0 b0 Hin;
          let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
          destruct (Hav a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov;
          repeat rewrite ftvar_in_aenv_app in *; simpl in *; fsetdec);
    reflexivity
  | exact I ].

(** Every head shape reaches the runner's [Flex-Flex-Id] arm the same way:
    the [α == β] test succeeds, and §5's reflexivity says the derivation
    left the supply AND the context where they were. *)
Local Ltac do_flex_id HD Hd :=
  let Hs := fresh "Hs" in let Ht := fresh "Ht" in
  destruct (e_unify_refl Hd HD) as [Hs Ht]; subst;
  match goal with
  | |- context [ sumbool_of_bool (flex_bound_ck ?T ?a) ] =>
      let Hfb := fresh "Hfb" in
      destruct (sumbool_of_bool (flex_bound_ck T a)) as [Hfb | Hfb];
      [ | exfalso; eapply flex_bound_ck_not_flex_tvar;
          [ exact Hfb | exact (proj1 (e_unify_target_flex Hd)) ] ]
  end;
  cbv beta iota;
  eexists; exists (@nil (atom * atom));
  split; [ reflexivity | ];
  repeat apply conj; [ intros ? ? [] | cbn [swaps_atoms cs_supply proj1_sig]; reflexivity
          | cbn [swaps_aenv cs_ctx proj1_sig]; reflexivity | exact I ].

(** The runner's binary tests are DEPENDENT matches (the branch's Equations
    obligation reads the equality), so [destruct (x == y)] does not abstract
    them — destruct the GOAL's own scrutinee. *)
(** ⚠️ The runner's atom tests are CONVOYED (Equations compiles
    [match x == y with …] with the scrutinee in the return type), so
    [destruct (x == y)] on a term of one's own does not abstract the goal's
    occurrence — the goal's OWN term has to be destructed.  ⚠️⚠️ And the
    pattern must stay FIRST-ORDER: matching [context [match ?e with left _
    => _ | right _ => _ end]] against a clause body of this size does not
    terminate in any useful time (measured, >800 s). *)
Local Ltac split_eqdec Hl Hr :=
  lazymatch goal with
  | |- context [ @eq_dec ?T ?E ?x ?y ] =>
      destruct (@eq_dec T E x y) as [ Hl | Hr ]
  end.

(** U-FlexL at a concrete non-variable PATTERN: the runner assigns the
    subject's flexible and answers with it. *)
Local Ltac do_flex_l Hmot Hd Hu Hcov :=
  let Hnf := fresh "Hnf" in let Da := fresh "Da" in
  let Hft := fresh "Hft" in let Hcov0 := fresh "Hcov0" in
  let r := fresh "r" in let Hr := fresh "Hr" in
  let ps := fresh "ps" in let Hav := fresh "Hav" in
  let HS := fresh "HS" in let HT := fresh "HT" in let HQ := fresh "HQ" in
  destruct (e_consis_inv_flex_l Hd ltac:(intros; discriminate)
              ltac:(discriminate) ltac:(intros; discriminate))
    as [-> [Hnf Da]];
  pose proof (e_assign_target_flex Da) as Hft;
  flex_test_true Hft; cbv beta iota;
  lazymatch goal with
  | |- context [ e_consis_call_impl (consis_call_assign nil ?a ?p)
                   ?s ?t ?x ?y ?zz ] =>
      assert (Hcov0 : ftvar_in_aenv (nil ++ t) ∪ ftvar_in_pskl p [<=] s)
        by (clear - Hcov; simpl in *; fsetdec)
  end;
  kill_ccall Hmot Hu Hcov0 Da pskl_unit r Hr ps Hav HS HT HQ;
  eexists; exists ps;
  split; [ reflexivity | ];
  repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
          | cbn [cs_ctx proj1_sig]; exact HT | ];
  out_var_id Hav Hcov.

(** ⭐ THE GHOST CELLS.  Since the [<> ◇] dispatch guards landed on
    [U-FlexL]/[U-FlexR] (algo/def_rules.v) every cell with a [◇] on one
    side admits EXACTLY ONE rule — the ghost one, which is the rule the
    runner takes — so the case is: invert (a single-rule inversion from
    §2), discharge the rule's own
    Δ-disjointness test that the runner performs, and answer with the
    input.  The swap chain is EMPTY: nothing was invented. *)
Local Ltac do_ghost_cell Hdis :=
  match goal with
  | |- context [ sumbool_of_bool (is_empty ?S) ] =>
      let He := fresh "He" in
      destruct (sumbool_of_bool (is_empty S)) as [He | He];
      [ cbv beta iota
      | exfalso; rewrite AtomSetImpl.is_empty_1 in He;
        [ discriminate | clear - Hdis; simpl in *; fsetdec ] ]
  end;
  eexists; exists (@nil (atom * atom));
  split; [ reflexivity | ];
  repeat apply conj; [ intros ? ? []
          | cbn [swaps_atoms cs_supply proj1_sig]; reflexivity
          | cbn [swaps_aenv cs_ctx proj1_sig]; reflexivity
          | cbn [swaps_pskl cs_out proj1_sig]; reflexivity ].

(** The ⫯-stripping rows: the runner passes the recursive answer through
    verbatim. *)
Local Ltac do_pass Hmot Hd Hu Hcov Qd :=
  let Hcov0 := fresh "Hcov0" in
  let r := fresh "r" in let Hr := fresh "Hr" in
  let ps := fresh "ps" in let Hav := fresh "Hav" in
  let HS := fresh "HS" in let HT := fresh "HT" in let HQ := fresh "HQ" in
  lazymatch goal with
  | |- context [ e_consis_call_impl ?c ?s ?t ?x ?y ?zz ] =>
      assert (Hcov0 : consis_call_cover t c [<=] s)
        by (clear - Hcov;
            cbn [consis_call_cover ftvar_in_pskl] in *; fsetdec)
  end;
  kill_ccall Hmot Hu Hcov0 Hd Qd r Hr ps Hav HS HT HQ;
  exists r, ps;
  split; [ reflexivity | ];
  repeat apply conj; [ exact Hav | exact HS | exact HT | exact HQ ].

(** U-FlexR at a concrete non-variable subject: the runner assigns the
    pattern's flexible and answers with it. *)
Local Ltac do_flex_r Hmot Hd Hu Hcov :=
  let Hnf := fresh "Hnf" in let Da := fresh "Da" in
  let Hft := fresh "Hft" in let Hcov0 := fresh "Hcov0" in
  let r := fresh "r" in let Hr := fresh "Hr" in
  let ps := fresh "ps" in let Hav := fresh "Hav" in
  let HS := fresh "HS" in let HT := fresh "HT" in let HQ := fresh "HQ" in
  destruct (e_consis_inv_flex_r Hd ltac:(intros; discriminate)
              ltac:(discriminate) ltac:(intros; discriminate))
    as [-> [Hnf Da]];
  pose proof (e_assign_target_flex Da) as Hft;
  flex_test_true Hft; cbv beta iota;
  lazymatch goal with
  | |- context [ e_consis_call_impl (consis_call_assign nil ?a ?p)
                   ?s ?t ?x ?y ?zz ] =>
      assert (Hcov0 : ftvar_in_aenv (nil ++ t) ∪ ftvar_in_pskl p [<=] s)
        by (clear - Hcov; simpl in *; fsetdec)
  end;
  kill_ccall Hmot Hu Hcov0 Da pskl_unit r Hr ps Hav HS HT HQ;
  eexists; exists ps;
  split; [ reflexivity | ];
  repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
          | cbn [cs_ctx proj1_sig]; exact HT | ];
  cbn [cs_out proj1_sig]; out_var_id Hav Hcov.

(** Close a recursive consistency result after moving its fresh binder.
    The recursive swap chain fixes the new binder because it avoids the
    extended supply. *)
Lemma consis_swaps_close : forall S Sd St Θ Q α β ps r,
  α `notin` S -> β `notin` S ->
  (forall a b, In (a, b) ps -> a `notin` add β S /\ b `notin` add β S) ->
  St [=] swap_atoms α β Sd -> swaps_atoms ps St [=] cs_supply r ->
  swaps_aenv ps ((β ~ abind_tvar) ++ swap_aenv α β Θ) = cs_ctx r ->
  swaps_pskl ps (swap_pskl α β Q) = cs_out r ->
  cs_ctx r = (β ~ abind_tvar) ++ swaps_aenv ps (swap_aenv α β Θ) /\
  (forall a b, In (a, b) ((α, β) :: ps) -> a `notin` S /\ b `notin` S) /\
  swaps_atoms ((α, β) :: ps) Sd [=] cs_supply r /\
  swaps_pskl ((α, β) :: ps) (pskl_all_syn (close_pskl_wrt_pskl α Q)) =
    pskl_all_syn (close_pskl_wrt_pskl β (cs_out r)).
Proof.
  intros * Hα Hβ Hav HSt HS HT HQ.
  assert (Hfix : swaps_atom ps β = β).
  { apply swaps_atom_notin. intros a b Hin.
    destruct (Hav _ _ Hin) as [Ha Hb].
    split; intro Heq; subst; clear - Ha Hb; fsetdec. }
  split.
  - rewrite <- HT, swaps_aenv_cons_tvar, Hfix. reflexivity.
  - split.
    + eapply swaps_fresh_cons; eassumption.
    + split.
      * eapply swaps_atoms_cons_transport; eassumption.
      * eapply swaps_pskl_close_binder; eassumption.
Qed.

Arguments consis_swaps_close {S Sd St Θ Q α β ps r} _ _ _ _ _ _ _.

Lemma e_consis_call_impl_complete : forall S0 Θ c
    (H0 : e_consis_call_order S0 Θ c), consis_call_complete S0 Θ c.
Proof.
  intros S0 Θ c H0.
  induction H0 as
    [S1 Θ' Ξ α P hg has Has hdep Hdep hskip Hskip hrg Hrg htv Htv hts Hts
    |S1 Θ' α β has Has hsk Hsk hrg Hrg htv Htv hts Hts
    |S1 Θ' Δ1 Δ2 P0 P qhead IHhead qtail IHtail
      q2 Q2 q3 Q3 q4 Q4 q5 Q5 q6 Q6 q7 Q7 q8 Q8 q9 Q9 q10 Q10];
    unfold consis_call_complete;
    intros Hlc HD Hord Hu Hcov Sd Θd Qd Hd;
    cbn [consis_call_lc consis_call_uniq consis_call_cover
         consis_call_run consis_call_out_rel consis_call_defs_mono] in *.
  - (* assign *)
    destruct Θ' as [ | [β0 b] Θ0 ];
      [ destruct (e_assign_inv_nil Hd) | ].
    destruct b as [ | A | Q | | τ ].
    + (* rigid head — Assign-SkipRigid *)
      rewrite e_consis_call_impl_equation_2. cbv beta iota.
      destruct (e_assign_inv_tvar Hd) as [Hnf [Θd' [-> Dt]]].
      destruct (sumbool_of_bool (mem β0 (ftvar_in_pskl P))) as [Hm | Hm];
        [ exfalso; apply mem_true_in in Hm; contradiction | ].
      cbv beta iota.
      assert (Hu0 : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S1)
        by (clear - Hcov; rewrite ftvar_in_aenv_app in *; simpl in *;
            fsetdec).
      kill_ccall (Hrg β0 Θ0 eq_refl) Hu0 Hcov0 Dt pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((β0 ~ abind_tvar) ++ cs_ctx r) pskl_unit), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS | | exact I ].
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    + (* term variable, TYPE payload — Assign-SkipTmVar *)
      rewrite e_consis_call_impl_equation_3. cbv beta iota.
      destruct (e_assign_inv_var_typ Hd) as [Θd' [-> Dt]].
      assert (Hu0 : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S1)
        by (clear - Hcov; rewrite ftvar_in_aenv_app in *; simpl in *;
            fsetdec).
      kill_ccall (Htv β0 A Θ0 eq_refl) Hu0 Hcov0 Dt pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((β0 ~ abind_var_typ A) ++ cs_ctx r) pskl_unit), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS | | exact I ].
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    + (* term variable, SKELETON payload *)
      rewrite e_consis_call_impl_equation_4. cbv beta iota.
      destruct (e_assign_inv_var_skl Hd) as [Θd' [-> Dt]].
      assert (Hu0 : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S1)
        by (clear - Hcov; rewrite ftvar_in_aenv_app in *; simpl in *;
            fsetdec).
      kill_ccall (Hts β0 Q Θ0 eq_refl) Hu0 Hcov0 Dt pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((β0 ~ abind_var_skl Q) ++ cs_ctx r) pskl_unit), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS | | exact I ].
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    + (* undefined flexible head *)
      rewrite e_consis_call_impl_equation_5. cbv beta iota.
      destruct (β0 == α) as [-> | Hne].
      * (* the head IS the target: Assign-UnivGhost-Id or Assign-SolveM *)
        destruct (e_assign_inv_flex_self Hd)
          as [[HΞ [HP [HSd HΘd]]] | [Hocc [bs [tau [Hg [Hmt HΘd]]]]]].
        -- (* Assign-UnivGhost-Id — the runner's own special row *)
           subst Ξ. subst P. subst Sd. subst Θd. cbv beta iota.
           split_eqdec Hca1 Hca2; [ | congruence ].
           cbv beta iota.
           exists (mk_consis_result S1 ((α ~ abind_flex_mono) ++ Θ0)
                     pskl_unit), (@nil (atom * atom)).
           split; [ reflexivity | ].
           repeat apply conj; [ intros ? ? [] | cbn [cs_supply proj1_sig]; reflexivity
                   | cbn [cs_ctx proj1_sig]; reflexivity
                   | exact I ].
        -- (* Assign-SolveM, at every leaf of the runner's Ξ × P dispatch *)
           subst Θd.
           destruct Ξ as [ | e Ξ' ];
             [ destruct P as [ | n | γ | Pa Pb | Pb | | Pb ];
               [ | | | | | | destruct Pb as [ | n' | γ | Pa' Pb' | Pb' | | Pb' ] ]
             | ];
             cbv beta iota;
             try (destruct (γ == α) as [-> | Hnγ];
                  [ exfalso; apply Hocc; simpl; fsetdec | ]);
             cbv beta iota;
             do_solve_m Hocc Hg Hmt Hcov rg Hgs psg Havg HSg HXg HAg.
      * (* a non-target flexible head — Assign-Depend / Assign-Skip *)
        destruct (e_assign_inv_flex_other (not_eq_sym Hne) Hd)
          as [[Hin Dd] | [Hni [Θd' [-> Ds]]]].
        -- destruct (sumbool_of_bool (mem β0 (ftvar_in_pskl P)))
             as [Hm | Hm];
             [ | exfalso; apply mem_false_notin in Hm; contradiction ].
           cbv beta iota.
           assert (Hu0 : uniq ((Ξ ++ (β0 ~ abind_flex_mono)) ++ Θ0))
             by (clear - Hu; solve_uniq).
           assert (Hcov0 : ftvar_in_aenv ((Ξ ++ (β0 ~ abind_flex_mono))
                             ++ Θ0) ∪ ftvar_in_pskl P [<=] S1)
             by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
                 simpl in *; fsetdec).
           kill_ccall (Hdep β0 Θ0 eq_refl) Hu0 Hcov0 Dd pskl_unit
             r Hr ps Hav HS HT HQ.
           exists r, ps.
           split; [ reflexivity | ].
           repeat apply conj; [ exact Hav | exact HS | exact HT | exact I ].
        -- destruct (sumbool_of_bool (mem β0 (ftvar_in_pskl P)))
             as [Hm | Hm];
             [ exfalso; apply mem_true_in in Hm; contradiction | ].
           cbv beta iota.
           assert (Hu0 : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
           assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S1)
             by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
                 simpl in *; fsetdec).
           kill_ccall (Hskip β0 Θ0 eq_refl) Hu0 Hcov0 Ds pskl_unit
             r Hr ps Hav HS HT HQ.
           exists (mk_consis_result (cs_supply r)
                     ((β0 ~ abind_flex_mono) ++ cs_ctx r) pskl_unit), ps.
           split; [ reflexivity | ].
           repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS | | exact I ].
           cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
           head_fresh Hav Hcov.
    + (* defined flexible head — Assign-Assign *)
      rewrite e_consis_call_impl_equation_6. cbv beta iota.
      destruct (e_assign_inv_def Hd) as [Hft [Θd' [Qm [-> Dc]]]].
      destruct (sumbool_of_bool
                  (flex_bound_ck ((β0, abind_flex_mono_def τ) :: Θ0) α))
        as [Hfb | Hfb];
        [ | exfalso; eapply flex_bound_ck_not_flex_tvar;
            [ exact Hfb | exact Hft ] ].
      cbv beta iota.
      assert (Hu0 : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
      pose proof (a_flex_tvar_in_dom Hft) as Hαdom.
      pose proof (dom_subset_ftvar_in_aenv
                    ((β0, abind_flex_mono_def τ) :: Θ0)) as Hdm.
      assert (HΘ : ftvar_in_aenv ((β0, abind_flex_mono_def τ) :: Θ0)
                [<=] S1)
        by (clear - Hcov; rewrite ftvar_in_aenv_app in Hcov; fsetdec).
      assert (HαS : α `in` S1) by (clear - HΘ Hαdom Hdm; fsetdec).
      assert (Hcov0 : consis_call_cover (Ξ ++ Θ0)
                (consis_call_consis empty empty
                   (subst_pskl_in_pskl (ptyp_to_pskl τ) β0 P)
                   (subst_pskl_in_pskl (ptyp_to_pskl τ) β0 (pskl_var_f α)))
                [<=] S1)
        by (cbn [consis_call_cover]; repeat rewrite (empty_union_2 (s := empty)) by (unfold Empty; clear; fsetdec);
            apply subst_pskl_preserves_cover; rewrite ftvar_ptyp_to_pskl;
            clear - Hcov HαS; repeat rewrite ftvar_in_aenv_app in *;
            simpl in *; fsetdec).
      kill_ccall (Has β0 τ Θ0 eq_refl) Hu0 Hcov0 Dc Qm
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((β0 ~ abind_flex_mono_def τ) ++ cs_ctx r) pskl_unit), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS | | exact I ].
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
  - (* unify *)
    destruct Θ' as [ | [γ b] Θ0 ];
      [ destruct (e_unify_inv_nil Hd) | ].
    destruct b as [ | A | Q | | τ ].
    + (* rigid head — Flex-Flex-Skip' *)
      rewrite e_consis_call_impl_equation_8. cbv beta iota.
      split_eqdec Heq Hne; [ subst; cbv beta iota; do_flex_id HD Hd | ].
      cbv beta iota.
      destruct (e_unify_inv_other Hne ltac:(left; reflexivity) Hd)
        as [Θd' [-> Ds]].
      assert (Hu0 : uniq Θ0) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv Θ0 [<=] S1)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_ccall (Hrg γ Θ0 eq_refl) Hu0 Hcov0 Ds pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((γ ~ abind_tvar) ++ cs_ctx r) pskl_unit), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS | | exact I ].
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    + (* term variable, TYPE payload *)
      rewrite e_consis_call_impl_equation_9. cbv beta iota.
      split_eqdec Heq Hne; [ subst; cbv beta iota; do_flex_id HD Hd | ].
      cbv beta iota.
      destruct (e_unify_inv_other Hne
                  ltac:(right; left; exists A; reflexivity) Hd)
        as [Θd' [-> Ds]].
      assert (Hu0 : uniq Θ0) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv Θ0 [<=] S1)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_ccall (Htv γ A Θ0 eq_refl) Hu0 Hcov0 Ds pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((γ ~ abind_var_typ A) ++ cs_ctx r) pskl_unit), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS | | exact I ].
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    + (* term variable, SKELETON payload *)
      rewrite e_consis_call_impl_equation_10. cbv beta iota.
      split_eqdec Heq Hne; [ subst; cbv beta iota; do_flex_id HD Hd | ].
      cbv beta iota.
      destruct (e_unify_inv_other Hne
                  ltac:(right; right; exists Q; reflexivity) Hd)
        as [Θd' [-> Ds]].
      assert (Hu0 : uniq Θ0) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv Θ0 [<=] S1)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_ccall (Hts γ Q Θ0 eq_refl) Hu0 Hcov0 Ds pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((γ ~ abind_var_skl Q) ++ cs_ctx r) pskl_unit), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS | | exact I ].
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    + (* undefined flexible head — L / R / Skip *)
      rewrite e_consis_call_impl_equation_11. cbv beta iota.
      split_eqdec Heq Hne; [ subst; cbv beta iota; do_flex_id HD Hd | ].
      cbv beta iota.
      split_eqdec Heq2 Hne2.
      * (* the head IS α — Flex-Flex-L *)
        subst. cbv beta iota.
        destruct (e_unify_inv_flex_l Hne Hd) as [Hfβ [-> ->]].
        destruct (sumbool_of_bool (flex_bound_ck Θ0 β)) as [Hfb | Hfb];
          [ | exfalso; eapply flex_bound_ck_not_flex_tvar;
              [ exact Hfb | exact Hfβ ] ].
        cbv beta iota.
        eexists; exists (@nil (atom * atom)).
        split; [ reflexivity | ].
        repeat apply conj; [ intros ? ? [] | cbn [swaps_atoms cs_supply proj1_sig]; reflexivity
                | cbn [swaps_aenv cs_ctx proj1_sig]; reflexivity | exact I ].
      * cbv beta iota. split_eqdec Heq3 Hne3.
        -- (* the head IS β — Flex-Flex-R *)
           subst. cbv beta iota.
           destruct (e_unify_inv_flex_r Hne Hd) as [Hfα [-> ->]].
           destruct (sumbool_of_bool (flex_bound_ck Θ0 α)) as [Hfb | Hfb];
             [ | exfalso; eapply flex_bound_ck_not_flex_tvar;
                 [ exact Hfb | exact Hfα ] ].
           cbv beta iota.
           eexists; exists (@nil (atom * atom)).
           split; [ reflexivity | ].
           repeat apply conj; [ intros ? ? [] | cbn [swaps_atoms cs_supply proj1_sig]; reflexivity
                   | cbn [swaps_aenv cs_ctx proj1_sig]; reflexivity | exact I ].
        -- (* Flex-Flex-Skip *)
           cbv beta iota.
           destruct (e_unify_inv_flex_skip Hne Hne2 Hne3 Hd)
             as [Θd' [-> Ds]].
           assert (Hu0 : uniq Θ0) by (clear - Hu; solve_uniq).
           assert (Hcov0 : ftvar_in_aenv Θ0 [<=] S1)
             by (clear - Hcov; simpl in *; fsetdec).
           kill_ccall (Hsk γ Θ0 eq_refl) Hu0 Hcov0 Ds pskl_unit
             r Hr ps Hav HS HT HQ.
           exists (mk_consis_result (cs_supply r)
                     ((γ ~ abind_flex_mono) ++ cs_ctx r) pskl_unit), ps.
           split; [ reflexivity | ].
           repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS | | exact I ].
           cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
           head_fresh Hav Hcov.
    + (* defined flexible head — Flex-Flex-Assign *)
      rewrite e_consis_call_impl_equation_12. cbv beta iota.
      split_eqdec Heq Hne; [ subst; cbv beta iota; do_flex_id HD Hd | ].
      cbv beta iota.
      destruct (e_unify_inv_def Hne Hd) as [Hfa [Hfb [Θd' [Qm [-> Dc]]]]].
      destruct (sumbool_of_bool
                  (flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) α
                   && flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) β))
        as [Hbb | Hbb];
        [ | exfalso; apply andb_false_iff in Hbb;
            destruct Hbb as [Hbb | Hbb];
            eapply flex_bound_ck_not_flex_tvar; eassumption ].
      cbv beta iota.
      assert (Hu0 : uniq Θ0) by (clear - Hu; solve_uniq).
      pose proof (a_flex_tvar_in_dom Hfa) as Hαdom.
      pose proof (a_flex_tvar_in_dom Hfb) as Hβdom.
      pose proof (dom_subset_ftvar_in_aenv
                    ((γ, abind_flex_mono_def τ) :: Θ0)) as Hdm.
      assert (HβS : β `in` S1) by (clear - Hcov Hβdom Hdm; fsetdec).
      assert (HαS : α `in` S1) by (clear - Hcov Hαdom Hdm; fsetdec).
      assert (Hcov0 : consis_call_cover Θ0
                (consis_call_consis empty empty
                   (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f β)))
                   (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f α))))
                [<=] S1)
        by (cbn [consis_call_cover]; repeat rewrite (empty_union_2 (s := empty)) by (unfold Empty; clear; fsetdec);
            repeat rewrite ptyp_to_pskl_subst; apply subst_pskl_preserves_cover;
            repeat rewrite ftvar_ptyp_to_pskl; clear - Hcov HαS HβS;
            simpl in *; fsetdec).
      kill_ccall (Has γ τ Θ0 eq_refl) Hu0 Hcov0 Dc Qm
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((γ ~ abind_flex_mono_def τ) ++ cs_ctx r) pskl_unit), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS | | exact I ].
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
  - (* consis *)
    destruct Hlc as [Hlc0 Hlc1].
    rewrite e_consis_call_impl_equation_13.
    destruct P0 as [ | n0 | β0 | P0a P0b | P0' | | P0' ]; cbv beta iota.
    + (* ================= pattern [1] ================= *)
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      * (* 1 ∼ 1 — U-Unit *)
        destruct (e_consis_inv_unit Hd) as [-> [-> ->]].
        exists (mk_consis_result S1 Θ' pskl_unit), (@nil (atom * atom)).
        split; [ reflexivity | ].
        repeat apply conj; [ intros ? ? [] | cbn [swaps_atoms cs_supply proj1_sig]; reflexivity
                | cbn [swaps_aenv cs_ctx proj1_sig]; reflexivity
                | cbn [swaps_pskl cs_out proj1_sig]; reflexivity ].
      * (* a dangling index is no subject *) inversion Hlc1.
      * (* 1 ∼ α̂ — U-FlexL *)
        destruct (e_consis_inv_flex_l Hd ltac:(intros; discriminate)
                    ltac:(discriminate) ltac:(intros; discriminate))
          as [-> [Hnf Da]].
        pose proof (e_assign_target_flex Da) as Hft.
        flex_test_true Hft. cbv beta iota.
        assert (Hcov0 : ftvar_in_aenv (nil ++ Θ') ∪ ftvar_in_pskl pskl_unit
                          [<=] S1) by (clear - Hcov; simpl in *; fsetdec).
        kill_ccall (Q9 α0 eq_refl) Hu Hcov0 Da pskl_unit
          r Hr ps Hav HS HT HQ.
        exists (mk_consis_result (cs_supply r) (cs_ctx r) (pskl_var_f α0)),
               ps.
        split; [ reflexivity | ].
        repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                | cbn [cs_ctx proj1_sig]; exact HT | ].
        cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
      * (* 1 ∼ → : no rule fires *) inversion Hd.
      * (* 1 ∼ ∀ : no rule fires *) inversion Hd.
      * (* 1 ∼ ◇ — U-Ghost, the only rule at a ◇ subject *)
        destruct (e_consis_inv_ghost_subject Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * (* 1 ∼ ⫯P — U-UnivGhost2 *)
        pose proof (e_consis_inv_univ_ghost2_unit Hd) as Dc.
        assert (Hcov0 : consis_call_cover Θ'
                  (consis_call_consis Δ1 Δ2 pskl_unit Pb) [<=] S1)
          by (clear - Hcov;
              cbn [consis_call_cover ftvar_in_pskl] in *; fsetdec).
        kill_ccall (Q6 Pb eq_refl) Hu Hcov0 Dc Qd r Hr ps Hav HS HT HQ.
        exists r, ps.
        split; [ reflexivity | ].
        repeat apply conj; [ exact Hav | exact HS | exact HT | exact HQ ].
    + (* a dangling index is no pattern *) inversion Hlc0.
    + (* ================= pattern [β̂] ================= *)
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      * (* β̂ ∼ 1 — U-FlexR *) do_flex_r (Q10 β0 eq_refl) Hd Hu Hcov.
      * inversion Hlc1.
      * (* β̂ ∼ α̂ — U-Rigid / U-Flex / U-FlexL / U-FlexR *)
        split_eqdec Heqab Hneab.
        -- (* the two variables COINCIDE *)
           subst β0. cbv beta iota.
           destruct (sumbool_of_bool (rigid_bound_ck Θ' α0)) as [Hrb | Hrb];
             cbv beta iota.
           ++ (* the runner answers U-Rigid *)
              destruct (e_consis_inv_var_var Hd)
                as [ [_ [_ [-> [-> ->]]]]
                   | [ [-> Du]
                     | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
              ** exists (mk_consis_result S1 Θ' (pskl_var_f α0)),
                        (@nil (atom * atom)).
                 split; [ reflexivity | ].
                 repeat apply conj; [ intros ? ? []
                         | cbn [swaps_atoms cs_supply proj1_sig]; reflexivity
                         | cbn [swaps_aenv cs_ctx proj1_sig]; reflexivity
                         | cbn [swaps_pskl cs_out proj1_sig]; reflexivity ].
              ** (* U-Flex at α̂ ≈ᵘ α̂ moves nothing (§5) *)
                 destruct (e_unify_refl Du HD) as [-> ->].
                 exists (mk_consis_result S1 Θ' (pskl_var_f α0)),
                        (@nil (atom * atom)).
                 split; [ reflexivity | ].
                 repeat apply conj; [ intros ? ? []
                         | cbn [swaps_atoms cs_supply proj1_sig]; reflexivity
                         | cbn [swaps_aenv cs_ctx proj1_sig]; reflexivity
                         | cbn [swaps_pskl cs_out proj1_sig]; reflexivity ].
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. eapply e_assign_target_flex;
                   eassumption.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. eapply e_assign_target_flex;
                   eassumption.
           ++ (* the runner recurses into [unifyvar] *)
              destruct (e_consis_inv_var_var Hd)
                as [ [_ [Hbt _]]
                   | [ [-> Du]
                     | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
              ** exfalso.
                 assert (Hct : rigid_bound_ck Θ' α0 = true)
                   by (apply rigid_bound_ck_complete; exact Hbt).
                 rewrite Hct in Hrb. discriminate.
              ** assert (Hcov0 : ftvar_in_aenv Θ' [<=] S1)
                   by (clear - Hcov; simpl in *; fsetdec).
                 kill_ccall (Q8 α0 α0 eq_refl eq_refl) Hu Hcov0 Du
                   pskl_unit r Hr ps Hav HS HT HQ.
                 exists (mk_consis_result (cs_supply r) (cs_ctx r)
                           (pskl_var_f α0)), ps.
                 split; [ reflexivity | ].
                 repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                         | cbn [cs_ctx proj1_sig]; exact HT | ].
                 cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. eapply e_assign_target_flex;
                   eassumption.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. eapply e_assign_target_flex;
                   eassumption.
        -- (* the two variables DIFFER *)
           cbv beta iota.
           destruct (sumbool_of_bool
                       (flex_bound_ck Θ' α0 && flex_bound_ck Θ' β0))
             as [Hbb | Hbb]; cbv beta iota.
           ++ (* both flexible — U-Flex *)
              pose proof (andb_prop _ _ Hbb) as [Hba Hbβ].
              destruct (e_consis_inv_var_var Hd)
                as [ [Heq _]
                   | [ [-> Du]
                     | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
              ** congruence.
              ** assert (Hcov0 : ftvar_in_aenv Θ' [<=] S1)
                   by (clear - Hcov; simpl in *; fsetdec).
                 kill_ccall (Q8 α0 β0 eq_refl eq_refl) Hu Hcov0 Du
                   pskl_unit r Hr ps Hav HS HT HQ.
                 exists (mk_consis_result (cs_supply r) (cs_ctx r)
                           (pskl_var_f α0)), ps.
                 split; [ reflexivity | ].
                 repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                         | cbn [cs_ctx proj1_sig]; exact HT | ].
                 cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. apply flex_bound_ck_flex_tvar.
                 exact Hbβ.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. apply flex_bound_ck_flex_tvar.
                 exact Hba.
           ++ destruct (sumbool_of_bool (flex_bound_ck Θ' β0))
                as [Hbβ | Hbβ]; cbv beta iota.
              ** (* only the PATTERN is flexible — U-FlexR *)
                 destruct (e_consis_inv_var_var Hd)
                   as [ [Heq _]
                      | [ [-> Du]
                        | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
                 --- congruence.
                 --- exfalso.
                     destruct (e_unify_target_flex Du) as [Hfa Hfb2].
                     assert (Hca : flex_bound_ck Θ' α0 = true)
                       by (apply flex_tvar_flex_bound_ck; exact Hfa).
                     assert (Hcb : flex_bound_ck Θ' β0 = true)
                       by (apply flex_tvar_flex_bound_ck; exact Hfb2).
                     rewrite Hca, Hcb in Hbb. discriminate.
                 --- exfalso. destruct Hnf as [_ Hf]. apply Hf.
                     apply a_flex_var_iff_tvar. apply flex_bound_ck_flex_tvar.
                     exact Hbβ.
                 --- assert (Hcov0 : ftvar_in_aenv (nil ++ Θ')
                               ∪ ftvar_in_pskl (pskl_var_f α0) [<=] S1)
                       by (clear - Hcov; simpl in *; fsetdec).
                     kill_ccall (Q10 β0 eq_refl) Hu Hcov0 Da pskl_unit
                       r Hr ps Hav HS HT HQ.
                     exists (mk_consis_result (cs_supply r) (cs_ctx r)
                               (pskl_var_f β0)), ps.
                     split; [ reflexivity | ].
                     repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                             | cbn [cs_ctx proj1_sig]; exact HT | ].
                     cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
              ** destruct (sumbool_of_bool (flex_bound_ck Θ' α0))
                   as [Hba | Hba]; cbv beta iota.
                 --- (* only the SUBJECT is flexible — U-FlexL *)
                     destruct (e_consis_inv_var_var Hd)
                       as [ [Heq _]
                          | [ [-> Du]
                            | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
                     +++ congruence.
                     +++ exfalso.
                         destruct (e_unify_target_flex Du) as [Hfa Hfb2].
                         assert (Hcb : flex_bound_ck Θ' β0 = true)
                           by (apply flex_tvar_flex_bound_ck; exact Hfb2).
                         rewrite Hcb in Hbβ. discriminate.
                     +++ assert (Hcov0 : ftvar_in_aenv (nil ++ Θ')
                                   ∪ ftvar_in_pskl (pskl_var_f β0) [<=] S1)
                           by (clear - Hcov; simpl in *; fsetdec).
                         kill_ccall (Q9 α0 eq_refl) Hu Hcov0 Da
                           pskl_unit r Hr ps Hav HS HT HQ.
                         exists (mk_consis_result (cs_supply r) (cs_ctx r)
                                   (pskl_var_f α0)), ps.
                         split; [ reflexivity | ].
                         repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                                 | cbn [cs_ctx proj1_sig]; exact HT | ].
                         cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
                     +++ exfalso. destruct Hnf as [_ Hf]. apply Hf.
                         apply a_flex_var_iff_tvar. apply flex_bound_ck_flex_tvar.
                         exact Hba.
                 --- (* NEITHER is flexible: no rule can have fired *)
                     exfalso.
                     destruct (e_consis_inv_var_var Hd)
                       as [ [Heq _]
                          | [ [-> Du]
                            | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
                     +++ congruence.
                     +++ destruct (e_unify_target_flex Du) as [Hfa _].
                         assert (Hca : flex_bound_ck Θ' α0 = true)
                           by (apply flex_tvar_flex_bound_ck; exact Hfa).
                         rewrite Hca in Hba. discriminate.
                     +++ assert (Hca : flex_bound_ck Θ' α0 = true)
                           by (apply flex_tvar_flex_bound_ck;
                               eapply e_assign_target_flex; eassumption).
                         rewrite Hca in Hba. discriminate.
                     +++ assert (Hcb : flex_bound_ck Θ' β0 = true)
                           by (apply flex_tvar_flex_bound_ck;
                               eapply e_assign_target_flex; eassumption).
                         rewrite Hcb in Hbβ. discriminate.
      * (* β̂ ∼ → — U-FlexR *) do_flex_r (Q10 β0 eq_refl) Hd Hu Hcov.
      * (* β̂ ∼ ∀ — U-FlexR *) do_flex_r (Q10 β0 eq_refl) Hd Hu Hcov.
      * (* ⭐ β̂ ∼ ◇ — FORMERLY DIVERGENT: [U-FlexR] is barred by its
           [<> ◇] guard, so only [U-Ghost] fires and the runner agrees. *)
        destruct (e_consis_inv_ghost_flex_pattern Hd) as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * (* β̂ ∼ ⫯P — U-FlexR, with U-UnivGhost2 as the rigid fallback *)
        destruct (e_consis_inv_var_univ_ghost Hd)
          as [ [Hft [-> Da]] | [Hnf Dc] ].
        -- flex_test_true Hft. cbv beta iota.
           assert (Hcov0 : ftvar_in_aenv (nil ++ Θ')
                     ∪ ftvar_in_pskl (pskl_univ_ghost Pb) [<=] S1)
             by (clear - Hcov; simpl in *; fsetdec).
           kill_ccall (Q10 β0 eq_refl) Hu Hcov0 Da pskl_unit
             r Hr ps Hav HS HT HQ.
           exists (mk_consis_result (cs_supply r) (cs_ctx r)
                     (pskl_var_f β0)), ps.
           split; [ reflexivity | ].
           repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                   | cbn [cs_ctx proj1_sig]; exact HT | ].
           cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
        -- destruct (sumbool_of_bool (flex_bound_ck Θ' β0)) as [Hfb | Hfb];
             [ exfalso; destruct Hnf as [_ Hf]; apply Hf;
               apply a_flex_var_iff_tvar; apply flex_bound_ck_flex_tvar;
               exact Hfb | ].
           cbv beta iota.
           assert (Hcov0 : consis_call_cover Θ'
                     (consis_call_consis Δ1 Δ2 (pskl_var_f β0) Pb) [<=] S1)
             by (clear - Hcov;
                 cbn [consis_call_cover ftvar_in_pskl] in *; fsetdec).
           kill_ccall (Q6 Pb eq_refl) Hu Hcov0 Dc Qd r Hr ps Hav HS HT HQ.
           exists r, ps.
           split; [ reflexivity | ].
           repeat apply conj; [ exact Hav | exact HS | exact HT | exact HQ ].
    + (* ================= pattern [→] ================= *)
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      * (* → ∼ 1 : no rule fires *) inversion Hd.
      * inversion Hlc1.
      * (* → ∼ α̂ — U-FlexL *) do_flex_l (Q9 α0 eq_refl) Hd Hu Hcov.
      * (* → ∼ → — U-Arrow, the one THREADING row *)
        pose proof (IHhead P0a P0b Pa Pb eq_refl eq_refl) as IH1.
        cbn [ftvar_in_pskl] in Hcov.
        destruct (e_consis_inv_arrow Hd)
          as [Sm [Θm [Qd1 [Qd2 [-> [D1 D2]]]]]].
        assert (Hcov1 : consis_call_cover Θ'
                  (consis_call_consis Δ1 Δ2 P0a Pa) [<=] S1)
          by (cbn [consis_call_cover] in *; clear - Hcov; fsetdec).
        kill_ccall IH1 Hu Hcov1 D1 Qd1 r1 Hr1 ps1 Hav1 HS1 HT1 HQ1.
        cbn [consis_call_spec consis_spec] in Hr1.
        pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                      _ _ _ _ _ _ _ _ _ Hr1 Hu
                      ltac:(cbn [consis_call_cover] in *; clear - Hcov;
                            fsetdec))
          as [Da1 [Hu1' Hcov1']].
        pose proof (e_consis_supply_grows Hr1) as Hgr1.
        pose proof ((proj2 (proj2 e_assign_unify_consis_out_ftvar))
                      _ _ _ _ _ _ _ _ _ Hr1 Hu
                      ltac:(cbn [consis_call_cover] in *; clear - Hcov;
                            fsetdec)) as Hout1.
        assert (HDl : Δ1 [=] swaps_atoms ps1 Δ1)
          by (symmetry; apply swaps_atoms_notin; intros a0 b0 Hin;
              destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
              clear - Ha0 Hb0 Hcov; fsetdec).
        assert (HDr : Δ2 [=] swaps_atoms ps1 Δ2)
          by (symmetry; apply swaps_atoms_notin; intros a0 b0 Hin;
              destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
              clear - Ha0 Hb0 Hcov; fsetdec).
        assert (HSm : cs_supply r1 [=] swaps_atoms ps1 Sm)
          by (symmetry; exact HS1).
        destruct (e_consis_swaps ps1 D2 HDl HDr HSm) as [S2t [HS2t D2t]].
        rewrite HT1 in D2t.
        rewrite (swaps_pskl_fresh_id ps1 P0b) in D2t;
          [ | intros a0 b0 Hin; destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0];
              split; clear - Ha0 Hb0 Hcov; fsetdec ].
        rewrite (swaps_pskl_fresh_id ps1 Pb) in D2t;
          [ | intros a0 b0 Hin; destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0];
              split; clear - Ha0 Hb0 Hcov; fsetdec ].
        pose proof (IHtail P0a P0b Pa Pb _ _ _ eq_refl eq_refl Hr1) as IH2.
        assert (Hcov2 : consis_call_cover (cs_ctx r1)
                  (consis_call_consis Δ1 Δ2 P0b Pb) [<=] cs_supply r1)
          by (cbn [consis_call_cover] in *;
              clear - Hcov Hcov1' Hgr1; fsetdec).
        kill_ccall IH2 Hu1' Hcov2 D2t (swaps_pskl ps1 Qd2)
          r2 Hr2 ps2 Hav2 HS2 HT2 HQ2.
        exists (mk_consis_result (cs_supply r2) (cs_ctx r2)
                  (pskl_arrow (cs_out r1) (cs_out r2))), (ps1 ++ ps2).
        split; [ reflexivity | ].
        repeat apply conj.
        -- intros a0 b0 Hin. apply in_app_or in Hin.
           destruct Hin as [Hin | Hin]; [ exact (Hav1 a0 b0 Hin) | ].
           destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
           split; clear - Ha0 Hb0 Hgr1; fsetdec.
        -- cbn [cs_supply]. rewrite swaps_atoms_app. rewrite <- HS2.
           apply swaps_atoms_cong. symmetry. exact HS2t.
        -- cbn [cs_ctx]. rewrite swaps_aenv_app. exact HT2.
        -- cbn [cs_out]. rewrite swaps_pskl_app, !swaps_pskl_arrow.
           rewrite HQ1 in *. f_equal; [ | exact HQ2 ].
           apply swaps_pskl_fresh_id. intros a0 b0 Hin.
           destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
           split; clear - Ha0 Hb0 Hout1; fsetdec.
      * (* → ∼ ∀ : no rule fires *) inversion Hd.
      * (* ⭐ → ∼ ◇ — U-Ghost is the only rule at a ◇ subject *)
        destruct (e_consis_inv_ghost_subject Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * (* → ∼ ⫯P — U-UnivGhost2 *)
        pose proof (e_consis_inv_univ_ghost2_arrow Hd) as Dc.
        do_pass (Q6 Pb eq_refl) Dc Hu Hcov Qd.
    + (* ================= pattern [∀] ================= *)
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      * (* ∀ ∼ 1 : no rule fires *) inversion Hd.
      * inversion Hlc1.
      * (* ∀ ∼ α̂ — U-FlexL *) do_flex_l (Q9 α0 eq_refl) Hd Hu Hcov.
      * (* ∀ ∼ → : no rule fires *) inversion Hd.
      * (* ∀ ∼ ∀ — U-ForallInh *)
        destruct (e_consis_inv_forall_inh Hd) as [α [Qb [Hα [-> Dp]]]].
        pose proof (supply_fresh_notin S1) as Hz.
        simpl ftvar_in_pskl in Hcov.
        assert (HD1 : add (supply_fresh S1) Δ1
                  [=] swap_atoms α (supply_fresh S1) (add α Δ1)).
        { rewrite swap_atoms_add.
          rewrite (swap_atoms_notin α (supply_fresh S1) Δ1)
            by (clear - Hα Hz Hcov; fsetdec).
          unfold swap_atom. destruct (α == α); [ reflexivity | congruence ]. }
        assert (HD2 : add (supply_fresh S1) Δ2
                  [=] swap_atoms α (supply_fresh S1) (add α Δ2)).
        { rewrite swap_atoms_add.
          rewrite (swap_atoms_notin α (supply_fresh S1) Δ2)
            by (clear - Hα Hz Hcov; fsetdec).
          unfold swap_atom. destruct (α == α); [ reflexivity | congruence ]. }
        assert (HSq : add (supply_fresh S1) S1
                  [=] swap_atoms α (supply_fresh S1) (add α S1)).
        { rewrite swap_atoms_add.
          rewrite (swap_atoms_notin α (supply_fresh S1) S1)
            by (clear - Hα Hz; fsetdec).
          unfold swap_atom. destruct (α == α); [ reflexivity | congruence ]. }
        destruct (e_consis_swap Dp HD1 HD2 HSq) as [S1t [HS1t Dpt]].
        rewrite !swap_aenv_app, !swap_aenv_one_tvar in Dpt.
        rewrite (swap_aenv_fresh_id α (supply_fresh S1) Θ') in Dpt
          by (clear - Hα Hz Hcov; fsetdec).
        rewrite !swap_pskl_open_var in Dpt.
        rewrite (swap_pskl_fresh_id α (supply_fresh S1) P0') in Dpt
          by (clear - Hα Hz Hcov; fsetdec).
        rewrite (swap_pskl_fresh_id α (supply_fresh S1) Pb) in Dpt
          by (clear - Hα Hz Hcov; fsetdec).
        replace (swap_atom α (supply_fresh S1) α) with (supply_fresh S1)
          in Dpt by (unfold swap_atom; destruct (α == α); congruence).
        pose proof (dom_subset_ftvar_in_aenv Θ') as Hdm.
        assert (Hu' : uniq ((supply_fresh S1 ~ abind_tvar) ++ Θ'))
          by (apply uniq_push;
              [ exact Hu | clear - Hz Hcov Hdm; fsetdec ]).
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0'
                      (pskl_var_f (supply_fresh S1))) as Hup1.
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Pb
                      (pskl_var_f (supply_fresh S1))) as Hup2.
        assert (Hcov' : consis_call_cover
                  ((supply_fresh S1 ~ abind_tvar) ++ Θ')
                  (consis_call_consis
                     (add (supply_fresh S1) Δ1) (add (supply_fresh S1) Δ2)
                     (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S1)))
                     (open_pskl_wrt_pskl Pb (pskl_var_f (supply_fresh S1))))
                  [<=] add (supply_fresh S1) S1).
        { cbn [consis_call_cover]. simpl ftvar_in_aenv.
          clear - Hcov Hup1 Hup2. simpl in *. fsetdec. }
        kill_ccall (Q2 P0' Pb eq_refl eq_refl) Hu' Hcov' Dpt
          (swap_pskl α (supply_fresh S1) Qb) r Hr ps Hav HS HT HQ.
        destruct (consis_swaps_close Hα Hz Hav HS1t HS HT HQ)
          as (HTz & HavAll & HSAll & HQAll).
        destruct (@split_tvar_head_hit_eq _ _ _ HTz) as [pf Hsp].
        rewrite Hsp. cbv beta iota.
        exists (mk_consis_result (cs_supply r)
                  (swaps_aenv ps (swap_aenv α (supply_fresh S1) Θd))
                  (pskl_all_syn (close_pskl_wrt_pskl (supply_fresh S1) (cs_out r)))),
               ((α, supply_fresh S1) :: ps).
        split; [ reflexivity | ].
        repeat apply conj;
          [ exact HavAll | exact HSAll | reflexivity | exact HQAll ].
      * (* ⭐ ∀ ∼ ◇ — U-Ghost is the only rule at a ◇ subject *)
        destruct (e_consis_inv_ghost_subject Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * (* ∀ ∼ ⫯P — U-UnivGhost1 *)
        destruct (e_consis_inv_univ_ghost1 Hd) as [α [Qb [Hα [-> Dp]]]].
        pose proof (supply_fresh_notin S1) as Hz.
        simpl ftvar_in_pskl in Hcov.
        assert (HD1 : add (supply_fresh S1) Δ1
                  [=] swap_atoms α (supply_fresh S1) (add α Δ1)).
        { rewrite swap_atoms_add.
          rewrite (swap_atoms_notin α (supply_fresh S1) Δ1)
            by (clear - Hα Hz Hcov; fsetdec).
          unfold swap_atom. destruct (α == α); [ reflexivity | congruence ]. }
        assert (HD2 : Δ2 [=] swap_atoms α (supply_fresh S1) Δ2)
          by (symmetry; apply swap_atoms_notin;
              clear - Hα Hz Hcov; fsetdec).
        assert (HSq : add (supply_fresh S1) S1
                  [=] swap_atoms α (supply_fresh S1) (add α S1)).
        { rewrite swap_atoms_add.
          rewrite (swap_atoms_notin α (supply_fresh S1) S1)
            by (clear - Hα Hz; fsetdec).
          unfold swap_atom. destruct (α == α); [ reflexivity | congruence ]. }
        destruct (e_consis_swap Dp HD1 HD2 HSq) as [S1t [HS1t Dpt]].
        rewrite !swap_aenv_app, !swap_aenv_one_tvar in Dpt.
        rewrite (swap_aenv_fresh_id α (supply_fresh S1) Θ') in Dpt
          by (clear - Hα Hz Hcov; fsetdec).
        rewrite !swap_pskl_open_var in Dpt.
        rewrite (swap_pskl_fresh_id α (supply_fresh S1) P0') in Dpt
          by (clear - Hα Hz Hcov; fsetdec).
        rewrite (swap_pskl_fresh_id α (supply_fresh S1) (pskl_univ_ghost Pb))
          in Dpt by (clear - Hα Hz Hcov; simpl; fsetdec).
        replace (swap_atom α (supply_fresh S1) α) with (supply_fresh S1)
          in Dpt by (unfold swap_atom; destruct (α == α); congruence).
        pose proof (dom_subset_ftvar_in_aenv Θ') as Hdm.
        assert (Hu' : uniq ((supply_fresh S1 ~ abind_tvar) ++ Θ'))
          by (apply uniq_push;
              [ exact Hu | clear - Hz Hcov Hdm; fsetdec ]).
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0'
                      (pskl_var_f (supply_fresh S1))) as Hup1.
        assert (Hcov' : consis_call_cover
                  ((supply_fresh S1 ~ abind_tvar) ++ Θ')
                  (consis_call_consis (add (supply_fresh S1) Δ1) Δ2
                     (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S1)))
                     (pskl_univ_ghost Pb))
                  [<=] add (supply_fresh S1) S1).
        { cbn [consis_call_cover]. simpl ftvar_in_aenv.
          clear - Hcov Hup1. simpl in *. fsetdec. }
        kill_ccall (Q5 P0' Pb eq_refl eq_refl) Hu' Hcov' Dpt
          (swap_pskl α (supply_fresh S1) Qb) r Hr ps Hav HS HT HQ.
        destruct (consis_swaps_close Hα Hz Hav HS1t HS HT HQ)
          as (HTz & HavAll & HSAll & HQAll).
        destruct (@split_tvar_head_hit_eq _ _ _ HTz) as [pf Hsp].
        rewrite Hsp. cbv beta iota.
        exists (mk_consis_result (cs_supply r)
                  (swaps_aenv ps (swap_aenv α (supply_fresh S1) Θd))
                  (pskl_all_syn (close_pskl_wrt_pskl (supply_fresh S1) (cs_out r)))),
               ((α, supply_fresh S1) :: ps).
        split; [ reflexivity | ].
        repeat apply conj;
          [ exact HavAll | exact HSAll | reflexivity | exact HQAll ].
    + (* ⭐ ================= pattern [◇] =================
         FORMERLY OUT OF THE FRAGMENT.  [U-GhostR] is the only rule: it
         coincides with [U-Ghost] at [(◇,◇)] (same triple), and [U-FlexL]
         is barred by its [<> ◇] guard.  The runner's ghost-pattern arm is
         unconditional in the subject, so every sub-case reaches the same
         code — only the INVERSION differs, by whether the subject is a
         variable. *)
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      * destruct (e_consis_inv_ghost_pattern Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * inversion Hlc1.
      * (* a FLEXIBLE subject — the other formerly divergent cell *)
        destruct (e_consis_inv_flex_subject_ghost Hd) as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * destruct (e_consis_inv_ghost_pattern Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * destruct (e_consis_inv_ghost_pattern Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * (* (◇, ◇) — the benign overlap: both ghost rows return this *)
        destruct (e_consis_inv_ghost_pattern Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * destruct (e_consis_inv_ghost_pattern Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
    + (* ================= pattern [⫯] ================= *)
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      * (* ⫯P0 ∼ 1 — U-UnivGhostR *)
        pose proof (e_consis_inv_univ_ghost_r_unit Hd) as Dc.
        do_pass (Q7 P0' eq_refl) Dc Hu Hcov Qd.
      * inversion Hlc1.
      * (* ⫯P0 ∼ α̂ — U-FlexL, with U-UnivGhostR as the rigid fallback *)
        destruct (e_consis_inv_univ_ghost_var Hd)
          as [ [Hft [-> Da]] | [Hnf Dc] ].
        -- flex_test_true Hft. cbv beta iota.
           assert (Hcov0 : ftvar_in_aenv (nil ++ Θ')
                     ∪ ftvar_in_pskl (pskl_univ_ghost P0') [<=] S1)
             by (clear - Hcov; simpl in *; fsetdec).
           kill_ccall (Q9 α0 eq_refl) Hu Hcov0 Da pskl_unit
             r Hr ps Hav HS HT HQ.
           eexists; exists ps.
           split; [ reflexivity | ].
           repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                   | cbn [cs_ctx proj1_sig]; exact HT | ].
           out_var_id Hav Hcov.
        -- destruct (sumbool_of_bool (flex_bound_ck Θ' α0)) as [Hfb | Hfb];
             [ exfalso; destruct Hnf as [_ Hf]; apply Hf;
               apply a_flex_var_iff_tvar; apply flex_bound_ck_flex_tvar;
               exact Hfb | ].
           cbv beta iota. do_pass (Q7 P0' eq_refl) Dc Hu Hcov Qd.
      * (* ⫯P0 ∼ → — U-UnivGhostR *)
        pose proof (e_consis_inv_univ_ghost_r_arrow Hd) as Dc.
        do_pass (Q7 P0' eq_refl) Dc Hu Hcov Qd.
      * (* ⫯P0 ∼ ∀ — U-ForallSyn *)
        destruct (e_consis_inv_forall_syn Hd) as [α [Qb [Hα [-> Dp]]]].
        pose proof (supply_fresh_notin S1) as Hz.
        simpl ftvar_in_pskl in Hcov.
        assert (HD1 : Δ1 [=] swap_atoms α (supply_fresh S1) Δ1)
          by (symmetry; apply swap_atoms_notin;
              clear - Hα Hz Hcov; fsetdec).
        assert (HD2 : add (supply_fresh S1) Δ2
                  [=] swap_atoms α (supply_fresh S1) (add α Δ2)).
        { rewrite swap_atoms_add.
          rewrite (swap_atoms_notin α (supply_fresh S1) Δ2)
            by (clear - Hα Hz Hcov; fsetdec).
          unfold swap_atom. destruct (α == α); [ reflexivity | congruence ]. }
        assert (HSq : add (supply_fresh S1) S1
                  [=] swap_atoms α (supply_fresh S1) (add α S1)).
        { rewrite swap_atoms_add.
          rewrite (swap_atoms_notin α (supply_fresh S1) S1)
            by (clear - Hα Hz; fsetdec).
          unfold swap_atom. destruct (α == α); [ reflexivity | congruence ]. }
        destruct (e_consis_swap Dp HD1 HD2 HSq) as [S1t [HS1t Dpt]].
        rewrite !swap_aenv_app, !swap_aenv_one_tvar in Dpt.
        rewrite (swap_aenv_fresh_id α (supply_fresh S1) Θ') in Dpt
          by (clear - Hα Hz Hcov; fsetdec).
        rewrite !swap_pskl_open_var in Dpt.
        rewrite (swap_pskl_fresh_id α (supply_fresh S1) (pskl_univ_ghost P0'))
          in Dpt by (clear - Hα Hz Hcov; simpl; fsetdec).
        rewrite (swap_pskl_fresh_id α (supply_fresh S1) Pb) in Dpt
          by (clear - Hα Hz Hcov; fsetdec).
        replace (swap_atom α (supply_fresh S1) α) with (supply_fresh S1)
          in Dpt by (unfold swap_atom; destruct (α == α); congruence).
        pose proof (dom_subset_ftvar_in_aenv Θ') as Hdm.
        assert (Hu' : uniq ((supply_fresh S1 ~ abind_tvar) ++ Θ'))
          by (apply uniq_push;
              [ exact Hu | clear - Hz Hcov Hdm; fsetdec ]).
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Pb
                      (pskl_var_f (supply_fresh S1))) as Hup2.
        assert (Hcov' : consis_call_cover
                  ((supply_fresh S1 ~ abind_tvar) ++ Θ')
                  (consis_call_consis Δ1 (add (supply_fresh S1) Δ2)
                     (pskl_univ_ghost P0')
                     (open_pskl_wrt_pskl Pb (pskl_var_f (supply_fresh S1))))
                  [<=] add (supply_fresh S1) S1).
        { cbn [consis_call_cover]. simpl ftvar_in_aenv.
          clear - Hcov Hup2. simpl in *. fsetdec. }
        kill_ccall (Q3 P0' Pb eq_refl eq_refl) Hu' Hcov' Dpt
          (swap_pskl α (supply_fresh S1) Qb) r Hr ps Hav HS HT HQ.
        destruct (consis_swaps_close Hα Hz Hav HS1t HS HT HQ)
          as (HTz & HavAll & HSAll & HQAll).
        destruct (@split_tvar_head_hit_eq _ _ _ HTz) as [pf Hsp].
        rewrite Hsp. cbv beta iota.
        exists (mk_consis_result (cs_supply r)
                  (swaps_aenv ps (swap_aenv α (supply_fresh S1) Θd))
                  (pskl_all_syn (close_pskl_wrt_pskl (supply_fresh S1) (cs_out r)))),
               ((α, supply_fresh S1) :: ps).
        split; [ reflexivity | ].
        repeat apply conj;
          [ exact HavAll | exact HSAll | reflexivity | exact HQAll ].
      * (* ⭐ ⫯P0 ∼ ◇ — U-Ghost is the only rule at a ◇ subject *)
        destruct (e_consis_inv_ghost_subject Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * (* ⫯P0 ∼ ⫯P — U-UnivGhost *)
        destruct (e_consis_inv_univ_ghost Hd) as [Qb [-> Dc]].
        assert (Hcov0 : consis_call_cover Θ'
                  (consis_call_consis Δ1 Δ2 P0' Pb) [<=] S1)
          by (clear - Hcov;
              cbn [consis_call_cover ftvar_in_pskl] in *; fsetdec).
        kill_ccall (Q4 P0' Pb eq_refl eq_refl) Hu Hcov0 Dc Qb
          r Hr ps Hav HS HT HQ.
        exists (mk_consis_result (cs_supply r) (cs_ctx r)
                  (pskl_univ_ghost (cs_out r))), ps.
        split; [ reflexivity | ].
        repeat apply conj; [ exact Hav | cbn [cs_supply]; exact HS
                | cbn [cs_ctx]; exact HT | ].
        cbn [cs_out]. rewrite swaps_pskl_univ_ghost. f_equal. exact HQ.

Qed.

(* ===================================================================== *)
(*  §8  The consistency implementation entry point                         *)
(*                                                                        *)
(*  The side conditions are prop_consis.v §4's, verbatim: the context is  *)
(*  [uniq] and the supply covers it — ⚠️ including [Δ1] and [Δ2], which    *)
(*  are reachable from neither the context nor the skeletons.             *)
(* ===================================================================== *)

(** ⚙ The same over [e_consis_impl], i.e. at an ARBITRARY order proof rather
    than at [e_consis_order_total]'s.  Levels 7/8 need this form and not the
    runner's: [e_split_impl]'s flexible clause calls [e_consis_impl] with the
    obligation proofs [Equations] generated, and a completeness statement
    that fixes the domain argument does not apply to them. *)
Corollary e_consis_impl_complete : forall Δ1 Δ2 S0 Θ P0 P
    (HP0 : lc_pskl P0) (HP : lc_pskl P) (HD : aenv_defs_mono Θ)
    (H : e_consis_order Δ1 Δ2 S0 Θ P0 P) Sd Θd Qd,
  {{ S0 ↝ Sd ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Qd ⊣ Θd }}e ->
  uniq Θ ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P ∪ Δ1 ∪ Δ2 [<=] S0 ->
  exists r ps,
    e_consis_impl Δ1 Δ2 S0 Θ P0 P HP0 HP HD H = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] cs_supply (proj1_sig r)
    /\ swaps_aenv ps Θd = cs_ctx (proj1_sig r)
    /\ swaps_pskl ps Qd = cs_out (proj1_sig r).
Proof.
  intros * Hd Hu Hcov.
  set (Ho := e_consis_order_to_call _ _ _ _ _ _ H).
  destruct (e_consis_call_impl_complete Ho (conj HP0 HP) HD Ho Hu Hcov
              Sd Θd Qd Hd) as [r0 [ps [Heq [Hav [HS [HT HQ]]]]]].
  unfold e_consis_impl. fold Ho.
  destruct (e_consis_call_impl (consis_call_consis Δ1 Δ2 P0 P) S0 Θ
              (conj HP0 HP) HD Ho) as [ [rr Hrr] | ] eqn:Hcl;
    try rewrite Hcl in Heq; cbn [consis_call_answer proj1_sig] in Heq;
    [ inversion Heq; subst | discriminate ].
  eexists; exists ps.
  split; [ reflexivity | ].
  split; [ exact Hav | ]. split; [ exact HS | ].
  split; [ exact HT | exact HQ ].
Qed.
