(** ext_algo — §8c.16 §D, campaign level 6, STEP 2:
    ⭐⭐⭐ EXTRACTION IS DETERMINISTIC UP TO A FRESH RENAMING —
    SUPPLY INCLUDED.  [e_extract_det], §9.

    §1  equivariance along a CHAIN, for the collection, the solve layer,
        [guess] and [extract] — the [_swaps] iterations §8c.16 §D found
        missing (the SINGLE-swap versions are prop_look.v §6,
        prop_solve.v §5, prop_guess.v and prop_extract.v)
    §2  the collection's ROOT INVERSIONS — §8c.16 §E's overlap table
    §3  [e_lookeq_rel]      — the eq collection
    §4  [e_looksub_rel]     — the sub collection
    §5  [e_solve_eq_rel]    — the solve layer's EQ half
    §6  [e_guess_rel]       — [guess], three lines off [e_guess_mono_rel]
    §7  [e_solve_sub_rel]   — the solve layer's SUB half (⭐ this is what
        GUARD 5 bought: before it the statement was FALSE, §8c.18)
    §8  [e_solve_cstr_rel]  — the constraint fold
    §9  ⭐⭐⭐ [e_extract_rel] / [e_extract_det] — the composition

    ⭐ WHY A CHAIN AND NOT A PAIRING.  The statement STEP 2 has to hit is

    {{ S0 ↝ S1  ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ  ↪ Q  }}e ->
    {{ S0 ↝ S1' ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ' ↪ Q' }}e ->
      exists ps, … /\ swaps_atoms ps S1 [=] S1'
                  /\ swaps_aenv ps Ξ = Ξ' /\ swaps_pskl ps Q = Q'

    — and its SUPPLY conjunct is what rules the [a_]-level pairing form
    (prop_solve_det.v §3/§4) out: that form carries no supply at all, and
    bridging it would need a separate "the supply increment is the block
    domain plus the openers" invariant per judgement, with three DIFFERENT
    fates for an opener (LEAKED into 𝒞 by [LS-ForallR], LEAKED into the
    output by [SS-ForallR], CLOSED by [SS-ForallL]).  ⚙ The template is
    prop_consis_complete.v §3/§3b — [e_guess_mono_rel_n] / [e_guess_mono_rel],
    already Qed and already a SIZE induction for the reason this level needs
    one (the arrow rows thread, so the second halves sit at DIFFERENT input
    supplies and a derivation-indexed IH would be pinned to one).

    ⚙ TWO CONVENTIONS THIS FILE KEEPS THROUGHOUT.  (1) Every [_rel_stmt]
    puts the DERIVATION before its size and coverage premises, so that
    [IH _ … _ D ltac:(lia) …] elaborates the [ltac:] AFTER [D] has fixed
    every underscore — in front of [D] the same [ltac:] runs against evars.
    (2) Names are taken off [match type of D1], never off [inversion]'s
    generated ones.

    ⛔ WHAT IT TOOK.  The headline was refuted THREE TIMES on the way, each
    time by a missing DISPATCH GUARD one layer further down, and each
    refutation is retracted by the guard that answers it:
    [cex/probe_extract_supply_drift.v] (absence-first, §8c.14),
    [cex/probe_extract_flexr_ug2_drift.v] (FlexR-priority, §8c.16), and
    [cex/probe_solve_sub_forall_r_drift.v] (SOLVE-dispatch, §8c.18–§8c.19 —
    at a VARIABLE subject against a ghost-free [∀] in check mode [SS-Var]
    and [SS-ForallR] both fired and differed ONLY in supply, by one atom).
    docs/HANDOFF-extractable-algo-encoding.md §8c.14–§8c.19. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_dec.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.prop_guess.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.prop_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.prop_solve.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.prop_extract.
Require Import src.fresco.ext_algo.prop_solve_det.
Require Import src.fresco.ext_algo.prop_consis_complete.

Set Implicit Arguments.

Local Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §1  EQUIVARIANCE ALONG A CHAIN                                        *)
(*                                                                        *)
(*  Each of these is prop_consis_complete.v §3's iteration verbatim: the   *)
(*  empty chain is the judgement's SUPPLY RESPECT, and a cons applies the  *)
(*  single swap and recurses.  ⚙ The output supply is carried up to [=]    *)
(*  and never as a term, which is what lets a caller feed one stage's      *)
(*  output straight into the next.                                        *)
(* ===================================================================== *)

Lemma e_looksub_swaps : forall ps S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ) ⊢ (swaps_pskl ps P)
       ≼[ (swaps_atom ps α) , m ] (swaps_pskl ps P')
       ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_cstrs ps C) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact ((proj1 e_looksub_lookeq_supply_respect)
             _ _ _ _ _ _ _ _ _ Hd _ Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct ((proj1 (e_looksub_lookeq_swap a b))
                _ _ _ _ _ _ _ _ _ Hd _ Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_lookeq_swaps : forall ps S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ) ⊢ (swaps_pskl ps P)
       ∼[ (swaps_atom ps α) ] (swaps_pskl ps P')
       ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_cstrs ps C) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact ((proj2 e_looksub_lookeq_supply_respect)
             _ _ _ _ _ _ _ _ Hd _ Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct ((proj2 (e_looksub_lookeq_swap a b))
                _ _ _ _ _ _ _ _ Hd _ Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_solve_sub_swaps : forall ps S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ) ⊢ₛ (swaps_pskl ps P) ≼[ m ]
       (swaps_pskl ps Q) ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_pskl ps P') }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_solve_sub_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_solve_sub_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_solve_eq_swaps : forall ps S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ) ⊢ₑ (swaps_pskl ps P) ∼
       (swaps_pskl ps Q) ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_pskl ps P') }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_solve_eq_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_solve_eq_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_solve_cstr_swaps : forall ps S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ) ⊩ (swaps_cstrs ps C) ⨾ (swaps_pskl ps P)
       ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_pskl ps Q) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_solve_cstr_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_solve_cstr_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_guess_swaps : forall ps S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    e_guess S0' NM (swaps_pskl ps Q) S1' (swaps_aenv ps Ξ)
      (swaps_pskl ps Q').
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_guess_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_guess_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_extract_swaps : forall ps S0 Θ0 NM α m P P' S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0) ⊢ (swaps_pskl ps P)
       ⊳[ NM , (swaps_atom ps α) , m ] (swaps_pskl ps P')
       ⤳ (swaps_aenv ps Ξ) ↪ (swaps_pskl ps Q) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_extract_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_extract_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

(* --------------------------------------------------------------------- *)
(*  §1b  the two [swaps_cstrs] facts the ARROW rows need                  *)
(* --------------------------------------------------------------------- *)

Lemma swaps_cstrs_app : forall ps1 ps2 C,
  swaps_cstrs (ps1 ++ ps2) C = swaps_cstrs ps2 (swaps_cstrs ps1 C).
Proof.
  induction ps1 as [ | [a b] ps1 IH ]; intros; simpl; auto.
Qed.

Lemma swaps_cstrs_app_dist : forall ps C1 C2,
  swaps_cstrs ps (C1 ++ C2) = swaps_cstrs ps C1 ++ swaps_cstrs ps C2.
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; auto.
  rewrite swap_cstrs_app. apply IH.
Qed.

(* ===================================================================== *)
(*  §2  ROOT INVERSIONS FOR THE COLLECTION — §8c.16 §E's table, as        *)
(*      lemmas                                                            *)
(*                                                                        *)
(*  ⭐ EVERY ONE OF THESE IS A CONSEQUENCE OF THE FOUR DISPATCH GUARDS,    *)
(*  and none of them was provable before them.  The audit (§8c.16 §E) is  *)
(*  what says the cell admits exactly one rule; these lemmas are that     *)
(*  audit machine-checked, one per cell the [_rel] induction visits.      *)
(*                                                                        *)
(*  ⚙ The α-FREE cells are NOT here: there the rules genuinely overlap    *)
(*  and the audit's answer is that they COINCIDE, which is                *)
(*  [e_lookeq_absent_pins] (prop_look.v §2c) and not an inversion.        *)
(* ===================================================================== *)

(** ⚙ THE KILLER.  Every branch [inversion] leaves that the guards exclude
    dies one of five ways, and none of the arms names a hypothesis the
    [subst] could have renamed. *)
Local Ltac le_kill :=
  try solve
    [ assumption
    | auto
    | exfalso; congruence
    | exfalso;
      match goal with
      | Hn : ?a `notin` ftvar_in_pskl (pskl_var_f ?a) |- _ =>
          simpl in Hn; clear - Hn; fsetdec
      end
    | exfalso;
      match goal with
      | Hn : ?a `notin` ftvar_in_pskl _, Hi : ?a `in` ftvar_in_pskl _ |- _ =>
          simpl in Hn, Hi; clear - Hn Hi; fsetdec
      end
    | exfalso;
      match goal with
      | Hoff : flex_r_off _ (pskl_var_f ?b), Hf : a_flex_tvar _ ?b |- _ =>
          exact (Hoff b eq_refl Hf)
      end
    | exfalso;
      match goal with
      | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
      end ].

(** subject [α] itself — [LE-Var].  Unconditional: [LE-Absent] wants the
    marker absent, and [LE-Vacuous] / [LE-FlexR] / [LE-UnivGhostR] all carry
    [P <> α]. *)
Lemma e_lookeq_inv_var : forall S0 Θ α P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_var_f α) ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  S1 = S0 /\ Ξ = nil /\ C = a_cstr_eq P' :: nil.
Proof.
  intros * H; inversion H; subst; le_kill.
Qed.

(** counterpart [◇] — [LE-Vacuous].  [LE-UnivGhost2] is barred because [◇]
    is not [guarded_pskl]. *)
Lemma e_lookeq_inv_ghost : forall S0 Θ α P S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] pskl_ghost ⤳ Ξ ⨾ C }}e ->
  P <> pskl_var_f α ->
  α `in` ftvar_in_pskl P ->
  S1 = S0 /\ Ξ = nil /\ C = nil.
Proof.
  intros * H Hne Hα; inversion H; subst; le_kill.
Qed.

(** ⭐ counterpart a FLEXIBLE variable — [LE-FlexR].  This is the cell guard
    4 is about: without the hat on [LE-FlexR] and [flex_r_off] on
    [LE-UnivGhost2] the two rows race here and answer with UNRELATED
    variables (§8c.16 §A). *)
Lemma e_lookeq_inv_flex_r : forall S0 Θ α P β S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] (pskl_var_f β) ⤳ Ξ ⨾ C }}e ->
  P <> pskl_var_f α ->
  a_flex_tvar Θ β ->
  α `in` ftvar_in_pskl P ->
  exists α1, α1 `notin` S0 /\ S1 = add α1 S0
    /\ Ξ = (α1 ~ abind_flex_mono) ++ nil
    /\ C = a_cstr_eq (pskl_var_f α1) :: nil.
Proof.
  intros * H Hne Hflx Hα; inversion H; subst; le_kill.
  match goal with
  | Hfr : ?a1 `notin` S0 |- _ => exists a1
  end.
  repeat split; solve [ assumption | reflexivity ].
Qed.

(** ⭐ subject [⫯Q] against a guarded, flex-r-OFF counterpart —
    [LE-UnivGhost2].  Both guards are load bearing: [guarded_pskl] kills
    [LE-Vacuous] / [LE-UnivGhost] / [LE-UnivGhost1] / [LE-UnivGhostR], and
    [flex_r_off] kills [LE-FlexR]. *)
Lemma e_lookeq_inv_ug2 : forall S0 Θ α Q P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost Q) ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  guarded_pskl P' ->
  flex_r_off Θ P' ->
  α `in` ftvar_in_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ Q ∼[ α ] P' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hg Hoff Hα; inversion H; subst; le_kill.
Qed.

(** subject [⫯Q] against [⫯Q'] — [LE-UnivGhost]. *)
Lemma e_lookeq_inv_ug : forall S0 Θ α Q Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost Q) ∼[ α ] (pskl_univ_ghost Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ Q ∼[ α ] Q' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
Qed.

(** subject [⫯Q] against [∀Q'] — [LE-UnivGhost1], and it OPENS. *)
Lemma e_lookeq_inv_ug1 : forall S0 Θ α Q Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost Q) ∼[ α ] (pskl_all_syn Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl Q ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ (pskl_univ_ghost Q)
       ∼[ α ] (open_pskl_wrt_pskl Q' (pskl_var_f β)) ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

(** subject [∀Q] against [∀Q'] — [LE-ForallInh], both sides open. *)
Lemma e_lookeq_inv_forall_inh : forall S0 Θ α Q Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn Q) ∼[ α ] (pskl_all_syn Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl (pskl_all_syn Q) ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl Q (pskl_var_f β))
       ∼[ α ] (open_pskl_wrt_pskl Q' (pskl_var_f β)) ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

(** subject [∀Q] against [⫯Q'] — [LE-ForallSyn]: the SUBJECT opens and the
    counterpart is untouched. *)
Lemma e_lookeq_inv_forall_syn : forall S0 Θ α Q Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn Q) ∼[ α ] (pskl_univ_ghost Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl (pskl_all_syn Q) ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl Q (pskl_var_f β))
       ∼[ α ] (pskl_univ_ghost Q') ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

(** [LE-Arrow] — the THREADING row. *)
Lemma e_lookeq_inv_arrow : forall S0 Θ α P1 P2 P1' P2' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_arrow P1 P2) ∼[ α ] (pskl_arrow P1' P2')
     ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl (pskl_arrow P1 P2) ->
  exists Sm Ξ1 Ξ2 C1 C2,
    Ξ = Ξ1 ++ Ξ2 /\ C = C1 ++ C2 /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e /\
    {{ Sm ↝ S1 ⊨ Θ ⊢ P2 ∼[ α ] P2' ⤳ Ξ2 ⨾ C2 }}e.
Proof.
  intros * H Hα; inversion H; subst;
    try solve [ exfalso;
                match goal with
                | Hn : ?a `notin` ftvar_in_pskl _,
                  Hi : ?a `in` ftvar_in_pskl _ |- _ =>
                    simpl in Hn, Hi; clear - Hn Hi; fsetdec
                end ].
  match goal with
  | Ha : e_lookeq S0 _ _ P1 P1' ?sm ?x1 ?c1,
    Hb : e_lookeq ?sm _ _ P2 P2' S1 ?x2 ?c2 |- _ =>
      exists sm, x1, x2, c1, c2
  end.
  repeat split; assumption.
Qed.

(** counterpart [⫯Q'] at a GUARDED subject — [LE-UnivGhostR]. *)
Lemma e_lookeq_inv_ug_r : forall S0 Θ α P Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] (pskl_univ_ghost Q') ⤳ Ξ ⨾ C }}e ->
  P <> pskl_var_f α ->
  guarded_pskl P ->
  α `in` ftvar_in_pskl P ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] Q' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hne Hg Hα; inversion H; subst; le_kill.
Qed.

(** ⭐ THE THREE SHAPE-SPECIFIC [LE-UnivGhost2] INVERSIONS.  At a CONCRETE
    counterpart the shape does the work [guarded_pskl] does in the general
    lemma, so no local-closure obligation arises — which matters, because the
    [_rel] induction has no [lc_pskl] to hand. *)

(* ===================================================================== *)
(*  §3  ⭐ THE COLLECTION'S EQ LAYER IS DETERMINISTIC UP TO A FRESH       *)
(*      RENAMING                                                          *)
(*                                                                        *)
(*  ⚙ THE DERIVATION COMES FIRST in the statement, before the size and    *)
(*  coverage premises.  That is deliberate: an [IH _ … _ D ltac:(lia) …]   *)
(*  elaborates the [ltac:] AFTER [D] has fixed every underscore, where     *)
(*  the same [ltac:] in front of [D] would run against evars.             *)
(*                                                                        *)
(*  ⚙ SIZE induction, not induction on either derivation — [LE-Arrow]      *)
(*  threads, so its second halves sit at DIFFERENT input supplies and a    *)
(*  derivation-indexed IH would be pinned to one (prop_consis_complete.v   *)
(*  §3b's reason, verbatim).                                              *)
(* ===================================================================== *)

Local Ltac rel4 := split; [ | split; [ | split ] ].

Definition lookeq_rel_stmt (n : nat) : Prop :=
  forall S0 Θ α P P' S1 Ξ C,
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
    size_pskl P + size_pskl P' <= n ->
    add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
    forall S1' Ξ' C',
      {{ S0 ↝ S1' ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ' ⨾ C' }}e ->
      exists ps,
        (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
        swaps_atoms ps S1 [=] S1' /\
        swaps_aenv ps Ξ = Ξ' /\
        swaps_cstrs ps C = C'.

Lemma e_lookeq_rel_n : forall n, lookeq_rel_stmt n.
Proof.
  induction n as [ | n IH ]; unfold lookeq_rel_stmt in *.
  { intros S0 Θ α P P' S1 Ξ C D1 Hsz; exfalso;
      destruct P; simpl in Hsz; lia. }
  intros S0 Θ α P P' S1 Ξ C D1 Hsz Hcov S1' Ξ' C' D2.
  destruct (sumbool_of_bool (mem α (ftvar_in_pskl P))) as [Hmem | Hmem].
  2:{ (* ---- the α-FREE collapse: both sides emit and spend nothing ---- *)
      apply mem_false_notin in Hmem.
      destruct (e_lookeq_absent_pins D1 Hmem) as [-> [-> HS]].
      destruct (e_lookeq_absent_pins D2 Hmem) as [-> [-> HS']].
      exists nil. rel4; simpl; try reflexivity.
      - intros ? ? [].
      - clear - HS HS'. fsetdec. }
  apply mem_true_in in Hmem. rename Hmem into HαP.
  inversion D1; subst.

  - (* LE-Var — the subject IS the marker *)
    destruct (e_lookeq_inv_var D2) as [-> [-> ->]].
    exists nil. rel4; simpl; try reflexivity. intros ? ? [].

  - (* LE-Absent — excluded by the occurrence split *)
    exfalso.
    match goal with
    | Hn : ?a `notin` ftvar_in_pskl _ |- _ => clear - Hn HαP; fsetdec
    end.

  - (* LE-Vacuous — counterpart ◇ *)
    match goal with
    | Hne : _ <> pskl_var_f α |- _ => rename Hne into Hnev
    end.
    destruct (e_lookeq_inv_ghost D2 Hnev HαP) as [-> [-> ->]].
    exists nil. rel4; simpl; try reflexivity. intros ? ? [].

  - (* LE-FlexR — the GENERATING row: one fresh flexible on each side *)
    match goal with
    | Hne : _ <> pskl_var_f α |- _ => rename Hne into Hnev
    end.
    match goal with
    | Hf : a_flex_tvar Θ ?b |- _ => rename Hf into Hflx
    end.
    match goal with
    | Hfr : ?a1 `notin` S0 |- _ => rename Hfr into Hα1; rename a1 into γ1
    end.
    destruct (e_lookeq_inv_flex_r D2 Hnev Hflx HαP)
      as (γ2 & Hγ2 & -> & -> & ->).
    exists ((γ1, γ2) :: nil). rel4.
    + intros ? ? [Heqp | []]. inversion Heqp; subst. split; assumption.
    + cbn [swaps_atoms]. rewrite swap_atoms_add.
      rewrite (swap_atoms_notin γ1 γ2 S0 Hα1 Hγ2).
      replace (swap_atom γ1 γ2 γ1) with γ2
        by (unfold swap_atom; destruct (γ1 == γ1); congruence).
      reflexivity.
    + rewrite swaps_aenv_app_dist, swaps_aenv_one_flex, swaps_aenv_nil.
      cbn [swaps_atom].
      replace (swap_atom γ1 γ2 γ1) with γ2
        by (unfold swap_atom; destruct (γ1 == γ1); congruence).
      reflexivity.
    + cbn [swaps_cstrs swap_cstrs List.map swap_cstr swaps_pskl swap_pskl].
      replace (swap_atom γ1 γ2 γ1) with γ2
        by (unfold swap_atom; destruct (γ1 == γ1); congruence).
      reflexivity.

  - (* LE-Arrow — the THREADING row *)
    match type of D1 with
    | e_lookeq _ _ _ (pskl_arrow ?p1 ?p2) (pskl_arrow ?q1 ?q2) _ _ _ =>
        rename p1 into Pa; rename p2 into Pb;
        rename q1 into Pa'; rename q2 into Pb'
    end.
    destruct (e_lookeq_inv_arrow D1 HαP)
      as (Sm & X1 & X2 & Cc1 & Cc2 & -> & -> & D1a & D1b).
    destruct (e_lookeq_inv_arrow D2 HαP)
      as (Sm' & X1' & X2' & Cc1' & Cc2' & -> & -> & D2a & D2b).
    simpl in Hsz, Hcov, HαP.
    (* --- the FIRST halves, at the common input supply --- *)
    destruct (IH _ _ _ _ _ _ _ _ D1a ltac:(lia)
                 ltac:(clear - Hcov; fsetdec) _ _ _ D2a)
      as [ps1 [Hav1 [HS1 [HX1 HC1]]]].
    (* --- move side 1's SECOND half onto side 2's rails --- *)
    assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (Hα1 : swaps_atom ps1 α = α)
      by (apply swaps_atom_notin; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (HPb : swaps_pskl ps1 Pb = Pb)
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (HPb' : swaps_pskl ps1 Pb' = Pb')
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (Heq2 : Sm' [=] swaps_atoms ps1 Sm) by (symmetry; exact HS1).
    destruct (e_lookeq_swaps ps1 D1b Heq2) as [S2t [HS2t D1bt]].
    rewrite HΘ1, Hα1, HPb, HPb' in D1bt.
    (* --- the SECOND halves, now at the SAME input supply --- *)
    pose proof (e_lookeq_supply_grows D2a) as Hgr1'.
    destruct (IH _ _ _ _ _ _ _ _ D1bt ltac:(lia)
                 ltac:(clear - Hcov Hgr1'; fsetdec) _ _ _ D2b)
      as [ps2 [Hav2 [HS2 [HX2 HC2]]]].
    (* --- what the SECOND renaming must leave alone: side 2's first yield --- *)
    pose proof (e_lookeq_generated_in_supply D2a) as Hdom1'.
    pose proof (e_lookeq_block_ftvar D2a) as Hftv1'.
    pose proof ((proj2 e_looksub_lookeq_cstr_ftvar) _ _ _ _ _ _ _ _ D2a)
      as Hcs1'.
    assert (HX1' : swaps_aenv ps2 X1' = X1')
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hdom1' Hftv1'; fsetdec).
    assert (HC1' : swaps_cstrs ps2 Cc1' = Cc1')
      by (apply swaps_cstrs_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcs1' Hcov Hgr1'; fsetdec).
    exists (ps1 ++ ps2). rel4.
    + intros a0 b0 Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exact (Hav1 a0 b0 Hin).
      * destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
        split; clear - Ha0 Hb0 Hgr1'; fsetdec.
    + rewrite swaps_atoms_app. rewrite <- HS2.
      apply swaps_atoms_cong. symmetry. exact HS2t.
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_cstrs_app, !swaps_cstrs_app_dist, HC1, HC2, HC1'.
      reflexivity.

  - (* LE-ForallInh — (∀,∀): both sides open, one transposition pairs them *)
    match type of D1 with
    | e_lookeq _ _ _ (pskl_all_syn ?q) (pskl_all_syn ?q') _ _ _ =>
        rename q into Qs; rename q' into Qt
    end.
    destruct (e_lookeq_inv_forall_inh D1 HαP) as (β1 & Hβ1 & Dp).
    destruct (e_lookeq_inv_forall_inh D2 HαP) as (β2 & Hβ2 & Dp').
    simpl in Hsz, Hcov, HαP.
    assert (Heqs : add β2 S0 [=] swap_atoms β1 β2 (add β1 S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β1 β2 S0 Hβ1 Hβ2).
      unfold swap_atom. destruct (β1 == β1); [ | congruence ]. reflexivity. }
    destruct (e_lookeq_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite ! swap_pskl_open_var in Dpt.
    rewrite (@swap_pskl_fresh_id β1 β2 Qs) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_pskl_fresh_id β1 β2 Qt) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_atom_other β1 β2 α) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    replace (swap_atom β1 β2 β1) with β2 in Dpt
      by (unfold swap_atom; destruct (β1 == β1); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Qs (pskl_var_f β2))
      as Hup1.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Qt (pskl_var_f β2))
      as Hup2.
    destruct (IH _ _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hup1 Hup2; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HC']]]].
    exists ((β1, β2) :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_cstrs]. exact HC'.

  - (* LE-ForallSyn — (∀,⫯): the SUBJECT opens, the counterpart is fixed *)
    match type of D1 with
    | e_lookeq _ _ _ (pskl_all_syn ?q) (pskl_univ_ghost ?q') _ _ _ =>
        rename q into Qs; rename q' into Qt
    end.
    destruct (e_lookeq_inv_forall_syn D1 HαP) as (β1 & Hβ1 & Dp).
    destruct (e_lookeq_inv_forall_syn D2 HαP) as (β2 & Hβ2 & Dp').
    simpl in Hsz, Hcov, HαP.
    assert (Heqs : add β2 S0 [=] swap_atoms β1 β2 (add β1 S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β1 β2 S0 Hβ1 Hβ2).
      unfold swap_atom. destruct (β1 == β1); [ | congruence ]. reflexivity. }
    destruct (e_lookeq_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite swap_pskl_open_var in Dpt.
    rewrite (@swap_pskl_fresh_id β1 β2 Qs) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_pskl_fresh_id β1 β2 (pskl_univ_ghost Qt)) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    rewrite (@swap_atom_other β1 β2 α) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    replace (swap_atom β1 β2 β1) with β2 in Dpt
      by (unfold swap_atom; destruct (β1 == β1); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Qs (pskl_var_f β2))
      as Hup1.
    destruct (IH _ _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                       simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hup1; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HC']]]].
    exists ((β1, β2) :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_cstrs]. exact HC'.

  - (* LE-UnivGhost — (⫯,⫯): both ⫯s vanish *)
    match type of D1 with
    | e_lookeq _ _ _ (pskl_univ_ghost ?q) (pskl_univ_ghost ?q') _ _ _ =>
        rename q into Qs; rename q' into Qt
    end.
    assert (Hα' : α `in` ftvar_in_pskl Qs) by (simpl in HαP; exact HαP).
    pose proof (e_lookeq_inv_ug D1 Hα') as Dp.
    pose proof (e_lookeq_inv_ug D2 Hα') as Dp'.
    simpl in Hsz, Hcov.
    exact (IH _ _ _ _ _ _ _ _ Dp ltac:(lia)
              ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp').

  - (* LE-UnivGhost1 — (⫯,∀): the COUNTERPART opens *)
    match type of D1 with
    | e_lookeq _ _ _ (pskl_univ_ghost ?q) (pskl_all_syn ?q') _ _ _ =>
        rename q into Qs; rename q' into Qt
    end.
    assert (Hα' : α `in` ftvar_in_pskl Qs) by (simpl in HαP; exact HαP).
    destruct (e_lookeq_inv_ug1 D1 Hα') as (β1 & Hβ1 & Dp).
    destruct (e_lookeq_inv_ug1 D2 Hα') as (β2 & Hβ2 & Dp').
    simpl in Hsz, Hcov, HαP.
    assert (Heqs : add β2 S0 [=] swap_atoms β1 β2 (add β1 S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β1 β2 S0 Hβ1 Hβ2).
      unfold swap_atom. destruct (β1 == β1); [ | congruence ]. reflexivity. }
    destruct (e_lookeq_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite swap_pskl_open_var in Dpt.
    rewrite (@swap_pskl_fresh_id β1 β2 (pskl_univ_ghost Qs)) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    rewrite (@swap_pskl_fresh_id β1 β2 Qt) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_atom_other β1 β2 α) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    replace (swap_atom β1 β2 β1) with β2 in Dpt
      by (unfold swap_atom; destruct (β1 == β1); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Qt (pskl_var_f β2))
      as Hup2.
    destruct (IH _ _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                       simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hup2; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HC']]]].
    exists ((β1, β2) :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_cstrs]. exact HC'.

  - (* LE-UnivGhost2 — ⭐ THE GUARDED ROW: the subject's ⫯ is stripped *)
    match type of D1 with
    | e_lookeq _ _ _ (pskl_univ_ghost ?q) _ _ _ _ => rename q into Qs
    end.
    match goal with
    | Hg : guarded_pskl _ |- _ => rename Hg into Hgd
    end.
    match goal with
    | Ho : flex_r_off _ _ |- _ => rename Ho into Hoff
    end.
    assert (Hα' : α `in` ftvar_in_pskl Qs) by (simpl in HαP; exact HαP).
    pose proof (e_lookeq_inv_ug2 D1 Hgd Hoff Hα') as Dp.
    pose proof (e_lookeq_inv_ug2 D2 Hgd Hoff Hα') as Dp'.
    simpl in Hsz, Hcov.
    exact (IH _ _ _ _ _ _ _ _ Dp ltac:(lia)
              ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp').

  - (* LE-UnivGhostR — the COUNTERPART's ⫯ is stripped *)
    match type of D1 with
    | e_lookeq _ _ _ _ (pskl_univ_ghost ?q') _ _ _ => rename q' into Qt
    end.
    match goal with
    | Hne : _ <> pskl_var_f α |- _ => rename Hne into Hnev
    end.
    match goal with
    | Hg : guarded_pskl _ |- _ => rename Hg into Hgd
    end.
    pose proof (e_lookeq_inv_ug_r D1 Hnev Hgd HαP) as Dp.
    pose proof (e_lookeq_inv_ug_r D2 Hnev Hgd HαP) as Dp'.
    simpl in Hsz, Hcov.
    exact (IH _ _ _ _ _ _ _ _ Dp ltac:(lia)
              ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp').
Qed.

Corollary e_lookeq_rel : forall S0 Θ α P P' S1 Ξ C S1' Ξ' C',
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  {{ S0 ↝ S1' ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ' ⨾ C' }}e ->
  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_cstrs ps C = C'.
Proof.
  intros * D1 D2 Hcov.
  exact (e_lookeq_rel_n D1 (le_n _) Hcov D2).
Qed.

(* ===================================================================== *)
(*  §4  ROOT INVERSIONS AND DETERMINISM FOR THE SUB LAYER                 *)
(*                                                                        *)
(*  The sub layer never calls itself through the eq layer, so §3 is a     *)
(*  finished tool here: [LS-Check] and [LS-Arrow]'s first half go to      *)
(*  [e_lookeq_rel], and only [LS-ForallR] / [LS-Arrow]'s second half /    *)
(*  [LS-ForallL] / [LS-UnivGhostL] need the size IH.                     *)
(* ===================================================================== *)

Local Ltac ls_kill :=
  try solve
    [ assumption
    | auto
    | exfalso; congruence
    | exfalso;
      match goal with
      | Hn : ?a `notin` ftvar_in_pskl (pskl_var_f ?a) |- _ =>
          simpl in Hn; clear - Hn; fsetdec
      end
    | exfalso;
      match goal with
      | Hn : ?a `notin` ftvar_in_pskl _, Hi : ?a `in` ftvar_in_pskl _ |- _ =>
          simpl in Hn, Hi; clear - Hn Hi; fsetdec
      end
    | exfalso;
      match goal with
      | Hoff : forall_r_off _ (pskl_all_syn ?B),
        Hgf : pskl_ghost_free (pskl_all_syn ?B) |- _ =>
          exact (Hoff B eq_refl eq_refl Hgf)
      end
    | exfalso;
      match goal with
      | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
      end ].

(** subject [α] itself — [LS-Var]. *)
Lemma e_looksub_inv_var : forall S0 Θ α m P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_var_f α) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  S1 = S0 /\ Ξ = nil /\ C = a_cstr_sub m P' :: nil.
Proof.
  intros * H; inversion H; subst; ls_kill.
Qed.

(** counterpart [◇] — [LS-Vacuous].  [LS-ForallL] / [LS-UnivGhostL] carry
    [P' <> ◇] and [LS-Check] wants a guarded counterpart. *)
Lemma e_looksub_inv_ghost : forall S0 Θ α m P S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] pskl_ghost ⤳ Ξ ⨾ C }}e ->
  P <> pskl_var_f α ->
  α `in` ftvar_in_pskl P ->
  S1 = S0 /\ Ξ = nil /\ C = nil.
Proof.
  intros * H Hne Hα; inversion H; subst; ls_kill.
Qed.

(** ⭐ the CHECK cell — both sides guarded, mode [TC].  [LS-Arrow] is barred
    by the MODE (it concludes at [mode_fn]), the two binder-left rows by the
    guarded SUBJECT, and [LS-ForallR] / [LS-Vacuous] by the guarded
    COUNTERPART. *)
Lemma e_looksub_inv_check : forall S0 Θ α A B S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ A ≼[ α , mode_tc ] B ⤳ Ξ ⨾ C }}e ->
  A <> pskl_var_f α ->
  guarded_pskl A ->
  guarded_pskl B ->
  α `in` ftvar_in_pskl A ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ A ∼[ α ] B ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H HneA HgA HgB Hα; inversion H; subst; ls_kill.
Qed.

(** ⭐ the ForallR cell — a GHOST-FREE [∀] counterpart at [TC].  The
    ForallR-PRIORITY guard is exactly what bars [LS-ForallL] and
    [LS-UnivGhostL] here. *)
Lemma e_looksub_inv_forall_r : forall S0 Θ α A B S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ A ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C }}e ->
  pskl_ghost_free (pskl_all_syn B) ->
  A <> pskl_var_f α ->
  α `in` ftvar_in_pskl A ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ A ≼[ α , mode_tc ]
       (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hgf HneA Hα; inversion H; subst; ls_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

(** [LS-Arrow] — the THREADING row; its first half is an EQ collection. *)
Lemma e_looksub_inv_arrow : forall S0 Θ α m P1 P2 P1' P2' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_arrow P1 P2) ≼[ α , (mode_fn m) ]
     (pskl_arrow P1' P2') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl (pskl_arrow P1 P2) ->
  exists Sm Ξ1 Ξ2 C1 C2,
    Ξ = Ξ1 ++ Ξ2 /\ C = C1 ++ C2 /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e /\
    {{ Sm ↝ S1 ⊨ Θ ⊢ P2 ≼[ α , m ] P2' ⤳ Ξ2 ⨾ C2 }}e.
Proof.
  intros * H Hα; inversion H; subst;
    try solve [ exfalso;
                match goal with
                | Hn : ?a `notin` ftvar_in_pskl _,
                  Hi : ?a `in` ftvar_in_pskl _ |- _ =>
                    simpl in Hn, Hi; clear - Hn Hi; fsetdec
                end ].
  match goal with
  | Ha : e_lookeq S0 _ _ P1 P1' ?sm ?x1 ?c1,
    Hb : e_looksub ?sm _ _ _ P2 P2' S1 ?x2 ?c2 |- _ =>
      exists sm, x1, x2, c1, c2
  end.
  repeat split; assumption.
Qed.

(** [LS-ForallL] — the subject peels. *)
Lemma e_looksub_inv_forall_l : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  P' <> pskl_ghost ->
  forall_r_off m P' ->
  α `in` ftvar_in_pskl (pskl_all_syn P) ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hnh Hoff Hα; inversion H; subst; ls_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

(** [LS-UnivGhostL] — the subject's [⫯] is stripped. *)
Lemma e_looksub_inv_univ_ghost_l : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  P' <> pskl_ghost ->
  forall_r_off m P' ->
  α `in` ftvar_in_pskl P ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hnh Hoff Hα; inversion H; subst; ls_kill.
Qed.

Definition looksub_rel_stmt (n : nat) : Prop :=
  forall S0 Θ α m P P' S1 Ξ C,
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
    size_pskl P + size_pskl P' <= n ->
    add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
    forall S1' Ξ' C',
      {{ S0 ↝ S1' ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ' ⨾ C' }}e ->
      exists ps,
        (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
        swaps_atoms ps S1 [=] S1' /\
        swaps_aenv ps Ξ = Ξ' /\
        swaps_cstrs ps C = C'.

Lemma e_looksub_rel_n : forall n, looksub_rel_stmt n.
Proof.
  induction n as [ | n IH ]; unfold looksub_rel_stmt in *.
  { intros S0 Θ α m P P' S1 Ξ C D1 Hsz; exfalso;
      destruct P; simpl in Hsz; lia. }
  intros S0 Θ α m P P' S1 Ξ C D1 Hsz Hcov S1' Ξ' C' D2.
  destruct (sumbool_of_bool (mem α (ftvar_in_pskl P))) as [Hmem | Hmem].
  2:{ apply mem_false_notin in Hmem.
      destruct (e_looksub_absent_pins D1 Hmem) as [-> [-> HS]].
      destruct (e_looksub_absent_pins D2 Hmem) as [-> [-> HS']].
      exists nil. rel4; simpl; try reflexivity.
      - intros ? ? [].
      - clear - HS HS'. fsetdec. }
  apply mem_true_in in Hmem. rename Hmem into HαP.
  inversion D1; subst.

  - (* LS-Var *)
    destruct (e_looksub_inv_var D2) as [-> [-> ->]].
    exists nil. rel4; simpl; try reflexivity. intros ? ? [].

  - (* LS-Absent — excluded *)
    exfalso.
    match goal with
    | Hn : ?a `notin` ftvar_in_pskl _ |- _ => clear - Hn HαP; fsetdec
    end.

  - (* LS-Vacuous *)
    match goal with
    | Hne : _ <> pskl_var_f α |- _ => rename Hne into Hnev
    end.
    destruct (e_looksub_inv_ghost D2 Hnev HαP) as [-> [-> ->]].
    exists nil. rel4; simpl; try reflexivity. intros ? ? [].

  - (* LS-Check — down to the EQ layer, which §3 has already settled *)
    match goal with
    | Hne : _ <> pskl_var_f α |- _ => rename Hne into Hnev
    end.
    match goal with
    | Hg1 : guarded_pskl ?A, Hg2 : guarded_pskl ?B |- _ =>
        rename Hg1 into HgA; rename Hg2 into HgB
    end.
    pose proof (e_looksub_inv_check D1 Hnev HgA HgB HαP) as Dp.
    pose proof (e_looksub_inv_check D2 Hnev HgA HgB HαP) as Dp'.
    exact (e_lookeq_rel Dp Dp' Hcov).

  - (* LS-ForallR — the COUNTERPART opens; the subject is untouched *)
    match type of D1 with
    | e_looksub _ _ _ _ ?a (pskl_all_syn ?b) _ _ _ =>
        rename a into As; rename b into Bt
    end.
    match goal with
    | Hgf : pskl_ghost_free (pskl_all_syn _) |- _ => rename Hgf into Hghf
    end.
    match goal with
    | Hne : _ <> pskl_var_f α |- _ => rename Hne into Hnev
    end.
    destruct (e_looksub_inv_forall_r D1 Hghf Hnev HαP) as (β1 & Hβ1 & Dp).
    destruct (e_looksub_inv_forall_r D2 Hghf Hnev HαP) as (β2 & Hβ2 & Dp').
    simpl in Hsz, Hcov.
    assert (Heqs : add β2 S0 [=] swap_atoms β1 β2 (add β1 S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β1 β2 S0 Hβ1 Hβ2).
      unfold swap_atom. destruct (β1 == β1); [ | congruence ]. reflexivity. }
    destruct (e_looksub_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite swap_pskl_open_var in Dpt.
    rewrite (@swap_pskl_fresh_id β1 β2 As) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_pskl_fresh_id β1 β2 Bt) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    rewrite (@swap_atom_other β1 β2 α) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    replace (swap_atom β1 β2 β1) with β2 in Dpt
      by (unfold swap_atom; destruct (β1 == β1); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Bt (pskl_var_f β2))
      as Hup.
    destruct (IH _ _ _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hup; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HC']]]].
    exists ((β1, β2) :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_cstrs]. exact HC'.

  - (* LS-Arrow — EQ first half, SUB second half *)
    match type of D1 with
    | e_looksub _ _ _ _ (pskl_arrow ?p1 ?p2) (pskl_arrow ?q1 ?q2) _ _ _ =>
        rename p1 into Pa; rename p2 into Pb;
        rename q1 into Pa'; rename q2 into Pb'
    end.
    destruct (e_looksub_inv_arrow D1 HαP)
      as (Sm & X1 & X2 & Cc1 & Cc2 & -> & -> & D1a & D1b).
    destruct (e_looksub_inv_arrow D2 HαP)
      as (Sm' & X1' & X2' & Cc1' & Cc2' & -> & -> & D2a & D2b).
    simpl in Hsz, Hcov, HαP.
    destruct (e_lookeq_rel D1a D2a ltac:(clear - Hcov; fsetdec))
      as [ps1 [Hav1 [HS1 [HX1 HC1]]]].
    assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (Hα1 : swaps_atom ps1 α = α)
      by (apply swaps_atom_notin; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (HPb : swaps_pskl ps1 Pb = Pb)
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (HPb' : swaps_pskl ps1 Pb' = Pb')
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (Heq2 : Sm' [=] swaps_atoms ps1 Sm) by (symmetry; exact HS1).
    destruct (e_looksub_swaps ps1 D1b Heq2) as [S2t [HS2t D1bt]].
    rewrite HΘ1, Hα1, HPb, HPb' in D1bt.
    pose proof (e_lookeq_supply_grows D2a) as Hgr1'.
    destruct (IH _ _ _ _ _ _ _ _ _ D1bt ltac:(lia)
                 ltac:(clear - Hcov Hgr1'; fsetdec) _ _ _ D2b)
      as [ps2 [Hav2 [HS2 [HX2 HC2]]]].
    pose proof (e_lookeq_generated_in_supply D2a) as Hdom1'.
    pose proof (e_lookeq_block_ftvar D2a) as Hftv1'.
    pose proof ((proj2 e_looksub_lookeq_cstr_ftvar) _ _ _ _ _ _ _ _ D2a)
      as Hcs1'.
    assert (HX1' : swaps_aenv ps2 X1' = X1')
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hdom1' Hftv1'; fsetdec).
    assert (HC1' : swaps_cstrs ps2 Cc1' = Cc1')
      by (apply swaps_cstrs_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcs1' Hcov Hgr1'; fsetdec).
    exists (ps1 ++ ps2). rel4.
    + intros a0 b0 Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exact (Hav1 a0 b0 Hin).
      * destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
        split; clear - Ha0 Hb0 Hgr1'; fsetdec.
    + rewrite swaps_atoms_app. rewrite <- HS2.
      apply swaps_atoms_cong. symmetry. exact HS2t.
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_cstrs_app, !swaps_cstrs_app_dist, HC1, HC2, HC1'.
      reflexivity.

  - (* LS-ForallL — the SUBJECT peels *)
    match type of D1 with
    | e_looksub _ _ _ _ (pskl_all_syn ?p) ?q _ _ _ =>
        rename p into Ps; rename q into Pt
    end.
    match goal with
    | Hnh : _ <> pskl_ghost |- _ => rename Hnh into Hnhl
    end.
    match goal with
    | Ho : forall_r_off _ _ |- _ => rename Ho into Hoff
    end.
    destruct (e_looksub_inv_forall_l D1 Hnhl Hoff HαP) as (β1 & Hβ1 & Dp).
    destruct (e_looksub_inv_forall_l D2 Hnhl Hoff HαP) as (β2 & Hβ2 & Dp').
    simpl in Hsz, Hcov, HαP.
    assert (Heqs : add β2 S0 [=] swap_atoms β1 β2 (add β1 S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β1 β2 S0 Hβ1 Hβ2).
      unfold swap_atom. destruct (β1 == β1); [ | congruence ]. reflexivity. }
    destruct (e_looksub_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite swap_pskl_open_var in Dpt.
    rewrite (@swap_pskl_fresh_id β1 β2 Ps) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_pskl_fresh_id β1 β2 Pt) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_atom_other β1 β2 α) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    replace (swap_atom β1 β2 β1) with β2 in Dpt
      by (unfold swap_atom; destruct (β1 == β1); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Ps (pskl_var_f β2))
      as Hup.
    destruct (IH _ _ _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hup; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HC']]]].
    exists ((β1, β2) :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_cstrs]. exact HC'.

  - (* LS-UnivGhostL — the subject's ⫯ is stripped *)
    match type of D1 with
    | e_looksub _ _ _ _ (pskl_univ_ghost ?p) _ _ _ _ => rename p into Ps
    end.
    match goal with
    | Hnh : _ <> pskl_ghost |- _ => rename Hnh into Hnhl
    end.
    match goal with
    | Ho : forall_r_off _ _ |- _ => rename Ho into Hoff
    end.
    assert (Hα' : α `in` ftvar_in_pskl Ps) by (simpl in HαP; exact HαP).
    pose proof (e_looksub_inv_univ_ghost_l D1 Hnhl Hoff Hα') as Dp.
    pose proof (e_looksub_inv_univ_ghost_l D2 Hnhl Hoff Hα') as Dp'.
    simpl in Hsz, Hcov.
    exact (IH _ _ _ _ _ _ _ _ _ Dp ltac:(lia)
              ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp').
Qed.

Corollary e_looksub_rel : forall S0 Θ α m P P' S1 Ξ C S1' Ξ' C',
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  {{ S0 ↝ S1' ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ' ⨾ C' }}e ->
  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_cstrs ps C = C'.
Proof.
  intros * D1 D2 Hcov.
  exact (e_looksub_rel_n D1 (le_n _) Hcov D2).
Qed.

(* ===================================================================== *)
(*  §5  ROOT INVERSIONS AND DETERMINISM FOR THE SOLVE LAYER, eq half      *)
(*                                                                        *)
(*  ⚙ The [a_]-level twin (prop_solve_det.v §4, [a_solve_eq_det]) is Qed   *)
(*  and HYPOTHESIS-FREE, and its case skeleton transfers row for row.     *)
(*  Two differences, both simplifications: the binder rows pair the two    *)
(*  openers with ONE transposition instead of rebinding both to a         *)
(*  globally fresh third atom (the supply already says each opener is     *)
(*  fresh for [S0]); and the overlap crosses that the [a_] version closes  *)
(*  with [det_nil_refl] close with the EMPTY CHAIN here, which is         *)
(*  strictly more informative — it pins the supply too.                   *)
(* ===================================================================== *)

(** ⭐ A VARIABLE SUBJECT ANSWERS ITSELF, spends nothing and generates
    nothing — whatever route the derivation took ([SE-Var],
    [SE-FlexR]-at-a-variable, [SE-VacuousR], [SE-GuardedGhost] all agree).
    This is what makes every var-row overlap trivial.  ⚙ The supply
    conjunct is new here; the [a_] twin cannot state it. *)
Lemma e_solve_eq_var_subject : forall S0 Θ α Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_var_f α) ∼ Q ⤳ Ξ ⨾ Y }}e ->
  S1 = S0 /\ Ξ = nil /\ Y = pskl_var_f α.
Proof.
  intros S0 Θ α Q S1 Ξ Y HD.
  remember (pskl_var_f α) as Ps eqn:HP.
  revert α HP.
  induction HD; intros α0 HP; try discriminate.
  - (* SE-Var *) inversion HP; subst. repeat split; reflexivity.
  - (* SE-FlexR — the guess at a variable IS the variable *)
    subst.
    match goal with
    | G : e_guess_mono _ (pskl_var_f _) _ _ _ |- _ =>
        destruct (e_guess_mono_inv_var G) as [-> [-> ->]]
    end.
    repeat split; reflexivity.
  - (* SE-VacuousR *) subst. repeat split; reflexivity.
  - (* SE-GuardedGhost *) exact (IHHD α0 HP).
Qed.

Local Ltac se_kill :=
  try solve
    [ assumption
    | exfalso;
      match goal with
      | Hg : nonghost_pskl (pskl_univ_ghost _) |- _ => inversion Hg
      | Hg : nonghost_pskl pskl_ghost |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
      | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
      end ].

Lemma e_solve_eq_inv_arrow : forall S0 Θ P1 P2 Q1 Q2 S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2)
     ⤳ Ξ ⨾ Y }}e ->
  exists Sm Ξ1 Ξ2 Y1 Y2,
    Ξ = Ξ2 ++ Ξ1 /\ Y = pskl_arrow Y1 Y2 /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ Y1 }}e /\
    {{ Sm ↝ S1 ⊨ (Ξ1 ++ Θ) ⊢ₑ P2 ∼ Q2 ⤳ Ξ2 ⨾ Y2 }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
  match goal with
  | Ha : e_solve_eq S0 _ P1 Q1 ?sm ?x1 ?y1,
    Hb : e_solve_eq ?sm _ P2 Q2 S1 ?x2 ?y2 |- _ =>
      exists sm, x1, x2, y1, y2
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_eq_inv_forall : forall S0 Θ P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_all_syn Q) ⤳ Ξ ⨾ Y }}e ->
  exists β Y0, β `notin` S0
    /\ Y = pskl_all_syn (close_pskl_wrt_pskl β Y0)
    /\ {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
          ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
          ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
  match goal with
  | Hfr : ?b `notin` S0, Hp : e_solve_eq _ _ _ _ _ _ ?y |- _ =>
      exists b, y
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_eq_inv_univ_ghost : forall S0 Θ P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ Y }}e ->
  exists Y0, Y = pskl_univ_ghost Y0
    /\ {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
  match goal with
  | Hp : e_solve_eq S0 _ P Q S1 Ξ ?y |- _ => exists y
  end.
  split; [ reflexivity | assumption ].
Qed.

Lemma e_solve_eq_inv_ghost_forall : forall S0 Θ P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ (pskl_all_syn Q) ⤳ Ξ ⨾ Y }}e ->
  exists β Y0, β `notin` S0
    /\ Y = pskl_all_syn (close_pskl_wrt_pskl β Y0)
    /\ {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (pskl_univ_ghost P)
          ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
  match goal with
  | Hfr : ?b `notin` S0, Hp : e_solve_eq _ _ _ _ _ _ ?y |- _ =>
      exists b, y
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_eq_inv_forall_ghost : forall S0 Θ P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ Y }}e ->
  exists β Y0, β `notin` S0
    /\ Y = pskl_all_syn (close_pskl_wrt_pskl β Y0)
    /\ {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
          ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
          ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
  match goal with
  | Hfr : ?b `notin` S0, Hp : e_solve_eq _ _ _ _ _ _ ?y |- _ =>
      exists b, y
  end.
  repeat split; assumption.
Qed.

(** the subject's [⫯] is stripped at a GUARDED counterpart — [SE-FlexR] is
    barred by its own [nonghost_pskl] premise, everything else by the shape
    of the counterpart. *)
Lemma e_solve_eq_inv_ghost_guarded : forall S0 Θ P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ Q ⤳ Ξ ⨾ Y }}e ->
  guarded_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * H Hg; inversion H; subst; se_kill.
Qed.

(** and the counterpart's [⫯] at a non-variable guarded subject.  ⚠️ A
    VARIABLE subject is genuinely a second route ([SE-Var] fires there too),
    which is why the two shape-specific forms are stated instead of one
    [guarded_pskl] form; the variable cell is closed by
    [e_solve_eq_var_subject] on both sides. *)
Lemma e_solve_eq_inv_guarded_ghost_unit : forall S0 Θ Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_unit ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ Y }}e ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_unit ∼ Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
Qed.

Lemma e_solve_eq_inv_guarded_ghost_arrow : forall S0 Θ P1 P2 Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ Y }}e ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
Qed.

Local Ltac rel_nil :=
  exists (@nil (atom * atom)); rel4;
  solve [ intros ? ? [] | simpl; reflexivity ].

Definition solve_eq_rel_stmt (n : nat) : Prop :=
  forall S0 Θ P Q S1 Ξ Y,
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ Y }}e ->
    size_pskl P + size_pskl Q <= n ->
    ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
    forall S1' Ξ' Y',
      {{ S0 ↝ S1' ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ' ⨾ Y' }}e ->
      exists ps,
        (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
        swaps_atoms ps S1 [=] S1' /\
        swaps_aenv ps Ξ = Ξ' /\
        swaps_pskl ps Y = Y'.

Lemma e_solve_eq_rel_n : forall n, solve_eq_rel_stmt n.
Proof.
  induction n as [ | n IH ]; unfold solve_eq_rel_stmt in *.
  { intros S0 Θ P Q S1 Ξ Y D1 Hsz; exfalso; destruct P; simpl in Hsz; lia. }
  intros S0 Θ P Q S1 Ξ Y D1 Hsz Hcov S1' Ξ' Y' D2.
  inversion D1; subst.

  - (* SE-Unit *)
    inversion D2; subst; se_kill; rel_nil.

  - (* SE-Var / SE-FlexL *)
    destruct (e_solve_eq_var_subject D2) as [-> [-> ->]]. rel_nil.

  - (* SE-FlexR — the layer's ONE generating row *)
    match goal with
    | G : e_guess_mono S0 _ S1 Ξ _ |- _ => rename G into G1
    end.
    inversion D2; subst; se_kill.
    + (* the subject is a variable: side 1's guess answers it verbatim *)
      destruct (e_guess_mono_inv_var G1) as [-> [-> ->]]. rel_nil.
    + (* flex_r × flex_r — [guess^TY]'s own determinism *)
      match goal with
      | G : e_guess_mono S0 _ S1' Ξ' _ |- _ => rename G into G2
      end.
      destruct (e_guess_mono_rel G1 G2 ltac:(clear - Hcov; fsetdec))
        as [ps [Hav [HS [HX HA]]]].
      exists ps. rel4; [ exact Hav | exact HS | exact HX | ].
      rewrite swaps_pskl_ptyp_to_pskl, HA. reflexivity.

  - (* SE-GhostL — a ◇ subject answers with the counterpart *)
    inversion D2; subst; se_kill; rel_nil.

  - (* SE-VacuousR — a ◇ counterpart answers with the subject *)
    inversion D2; subst; se_kill; rel_nil.

  - (* SE-Arrow — the THREADING row (supply AND context) *)
    match type of D1 with
    | e_solve_eq _ _ (pskl_arrow ?p1 ?p2) (pskl_arrow ?q1 ?q2) _ _ _ =>
        rename p1 into Pa; rename p2 into Pb;
        rename q1 into Qa; rename q2 into Qb
    end.
    destruct (e_solve_eq_inv_arrow D1)
      as (Sm & X1 & X2 & Y1 & Y2 & -> & -> & D1a & D1b).
    destruct (e_solve_eq_inv_arrow D2)
      as (Sm' & X1' & X2' & Y1' & Y2' & -> & -> & D2a & D2b).
    simpl in Hsz, Hcov.
    destruct (IH _ _ _ _ _ _ _ D1a ltac:(simpl; lia)
                 ltac:(clear - Hcov; fsetdec) _ _ _ D2a)
      as [ps1 [Hav1 [HS1 [HX1 HY1]]]].
    assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (HPb : swaps_pskl ps1 Pb = Pb)
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (HQb : swaps_pskl ps1 Qb = Qb)
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (Heq2 : Sm' [=] swaps_atoms ps1 Sm) by (symmetry; exact HS1).
    destruct (e_solve_eq_swaps ps1 D1b Heq2) as [S2t [HS2t D1bt]].
    rewrite swaps_aenv_app_dist, HX1, HΘ1, HPb, HQb in D1bt.
    pose proof (e_solve_eq_supply_grows D2a) as Hgr1'.
    pose proof (e_solve_eq_block_in_supply D2a) as Hdom1'.
    pose proof (e_solve_eq_block_ftvar D2a) as Hftv1'.
    pose proof (e_solve_eq_out_ftvar D2a ltac:(clear - Hcov; fsetdec))
      as Hout1'.
    destruct (IH _ _ _ _ _ _ _ D1bt ltac:(simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_app;
                       clear - Hcov Hgr1' Hdom1' Hftv1'; fsetdec)
                 _ _ _ D2b)
      as [ps2 [Hav2 [HS2 [HX2 HY2]]]].
    assert (HX1' : swaps_aenv ps2 X1' = X1')
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hdom1' Hftv1'; fsetdec).
    assert (HY1' : swaps_pskl ps2 Y1' = Y1')
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hout1'; fsetdec).
    exists (ps1 ++ ps2). rel4.
    + intros a0 b0 Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exact (Hav1 a0 b0 Hin).
      * destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
        split; clear - Ha0 Hb0 Hgr1'; fsetdec.
    + rewrite swaps_atoms_app. rewrite <- HS2.
      apply swaps_atoms_cong. symmetry. exact HS2t.
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_pskl_app, !swaps_pskl_arrow, HY1, HY2, HY1'.
      reflexivity.

  - (* SE-Forall — both sides open; ONE transposition pairs the openers *)
    match type of D1 with
    | e_solve_eq _ _ (pskl_all_syn ?p) (pskl_all_syn ?q) _ _ _ =>
        rename p into P0; rename q into Q0
    end.
    destruct (e_solve_eq_inv_forall D1) as (β1 & Y1 & Hβ1 & -> & Dp).
    destruct (e_solve_eq_inv_forall D2) as (β2 & Y2 & Hβ2 & -> & Dp').
    simpl in Hsz, Hcov.
    assert (Heqs : add β2 S0 [=] swap_atoms β1 β2 (add β1 S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β1 β2 S0 Hβ1 Hβ2).
      unfold swap_atom. destruct (β1 == β1); [ | congruence ]. reflexivity. }
    destruct (e_solve_eq_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite ! swap_pskl_open_var in Dpt.
    rewrite (@swap_pskl_fresh_id β1 β2 P0) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_pskl_fresh_id β1 β2 Q0) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    replace (swap_atom β1 β2 β1) with β2 in Dpt
      by (unfold swap_atom; destruct (β1 == β1); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f β2))
      as Hu1.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0 (pskl_var_f β2))
      as Hu2.
    destruct (IH _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hu1 Hu2; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ((β1, β2) :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_pskl swap_pskl]. rewrite swap_pskl_close.
      replace (swap_atom β1 β2 β1) with β2
        by (unfold swap_atom; destruct (β1 == β1); congruence).
      rewrite swaps_pskl_all_syn, swaps_pskl_close, HY'.
      f_equal. f_equal.
      apply swaps_atom_notin. intros a0 b0 Hin.
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; [ clear - Ha0 | clear - Hb0 ]; fsetdec.

  - (* SE-UnivGhost — both ⫯s vanish and reappear on the output *)
    match type of D1 with
    | e_solve_eq _ _ (pskl_univ_ghost ?p) (pskl_univ_ghost ?q) _ _ _ =>
        rename p into P0; rename q into Q0
    end.
    destruct (e_solve_eq_inv_univ_ghost D1) as (Y1 & -> & Dp).
    destruct (e_solve_eq_inv_univ_ghost D2) as (Y2 & -> & Dp').
    simpl in Hsz, Hcov.
    destruct (IH _ _ _ _ _ _ _ Dp ltac:(simpl; lia)
                 ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ps'. rel4; [ exact Hav' | exact HS' | exact HX' | ].
    rewrite swaps_pskl_univ_ghost, HY'. reflexivity.

  - (* SE-GhostForall — the COUNTERPART opens *)
    match type of D1 with
    | e_solve_eq _ _ (pskl_univ_ghost ?p) (pskl_all_syn ?q) _ _ _ =>
        rename p into P0; rename q into Q0
    end.
    destruct (e_solve_eq_inv_ghost_forall D1) as (β1 & Y1 & Hβ1 & -> & Dp).
    destruct (e_solve_eq_inv_ghost_forall D2) as (β2 & Y2 & Hβ2 & -> & Dp').
    simpl in Hsz, Hcov.
    assert (Heqs : add β2 S0 [=] swap_atoms β1 β2 (add β1 S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β1 β2 S0 Hβ1 Hβ2).
      unfold swap_atom. destruct (β1 == β1); [ | congruence ]. reflexivity. }
    destruct (e_solve_eq_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite swap_pskl_open_var in Dpt.
    rewrite (@swap_pskl_fresh_id β1 β2 (pskl_univ_ghost P0)) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    rewrite (@swap_pskl_fresh_id β1 β2 Q0) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    replace (swap_atom β1 β2 β1) with β2 in Dpt
      by (unfold swap_atom; destruct (β1 == β1); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0 (pskl_var_f β2))
      as Hu2.
    destruct (IH _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hu2; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ((β1, β2) :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_pskl swap_pskl]. rewrite swap_pskl_close.
      replace (swap_atom β1 β2 β1) with β2
        by (unfold swap_atom; destruct (β1 == β1); congruence).
      rewrite swaps_pskl_all_syn, swaps_pskl_close, HY'.
      f_equal. f_equal.
      apply swaps_atom_notin. intros a0 b0 Hin.
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; [ clear - Ha0 | clear - Hb0 ]; fsetdec.

  - (* SE-GhostGuarded — the subject's ⫯ is stripped, the yield passes *)
    match goal with
    | Hg : guarded_pskl _ |- _ => rename Hg into Hgd
    end.
    pose proof (e_solve_eq_inv_ghost_guarded D1 Hgd) as Dp.
    pose proof (e_solve_eq_inv_ghost_guarded D2 Hgd) as Dp'.
    simpl in Hsz, Hcov.
    exact (IH _ _ _ _ _ _ _ Dp ltac:(simpl; lia)
              ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp').

  - (* SE-ForallGhost — the SUBJECT opens *)
    match type of D1 with
    | e_solve_eq _ _ (pskl_all_syn ?p) (pskl_univ_ghost ?q) _ _ _ =>
        rename p into P0; rename q into Q0
    end.
    destruct (e_solve_eq_inv_forall_ghost D1) as (β1 & Y1 & Hβ1 & -> & Dp).
    destruct (e_solve_eq_inv_forall_ghost D2) as (β2 & Y2 & Hβ2 & -> & Dp').
    simpl in Hsz, Hcov.
    assert (Heqs : add β2 S0 [=] swap_atoms β1 β2 (add β1 S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β1 β2 S0 Hβ1 Hβ2).
      unfold swap_atom. destruct (β1 == β1); [ | congruence ]. reflexivity. }
    destruct (e_solve_eq_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite swap_pskl_open_var in Dpt.
    rewrite (@swap_pskl_fresh_id β1 β2 P0) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_pskl_fresh_id β1 β2 (pskl_univ_ghost Q0)) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    replace (swap_atom β1 β2 β1) with β2 in Dpt
      by (unfold swap_atom; destruct (β1 == β1); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f β2))
      as Hu1.
    destruct (IH _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hu1; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ((β1, β2) :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_pskl swap_pskl]. rewrite swap_pskl_close.
      replace (swap_atom β1 β2 β1) with β2
        by (unfold swap_atom; destruct (β1 == β1); congruence).
      rewrite swaps_pskl_all_syn, swaps_pskl_close, HY'.
      f_equal. f_equal.
      apply swaps_atom_notin. intros a0 b0 Hin.
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; [ clear - Ha0 | clear - Hb0 ]; fsetdec.

  - (* SE-GuardedGhost — ⚠️ a VARIABLE subject is a second route *)
    match goal with
    | Hg : guarded_pskl _ |- _ => rename Hg into Hgd
    end.
    inversion Hgd; subst.
    + (* unit subject *)
      pose proof (e_solve_eq_inv_guarded_ghost_unit D1) as Dp.
      pose proof (e_solve_eq_inv_guarded_ghost_unit D2) as Dp'.
      simpl in Hsz, Hcov.
      exact (IH _ _ _ _ _ _ _ Dp ltac:(simpl; lia)
                ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp').
    + (* VARIABLE subject — both sides answer the variable, whatever route *)
      destruct (e_solve_eq_var_subject D1) as [-> [-> ->]].
      destruct (e_solve_eq_var_subject D2) as [-> [-> ->]].
      rel_nil.
    + (* arrow subject *)
      pose proof (e_solve_eq_inv_guarded_ghost_arrow D1) as Dp.
      pose proof (e_solve_eq_inv_guarded_ghost_arrow D2) as Dp'.
      simpl in Hsz, Hcov.
      exact (IH _ _ _ _ _ _ _ Dp ltac:(simpl; lia)
                ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp').
Qed.

Corollary e_solve_eq_rel : forall S0 Θ P Q S1 Ξ Y S1' Ξ' Y',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ Y }}e ->
  {{ S0 ↝ S1' ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ' ⨾ Y' }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_pskl ps Y = Y'.
Proof.
  intros * D1 D2 Hcov.
  exact (e_solve_eq_rel_n D1 (le_n _) Hcov D2).
Qed.

(* ===================================================================== *)
(*  §6  [guess] — three lines off [e_guess_mono_rel]                      *)
(*                                                                        *)
(*  ⚙ At [NM = SK] the judgement is the IDENTITY and the empty chain does *)
(*  it; at [NM = TY] it is [guess^TY] followed by the [ptyp → pskl]       *)
(*  reading, which the chain commutes with.                              *)
(* ===================================================================== *)

Lemma e_guess_rel : forall S0 NM Q S1 Ξ Y S1' Ξ' Y',
  e_guess S0 NM Q S1 Ξ Y ->
  e_guess S0 NM Q S1' Ξ' Y' ->
  ftvar_in_pskl Q [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_pskl ps Y = Y'.
Proof.
  intros * D1 D2 Hcov.
  inversion D1; subst; inversion D2; subst.
  - (* SK — the identity *)
    exists (@nil (atom * atom)). rel4; simpl; try reflexivity.
    intros ? ? [].
  - (* TY — [guess^TY]'s own determinism, read through [ptyp_to_pskl] *)
    match goal with
    | G1 : e_guess_mono S0 Q S1 Ξ _, G2 : e_guess_mono S0 Q S1' Ξ' _ |- _ =>
        destruct (e_guess_mono_rel G1 G2 Hcov) as [ps [Hav [HS [HX HA]]]]
    end.
    exists ps. rel4; [ exact Hav | exact HS | exact HX | ].
    rewrite swaps_pskl_ptyp_to_pskl, HA. reflexivity.
Qed.

(* ===================================================================== *)
(*  §7  ROOT INVERSIONS AND DETERMINISM FOR THE SOLVE LAYER, sub half     *)
(*                                                                        *)
(*  ⭐ THIS IS WHAT GUARD 5 BOUGHT.  Before it the layer answered the same *)
(*  query with two different amounts of supply at two cells — [SS-Var] vs *)
(*  [SS-ForallR] at a variable subject, and [SS-Vacuous] vs [SS-ForallL]  *)
(*  at a [∀] subject against [◇] — and the statement below was FALSE      *)
(*  (§8c.18).  With the guard the dispatch is single-rule everywhere      *)
(*  except at a VARIABLE subject, where the surviving routes COINCIDE     *)
(*  ([e_solve_sub_var_subject]), exactly as the collection's α-free cells *)
(*  do.                                                                    *)
(* ===================================================================== *)

(** ⭐ A VARIABLE subject answers itself, spends nothing and generates
    nothing — by [SS-Var], by [SS-Vacuous] at a [◇] counterpart, or through
    [SS-Check]'s premise; [SS-ForallR] is BARRED (that is the guard). *)
Lemma e_solve_sub_var_subject : forall S0 Θ m α Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_var_f α) ≼[ m ] Q ⤳ Ξ ⨾ Y }}e ->
  S1 = S0 /\ Ξ = nil /\ Y = pskl_var_f α.
Proof.
  intros * HD; inversion HD; subst.
  - (* SS-Var *) repeat split; reflexivity.
  - (* SS-Vacuous *) repeat split; reflexivity.
  - (* SS-Check — the EQ layer answers a variable subject with itself *)
    match goal with
    | He : e_solve_eq _ _ _ _ _ _ _ |- _ => exact (e_solve_eq_var_subject He)
    end.
  - (* SS-ForallR — ⛔ BARRED at a variable subject by the guard *)
    exfalso.
    match goal with
    | Hoff : solve_l_off (pskl_var_f _) |- _ => exact (proj1 Hoff _ eq_refl)
    end.
Qed.

Local Ltac ss_kill :=
  try solve
    [ assumption
    | exfalso;
      match goal with
      | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
      end
    | exfalso;
      match goal with
      | Hoff : peel_l_off (pskl_all_syn _) |- _ => exact (proj1 Hoff _ eq_refl)
      | Hoff : peel_l_off (pskl_univ_ghost _) |- _ => exact (proj2 Hoff _ eq_refl)
      end
    | exfalso;
      match goal with
      | Hoff : solve_l_off (pskl_var_f _) |- _ => exact (proj1 Hoff _ eq_refl)
      | Hoff : solve_l_off (pskl_all_syn _) |- _ =>
          exact (proj1 (proj2 Hoff) _ eq_refl)
      | Hoff : solve_l_off (pskl_univ_ghost _) |- _ =>
          exact (proj2 (proj2 Hoff) _ eq_refl)
      end ].

(** counterpart [◇].  ⚙ Unconditional given the guard's own premise: the
    two surviving roots ([SS-Var] at a variable subject, [SS-Vacuous]) give
    the SAME answer. *)
Lemma e_solve_sub_inv_ghost : forall S0 Θ m P S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] pskl_ghost ⤳ Ξ ⨾ Y }}e ->
  peel_l_off P ->
  S1 = S0 /\ Ξ = nil /\ Y = P.
Proof.
  intros * HD Hoff; inversion HD; subst; ss_kill;
    repeat split; reflexivity.
Qed.

Lemma e_solve_sub_inv_forall_l : forall S0 Θ m P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_all_syn P) ≼[ m ] Q ⤳ Ξ ⨾ Y }}e ->
  exists β Y0, β `notin` S0
    /\ Y = pskl_all_syn (close_pskl_wrt_pskl β Y0)
    /\ {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
          ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ m ] Q ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * HD; inversion HD; subst; ss_kill.
  match goal with
  | Hfr : ?b `notin` S0, Hp : e_solve_sub _ _ _ _ _ _ _ ?y |- _ =>
      exists b, y
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_sub_inv_univ_ghost_l : forall S0 Θ m P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_univ_ghost P) ≼[ m ] Q ⤳ Ξ ⨾ Y }}e ->
  exists Y0, Y = pskl_univ_ghost Y0
    /\ {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * HD; inversion HD; subst; ss_kill.
  match goal with
  | Hp : e_solve_sub S0 _ _ P Q S1 Ξ ?y |- _ => exists y
  end.
  split; [ reflexivity | assumption ].
Qed.

(** ⭐ the ForallR cell.  [SS-Var] is barred by the guard, and everything
    else by the shape of the counterpart. *)
Lemma e_solve_sub_inv_forall_r : forall S0 Θ P B S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ Y }}e ->
  solve_l_off P ->
  exists β, β `notin` S0
    /\ {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
          (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * HD Hoff; inversion HD; subst; ss_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

Lemma e_solve_sub_inv_arrow : forall S0 Θ m P1 P2 Q1 Q2 S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_arrow P1 P2) ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
     ⤳ Ξ ⨾ Y }}e ->
  exists Sm Ξ1 Ξ2 Y1 Y2,
    Ξ = Ξ2 ++ Ξ1 /\ Y = pskl_arrow Y1 Y2 /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ Y1 }}e /\
    {{ Sm ↝ S1 ⊨ (Ξ1 ++ Θ) ⊢ₛ P2 ≼[ m ] Q2 ⤳ Ξ2 ⨾ Y2 }}e.
Proof.
  intros * HD; inversion HD; subst; ss_kill.
  match goal with
  | Ha : e_solve_eq S0 _ P1 Q1 ?sm ?x1 ?y1,
    Hb : e_solve_sub ?sm _ _ P2 Q2 S1 ?x2 ?y2 |- _ =>
      exists sm, x1, x2, y1, y2
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_sub_inv_ghost_l_fn : forall S0 Θ m Q1 Q2 S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ pskl_ghost ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
     ⤳ Ξ ⨾ Y }}e ->
  exists Sm Ξ1 Ξ2 Y1 Y2,
    Ξ = Ξ2 ++ Ξ1 /\ Y = pskl_univ_ghost (pskl_arrow Y1 Y2) /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ₑ pskl_ghost ∼ Q1 ⤳ Ξ1 ⨾ Y1 }}e /\
    {{ Sm ↝ S1 ⊨ (Ξ1 ++ Θ) ⊢ₛ pskl_ghost ≼[ m ] Q2 ⤳ Ξ2 ⨾ Y2 }}e.
Proof.
  intros * HD; inversion HD; subst; ss_kill.
  match goal with
  | Ha : e_solve_eq S0 _ pskl_ghost Q1 ?sm ?x1 ?y1,
    Hb : e_solve_sub ?sm _ _ pskl_ghost Q2 S1 ?x2 ?y2 |- _ =>
      exists sm, x1, x2, y1, y2
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_sub_inv_ghost_l : forall S0 Θ B S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ pskl_ghost ≼[ mode_tc ] B ⤳ Ξ ⨾ Y }}e ->
  guarded_pskl B ->
  S1 = S0 /\ Ξ = nil /\ Y = pskl_univ_ghost B.
Proof.
  intros * HD Hg; inversion HD; subst; ss_kill;
    repeat split; reflexivity.
Qed.

(** the CHECK cell, in the two shapes a NON-variable guarded subject can
    take.  ⚠️ A variable subject is a second route ([SS-Var]); that cell is
    closed by [e_solve_sub_var_subject] on both sides. *)
Lemma e_solve_sub_inv_check_unit : forall S0 Θ Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ pskl_unit ≼[ mode_tc ] Q ⤳ Ξ ⨾ Y }}e ->
  guarded_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_unit ∼ Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * HD Hg; inversion HD; subst; ss_kill.
Qed.

Lemma e_solve_sub_inv_check_arrow : forall S0 Θ P1 P2 Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_arrow P1 P2) ≼[ mode_tc ] Q ⤳ Ξ ⨾ Y }}e ->
  guarded_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * HD Hg; inversion HD; subst; ss_kill.
Qed.

Definition solve_sub_rel_stmt (n : nat) : Prop :=
  forall S0 Θ m P Q S1 Ξ Y,
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ Y }}e ->
    size_pskl P + size_pskl Q <= n ->
    ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
    forall S1' Ξ' Y',
      {{ S0 ↝ S1' ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ' ⨾ Y' }}e ->
      exists ps,
        (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
        swaps_atoms ps S1 [=] S1' /\
        swaps_aenv ps Ξ = Ξ' /\
        swaps_pskl ps Y = Y'.

Lemma e_solve_sub_rel_n : forall n, solve_sub_rel_stmt n.
Proof.
  induction n as [ | n IH ]; unfold solve_sub_rel_stmt in *.
  { intros S0 Θ m P Q S1 Ξ Y D1 Hsz; exfalso;
      destruct P; simpl in Hsz; lia. }
  intros S0 Θ m P Q S1 Ξ Y D1 Hsz Hcov S1' Ξ' Y' D2.
  inversion D1; subst.

  - (* SS-Var *)
    destruct (e_solve_sub_var_subject D2) as [-> [-> ->]]. rel_nil.

  - (* SS-ForallL — the SUBJECT peels and the output re-CLOSES *)
    match type of D1 with
    | e_solve_sub _ _ _ (pskl_all_syn ?p) _ _ _ _ => rename p into P0
    end.
    destruct (e_solve_sub_inv_forall_l D1) as (β1 & Y1 & Hβ1 & -> & Dp).
    destruct (e_solve_sub_inv_forall_l D2) as (β2 & Y2 & Hβ2 & -> & Dp').
    simpl in Hsz, Hcov.
    assert (Heqs : add β2 S0 [=] swap_atoms β1 β2 (add β1 S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β1 β2 S0 Hβ1 Hβ2).
      unfold swap_atom. destruct (β1 == β1); [ | congruence ]. reflexivity. }
    destruct (e_solve_sub_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite swap_pskl_open_var in Dpt.
    rewrite (@swap_pskl_fresh_id β1 β2 P0) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_pskl_fresh_id β1 β2 Q) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    replace (swap_atom β1 β2 β1) with β2 in Dpt
      by (unfold swap_atom; destruct (β1 == β1); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f β2))
      as Hu1.
    destruct (IH _ _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hu1; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ((β1, β2) :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_pskl swap_pskl]. rewrite swap_pskl_close.
      replace (swap_atom β1 β2 β1) with β2
        by (unfold swap_atom; destruct (β1 == β1); congruence).
      rewrite swaps_pskl_all_syn, swaps_pskl_close, HY'.
      f_equal. f_equal.
      apply swaps_atom_notin. intros a0 b0 Hin.
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; [ clear - Ha0 | clear - Hb0 ]; fsetdec.

  - (* SS-UnivGhostL — the subject's ⫯ is stripped and re-wrapped *)
    match type of D1 with
    | e_solve_sub _ _ _ (pskl_univ_ghost ?p) _ _ _ _ => rename p into P0
    end.
    destruct (e_solve_sub_inv_univ_ghost_l D1) as (Y1 & -> & Dp).
    destruct (e_solve_sub_inv_univ_ghost_l D2) as (Y2 & -> & Dp').
    simpl in Hsz, Hcov.
    destruct (IH _ _ _ _ _ _ _ _ Dp ltac:(simpl; lia)
                 ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ps'. rel4; [ exact Hav' | exact HS' | exact HX' | ].
    rewrite swaps_pskl_univ_ghost, HY'. reflexivity.

  - (* SS-Vacuous — a ◇ counterpart answers with the subject *)
    match goal with
    | Hoff : peel_l_off _ |- _ => rename Hoff into Hpo
    end.
    destruct (e_solve_sub_inv_ghost D2 Hpo) as [-> [-> ->]]. rel_nil.

  - (* SS-Check — down to the EQ layer, which §5 has already settled *)
    match goal with
    | Hg1 : guarded_pskl ?A, Hg2 : guarded_pskl ?B |- _ =>
        rename Hg1 into HgP; rename Hg2 into HgQ
    end.
    inversion HgP; subst.
    + (* unit subject *)
      pose proof (e_solve_sub_inv_check_unit D1 HgQ) as Dp.
      pose proof (e_solve_sub_inv_check_unit D2 HgQ) as Dp'.
      exact (e_solve_eq_rel Dp Dp' Hcov).
    + (* VARIABLE subject — both sides answer the variable *)
      destruct (e_solve_sub_var_subject D1) as [-> [-> ->]].
      destruct (e_solve_sub_var_subject D2) as [-> [-> ->]].
      rel_nil.
    + (* arrow subject *)
      pose proof (e_solve_sub_inv_check_arrow D1 HgQ) as Dp.
      pose proof (e_solve_sub_inv_check_arrow D2 HgQ) as Dp'.
      exact (e_solve_eq_rel Dp Dp' Hcov).

  - (* SS-ForallR — the COUNTERPART peels; ⚠️ NO close, the opener LEAKS *)
    match type of D1 with
    | e_solve_sub _ _ _ _ (pskl_all_syn ?b) _ _ _ => rename b into B0
    end.
    match goal with
    | Hoff : solve_l_off _ |- _ => rename Hoff into Hso
    end.
    destruct (e_solve_sub_inv_forall_r D1 Hso) as (β1 & Hβ1 & Dp).
    destruct (e_solve_sub_inv_forall_r D2 Hso) as (β2 & Hβ2 & Dp').
    simpl in Hsz, Hcov.
    assert (Heqs : add β2 S0 [=] swap_atoms β1 β2 (add β1 S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β1 β2 S0 Hβ1 Hβ2).
      unfold swap_atom. destruct (β1 == β1); [ | congruence ]. reflexivity. }
    destruct (e_solve_sub_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite swap_pskl_open_var in Dpt.
    rewrite (@swap_pskl_fresh_id β1 β2 P) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    rewrite (@swap_pskl_fresh_id β1 β2 B0) in Dpt
      by (clear - Hcov Hβ1 Hβ2; fsetdec).
    replace (swap_atom β1 β2 β1) with β2 in Dpt
      by (unfold swap_atom; destruct (β1 == β1); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B0 (pskl_var_f β2))
      as Hu1.
    destruct (IH _ _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hu1; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ((β1, β2) :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_pskl]. exact HY'.

  - (* SS-Arrow — the THREADING row: an EQ half then a SUB half *)
    match type of D1 with
    | e_solve_sub _ _ _ (pskl_arrow ?p1 ?p2) (pskl_arrow ?q1 ?q2) _ _ _ =>
        rename p1 into Pa; rename p2 into Pb;
        rename q1 into Qa; rename q2 into Qb
    end.
    destruct (e_solve_sub_inv_arrow D1)
      as (Sm & X1 & X2 & Y1 & Y2 & -> & -> & D1a & D1b).
    destruct (e_solve_sub_inv_arrow D2)
      as (Sm' & X1' & X2' & Y1' & Y2' & -> & -> & D2a & D2b).
    simpl in Hsz, Hcov.
    destruct (e_solve_eq_rel D1a D2a ltac:(clear - Hcov; fsetdec))
      as [ps1 [Hav1 [HS1 [HX1 HY1]]]].
    assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (HPb : swaps_pskl ps1 Pb = Pb)
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (HQb : swaps_pskl ps1 Qb = Qb)
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (Heq2 : Sm' [=] swaps_atoms ps1 Sm) by (symmetry; exact HS1).
    destruct (e_solve_sub_swaps ps1 D1b Heq2) as [S2t [HS2t D1bt]].
    rewrite swaps_aenv_app_dist, HX1, HΘ1, HPb, HQb in D1bt.
    pose proof (e_solve_eq_supply_grows D2a) as Hgr1'.
    pose proof (e_solve_eq_block_in_supply D2a) as Hdom1'.
    pose proof (e_solve_eq_block_ftvar D2a) as Hftv1'.
    pose proof (e_solve_eq_out_ftvar D2a ltac:(clear - Hcov; fsetdec))
      as Hout1'.
    destruct (IH _ _ _ _ _ _ _ _ D1bt ltac:(simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_app;
                       clear - Hcov Hgr1' Hdom1' Hftv1'; fsetdec)
                 _ _ _ D2b)
      as [ps2 [Hav2 [HS2 [HX2 HY2]]]].
    assert (HX1' : swaps_aenv ps2 X1' = X1')
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hdom1' Hftv1'; fsetdec).
    assert (HY1' : swaps_pskl ps2 Y1' = Y1')
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hout1'; fsetdec).
    exists (ps1 ++ ps2). rel4.
    + intros a0 b0 Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exact (Hav1 a0 b0 Hin).
      * destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
        split; clear - Ha0 Hb0 Hgr1'; fsetdec.
    + rewrite swaps_atoms_app. rewrite <- HS2.
      apply swaps_atoms_cong. symmetry. exact HS2t.
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_pskl_app, !swaps_pskl_arrow, HY1, HY2, HY1'.
      reflexivity.

  - (* SS-GhostLF — the same threading at a ◇ subject, output under a ⫯ *)
    match type of D1 with
    | e_solve_sub _ _ _ _ (pskl_arrow ?q1 ?q2) _ _ _ =>
        rename q1 into Qa; rename q2 into Qb
    end.
    destruct (e_solve_sub_inv_ghost_l_fn D1)
      as (Sm & X1 & X2 & Y1 & Y2 & -> & -> & D1a & D1b).
    destruct (e_solve_sub_inv_ghost_l_fn D2)
      as (Sm' & X1' & X2' & Y1' & Y2' & -> & -> & D2a & D2b).
    simpl in Hsz, Hcov.
    destruct (e_solve_eq_rel D1a D2a ltac:(clear - Hcov; simpl; fsetdec))
      as [ps1 [Hav1 [HS1 [HX1 HY1]]]].
    assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (HQb : swaps_pskl ps1 Qb = Qb)
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (Heq2 : Sm' [=] swaps_atoms ps1 Sm) by (symmetry; exact HS1).
    destruct (e_solve_sub_swaps ps1 D1b Heq2) as [S2t [HS2t D1bt]].
    rewrite swaps_aenv_app_dist, HX1, HΘ1, HQb in D1bt.
    rewrite swaps_pskl_ghost in D1bt.
    pose proof (e_solve_eq_supply_grows D2a) as Hgr1'.
    pose proof (e_solve_eq_block_in_supply D2a) as Hdom1'.
    pose proof (e_solve_eq_block_ftvar D2a) as Hftv1'.
    pose proof (e_solve_eq_out_ftvar D2a ltac:(clear - Hcov; simpl; fsetdec))
      as Hout1'.
    destruct (IH _ _ _ _ _ _ _ _ D1bt ltac:(simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_app;
                       clear - Hcov Hgr1' Hdom1' Hftv1'; simpl in *; fsetdec)
                 _ _ _ D2b)
      as [ps2 [Hav2 [HS2 [HX2 HY2]]]].
    assert (HX1' : swaps_aenv ps2 X1' = X1')
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hdom1' Hftv1'; fsetdec).
    assert (HY1' : swaps_pskl ps2 Y1' = Y1')
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hout1'; simpl in *; fsetdec).
    exists (ps1 ++ ps2). rel4.
    + intros a0 b0 Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exact (Hav1 a0 b0 Hin).
      * destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
        split; clear - Ha0 Hb0 Hgr1'; fsetdec.
    + rewrite swaps_atoms_app. rewrite <- HS2.
      apply swaps_atoms_cong. symmetry. exact HS2t.
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_pskl_app, !swaps_pskl_univ_ghost, !swaps_pskl_arrow,
        HY1, HY2, HY1'.
      reflexivity.

  - (* SS-GhostL — a ◇ subject at a guarded ghost-free counterpart *)
    match goal with
    | Hg : guarded_pskl _ |- _ => rename Hg into HgB
    end.
    destruct (e_solve_sub_inv_ghost_l D2 HgB) as [-> [-> ->]]. rel_nil.
Qed.

Corollary e_solve_sub_rel : forall S0 Θ m P Q S1 Ξ Y S1' Ξ' Y',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ Y }}e ->
  {{ S0 ↝ S1' ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ' ⨾ Y' }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_pskl ps Y = Y'.
Proof.
  intros * D1 D2 Hcov.
  exact (e_solve_sub_rel_n D1 (le_n _) Hcov D2).
Qed.

(* ===================================================================== *)
(*  §8  THE CONSTRAINT FOLD                                               *)
(*                                                                        *)
(*  ⚙ Structural induction on the CONSTRAINT LIST, not on a size: the     *)
(*  list is what the fold dispatches on, and it is what shrinks.  The     *)
(*  [eq] row threads BOTH the supply and the context, so its tail sits at *)
(*  a different everything — which is why the IH must be list-indexed and *)
(*  not derivation-indexed.                                              *)
(* ===================================================================== *)

Lemma e_solve_cstr_inv_nil : forall S0 Θ P S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊩ nil ⨾ P ⤳ Ξ ⨾ Y }}e ->
  S1 = S0 /\ Ξ = nil /\ Y = P.
Proof.
  intros * H; inversion H; subst; repeat split; reflexivity.
Qed.

Lemma e_solve_cstr_inv_sub : forall S0 Θ m Q C P S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊩ (a_cstr_sub m Q :: C) ⨾ P ⤳ Ξ ⨾ Y }}e ->
  C = nil /\ {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * H; inversion H; subst. split; [ reflexivity | assumption ].
Qed.

Lemma e_solve_cstr_inv_eq : forall S0 Θ Q C P S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ Ξ ⨾ Y }}e ->
  exists Sm Ξ1 Ξ2 Y0,
    Ξ = Ξ2 ++ Ξ1 /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ Y0 }}e /\
    {{ Sm ↝ S1 ⊨ (Ξ1 ++ Θ) ⊩ C ⨾ Y0 ⤳ Ξ2 ⨾ Y }}e.
Proof.
  intros * H; inversion H; subst.
  match goal with
  | Ha : e_solve_eq S0 _ P Q ?sm ?x1 ?y0,
    Hb : e_solve_cstr ?sm _ C ?y0 S1 ?x2 _ |- _ =>
      exists sm, x1, x2, y0
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_cstr_rel : forall C S0 Θ P S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Y }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_a_cstrs C [<=] S0 ->
  forall S1' Ξ' Y',
    {{ S0 ↝ S1' ⊨ Θ ⊩ C ⨾ P ⤳ Ξ' ⨾ Y' }}e ->
    exists ps,
      (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
      swaps_atoms ps S1 [=] S1' /\
      swaps_aenv ps Ξ = Ξ' /\
      swaps_pskl ps Y = Y'.
Proof.
  induction C as [ | c C IHC ];
    intros S0 Θ P S1 Ξ Y D1 Hcov S1' Ξ' Y' D2.
  - (* the empty fold *)
    destruct (e_solve_cstr_inv_nil D1) as [-> [-> ->]].
    destruct (e_solve_cstr_inv_nil D2) as [-> [-> ->]]. rel_nil.
  - destruct c as [ m Q | Q ].
    + (* a SUB head — necessarily the LAST constraint *)
      destruct (e_solve_cstr_inv_sub D1) as [-> Dp].
      destruct (e_solve_cstr_inv_sub D2) as [_ Dp'].
      apply (e_solve_sub_rel Dp Dp').
      simpl in Hcov. clear - Hcov. fsetdec.
    + (* an EQ head — the THREADING row, in the supply AND the context *)
      destruct (e_solve_cstr_inv_eq D1) as (Sm & X1 & X2 & Y0 & -> & D1a & D1b).
      destruct (e_solve_cstr_inv_eq D2)
        as (Sm' & X1' & X2' & Y0' & -> & D2a & D2b).
      simpl in Hcov.
      destruct (e_solve_eq_rel D1a D2a ltac:(clear - Hcov; fsetdec))
        as [ps1 [Hav1 [HS1 [HX1 HY1]]]].
      assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
        by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
            clear - Ha0 Hb0 Hcov; fsetdec).
      assert (HC1 : swaps_cstrs ps1 C = C)
        by (apply swaps_cstrs_fresh_id; intros a0 b0 Hin;
            destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
            clear - Ha0 Hb0 Hcov; fsetdec).
      assert (Heq2 : Sm' [=] swaps_atoms ps1 Sm) by (symmetry; exact HS1).
      destruct (e_solve_cstr_swaps ps1 D1b Heq2) as [S2t [HS2t D1bt]].
      rewrite swaps_aenv_app_dist, HX1, HΘ1, HC1, HY1 in D1bt.
      pose proof (e_solve_eq_supply_grows D2a) as Hgr1'.
      pose proof (e_solve_eq_block_in_supply D2a) as Hdom1'.
      pose proof (e_solve_eq_block_ftvar D2a) as Hftv1'.
      pose proof (e_solve_eq_out_ftvar D2a ltac:(clear - Hcov; fsetdec))
        as Hout1'.
      destruct (IHC _ _ _ _ _ _ D1bt
                   ltac:(rewrite ftvar_in_aenv_app;
                         clear - Hcov Hgr1' Hdom1' Hftv1' Hout1'; fsetdec)
                   _ _ _ D2b)
        as [ps2 [Hav2 [HS2 [HX2 HY2]]]].
      assert (HX1' : swaps_aenv ps2 X1' = X1')
        by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
            clear - Ha0 Hb0 Hdom1' Hftv1'; fsetdec).
      exists (ps1 ++ ps2). rel4.
      * intros a0 b0 Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        { exact (Hav1 a0 b0 Hin). }
        { destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
          split; clear - Ha0 Hb0 Hgr1'; fsetdec. }
      * rewrite swaps_atoms_app. rewrite <- HS2.
        apply swaps_atoms_cong. symmetry. exact HS2t.
      * rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
        reflexivity.
      * rewrite swaps_pskl_app, HY2. reflexivity.
Qed.

(* ===================================================================== *)
(*  §9  ⭐⭐⭐ EXTRACTION IS DETERMINISTIC UP TO A FRESH RENAMING           *)
(*                                                                        *)
(*  The composition: collect, fold, guess — each stage moved onto the     *)
(*  previous chain's rails by its [_swaps] iteration (§1), and the three  *)
(*  chains concatenated.  ⚙ The only real work is the FIXITY bookkeeping: *)
(*  a later stage's chain must leave the earlier stages' outputs alone,   *)
(*  which it does because every pair it contains avoids the supply those  *)
(*  outputs are drawn from.                                              *)
(* ===================================================================== *)

Lemma e_extract_inv : forall S0 Θ0 NM α m P P' S3 Ξt Y,
  {{ S0 ↝ S3 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξt ↪ Y }}e ->
  exists S1 S2 Ξ Ξs Ξg C Q,
    Ξt = Ξ ++ Ξs ++ Ξg /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e /\
    {{ S1 ↝ S2 ⊨ (Ξ ++ Θ0) ⊩ C ⨾ pskl_ghost ⤳ Ξs ⨾ Q }}e /\
    e_guess S2 NM Q S3 Ξg Y.
Proof.
  intros * H; inversion H; subst.
  match goal with
  | Hl : e_looksub S0 _ _ _ _ _ ?s1 ?x ?c,
    Hf : e_solve_cstr ?s1 _ _ _ ?s2 ?xs ?q,
    Hg : e_guess ?s2 _ _ S3 ?xg _ |- _ =>
      exists s1, s2, x, xs, xg, c, q
  end.
  repeat split; assumption.
Qed.

Lemma e_extract_rel : forall S0 Θ0 NM α m P P' S3 Ξt Y S3' Ξt' Y',
  {{ S0 ↝ S3 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξt ↪ Y }}e ->
  {{ S0 ↝ S3' ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξt' ↪ Y' }}e ->
  add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S3 [=] S3' /\
    swaps_aenv ps Ξt = Ξt' /\
    swaps_pskl ps Y = Y'.
Proof.
  intros * D1 D2 Hcov.
  destruct (e_extract_inv D1)
    as (S1a & S2a & X & Xs & Xg & C & Q & -> & L1 & F1 & G1).
  destruct (e_extract_inv D2)
    as (S1b & S2b & X' & Xs' & Xg' & C' & Q' & -> & L2 & F2 & G2).
  (* ---- STAGE 1: the collection ---- *)
  destruct (e_looksub_rel L1 L2 Hcov) as [ps1 [Hav1 [HS1 [HX1 HC1]]]].
  (* what side 2's collection puts in scope for the fold *)
  pose proof (e_looksub_supply_grows L2) as HgrL.
  pose proof (e_looksub_generated_in_supply L2) as HdomL.
  pose proof (e_looksub_block_ftvar L2) as HftL.
  pose proof (e_looksub_cstr_ftvar L2 ltac:(clear - Hcov; fsetdec)) as HcsL.
  (* ---- STAGE 2: move side 1's fold onto side 2's rails ---- *)
  assert (HΘ0 : swaps_aenv ps1 Θ0 = Θ0)
    by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
        destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
        clear - Ha0 Hb0 Hcov; fsetdec).
  assert (Heq2 : S1b [=] swaps_atoms ps1 S1a) by (symmetry; exact HS1).
  destruct (e_solve_cstr_swaps ps1 F1 Heq2) as [S2t [HS2t F1t]].
  rewrite swaps_aenv_app_dist, HX1, HΘ0, HC1, swaps_pskl_ghost in F1t.
  destruct (e_solve_cstr_rel F1t
              ltac:(rewrite ftvar_in_aenv_app;
                    clear - Hcov HgrL HdomL HftL HcsL; simpl; fsetdec)
              F2)
    as [ps2 [Hav2 [HS2 [HX2 HY2]]]].
  (* what side 2's fold puts in scope for the guess *)
  pose proof (e_solve_cstr_supply_grows F2) as HgrF.
  pose proof (e_solve_cstr_block F2) as [HdomF [_ [_ HftF]]].
  pose proof (e_solve_cstr_out_ftvar F2) as HoutF.
  (* ---- STAGE 3: move side 1's guess along BOTH chains ---- *)
  destruct (e_guess_swaps ps1 G1 HS2t) as [S3t1 [HS3t1 G1t]].
  assert (Heq3 : S2b [=] swaps_atoms ps2 S2t) by (symmetry; exact HS2).
  destruct (e_guess_swaps ps2 G1t Heq3) as [S3t2 [HS3t2 G1tt]].
  rewrite HY2 in G1tt.
  destruct (e_guess_rel G1tt G2
              ltac:(clear - HoutF HcsL HgrF HgrL Hcov; simpl in *; fsetdec))
    as [ps3 [Hav3 [HS3 [HXg HYg]]]].
  (* ---- the three chains, concatenated ---- *)
  assert (HXfix2 : swaps_aenv ps2 X' = X')
    by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
        destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
        clear - Ha0 Hb0 HdomL HftL; fsetdec).
  assert (HXfix3 : swaps_aenv ps3 X' = X')
    by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
        destruct (Hav3 a0 b0 Hin) as [Ha0 Hb0]; split;
        clear - Ha0 Hb0 HdomL HftL HgrF; fsetdec).
  assert (HXsfix3 : swaps_aenv ps3 Xs' = Xs')
    by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
        destruct (Hav3 a0 b0 Hin) as [Ha0 Hb0]; split;
        clear - Ha0 Hb0 HdomF HftF; fsetdec).
  exists (ps1 ++ ps2 ++ ps3). rel4.
  - intros a0 b0 Hin. rewrite ? in_app_iff in Hin.
    destruct Hin as [Hin | [Hin | Hin]].
    + exact (Hav1 a0 b0 Hin).
    + destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0 HgrL; fsetdec.
    + destruct (Hav3 a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0 HgrL HgrF; fsetdec.
  - rewrite ! swaps_atoms_app. rewrite <- HS3.
    apply swaps_atoms_cong. rewrite HS3t2.
    apply swaps_atoms_cong. symmetry. exact HS3t1.
  - rewrite ! swaps_aenv_app, ! swaps_aenv_app_dist,
      HX1, HX2, HXg, HXfix2, HXfix3, HXsfix3.
    reflexivity.
  - rewrite ! swaps_pskl_app, HYg. reflexivity.
Qed.

(** ⭐⭐⭐ THE HEADLINE, in the shape §8c.16 §D pinned it — and the shape
    [cex/probe_extract_supply_drift.v], [cex/probe_extract_flexr_ug2_drift.v]
    and [cex/probe_solve_sub_forall_r_drift.v] each refuted in turn, before
    the absence-first, FlexR-priority and solve-dispatch guards. *)
Theorem e_extract_det : forall S0 Θ0 NM α m P P' S1 Ξ Q S1' Ξ' Q',
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e ->
  {{ S0 ↝ S1' ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ' ↪ Q' }}e ->
  add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  exists ps,
    (forall x y, In (x, y) ps -> x `notin` S0 /\ y `notin` S0)
    /\ swaps_atoms ps S1 [=] S1'
    /\ swaps_aenv ps Ξ = Ξ'
    /\ swaps_pskl ps Q = Q'.
Proof. intros. eapply e_extract_rel; eassumption. Qed.
