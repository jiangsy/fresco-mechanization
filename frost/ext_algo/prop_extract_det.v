(** ext_algo — §8c.16 §D, campaign level 6, STEP 2:
    ⭐ EXTRACTION IS DETERMINISTIC UP TO A FRESH RENAMING.

    §1  equivariance along a CHAIN, for the collection, the solve layer,
        [guess] and [extract] — the [_swaps] iterations §8c.16 §D found
        missing (the SINGLE-swap versions are prop_look.v §6,
        prop_solve.v §7, prop_guess.v §10 and prop_extract.v §3)

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

    ⛔ NONE OF THIS IS REACHABLE BEFORE THE FOUR DISPATCH GUARDS.  Until
    guard 4 (the FlexR-PRIORITY split, §8c.16) the statement above was
    machine-checked FALSE. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_coercions.
Require Import src.frost.prop_tag.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_dec.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.prop_guess.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.prop_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.prop_solve.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.prop_extract.
Require Import src.frost.ext_algo.prop_solve_det.

Set Implicit Arguments.

Local Open Scope frost_e_scope.

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
      | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
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
Lemma e_lookeq_inv_hole : forall S0 Θ α P S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] pskl_hole ⤳ Ξ ⨾ C }}e ->
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
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole Q) ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  guarded_pskl P' ->
  flex_r_off Θ P' ->
  α `in` ftvar_in_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ Q ∼[ α ] P' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hg Hoff Hα; inversion H; subst; le_kill.
Qed.

(** subject [⫯Q] against [⫯Q'] — [LE-UnivGhost]. *)
Lemma e_lookeq_inv_ug : forall S0 Θ α Q Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole Q) ∼[ α ] (pskl_tophole Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ Q ∼[ α ] Q' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
Qed.

(** subject [⫯Q] against [∀Q'] — [LE-UnivGhost1], and it OPENS. *)
Lemma e_lookeq_inv_ug1 : forall S0 Θ α Q Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole Q) ∼[ α ] (pskl_all_syn Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl Q ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ (pskl_tophole Q)
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
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn Q) ∼[ α ] (pskl_tophole Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl (pskl_all_syn Q) ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl Q (pskl_var_f β))
       ∼[ α ] (pskl_tophole Q') ⤳ Ξ ⨾ C }}e.
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
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] (pskl_tophole Q') ⤳ Ξ ⨾ C }}e ->
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
Lemma e_lookeq_inv_ug2_unit : forall S0 Θ α Q S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole Q) ∼[ α ] pskl_unit ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ Q ∼[ α ] pskl_unit ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
Qed.

Lemma e_lookeq_inv_ug2_arrow : forall S0 Θ α Q P1' P2' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole Q) ∼[ α ] (pskl_arrow P1' P2')
     ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ Q ∼[ α ] (pskl_arrow P1' P2') ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
Qed.

Lemma e_lookeq_inv_ug2_var : forall S0 Θ α Q β S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole Q) ∼[ α ] (pskl_var_f β) ⤳ Ξ ⨾ C }}e ->
  ~ a_flex_tvar Θ β ->
  α `in` ftvar_in_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ Q ∼[ α ] (pskl_var_f β) ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hrig Hα; inversion H; subst;
    try solve [ assumption
              | exfalso;
                match goal with
                | Hn : ?a `notin` ftvar_in_pskl _,
                  Hi : ?a `in` ftvar_in_pskl _ |- _ =>
                    simpl in Hn, Hi; clear - Hn Hi; fsetdec
                end
              | exfalso;
                match goal with
                | Hf : a_flex_tvar _ _ |- _ => exact (Hrig Hf)
                end ].
Qed.

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
    destruct (e_lookeq_inv_hole D2 Hnev HαP) as [-> [-> ->]].
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
    | e_lookeq _ _ _ (pskl_all_syn ?q) (pskl_tophole ?q') _ _ _ =>
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
    rewrite (@swap_pskl_fresh_id β1 β2 (pskl_tophole Qt)) in Dpt
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
    | e_lookeq _ _ _ (pskl_tophole ?q) (pskl_tophole ?q') _ _ _ =>
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
    | e_lookeq _ _ _ (pskl_tophole ?q) (pskl_all_syn ?q') _ _ _ =>
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
    rewrite (@swap_pskl_fresh_id β1 β2 (pskl_tophole Qs)) in Dpt
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
    | e_lookeq _ _ _ (pskl_tophole ?q) _ _ _ _ => rename q into Qs
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
    | e_lookeq _ _ _ _ (pskl_tophole ?q') _ _ _ => rename q' into Qt
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
      | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
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
Lemma e_looksub_inv_hole : forall S0 Θ α m P S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] pskl_hole ⤳ Ξ ⨾ C }}e ->
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
  P' <> pskl_hole ->
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
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  P' <> pskl_hole ->
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
    destruct (e_looksub_inv_hole D2 Hnev HαP) as [-> [-> ->]].
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
    | Hnh : _ <> pskl_hole |- _ => rename Hnh into Hnhl
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
    | e_looksub _ _ _ _ (pskl_tophole ?p) _ _ _ _ => rename p into Ps
    end.
    match goal with
    | Hnh : _ <> pskl_hole |- _ => rename Hnh into Hnhl
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
