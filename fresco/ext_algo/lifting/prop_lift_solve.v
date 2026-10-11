(** Guessing, constraint solving and extraction: lifting from [a_*] to supply-threaded [e_*] derivations. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.ltac_utils.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.prop_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.prop_solve.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.subtyping.prop_solve_rel.
Require Import src.fresco.ext_algo.lifting.prop_lift_context.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.consistency.prop_consis_rename.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.consistency.prop_consis.
Require Import src.fresco.ext_algo.subtyping.def_sub.
Require Import src.fresco.ext_algo.subtyping.prop_sub.
Require Import src.fresco.ext_algo.subtyping.prop_extract.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_wf_preservation.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.ext_algo.typing.def_pat.
Require Import src.fresco.ext_algo.typing.prop_pat.
Require Import src.fresco.algo.basic.prop_mod_compat.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.typing.prop_completeness_pat.
Require Import src.fresco.algo.typing.prop_soundness_typing.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.ext_algo.typing.def_typing.
Require Import src.fresco.ext_algo.typing.prop_typing.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.



(* ===================================================================== *)
(*  §3  ⭐⭐⭐ THE LOOK BLOCK — ALREADY CLOSED, AND IN A DIFFERENT           *)
(*      CURRENCY.  READ THIS BEFORE WRITING ANY BLOCK ABOVE THE GUESS.    *)
(*                                                                        *)
(*  §8c.24's costed plan lists the collection as the lift's next block,    *)
(*  nineteen rows in the CHAIN currency.  ⛔ DO NOT WRITE IT: the chain    *)
(*  currency is UNAVAILABLE here, and the block is already proved in the   *)
(*  currency that is — [a_looksub_lookeq_rel_e] (prop_lift_context.v §7,       *)
(*  campaign §8c.9's transport 5), which is stated a → e and needs only    *)
(*  to be instantiated at the EMPTY pair list.                            *)
(*                                                                        *)
(*  ⛔⛔ WHY THE CHAIN CURRENCY CANNOT WORK ABOVE THE GUESS.  A chain is a  *)
(*  FUNCTION on atoms; [rel_pskl] is deliberately a RELATION (see          *)
(*  prop_solve_det.v §1's header).  The guess could use a chain only      *)
(*  because [a_guess_mono] leaks NOTHING: its ∀ row closes its witness     *)
(*  away, so every atom the derivation invents lands in [dom Ξ] and       *)
(*  [uniq Ξ] — one premise, available at the only consumer — makes the   *)
(*  columns distinct.                                                     *)
(*  ⚠️ ALL FIVE of the collection's ∀ rows LEAK their binder into [𝒞]      *)
(*  (def_look.v's header, and [a_looksub_lookeq_ftv]'s three target-       *)
(*  opening rows), and a leaked binder is NOT in [dom Ξ].  So a LEFT atom  *)
(*  can be a binder in one premise and a generated flexible in its         *)
(*  SIBLING — [LE-Arrow] runs both halves at the SAME [Θ], and the two     *)
(*  side conditions ([β ∉ add α (ftvar Θ ∪ ftvar P1 ∪ ftvar P1')] and      *)
(*  [α1 ∉ add α (add β̂ (ftvar Θ ∪ ftvar P2))]) do not exclude each other.  *)
(*  The e-side keeps the two apart (the opener is drawn at [S0], the       *)
(*  flexible at [S1 ⊇ add opener S0]), so ONE left atom needs TWO right    *)
(*  images and no chain — and no [uniq Ξ] strengthening, since neither     *)
(*  atom need be in the block — can supply them.  ⚙ INFERRED from the two  *)
(*  rules' side conditions, not machine-checked; what IS machine-checked   *)
(*  is that the relational form goes through, which is this section.       *)
(*                                                                        *)
(*  ⭐ CONSEQUENCE FOR THE REST OF THE CAMPAIGN.  Every block above the    *)
(*  guess whose rows can leak a binder into an OUTPUT — the solve layer's  *)
(*  SS-ForallR leaks by design (def_rules.v:625-638) — wants transport 5's *)
(*  shape, not the chain's: side 2 an [e_] derivation, the outputs related *)
(*  at a ρ that GROWS, the blocks read off as [flex_pairs_l] /            *)
(*  [flex_pairs_r].                                                       *)
(*  §8c.9 already built that shape a → a for guess, both solve layers and  *)
(*  the fold (prop_solve_rel.v §3-§6); those are what the a → e versions   *)
(*  should be copied from.                                                *)
(*                                                                        *)
(*  ⚙ THE LIFT PROPER is transport 5 at [ρ = nil], where [rel_pskl] is     *)
(*  reflexivity on anything the support covers ([rel_pskl_refl]) and the   *)
(*  flex agreement is two [reflexivity]s.                                 *)
(* ===================================================================== *)

(** ⚙ An [In]-inclusion between two ways of associating the same pairs —
    what [rel_pskl_close_pair_restrict]'s last two premises ask for. *)
#[local] Ltac in_incl :=
  let a0 := fresh "a0" in let b0 := fresh "b0" in let Hi := fresh "Hi" in
  intros a0 b0 Hi; revert Hi;
  rewrite ? in_app_iff; simpl; rewrite ? in_app_iff; tauto.

(* ===================================================================== *)
(*  §4  ⭐ [guess^TY] LIFTS IN THE REL CURRENCY TOO — and this is the copy *)
(*      the SOLVE layer consumes                                          *)
(*                                                                        *)
(*  A chain form is what a consumer holding [uniq Ξ] would want (AT-Abs). *)
(*  [SE-FlexR] is not such a consumer: it sits inside the solve layer,     *)
(*  whose own transport must be relational (§3), so the guess it calls has *)
(*  to hand its block back as a PAIR LIST that extends the caller's ρ.     *)
(*  ⚙ Row for row this is prop_solve_rel.v §3's [a_guess_mono_rel] with    *)
(*  side 2 moved from [a_guess_mono] to [e_guess_mono]; the two            *)
(*  differences are that the ARROW row THREADS (so the a → a version's     *)
(*  avoid-set [L] and its [uniq Ξ2] / [dom Ξ2 ∩ L] conclusions are         *)
(*  DELETED — both are e-side theorems, prop_guess.v §1) and that every    *)
(*  invented atom is drawn against the SUPPLY instead of against           *)
(*  [ftvar_in_aenv Θ2].                                                    *)
(* ===================================================================== *)

Lemma a_guess_mono_rel_e : forall Θ1 P1 Ξ1 A1,
  a_guess_mono Θ1 P1 Ξ1 A1 ->
  forall S0 P2 ρ V,
  rel_pskl ρ V P1 P2 ->
  (* ⭐ THE SCOPING PREMISE NAMES THE SUBJECT TOO (2026-08-20).  Its ONLY
     job is the ∀ row's [β ∉ V], and that row's side condition is
     [β ∉ ftvar_in_aenv Θ ∪ ftvar_in_pskl P] — BOTH halves.  The narrow
     form is unsatisfiable at [Assign-SolveM] (the trio's rung): there the
     guess runs at the walk's TAIL [Θ0] while [V] is bounded by the whole
     [Ξ ++ (α ~ ⌢) ++ Θ0], and every [Ξ] atom is in [ftvar_in_pskl P] by
     [Assign-Depend]'s own premise.  ⚙ Strictly WEAKER, so every existing
     consumer widens by one [fsetdec].  The ARROW row pays for it with a
     V-SHRINK, which is free because this lemma's only conclusion about
     [V] is a [rel_pskl] — MONOTONE in [V]. *)
  V [<=] ftvar_in_aenv Θ1 ∪ ftvar_in_pskl P1 ->
  (* ⚙ [cols_r ρ] is GONE from the coverage too (2026-08-19): its only use
     was [β2 ∉ cols_r ρ] at the ∀ row, which the PAIR RESTRICTION now buys.
     The extract rung needs the weaker form — its ρ carries the fold's own
     leaked openers, which no single supply covers. *)
  V ∪ ftvar_in_pskl P2 [<=] S0 ->
  exists S1 ρn Ξ2 A2,
    e_guess_mono S0 P2 S1 Ξ2 A2
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    /\ rel_pskl (ρn ++ ρ) V (ptyp_to_pskl A1) (ptyp_to_pskl A2).
Proof.
  intros Θ1 P1 Ξ1 A1 HG.
  induction HG; intros S0 P2 ρ V Hrel Hscp1 Hscp2.
  - (* □ ↦ a fresh flexible on each side, PAIRED — side 2 draws at [S0] *)
    inversion Hrel; subst.
    destruct (atom_fresh S0) as [α2 Hα2].
    exists (add α2 S0), ((α, α2) :: nil), ((α2 ~ abind_flex_mono) ++ nil),
      (ptyp_var_f α2).
    split; [ apply e_guess_mono__ghost; exact Hα2 | ].
    split; [ reflexivity | ].
    split; [ reflexivity | ].
    simpl. constructor. apply rel_atom__pair. left. reflexivity.
  - (* ⫯ — pass through *)
    inversion Hrel; subst.
    match goal with
    | Hb : rel_pskl ρ V P ?X |- _ => rename Hb into Hbody; rename X into Q0
    end.
    assert (Hcov : V ∪ ftvar_in_pskl Q0 [<=] S0)
      by (clear - Hscp2; simpl in *; fsetdec).
    destruct (IHHG S0 Q0 ρ V Hbody Hscp1 Hcov)
      as (S1 & ρn & Ξ2 & A2 & HG2 & E1 & E2 & Hrel').
    exists S1, ρn, Ξ2, A2.
    split; [ apply e_guess_mono__univ_ghost; exact HG2 | ].
    split; [ exact E1 | split; [ exact E2 | exact Hrel' ] ].
  - (* a variable — nothing is invented, and the two names are ρ-related *)
    inversion Hrel; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ => rename Ha into Hat; rename b into β0
    end.
    exists S0, nil, nil, (ptyp_var_f β0).
    split; [ apply e_guess_mono__var | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    simpl. constructor. exact Hat.
  - (* unit *)
    inversion Hrel; subst.
    exists S0, nil, nil, ptyp_unit.
    split; [ apply e_guess_mono__unit | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    simpl. constructor.
  - (* ⭐ the ARROW row — side 1 runs both halves at [Θ], side 2 THREADS *)
    inversion Hrel; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?X, Hb : rel_pskl ρ V Q ?Y |- _ =>
        rename Ha into HrelA; rename Hb into HrelB;
        rename X into Q0a; rename Y into Q0b
    end.
    (* ⭐ THE V-SHRINK.  Both halves run at the SAME [Θ], but each may only
       claim its OWN subject, so [V] is cut to what the half can see.  Free:
       the conclusion is a [rel_pskl], monotone in [V]. *)
    remember (V ∩ (ftvar_in_aenv Θ ∪ ftvar_in_pskl P)) as VA eqn:EVA.
    remember (V ∩ (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q)) as VB eqn:EVB.
    assert (HsA : VA [<=] V) by (subst VA; clear; fsetdec).
    assert (HsB : VB [<=] V) by (subst VB; clear; fsetdec).
    assert (HrelA0 : rel_pskl ρ VA P Q0a).
    { eapply rel_pskl_shrink_V; [ exact HrelA | ].
      intros a Ha Hf. subst VA. clear - Ha Hf. fsetdec. }
    assert (HrelB0 : rel_pskl ρ VB Q Q0b).
    { eapply rel_pskl_shrink_V; [ exact HrelB | ].
      intros a Ha Hf. subst VB. clear - Ha Hf. fsetdec. }
    assert (Hscp1A : VA [<=] ftvar_in_aenv Θ ∪ ftvar_in_pskl P)
      by (subst VA; clear; fsetdec).
    assert (Hscp1B : VB [<=] ftvar_in_aenv Θ ∪ ftvar_in_pskl Q)
      by (subst VB; clear; fsetdec).
    assert (HcovA : VA ∪ ftvar_in_pskl Q0a [<=] S0)
      by (clear - Hscp2 HsA; simpl in *; fsetdec).
    destruct (IHHG1 S0 Q0a ρ VA HrelA0 Hscp1A HcovA)
      as (S1 & ρnA & Ξ2a & A2a & HG2a & E1a & E2a & HrelA0').
    pose proof (e_guess_mono_supply_grows HG2a) as Hgr1.
    assert (HcovB : VB ∪ ftvar_in_pskl Q0b [<=] S1)
      by (clear - Hscp2 Hgr1 HsB; simpl in *; fsetdec).
    destruct (IHHG2 S1 Q0b ρ VB HrelB0 Hscp1B HcovB)
      as (S2 & ρnB & Ξ2b & B2b & HG2b & E1b & E2b & HrelB0').
    assert (HrelA' : rel_pskl (ρnA ++ ρ) V (ptyp_to_pskl A) (ptyp_to_pskl A2a))
      by (eapply rel_pskl_mono; [ exact HrelA0' | intros x y Hx; exact Hx
                                | exact HsA ]).
    assert (HrelB' : rel_pskl (ρnB ++ ρ) V (ptyp_to_pskl B) (ptyp_to_pskl B2b))
      by (eapply rel_pskl_mono; [ exact HrelB0' | intros x y Hx; exact Hx
                                | exact HsB ]).
    clear HrelA0' HrelB0'.
    exists S2, (ρnA ++ ρnB), (Ξ2a ++ Ξ2b), (ptyp_arrow A2a B2b).
    split; [ eapply e_guess_mono__arrow; eassumption | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    simpl. constructor.
    + eapply rel_pskl_mono; [ exact HrelA' | | intros x Hx; exact Hx ].
      intros a b Hin. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [Hin | Hin];
        [ left; apply in_or_app; left; exact Hin | right; exact Hin ].
    + eapply rel_pskl_mono; [ exact HrelB' | | intros x Hx; exact Hx ].
      intros a b Hin. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [Hin | Hin];
        [ left; apply in_or_app; right; exact Hin | right; exact Hin ].
  - (* ⭐ the ∀ row — side 2 opens at ITS supply-fresh witness; the two
       openers PAIR, and the yields re-close along the RESTRICTED list *)
    inversion Hrel; subst.
    match goal with
    | Hb : rel_pskl ρ V P ?X |- _ => rename Hb into Hbody; rename X into Q0
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh S0) as [β2 Hβ2].
    (* ⭐ THE RESTRICTION (prop_solve_rel.v §6).  [rel_pskl_close_pair] wants
       [β] off [cols_l ρ]; side 2 buys that from the SUPPLY and side 1 has
       none, so the pairs the close must not see are DELETED.  Legal here
       because the row has not opened yet: [β] misses [P] by the rule's own
       side condition, [β2] misses [Q0] by the supply. *)
    assert (Hbody0 : rel_pskl (restrict_pairs β β2 ρ) V P Q0).
    { apply rel_pskl_restrict;
        [ exact Hbody
        | clear - Hβ1; fsetdec
        | clear - Hβ2 Hscp2; simpl in Hscp2; fsetdec ]. }
    assert (Hrelo : rel_pskl ((β, β2) :: restrict_pairs β β2 ρ) V
                      (open_pskl_wrt_pskl P (pskl_var_f β))
                      (open_pskl_wrt_pskl Q0 (pskl_var_f β2)))
      by (apply rel_pskl_open_pair; exact Hbody0).
    assert (Hlow : ftvar_in_pskl P
                   [<=] ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f β)))
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_lower).
    assert (Hscp1' : V [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ)
                       ∪ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f β)))
      by (simpl; simpl in Hscp1; clear - Hscp1 Hlow; fsetdec).
    assert (Hup : ftvar_in_pskl (open_pskl_wrt_pskl Q0 (pskl_var_f β2))
                  [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl Q0)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hscp2' : V ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q0 (pskl_var_f β2))
                       [<=] add β2 S0)
      by (simpl in *; clear - Hscp2 Hup; fsetdec).
    destruct (IHHG (add β2 S0) (open_pskl_wrt_pskl Q0 (pskl_var_f β2))
                ((β, β2) :: restrict_pairs β β2 ρ) V Hrelo Hscp1' Hscp2')
      as (S1 & ρn & Ξ2 & A2 & HG2 & E1 & E2 & Hrel').
    exists S1, ρn, Ξ2, (ptyp_all (close_ptyp_wrt_ptyp β2 A2)).
    (* the two openers leave the two block domains *)
    assert (HβΞ1 : β `notin` dom Ξ).
    { intros Hin.
      pose proof (a_guess_mono_generated_fresh HG Hin) as Hgf.
      simpl in Hgf. clear - Hgf. fsetdec. }
    assert (Hβ2Ξ2 : β2 `notin` dom Ξ2)
      by (pose proof (e_guess_mono_block_fresh HG2) as Hbf;
          clear - Hbf; fsetdec).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    split;
      [ apply e_guess_mono__forall with (β := β2); [ exact Hβ2 | exact HG2 ] | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    simpl. rewrite ! ptyp_to_pskl_close.
    constructor.
    eapply rel_pskl_close_pair_restrict.
    + exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + clear - HβΞ1 Hdfl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + clear - Hβ2Ξ2 Hdfr. fsetdec.
    + intros a b Hin. apply in_or_app. left. exact Hin.
    + intros a b Hin. apply in_or_app. right. exact Hin.
Qed.

(** The sort wrapper, relationally: [guess^SK] moves nothing and pairs
    nothing, [guess^TY] is §4's rows read back through the painting. *)
Lemma a_guess_rel_e : forall Θ1 NM Q1 Ξ1 Q1',
  a_guess Θ1 NM Q1 Ξ1 Q1' ->
  forall S0 Q2 ρ V,
  rel_pskl ρ V Q1 Q2 ->
  V [<=] ftvar_in_aenv Θ1 ->
  V ∪ ftvar_in_pskl Q2 [<=] S0 ->
  exists S1 ρn Ξ2 Q2',
    e_guess S0 NM Q2 S1 Ξ2 Q2'
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    /\ rel_pskl (ρn ++ ρ) V Q1' Q2'.
Proof.
  intros Θ1 NM Q1 Ξ1 Q1' Hg S0 Q2 ρ V Hrel Hscp1 Hscp2.
  destruct Hg as [ Θ0 Q0 | Θ0 Q0 Ξ0 A Hgm ].
  - exists S0, nil, nil, Q2.
    split; [ apply e_guess__sk | ].
    split; [ reflexivity | split; [ reflexivity | simpl; exact Hrel ] ].
  - assert (Hscp1' : V [<=] ftvar_in_aenv Θ0 ∪ ftvar_in_pskl Q0)
      by (clear - Hscp1; fsetdec).
    destruct (a_guess_mono_rel_e Hgm Hrel Hscp1' Hscp2)
      as (S1 & ρn & Ξ2 & A2 & HG2 & E1 & E2 & Hrel').
    exists S1, ρn, Ξ2, (ptyp_to_pskl A2).
    split; [ apply e_guess__ty; exact HG2 | ].
    split; [ exact E1 | split; [ exact E2 | exact Hrel' ] ].
Qed.

(* ===================================================================== *)
(*  §5  ⭐ THE eq-SOLVE LIFTS — twelve rows                                *)
(*                                                                        *)
(*  Row for row prop_solve_rel.v §4's [a_solve_eq_rel] with side 2 moved   *)
(*  from [a_solve_eq] to [e_solve_eq].  Three systematic changes:          *)
(*                                                                        *)
(*  ⭐ THE AVOID-SET [L] AND ITS TWO CONCLUSIONS ARE GONE.  On the a-side  *)
(*  the caller had to be told the new block dodges [L] and is [uniq];      *)
(*  threaded, both are theorems of the e-side derivation alone             *)
(*  ([e_solve_sub_eq_block]), so the arrow row's bookkeeping collapses to  *)
(*  "the supply grew".                                                     *)
(*                                                                        *)
(*  ⭐ EVERY INVENTED ATOM IS DRAWN AGAINST THE SUPPLY.  Side 2's openers  *)
(*  need [∉ S0] and nothing else — but the [flex_agree_rel] push still     *)
(*  wants them off [dom Θ2], which is why the coverage premise             *)
(*  [dom Θ2 [<=] S0] is carried.  ⚙ [dom], not [ftvar_in_aenv]: that is    *)
(*  the version the arrow row can re-establish for [Ξ2a ++ Θ2] out of the  *)
(*  e-side block facts alone.                                              *)
(*                                                                        *)
(*  ⚠️ THE COVERAGE IS THREE PREMISES, NOT ONE UNION.  Written as a single *)
(*  [… ∪ … ∪ … ∪ … [<=] S0] every later [fsetdec] would face six set       *)
(*  variables, which is the documented cliff (§8c.23).                     *)
(* ===================================================================== *)

(** Restrict old opener pairs before pushing the fresh rigid pair.  This
    preserves the context agreement and scopes used by both solving lifts;
    generated blocks remain disjoint from the enlarged relation. *)
Lemma solve_lift_open_context : forall ρ V Θ Θ2 S (Ξ : aenv) β β2,
  flex_agree_rel ρ V Θ Θ2 ->
  V [<=] ftvar_in_aenv Θ -> dom Θ2 [<=] S -> V ∪ cols_r ρ [<=] S ->
  dom Ξ ∩ cols_l ρ [=] empty ->
  dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty ->
  β `notin` ftvar_in_aenv Θ -> β2 `notin` S ->
  flex_agree_rel ((β, β2) :: restrict_pairs β β2 ρ) V
    ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2) /\
  V [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) /\
  dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S /\
  V ∪ cols_r ((β, β2) :: restrict_pairs β β2 ρ) [<=] add β2 S /\
  dom Ξ ∩ cols_l ((β, β2) :: restrict_pairs β β2 ρ) [=] empty.
Proof.
  intros * Hagr Hscp1 HdΘ Hscp2 Hblk Hgen Hβ Hβ2.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
  pose proof (cols_l_restrict_pairs β β2 ρ) as Hcl0.
  pose proof (cols_r_restrict_pairs β β2 ρ) as Hcr0.
  split.
  - apply flex_agree_rel_push_look.
    + eapply flex_agree_rel_weaken;
        [ exact Hagr | intros a b Hin; eapply restrict_pairs_incl; exact Hin
        | intros a Ha; exact Ha ].
    + clear - Hβ Hds1; fsetdec.
    + clear - Hβ2 HdΘ; fsetdec.
  - split; [ simpl; clear - Hscp1; fsetdec | ].
    split; [ simpl; clear - HdΘ; fsetdec | ].
    split; [ simpl; clear - Hscp2 Hcr0; fsetdec | ].
    simpl. simpl in Hgen. clear - Hblk Hgen Hcl0; fsetdec.
Qed.

Arguments solve_lift_open_context {ρ V Θ Θ2 S Ξ β β2} _ _ _ _ _ _ _ _.

(** ⭐ SE-Forall, SE-GhostForall and SE-ForallGhost, ONE proof: they differ
    only in which side OPENS at the binder (the other keeps its [∀◇]).
    Side 2 opens at ITS supply-fresh witness; the openers PAIR, after the
    old pairs at either opener are restricted away. *)
Lemma solve_eq_binder_row : forall (opensP opensQ : bool) {Θ P Q Ξ Y β},
  β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (binder_body opensP P β)
     ∼ (binder_body opensQ Q β) ⤳ Ξ ⨾ Y }}a ->
  (forall S0 Θ2 P2 Q2 ρ V,
     rel_pskl ρ V (binder_body opensP P β) P2 ->
     rel_pskl ρ V (binder_body opensQ Q β) Q2 ->
     flex_agree_rel ρ V ((β ~ abind_tvar) ++ Θ) Θ2 ->
     V [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) ->
     dom Ξ ∩ cols_l ρ [=] empty ->
     dom Θ2 [<=] S0 ->
     V ∪ cols_r ρ [<=] S0 ->
     ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2 [<=] S0 ->
     exists S1 ρn Ξ2 P2',
       {{ S0 ↝ S1 ⊨ Θ2 ⊢ₑ P2 ∼ Q2 ⤳ Ξ2 ⨾ P2' }}e
       /\ Ξ = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
       /\ rel_pskl (ρn ++ ρ) V Y P2') ->
  (forall S0 S1 Θ P Q Ξ P' β,
     β `notin` S0 ->
     {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
        ⊢ₑ (binder_body opensP P β) ∼ (binder_body opensQ Q β) ⤳ Ξ ⨾ P' }}e ->
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (binder_head opensP P) ∼ (binder_head opensQ Q)
        ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}e) ->
  forall S0 Θ2 P3 Q3 ρ V,
  rel_pskl ρ V (binder_head opensP P) P3 ->
  rel_pskl ρ V (binder_head opensQ Q) Q3 ->
  flex_agree_rel ρ V Θ Θ2 ->
  V [<=] ftvar_in_aenv Θ ->
  dom Ξ ∩ cols_l ρ [=] empty ->
  dom Θ2 [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P3 ∪ ftvar_in_pskl Q3 [<=] S0 ->
  exists S1 ρn Ξ2 P2',
    {{ S0 ↝ S1 ⊨ Θ2 ⊢ₑ P3 ∼ Q3 ⤳ Ξ2 ⨾ P2' }}e
    /\ Ξ = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    /\ rel_pskl (ρn ++ ρ) V (pskl_all_syn (close_pskl_wrt_pskl β Y)) P2'.
Proof.
  intros opensP opensQ Θ P Q Ξ Y β Hβ1 HD IH Hrule
    S0 Θ2 P3 Q3 ρ V HrelP HrelQ Hagr Hscp1 Hblk HdΘ Hscp2 Hcov.
  destruct (rel_pskl_binder_head_inv HrelP) as (P2b & -> & HrP0).
  destruct (rel_pskl_binder_head_inv HrelQ) as (Q2b & -> & HrQ0).
  rewrite !ftvar_in_pskl_binder_head in Hcov.
  destruct (atom_fresh S0) as [β2 Hβ2].
  assert (Hcov' : ftvar_in_pskl (binder_body opensP P2b β2)
                  ∪ ftvar_in_pskl (binder_body opensQ Q2b β2) [<=] add β2 S0).
  { pose proof (ftvar_in_pskl_binder_body_upper opensP P2b β2) as HupP.
    pose proof (ftvar_in_pskl_binder_body_upper opensQ Q2b β2) as HupQ.
    clear - Hcov HupP HupQ; fsetdec. }
  assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
    by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD)).
  assert (HβΘ : β `notin` ftvar_in_aenv Θ)
    by (clear - Hβ1; fsetdec).
  destruct (solve_lift_open_context Hagr Hscp1 HdΘ Hscp2 Hblk Hd1p HβΘ Hβ2)
    as (Hagr' & Hscp1' & HdΘ' & Hscp2' & Hblk').
  assert (HrP0' : rel_pskl ((β, β2) :: restrict_pairs β β2 ρ) V
                    (binder_body opensP P β) (binder_body opensP P2b β2)).
  { apply rel_pskl_binder_body. apply rel_pskl_restrict;
      [ exact HrP0 | clear - Hβ1; fsetdec | clear - Hβ2 Hcov; fsetdec ]. }
  assert (HrQ0' : rel_pskl ((β, β2) :: restrict_pairs β β2 ρ) V
                    (binder_body opensQ Q β) (binder_body opensQ Q2b β2)).
  { apply rel_pskl_binder_body. apply rel_pskl_restrict;
      [ exact HrQ0 | clear - Hβ1; fsetdec | clear - Hβ2 Hcov; fsetdec ]. }
  destruct (IH (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
              (binder_body opensP P2b β2) (binder_body opensQ Q2b β2)
              ((β, β2) :: restrict_pairs β β2 ρ) V
              HrP0' HrQ0' Hagr' Hscp1' Hblk' HdΘ' Hscp2' Hcov')
    as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
  assert (Hd2p : dom Ξ2 ∩ add β2 S0 [=] empty)
    by (apply (proj2 e_solve_sub_eq_block) in D2p; tauto).
  pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
  pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
  exists S1, ρn, Ξ2, (pskl_all_syn (close_pskl_wrt_pskl β2 Y2)).
  split; [ apply Hrule; [ exact Hβ2 | exact D2p ] | ].
  split; [ exact E1 | split; [ exact E2 | ] ].
  constructor.
  eapply rel_pskl_close_pair_restrict.
  - exact Hrel'.
  - clear - Hβ1 Hscp1. fsetdec.
  - simpl in Hd1p. clear - Hd1p Hdfl. fsetdec.
  - clear - Hβ2 Hscp2. fsetdec.
  - clear - Hd2p Hdfr. fsetdec.
  - in_incl.
  - in_incl.
Qed.

Lemma a_solve_eq_rel_e : forall Θ1 P1 Q1 Ξ1 P1',
  {{ Θ1 ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}a ->
  forall S0 Θ2 P2 Q2 ρ V,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V Q1 Q2 ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  (* ⭐⭐ THE SCOPING PREMISE SPLIT IN TWO (2026-08-19).  The old single
     [V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1] is UNSATISFIABLE at [a_extract]:
     there ρ carries the COLLECTION's leaked openers, which are bound
     nowhere.  Its two jobs separate cleanly —
     - the ∀ rows wanted [β ∉ V ∪ cols_l ρ]; [V] still comes from the
       context and [cols_l ρ] is now paid by the PAIR RESTRICTION
       (prop_solve_rel.v §6), which deletes the offending pairs instead;
     - the ARROW rows wanted the newly generated block to dodge the pair
       columns, and that is the SECOND premise below — a statement about
       the derivation's OWN output block, which every consumer can see. *)
  V [<=] ftvar_in_aenv Θ1 ->
  dom Ξ1 ∩ cols_l ρ [=] empty ->
  dom Θ2 [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2 [<=] S0 ->
  exists S1 ρn Ξ2 P2',
    {{ S0 ↝ S1 ⊨ Θ2 ⊢ₑ P2 ∼ Q2 ⤳ Ξ2 ⨾ P2' }}e
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    /\ rel_pskl (ρn ++ ρ) V P1' P2'.
Proof.
  intros Θ1 P1 Q1 Ξ1 P1' HD.
  induction HD;
    intros S0 Θ2 P3 Q3 ρ V HrelP HrelQ Hagr Hscp1 Hblk HdΘ Hscp2 Hcov.
  - (* SE-Unit *)
    inversion HrelP; subst. inversion HrelQ; subst.
    exists S0, nil, nil, pskl_unit.
    split; [ apply e_solve_eq__unit | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    simpl. constructor.
  - (* SE-Var: a variable subject answers itself *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ => rename Ha into Hat; rename b into β0
    end.
    exists S0, nil, nil, (pskl_var_f β0).
    split; [ apply e_solve_eq__var | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    simpl. constructor. exact Hat.
  - (* ⭐ SE-FlexR — the layer's ONLY generating row, and §4 is what it calls *)
    inversion HrelQ; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ => rename Ha into Hat; rename b into β0
    end.
    match goal with
    | Hf : a_flex_tvar Θ α |- _ => rename Hf into Hflex1
    end.
    assert (Hflex2 : a_flex_tvar Θ2 β0).
    { inversion Hat; subst.
      - exact (proj1 ((proj2 Hagr) _ _ ltac:(eassumption)) Hflex1).
      - exact (proj1 ((proj1 Hagr) _ ltac:(eassumption)) Hflex1). }
    match goal with
    | HG : a_guess_mono Θ P Ξ ?AA |- _ => rename HG into Hguess
    end.
    assert (HcovG : V ∪ ftvar_in_pskl P3 [<=] S0)
      by (clear - Hscp2 Hcov; fsetdec).
    assert (Hscp1G : V [<=] ftvar_in_aenv Θ ∪ ftvar_in_pskl P)
      by (clear - Hscp1; fsetdec).
    destruct (a_guess_mono_rel_e Hguess HrelP Hscp1G HcovG)
      as (S1 & ρn & Ξ2g & A2 & HG2 & E1 & E2 & Hrel').
    exists S1, ρn, Ξ2g, (ptyp_to_pskl A2).
    split.
    { apply e_solve_eq__flex_r.
      - exact Hflex2.
      - eapply rel_pskl_non_flex; [ exact HrelP | exact Hagr | assumption ].
      - eapply rel_pskl_nonghost; [ exact HrelP | assumption ].
      - exact HG2. }
    split; [ exact E1 | split; [ exact E2 | exact Hrel' ] ].
  - (* SE-GhostL: a ghost subject answers the target *)
    inversion HrelP; subst.
    exists S0, nil, nil, Q3.
    split; [ apply e_solve_eq__ghost_l | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    simpl. exact HrelQ.
  - (* SE-VacuousR: a ghost target answers the subject *)
    inversion HrelQ; subst.
    exists S0, nil, nil, P3.
    split; [ apply e_solve_eq__ghost_r | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    simpl. exact HrelP.
  - (* ⭐ SE-Arrow — both sides thread, so the second half's coverage is the
       first half's OUTPUT supply *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P1 ?xa, Hb : rel_pskl ρ V P2 ?xb,
      Hc : rel_pskl ρ V Q1 ?xc, Hd : rel_pskl ρ V Q2 ?xd |- _ =>
        rename Ha into HrPa; rename Hb into HrPb;
        rename Hc into HrQa; rename Hd into HrQb;
        rename xa into P2a; rename xb into P2b;
        rename xc into Q2a; rename xd into Q2b
    end.
    assert (HcovA : ftvar_in_pskl P2a ∪ ftvar_in_pskl Q2a [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    assert (Hblk1 : dom Ξ1 ∩ cols_l ρ [=] empty)
      by (rewrite dom_app in Hblk; clear - Hblk; fsetdec).
    destruct (IHHD1 S0 Θ2 P2a Q2a ρ V HrPa HrQa Hagr Hscp1 Hblk1
                HdΘ Hscp2 HcovA)
      as (S1 & ρnA & Ξ2a & P2a' & D2a & E1a & E2a & HrelA').
    pose proof (e_solve_eq_supply_grows D2a) as Hgr1.
    assert (Hd1a : dom Ξ1 ∩ ftvar_in_aenv Θ [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD1)).
    assert (Hd2a : dom Ξ2a ∩ S0 [=] empty)
      by (apply (proj2 e_solve_sub_eq_block) in D2a; tauto).
    assert (Hi2a : dom Ξ2a [<=] S1) by (exact (e_solve_eq_block_in_supply D2a)).
    pose proof (dom_flex_pairs_l ρnA) as Hdfl. rewrite <- E1a in Hdfl.
    pose proof (dom_flex_pairs_r ρnA) as Hdfr. rewrite <- E2a in Hdfr.
    assert (Hagr' : flex_agree_rel (ρnA ++ ρ) V (Ξ1 ++ Θ) (Ξ2a ++ Θ2)).
    { rewrite E1a, E2a. apply flex_agree_rel_push_pairs.
      - exact Hagr.
      (* ⭐ the head block dodges the pair columns — the SECOND half of the
         old scoping premise, now hypothesised directly. *)
      - clear - Hd1a Hscp1 Hdfl Hblk1. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V [<=] ftvar_in_aenv (Ξ1 ++ Θ))
      by (rewrite ftvar_in_aenv_app; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom (Ξ2a ++ Θ2) [<=] S1)
      by (rewrite dom_app; clear - Hi2a HdΘ Hgr1; fsetdec).
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hscp2 Hdfr Hi2a Hgr1. fsetdec. }
    assert (HcovB : ftvar_in_pskl P2b ∪ ftvar_in_pskl Q2b [<=] S1)
      by (clear - Hcov Hgr1; simpl in *; fsetdec).
    assert (HrPb' : rel_pskl (ρnA ++ ρ) V P2 P2b)
      by (apply rel_pskl_widen; exact HrPb).
    assert (HrQb' : rel_pskl (ρnA ++ ρ) V Q2 Q2b)
      by (apply rel_pskl_widen; exact HrQb).
    assert (Hd1b : dom Ξ2 ∩ ftvar_in_aenv (Ξ1 ++ Θ) [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD2)).
    assert (Hblk2 : dom Ξ2 ∩ cols_l (ρnA ++ ρ) [=] empty).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app in Hd1b.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      rewrite dom_app in Hblk.
      clear - Hd1b Hds Hdfl Hblk. fsetdec. }
    destruct (IHHD2 S1 (Ξ2a ++ Θ2) P2b Q2b (ρnA ++ ρ) V
                HrPb' HrQb' Hagr' Hscp1' Hblk2 HdΘ' Hscp2' HcovB)
      as (S2 & ρnB & Ξ2b & P2b' & D2b & E1b & E2b & HrelB').
    exists S2, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a), (pskl_arrow P2a' P2b').
    split; [ eapply e_solve_eq__arrow; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    constructor.
    + apply rel_pskl_widen_hd. exact HrelA'.
    + apply rel_pskl_app_assoc. exact HrelB'.
  - (* ⭐ SE-Forall — side 2 opens at ITS supply-fresh witness; openers PAIR *)
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    exact (solve_eq_binder_row true true Hβ1 HD IHHD e_solve_eq__forall
             HrelP HrelQ Hagr Hscp1 Hblk HdΘ Hscp2 Hcov).
  - (* SE-UnivGhost: ⫯ on both sides passes through *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa, Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    assert (Hcov' : ftvar_in_pskl P2b ∪ ftvar_in_pskl Q2b [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    destruct (IHHD S0 Θ2 P2b Q2b ρ V HrP0 HrQ0 Hagr Hscp1 Hblk HdΘ Hscp2 Hcov')
      as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
    exists S1, ρn, Ξ2, (pskl_univ_ghost Y2).
    split; [ apply e_solve_eq__univ_ghost_both; exact D2p | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    constructor. exact Hrel'.
  - (* SE-GhostForall: the TARGET opens; the subject stays whole *)
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    exact (solve_eq_binder_row false true Hβ1 HD IHHD e_solve_eq__univ_ghost_l_all
             HrelP HrelQ Hagr Hscp1 Hblk HdΘ Hscp2 Hcov).
  - (* SE-GhostGuarded: the subject strips its ⫯ *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa |- _ =>
        rename Ha into HrP0; rename xa into P2b
    end.
    assert (Hcov' : ftvar_in_pskl P2b ∪ ftvar_in_pskl Q3 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    destruct (IHHD S0 Θ2 P2b Q3 ρ V HrP0 HrelQ Hagr Hscp1 Hblk HdΘ Hscp2 Hcov')
      as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
    exists S1, ρn, Ξ2, Y2.
    split.
    { apply e_solve_eq__univ_ghost_l_guarded;
        [ eapply rel_pskl_guarded; [ exact HrelQ | assumption ]
        | exact D2p ]. }
    split; [ exact E1 | split; [ exact E2 | exact Hrel' ] ].
  - (* SE-ForallGhost: the SUBJECT opens; the target stays whole *)
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    exact (solve_eq_binder_row true false Hβ1 HD IHHD e_solve_eq__all_l_univ_ghost
             HrelP HrelQ Hagr Hscp1 Hblk HdΘ Hscp2 Hcov).
  - (* SE-GuardedGhost: the target strips its ⫯ *)
    inversion HrelQ; subst.
    match goal with
    | Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Hb into HrQ0; rename xb into Q2b
    end.
    assert (Hcov' : ftvar_in_pskl P3 ∪ ftvar_in_pskl Q2b [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    destruct (IHHD S0 Θ2 P3 Q2b ρ V HrelP HrQ0 Hagr Hscp1 Hblk HdΘ Hscp2 Hcov')
      as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
    exists S1, ρn, Ξ2, Y2.
    split.
    { apply e_solve_eq__univ_ghost_r_guarded;
        [ eapply rel_pskl_guarded; [ exact HrelP | assumption ]
        | exact D2p ]. }
    split; [ exact E1 | split; [ exact E2 | exact Hrel' ] ].
Qed.

(* ===================================================================== *)
(*  §6  ⭐ THE sub-SOLVE LIFTS — nine rows                                 *)
(*                                                                        *)
(*  prop_solve_rel.v §5's [a_solve_sub_rel], side 2 moved to              *)
(*  [e_solve_sub].  ⭐ THE EXTRA COLUMN [ρx] IS WHAT MAKES THIS BLOCK      *)
(*  DIFFERENT FROM §5, and it is exactly the reason the whole campaign     *)
(*  above the guess must be relational: [SS-ForallR] does NOT close over   *)
(*  its opener — the leak is by design (def_rules.v:625-638) — so the      *)
(*  opener survives in the YIELD as a rigid pair that never joins the      *)
(*  block.  On the e-side its side condition is ONE set instead of two:    *)
(*  a leaked opener is off the INPUT SUPPLY, which is all any caller of    *)
(*  this lemma can be told and all it needs.                              *)
(* ===================================================================== *)

(** Re-shuffle a pair list by any [In]-preserving permutation (the local
    tactic prop_solve_rel.v §5 uses; it is [Local] there). *)
#[local] Ltac rel_perm H :=
  eapply rel_pskl_mono;
    [ exact H
    | let a0 := fresh "a0" in let b0 := fresh "b0" in
      let Hi := fresh "Hi" in
      intros a0 b0 Hi; revert Hi;
      rewrite ? in_app_iff; simpl; rewrite ? in_app_iff; tauto
    | let x0 := fresh "x0" in let Hx0 := fresh "Hx0" in
      intros x0 Hx0; exact Hx0 ].

(** ⭐ THE THIN MORPHISM — only the pairs at the LEFT skeleton's own free
    variables have to survive.  ⚙ [S-ForallR]'s TRIM uses it to DELETE a
    leaked pair whose opener never reached the output. *)
Lemma rel_pskl_morph_ftv : forall ρ ρ' V V' P Q,
  rel_pskl ρ V P Q ->
  (forall a b, a `in` ftvar_in_pskl P -> In (a, b) ρ -> rel_atom ρ' V' a b) ->
  (forall a, a `in` ftvar_in_pskl P -> a `in` V -> rel_atom ρ' V' a a) ->
  rel_pskl ρ' V' P Q.
Proof.
  intros ρ ρ' V V' P Q Hrel; induction Hrel; intros Hp Hv.
  - apply rel_pskl__unit.
  - apply rel_pskl__var_b.
  - apply rel_pskl__var_f.
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
    end;
      [ apply Hp | apply Hv ]; solve [ simpl; clear; fsetdec | assumption ].
  - apply rel_pskl__arrow.
    + apply IHHrel1;
        [ intros a b Ha Hin; apply Hp;
            [ simpl; clear - Ha; fsetdec | exact Hin ]
        | intros a Ha Hin; apply Hv;
            [ simpl; clear - Ha; fsetdec | exact Hin ] ].
    + apply IHHrel2;
        [ intros a b Ha Hin; apply Hp;
            [ simpl; clear - Ha; fsetdec | exact Hin ]
        | intros a Ha Hin; apply Hv;
            [ simpl; clear - Ha; fsetdec | exact Hin ] ].
  - apply rel_pskl__all_syn. apply IHHrel; assumption.
  - apply rel_pskl__ghost.
  - apply rel_pskl__univ_ghost. apply IHHrel; assumption.
Qed.

Lemma a_solve_sub_rel_e : forall Θ1 m P1 Q1 Ξ1 P1',
  {{ Θ1 ⊢ₛ P1 ≼[ m ] Q1 ⤳ Ξ1 ⨾ P1' }}a ->
  forall S0 Θ2 P3 Q3 ρ V,
  rel_pskl ρ V P1 P3 ->
  rel_pskl ρ V Q1 Q3 ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  (* ⭐⭐ THE SCOPING PREMISE SPLIT IN TWO (2026-08-19).  The old single
     [V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1] is UNSATISFIABLE at [a_extract]:
     there ρ carries the COLLECTION's leaked openers, which are bound
     nowhere.  Its two jobs separate cleanly —
     - the ∀ rows wanted [β ∉ V ∪ cols_l ρ]; [V] still comes from the
       context and [cols_l ρ] is now paid by the PAIR RESTRICTION
       (prop_solve_rel.v §6), which deletes the offending pairs instead;
     - the ARROW rows wanted the newly generated block to dodge the pair
       columns, and that is the SECOND premise below — a statement about
       the derivation's OWN output block, which every consumer can see. *)
  V [<=] ftvar_in_aenv Θ1 ->
  dom Ξ1 ∩ cols_l ρ [=] empty ->
  dom Θ2 [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P3 ∪ ftvar_in_pskl Q3 [<=] S0 ->
  exists S1 ρx ρn Ξ2 P3',
    {{ S0 ↝ S1 ⊨ Θ2 ⊢ₛ P3 ≼[ m ] Q3 ⤳ Ξ2 ⨾ P3' }}e
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    (* ⭐ THE LEFT COLUMN ALSO DODGES THE DERIVATION'S OWN BLOCK
       (2026-08-21, §8c.41).  A leaked opener is bound NOWHERE, so nothing
       stops it colliding with a generated flexible NAME — and the extract
       rung's consumer ([a_sub__forall_l]) must drop the ρx column at the
       atoms of a skeleton wf over [Ξ1 ++ Θ1], which is exactly this.
       ⚙ Free at [SS-ForallR], the only row that creates a pair: its proof
       already derives [β ∉ dom Ξ] for the recursive call's block premise. *)
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 ∪ dom Ξ1 /\ b `notin` S0)
    (* ⭐ AND THE LEFT COLUMN LIVES IN THE OUTPUT (2026-08-21, §8c.41): the
       ∀ rows carry a leaked pair only when the opener actually ESCAPES.
       This is what keeps the extract rung's FINAL GUESS off the ρx column —
       that guess avoids [ftvar_in_pskl Q], hence everything ρx names. *)
    /\ cols_l ρx [<=] ftvar_in_pskl P1'
    /\ rel_pskl (ρx ++ ρn ++ ρ) V P1' P3'.
Proof.
  intros Θ1 m P1 Q1 Ξ1 P1' HD.
  induction HD;
    intros S0 Θ2 P3 Q3 ρ V HrelP HrelQ Hagr Hscp1 Hblk HdΘ Hscp2 Hcov.
  - (* SS-Var *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ => rename Ha into Hat; rename b into β0
    end.
    exists S0, nil, nil, nil, (pskl_var_f β0).
    split; [ apply e_solve_sub__var | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor. exact Hat.
  - (* SS-ForallL: the subject opens; openers PAIR; the yield re-closes *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa |- _ =>
        rename Ha into HrP0; rename xa into P3b
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh S0) as [β2 Hβ2].
    assert (HupP : ftvar_in_pskl (open_pskl_wrt_pskl P3b (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl P3b)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl (open_pskl_wrt_pskl P3b (pskl_var_f β2))
                    ∪ ftvar_in_pskl Q3 [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupP; fsetdec).
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ HD)).
    assert (HβΘ : β `notin` ftvar_in_aenv Θ)
      by (clear - Hβ1; fsetdec).
    destruct (solve_lift_open_context Hagr Hscp1 HdΘ Hscp2 Hblk Hd1p HβΘ Hβ2)
      as (Hagr' & Hscp1' & HdΘ' & Hscp2' & Hblk').
    assert (HrP0r : rel_pskl (restrict_pairs β β2 ρ) V P P3b)
      by (apply rel_pskl_restrict;
          [ exact HrP0 | clear - Hβ1; fsetdec
          | clear - Hβ2 Hcov; simpl in Hcov; fsetdec ]).
    assert (HrelQr : rel_pskl (restrict_pairs β β2 ρ) V Q Q3)
      by (apply rel_pskl_restrict;
          [ exact HrelQ | clear - Hβ1; fsetdec
          | clear - Hβ2 Hcov; simpl in Hcov; fsetdec ]).
    destruct (IHHD (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (open_pskl_wrt_pskl P3b (pskl_var_f β2)) Q3
                ((β, β2) :: restrict_pairs β β2 ρ) V
                ltac:(apply rel_pskl_open_pair; exact HrP0r)
                ltac:(apply rel_pskl_extend_pair; exact HrelQr)
                Hagr' Hscp1' Hblk' HdΘ' Hscp2' Hcov')
      as (S1 & ρx & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hρx & Htr & Hrel').
    assert (Hd2p : dom Ξ2 ∩ add β2 S0 [=] empty)
      by (apply (proj1 e_solve_sub_eq_block) in D2p; tauto).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    assert (Hβcl : β `notin` cols_l ρx).
    { apply cols_l_fresh. intros a b Hin.
      destruct (Hρx a b Hin) as [Ha _]. simpl in Ha.
      intros ->. clear - Ha. fsetdec. }
    assert (Hβ2cr : β2 `notin` cols_r ρx).
    { apply cols_r_fresh. intros a b Hin.
      destruct (Hρx a b Hin) as [_ Hb].
      intros ->. clear - Hb. fsetdec. }
    exists S1, ρx, ρn, Ξ2, (pskl_all_syn (close_pskl_wrt_pskl β2 Y2)).
    split;
      [ apply e_solve_sub__forall_l with (β := β2); [ exact Hβ2 | exact D2p ] | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      simpl in Ha. split; [ clear - Ha; fsetdec | clear - Hb; fsetdec ]. }
    split.
    { assert (Hβx : β `notin` cols_l ρx).
      { intros Hin. destruct (cols_l_in_inv _ _ Hin) as [b Hin'].
        destruct (Hρx _ _ Hin') as [Ha _]. simpl in Ha. clear - Ha. fsetdec. }
      simpl. rewrite ftvar_in_pskl_close_pskl_wrt_pskl.
      clear - Htr Hβx. fsetdec. }
    constructor.
    rewrite <- app_assoc in Hrel'.
    eapply rel_pskl_close_pair_restrict.
    + exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + rewrite cols_l_app. simpl in Hd1p.
      clear - Hd1p Hdfl Hβcl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + rewrite cols_r_app. clear - Hd2p Hdfr Hβ2cr. fsetdec.
    + in_incl.
    + in_incl.
  - (* SS-UnivGhostL: the subject strips its ⫯; the yield re-wraps *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa |- _ =>
        rename Ha into HrP0; rename xa into P3b
    end.
    assert (Hcov' : ftvar_in_pskl P3b ∪ ftvar_in_pskl Q3 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    destruct (IHHD S0 Θ2 P3b Q3 ρ V HrP0 HrelQ Hagr Hscp1 Hblk HdΘ Hscp2 Hcov')
      as (S1 & ρx & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hρx & Htr & Hrel').
    exists S1, ρx, ρn, Ξ2, (pskl_univ_ghost Y2).
    split; [ apply e_solve_sub__univ_ghost_l; exact D2p | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    split; [ exact Hρx | ].
    split; [ simpl; exact Htr | ].
    constructor. exact Hrel'.
  - (* SS-Vacuous *)
    inversion HrelQ; subst.
    exists S0, nil, nil, nil, P3.
    split;
      [ apply e_solve_sub__vacuous;
        eapply rel_pskl_peel_l_off; [ exact HrelP | assumption ] | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. exact HrelP.
  - (* SS-Check: drops into §5 *)
    match goal with
    | He : a_solve_eq _ _ _ _ _ |- _ => rename He into HDeq0
    end.
    destruct (a_solve_eq_rel_e HDeq0 HrelP HrelQ Hagr Hscp1 Hblk HdΘ Hscp2 Hcov)
      as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
    exists S1, nil, ρn, Ξ2, Y2.
    split.
    { apply e_solve_sub__check.
      - eapply rel_pskl_ghost_free; [ exact HrelQ | assumption ].
      - eapply rel_pskl_guarded; [ exact HrelP | assumption ].
      - eapply rel_pskl_guarded; [ exact HrelQ | assumption ].
      - exact D2p. }
    split; [ exact E1 | split; [ exact E2 | ] ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. exact Hrel'.
  - (* ⭐ SS-ForallR: the TARGET opens and the pair LEAKS into ρx *)
    inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V B ?xa |- _ =>
        rename Ha into HrB0; rename xa into B3
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh S0) as [β2 Hβ2].
    assert (HupB : ftvar_in_pskl (open_pskl_wrt_pskl B3 (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl B3)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl P3
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl B3 (pskl_var_f β2))
                      [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupB; fsetdec).
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ HD)).
    assert (HβΘ : β `notin` ftvar_in_aenv Θ)
      by (clear - Hβ1; fsetdec).
    destruct (solve_lift_open_context Hagr Hscp1 HdΘ Hscp2 Hblk Hd1p HβΘ Hβ2)
      as (Hagr' & Hscp1' & HdΘ' & Hscp2' & Hblk').
    assert (HrelPr : rel_pskl (restrict_pairs β β2 ρ) V P P3)
      by (apply rel_pskl_restrict;
          [ exact HrelP | clear - Hβ1; fsetdec
          | clear - Hβ2 Hcov; simpl in Hcov; fsetdec ]).
    assert (HrB0r : rel_pskl (restrict_pairs β β2 ρ) V B B3)
      by (apply rel_pskl_restrict;
          [ exact HrB0 | clear - Hβ1; fsetdec
          | clear - Hβ2 Hcov; simpl in Hcov; fsetdec ]).
    destruct (IHHD (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                P3 (open_pskl_wrt_pskl B3 (pskl_var_f β2))
                ((β, β2) :: restrict_pairs β β2 ρ) V
                ltac:(apply rel_pskl_extend_pair; exact HrelPr)
                ltac:(apply rel_pskl_open_pair; exact HrB0r)
                Hagr' Hscp1' Hblk' HdΘ' Hscp2' Hcov')
      as (S1 & ρx & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hρx & Htr & Hrel').
    (* ⭐⭐ THE TRIM (2026-08-21, §8c.41).  The rule PERMITS β to escape into
       [P'] and does NOT force it — see its own comment.  A pair whose atom
       is nowhere in the output would break [cols_l ρx ⊆ ftvar_in_pskl P1'],
       which is what keeps the extract rung's FINAL GUESS off the ρx column.
       ⇒ carry the leaked pair only when it is USED. *)
    assert (Hbase : forall a b, In (a, b) ρx ->
              a `notin` ftvar_in_aenv Θ ∪ dom Ξ /\ b `notin` S0).
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb]. simpl in Ha.
      split; [ clear - Ha; fsetdec | clear - Hb; fsetdec ]. }
    assert (Htrim : exists ρxN,
              (forall a b, In (a, b) ρxN ->
                 a `notin` ftvar_in_aenv Θ ∪ dom Ξ /\ b `notin` S0)
              /\ cols_l ρxN [<=] ftvar_in_pskl P'
              /\ rel_pskl (ρxN ++ ρn ++ ρ) V P' Y2).
    { destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P'))
        as [Hβin | Hβni].
      - exists (ρx ++ (β, β2) :: nil). split; [ | split ].
        + intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
          * exact (Hbase a b Hin).
          * destruct Hin as [E | Hin]; [ inversion E; subst | inversion Hin ].
            simpl in Hd1p.
            split; [ clear - Hβ1 Hd1p; fsetdec | exact Hβ2 ].
        + rewrite cols_l_app. simpl. clear - Htr Hβin. fsetdec.
        + (* ⚙ the restriction is UNDONE here: the leaked pair moves into ρx
             and the deleted pairs go back into ρ. *)
          eapply rel_pskl_mono; [ exact Hrel' | | intros x0 Hx0; exact Hx0 ].
          intros a0 b0 Hin0. apply in_app_or in Hin0. apply in_or_app.
          destruct Hin0 as [Hin0 | Hin0].
          { left. apply in_or_app. left. exact Hin0. }
          apply in_app_or in Hin0. destruct Hin0 as [Hin0 | Hin0].
          { right. apply in_or_app. left. exact Hin0. }
          destruct Hin0 as [E0 | Hin0].
          { left. apply in_or_app. right. left. exact E0. }
          right. apply in_or_app. right. eapply restrict_pairs_incl; exact Hin0.
      - exists ρx. split; [ exact Hbase | split; [ exact Htr | ] ].
        eapply rel_pskl_morph_ftv; [ exact Hrel' | | ].
        + intros a0 b0 Ha0 Hin0. apply rel_atom__pair.
          apply in_app_or in Hin0. apply in_or_app.
          destruct Hin0 as [Hin0 | Hin0].
          { left. exact Hin0. }
          apply in_app_or in Hin0. destruct Hin0 as [Hin0 | Hin0].
          { right. apply in_or_app. left. exact Hin0. }
          destruct Hin0 as [E0 | Hin0].
          { exfalso. inversion E0; subst. apply Hβni. exact Ha0. }
          right. apply in_or_app. right. eapply restrict_pairs_incl; exact Hin0.
        + intros a0 Ha0 Hv0. apply rel_atom__id. exact Hv0. }
    destruct Htrim as (ρxN & HρxN & HtrN & HrelN).
    exists S1, ρxN, ρn, Ξ2, Y2.
    split.
    { apply e_solve_sub__forall_r with (β := β2).
      - eapply rel_pskl_ghost_free; [ exact HrelQ | assumption ].
      - eapply rel_pskl_solve_l_off; [ exact HrelP | assumption ].
      - exact Hβ2.
      - exact D2p. }
    split; [ exact E1 | split; [ exact E2 | ] ].
    exact (conj HρxN (conj HtrN HrelN)).
  - (* ⭐ SS-Arrow: §5's eq half feeds the threaded sub half *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P1 ?xa, Hb : rel_pskl ρ V P2 ?xb,
      Hc : rel_pskl ρ V Q1 ?xc, Hd : rel_pskl ρ V Q2 ?xd |- _ =>
        rename Ha into HrPa; rename Hb into HrPb;
        rename Hc into HrQa; rename Hd into HrQb;
        rename xa into P3a; rename xb into P3b;
        rename xc into Q3a; rename xd into Q3b
    end.
    match goal with
    | He : a_solve_eq Θ P1 Q1 ?x ?y |- _ => rename He into HDeq
    end.
    assert (HcovA : ftvar_in_pskl P3a ∪ ftvar_in_pskl Q3a [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    assert (Hblk1 : dom Ξ1 ∩ cols_l ρ [=] empty)
      by (rewrite dom_app in Hblk; clear - Hblk; fsetdec).
    destruct (a_solve_eq_rel_e HDeq HrPa HrQa Hagr Hscp1 Hblk1
                HdΘ Hscp2 HcovA)
      as (S1 & ρnA & Ξ2a & P2a' & D2a & E1a & E2a & HrelA').
    pose proof (e_solve_eq_supply_grows D2a) as Hgr1.
    assert (Hd1a : dom Ξ1 ∩ ftvar_in_aenv Θ [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HDeq)).
    assert (Hd2a : dom Ξ2a ∩ S0 [=] empty)
      by (apply (proj2 e_solve_sub_eq_block) in D2a; tauto).
    assert (Hi2a : dom Ξ2a [<=] S1) by (exact (e_solve_eq_block_in_supply D2a)).
    pose proof (dom_flex_pairs_l ρnA) as Hdfl. rewrite <- E1a in Hdfl.
    pose proof (dom_flex_pairs_r ρnA) as Hdfr. rewrite <- E2a in Hdfr.
    assert (Hagr' : flex_agree_rel (ρnA ++ ρ) V (Ξ1 ++ Θ) (Ξ2a ++ Θ2)).
    { rewrite E1a, E2a. apply flex_agree_rel_push_pairs.
      - exact Hagr.
      (* ⭐ the head block dodges the pair columns — the SECOND half of the
         old scoping premise, now hypothesised directly. *)
      - clear - Hd1a Hscp1 Hdfl Hblk1. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V [<=] ftvar_in_aenv (Ξ1 ++ Θ))
      by (rewrite ftvar_in_aenv_app; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom (Ξ2a ++ Θ2) [<=] S1)
      by (rewrite dom_app; clear - Hi2a HdΘ Hgr1; fsetdec).
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hscp2 Hdfr Hi2a Hgr1. fsetdec. }
    assert (HcovB : ftvar_in_pskl P3b ∪ ftvar_in_pskl Q3b [<=] S1)
      by (clear - Hcov Hgr1; simpl in *; fsetdec).
    assert (Hd1b : dom Ξ2 ∩ ftvar_in_aenv (Ξ1 ++ Θ) [=] empty)
      by (exact ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ HD)).
    assert (Hblk2 : dom Ξ2 ∩ cols_l (ρnA ++ ρ) [=] empty).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app in Hd1b.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      rewrite dom_app in Hblk.
      clear - Hd1b Hds Hdfl Hblk. fsetdec. }
    destruct (IHHD S1 (Ξ2a ++ Θ2) P3b Q3b (ρnA ++ ρ) V
                ltac:(apply rel_pskl_widen; exact HrPb)
                ltac:(apply rel_pskl_widen; exact HrQb)
                Hagr' Hscp1' Hblk2 HdΘ' Hscp2' HcovB)
      as (S2 & ρx & ρnB & Ξ2b & P2b' & D2b & E1b & E2b & Hρx & Htr & HrelB').
    exists S2, ρx, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a), (pskl_arrow P2a' P2b').
    split; [ eapply e_solve_sub__arrow; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      rewrite ftvar_in_aenv_app in Ha. rewrite dom_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds1.
      split; [ clear - Ha Hds1; fsetdec | clear - Hb Hgr1; fsetdec ]. }
    split; [ simpl; clear - Htr; fsetdec | ].
    constructor.
    + rel_perm HrelA'.
    + rel_perm HrelB'.
  - (* SS-GhostLF: a ghost subject against an arrow target *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Hc : rel_pskl ρ V Q1 ?xc, Hd : rel_pskl ρ V Q2 ?xd |- _ =>
        rename Hc into HrQa; rename Hd into HrQb;
        rename xc into Q3a; rename xd into Q3b
    end.
    match goal with
    | He : a_solve_eq Θ pskl_ghost Q1 ?x ?y |- _ => rename He into HDeq
    end.
    assert (HcovA : ftvar_in_pskl pskl_ghost ∪ ftvar_in_pskl Q3a [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    assert (Hblk1 : dom Ξ1 ∩ cols_l ρ [=] empty)
      by (rewrite dom_app in Hblk; clear - Hblk; fsetdec).
    destruct (a_solve_eq_rel_e HDeq (rel_pskl__ghost ρ V) HrQa Hagr Hscp1
                Hblk1 HdΘ Hscp2 HcovA)
      as (S1 & ρnA & Ξ2a & P2a' & D2a & E1a & E2a & HrelA').
    pose proof (e_solve_eq_supply_grows D2a) as Hgr1.
    assert (Hd1a : dom Ξ1 ∩ ftvar_in_aenv Θ [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HDeq)).
    assert (Hd2a : dom Ξ2a ∩ S0 [=] empty)
      by (apply (proj2 e_solve_sub_eq_block) in D2a; tauto).
    assert (Hi2a : dom Ξ2a [<=] S1) by (exact (e_solve_eq_block_in_supply D2a)).
    pose proof (dom_flex_pairs_l ρnA) as Hdfl. rewrite <- E1a in Hdfl.
    pose proof (dom_flex_pairs_r ρnA) as Hdfr. rewrite <- E2a in Hdfr.
    assert (Hagr' : flex_agree_rel (ρnA ++ ρ) V (Ξ1 ++ Θ) (Ξ2a ++ Θ2)).
    { rewrite E1a, E2a. apply flex_agree_rel_push_pairs.
      - exact Hagr.
      (* ⭐ the head block dodges the pair columns — the SECOND half of the
         old scoping premise, now hypothesised directly. *)
      - clear - Hd1a Hscp1 Hdfl Hblk1. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V [<=] ftvar_in_aenv (Ξ1 ++ Θ))
      by (rewrite ftvar_in_aenv_app; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom (Ξ2a ++ Θ2) [<=] S1)
      by (rewrite dom_app; clear - Hi2a HdΘ Hgr1; fsetdec).
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hscp2 Hdfr Hi2a Hgr1. fsetdec. }
    assert (HcovB : ftvar_in_pskl pskl_ghost ∪ ftvar_in_pskl Q3b [<=] S1)
      by (clear - Hcov Hgr1; simpl in *; fsetdec).
    assert (Hd1b : dom Ξ2 ∩ ftvar_in_aenv (Ξ1 ++ Θ) [=] empty)
      by (exact ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ HD)).
    assert (Hblk2 : dom Ξ2 ∩ cols_l (ρnA ++ ρ) [=] empty).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app in Hd1b.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      rewrite dom_app in Hblk.
      clear - Hd1b Hds Hdfl Hblk. fsetdec. }
    destruct (IHHD S1 (Ξ2a ++ Θ2) pskl_ghost Q3b (ρnA ++ ρ) V
                (rel_pskl__ghost (ρnA ++ ρ) V)
                ltac:(apply rel_pskl_widen; exact HrQb)
                Hagr' Hscp1' Hblk2 HdΘ' Hscp2' HcovB)
      as (S2 & ρx & ρnB & Ξ2b & P2b' & D2b & E1b & E2b & Hρx & Htr & HrelB').
    exists S2, ρx, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a),
      (pskl_univ_ghost (pskl_arrow P2a' P2b')).
    split; [ eapply e_solve_sub__ghost_l_fn; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      rewrite ftvar_in_aenv_app in Ha. rewrite dom_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds1.
      split; [ clear - Ha Hds1; fsetdec | clear - Hb Hgr1; fsetdec ]. }
    split; [ simpl; clear - Htr; fsetdec | ].
    constructor. constructor.
    + rel_perm HrelA'.
    + rel_perm HrelB'.
  - (* SS-GhostL: no premise; the target passes as the pattern *)
    inversion HrelP; subst.
    exists S0, nil, nil, nil, (pskl_univ_ghost Q3).
    split.
    { apply e_solve_sub__ghost_l.
      - eapply rel_pskl_ghost_free; [ exact HrelQ | assumption ].
      - eapply rel_pskl_guarded; [ exact HrelQ | assumption ]. }
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor. exact HrelQ.
Qed.

(* ===================================================================== *)
(*  §7  ⭐ THE CONSTRAINT FOLD LIFTS — three rows                          *)
(*                                                                        *)
(*  The constraint fold's transport, side 2 moved to [e_solve_cstr].      *)
(*  ⚙ The eq-cons row is the only one with work: the head *)
(*  goes through §5 and the TAIL runs at the head's OUTPUT supply, so its  *)
(*  coverage needs [e_solve_eq_out_ftvar] — what the solved pattern can mention —  *)
(*  which is exactly the fact prop_solve.v §2 says it exists    *)
(*  for.                                                                   *)
(* ===================================================================== *)

Lemma a_solve_cstr_rel_e : forall Θ1 C1 P1 Ξ1 P1',
  {{ Θ1 ⊩ C1 ⨾ P1 ⤳ Ξ1 ⨾ P1' }}a ->
  forall S0 Θ2 C2 P3 ρ V,
  rel_pskl ρ V P1 P3 ->
  rel_a_cstrs ρ V C1 C2 ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  (* ⭐⭐ THE SCOPING PREMISE SPLIT IN TWO (2026-08-19).  The old single
     [V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1] is UNSATISFIABLE at [a_extract]:
     there ρ carries the COLLECTION's leaked openers, which are bound
     nowhere.  Its two jobs separate cleanly —
     - the ∀ rows wanted [β ∉ V ∪ cols_l ρ]; [V] still comes from the
       context and [cols_l ρ] is now paid by the PAIR RESTRICTION
       (prop_solve_rel.v §6), which deletes the offending pairs instead;
     - the ARROW rows wanted the newly generated block to dodge the pair
       columns, and that is the SECOND premise below — a statement about
       the derivation's OWN output block, which every consumer can see. *)
  V [<=] ftvar_in_aenv Θ1 ->
  dom Ξ1 ∩ cols_l ρ [=] empty ->
  dom Θ2 [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P3 ∪ ftvar_in_a_cstrs C2 [<=] S0 ->
  exists S1 ρx ρn Ξ2 P3',
    {{ S0 ↝ S1 ⊨ Θ2 ⊩ C2 ⨾ P3 ⤳ Ξ2 ⨾ P3' }}e
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    (* ⭐ the block conjunct of §8c.41 — see [a_solve_sub_rel_e] *)
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 ∪ dom Ξ1 /\ b `notin` S0)
    (* ⭐ AND THE LEFT COLUMN LIVES IN THE OUTPUT (2026-08-21, §8c.41): the
       ∀ rows carry a leaked pair only when the opener actually ESCAPES.
       This is what keeps the extract rung's FINAL GUESS off the ρx column —
       that guess avoids [ftvar_in_pskl Q], hence everything ρx names. *)
    /\ cols_l ρx [<=] ftvar_in_pskl P1'
    /\ rel_pskl (ρx ++ ρn ++ ρ) V P1' P3'.
Proof.
  intros Θ1 C1 P1 Ξ1 P1' HD.
  induction HD;
    intros S0 Θ2 C3 P3 ρ V HrelP HrelC Hagr Hscp1 Hblk HdΘ Hscp2 Hcov.
  - (* SC-Empty *)
    inversion HrelC; subst.
    exists S0, nil, nil, nil, P3.
    split; [ apply e_solve_cstr__empty | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. exact HrelP.
  - (* SC-Sub: the terminal singleton, §6 *)
    inversion HrelC; subst.
    match goal with
    | Hc : rel_a_cstr ρ V (a_cstr_sub m Q) ?y,
      Ht : Forall2 _ nil ?l |- _ =>
        inversion Hc; subst; inversion Ht; subst
    end.
    match goal with
    | Hq : rel_pskl ρ V Q ?x |- _ => rename Hq into HrelQ; rename x into Q2c
    end.
    match goal with
    | Hs : a_solve_sub _ _ _ _ _ _ |- _ => rename Hs into HDsub
    end.
    assert (HcovS : ftvar_in_pskl P3 ∪ ftvar_in_pskl Q2c [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    destruct (a_solve_sub_rel_e HDsub HrelP HrelQ Hagr Hscp1 Hblk HdΘ Hscp2 HcovS)
      as (S1 & ρx & ρn & Ξ2 & Y2 & D2s & E1 & E2 & Hρx & Htr & Hrel').
    exists S1, ρx, ρn, Ξ2, Y2.
    split; [ apply e_solve_cstr__sub; exact D2s | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    split; [ exact Hρx | split; [ exact Htr | exact Hrel' ] ].
  - (* ⭐ SC-Eq: head via §5, tail via the IH at the head's OUTPUT supply *)
    inversion HrelC; subst.
    match goal with
    | Hc : rel_a_cstr ρ V (a_cstr_eq Q) ?y |- _ => inversion Hc; subst
    end.
    match goal with
    | Hq : rel_pskl ρ V Q ?x, Ht : Forall2 _ C ?l |- _ =>
        rename Hq into HrelQ; rename x into Q2c;
        rename Ht into HrelC'; rename l into C2'
    end.
    match goal with
    | He : a_solve_eq _ _ _ _ _ |- _ => rename He into HDeq
    end.
    assert (HcovH : ftvar_in_pskl P3 ∪ ftvar_in_pskl Q2c [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    assert (Hblk1 : dom Ξ1 ∩ cols_l ρ [=] empty)
      by (rewrite dom_app in Hblk; clear - Hblk; fsetdec).
    destruct (a_solve_eq_rel_e HDeq HrelP HrelQ Hagr Hscp1 Hblk1
                HdΘ Hscp2 HcovH)
      as (S1 & ρnA & Ξ2a & Pmid2 & D2a & E1a & E2a & HrelM).
    pose proof (e_solve_eq_supply_grows D2a) as Hgr1.
    pose proof (e_solve_eq_out_ftvar D2a HcovH) as Hout.
    assert (Hd1a : dom Ξ1 ∩ ftvar_in_aenv Θ [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HDeq)).
    assert (Hd2a : dom Ξ2a ∩ S0 [=] empty)
      by (apply (proj2 e_solve_sub_eq_block) in D2a; tauto).
    assert (Hi2a : dom Ξ2a [<=] S1) by (exact (e_solve_eq_block_in_supply D2a)).
    pose proof (dom_flex_pairs_l ρnA) as Hdfl. rewrite <- E1a in Hdfl.
    pose proof (dom_flex_pairs_r ρnA) as Hdfr. rewrite <- E2a in Hdfr.
    assert (Hagr' : flex_agree_rel (ρnA ++ ρ) V (Ξ1 ++ Θ) (Ξ2a ++ Θ2)).
    { rewrite E1a, E2a. apply flex_agree_rel_push_pairs.
      - exact Hagr.
      (* ⭐ the head block dodges the pair columns — the SECOND half of the
         old scoping premise, now hypothesised directly. *)
      - clear - Hd1a Hscp1 Hdfl Hblk1. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V [<=] ftvar_in_aenv (Ξ1 ++ Θ))
      by (rewrite ftvar_in_aenv_app; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom (Ξ2a ++ Θ2) [<=] S1)
      by (rewrite dom_app; clear - Hi2a HdΘ Hgr1; fsetdec).
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hscp2 Hdfr Hi2a Hgr1. fsetdec. }
    assert (HcovT : ftvar_in_pskl Pmid2 ∪ ftvar_in_a_cstrs C2' [<=] S1)
      by (clear - Hout Hcov Hgr1; simpl in *; fsetdec).
    assert (Hd1b : dom Ξ2 ∩ ftvar_in_aenv (Ξ1 ++ Θ) [=] empty)
      by (exact (a_solve_cstr_generated_fresh_set HD)).
    assert (Hblk2 : dom Ξ2 ∩ cols_l (ρnA ++ ρ) [=] empty).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app in Hd1b.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      rewrite dom_app in Hblk.
      clear - Hd1b Hds Hdfl Hblk. fsetdec. }
    destruct (IHHD S1 (Ξ2a ++ Θ2) C2' Pmid2 (ρnA ++ ρ) V
                HrelM
                ltac:(apply rel_a_cstrs_widen; exact HrelC')
                Hagr' Hscp1' Hblk2 HdΘ' Hscp2' HcovT)
      as (S2 & ρx & ρnB & Ξ2b & P3' & D2b & E1b & E2b & Hρx & Htr & HrelB').
    exists S2, ρx, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a), P3'.
    split; [ eapply e_solve_cstr__eq; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      rewrite ftvar_in_aenv_app in Ha. rewrite dom_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds1.
      split; [ clear - Ha Hds1; fsetdec | clear - Hb Hgr1; fsetdec ]. }
    split; [ exact Htr | ].
    rel_perm HrelB'.
Qed.

(* ===================================================================== *)
(*  §8  ⭐⭐ THE EXTRACT ROW — look, fold, guess, COMPOSED                  *)
(*                                                                        *)
(*  [a_extract] has ONE rule and it is §3 → §7 → §4.  What makes the       *)
(*  composition go through are the rule's two cross-layer freshness       *)
(*  guards ([a_extract__solve], [paper-gap], algo/def_rules.v):            *)
(*                                                                        *)
(*      ftvar_in_a_cstrs 𝒞 ∩ dom Ξs [=] empty                             *)
(*      (ftvar_in_a_cstrs 𝒞 ∪ ftvar_in_pskl Q) ∩ dom Ξ' [=] empty           *)
(*                                                                        *)
(*  ⛔ WHY THEY ARE OWED.  The collection LEAKS openers into [𝒞] (all five *)
(*  ∀ rows do), and those openers are bound NOWHERE — not in [Θ0], not in  *)
(*  [Ξ].  The fold runs at [Ξ ++ Θ0] and [SE-FlexR]'s guess draws its     *)
(*  flexibles fresh for [ftvar_in_aenv (Ξ ++ Θ0)] ONLY, so without the    *)
(*  guard it may draw a leaked opener.  Side 1 then reads that atom as    *)
(*  FLEXIBLE (it is in [Ξs]) where side 2 reads its counterpart as a rigid *)
(*  free atom — no [flex_agree_rel] between the two contexts exists, which *)
(*  is precisely §7's premise.  The same leak between the two halves of   *)
(*  [LE-Arrow] is what the collection's cross-half guard rules out; it is *)
(*  machine-checked in cex/probe_extract_conflated_opener.v.              *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §8b  ⭐⭐ THE IDENTITY-PAIR SHIFT — one atom, between [V] and ρ        *)
(*                                                                        *)
(*  [rel_atom] is a plain disjunction of a PAIR clause and an IDENTITY    *)
(*  clause, so for an atom already related to ITSELF the two clauses       *)
(*  two carry the same information: [(α, α) ∈ ρ] and [α `in` V] relate     *)
(*  exactly the same atoms.                                               *)
(*                                                                        *)
(*  ⭐ That is what lets [a_extract_rel_e] accept a looked-for variable    *)
(*  its own context does NOT bind — [a_sub__forall_l]'s opener, which is   *)
(*  fresh for [Θ0] by the rule's own side condition.  The LOOK needs α in  *)
(*  [V] and outside both columns (it dispatches on α's ABSENCE from a      *)
(*  skeleton, [rel_pskl_notin_r]); the FOLD and the GUESS carry the        *)
(*  scoping premise [V ⊆ ftvar_in_aenv Θ], which the opener escapes.       *)
(*  ⇒ shift α from [V] to the pair list BETWEEN the two layers; neither    *)
(*  layer changes.                                                        *)
(* ===================================================================== *)

(** The universal morphism: [rel_pskl_mono] is its pair-inclusion instance,
    and the shift in EITHER direction is another. *)
Lemma rel_pskl_morph : forall ρ ρ' V V' P Q,
  rel_pskl ρ V P Q ->
  (forall a b, In (a, b) ρ -> rel_atom ρ' V' a b) ->
  (forall a, a `in` V -> rel_atom ρ' V' a a) ->
  rel_pskl ρ' V' P Q.
Proof.
  intros ρ ρ' V V' P Q Hrel Hp Hv.
  induction Hrel; constructor; auto.
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ =>
      inversion Ha; subst; [ apply Hp | apply Hv ]; assumption
  end.
Qed.

Lemma rel_a_cstrs_morph : forall ρ ρ' V V' C1 C2,
  rel_a_cstrs ρ V C1 C2 ->
  (forall a b, In (a, b) ρ -> rel_atom ρ' V' a b) ->
  (forall a, a `in` V -> rel_atom ρ' V' a a) ->
  rel_a_cstrs ρ' V' C1 C2.
Proof.
  intros ρ ρ' V V' C1 C2 Hrel Hp Hv.
  induction Hrel as [ | c1 c2 C1' C2' Hc Hrel' IH ].
  - constructor.
  - constructor; [ | exact IH ].
    inversion Hc; subst; constructor;
      (eapply rel_pskl_morph; [ eassumption | exact Hp | exact Hv ]).
Qed.

(** ⚙ [flex_agree_rel] is INVARIANT under the shift — the two clauses relate
    the same atoms — so only the direction the extract spends is stated. *)
Lemma flex_agree_rel_id_to_pair : forall ρ V VS α Θ1 Θ2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  α `in` V ->
  VS [<=] V ->
  flex_agree_rel ((α, α) :: ρ) VS Θ1 Θ2.
Proof.
  intros ρ V VS α Θ1 Θ2 [HagV Hagp] HαV Hsub. split.
  - intros x Hx. apply HagV. clear - Hx Hsub. fsetdec.
  - intros a b Hin. destruct Hin as [E | Hin].
    + inversion E; subst. apply HagV. exact HαV.
    + apply Hagp. exact Hin.
Qed.


Lemma a_extract_rel_e : forall Θ1 NM α m P1 P1' Ξ1 Q1',
  {{ Θ1 ⊢ P1 ⊳[ NM , α , m ] P1' ⤳ Ξ1 ↪ Q1' }}a ->
  forall S0 Θ2 P2 P2' ρ V,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V P1' P2' ->
  α `in` V ->
  α `notin` cols_l ρ ->
  α `notin` cols_r ρ ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  (* ⭐⭐ THE SCOPING PREMISE SPLIT IN THREE, AND WEAKENED BY EXACTLY ONE
     ATOM (2026-08-21, §8c.41).  The old single
     [V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1] is UNSATISFIABLE BY THIS LEMMA'S
     ONLY CONSUMER: [a_sub__forall_l] picks its opener OFF
     [ftvar_in_aenv Θ0] (algo/def_rules.v), and that opener is the [α]
     here — so [α `in` V] and the old bound cannot both hold.  ⇒ the same
     split the fold took on 2026-08-19, one layer up:

     - [V] is still bounded by the CONTEXT, plus the looked-for variable —
       the one atom an exists-fresh binder row hands down.  §8b shifts it
       out of [V] again before the fold and the guess, whose own scoping
       premise the opener escapes;
     - the two jobs [cols_l ρ] had were both "the derivation's OWN output
       block dodges the pair column", which is a statement every consumer
       can see — and [a_sub__forall_l]'s consumer reads it off the lift
       motive's block premise, since [dom Ξ1 ⊆ dom Θ1 \ dom Θ0]. *)
  V [<=] add α (ftvar_in_aenv Θ1) ->
  dom Ξ1 ∩ cols_l ρ [=] empty ->
  α `notin` dom Ξ1 ->
  dom Θ2 [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] S0 ->
  exists S1 ρx ρn Ξ2 Q2',
    {{ S0 ↝ S1 ⊨ Θ2 ⊢ P2 ⊳[ NM , α , m ] P2' ⤳ Ξ2 ↪ Q2' }}e
    /\ Ξ1 = flex_pairs_l ρn
    /\ Ξ2 = flex_pairs_r ρn
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 /\ b `notin` S0)
    (* ⭐⭐ AND THE LEFT COLUMN DODGES THE WHOLE OUTPUT BLOCK (§8c.41).
       This is what [a_sub__forall_l] needs to DROP the ρx column at the
       atoms of a skeleton wf over [Ξ1 ++ Θ1]: a leaked opener is bound
       nowhere, so the motive's block premise cannot keep it out of
       [dom Θ1] and [rel_aenv] would owe a binding for each. *)
    /\ cols_l ρx ∩ dom Ξ1 [=] empty
    /\ rel_pskl (ρx ++ ρn ++ ρ) V Q1' Q2'.
Proof.
  intros ? ? ? ? ? ? ? ? HD.
  (* [a_extract] has one rule: look, fold, guess, and the rule's two guards *)
  destruct HD as
    [ Θ1 NM α m P1 P1' Ξ1L Ξ1F Ξ1G C1 Q1 Q1' HL HF HG Hguard Hguard2 ].
  intros S0 Θ2 P2 P2' ρ V HrP HrP' HαV Hαl Hαr Hagr Hscp1 Hblkρ HαΞ
    HdΘ Hscp2 Hcov.
  rewrite ! dom_app in Hblkρ, HαΞ.
  assert (HblkL : dom Ξ1L ∩ cols_l ρ [=] empty) by (clear - Hblkρ; fsetdec).
  assert (HblkF0 : dom Ξ1F ∩ cols_l ρ [=] empty) by (clear - Hblkρ; fsetdec).
  assert (HαF : α `notin` dom Ξ1F) by (clear - HαΞ; fsetdec).
  assert (HαS0 : α `in` S0) by (clear - HαV Hscp2; fsetdec).

  (* ---- STEP 1: the collection, transport 5 (prop_lift_context.v §7) ---- *)
  assert (HcovL : V ∪ cols_r ρ ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] S0)
    by (clear - Hscp2 Hcov; fsetdec).
  pose proof (proj1 a_looksub_lookeq_rel_e) as HTL.
  destruct (HTL _ _ _ _ _ _ _ HL S0 Θ2 P2 P2' ρ V
              HrP HrP' HαV Hαl Hαr Hagr HcovL)
    as (S1 & ρxL & ρnL & Ξ2L & C2 & DL & E1L & E2L
        & HρL & HxrL & HxaL & HxlL & HrC).
  pose proof (e_looksub_supply_grows DL) as HgL.
  pose proof (e_looksub_generated_in_supply DL) as HiL.
  pose proof (dom_flex_pairs_l ρnL) as HdflL. rewrite <- E1L in HdflL.
  pose proof (dom_flex_pairs_r ρnL) as HdfrL. rewrite <- E2L in HdfrL.

  (* the two columns of ρnL are the two blocks, and both are apart from
     everything the caller knows.  ⚙ On the left the look's OWN spec already
     excludes the looked-for variable ([a ∉ add α (ftvar_in_aenv Θ1)]), so
     the weakened [V] bound costs nothing here. *)
  assert (HnLl : cols_l ρnL ∩ (V ∪ cols_l ρ) [=] empty).
  { assert (Hd : cols_l ρnL ∩ add α (ftvar_in_aenv Θ1) [=] empty).
    { intros x. split; intros Hx; [ | clear - Hx; fsetdec ].
      exfalso.
      assert (Hxl : x `in` cols_l ρnL) by (clear - Hx; fsetdec).
      destruct (cols_l_in_inv _ _ Hxl) as [b Hin].
      assert (Hin' : In (x, b) (ρxL ++ ρnL))
        by (apply in_or_app; right; exact Hin).
      destruct (HρL _ _ Hin') as [Ha _]. clear - Ha Hx. fsetdec. }
    assert (HdV : cols_l ρnL ∩ V [=] empty) by (clear - Hd Hscp1; fsetdec).
    assert (Hdρ : cols_l ρnL ∩ cols_l ρ [=] empty)
      by (clear - HblkL HdflL; fsetdec).
    clear - HdV Hdρ. fsetdec. }
  assert (HnLr : cols_r ρnL ∩ (V ∪ cols_r ρ) [=] empty).
  { assert (Hd : cols_r ρnL ∩ S0 [=] empty).
    { intros x. split; intros Hx; [ | clear - Hx; fsetdec ].
      exfalso.
      assert (Hxr : x `in` cols_r ρnL) by (clear - Hx; fsetdec).
      destruct (cols_r_in_inv _ _ Hxr) as [a Hin].
      assert (Hin' : In (a, x) (ρxL ++ ρnL))
        by (apply in_or_app; right; exact Hin).
      destruct (HρL _ _ Hin') as [_ [_ Hb]]. clear - Hb Hx. fsetdec. }
    clear - Hd Hscp2. fsetdec. }

  (* ---- STEP 2: the fold, §7, at the two extended contexts ---- *)
  assert (HagrN : flex_agree_rel (ρnL ++ ρ) V (Ξ1L ++ Θ1) (Ξ2L ++ Θ2)).
  { rewrite E1L, E2L. apply flex_agree_rel_push_pairs;
      [ exact Hagr | exact HnLl | exact HnLr ]. }
  assert (HagrF : flex_agree_rel (ρxL ++ ρnL ++ ρ) V (Ξ1L ++ Θ1) (Ξ2L ++ Θ2)).
  { apply flex_agree_rel_extend_nonflex; [ exact HagrN | ].
    intros a b Hin.
    assert (Hin' : In (a, b) (ρxL ++ ρnL))
      by (apply in_or_app; left; exact Hin).
    destruct (HρL _ _ Hin') as [Ha [_ Hb]].
    assert (Hal : a `in` cols_l ρxL) by (eapply cols_l_in; exact Hin).
    assert (Har : b `in` cols_r ρxL) by (eapply cols_r_in; exact Hin).
    pose proof (dom_subset_ftvar_in_aenv Θ1) as Hd1.
    split; intros Hfl; apply a_flex_tvar_in_dom in Hfl;
      rewrite dom_app in Hfl.
    - clear - Hfl Ha Hal HxlL Hd1. fsetdec.
    - clear - Hfl Hb Har HxrL HdΘ. fsetdec. }

  (* ---- ⭐⭐ THE IDENTITY-PAIR SHIFT (§8b) ----------------------------
     [α] leaves [V] and becomes the pair [(α, α)].  Below this line the
     identity support is [V ∩ ftvar_in_aenv Θ1], which the fold's and the
     guess's context-shaped scoping premises accept, and every fact about
     the looked-for variable travels as a pair instead. *)
  assert (HVSsub : V ∩ ftvar_in_aenv Θ1 [<=] V) by (clear; fsetdec).
  assert (HVSadd : V [<=] add α (V ∩ ftvar_in_aenv Θ1))
    by (clear - Hscp1; fsetdec).
  assert (HαS1 : α `in` S1) by (clear - HαS0 HgL; fsetdec).

  assert (Hscp1F : V ∩ ftvar_in_aenv Θ1 [<=] ftvar_in_aenv (Ξ1L ++ Θ1))
    by (rewrite ftvar_in_aenv_app; clear; fsetdec).
  pose proof (a_solve_cstr_generated_fresh_set HF) as HgfF.
  rewrite ftvar_in_aenv_app in HgfF.
  assert (HxsubL : cols_l ρxL [<=] ftvar_in_a_cstrs C1).
  { intros x Hx. destruct (cols_l_in_inv _ _ Hx) as [b Hin].
    exact (HxaL _ _ Hin). }
  assert (HbFx : dom Ξ1F ∩ cols_l ρxL [=] empty)
    by (clear - Hguard HxsubL; fsetdec).
  assert (HbFn : dom Ξ1F ∩ cols_l ρnL [=] empty).
  { pose proof (dom_subset_ftvar_in_aenv Ξ1L) as Hds.
    clear - HgfF Hds HdflL. fsetdec. }
  assert (Hclx : cols_l (ρxL ++ ρnL ++ ρ) ∩ dom Ξ1F [=] empty)
    by (rewrite ! cols_l_app; clear - HbFx HbFn HblkF0; fsetdec).
  assert (HblkF : dom Ξ1F ∩ cols_l ((α, α) :: ρxL ++ ρnL ++ ρ) [=] empty)
    by (cbn [cols_l fst]; clear - Hclx HαF; fsetdec).
  assert (HdΘF : dom (Ξ2L ++ Θ2) [<=] S1)
    by (rewrite dom_app; clear - HiL HdΘ HgL; fsetdec).
  assert (HxrS : cols_r ρxL [<=] S1).
  { intros x Hx. destruct (cols_r_in_inv _ _ Hx) as [a Hin].
    assert (Hin' : In (a, x) (ρxL ++ ρnL))
      by (apply in_or_app; left; exact Hin).
    destruct (HρL _ _ Hin') as [_ [Hb _]]. exact Hb. }
  assert (HnrS : cols_r ρnL [<=] S1)
    by (clear - HdfrL HiL; fsetdec).
  assert (HVS1 : V ∩ ftvar_in_aenv Θ1 [<=] S1)
    by (clear - Hscp2 HgL; fsetdec).
  assert (Hcr1 : cols_r (ρxL ++ ρnL ++ ρ) [<=] S1)
    by (rewrite ! cols_r_app; clear - Hscp2 HgL HxrS HnrS; fsetdec).
  assert (Hscp2F : (V ∩ ftvar_in_aenv Θ1)
                     ∪ cols_r ((α, α) :: ρxL ++ ρnL ++ ρ) [<=] S1)
    by (cbn [cols_r snd]; clear - HVS1 Hcr1 HαS1; fsetdec).
  assert (HcovF : ftvar_in_pskl pskl_ghost ∪ ftvar_in_a_cstrs C2 [<=] S1).
  { assert (HcC : ftvar_in_a_cstrs C2 [<=] S1)
      by (eapply e_looksub_cstr_ftvar; [ exact DL | clear - Hcov; fsetdec ]).
    simpl. clear - HcC. fsetdec. }
  assert (HagrS : flex_agree_rel ((α, α) :: ρxL ++ ρnL ++ ρ)
                    (V ∩ ftvar_in_aenv Θ1) (Ξ1L ++ Θ1) (Ξ2L ++ Θ2))
    by (eapply flex_agree_rel_id_to_pair;
        [ exact HagrF | exact HαV | exact HVSsub ]).
  assert (HrCS : rel_a_cstrs ((α, α) :: ρxL ++ ρnL ++ ρ)
                   (V ∩ ftvar_in_aenv Θ1) C1 C2).
  { eapply rel_a_cstrs_morph; [ exact HrC | | ].
    - intros a b Hin. apply rel_atom__pair. right. exact Hin.
    - intros a Ha. destruct (a == α) as [-> | Hne].
      + apply rel_atom__pair. left. reflexivity.
      + apply rel_atom__id. clear - Ha Hne HVSadd. fsetdec. }
  destruct (a_solve_cstr_rel_e HF
              (rel_pskl__ghost ((α, α) :: ρxL ++ ρnL ++ ρ)
                 (V ∩ ftvar_in_aenv Θ1)) HrCS
              HagrS Hscp1F HblkF HdΘF Hscp2F HcovF)
    as (S2 & ρxF & ρnF & Ξ2F & Q2 & DF & E1F & E2F & HρF & HtrF & HrQ).
  pose proof (e_solve_cstr_supply_grows DF) as HgF.

  (* ---- STEP 3: the guess, §4, at the three-block context ---- *)
  assert (HrQ'' : rel_pskl ((α, α) :: ρxF ++ ρnF ++ ρxL ++ ρnL ++ ρ)
                    (V ∩ ftvar_in_aenv Θ1) Q1 Q2)
    by rel_perm HrQ.
  assert (Hscp1G : V ∩ ftvar_in_aenv Θ1
                   [<=] ftvar_in_aenv (Ξ1F ++ Ξ1L ++ Θ1))
    by (rewrite ! ftvar_in_aenv_app; clear; fsetdec).
  assert (HcovG0 : V ∪ ftvar_in_pskl Q2 [<=] S2).
  { pose proof (e_solve_cstr_out_ftvar DF) as Hout. simpl in Hout.
    clear - Hout Hscp2 HgL HgF HcovF. fsetdec. }
  assert (HcovG : (V ∩ ftvar_in_aenv Θ1) ∪ ftvar_in_pskl Q2 [<=] S2)
    by (clear - HcovG0; fsetdec).
  destruct (a_guess_rel_e HG HrQ'' Hscp1G HcovG)
    as (S3 & ρnG & Ξ2G & Q2' & DG & E1G & E2G & HrQ').

  (* ---- the answer ---- *)
  exists S3, (ρxF ++ ρxL), (ρnL ++ ρnF ++ ρnG), (Ξ2L ++ Ξ2F ++ Ξ2G), Q2'.
  split; [ eapply e_extract__solve; [ exact DL | exact DF | exact DG ] | ].
  split;
    [ rewrite ! flex_pairs_l_app; rewrite <- E1L, <- E1F, <- E1G; reflexivity | ].
  split;
    [ rewrite ! flex_pairs_r_app; rewrite <- E2L, <- E2F, <- E2G; reflexivity | ].
  split.
  { intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - destruct (HρF _ _ Hin) as [Ha Hb].
      rewrite ftvar_in_aenv_app in Ha.
      split; [ clear - Ha; fsetdec | clear - Hb HgL; fsetdec ].
    - assert (Hin' : In (a, b) (ρxL ++ ρnL))
        by (apply in_or_app; left; exact Hin).
      destruct (HρL _ _ Hin') as [Ha [_ Hb]].
      split; [ clear - Ha; fsetdec | exact Hb ]. }
  (* ⭐⭐ THE ρx COLUMN DODGES THE WHOLE BLOCK — six facts, one per
     (column, block) pair.  Four are the layers' own; the two against the
     GUESS's block are the new guard's, through [cols_l ρxL ⊆ 𝒞₁] (the
     look's) and [cols_l ρxF ⊆ ftvar_in_pskl Q1] (the fold's TRIM). *)
  split.
  { assert (H1 : cols_l ρxL ∩ dom Ξ1L [=] empty) by (clear - HxlL; fsetdec).
    assert (H2 : cols_l ρxL ∩ dom Ξ1F [=] empty) by (clear - HbFx; fsetdec).
    assert (H3 : cols_l ρxL ∩ dom Ξ1G [=] empty)
      by (clear - Hguard2 HxsubL; fsetdec).
    assert (H4 : cols_l ρxF ∩ (dom Ξ1L ∪ dom Ξ1F) [=] empty).
    { intros x. split; intros Hx; [ | clear - Hx; fsetdec ]. exfalso.
      assert (Hxl : x `in` cols_l ρxF) by (clear - Hx; fsetdec).
      destruct (cols_l_in_inv _ _ Hxl) as [b Hin].
      destruct (HρF _ _ Hin) as [Ha _].
      rewrite ftvar_in_aenv_app in Ha.
      pose proof (dom_subset_ftvar_in_aenv Ξ1L) as Hds.
      clear - Ha Hds Hx. fsetdec. }
    assert (H5 : cols_l ρxF ∩ dom Ξ1G [=] empty)
      by (clear - Hguard2 HtrF; fsetdec).
    rewrite ! dom_app. rewrite cols_l_app.
    clear - H1 H2 H3 H4 H5. fsetdec. }
  (* ⭐ THE SHIFT BACK: the pair [(α, α)] is spent, and [α] is in [V]. *)
  eapply rel_pskl_morph; [ exact HrQ' | | ].
  - intros a b Hin.
    rewrite ? in_app_iff in Hin; simpl in Hin; rewrite ? in_app_iff in Hin.
    repeat match goal with
           | H : _ \/ _ |- _ => destruct H as [H | H]
           end;
      try (match goal with
           | H : (α, α) = (a, b) |- _ =>
               inversion H; subst; apply rel_atom__id; exact HαV
           end);
      apply rel_atom__pair; rewrite ? in_app_iff; tauto.
  - intros a Ha. apply rel_atom__id. clear - Ha. fsetdec.
Qed.
