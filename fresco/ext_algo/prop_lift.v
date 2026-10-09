(** ext_algo — ⛔ THE CAMPAIGN'S LAST DEBT: the LIFT, [a_*] ⟹ [e_*].

    §8c.23 left exactly one link open.  Runner completeness (levels 1–8) is
    stated over the SUPPLY-THREADED relations, so the decidability corollary's
    NEGATIVE branch refutes [e_typing] and not [algo/]'s own [a_typing].  What
    closes the gap — and with it makes the extracted program SOUND AND
    COMPLETE for the paper's DECLARATIVE system — is the converse of the
    bridge, composed with what already exists:

      d_ ⟹ a_typing        a_typing_complete_decl_*   (README §III)   ✅
      a_typing ⟹ e_typing  THIS FILE (§3–§12) + prop_lift_typing.v    ✅
      e_typing ⟹ Some      e_typing_run_complete      (level 8)       ✅

    ⭐⭐ THE TECHNIQUE (§8c.24).  A structural induction on the [a_*]
    derivation FAILS at every row that invents a name: the [a_] rule chose its
    atom freely, the [e_] rule must choose one fresh for the SUPPLY, so the IH
    is wanted at a TRANSPOSED sub-derivation, which is not a subterm — §8c.3's
    obstruction.  Two repairs, both affordable now:

    - induct on the e-side ORDER (total and unconditional), leaving the [a_*]
      derivation an ordinary HYPOTHESIS that may be transposed freely with
      algo/prop_swap.v's single-swap equivariance;
    - or on a plain syntactic MEASURE where one exists — [size_pskl] of the
      subject for [guess^TY], whose ∀ row opens at a variable (size-preserving)
      below a [pskl_all_syn] node that pays the [S].

    ⚙ At the guess alone the conclusion could be EXISTENTIAL up to a CHAIN:
    the [e_] derivation's outputs [swaps_*] images of the [a_] derivation's.

    ⛔⛔ BUT THAT CURRENCY DIES ONE LEVEL UP — read §3 before writing any
    block above the guess.  A chain is a FUNCTION on atoms, and above the
    guess the [a_] rules LEAK binders into their outputs, so one left atom
    can need two right images.  Everything here is therefore stated over
    prop_solve_det.v §1's deliberately RELATIONAL [rel_pskl] / [rel_a_cstrs]
    at a pair list ρ that GROWS — which is also the currency §8c.9's
    transport layer (prop_solve_rel.v §3-§7) already built a → a, so those
    are what §4-§7 are copied from.

    §3  ⭐⭐⭐ the LOOK block — ALREADY CLOSED upstream, and why the chain
        currency cannot reach it
    §4  ⭐ [guess^TY] again, REL currency — what the solve layer calls
    §5  ⭐ the eq-solve, twelve rows
    §6  ⭐ the sub-solve, nine rows (and the leaked-opener column ρx)
    §7  ⭐ the constraint fold, three rows

    ⛔ WHAT IS LEFT: extract, consis, sub, split, pat, typing.  ⚠️⚠️ THE
    EXTRACT ROW IS NOT ROUTINE AND IS NOT A MISSING PROOF — as stated it is
    FALSE.  See §7's closing note. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.ltac_utils.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.prop_basic.
Require Import src.fresco.prop_ln.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.sub.prop_looksub.
Require Import src.fresco.algo.sub.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.prop_guess.
Require Import src.fresco.ext_algo.prop_termination.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.prop_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.prop_solve.
Require Import src.fresco.ext_algo.prop_solve_det.
Require Import src.fresco.ext_algo.prop_solve_rel.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo.prop_inc_strengthen.
Require Import src.fresco.algo.consis.prop_consis_rename.
Require Import src.fresco.algo.consis.prop_soundness_consis.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.prop_consis.
(* ⚙ for the [swaps_*] kit levels 7/8 added — [swaps_pskl_ptyp_to_pskl] here,
   and [swaps_ptyp_open] / [ptyp_to_pskl_inj] for the blocks above. *)
Require Import src.fresco.ext_algo.prop_typing_complete.
Require Import src.fresco.ext_algo.def_sub.
Require Import src.fresco.ext_algo.prop_sub.
Require Import src.fresco.ext_algo.prop_extract.
Require Import src.fresco.algo.prop_stability.
Require Import src.fresco.algo.prop_wf_preservation.
Require Import src.fresco.algo.sub.prop_soundness_subtag.
Require Import src.fresco.ext_algo.def_pat.
Require Import src.fresco.ext_algo.prop_pat.
Require Import src.fresco.algo.prop_mod_compat.
Require Import src.fresco.algo.prop_precise.
Require Import src.fresco.algo.pat.prop_soundness_pat.
Require Import src.fresco.algo.pat.prop_completeness_pat.
Require Import src.fresco.algo.typing.prop_soundness_typing.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.ext_algo.def_typing.
Require Import src.fresco.ext_algo.prop_typing.

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
(*  currency that is — [a_looksub_lookeq_rel_e] (prop_solve_rel.v §7,      *)
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

(** ⚙ The SET form of [a_solve_cstr_generated_fresh] (algo/sub/
    prop_solve_sub.v).  prop_look_pair.v has one, but that file is a heavy
    dependency for a single fact the fold's arrow row needs. *)
Lemma a_solve_cstr_block_fresh_set : forall Θ C P Ξ P',
  {{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ P' }}a ->
  dom Ξ ∩ ftvar_in_aenv Θ [=] empty.
Proof.
  intros * H.
  apply AtomSetProperties.empty_is_empty_1.
  intros x Hx. apply AtomSetFacts.inter_iff in Hx. destruct Hx as [HA HB].
  exact (a_solve_cstr_generated_fresh H HA HB).
Qed.

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
    split; [ apply e_guess_mono__hole; exact Hα2 | ].
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
    split; [ apply e_guess_mono__tophole; exact HG2 | ].
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
    assert (Hcr0 : cols_r (restrict_pairs β β2 ρ) [<=] cols_r ρ)
      by apply cols_r_restrict_pairs.
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
    split; [ apply e_solve_eq__hole_l | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    simpl. exact HrelQ.
  - (* SE-VacuousR: a ghost target answers the subject *)
    inversion HrelQ; subst.
    exists S0, nil, nil, P3.
    split; [ apply e_solve_eq__hole_r | ].
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
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa, Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh S0) as [β2 Hβ2].
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
    (* ⭐ THE RESTRICTION.  [rel_pskl_close_pair] wants [β] off [cols_l ρ];
       side 2 buys that from the SUPPLY and side 1 has none, so the pairs
       the close must not see are DELETED.  Legal here because the row has
       not opened yet: [β] misses both inputs by the rule's own side
       condition, [β2] misses both by the supply. *)
    assert (Hcl0 : cols_l (restrict_pairs β β2 ρ) [<=] cols_l ρ)
      by apply cols_l_restrict_pairs.
    assert (Hcr0 : cols_r (restrict_pairs β β2 ρ) [<=] cols_r ρ)
      by apply cols_r_restrict_pairs.
    (* ⭐ and the push is the WEAK one — [flex_agree_rel_push_look] asks
       only that the two openers miss the two DOMAINS. *)
    assert (Hagr' : flex_agree_rel ((β, β2) :: restrict_pairs β β2 ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_look.
      - eapply flex_agree_rel_weaken;
          [ exact Hagr
          | intros a0 b0 Hin0; eapply restrict_pairs_incl; exact Hin0
          | fsetdec ].
      - clear - Hβ1 Hds1. fsetdec.
      - clear - Hβ2 HdΘ. fsetdec. }
    assert (Hscp1' : V [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: restrict_pairs β β2 ρ)
                       [<=] add β2 S0)
      by (simpl; clear - Hscp2 Hcr0; fsetdec).
    assert (HupP : ftvar_in_pskl (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl P2b)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (HupQ : ftvar_in_pskl (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl Q2b)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                      [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupP HupQ; fsetdec).
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD)).
    assert (Hblk' : dom Ξ ∩ cols_l ((β, β2) :: restrict_pairs β β2 ρ)
                      [=] empty)
      by (simpl; simpl in Hd1p; clear - Hblk Hd1p Hcl0; fsetdec).
    assert (HrP0r : rel_pskl (restrict_pairs β β2 ρ) V P P2b)
      by (apply rel_pskl_restrict;
          [ exact HrP0 | clear - Hβ1; fsetdec
          | clear - Hβ2 Hcov; simpl in Hcov; fsetdec ]).
    assert (HrQ0r : rel_pskl (restrict_pairs β β2 ρ) V Q Q2b)
      by (apply rel_pskl_restrict;
          [ exact HrQ0 | clear - Hβ1; fsetdec
          | clear - Hβ2 Hcov; simpl in Hcov; fsetdec ]).
    destruct (IHHD (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                ((β, β2) :: restrict_pairs β β2 ρ) V
                ltac:(apply rel_pskl_open_pair; exact HrP0r)
                ltac:(apply rel_pskl_open_pair; exact HrQ0r)
                Hagr' Hscp1' Hblk' HdΘ' Hscp2' Hcov')
      as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
    assert (Hd2p : dom Ξ2 ∩ add β2 S0 [=] empty)
      by (apply (proj2 e_solve_sub_eq_block) in D2p; tauto).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    exists S1, ρn, Ξ2, (pskl_all_syn (close_pskl_wrt_pskl β2 Y2)).
    split; [ apply e_solve_eq__forall with (β := β2); [ exact Hβ2 | exact D2p ] | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    constructor.
    eapply rel_pskl_close_pair_restrict.
    + exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + simpl in Hd1p. clear - Hd1p Hdfl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + clear - Hd2p Hdfr. fsetdec.
    + in_incl.
    + in_incl.
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
    exists S1, ρn, Ξ2, (pskl_tophole Y2).
    split; [ apply e_solve_eq__tophole_both; exact D2p | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    constructor. exact Hrel'.
  - (* SE-GhostForall: the TARGET opens; the subject stays whole *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa, Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh S0) as [β2 Hβ2].
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
    (* ⭐ THE RESTRICTION.  [rel_pskl_close_pair] wants [β] off [cols_l ρ];
       side 2 buys that from the SUPPLY and side 1 has none, so the pairs
       the close must not see are DELETED.  Legal here because the row has
       not opened yet: [β] misses both inputs by the rule's own side
       condition, [β2] misses both by the supply. *)
    assert (Hcl0 : cols_l (restrict_pairs β β2 ρ) [<=] cols_l ρ)
      by apply cols_l_restrict_pairs.
    assert (Hcr0 : cols_r (restrict_pairs β β2 ρ) [<=] cols_r ρ)
      by apply cols_r_restrict_pairs.
    (* ⭐ and the push is the WEAK one — [flex_agree_rel_push_look] asks
       only that the two openers miss the two DOMAINS. *)
    assert (Hagr' : flex_agree_rel ((β, β2) :: restrict_pairs β β2 ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_look.
      - eapply flex_agree_rel_weaken;
          [ exact Hagr
          | intros a0 b0 Hin0; eapply restrict_pairs_incl; exact Hin0
          | fsetdec ].
      - clear - Hβ1 Hds1. fsetdec.
      - clear - Hβ2 HdΘ. fsetdec. }
    assert (Hscp1' : V [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: restrict_pairs β β2 ρ)
                       [<=] add β2 S0)
      by (simpl; clear - Hscp2 Hcr0; fsetdec).
    assert (HupQ : ftvar_in_pskl (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl Q2b)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl (pskl_tophole P2b)
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                      [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupQ; fsetdec).
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD)).
    assert (Hblk' : dom Ξ ∩ cols_l ((β, β2) :: restrict_pairs β β2 ρ)
                      [=] empty)
      by (simpl; simpl in Hd1p; clear - Hblk Hd1p Hcl0; fsetdec).
    assert (HrP0r : rel_pskl (restrict_pairs β β2 ρ) V P P2b)
      by (apply rel_pskl_restrict;
          [ exact HrP0 | clear - Hβ1; fsetdec
          | clear - Hβ2 Hcov; simpl in Hcov; fsetdec ]).
    assert (HrQ0r : rel_pskl (restrict_pairs β β2 ρ) V Q Q2b)
      by (apply rel_pskl_restrict;
          [ exact HrQ0 | clear - Hβ1; fsetdec
          | clear - Hβ2 Hcov; simpl in Hcov; fsetdec ]).
    destruct (IHHD (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (pskl_tophole P2b)
                (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                ((β, β2) :: restrict_pairs β β2 ρ) V
                ltac:(apply rel_pskl_extend_pair; constructor; exact HrP0r)
                ltac:(apply rel_pskl_open_pair; exact HrQ0r)
                Hagr' Hscp1' Hblk' HdΘ' Hscp2' Hcov')
      as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
    assert (Hd2p : dom Ξ2 ∩ add β2 S0 [=] empty)
      by (apply (proj2 e_solve_sub_eq_block) in D2p; tauto).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    exists S1, ρn, Ξ2, (pskl_all_syn (close_pskl_wrt_pskl β2 Y2)).
    split;
      [ apply e_solve_eq__tophole_l_all with (β := β2);
        [ exact Hβ2 | exact D2p ] | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    constructor.
    eapply rel_pskl_close_pair_restrict.
    + exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + simpl in Hd1p. clear - Hd1p Hdfl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + clear - Hd2p Hdfr. fsetdec.
    + in_incl.
    + in_incl.
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
    { apply e_solve_eq__tophole_l_guarded;
        [ eapply rel_pskl_guarded; [ exact HrelQ | assumption ]
        | exact D2p ]. }
    split; [ exact E1 | split; [ exact E2 | exact Hrel' ] ].
  - (* SE-ForallGhost: the SUBJECT opens; the target stays whole *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa, Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh S0) as [β2 Hβ2].
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
    (* ⭐ THE RESTRICTION.  [rel_pskl_close_pair] wants [β] off [cols_l ρ];
       side 2 buys that from the SUPPLY and side 1 has none, so the pairs
       the close must not see are DELETED.  Legal here because the row has
       not opened yet: [β] misses both inputs by the rule's own side
       condition, [β2] misses both by the supply. *)
    assert (Hcl0 : cols_l (restrict_pairs β β2 ρ) [<=] cols_l ρ)
      by apply cols_l_restrict_pairs.
    assert (Hcr0 : cols_r (restrict_pairs β β2 ρ) [<=] cols_r ρ)
      by apply cols_r_restrict_pairs.
    (* ⭐ and the push is the WEAK one — [flex_agree_rel_push_look] asks
       only that the two openers miss the two DOMAINS. *)
    assert (Hagr' : flex_agree_rel ((β, β2) :: restrict_pairs β β2 ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_look.
      - eapply flex_agree_rel_weaken;
          [ exact Hagr
          | intros a0 b0 Hin0; eapply restrict_pairs_incl; exact Hin0
          | fsetdec ].
      - clear - Hβ1 Hds1. fsetdec.
      - clear - Hβ2 HdΘ. fsetdec. }
    assert (Hscp1' : V [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: restrict_pairs β β2 ρ)
                       [<=] add β2 S0)
      by (simpl; clear - Hscp2 Hcr0; fsetdec).
    assert (HupP : ftvar_in_pskl (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl P2b)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                    ∪ ftvar_in_pskl (pskl_tophole Q2b) [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupP; fsetdec).
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD)).
    assert (Hblk' : dom Ξ ∩ cols_l ((β, β2) :: restrict_pairs β β2 ρ)
                      [=] empty)
      by (simpl; simpl in Hd1p; clear - Hblk Hd1p Hcl0; fsetdec).
    assert (HrP0r : rel_pskl (restrict_pairs β β2 ρ) V P P2b)
      by (apply rel_pskl_restrict;
          [ exact HrP0 | clear - Hβ1; fsetdec
          | clear - Hβ2 Hcov; simpl in Hcov; fsetdec ]).
    assert (HrQ0r : rel_pskl (restrict_pairs β β2 ρ) V Q Q2b)
      by (apply rel_pskl_restrict;
          [ exact HrQ0 | clear - Hβ1; fsetdec
          | clear - Hβ2 Hcov; simpl in Hcov; fsetdec ]).
    destruct (IHHD (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                (pskl_tophole Q2b)
                ((β, β2) :: restrict_pairs β β2 ρ) V
                ltac:(apply rel_pskl_open_pair; exact HrP0r)
                ltac:(apply rel_pskl_extend_pair; constructor; exact HrQ0r)
                Hagr' Hscp1' Hblk' HdΘ' Hscp2' Hcov')
      as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
    assert (Hd2p : dom Ξ2 ∩ add β2 S0 [=] empty)
      by (apply (proj2 e_solve_sub_eq_block) in D2p; tauto).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    exists S1, ρn, Ξ2, (pskl_all_syn (close_pskl_wrt_pskl β2 Y2)).
    split;
      [ apply e_solve_eq__all_l_tophole with (β := β2);
        [ exact Hβ2 | exact D2p ] | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    constructor.
    eapply rel_pskl_close_pair_restrict.
    + exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + simpl in Hd1p. clear - Hd1p Hdfl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + clear - Hd2p Hdfr. fsetdec.
    + in_incl.
    + in_incl.
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
    { apply e_solve_eq__tophole_r_guarded;
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
  - apply rel_pskl__hole.
  - apply rel_pskl__tophole. apply IHHrel; assumption.
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
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
    (* ⭐ THE RESTRICTION.  [rel_pskl_close_pair] wants [β] off [cols_l ρ];
       side 2 buys that from the SUPPLY and side 1 has none, so the pairs
       the close must not see are DELETED.  Legal here because the row has
       not opened yet: [β] misses both inputs by the rule's own side
       condition, [β2] misses both by the supply. *)
    assert (Hcl0 : cols_l (restrict_pairs β β2 ρ) [<=] cols_l ρ)
      by apply cols_l_restrict_pairs.
    assert (Hcr0 : cols_r (restrict_pairs β β2 ρ) [<=] cols_r ρ)
      by apply cols_r_restrict_pairs.
    (* ⭐ and the push is the WEAK one — [flex_agree_rel_push_look] asks
       only that the two openers miss the two DOMAINS. *)
    assert (Hagr' : flex_agree_rel ((β, β2) :: restrict_pairs β β2 ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_look.
      - eapply flex_agree_rel_weaken;
          [ exact Hagr
          | intros a0 b0 Hin0; eapply restrict_pairs_incl; exact Hin0
          | fsetdec ].
      - clear - Hβ1 Hds1. fsetdec.
      - clear - Hβ2 HdΘ. fsetdec. }
    assert (Hscp1' : V [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: restrict_pairs β β2 ρ)
                       [<=] add β2 S0)
      by (simpl; clear - Hscp2 Hcr0; fsetdec).
    assert (HupP : ftvar_in_pskl (open_pskl_wrt_pskl P3b (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl P3b)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl (open_pskl_wrt_pskl P3b (pskl_var_f β2))
                    ∪ ftvar_in_pskl Q3 [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupP; fsetdec).
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ HD)).
    assert (Hblk' : dom Ξ ∩ cols_l ((β, β2) :: restrict_pairs β β2 ρ)
                      [=] empty)
      by (simpl; simpl in Hd1p; clear - Hblk Hd1p Hcl0; fsetdec).
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
    exists S1, ρx, ρn, Ξ2, (pskl_tophole Y2).
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
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
    (* ⭐ THE RESTRICTION.  [rel_pskl_close_pair] wants [β] off [cols_l ρ];
       side 2 buys that from the SUPPLY and side 1 has none, so the pairs
       the close must not see are DELETED.  Legal here because the row has
       not opened yet: [β] misses both inputs by the rule's own side
       condition, [β2] misses both by the supply. *)
    assert (Hcl0 : cols_l (restrict_pairs β β2 ρ) [<=] cols_l ρ)
      by apply cols_l_restrict_pairs.
    assert (Hcr0 : cols_r (restrict_pairs β β2 ρ) [<=] cols_r ρ)
      by apply cols_r_restrict_pairs.
    (* ⭐ and the push is the WEAK one — [flex_agree_rel_push_look] asks
       only that the two openers miss the two DOMAINS. *)
    assert (Hagr' : flex_agree_rel ((β, β2) :: restrict_pairs β β2 ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_look.
      - eapply flex_agree_rel_weaken;
          [ exact Hagr
          | intros a0 b0 Hin0; eapply restrict_pairs_incl; exact Hin0
          | fsetdec ].
      - clear - Hβ1 Hds1. fsetdec.
      - clear - Hβ2 HdΘ. fsetdec. }
    assert (Hscp1' : V [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: restrict_pairs β β2 ρ)
                       [<=] add β2 S0)
      by (simpl; clear - Hscp2 Hcr0; fsetdec).
    assert (HupB : ftvar_in_pskl (open_pskl_wrt_pskl B3 (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl B3)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl P3
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl B3 (pskl_var_f β2))
                      [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupB; fsetdec).
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ HD)).
    assert (Hblk' : dom Ξ ∩ cols_l ((β, β2) :: restrict_pairs β β2 ρ)
                      [=] empty)
      by (simpl; simpl in Hd1p; clear - Hblk Hd1p Hcl0; fsetdec).
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
    split; [ exact HρxN | ].
    split; [ exact HtrN | ].
    exact HrelN.
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
    | He : a_solve_eq Θ pskl_hole Q1 ?x ?y |- _ => rename He into HDeq
    end.
    assert (HcovA : ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl Q3a [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    assert (Hblk1 : dom Ξ1 ∩ cols_l ρ [=] empty)
      by (rewrite dom_app in Hblk; clear - Hblk; fsetdec).
    destruct (a_solve_eq_rel_e HDeq (rel_pskl__hole ρ V) HrQa Hagr Hscp1
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
    assert (HcovB : ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl Q3b [<=] S1)
      by (clear - Hcov Hgr1; simpl in *; fsetdec).
    assert (Hd1b : dom Ξ2 ∩ ftvar_in_aenv (Ξ1 ++ Θ) [=] empty)
      by (exact ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ HD)).
    assert (Hblk2 : dom Ξ2 ∩ cols_l (ρnA ++ ρ) [=] empty).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app in Hd1b.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      rewrite dom_app in Hblk.
      clear - Hd1b Hds Hdfl Hblk. fsetdec. }
    destruct (IHHD S1 (Ξ2a ++ Θ2) pskl_hole Q3b (ρnA ++ ρ) V
                (rel_pskl__hole (ρnA ++ ρ) V)
                ltac:(apply rel_pskl_widen; exact HrQb)
                Hagr' Hscp1' Hblk2 HdΘ' Hscp2' HcovB)
      as (S2 & ρx & ρnB & Ξ2b & P2b' & D2b & E1b & E2b & Hρx & Htr & HrelB').
    exists S2, ρx, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a),
      (pskl_tophole (pskl_arrow P2a' P2b')).
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
    exists S0, nil, nil, nil, (pskl_tophole Q3).
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
      by (exact (a_solve_cstr_block_fresh_set HD)).
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
(*  [a_extract] has ONE rule and it is §3 → §7 → §4.  Every premise of the *)
(*  three transports is now available at the composition EXCEPT one, and   *)
(*  that one is carried here as an explicit hypothesis:                    *)
(*                                                                        *)
(*      ftvar_in_a_cstrs 𝒞 ∩ dom Ξs [=] empty                             *)
(*                                                                        *)
(*  — the FOLD's generated flexibles are fresh for the constraints it is  *)
(*  solving.  ⛔ WHY IT IS OWED, and it is the SAME species as the         *)
(*  cross-half guard one layer down.  The collection LEAKS openers into    *)
(*  [𝒞] (all five ∀ rows do), and those openers are bound NOWHERE — not in *)
(*  [Θ0], not in [Ξ].  The fold then runs at [Ξ ++ Θ0] and [SE-FlexR]'s    *)
(*  guess draws its flexibles fresh for [ftvar_in_aenv (Ξ ++ Θ0)] ONLY, so *)
(*  it may draw a leaked opener.  Side 1 then reads that atom as FLEXIBLE  *)
(*  (it is in [Ξs]) where side 2 reads its counterpart as a rigid free     *)
(*  atom — no [flex_agree_rel] between the two contexts exists, which is   *)
(*  precisely §7's premise, and it is the configuration                    *)
(*  cex/probe_extract_conflated_opener.v refutes one level down.           *)
(*                                                                        *)
(*  ⭐ UNLIKE the solve layer's ∀-binders, this one IS expressible at the   *)
(*  rule: [𝒞] and [Ξs] are both named in [a_extract__solve]'s premises.    *)
(*  Transport 5's [∀ (a,b) ∈ ρx, a ∈ ftvar_in_a_cstrs 𝒞₁] is what connects *)
(*  the guard to the pair columns.  ⇒ landing it is a RULE CHANGE          *)
(*  ([paper-gap] + docs/PAPER-GAPS.md), and this lemma is the proof that   *)
(*  it is exactly what the rung needs — nothing weaker, nothing more.      *)
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

Lemma a_extract_rel_e_gen :
  forall Θ1 α m NM P1 P1' Ξ1L C1 Ξ1F Q1 Ξ1G Q1',
  {{ Θ1 ⊢ P1 ≼[ α , m ] P1' ⤳ Ξ1L ⨾ C1 }}a ->
  {{ (Ξ1L ++ Θ1) ⊩ C1 ⨾ pskl_hole ⤳ Ξ1F ⨾ Q1 }}a ->
  a_guess (Ξ1F ++ Ξ1L ++ Θ1) NM Q1 Ξ1G Q1' ->
  (* ⛔ THE TWO GUARDS THE ROW OWES — see the box above.  The second is the
     GUESS's half (2026-08-21, §8c.41). *)
  ftvar_in_a_cstrs C1 ∩ dom Ξ1F [=] empty ->
  (ftvar_in_a_cstrs C1 ∪ ftvar_in_pskl Q1) ∩ dom Ξ1G [=] empty ->
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
  dom (Ξ1L ++ Ξ1F ++ Ξ1G) ∩ cols_l ρ [=] empty ->
  α `notin` dom (Ξ1L ++ Ξ1F ++ Ξ1G) ->
  dom Θ2 [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] S0 ->
  exists S1 ρx ρn Ξ2 Q2',
    {{ S0 ↝ S1 ⊨ Θ2 ⊢ P2 ⊳[ NM , α , m ] P2' ⤳ Ξ2 ↪ Q2' }}e
    /\ (Ξ1L ++ Ξ1F ++ Ξ1G) = flex_pairs_l ρn
    /\ Ξ2 = flex_pairs_r ρn
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 /\ b `notin` S0)
    (* ⭐⭐ AND THE LEFT COLUMN DODGES THE WHOLE OUTPUT BLOCK (§8c.41).
       This is what [a_sub__forall_l] needs to DROP the ρx column at the
       atoms of a skeleton wf over [Ξ1 ++ Θ1]: a leaked opener is bound
       nowhere, so the motive's block premise cannot keep it out of
       [dom Θ1] and [rel_aenv] would owe a binding for each. *)
    /\ cols_l ρx ∩ dom (Ξ1L ++ Ξ1F ++ Ξ1G) [=] empty
    /\ rel_pskl (ρx ++ ρn ++ ρ) V Q1' Q2'.
Proof.
  intros Θ1 α m NM P1 P1' Ξ1L C1 Ξ1F Q1 Ξ1G Q1' HL HF HG Hguard Hguard2.
  intros S0 Θ2 P2 P2' ρ V HrP HrP' HαV Hαl Hαr Hagr Hscp1 Hblkρ HαΞ
    HdΘ Hscp2 Hcov.
  rewrite ! dom_app in Hblkρ, HαΞ.
  assert (HblkL : dom Ξ1L ∩ cols_l ρ [=] empty) by (clear - Hblkρ; fsetdec).
  assert (HblkF0 : dom Ξ1F ∩ cols_l ρ [=] empty) by (clear - Hblkρ; fsetdec).
  assert (HαF : α `notin` dom Ξ1F) by (clear - HαΞ; fsetdec).
  assert (HαS0 : α `in` S0) by (clear - HαV Hscp2; fsetdec).

  (* ---- STEP 1: the collection, transport 5 (prop_solve_rel.v §7) ---- *)
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
  pose proof (a_solve_cstr_block_fresh_set HF) as HgfF.
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
  assert (HcovF : ftvar_in_pskl pskl_hole ∪ ftvar_in_a_cstrs C2 [<=] S1).
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
              (rel_pskl__hole ((α, α) :: ρxL ++ ρnL ++ ρ)
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

(** ⭐⭐⭐ THE WRAPPER — and it is one [destruct], now that
    [a_extract__solve] CARRIES the guard (2026-08-20, algo/def_rules.v).
    The rung is CLOSED: [a_extract] lifts to [e_extract]. *)
Lemma a_extract_rel_e : forall Θ1 NM α m P1 P1' Ξ1 Q1',
  {{ Θ1 ⊢ P1 ⊳[ NM , α , m ] P1' ⤳ Ξ1 ↪ Q1' }}a ->
  forall S0 Θ2 P2 P2' ρ V,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V P1' P2' ->
  α `in` V ->
  α `notin` cols_l ρ ->
  α `notin` cols_r ρ ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  (* ⭐⭐ the three scoping premises of §8c.41 — see [a_extract_rel_e_gen].
     ⚙ [a_sub__forall_l] reads the middle one off the lift motive's block
     premise and the last off its own choice of opener. *)
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
    /\ cols_l ρx ∩ dom Ξ1 [=] empty
    /\ rel_pskl (ρx ++ ρn ++ ρ) V Q1' Q2'.
Proof.
  intros Θ1 NM α m P1 P1' Ξ1 Q1' HD.
  destruct HD as
    [ Θ0 NM0 α0 m0 Ps Ps' ΞL ΞF ΞG C0 Q0 Q0' HL HF HG Hgd Hgd2 ].
  intros S0 Θ2 P2 P2' ρ V HrP HrP' HαV Hαl Hαr Hagr Hscp1 Hblkρ HαΞ
    HdΘ Hscp2 Hcov.
  eapply a_extract_rel_e_gen;
    [ exact HL | exact HF | exact HG | exact Hgd | exact Hgd2
    | exact HrP | exact HrP' | exact HαV | exact Hαl | exact Hαr
    | exact Hagr | exact Hscp1 | exact Hblkρ | exact HαΞ
    | exact HdΘ | exact Hscp2 | exact Hcov ].
Qed.

(* ===================================================================== *)
(*  ✅ WHAT THE NEXT BLOCK OWED — AND THE GUARD THAT NOW PAYS IT          *)
(*                                                                        *)
(*  [a_extract] has ONE rule and it composes exactly §3, §7 and §4:        *)
(*                                                                        *)
(*      look    Θ0 ⊢ P ≼[α,m] P' ⤳ Ξ ⨾ 𝒞                                  *)
(*      fold    (Ξ ++ Θ0) ⊩ 𝒞 ⨾ ◇ ⤳ Ξs ⨾ Q                                *)
(*      guess   (Ξs ++ Ξ ++ Θ0) ⊢ guess^N Q ⤳ Ξ' ⨾ Q'                     *)
(*                                                                        *)
(*  so it LOOKS like three [destruct]s.  It is not, and the obstruction is *)
(*  the SAME leak §6 names, now crossing between two SIBLING premises of   *)
(*  the collection.                                                        *)
(*                                                                        *)
(*  ⚠️ THE CONFIGURATION (machine-checked; see the ✅ below).  [LE-Arrow]  *)
(*  runs both halves at the SAME [Θ], so *)
(*  a binder LEFT half 1 leaked into [𝒞1] and a flexible half 2 INVENTED   *)
(*  into [Ξ2] may be the SAME ATOM: the first avoids                       *)
(*  [add α (ftvar Θ ∪ ftvar P1 ∪ ftvar P1')], the second                   *)
(*  [add α (add β̂ (ftvar Θ ∪ ftvar P2))], and neither excludes the other.  *)
(*  Concretely, with [Q = α], [Q' = 0] and [P2 = α → α]:                   *)
(*                                                                        *)
(*      Θ ⊢ (∀α) → (α→α)  ∼[α]  (∀0) → β̂  ⤳ (γ ~ ⌢)  ⨾  [eq γ ; eq γ]     *)
(*                                                                        *)
(*  where the FIRST [γ] is half 1's leaked opener and the second is        *)
(*  half 2's fresh flexible.  The e-side keeps them apart — the opener is  *)
(*  drawn at [S0], the flexible at [S1 ⊇ add opener S0] — so §3 hands back *)
(*  [𝒞2 = [eq γ1 ; eq γ2]] with [γ1 ≠ γ2] and [Ξ2 = (γ2 ~ ⌢)].            *)
(*                                                                        *)
(*  ⛔ AND THE FOLD THEN DISAGREES, not merely renames.  Put a non-ghost    *)
(*  constraint ahead of the pair (nest one more arrow, so                  *)
(*  [𝒞 = [eq 1 ; eq γ ; eq γ]]) and the accumulated pattern is [1] by the  *)
(*  time the leaked [γ] is met.  Side 1 sees [γ] FLEXIBLE — it is in [Ξ] — *)
(*  and fires [SE-FlexR]; side 2 sees [γ1] bound NOWHERE ([e_looksub]      *)
(*  discards its openers, exactly as the implementation does) and has NO   *)
(*  rule at [1 ∼ γ1]: not SE-Unit, not SE-Var, not SE-VacuousR, not        *)
(*  SE-GuardedGhost.  The threaded fold is STUCK where the unthreaded one  *)
(*  runs.  ⇒ no [flex_agree_rel] between [Ξ ++ Θ0] and [Ξ2 ++ Θ2] exists,  *)
(*  which is precisely the premise §7 needs.                               *)
(*                                                                        *)
(*  ✅ MACHINE-CHECKED: [cex/probe_extract_conflated_opener.v], four        *)
(*  lemmas, all Qed and assumptions-closed.  §1 builds the conflating       *)
(*  collection; §2a runs the a-side fold on it; §2b shows the fold is      *)
(*  STUCK once the opener is any atom the context does not bind; §3 builds *)
(*  the THREADED collection at the same inputs and it returns TWO atoms    *)
(*  where the a-side returns one; §4 composes them — the a-side fold runs  *)
(*  and the threaded one cannot, at one configuration.  (The threaded fold *)
(*  is refuted through [e_solve_cstr_sound], so §2b covers both.)          *)
(*                                                                        *)
(*  ✅✅ THE REPAIR IS LANDED (2026-08-19).  Both collection arrow rows now  *)
(*  carry the CROSS-HALF FRESHNESS GUARD                                   *)
(*                                                                        *)
(*      ftvar_in_a_cstrs C1 ∩ dom Ξ2 [=] empty                            *)
(*      ftvar_in_a_cstrs C2 ∩ dom Ξ1 [=] empty                            *)
(*                                                                        *)
(*  (fresco/algo/def_rules.v), so the configuration above is no longer      *)
(*  derivable and [e_looksub_sound] discharges both conjuncts — the guard  *)
(*  costs the threaded encoding NOTHING, and that is a theorem            *)
(*  ([e_looksub_lookeq_cstr_old], prop_look.v §2c).  ⇒ the extract row's   *)
(*  [flex_agree_rel] obligation is now available and this block is         *)
(*  UNBLOCKED.  What it cost inside the mech: hand-off §8c.25.             *)
(*                                                                        *)
(*  ⚙ FOR THE RECORD — WHAT THE REPAIR HAD TO BE.  A PREMISE that the      *)
(*  collection's leaked                                                    *)
(*  openers are apart from its own block — the fourth instance of the      *)
(*  prose-completion this tree has already had to make three times         *)
(*  ([AT-Abs]'s [uniq (αs ++ Θ1)], [a_sub__forall_l]'s [uniq (Ξ ++ Θ0)],   *)
(*  and [uniq Ξ] for [guess^TY]'s block).  ⚠️ [uniq Ξ] does NOT           *)
(*  suffice here and no strengthening of it can: a leaked opener is not a  *)
(*  block member, so [uniq] cannot see it.  ⛔ Nor is it derivable from a  *)
(*  scoping hypothesis on the look's inputs — both side conditions above   *)
(*  already dodge [ftvar_in_aenv Θ] and that is all a scoping premise      *)
(*  buys.  The premise has to be about the DERIVATION, and where it is     *)
(*  discharged ([a_sub__forall_l] is the only consumer) is the design      *)
(*  question the next session opens on.  docs/PAPER-GAPS.md will want it   *)
(*  once it is machine-checked.                                            *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §9  ⭐⭐⭐ THE CONSIS RUNG — [a_assign] / [a_unify] / [a_consis] LIFT     *)
(*                                                                        *)
(*  ONE mutual induction, 28 rows.  The motives are below; what they say  *)
(*  is that an [a_]-side run of the trio is MIRRORED by a supply-threaded  *)
(*  one, up to a pair list ρ that grows by the pairs each generative row   *)
(*  invents ([rel_ext] is that growth's spec, and it is what lets the      *)
(*  caller rebuild [rel_inj] / [rel_fun] at the wider list).               *)
(*                                                                        *)
(*  ⭐ SIDE 2 CARRIES NO WELL-FORMEDNESS.  [uniq Θ0'] and                   *)
(*  [ftvar_in_aenv Θ0' ⊆ S0] cover every use, and both are re-established  *)
(*  at the output ([e_consis_sound] + [a_assign_unify_consis_uniq], and    *)
(*  [e_assign_unify_consis_ctx_ftvar]).  That is what made the arrow row   *)
(*  tractable — see the hand-off §8c.32.                                   *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  THE MOTIVES                                                           *)
(* ===================================================================== *)

Definition lift_assign_post (Θ0 Ξ : aenv) (P : pskl) (Θ1 : aenv)
    (S0 : atoms) (Θ0' Ξ' : aenv) (α' : atom) (P' : pskl)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1',
    {{ S0 ↝ S1 ⊨ Θ0' ⊲[ Ξ' ] α' ≔ P' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_ext ρe (ftvar_in_aenv (Ξ ++ Θ0)) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_assign_concl (Θ0 Ξ : aenv) (α : atom) (P : pskl)
    (Θ1 : aenv) : Prop :=
  forall S0 Θ0' Ξ' α' P' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_aenv ρ V Ξ Ξ' ->
    rel_atom ρ V α α' ->
    rel_pskl ρ V P P' ->
    flex_agree_rel ρ V (Ξ ++ Θ0) (Ξ' ++ Θ0') ->
    rel_inj ρ V ->
    rel_fun ρ V (dom (Ξ ++ Θ0)) ->
    a_flex_tvar (Ξ ++ Θ0) α ->
    {{ ⊢ (Ξ ++ Θ0) }}a ->
    a_decls Ξ ->
    a_decls Ξ' ->
    uniq (Ξ' ++ Θ0') ->
    ftvar_in_aenv (Ξ' ++ Θ0') [<=] S0 ->
    V [<=] ftvar_in_aenv (Ξ ++ Θ0) ->
    (forall a, a `in` dom Θ1 -> a `notin` dom (Ξ ++ Θ0) -> a `notin` cols_l ρ) ->
    dom (Ξ' ++ Θ0') [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P' [<=] S0 ->
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a ->
    lift_assign_post Θ0 Ξ P Θ1 S0 Θ0' Ξ' α' P' ρ V.

Definition lift_unify_post (Θ0 : aenv) (Θ1 : aenv)
    (S0 : atoms) (Θ0' : aenv) (α' β' : atom)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1',
    {{ S0 ↝ S1 ⊨ Θ0' ⊲ α' ≈ᵘ β' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_unify_concl (Θ0 : aenv) (α β : atom) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' α' β' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_atom ρ V α α' ->
    rel_atom ρ V β β' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    a_flex_tvar Θ0 α ->
    a_flex_tvar Θ0 β ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    lift_unify_post Θ0 Θ1 S0 Θ0' α' β' ρ V.

Definition lift_consis_post (Θ0 : aenv) (Q : pskl) (Θ1 : aenv)
    (S0 : atoms) (Θ0' : aenv) (Δ1' Δ2' : atoms) (P0' P' : pskl)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' Q',
    {{ S0 ↝ S1 ⊨ Θ0' ⊢[ Δ1' | Δ2' | P0' ] P' ∼ Q' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_consis_concl (Δ1 Δ2 : atoms) (Θ0 : aenv)
    (P0 P Q : pskl) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' Δ1' Δ2' P0' P' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    rel_pskl ρ V P P' ->
    rel_atoms ρ V Δ1 Δ1' ->
    rel_atoms ρ V Δ2 Δ2' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' ∪ ftvar_in_pskl P' [<=] S0 ->
    Δ1' ∪ Δ2' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
    (forall α, α `in` (Δ1 ∪ Δ2) -> binds α abind_tvar Θ0) ->
    no_flex_dep (Δ1 ∪ Δ2) Θ0 ->
    flex_above_free (Δ1 ∪ Δ2) Θ0 ->
    Δ1 ∪ Δ2 [<=] ftvar_in_aenv Θ0 ->
    lift_consis_post Θ0 Q Θ1 S0 Θ0' Δ1' Δ2' P0' P' ρ V.

Lemma rel_aenv_nil_inv_l : forall ρ V Θ2,
  rel_aenv ρ V nil Θ2 -> Θ2 = nil.
Proof. intros ρ V Θ2 H; inversion H; reflexivity. Qed.


(* ===================================================================== *)
(*  ⭐⭐ THE ∀ ROWS' SHARED CLOSER                                          *)
(*                                                                        *)
(*  All three binder rows of [a_consis] restrict ρ, push the opener PAIR,  *)
(*  run the premise and then have to hand the caller a relation that no    *)
(*  longer mentions either opener.  Everything after the IH is the same    *)
(*  for the three, so it lives here once.  The one step that is not        *)
(*  bookkeeping is the DELETED PAIR: [flex_agree_rel] is ANTITONE, so the  *)
(*  conclusion still owes an answer at every [(α, b) ∈ ρ] that             *)
(*  [restrict_pairs] threw away — and both halves are FALSE, side 1's      *)
(*  because the opener never reaches its own output and side 2's because   *)
(*  an OLD atom the input agreed was rigid cannot become flexible          *)
(*  ([a_assign_unify_consis_flex_rev], through [e_consis_sound]).          *)
(* ===================================================================== *)

Lemma lift_consis_forall_close :
  forall Θ0 Θ1 Q α S0 Θ0' Δ1' Δ2' P0' P' ρ V α2 S1 ρe Θ1' Q',
  {{ ⊢ ((α ~ abind_tvar) ++ Θ1) }}a ->
  α `notin` dom Θ0 ->
  α `notin` V ->
  α2 `notin` V ->
  α2 `notin` cols_r ρ ->
  uniq ((α2 ~ abind_tvar) ++ Θ1') ->
  uniq Θ0' ->
  flex_agree_rel ρ V Θ0 Θ0' ->
  rel_inj ((α, α2) :: restrict_pairs α α2 ρ) V ->
  rel_ext ρe (ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0)) (add α2 S0) ->
  V ∪ cols_r ((α, α2) :: restrict_pairs α α2 ρ) [<=] add α2 S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  rel_aenv (ρe ++ (α, α2) :: restrict_pairs α α2 ρ) V
    ((α ~ abind_tvar) ++ Θ1) ((α2 ~ abind_tvar) ++ Θ1') ->
  flex_agree_rel (ρe ++ (α, α2) :: restrict_pairs α α2 ρ) V
    ((α ~ abind_tvar) ++ Θ1) ((α2 ~ abind_tvar) ++ Θ1') ->
  rel_pskl (ρe ++ (α, α2) :: restrict_pairs α α2 ρ) V Q Q' ->
  (forall a b, In (a, b) ρe ->
     a `in` dom ((α ~ abind_tvar) ++ Θ1)
     /\ b `in` dom ((α2 ~ abind_tvar) ++ Θ1')) ->
  {{ S0 ↝ S1 ⊨ Θ0' ⊢[ Δ1' | Δ2' | P0' ] P'
     ∼ (pskl_all_syn (close_pskl_wrt_pskl α2 Q')) ⊣ Θ1' }}e ->
  ftvar_in_aenv Θ0' ∪ ftvar_in_pskl P0' ∪ ftvar_in_pskl P' ∪ Δ1' ∪ Δ2'
    [<=] S0 ->
  lift_consis_post Θ0 (pskl_all_syn (close_pskl_wrt_pskl α Q)) Θ1
    S0 Θ0' Δ1' Δ2' P0' P' ρ V.
Proof.
  intros Θ0 Θ1 Q α S0 Θ0' Δ1' Δ2' P0' P' ρ V α2 S1 ρe Θ1' Q'
    Hwf1α Hαd HαV Hα2V Hα2c Huq1out Huq2p Hagr Hinj' Hext Hcov' Hcov
    HrΘout Hagrout HrQ Hdomout Dc HcovC.
  assert (HαΘ1 : α `notin` dom Θ1) by (inversion Hwf1α; subst; assumption).
  assert (HwfΘ1 : {{ ⊢ Θ1 }}a) by (inversion Hwf1α; subst; assumption).
  assert (HαfΘ1 : α `notin` ftvar_in_aenv Θ1).
  { pose proof (a_wf_aenv_ftv_dom HwfΘ1) as Hs. clear - HαΘ1 Hs. fsetdec. }
  assert (Hα2Θ1 : α2 `notin` dom Θ1') by (clear - Huq1out; solve_uniq).
  (* ---- the pair list the premise ran at, and its injectivity ---- *)
  assert (Hinjout : rel_inj (ρe ++ (α, α2) :: restrict_pairs α α2 ρ) V)
    by (eapply rel_inj_app; [ exact Hinj' | exact Hext | exact Hcov' ]).
  assert (Hαρe : forall b, ~ In (α, b) ρe).
  { intros b Hin. destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin) as [Hna _].
    apply Hna. simpl. clear; fsetdec. }
  assert (Hα2ρe : forall a, ~ In (a, α2) ρe).
  { intros a Hin. destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin) as [_ Hnb].
    apply Hnb. clear; fsetdec. }
  (* ⭐ the opener is related to ITS OWN counterpart and to nothing else *)
  assert (Hαonly : forall y,
            rel_atom (ρe ++ (α, α2) :: restrict_pairs α α2 ρ) V α y -> y = α2).
  { intros y Hat. inversion Hat as [ a0 b0 Hin | a0 HinV ]; subst.
    - apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
      + exfalso. exact (Hαρe _ Hin).
      + inversion Ehd; reflexivity.
      + exfalso. apply (@restrict_pairs_notin_l α α2 ρ).
        eapply cols_l_in; exact Hin.
    - exfalso. exact (HαV HinV). }
  (* ---- peel the opener off BOTH contexts ---- *)
  inversion HrΘout as [ | a0 b0 bd1 bd2 Θa Θb Hat0 Hbd0 HrΘtail Ea Eb ]; subst.
  assert (Hα2fΘ1 : α2 `notin` ftvar_in_aenv Θ1').
  { intros Hin. destruct (rel_aenv_ftv_corr_r HrΘtail Hin) as (a & Ha & Hat).
  assert (Ea2 : a = α).
    { apply (Hinjout a α α2 Hat). apply rel_atom__pair.
      apply in_or_app; right; left; reflexivity. }
    subst a. exact (HαfΘ1 Ha). }
  (* ---- the CONTEXT relation, back at the caller's pair list ---- *)
  assert (HrΘfin : rel_aenv (ρe ++ ρ) V Θ1 Θ1').
  { eapply rel_aenv_mono;
      [ exact (rel_aenv_restrict HrΘtail HαfΘ1 Hα2fΘ1)
      | | intros x Hx; exact Hx ].
  intros a b Hin.
  assert (Hnl : a <> α).
    { intros ->.
      apply (@restrict_pairs_notin_l α α2
               (ρe ++ (α, α2) :: restrict_pairs α α2 ρ)).
      eapply cols_l_in; exact Hin. }
    apply restrict_pairs_incl in Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
    - apply in_or_app; left; exact Hin.
    - exfalso. injection Ehd as E1 E2. apply Hnl. symmetry. exact E1.
    - apply in_or_app; right. eapply restrict_pairs_incl; exact Hin. }
  (* ---- and the FLEX AGREEMENT, which is where the owed fact is spent ---- *)
  assert (Hagrpeel : flex_agree_rel (ρe ++ (α, α2) :: restrict_pairs α α2 ρ)
                       V Θ1 Θ1').
  { eapply flex_agree_peel_cons;
      [ exact Hagrout
      | apply rel_atom__pair; apply in_or_app; right; left; reflexivity
      | exact Hinjout
      | exact Hαonly
      | exact HαΘ1
      | exact Hα2Θ1
      | intros x Hx; exact Hx
      | intros y Hy Ey; subst; contradiction ]. }
  assert (Hagrfin : flex_agree_rel (ρe ++ ρ) V Θ1 Θ1').
  { destruct Hagrpeel as [HagV Hagp]. split; [ exact HagV | ].
  intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - apply Hagp. apply in_or_app; left; exact Hin.
    - destruct (a == α) as [-> | Hne].
      + (* ⭐ THE PAIR [restrict_pairs] DELETED: both halves are FALSE *)
      assert (Hb2 : ~ a_flex_tvar Θ1' b).
        { intros Hf.
        assert (Hbd : b `in` dom Θ1') by (apply a_flex_tvar_in_dom; exact Hf).
        assert (HbS0 : b `in` S0).
          { assert (Hc : b `in` cols_r ρ) by (eapply cols_r_in; exact Hin).
            clear - Hc Hcov. fsetdec. }
        assert (Hb0 : b `in` dom Θ0').
          { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                          _ _ _ _ _ _ _ _ _ Dc) as Hup.
            clear - Hbd HbS0 Hup. fsetdec. }
          pose proof (e_consis_sound Dc Huq2p HcovC) as HaDc.
        assert (Hf0 : a_flex_tvar Θ0' b)
            by (exact ((proj2 (proj2 a_assign_unify_consis_flex_rev))
                         _ _ _ _ _ _ _ HaDc b Hb0 Hf)).
          apply Hαd. apply a_flex_tvar_in_dom.
          exact (proj2 (proj2 Hagr α b Hin) Hf0). }
      split; intros Hf; exfalso;
          [ apply HαΘ1; apply a_flex_tvar_in_dom; exact Hf | exact (Hb2 Hf) ].
      + assert (Hbne : b <> α2)
          by (intros ->; apply Hα2c; eapply cols_r_in; exact Hin).
        apply Hagp. apply in_or_app; right; right.
        apply restrict_pairs_in; assumption. }
  (* ---- assemble ---- *)
  exists S1, ρe, Θ1', (pskl_all_syn (close_pskl_wrt_pskl α2 Q')).
  split; [ exact Dc | ].
  split; [ exact HrΘfin | ].
  split; [ exact Hagrfin | ].
  split.
  { apply rel_pskl__all_syn.
    eapply rel_pskl_close_pair_restrict;
      [ exact HrQ | exact HαV
      | intros Hc; destruct (cols_l_in_inv _ _ Hc) as [y Hin];
        exact (Hαρe _ Hin)
      | exact Hα2V
      | intros Hc; destruct (cols_r_in_inv _ _ Hc) as [y Hin];
        exact (Hα2ρe _ Hin)
      | intros a b Hin; apply in_or_app; left; exact Hin
      | intros a b Hin; apply in_or_app; right; exact Hin ]. }
  split.
  { destruct Hext as [Hxfr [Hri Hlf]]. split; [ | split; assumption ].
  intros a b Hin. destruct (Hxfr _ _ Hin) as [Hna Hnb].
  simpl in Hna. split; [ clear - Hna; fsetdec | clear - Hnb; fsetdec ]. }
  intros a b Hin. destruct (Hdomout _ _ Hin) as [Hd1 Hd2].
  assert (Hne1 : a <> α) by (intros ->; exact (Hαρe _ Hin)).
  assert (Hne2 : b <> α2) by (intros ->; exact (Hα2ρe _ Hin)).
  simpl in Hd1, Hd2.
  split; [ clear - Hd1 Hne1; fsetdec | clear - Hd2 Hne2; fsetdec ].
Qed.

Lemma lift_consis_forall_inh_row : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,
  α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
    `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
  {{ ((α ~ abind_tvar) ++ Θ0)
     ⊢[ (add α Δ1) | (add α Δ2) | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ] (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
     ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
  lift_consis_concl (add α Δ1) (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
    (open_pskl_wrt_pskl P0 (pskl_var_f α)) (open_pskl_wrt_pskl P (pskl_var_f α)) Q ((α ~ abind_tvar) ++ Θ1) ->
  lift_consis_concl Δ1 Δ2 Θ0 (pskl_all_syn P0) (pskl_all_syn P)
    (pskl_all_syn (close_pskl_wrt_pskl α Q)) Θ1.
Proof.
  intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
  intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
    Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
    Hfaf HΔsc.
  inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 P0b2 HrP0b | | C1 C2 Hu3 ]; subst.
  inversion HrP as [ | n1 | u3 v3 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 P12 HrPb | | F1 F2 Hu7 ]; subst.
  destruct (atom_fresh S0) as [α2 Hα2].
  assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HfrΘ : α `notin` ftvar_in_aenv Θ0) by (clear - Hfr; solve_notin_auto).
  assert (HfrP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfr; solve_notin_auto).
  assert (HfrP : α `notin` ftvar_in_pskl P) by (clear - Hfr; solve_notin_auto).
  assert (HfrD1 : α `notin` Δ1) by (clear - Hfr; solve_notin_auto).
  assert (HfrD2 : α `notin` Δ2) by (clear - Hfr; solve_notin_auto).
  assert (HαV : α `notin` V) by (intros Hin; apply HfrΘ; apply Hscp; exact Hin).
  assert (Hαd : α `notin` dom Θ0)
    by (intros Hin; apply HfrΘ; apply (dom_subset_ftvar_in_aenv Θ0); exact Hin).
  assert (Hα2d : α2 `notin` dom Θ0') by (clear - Hα2 HdΘ; fsetdec).
  assert (Hα2V : α2 `notin` V) by (clear - Hα2 Hcov; fsetdec).
  assert (Hα2c : α2 `notin` cols_r ρ) by (clear - Hα2 Hcov; fsetdec).
  assert (Hα2f : α2 `notin` ftvar_in_aenv Θ0') by (clear - Hα2 Hftv2; fsetdec).
  assert (Hα2D1 : α2 `notin` Δ1') by (clear - Hα2 HcovΔ; fsetdec).
  assert (Hα2D2 : α2 `notin` Δ2') by (clear - Hα2 HcovΔ; fsetdec).
  (* ---- the PAIR RESTRICTION, then the push ---- *)
  assert (Hcl0 : cols_l (restrict_pairs α α2 ρ) [<=] cols_l ρ)
    by apply cols_l_restrict_pairs.
  assert (Hcr0 : cols_r (restrict_pairs α α2 ρ) [<=] cols_r ρ)
    by apply cols_r_restrict_pairs.
  assert (Hαl : α `notin` cols_l (restrict_pairs α α2 ρ))
    by apply restrict_pairs_notin_l.
  assert (Hα2r : α2 `notin` cols_r (restrict_pairs α α2 ρ))
    by apply restrict_pairs_notin_r.
  assert (HrΘr : rel_aenv (restrict_pairs α α2 ρ) V Θ0 Θ0')
    by (apply rel_aenv_restrict; [ exact HrΘ | exact HfrΘ | exact Hα2f ]).
  assert (HrΘ' : rel_aenv ((α, α2) :: restrict_pairs α α2 ρ) V
                   ((α ~ abind_tvar) ++ Θ0) ((α2 ~ abind_tvar) ++ Θ0')).
  { apply rel_aenv__cons;
      [ apply rel_atom__pair; left; reflexivity | constructor | ].
    eapply rel_aenv_mono;
      [ exact HrΘr | intros x y Hx; right; exact Hx | intros x Hx; exact Hx ]. }
  assert (HrP0r : rel_pskl (restrict_pairs α α2 ρ) V P0 P0b2)
    by (apply rel_pskl_restrict;
        [ exact HrP0b | clear - HfrP0; simpl in HfrP0; fsetdec
        | clear - Hα2 HcovP; simpl in HcovP; fsetdec ]).
  assert (HrPr : rel_pskl (restrict_pairs α α2 ρ) V P P12)
    by (apply rel_pskl_restrict;
        [ exact HrPb | clear - HfrP; simpl in HfrP; fsetdec
        | clear - Hα2 HcovP; simpl in HcovP; fsetdec ]).
  assert (HrP0' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ) V (open_pskl_wrt_pskl P0 (pskl_var_f α)) (open_pskl_wrt_pskl P0b2 (pskl_var_f α2)))
    by (apply rel_pskl_open_pair; exact HrP0r).
  assert (HrP' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ) V (open_pskl_wrt_pskl P (pskl_var_f α)) (open_pskl_wrt_pskl P12 (pskl_var_f α2)))
    by (apply rel_pskl_open_pair; exact HrPr).
  assert (Hrd1' : rel_atoms ((α, α2) :: restrict_pairs α α2 ρ) V (add α Δ1) (add α2 Δ1'))
    by (apply rel_atoms_push;
        [ eapply rel_atoms_weaken;
            [ exact Hrd1 | intros x y Hx; eapply restrict_pairs_incl; exact Hx
            | intros x Hx; exact Hx ]
        | exact HαV | exact Hαl | exact Hα2V | exact Hα2r ]).
  assert (Hrd2' : rel_atoms ((α, α2) :: restrict_pairs α α2 ρ) V (add α Δ2) (add α2 Δ2'))
    by (apply rel_atoms_push;
        [ eapply rel_atoms_weaken;
            [ exact Hrd2 | intros x y Hx; eapply restrict_pairs_incl; exact Hx
            | intros x Hx; exact Hx ]
        | exact HαV | exact Hαl | exact Hα2V | exact Hα2r ]).
  assert (Hagr' : flex_agree_rel ((α, α2) :: restrict_pairs α α2 ρ) V
                    ((α ~ abind_tvar) ++ Θ0) ((α2 ~ abind_tvar) ++ Θ0')).
  { apply flex_agree_rel_push_look; [ | exact Hαd | exact Hα2d ].
    eapply flex_agree_rel_weaken;
      [ exact Hagr | intros x y Hx; eapply restrict_pairs_incl; exact Hx
      | intros x Hx; exact Hx ]. }
  assert (Hinj' : rel_inj ((α, α2) :: restrict_pairs α α2 ρ) V)
    by (apply rel_inj_push;
        [ eapply rel_inj_sub;
            [ exact Hinj | intros x y Hx; eapply restrict_pairs_incl; exact Hx ]
        | exact Hα2V | exact Hα2r ]).
  assert (Hfun' : rel_fun ((α, α2) :: restrict_pairs α α2 ρ) V
                    (dom ((α ~ abind_tvar) ++ Θ0))).
  { simpl. apply rel_fun_push;
      [ eapply rel_fun_weaken;
          [ exact Hfun | intros x y Hx; eapply restrict_pairs_incl; exact Hx
          | intros x Hx; exact Hx ]
      | exact HαV | exact Hαl ]. }
  assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
    by (apply a_wf_aenv__tvar; [ exact Hαd | exact Hwf ]).
  assert (Huq2' : uniq ((α2 ~ abind_tvar) ++ Θ0'))
    by (clear - Huq2p Hα2d; solve_uniq).
  assert (Hftv2' : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0') [<=] add α2 S0)
    by (simpl; clear - Hftv2; fsetdec).
  assert (Hscp' : V [<=] ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0))
    by (simpl; clear - Hscp; fsetdec).
  assert (Hblk' : forall a, a `in` dom ((α ~ abind_tvar) ++ Θ1) ->
            a `notin` dom ((α ~ abind_tvar) ++ Θ0) ->
            a `notin` cols_l ((α, α2) :: restrict_pairs α α2 ρ)).
  { intros a Ha Hn. simpl in Ha, Hn |- *.
    assert (Hne : a <> α) by (clear - Hn; fsetdec).
    assert (Hc : a `notin` cols_l ρ)
      by (apply Hblk; [ clear - Ha Hne; fsetdec | clear - Hn; fsetdec ]).
    clear - Hne Hc Hcl0. fsetdec. }
  assert (HdΘ' : dom ((α2 ~ abind_tvar) ++ Θ0') [<=] add α2 S0)
    by (simpl; clear - HdΘ; fsetdec).
  assert (Hcov' : V ∪ cols_r ((α, α2) :: restrict_pairs α α2 ρ)
                  [<=] add α2 S0)
    by (simpl; clear - Hcov Hcr0; fsetdec).
  assert (HcovP' : ftvar_in_pskl (open_pskl_wrt_pskl P0b2 (pskl_var_f α2)) ∪ ftvar_in_pskl (open_pskl_wrt_pskl P12 (pskl_var_f α2))
                   [<=] add α2 S0).
  { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0b2
                  (pskl_var_f α2)) as Hu1.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P12
                  (pskl_var_f α2)) as Hu2.
    simpl in Hu1, Hu2, HcovP. clear - Hu1 Hu2 HcovP. fsetdec. }
  assert (HcovΔ' : (add α2 Δ1') ∪ (add α2 Δ2') [<=] add α2 S0)
    by (clear - HcovΔ; fsetdec).
  assert (Hwfp0' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (open_pskl_wrt_pskl P0 (pskl_var_f α)) }}a)
    by (apply a_wf_pskl_all_syn_open_tvar;
        [ exact Hwfp0 | clear - Hαd HfrP0; fsetdec ]).
  assert (Hwfp' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (open_pskl_wrt_pskl P (pskl_var_f α)) }}a)
    by (apply a_wf_pskl_all_syn_open_tvar;
        [ exact Hwfp | clear - Hαd HfrP; fsetdec ]).
  assert (HΔtv' : forall γ, γ `in` ((add α Δ1) ∪ (add α Δ2)) ->
            binds γ abind_tvar ((α ~ abind_tvar) ++ Θ0)).
  { intros γ Hγ. destruct (γ == α) as [-> | Hne].
    - unfold binds; simpl; left; reflexivity.
    - unfold binds; simpl; right. apply HΔtv. clear - Hγ Hne. fsetdec. }
  assert (Hnfd' : no_flex_dep ((add α Δ1) ∪ (add α Δ2)) ((α ~ abind_tvar) ++ Θ0)).
  { intros γ t Hb. unfold binds in Hb; simpl in Hb.
    destruct Hb as [E | Hb]; [ inversion E | ].
    pose proof (Hnfd γ t Hb) as Hd.
    assert (Hτ : ftvar_in_ptyp t [<=] dom Θ0).
    { apply a_wf_ptyp_ftv_dom.
      eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb ]. }
    clear - Hd Hτ Hαd. fsetdec. }
  assert (Hfaf' : flex_above_free ((add α Δ1) ∪ (add α Δ2)) ((α ~ abind_tvar) ++ Θ0)).
  { intros Θa γ bb Θb Heq Hne.
    destruct Θa as [ | [z bz] Θa ]; simpl in Heq.
    - injection Heq as E1 E2 E3. exfalso. apply Hne. symmetry. exact E2.
    - injection Heq as E1 E2 E3.
      pose proof (Hfaf Θa γ bb Θb E3 Hne) as Hd.
      assert (Hαn : α `notin` dom (Θa ++ (γ, bb) :: Θb))
        by (rewrite <- E3; exact Hαd).
      rewrite dom_app in Hαn. simpl in Hαn.
      assert (Hαn2 : α `notin` add γ (dom Θb)) by (clear - Hαn; fsetdec).
      apply (inter_empty_cong_l (D := add α (Δ1 ∪ Δ2)));
        [ clear; fsetdec | apply inter_empty_add; [ exact Hd | exact Hαn2 ] ]. }
  assert (HΔsc' : (add α Δ1) ∪ (add α Δ2)
                  [<=] ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0))
    by (simpl; clear - HΔsc; fsetdec).
  destruct (IH (add α2 S0) ((α2 ~ abind_tvar) ++ Θ0') (add α2 Δ1') (add α2 Δ2')
              (open_pskl_wrt_pskl P0b2 (pskl_var_f α2)) (open_pskl_wrt_pskl P12 (pskl_var_f α2)) ((α, α2) :: restrict_pairs α α2 ρ) V
              HrΘ' HrP0' HrP' Hrd1' Hrd2' Hagr' Hinj' Hfun' Hwf' Huq2' Hftv2'
              Hscp' Hblk' HdΘ' Hcov' HcovP' HcovΔ' Hwfp0' Hwfp' HΔtv' Hnfd'
              Hfaf' HΔsc')
    as (S1 & ρe & Θ1out & Q' & De & HrΘout & Hagrout & HrQ & Hext & Hdomout).
  (* ---- side 1's output context, via SOUNDNESS of the premise ---- *)
  pose proof ((proj2 (proj2 a_assign_unify_consis_sound)) _ _ _ _ _ _ _ HD
                Hwf' Hwfp0' Hwfp' HΔtv' Hnfd' Hfaf') as Hsnd.
  destruct Hsnd as (Hinc1 & HwfΘ1α & Hdmp & HΔinv & Hrest).
  (* ---- side 2's output: the OPENER SURVIVES as a rigid prefix ---- *)
  assert (HcovS : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0')
                  ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0b2 (pskl_var_f α2)) ∪ ftvar_in_pskl (open_pskl_wrt_pskl P12 (pskl_var_f α2))
                  ∪ (add α2 Δ1') ∪ (add α2 Δ2') [<=] add α2 S0).
  { repeat apply AtomSetProperties.union_subset_3;
      [ exact Hftv2'
      | clear - HcovP'; fsetdec | clear - HcovP'; fsetdec
      | clear - HcovΔ'; fsetdec | clear - HcovΔ'; fsetdec ]. }
  pose proof (e_consis_sound De Huq2' HcovS) as HaD.
  destruct ((proj2 (proj2 a_assign_unify_consis_tvar_prefix))
              _ _ _ _ _ _ _ HaD (α2 ~ abind_tvar) Θ0' eq_refl
              (@tvar_prefix_cons α2 nil tvar_prefix_nil)) as (Θ1' & Eout).
  subst Θ1out.
  assert (Huq1out : uniq ((α2 ~ abind_tvar) ++ Θ1'))
    by (exact ((proj2 (proj2 a_assign_unify_consis_uniq))
                 _ _ _ _ _ _ _ HaD Huq2')).
  (* ---- the e-side conclusion, and the shared closer ---- *)
  assert (Dc : {{ S0 ↝ S1 ⊨ Θ0' ⊢[ Δ1' | Δ2' | (pskl_all_syn P0b2) ] (pskl_all_syn P12)
                  ∼ (pskl_all_syn (close_pskl_wrt_pskl α2 Q')) ⊣ Θ1' }}e)
    by (apply e_consis__forall_inh with (α := α2); [ exact Hα2 | exact De ]).
  assert (HcovC : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl (pskl_all_syn P0b2)
                  ∪ ftvar_in_pskl (pskl_all_syn P12) ∪ Δ1' ∪ Δ2' [<=] S0).
  { repeat apply AtomSetProperties.union_subset_3;
      [ exact Hftv2
      | clear - HcovP; simpl in HcovP |- *; fsetdec
      | clear - HcovP; simpl in HcovP |- *; fsetdec
      | clear - HcovΔ; fsetdec | clear - HcovΔ; fsetdec ]. }
  eapply lift_consis_forall_close;
    [ exact HwfΘ1α | exact Hαd | exact HαV | exact Hα2V | exact Hα2c
    | exact Huq1out | exact Huq2p | exact Hagr | exact Hinj' | exact Hext
    | exact Hcov' | exact Hcov | exact HrΘout | exact Hagrout | exact HrQ
    | exact Hdomout | exact Dc | exact HcovC ].
Qed.

Lemma lift_consis_forall_syn_row : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,
  α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
    `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
  {{ ((α ~ abind_tvar) ++ Θ0)
     ⊢[ Δ1 | (add α Δ2) | (pskl_tophole P0) ] (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
     ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
  lift_consis_concl Δ1 (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
    (pskl_tophole P0) (open_pskl_wrt_pskl P (pskl_var_f α)) Q ((α ~ abind_tvar) ++ Θ1) ->
  lift_consis_concl Δ1 Δ2 Θ0 (pskl_tophole P0) (pskl_all_syn P)
    (pskl_all_syn (close_pskl_wrt_pskl α Q)) Θ1.
Proof.
  intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
  intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
    Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
    Hfaf HΔsc.
  inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3 | | C1 P0b2 HrP0b ]; subst.
  inversion HrP as [ | n1 | u3 v3 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 P12 HrPb | | F1 F2 Hu7 ]; subst.
  destruct (atom_fresh S0) as [α2 Hα2].
  assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HfrΘ : α `notin` ftvar_in_aenv Θ0) by (clear - Hfr; solve_notin_auto).
  assert (HfrP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfr; solve_notin_auto).
  assert (HfrP : α `notin` ftvar_in_pskl P) by (clear - Hfr; solve_notin_auto).
  assert (HfrD1 : α `notin` Δ1) by (clear - Hfr; solve_notin_auto).
  assert (HfrD2 : α `notin` Δ2) by (clear - Hfr; solve_notin_auto).
  assert (HαV : α `notin` V) by (intros Hin; apply HfrΘ; apply Hscp; exact Hin).
  assert (Hαd : α `notin` dom Θ0)
    by (intros Hin; apply HfrΘ; apply (dom_subset_ftvar_in_aenv Θ0); exact Hin).
  assert (Hα2d : α2 `notin` dom Θ0') by (clear - Hα2 HdΘ; fsetdec).
  assert (Hα2V : α2 `notin` V) by (clear - Hα2 Hcov; fsetdec).
  assert (Hα2c : α2 `notin` cols_r ρ) by (clear - Hα2 Hcov; fsetdec).
  assert (Hα2f : α2 `notin` ftvar_in_aenv Θ0') by (clear - Hα2 Hftv2; fsetdec).
  assert (Hα2D1 : α2 `notin` Δ1') by (clear - Hα2 HcovΔ; fsetdec).
  assert (Hα2D2 : α2 `notin` Δ2') by (clear - Hα2 HcovΔ; fsetdec).
  (* ---- the PAIR RESTRICTION, then the push ---- *)
  assert (Hcl0 : cols_l (restrict_pairs α α2 ρ) [<=] cols_l ρ)
    by apply cols_l_restrict_pairs.
  assert (Hcr0 : cols_r (restrict_pairs α α2 ρ) [<=] cols_r ρ)
    by apply cols_r_restrict_pairs.
  assert (Hαl : α `notin` cols_l (restrict_pairs α α2 ρ))
    by apply restrict_pairs_notin_l.
  assert (Hα2r : α2 `notin` cols_r (restrict_pairs α α2 ρ))
    by apply restrict_pairs_notin_r.
  assert (HrΘr : rel_aenv (restrict_pairs α α2 ρ) V Θ0 Θ0')
    by (apply rel_aenv_restrict; [ exact HrΘ | exact HfrΘ | exact Hα2f ]).
  assert (HrΘ' : rel_aenv ((α, α2) :: restrict_pairs α α2 ρ) V
                   ((α ~ abind_tvar) ++ Θ0) ((α2 ~ abind_tvar) ++ Θ0')).
  { apply rel_aenv__cons;
      [ apply rel_atom__pair; left; reflexivity | constructor | ].
    eapply rel_aenv_mono;
      [ exact HrΘr | intros x y Hx; right; exact Hx | intros x Hx; exact Hx ]. }
  assert (HrP0r : rel_pskl (restrict_pairs α α2 ρ) V P0 P0b2)
    by (apply rel_pskl_restrict;
        [ exact HrP0b | clear - HfrP0; simpl in HfrP0; fsetdec
        | clear - Hα2 HcovP; simpl in HcovP; fsetdec ]).
  assert (HrPr : rel_pskl (restrict_pairs α α2 ρ) V P P12)
    by (apply rel_pskl_restrict;
        [ exact HrPb | clear - HfrP; simpl in HfrP; fsetdec
        | clear - Hα2 HcovP; simpl in HcovP; fsetdec ]).
  assert (HrP0' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ) V (pskl_tophole P0) (pskl_tophole P0b2))
    by (apply rel_pskl__tophole; eapply rel_pskl_mono;
        [ exact HrP0r | intros x y Hx; right; exact Hx
        | intros x Hx; exact Hx ]).
  assert (HrP' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ) V (open_pskl_wrt_pskl P (pskl_var_f α)) (open_pskl_wrt_pskl P12 (pskl_var_f α2)))
    by (apply rel_pskl_open_pair; exact HrPr).
  assert (Hrd1' : rel_atoms ((α, α2) :: restrict_pairs α α2 ρ) V Δ1 Δ1')
    by (apply rel_atoms_push_absent;
        [ eapply rel_atoms_weaken;
            [ exact Hrd1 | intros x y Hx; eapply restrict_pairs_incl; exact Hx
            | intros x Hx; exact Hx ]
        | exact HαV | exact Hαl | exact Hα2V | exact Hα2r
        | exact HfrD1 | exact Hα2D1 ]).
  assert (Hrd2' : rel_atoms ((α, α2) :: restrict_pairs α α2 ρ) V (add α Δ2) (add α2 Δ2'))
    by (apply rel_atoms_push;
        [ eapply rel_atoms_weaken;
            [ exact Hrd2 | intros x y Hx; eapply restrict_pairs_incl; exact Hx
            | intros x Hx; exact Hx ]
        | exact HαV | exact Hαl | exact Hα2V | exact Hα2r ]).
  assert (Hagr' : flex_agree_rel ((α, α2) :: restrict_pairs α α2 ρ) V
                    ((α ~ abind_tvar) ++ Θ0) ((α2 ~ abind_tvar) ++ Θ0')).
  { apply flex_agree_rel_push_look; [ | exact Hαd | exact Hα2d ].
    eapply flex_agree_rel_weaken;
      [ exact Hagr | intros x y Hx; eapply restrict_pairs_incl; exact Hx
      | intros x Hx; exact Hx ]. }
  assert (Hinj' : rel_inj ((α, α2) :: restrict_pairs α α2 ρ) V)
    by (apply rel_inj_push;
        [ eapply rel_inj_sub;
            [ exact Hinj | intros x y Hx; eapply restrict_pairs_incl; exact Hx ]
        | exact Hα2V | exact Hα2r ]).
  assert (Hfun' : rel_fun ((α, α2) :: restrict_pairs α α2 ρ) V
                    (dom ((α ~ abind_tvar) ++ Θ0))).
  { simpl. apply rel_fun_push;
      [ eapply rel_fun_weaken;
          [ exact Hfun | intros x y Hx; eapply restrict_pairs_incl; exact Hx
          | intros x Hx; exact Hx ]
      | exact HαV | exact Hαl ]. }
  assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
    by (apply a_wf_aenv__tvar; [ exact Hαd | exact Hwf ]).
  assert (Huq2' : uniq ((α2 ~ abind_tvar) ++ Θ0'))
    by (clear - Huq2p Hα2d; solve_uniq).
  assert (Hftv2' : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0') [<=] add α2 S0)
    by (simpl; clear - Hftv2; fsetdec).
  assert (Hscp' : V [<=] ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0))
    by (simpl; clear - Hscp; fsetdec).
  assert (Hblk' : forall a, a `in` dom ((α ~ abind_tvar) ++ Θ1) ->
            a `notin` dom ((α ~ abind_tvar) ++ Θ0) ->
            a `notin` cols_l ((α, α2) :: restrict_pairs α α2 ρ)).
  { intros a Ha Hn. simpl in Ha, Hn |- *.
    assert (Hne : a <> α) by (clear - Hn; fsetdec).
    assert (Hc : a `notin` cols_l ρ)
      by (apply Hblk; [ clear - Ha Hne; fsetdec | clear - Hn; fsetdec ]).
    clear - Hne Hc Hcl0. fsetdec. }
  assert (HdΘ' : dom ((α2 ~ abind_tvar) ++ Θ0') [<=] add α2 S0)
    by (simpl; clear - HdΘ; fsetdec).
  assert (Hcov' : V ∪ cols_r ((α, α2) :: restrict_pairs α α2 ρ)
                  [<=] add α2 S0)
    by (simpl; clear - Hcov Hcr0; fsetdec).
  assert (HcovP' : ftvar_in_pskl (pskl_tophole P0b2) ∪ ftvar_in_pskl (open_pskl_wrt_pskl P12 (pskl_var_f α2))
                   [<=] add α2 S0).
  { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P12
                  (pskl_var_f α2)) as Hu2.
    simpl in Hu2, HcovP |- *. clear - Hu2 HcovP. fsetdec. }
  assert (HcovΔ' : Δ1' ∪ (add α2 Δ2') [<=] add α2 S0)
    by (clear - HcovΔ; fsetdec).
  assert (Hwfp0' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (pskl_tophole P0) }}a)
    by (eapply a_wf_pskl_weaken_tvarish;
        [ intros γ Hγ; apply (a_binds_tvar_weaken_mid nil (α ~ abind_tvar));
          exact Hγ
        | exact Hwfp0 ]).
  assert (Hwfp' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (open_pskl_wrt_pskl P (pskl_var_f α)) }}a)
    by (apply a_wf_pskl_all_syn_open_tvar;
        [ exact Hwfp | clear - Hαd HfrP; fsetdec ]).
  assert (HΔtv' : forall γ, γ `in` (Δ1 ∪ (add α Δ2)) ->
            binds γ abind_tvar ((α ~ abind_tvar) ++ Θ0)).
  { intros γ Hγ. destruct (γ == α) as [-> | Hne].
    - unfold binds; simpl; left; reflexivity.
    - unfold binds; simpl; right. apply HΔtv. clear - Hγ Hne. fsetdec. }
  assert (Hnfd' : no_flex_dep (Δ1 ∪ (add α Δ2)) ((α ~ abind_tvar) ++ Θ0)).
  { intros γ t Hb. unfold binds in Hb; simpl in Hb.
    destruct Hb as [E | Hb]; [ inversion E | ].
    pose proof (Hnfd γ t Hb) as Hd.
    assert (Hτ : ftvar_in_ptyp t [<=] dom Θ0).
    { apply a_wf_ptyp_ftv_dom.
      eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb ]. }
    clear - Hd Hτ Hαd. fsetdec. }
  assert (Hfaf' : flex_above_free (Δ1 ∪ (add α Δ2)) ((α ~ abind_tvar) ++ Θ0)).
  { intros Θa γ bb Θb Heq Hne.
    destruct Θa as [ | [z bz] Θa ]; simpl in Heq.
    - injection Heq as E1 E2 E3. exfalso. apply Hne. symmetry. exact E2.
    - injection Heq as E1 E2 E3.
      pose proof (Hfaf Θa γ bb Θb E3 Hne) as Hd.
      assert (Hαn : α `notin` dom (Θa ++ (γ, bb) :: Θb))
        by (rewrite <- E3; exact Hαd).
      rewrite dom_app in Hαn. simpl in Hαn.
      assert (Hαn2 : α `notin` add γ (dom Θb)) by (clear - Hαn; fsetdec).
      apply (inter_empty_cong_l (D := add α (Δ1 ∪ Δ2)));
        [ clear; fsetdec | apply inter_empty_add; [ exact Hd | exact Hαn2 ] ]. }
  assert (HΔsc' : Δ1 ∪ (add α Δ2)
                  [<=] ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0))
    by (simpl; clear - HΔsc; fsetdec).
  destruct (IH (add α2 S0) ((α2 ~ abind_tvar) ++ Θ0') Δ1' (add α2 Δ2')
              (pskl_tophole P0b2) (open_pskl_wrt_pskl P12 (pskl_var_f α2)) ((α, α2) :: restrict_pairs α α2 ρ) V
              HrΘ' HrP0' HrP' Hrd1' Hrd2' Hagr' Hinj' Hfun' Hwf' Huq2' Hftv2'
              Hscp' Hblk' HdΘ' Hcov' HcovP' HcovΔ' Hwfp0' Hwfp' HΔtv' Hnfd'
              Hfaf' HΔsc')
    as (S1 & ρe & Θ1out & Q' & De & HrΘout & Hagrout & HrQ & Hext & Hdomout).
  (* ---- side 1's output context, via SOUNDNESS of the premise ---- *)
  pose proof ((proj2 (proj2 a_assign_unify_consis_sound)) _ _ _ _ _ _ _ HD
                Hwf' Hwfp0' Hwfp' HΔtv' Hnfd' Hfaf') as Hsnd.
  destruct Hsnd as (Hinc1 & HwfΘ1α & Hdmp & HΔinv & Hrest).
  (* ---- side 2's output: the OPENER SURVIVES as a rigid prefix ---- *)
  assert (HcovS : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0')
                  ∪ ftvar_in_pskl (pskl_tophole P0b2) ∪ ftvar_in_pskl (open_pskl_wrt_pskl P12 (pskl_var_f α2))
                  ∪ Δ1' ∪ (add α2 Δ2') [<=] add α2 S0).
  { repeat apply AtomSetProperties.union_subset_3;
      [ exact Hftv2'
      | clear - HcovP'; fsetdec | clear - HcovP'; fsetdec
      | clear - HcovΔ'; fsetdec | clear - HcovΔ'; fsetdec ]. }
  pose proof (e_consis_sound De Huq2' HcovS) as HaD.
  destruct ((proj2 (proj2 a_assign_unify_consis_tvar_prefix))
              _ _ _ _ _ _ _ HaD (α2 ~ abind_tvar) Θ0' eq_refl
              (@tvar_prefix_cons α2 nil tvar_prefix_nil)) as (Θ1' & Eout).
  subst Θ1out.
  assert (Huq1out : uniq ((α2 ~ abind_tvar) ++ Θ1'))
    by (exact ((proj2 (proj2 a_assign_unify_consis_uniq))
                 _ _ _ _ _ _ _ HaD Huq2')).
  (* ---- the e-side conclusion, and the shared closer ---- *)
  assert (Dc : {{ S0 ↝ S1 ⊨ Θ0' ⊢[ Δ1' | Δ2' | (pskl_tophole P0b2) ] (pskl_all_syn P12)
                  ∼ (pskl_all_syn (close_pskl_wrt_pskl α2 Q')) ⊣ Θ1' }}e)
    by (apply e_consis__forall_syn with (α := α2); [ exact Hα2 | exact De ]).
  assert (HcovC : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl (pskl_tophole P0b2)
                  ∪ ftvar_in_pskl (pskl_all_syn P12) ∪ Δ1' ∪ Δ2' [<=] S0).
  { repeat apply AtomSetProperties.union_subset_3;
      [ exact Hftv2
      | clear - HcovP; simpl in HcovP |- *; fsetdec
      | clear - HcovP; simpl in HcovP |- *; fsetdec
      | clear - HcovΔ; fsetdec | clear - HcovΔ; fsetdec ]. }
  eapply lift_consis_forall_close;
    [ exact HwfΘ1α | exact Hαd | exact HαV | exact Hα2V | exact Hα2c
    | exact Huq1out | exact Huq2p | exact Hagr | exact Hinj' | exact Hext
    | exact Hcov' | exact Hcov | exact HrΘout | exact Hagrout | exact HrQ
    | exact Hdomout | exact Dc | exact HcovC ].
Qed.

Lemma lift_consis_univ_ghost1_row : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,
  α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
    `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
  {{ ((α ~ abind_tvar) ++ Θ0)
     ⊢[ (add α Δ1) | Δ2 | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ] (pskl_tophole P) ∼ Q
     ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
  lift_consis_concl (add α Δ1) Δ2 ((α ~ abind_tvar) ++ Θ0)
    (open_pskl_wrt_pskl P0 (pskl_var_f α)) (pskl_tophole P) Q ((α ~ abind_tvar) ++ Θ1) ->
  lift_consis_concl Δ1 Δ2 Θ0 (pskl_all_syn P0) (pskl_tophole P)
    (pskl_all_syn (close_pskl_wrt_pskl α Q)) Θ1.
Proof.
  intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
  intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
    Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
    Hfaf HΔsc.
  inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 P0b2 HrP0b | | C1 C2 Hu3 ]; subst.
  inversion HrP as [ | n1 | u3 v3 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7 | | F1 P12 HrPb ]; subst.
  destruct (atom_fresh S0) as [α2 Hα2].
  assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HfrΘ : α `notin` ftvar_in_aenv Θ0) by (clear - Hfr; solve_notin_auto).
  assert (HfrP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfr; solve_notin_auto).
  assert (HfrP : α `notin` ftvar_in_pskl P) by (clear - Hfr; solve_notin_auto).
  assert (HfrD1 : α `notin` Δ1) by (clear - Hfr; solve_notin_auto).
  assert (HfrD2 : α `notin` Δ2) by (clear - Hfr; solve_notin_auto).
  assert (HαV : α `notin` V) by (intros Hin; apply HfrΘ; apply Hscp; exact Hin).
  assert (Hαd : α `notin` dom Θ0)
    by (intros Hin; apply HfrΘ; apply (dom_subset_ftvar_in_aenv Θ0); exact Hin).
  assert (Hα2d : α2 `notin` dom Θ0') by (clear - Hα2 HdΘ; fsetdec).
  assert (Hα2V : α2 `notin` V) by (clear - Hα2 Hcov; fsetdec).
  assert (Hα2c : α2 `notin` cols_r ρ) by (clear - Hα2 Hcov; fsetdec).
  assert (Hα2f : α2 `notin` ftvar_in_aenv Θ0') by (clear - Hα2 Hftv2; fsetdec).
  assert (Hα2D1 : α2 `notin` Δ1') by (clear - Hα2 HcovΔ; fsetdec).
  assert (Hα2D2 : α2 `notin` Δ2') by (clear - Hα2 HcovΔ; fsetdec).
  (* ---- the PAIR RESTRICTION, then the push ---- *)
  assert (Hcl0 : cols_l (restrict_pairs α α2 ρ) [<=] cols_l ρ)
    by apply cols_l_restrict_pairs.
  assert (Hcr0 : cols_r (restrict_pairs α α2 ρ) [<=] cols_r ρ)
    by apply cols_r_restrict_pairs.
  assert (Hαl : α `notin` cols_l (restrict_pairs α α2 ρ))
    by apply restrict_pairs_notin_l.
  assert (Hα2r : α2 `notin` cols_r (restrict_pairs α α2 ρ))
    by apply restrict_pairs_notin_r.
  assert (HrΘr : rel_aenv (restrict_pairs α α2 ρ) V Θ0 Θ0')
    by (apply rel_aenv_restrict; [ exact HrΘ | exact HfrΘ | exact Hα2f ]).
  assert (HrΘ' : rel_aenv ((α, α2) :: restrict_pairs α α2 ρ) V
                   ((α ~ abind_tvar) ++ Θ0) ((α2 ~ abind_tvar) ++ Θ0')).
  { apply rel_aenv__cons;
      [ apply rel_atom__pair; left; reflexivity | constructor | ].
    eapply rel_aenv_mono;
      [ exact HrΘr | intros x y Hx; right; exact Hx | intros x Hx; exact Hx ]. }
  assert (HrP0r : rel_pskl (restrict_pairs α α2 ρ) V P0 P0b2)
    by (apply rel_pskl_restrict;
        [ exact HrP0b | clear - HfrP0; simpl in HfrP0; fsetdec
        | clear - Hα2 HcovP; simpl in HcovP; fsetdec ]).
  assert (HrPr : rel_pskl (restrict_pairs α α2 ρ) V P P12)
    by (apply rel_pskl_restrict;
        [ exact HrPb | clear - HfrP; simpl in HfrP; fsetdec
        | clear - Hα2 HcovP; simpl in HcovP; fsetdec ]).
  assert (HrP0' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ) V (open_pskl_wrt_pskl P0 (pskl_var_f α)) (open_pskl_wrt_pskl P0b2 (pskl_var_f α2)))
    by (apply rel_pskl_open_pair; exact HrP0r).
  assert (HrP' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ) V (pskl_tophole P) (pskl_tophole P12))
    by (apply rel_pskl__tophole; eapply rel_pskl_mono;
        [ exact HrPr | intros x y Hx; right; exact Hx
        | intros x Hx; exact Hx ]).
  assert (Hrd1' : rel_atoms ((α, α2) :: restrict_pairs α α2 ρ) V (add α Δ1) (add α2 Δ1'))
    by (apply rel_atoms_push;
        [ eapply rel_atoms_weaken;
            [ exact Hrd1 | intros x y Hx; eapply restrict_pairs_incl; exact Hx
            | intros x Hx; exact Hx ]
        | exact HαV | exact Hαl | exact Hα2V | exact Hα2r ]).
  assert (Hrd2' : rel_atoms ((α, α2) :: restrict_pairs α α2 ρ) V Δ2 Δ2')
    by (apply rel_atoms_push_absent;
        [ eapply rel_atoms_weaken;
            [ exact Hrd2 | intros x y Hx; eapply restrict_pairs_incl; exact Hx
            | intros x Hx; exact Hx ]
        | exact HαV | exact Hαl | exact Hα2V | exact Hα2r
        | exact HfrD2 | exact Hα2D2 ]).
  assert (Hagr' : flex_agree_rel ((α, α2) :: restrict_pairs α α2 ρ) V
                    ((α ~ abind_tvar) ++ Θ0) ((α2 ~ abind_tvar) ++ Θ0')).
  { apply flex_agree_rel_push_look; [ | exact Hαd | exact Hα2d ].
    eapply flex_agree_rel_weaken;
      [ exact Hagr | intros x y Hx; eapply restrict_pairs_incl; exact Hx
      | intros x Hx; exact Hx ]. }
  assert (Hinj' : rel_inj ((α, α2) :: restrict_pairs α α2 ρ) V)
    by (apply rel_inj_push;
        [ eapply rel_inj_sub;
            [ exact Hinj | intros x y Hx; eapply restrict_pairs_incl; exact Hx ]
        | exact Hα2V | exact Hα2r ]).
  assert (Hfun' : rel_fun ((α, α2) :: restrict_pairs α α2 ρ) V
                    (dom ((α ~ abind_tvar) ++ Θ0))).
  { simpl. apply rel_fun_push;
      [ eapply rel_fun_weaken;
          [ exact Hfun | intros x y Hx; eapply restrict_pairs_incl; exact Hx
          | intros x Hx; exact Hx ]
      | exact HαV | exact Hαl ]. }
  assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
    by (apply a_wf_aenv__tvar; [ exact Hαd | exact Hwf ]).
  assert (Huq2' : uniq ((α2 ~ abind_tvar) ++ Θ0'))
    by (clear - Huq2p Hα2d; solve_uniq).
  assert (Hftv2' : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0') [<=] add α2 S0)
    by (simpl; clear - Hftv2; fsetdec).
  assert (Hscp' : V [<=] ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0))
    by (simpl; clear - Hscp; fsetdec).
  assert (Hblk' : forall a, a `in` dom ((α ~ abind_tvar) ++ Θ1) ->
            a `notin` dom ((α ~ abind_tvar) ++ Θ0) ->
            a `notin` cols_l ((α, α2) :: restrict_pairs α α2 ρ)).
  { intros a Ha Hn. simpl in Ha, Hn |- *.
    assert (Hne : a <> α) by (clear - Hn; fsetdec).
    assert (Hc : a `notin` cols_l ρ)
      by (apply Hblk; [ clear - Ha Hne; fsetdec | clear - Hn; fsetdec ]).
    clear - Hne Hc Hcl0. fsetdec. }
  assert (HdΘ' : dom ((α2 ~ abind_tvar) ++ Θ0') [<=] add α2 S0)
    by (simpl; clear - HdΘ; fsetdec).
  assert (Hcov' : V ∪ cols_r ((α, α2) :: restrict_pairs α α2 ρ)
                  [<=] add α2 S0)
    by (simpl; clear - Hcov Hcr0; fsetdec).
  assert (HcovP' : ftvar_in_pskl (open_pskl_wrt_pskl P0b2 (pskl_var_f α2)) ∪ ftvar_in_pskl (pskl_tophole P12)
                   [<=] add α2 S0).
  { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0b2
                  (pskl_var_f α2)) as Hu1.
    simpl in Hu1, HcovP |- *. clear - Hu1 HcovP. fsetdec. }
  assert (HcovΔ' : (add α2 Δ1') ∪ Δ2' [<=] add α2 S0)
    by (clear - HcovΔ; fsetdec).
  assert (Hwfp0' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (open_pskl_wrt_pskl P0 (pskl_var_f α)) }}a)
    by (apply a_wf_pskl_all_syn_open_tvar;
        [ exact Hwfp0 | clear - Hαd HfrP0; fsetdec ]).
  assert (Hwfp' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (pskl_tophole P) }}a)
    by (eapply a_wf_pskl_weaken_tvarish;
        [ intros γ Hγ; apply (a_binds_tvar_weaken_mid nil (α ~ abind_tvar));
          exact Hγ
        | exact Hwfp ]).
  assert (HΔtv' : forall γ, γ `in` ((add α Δ1) ∪ Δ2) ->
            binds γ abind_tvar ((α ~ abind_tvar) ++ Θ0)).
  { intros γ Hγ. destruct (γ == α) as [-> | Hne].
    - unfold binds; simpl; left; reflexivity.
    - unfold binds; simpl; right. apply HΔtv. clear - Hγ Hne. fsetdec. }
  assert (Hnfd' : no_flex_dep ((add α Δ1) ∪ Δ2) ((α ~ abind_tvar) ++ Θ0)).
  { intros γ t Hb. unfold binds in Hb; simpl in Hb.
    destruct Hb as [E | Hb]; [ inversion E | ].
    pose proof (Hnfd γ t Hb) as Hd.
    assert (Hτ : ftvar_in_ptyp t [<=] dom Θ0).
    { apply a_wf_ptyp_ftv_dom.
      eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb ]. }
    clear - Hd Hτ Hαd. fsetdec. }
  assert (Hfaf' : flex_above_free ((add α Δ1) ∪ Δ2) ((α ~ abind_tvar) ++ Θ0)).
  { intros Θa γ bb Θb Heq Hne.
    destruct Θa as [ | [z bz] Θa ]; simpl in Heq.
    - injection Heq as E1 E2 E3. exfalso. apply Hne. symmetry. exact E2.
    - injection Heq as E1 E2 E3.
      pose proof (Hfaf Θa γ bb Θb E3 Hne) as Hd.
      assert (Hαn : α `notin` dom (Θa ++ (γ, bb) :: Θb))
        by (rewrite <- E3; exact Hαd).
      rewrite dom_app in Hαn. simpl in Hαn.
      assert (Hαn2 : α `notin` add γ (dom Θb)) by (clear - Hαn; fsetdec).
      apply (inter_empty_cong_l (D := add α (Δ1 ∪ Δ2)));
        [ clear; fsetdec | apply inter_empty_add; [ exact Hd | exact Hαn2 ] ]. }
  assert (HΔsc' : (add α Δ1) ∪ Δ2
                  [<=] ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0))
    by (simpl; clear - HΔsc; fsetdec).
  destruct (IH (add α2 S0) ((α2 ~ abind_tvar) ++ Θ0') (add α2 Δ1') Δ2'
              (open_pskl_wrt_pskl P0b2 (pskl_var_f α2)) (pskl_tophole P12) ((α, α2) :: restrict_pairs α α2 ρ) V
              HrΘ' HrP0' HrP' Hrd1' Hrd2' Hagr' Hinj' Hfun' Hwf' Huq2' Hftv2'
              Hscp' Hblk' HdΘ' Hcov' HcovP' HcovΔ' Hwfp0' Hwfp' HΔtv' Hnfd'
              Hfaf' HΔsc')
    as (S1 & ρe & Θ1out & Q' & De & HrΘout & Hagrout & HrQ & Hext & Hdomout).
  (* ---- side 1's output context, via SOUNDNESS of the premise ---- *)
  pose proof ((proj2 (proj2 a_assign_unify_consis_sound)) _ _ _ _ _ _ _ HD
                Hwf' Hwfp0' Hwfp' HΔtv' Hnfd' Hfaf') as Hsnd.
  destruct Hsnd as (Hinc1 & HwfΘ1α & Hdmp & HΔinv & Hrest).
  (* ---- side 2's output: the OPENER SURVIVES as a rigid prefix ---- *)
  assert (HcovS : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0')
                  ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0b2 (pskl_var_f α2)) ∪ ftvar_in_pskl (pskl_tophole P12)
                  ∪ (add α2 Δ1') ∪ Δ2' [<=] add α2 S0).
  { repeat apply AtomSetProperties.union_subset_3;
      [ exact Hftv2'
      | clear - HcovP'; fsetdec | clear - HcovP'; fsetdec
      | clear - HcovΔ'; fsetdec | clear - HcovΔ'; fsetdec ]. }
  pose proof (e_consis_sound De Huq2' HcovS) as HaD.
  destruct ((proj2 (proj2 a_assign_unify_consis_tvar_prefix))
              _ _ _ _ _ _ _ HaD (α2 ~ abind_tvar) Θ0' eq_refl
              (@tvar_prefix_cons α2 nil tvar_prefix_nil)) as (Θ1' & Eout).
  subst Θ1out.
  assert (Huq1out : uniq ((α2 ~ abind_tvar) ++ Θ1'))
    by (exact ((proj2 (proj2 a_assign_unify_consis_uniq))
                 _ _ _ _ _ _ _ HaD Huq2')).
  (* ---- the e-side conclusion, and the shared closer ---- *)
  assert (Dc : {{ S0 ↝ S1 ⊨ Θ0' ⊢[ Δ1' | Δ2' | (pskl_all_syn P0b2) ] (pskl_tophole P12)
                  ∼ (pskl_all_syn (close_pskl_wrt_pskl α2 Q')) ⊣ Θ1' }}e)
    by (apply e_consis__univ_ghost1 with (α := α2); [ exact Hα2 | exact De ]).
  assert (HcovC : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl (pskl_all_syn P0b2)
                  ∪ ftvar_in_pskl (pskl_tophole P12) ∪ Δ1' ∪ Δ2' [<=] S0).
  { repeat apply AtomSetProperties.union_subset_3;
      [ exact Hftv2
      | clear - HcovP; simpl in HcovP |- *; fsetdec
      | clear - HcovP; simpl in HcovP |- *; fsetdec
      | clear - HcovΔ; fsetdec | clear - HcovΔ; fsetdec ]. }
  eapply lift_consis_forall_close;
    [ exact HwfΘ1α | exact Hαd | exact HαV | exact Hα2V | exact Hα2c
    | exact Huq1out | exact Huq2p | exact Hagr | exact Hinj' | exact Hext
    | exact Hcov' | exact Hcov | exact HrΘout | exact Hagrout | exact HrQ
    | exact Hdomout | exact Dc | exact HcovC ].
Qed.

Theorem a_assign_unify_consis_rel_e :
  (forall Θ0 Ξ α P Θ1, {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
     lift_assign_concl Θ0 Ξ α P Θ1) /\
  (forall Θ0 α β Θ1, {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
     lift_unify_concl Θ0 α β Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P Q Θ1, {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
     lift_consis_concl Δ1 Δ2 Θ0 P0 P Q Θ1).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun Θ0 Ξ α P Θ1 _ => lift_assign_concl Θ0 Ξ α P Θ1)
           (fun Θ0 α β Θ1 _ => lift_unify_concl Θ0 α β Θ1)
           (fun Δ1 Δ2 Θ0 P0 P Q Θ1 _ => lift_consis_concl Δ1 Δ2 Θ0 P0 P Q Θ1)).
  - (* Assign-UnivGhost-Id *)
    intros Θ0 α.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    apply rel_aenv_nil_inv_l in HrΞ. subst Ξ'.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & b2 & Θ0'' & -> & Hab & Hbd & Hrest).
    inversion Hbd; subst.
    assert (Hfun0 : rel_fun ρ V (dom ((α ~ abind_flex_mono) ++ Θ0))).
    { eapply rel_fun_weaken; [ exact Hfun | intros x y Hin; exact Hin | ].
      simpl_env. reflexivity. }
    assert (Hαd : α `in` dom ((α ~ abind_flex_mono) ++ Θ0))
      by (simpl; clear; fsetdec).
    assert (Eb : α' = b) by (exact (Hfun0 α α' b Hαd Hrα Hab)).
    subst α'.
    inversion HrP as [ | n0 | x0 y0 Hx0 | Pa Pb Qa Qb Ha Hb | Pa Qa Ha
                     | | Pa Qa Hin1 ]; subst.
    inversion Hin1 as [ | n1 | x1 c Hxc | Pc Pd Qc Qd Hc Hd | Pc Qc Hc
                      | | Pc Qc Hc ]; subst.
    assert (Ec : c = b) by (exact (Hfun0 α c b Hαd Hxc Hab)). subst c.
    unfold lift_assign_post.
    exists S0, (@nil (atom * atom)%type), ((b ~ abind_flex_mono) ++ Θ0'').
    split; [ apply e_assign__univ_ghost_id | ].
    simpl. simpl in Hagr.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* ⭐ Assign-SolveM *)
    intros Θ0 Ξ α P βs τ Hαp Hguess Hmono Huqβ Hfrβ.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Hαd : α `in` dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Eb : α' = b) by (exact (Hfun α α' b Hαd Hrα Hab)). subst α'.
    assert (HbP : b `notin` ftvar_in_pskl P')
      by (eapply rel_pskl_notin_r_inj;
          [ exact HrP | exact Hinj | exact Hab | exact Hαp ]).
    remember (V ∩ (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P)) as VG eqn:EVG.
    assert (HVG : VG [<=] V) by (subst VG; clear; fsetdec).
    assert (HrPG : rel_pskl ρ VG P P').
    { eapply rel_pskl_shrink_V; [ exact HrP | ].
      intros a Ha Hf. subst VG. clear - Ha Hf. fsetdec. }
    assert (Hscp1G : VG [<=] ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P)
      by (subst VG; clear; fsetdec).
    assert (HcovG : VG ∪ ftvar_in_pskl P' [<=] S0)
      by (clear - HVG Hcov HcovP; fsetdec).
    destruct (a_guess_mono_rel_e Hguess HrPG Hscp1G HcovG)
      as (S1 & ρn & Ξ2 & τ2 & HG2 & E1 & E2 & HrelT0).
    assert (HrelT : rel_ptyp (ρn ++ ρ) V τ τ2).
    { unfold rel_ptyp. eapply rel_pskl_mono;
        [ exact HrelT0 | intros x y Hx; exact Hx | exact HVG ]. }
    assert (Hmono2 : mono_ptyp τ2)
      by (eapply rel_ptyp_mono_ptyp; [ exact HrelT | exact Hmono ]).
    assert (Hb2fr : dom Ξ2 ∩ S0 [=] empty)
      by (exact (e_guess_mono_block_fresh HG2)).
    assert (Huq2b : uniq Ξ2) by (exact (e_guess_mono_uniq HG2)).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    assert (Hsc : ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0)
                  [<=] dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (Hβdom : forall a, a `in` dom βs ->
                    a `notin` dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0)).
    { intros a Ha. pose proof (Hfrβ a Ha) as Hn.
      repeat rewrite dom_app in Hn |- *. simpl. clear - Hn. fsetdec. }
    assert (Hβcols : forall a, a `in` dom βs -> a `notin` cols_l ρ).
    { intros a Ha. apply Hblk; [ | exact (Hβdom a Ha) ].
      repeat rewrite dom_app. simpl. clear - Ha. fsetdec. }
    assert (Hext : rel_ext ρn
                     (ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0)) S0).
    { unfold rel_ext. split; [ | split ].
      - intros a b0 Hin. split.
        + assert (Ha : a `in` dom βs)
            by (rewrite Hdfl; eapply cols_l_in; exact Hin).
          pose proof (Hβdom a Ha) as Hn. clear - Hn Hsc. fsetdec.
        + assert (Hb0 : b0 `in` dom Ξ2)
            by (rewrite Hdfr; eapply cols_r_in; exact Hin).
          clear - Hb0 Hb2fr. fsetdec.
      - intros a1 a2 b0 Hin1 Hin2.
        eapply nodup_snd_inj; [ | exact Hin1 | exact Hin2 ].
        apply uniq_flex_pairs_r_nodup. rewrite <- E2. exact Huq2b.
      - intros a b1 b2 Hin1 Hin2.
        eapply nodup_fst_fun; [ | exact Hin1 | exact Hin2 ].
        apply uniq_flex_pairs_l_nodup. rewrite <- E1. exact Huqβ. }
    unfold lift_assign_post.
    exists S1, ρn, ((b ~ abind_flex_mono_def τ2) ++ Ξ2 ++ Ξ' ++ Θ0'').
    split.
    { apply e_assign__solve_m; [ exact HbP | exact HG2 | exact Hmono2 ]. }
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros x y Hx. apply in_or_app. right. exact Hx.
      - constructor. exact HrelT.
      - apply rel_aenv_app.
        + rewrite E1, E2. apply rel_aenv_flex_pairs.
        + apply rel_aenv_app; apply rel_aenv_widen; assumption. }
    split.
    { split.
      - intros x HxV.
        assert (Hxβ : x `notin` dom βs).
        { intros Hin. pose proof (Hβdom x Hin) as Hn.
          clear - Hn HVdom HxV. fsetdec. }
        assert (HxΞ2 : x `notin` dom Ξ2).
        { intros Hin. clear - Hin Hb2fr HxV Hcov. fsetdec. }
        rewrite (@a_flex_tvar_solve_m α τ βs Ξ Θ0 x Hxβ).
        rewrite (@a_flex_tvar_solve_m b τ2 Ξ2 Ξ' Θ0'' x HxΞ2).
        exact (proj1 Hagr x HxV).
      - intros x y Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        + assert (Hx : x `in` dom βs)
            by (rewrite Hdfl; eapply cols_l_in; exact Hin).
          assert (Hy : y `in` dom Ξ2)
            by (rewrite Hdfr; eapply cols_r_in; exact Hin).
          split; intros _.
          * rewrite E2 in Hy |- *. rewrite ! a_flex_tvar_app_iff.
            right. left.
            apply (proj2 (a_flex_tvar_decls y (a_decls_flex_pairs_r ρn))).
            exact Hy.
          * rewrite E1 in Hx |- *. rewrite ! a_flex_tvar_app_iff.
            right. left.
            apply (proj2 (a_flex_tvar_decls x (a_decls_flex_pairs_l ρn))).
            exact Hx.
        + assert (Hxβ : x `notin` dom βs).
          { intros Hb0. apply (Hβcols x Hb0). eapply cols_l_in; exact Hin. }
          assert (HyΞ2 : y `notin` dom Ξ2).
          { intros Hb0. pose proof (cols_r_in _ _ _ Hin) as Hyc.
            clear - Hb0 Hyc Hb2fr Hcov. fsetdec. }
          rewrite (@a_flex_tvar_solve_m α τ βs Ξ Θ0 x Hxβ).
          rewrite (@a_flex_tvar_solve_m b τ2 Ξ2 Ξ' Θ0'' y HyΞ2).
          exact (proj2 Hagr x y Hin). }
    split; [ exact Hext | ].
    intros a b0 Hin. split.
    { assert (Ha : a `in` dom βs)
        by (rewrite Hdfl; eapply cols_l_in; exact Hin).
      repeat rewrite dom_app. simpl. clear - Ha. fsetdec. }
    { assert (Hb0 : b0 `in` dom Ξ2)
        by (rewrite Hdfr; eapply cols_r_in; exact Hin).
      repeat rewrite dom_app. simpl. clear - Hb0. fsetdec. }
  - (* ⭐ Assign-Assign — the SUBSTITUTION row, and the walk's only descent
       into CONSISTENCY *)
    intros Θ0 Θ1 Ξ α β τ P Q Hfa Hβd HD IH.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'.
    inversion Hbd as [ | | t1 t2 Hrτ | A1 A2 HrA | Q1 Q2 HrQ ]; subst.
    assert (Huq1 : uniq (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq (Ξ' ++ (b ~ abind_flex_mono_def t2) ++ Θ0''))
      by (exact Huq2p).
    assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
    assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hτdom : ftvar_in_ptyp τ [<=] dom Θ0)
      by (apply a_wf_ptyp_ftv_dom;
          exact (proj1 (@a_wf_aenv_mid_def_inv Ξ β τ Θ0 Hdec Hwf))).
    assert (Hτ2dom : ftvar_in_ptyp t2 [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hsc : ftvar_in_aenv (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0)
                  [<=] dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (Hβnd : β `notin` dom (Ξ ++ Θ0)).
    { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
    { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hβd0 : β `in` dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Hβfun : forall y, rel_atom ρ V β y -> y = b)
      by (intros y Hy; exact (Hfun β y b Hβd0 Hy Hab)).
    assert (HαΞ : α `notin` dom Ξ).
    { pose proof (a_flex_tvar_in_dom Hfa) as Hin.
      assert (Hdisj : disjoint Ξ ((β ~ abind_flex_mono_def τ) ++ Θ0))
        by (clear - Huq1; solve_uniq).
      unfold disjoint in Hdisj. clear - Hdisj Hin. fsetdec. }
    assert (Hα'Ξ : α' `notin` dom Ξ').
    { intros Hin. destruct (rel_aenv_dom_r_inv HrΞ Hin) as (a0 & Ha0 & Hat0).
      apply HαΞ. assert (Ea : a0 = α) by (exact (Hinj a0 α α' Hat0 Hrα)).
      rewrite <- Ea. exact Ha0. }
    assert (Hfa2 : a_flex_tvar ((b ~ abind_flex_mono_def t2) ++ Θ0'') α').
    { assert (Hbig : a_flex_tvar (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) α)
        by (apply a_flex_tvar_prepend; exact Hfa).
      apply (proj1 (flex_agree_rel_use Hagr Hrα)) in Hbig.
      apply (proj1 (a_flex_tvar_app_notin _ _ Hα'Ξ)). exact Hbig. }
    remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VC eqn:EVC.
    assert (HVC : VC [<=] V) by (subst VC; clear; fsetdec).
    assert (HVCsplit : forall x, x `in` V -> x <> β -> x `in` VC).
    { intros x Hx Hne. subst VC.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      assert (Hxd : x `in` dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
        by (clear - Hx HVdom; fsetdec).
      repeat rewrite dom_app in Hxd. simpl in Hxd.
      repeat rewrite dom_app in Hds.
      clear - Hx Hne Hxd Hds. fsetdec. }
    assert (HVCne : forall x, x `in` VC -> x <> β).
    { intros x Hx Ex. rewrite Ex in Hx.
      assert (Hin : β `in` ftvar_in_aenv (Ξ ++ Θ0))
        by (subst VC; clear - Hx; fsetdec).
      clear - Hin HscC Hβnd. fsetdec. }
    assert (HrΘC : rel_aenv ρ VC (Ξ ++ Θ0) (Ξ' ++ Θ0'')).
    { eapply rel_aenv_shrink_V; [ apply rel_aenv_app; eassumption | ].
      intros x Hx Hf. apply HVCsplit; [ exact Hx | ].
      intros Ex. rewrite Ex in Hf.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      clear - Hf Hds HscC Hβnd. fsetdec. }
    assert (HrPsub : rel_pskl ρ V (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
                       (subst_pskl_in_pskl (ptyp_to_pskl t2) b P'))
      by (apply rel_pskl_subst;
          [ exact HrP | exact Hrτ | exact Hab | exact Hinj | exact Hβfun ]).
    assert (HrVsub : rel_pskl ρ V
                       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
                       (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α')))
      by (apply rel_pskl_subst;
          [ constructor; exact Hrα | exact Hrτ | exact Hab | exact Hinj
          | exact Hβfun ]).
    assert (Hshr : forall (R : pskl) x, x `in` V ->
              x `in` ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β R) ->
              x `in` VC).
    { intros R x Hx Hin.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper R (ptyp_to_pskl τ) β)
        as Hu.
      rewrite ftvar_ptyp_to_pskl in Hu.
      destruct (AtomSetProperties.In_dec x (ftvar_in_ptyp τ)) as [Hxτ | Hxτ].
      - subst VC.
        pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
        repeat rewrite dom_app in Hds.
        clear - Hx Hxτ Hτdom Hds. fsetdec.
      - apply HVCsplit; [ exact Hx | ].
        intros Ex. rewrite Ex in Hin. clear - Hin Hu Hxτ Ex. fsetdec. }
    assert (HrPsubC : rel_pskl ρ VC (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b P'))
      by (eapply rel_pskl_shrink_V;
          [ exact HrPsub | intros x Hx Hf; exact (Hshr P x Hx Hf) ]).
    assert (HrVsubC : rel_pskl ρ VC
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α')))
      by (eapply rel_pskl_shrink_V;
          [ exact HrVsub
          | intros x Hx Hf; exact (Hshr (pskl_var_f α) x Hx Hf) ]).
    assert (HatomsC : rel_atoms ρ VC empty empty)
      by (intros x y _; split; intros Hin0; exfalso; clear - Hin0; fsetdec).
    assert (HagrC : flex_agree_rel ρ VC (Ξ ++ Θ0) (Ξ' ++ Θ0''))
      by (eapply flex_agree_peel;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | exact HVC | exact HVCne ]).
    assert (HinjC : rel_inj ρ VC)
      by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVC ]).
    assert (HfunC : rel_fun ρ VC (dom (Ξ ++ Θ0))).
    { eapply rel_fun_weaken;
        [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVC ]
        | intros x y Hx; exact Hx
        | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (HblkC : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne : a0 <> β) by (intros Ex; rewrite Ex in Ha0; contradiction).
        repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne. fsetdec. }
    assert (HdΘC : dom (Ξ' ++ Θ0'') [<=] S0)
      by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
          clear - HdΘ; fsetdec).
    assert (HcovC : VC ∪ cols_r ρ [<=] S0) by (clear - Hcov HVC; fsetdec).
    assert (HcovS : ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl t2) b P')
                    ∪ ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b
                           (pskl_var_f α')) [<=] S0).
    { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P' (ptyp_to_pskl t2) b)
        as Hu1.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper (pskl_var_f α')
                    (ptyp_to_pskl t2) b) as Hu2.
      rewrite ftvar_ptyp_to_pskl in Hu1, Hu2.
      assert (Hα'd : ftvar_in_pskl (pskl_var_f α') [<=] S0).
      { simpl. pose proof (a_flex_tvar_in_dom Hfa2) as Hin.
        repeat rewrite dom_app in HdΘ. simpl in HdΘ, Hin.
        clear - Hin HdΘ. fsetdec. }
      repeat rewrite dom_app in HdΘ. simpl in HdΘ.
      clear - Hu1 Hu2 HcovP Hτ2dom HdΘ Hα'd. fsetdec. }
    assert (HcovΔ : empty ∪ empty [<=] S0) by (clear; fsetdec).
    (* ---- the wf package the consis premise wants ---- *)
    assert (Hbβ : binds β (abind_flex_mono_def τ)
                    (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (unfold binds; apply in_or_app; right; simpl; left; reflexivity).
    assert (Hτmono : mono_ptyp τ) by (exact (@a_wf_aenv_binds_def_mono _ β τ Hwf Hbβ)).
    assert (Hβτ : β `notin` ftvar_in_ptyp τ).
    { repeat rewrite dom_app in Hβnd. clear - Hτdom Hβnd. fsetdec. }
    assert (HwfPsub : {{ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ⨟ empty ⊢ₚₛ
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) }}a)
      by (apply a_wf_pskl_mono_subst;
          [ exact Hwfp | exact Hwf | exact Hbβ | exact Hτmono ]).
    assert (HwfVsub : {{ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ⨟ empty ⊢ₚₛ
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                           (pskl_var_f α)) }}a).
    { apply a_wf_pskl_mono_subst;
        [ | exact Hwf | exact Hbβ | exact Hτmono ].
      apply a_wf_pskl__var. destruct Hfa as [Hb | [t Hb]];
        [ right; left | right; right; exists t ];
        unfold binds in *; apply in_or_app; right; exact Hb. }
    assert (Hstrip : forall R, β `notin` ftvar_in_ptyp τ ->
              β `notin` ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β R)).
    { intros R _.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper R (ptyp_to_pskl τ) β)
        as Hu.
      rewrite ftvar_ptyp_to_pskl in Hu. clear - Hu Hβτ. fsetdec. }
    assert (HwfPsubC : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) }}a)
      by (eapply a_wf_pskl_strip_mid;
          [ exact HwfPsub | exact (Hstrip P Hβτ) ]).
    assert (HwfVsubC : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                         (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                            (pskl_var_f α)) }}a)
      by (eapply a_wf_pskl_strip_mid;
          [ exact HwfVsub | exact (Hstrip (pskl_var_f α) Hβτ) ]).
    assert (HΔtv : forall γ, γ `in` (empty ∪ empty) ->
                   binds γ abind_tvar (Ξ ++ Θ0))
      by (intros γ Hγ; exfalso; clear - Hγ; fsetdec).
    assert (Hnfd : no_flex_dep (empty ∪ empty) (Ξ ++ Θ0))
      by (intros γ t Hb0; clear; fsetdec).
    assert (Hfaf : flex_above_free (empty ∪ empty) (Ξ ++ Θ0))
      by (intros Θa γ bb Θb Heq Hne0; clear; fsetdec).
    assert (HΔsc : empty ∪ empty [<=] ftvar_in_aenv (Ξ ++ Θ0))
      by (clear; fsetdec).
    destruct (IH S0 (Ξ' ++ Θ0'') empty empty
                (subst_pskl_in_pskl (ptyp_to_pskl t2) b P')
                (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α'))
                ρ VC HrΘC HrPsubC HrVsubC HatomsC HatomsC HagrC HinjC HfunC
                HwfC Huq2C Hftv2C ltac:(subst VC; clear; fsetdec) HblkC HdΘC HcovC
                HcovS HcovΔ HwfPsubC HwfVsubC HΔtv Hnfd Hfaf HΔsc)
      as (S1 & ρe & Θ1' & Q' & D2 & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
    assert (Hbnd1 : b `notin` dom Θ1').
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper)) _ _ _ _ _ _ _
                    _ _ D2) as Hup.
      assert (HbS0 : b `in` S0).
      { repeat rewrite dom_app in HdΘ. simpl in HdΘ. clear - HdΘ. fsetdec. }
      clear - Hup Hbnd HbS0. fsetdec. }
    unfold lift_assign_post.
    exists S1, ρe, ((b ~ abind_flex_mono_def t2) ++ Θ1').
    split.
    { apply e_assign__assign with (τ := t2) (Q := Q');
        [ exact Hfa2 | exact D2 ]. }
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros x y Hx. apply in_or_app. right. exact Hx.
      - constructor. unfold rel_ptyp in Hrτ |- *.
        eapply rel_pskl_mono;
          [ exact Hrτ | intros x y Hx; apply in_or_app; right; exact Hx
          | intros x Hx; exact Hx ].
      - eapply rel_aenv_mono;
          [ exact HrΘ1 | intros x y Hx; exact Hx | exact HVC ]. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V β b)
      by (eapply rel_atom_incl;
          [ exact Hab | intros x y Hx; apply in_or_app; right; exact Hx ]).
    assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V β y -> y = b).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hβfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
        | exact HVCsplit
        | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
        | split; intros _; apply a_flex_tvar_head_flexish;
          right; eexists; reflexivity ]. }
    assert (Hftsub : ftvar_in_aenv (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0)
                     [<=] add β (ftvar_in_aenv (Ξ ++ Θ0))).
    { repeat rewrite ftvar_in_aenv_app. simpl.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hτdom Hds. fsetdec. }
    split.
    { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
      split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
      intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
      split; [ | exact Hb0 ].
      destruct (Hdom1 _ _ Hin) as [Hd1 _].
      assert (Hne : a0 <> β) by (intros Ex; rewrite Ex in Hd1; contradiction).
      clear - Ha0 Hne Hftsub. fsetdec. }
    intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  - (* Assign-Depend — the entry MOVES into the pending suffix *)
    intros Θ0 Θ1 Ξ α β P Hne Hbin HD IH.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Hne2 : α' <> b).
    { intros Ex. apply Hne. rewrite Ex in Hrα. exact (Hinj α β b Hrα Hab). }
    assert (Hβd0 : β `in` dom (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (HbinP : b `in` ftvar_in_pskl P').
    { destruct (rel_pskl_ftv_corr_l HrP Hbin) as (y & Hy & Hat).
      assert (Ey : y = b) by (exact (Hfun β y b Hβd0 Hat Hab)).
      rewrite <- Ey. exact Hy. }
    assert (HrΞ' : rel_aenv ρ V (Ξ ++ (β ~ abind_flex_mono))
                     (Ξ' ++ (b ~ abind_flex_mono))).
    { apply rel_aenv_app; [ exact HrΞ | ].
      apply rel_aenv__cons; [ exact Hab | constructor | constructor ]. }
    assert (Hagr' : flex_agree_rel ρ V ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)
                      ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0''))
      by (simpl_env; exact Hagr).
    assert (Hfun' : rel_fun ρ V (dom ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)))
      by (simpl_env; exact Hfun).
    assert (Hfl' : a_flex_tvar ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) α)
      by (simpl_env; exact Hfl).
    assert (Hwf' : {{ ⊢ ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) }}a)
      by (simpl_env; exact Hwf).
    assert (Huq2' : uniq ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0''))
      by (simpl_env; exact Huq2p).
    assert (Hftv2' : ftvar_in_aenv ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0'')
                     [<=] S0)
      by (simpl_env; exact Hftv2).
    assert (Hdec' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app; [ exact Hdec | apply a_decls_one ]).
    assert (Hdec2' : a_decls (Ξ' ++ (b ~ abind_flex_mono)))
      by (apply a_decls_app; [ exact Hdec2 | apply a_decls_one ]).
    assert (Hscp' : V [<=] ftvar_in_aenv ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0))
      by (simpl_env; exact Hscp).
    assert (Hblk' : forall a0, a0 `in` dom Θ1 ->
              a0 `notin` dom ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) ->
              a0 `notin` cols_l ρ)
      by (intros a0 Ha0 Hn0; apply Hblk;
          [ exact Ha0
          | repeat rewrite dom_app in Hn0 |- *; simpl in Hn0 |- *;
            clear - Hn0; fsetdec ]).
    assert (HdΘ' : dom ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0'') [<=] S0).
    { repeat rewrite dom_app in HdΘ |- *. simpl in HdΘ |- *.
      clear - HdΘ. fsetdec. }
    assert (Hwfp' : {{ ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (simpl_env; exact Hwfp).
    destruct (IH S0 Θ0'' (Ξ' ++ (b ~ abind_flex_mono)) α' P' ρ V
                Hrest HrΞ' Hrα HrP Hagr' Hinj Hfun' Hfl' Hwf' Hdec'
                Hdec2' Huq2' Hftv2' Hscp' Hblk' HdΘ' Hcov HcovP Hwfp')
      as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
    exists S1, ρe, Θ1'.
    split; [ apply e_assign__depend;
             [ exact Hne2 | exact HbinP | exact D2 ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ simpl_env in Hext1; simpl_env; exact Hext1 | exact Hdom1 ].
  - (* Assign-Skip *)
    intros Θ0 Θ1 Ξ α β P Hne Hβp Hβd HD IH.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Huq1 : uniq (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq (Ξ' ++ (b ~ abind_flex_mono) ++ Θ0''))
      by (exact Huq2p).
    assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
    assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hβnd : β `notin` dom (Ξ ++ Θ0)).
    { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
    { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hsc : ftvar_in_aenv (Ξ ++ (β ~ abind_flex_mono) ++ Θ0)
                  [<=] dom (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hβd0 : β `in` dom (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Hβfun : forall y, rel_atom ρ V β y -> y = b)
      by (intros y Hy; exact (Hfun β y b Hβd0 Hy Hab)).
    assert (Hne2 : α' <> b).
    { intros Ex. apply Hne. rewrite Ex in Hrα. exact (Hinj α β b Hrα Hab). }
    assert (HbP : b `notin` ftvar_in_pskl P')
      by (eapply rel_pskl_notin_r_inj;
          [ exact HrP | exact Hinj | exact Hab | exact Hβp ]).
    remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VS eqn:EVS.
    assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
    assert (HVSsplit : forall x, x `in` V -> x <> β -> x `in` VS).
    { intros x Hx Hne0. subst VS.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      assert (Hxd : x `in` dom (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
        by (clear - Hx HVdom; fsetdec).
      repeat rewrite dom_app in Hxd. simpl in Hxd.
      repeat rewrite dom_app in Hds.
      clear - Hx Hne0 Hxd Hds. fsetdec. }
    assert (HVSne : forall x, x `in` VS -> x <> β).
    { intros x Hx Ex. rewrite Ex in Hx.
      assert (Hin : β `in` ftvar_in_aenv (Ξ ++ Θ0))
        by (subst VS; clear - Hx; fsetdec).
      clear - Hin HscC Hβnd. fsetdec. }
    assert (HrΘS : rel_aenv ρ VS Θ0 Θ0'').
    { eapply rel_aenv_shrink_V; [ exact Hrest | ].
      intros x Hx Hf. subst VS.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      rewrite ftvar_in_aenv_app. clear - Hx Hf Hds. fsetdec. }
    assert (HrΞS : rel_aenv ρ VS Ξ Ξ').
    { eapply rel_aenv_shrink_V; [ exact HrΞ | ].
      intros x Hx Hf. subst VS.
      pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
      rewrite ftvar_in_aenv_app. clear - Hx Hf Hds. fsetdec. }
    assert (HrαS : rel_atom ρ VS α α').
    { inversion Hrα; subst.
      - apply rel_atom__pair; assumption.
      - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hne ]. }
    assert (HrPS : rel_pskl ρ VS P P').
    { eapply rel_pskl_shrink_V; [ exact HrP | ].
      intros x Hx Hf. apply HVSsplit; [ exact Hx | ].
      intros Ex. rewrite Ex in Hf. contradiction. }
    assert (HagrS : flex_agree_rel ρ VS (Ξ ++ Θ0) (Ξ' ++ Θ0''))
      by (eapply flex_agree_peel;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | exact HVS | exact HVSne ]).
    assert (HinjS : rel_inj ρ VS)
      by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVS ]).
    assert (HfunS : rel_fun ρ VS (dom (Ξ ++ Θ0))).
    { eapply rel_fun_weaken;
        [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVS ]
        | intros x y Hx; exact Hx
        | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (HflS : a_flex_tvar (Ξ ++ Θ0) α)
      by (rewrite <- (@a_flex_tvar_mid_other Ξ β abind_flex_mono Θ0 α Hne);
          exact Hfl).
    assert (HscpS : VS [<=] ftvar_in_aenv (Ξ ++ Θ0))
      by (subst VS; clear; fsetdec).
    assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne0 : a0 <> β)
          by (intros Ex; rewrite Ex in Ha0; contradiction).
        repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne0. fsetdec. }
    assert (HdΘS : dom (Ξ' ++ Θ0'') [<=] S0)
      by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
          clear - HdΘ; fsetdec).
    assert (HcovS : VS ∪ cols_r ρ [<=] S0) by (clear - Hcov HVS; fsetdec).
    assert (HwfpS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_strip_mid; [ exact Hwfp | exact Hβp ]).
    destruct (IH S0 Θ0'' Ξ' α' P' ρ VS HrΘS HrΞS HrαS HrPS HagrS HinjS HfunS
                HflS HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS HdΘS HcovS HcovP HwfpS)
      as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
    assert (Hbnd1 : b `notin` dom Θ1').
    { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ D2)
        as Hup.
      assert (HbS0 : b `in` S0).
      { repeat rewrite dom_app in HdΘ. simpl in HdΘ. clear - HdΘ. fsetdec. }
      clear - Hup Hbnd HbS0. fsetdec. }
    exists S1, ρe, ((b ~ abind_flex_mono) ++ Θ1').
    split; [ apply e_assign__skip; [ exact Hne2 | exact HbP | exact D2 ] | ].
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros x y Hx. apply in_or_app. right. exact Hx.
      - constructor.
      - eapply rel_aenv_mono;
          [ exact HrΘ1 | intros x y Hx; exact Hx | exact HVS ]. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V β b)
      by (eapply rel_atom_incl;
          [ exact Hab | intros x y Hx; apply in_or_app; right; exact Hx ]).
    assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V β y -> y = b).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hβfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
        | exact HVSsplit
        | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
        | split; intros _; apply a_flex_tvar_head_flexish;
          left; reflexivity ]. }
    assert (Hftsub : ftvar_in_aenv (Ξ ++ (β ~ abind_flex_mono) ++ Θ0)
                     [<=] add β (ftvar_in_aenv (Ξ ++ Θ0))).
    { repeat rewrite ftvar_in_aenv_app. simpl. clear; fsetdec. }
    split.
    { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
      split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
      intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
      split; [ | exact Hb0 ].
      destruct (Hdom1 _ _ Hin) as [Hd1 _].
      assert (Hne0 : a0 <> β)
        by (intros Ex; rewrite Ex in Hd1; contradiction).
      clear - Ha0 Hne0 Hftsub. fsetdec. }
    intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  - (* Assign-SkipRigid *)
    intros Θ0 Θ1 Ξ α β P Hβp Hβd HD IH.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Huq1 : uniq (Ξ ++ (β ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq (Ξ' ++ (b ~ abind_tvar) ++ Θ0''))
      by (exact Huq2p).
    assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
    assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hβnd : β `notin` dom (Ξ ++ Θ0)).
    { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
    { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hsc : ftvar_in_aenv (Ξ ++ (β ~ abind_tvar) ++ Θ0)
                  [<=] dom (Ξ ++ (β ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom (Ξ ++ (β ~ abind_tvar) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hβd0 : β `in` dom (Ξ ++ (β ~ abind_tvar) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Hβfun : forall y, rel_atom ρ V β y -> y = b)
      by (intros y Hy; exact (Hfun β y b Hβd0 Hy Hab)).
    assert (Hne : α <> β).
    { intros Ex. rewrite Ex in Hfl.
      exact (@a_flex_tvar_mid_nonflex_absurd Ξ β abind_tvar Θ0 Huq1
               ltac:(discriminate) ltac:(intros t; discriminate) Hfl). }
    assert (HbP : b `notin` ftvar_in_pskl P')
      by (eapply rel_pskl_notin_r_inj;
          [ exact HrP | exact Hinj | exact Hab | exact Hβp ]).
    remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VS eqn:EVS.
    assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
    assert (HVSsplit : forall x, x `in` V -> x <> β -> x `in` VS).
    { intros x Hx Hne0. subst VS.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      assert (Hxd : x `in` dom (Ξ ++ (β ~ abind_tvar) ++ Θ0))
        by (clear - Hx HVdom; fsetdec).
      repeat rewrite dom_app in Hxd. simpl in Hxd.
      repeat rewrite dom_app in Hds.
      clear - Hx Hne0 Hxd Hds. fsetdec. }
    assert (HVSne : forall x, x `in` VS -> x <> β).
    { intros x Hx Ex. rewrite Ex in Hx.
      assert (Hin : β `in` ftvar_in_aenv (Ξ ++ Θ0))
        by (subst VS; clear - Hx; fsetdec).
      clear - Hin HscC Hβnd. fsetdec. }
    assert (HrΘS : rel_aenv ρ VS Θ0 Θ0'').
    { eapply rel_aenv_shrink_V; [ exact Hrest | ].
      intros x Hx Hf. subst VS.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      rewrite ftvar_in_aenv_app. clear - Hx Hf Hds. fsetdec. }
    assert (HrΞS : rel_aenv ρ VS Ξ Ξ').
    { eapply rel_aenv_shrink_V; [ exact HrΞ | ].
      intros x Hx Hf. subst VS.
      pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
      rewrite ftvar_in_aenv_app. clear - Hx Hf Hds. fsetdec. }
    assert (HrαS : rel_atom ρ VS α α').
    { inversion Hrα; subst.
      - apply rel_atom__pair; assumption.
      - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hne ]. }
    assert (HrPS : rel_pskl ρ VS P P').
    { eapply rel_pskl_shrink_V; [ exact HrP | ].
      intros x Hx Hf. apply HVSsplit; [ exact Hx | ].
      intros Ex. rewrite Ex in Hf. contradiction. }
    assert (HagrS : flex_agree_rel ρ VS (Ξ ++ Θ0) (Ξ' ++ Θ0''))
      by (eapply flex_agree_peel;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | exact HVS | exact HVSne ]).
    assert (HinjS : rel_inj ρ VS)
      by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVS ]).
    assert (HfunS : rel_fun ρ VS (dom (Ξ ++ Θ0))).
    { eapply rel_fun_weaken;
        [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVS ]
        | intros x y Hx; exact Hx
        | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (HflS : a_flex_tvar (Ξ ++ Θ0) α)
      by (rewrite <- (@a_flex_tvar_mid_other Ξ β abind_tvar Θ0 α Hne);
          exact Hfl).
    assert (HscpS : VS [<=] ftvar_in_aenv (Ξ ++ Θ0))
      by (subst VS; clear; fsetdec).
    assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne0 : a0 <> β)
          by (intros Ex; rewrite Ex in Ha0; contradiction).
        repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne0. fsetdec. }
    assert (HdΘS : dom (Ξ' ++ Θ0'') [<=] S0)
      by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
          clear - HdΘ; fsetdec).
    assert (HcovS : VS ∪ cols_r ρ [<=] S0) by (clear - Hcov HVS; fsetdec).
    assert (HwfpS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_strip_mid; [ exact Hwfp | exact Hβp ]).
    destruct (IH S0 Θ0'' Ξ' α' P' ρ VS HrΘS HrΞS HrαS HrPS HagrS HinjS HfunS
                HflS HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS HdΘS HcovS HcovP HwfpS)
      as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
    assert (Hbnd1 : b `notin` dom Θ1').
    { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ D2)
        as Hup.
      assert (HbS0 : b `in` S0).
      { repeat rewrite dom_app in HdΘ. simpl in HdΘ. clear - HdΘ. fsetdec. }
      clear - Hup Hbnd HbS0. fsetdec. }
    exists S1, ρe, ((b ~ abind_tvar) ++ Θ1').
    split; [ apply e_assign__skip_rigid; [ exact HbP | exact D2 ] | ].
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros x y Hx. apply in_or_app. right. exact Hx.
      - constructor.
      - eapply rel_aenv_mono;
          [ exact HrΘ1 | intros x y Hx; exact Hx | exact HVS ]. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V β b)
      by (eapply rel_atom_incl;
          [ exact Hab | intros x y Hx; apply in_or_app; right; exact Hx ]).
    assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V β y -> y = b).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hβfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
        | exact HVSsplit
        | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
        | split; intros Hf; exfalso;
          [ exact (@a_flex_tvar_cons_absent β abind_tvar Θ1 β
                     ltac:(discriminate) ltac:(intros t; discriminate)
                     Hβd Hf)
          | exact (@a_flex_tvar_cons_absent b abind_tvar Θ1' b
                     ltac:(discriminate) ltac:(intros t; discriminate)
                     Hbnd1 Hf) ] ]. }
    assert (Hftsub : ftvar_in_aenv (Ξ ++ (β ~ abind_tvar) ++ Θ0)
                     [<=] add β (ftvar_in_aenv (Ξ ++ Θ0))).
    { repeat rewrite ftvar_in_aenv_app. simpl. clear; fsetdec. }
    split.
    { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
      split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
      intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
      split; [ | exact Hb0 ].
      destruct (Hdom1 _ _ Hin) as [Hd1 _].
      assert (Hne0 : a0 <> β)
        by (intros Ex; rewrite Ex in Hd1; contradiction).
      clear - Ha0 Hne0 Hftsub. fsetdec. }
    intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  - (* Assign-SkipTmVar — ⭐ the row with NO [x ∉ ftvar P] premise: [V] keeps [x]
       as an IDENTITY PAIR when it has to, and deletes it again after *)
    intros Θ0 Θ1 Ξ α x A P Hxd HD IH.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd as [ | | | A1 A2 HrA | ]; subst.
    assert (Huq1 : uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq (Ξ' ++ (b ~ abind_var_typ A2) ++ Θ0''))
      by (exact Huq2p).
    assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
    assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hβnd : x `notin` dom (Ξ ++ Θ0)).
    { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
    { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hsc : ftvar_in_aenv (Ξ ++ (x ~ abind_var_typ A) ++ Θ0)
                  [<=] dom (Ξ ++ (x ~ abind_var_typ A) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom (Ξ ++ (x ~ abind_var_typ A) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hβd0 : x `in` dom (Ξ ++ (x ~ abind_var_typ A) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Hβfun : forall y, rel_atom ρ V x y -> y = b)
      by (intros y Hy; exact (Hfun x y b Hβd0 Hy Hab)).
    assert (Hne : α <> x).
    { intros Ex. rewrite Ex in Hfl.
      exact (@a_flex_tvar_mid_nonflex_absurd Ξ x (abind_var_typ A) Θ0 Huq1
               ltac:(discriminate) ltac:(intros t; discriminate) Hfl). }
    assert (HflS : a_flex_tvar (Ξ ++ Θ0) α)
      by (rewrite <- (@a_flex_tvar_mid_other Ξ x (abind_var_typ A) Θ0 α Hne);
          exact Hfl).
    (* the peeled payload is scoped in the TAIL *)
    assert (Hpay : ftvar_in_abind (abind_var_typ A) [<=] ftvar_in_aenv (Ξ ++ Θ0)).
    { pose proof (a_wf_ptyp_ftv_dom
                    (@a_wf_aenv_mid_var_typ_inv Ξ x A Θ0 Hdec Hwf)) as Hd.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      rewrite ftvar_in_aenv_app. simpl. clear - Hd Hds. fsetdec. }
    assert (Hxp : x `notin` ftvar_in_pskl P).
    { intros Hin.
      pose proof (a_wf_pskl_ftv_binds Hwfp Hin) as Htv.
      apply (@a_binds_tvar_not_var_typ
               (Ξ ++ (x ~ abind_var_typ A) ++ Θ0) x A Huq1
               ltac:(unfold binds; apply in_or_app; right; simpl;
                     left; reflexivity)).
      exact Htv. }
    assert (HwfpS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_strip_mid; [ exact Hwfp | exact Hxp ]).
    assert (Hftsub : ftvar_in_aenv (Ξ ++ (x ~ abind_var_typ A) ++ Θ0)
                     [<=] add x (ftvar_in_aenv (Ξ ++ Θ0))).
    { repeat rewrite ftvar_in_aenv_app. repeat rewrite ftvar_in_aenv_app in Hpay.
      simpl. simpl in Hpay. clear - Hpay. fsetdec. }
    assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne0 : a0 <> x)
          by (intros Ex; rewrite Ex in Ha0; contradiction).
        repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne0. fsetdec. }
    assert (HdΘS : dom (Ξ' ++ Θ0'') [<=] S0)
      by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
          clear - HdΘ; fsetdec).
    assert (HbS0 : b `in` S0)
      by (repeat rewrite dom_app in HdΘ; simpl in HdΘ; clear - HdΘ; fsetdec).
    assert (HfunD : rel_fun ρ V (dom (Ξ ++ Θ0))).
    { eapply rel_fun_weaken;
        [ exact Hfun | intros y z Hy; exact Hy
        | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    destruct (AtomSetProperties.In_dec x V) as [HxV | HxV].
    + (* ⭐ [x ∈ V]: [rel_fun] forces side 2's head to be [x] too, so the
         pair the shrink needs is the IDENTITY one, and it leaves again *)
      assert (Ebx : b = x)
        by (symmetry; apply Hβfun; apply rel_atom__id; exact HxV).
      subst b.
      remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VS eqn:EVS.
      assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
      assert (HVSsplit : forall y, y `in` V -> y <> x -> y `in` VS).
      { intros y Hy Hne0. subst VS.
        pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
        assert (Hyd : y `in` dom (Ξ ++ (x ~ abind_var_typ A) ++ Θ0))
          by (clear - Hy HVdom; fsetdec).
        repeat rewrite dom_app in Hyd. simpl in Hyd.
        repeat rewrite dom_app in Hds.
        clear - Hy Hne0 Hyd Hds. fsetdec. }
      assert (HVSne : forall y, y `in` VS -> y <> x).
      { intros y Hy Ex. rewrite Ex in Hy.
        assert (Hin : x `in` ftvar_in_aenv (Ξ ++ Θ0))
          by (subst VS; clear - Hy; fsetdec).
        clear - Hin HscC Hβnd. fsetdec. }
      assert (HrΘS : rel_aenv ((x, x) :: ρ) VS Θ0 Θ0'').
      { eapply rel_aenv_mono;
          [ eapply rel_aenv_shrink_V; [ exact Hrest | ]
          | intros y z Hy; right; exact Hy | intros y Hy; exact Hy ].
        intros y Hy Hf. subst VS.
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
        rewrite ftvar_in_aenv_app. clear - Hy Hf Hds. fsetdec. }
      assert (HrΞS : rel_aenv ((x, x) :: ρ) VS Ξ Ξ').
      { eapply rel_aenv_mono;
          [ eapply rel_aenv_shrink_V; [ exact HrΞ | ]
          | intros y z Hy; right; exact Hy | intros y Hy; exact Hy ].
        intros y Hy Hf. subst VS.
        pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
        rewrite ftvar_in_aenv_app. clear - Hy Hf Hds. fsetdec. }
      assert (HrαS : rel_atom ((x, x) :: ρ) VS α α').
      { inversion Hrα; subst.
        - apply rel_atom__pair. right. assumption.
        - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hne ]. }
      assert (HrPS : rel_pskl ((x, x) :: ρ) VS P P').
      { eapply rel_pskl_shrink_V_id; [ exact HrP | ].
        intros y Hy Hf. destruct (y == x) as [-> | Hne0];
          [ left; reflexivity | right; apply HVSsplit; assumption ]. }
      assert (HagrS : flex_agree_rel ((x, x) :: ρ) VS (Ξ ++ Θ0) (Ξ' ++ Θ0'')).
      { apply flex_agree_rel_push_id_absent; [ | exact Hβnd | exact Hbnd ].
        eapply flex_agree_peel;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | exact HVS | exact HVSne ]. }
      assert (HinjS : rel_inj ((x, x) :: ρ) VS)
        by (eapply rel_inj_push_id; [ exact Hinj | exact HxV | exact HVS ]).
      assert (HfunS : rel_fun ((x, x) :: ρ) VS (dom (Ξ ++ Θ0)))
        by (eapply rel_fun_push_absent;
            [ exact HfunD | exact HVS | exact Hβnd ]).
      assert (HscpS : VS [<=] ftvar_in_aenv (Ξ ++ Θ0))
        by (subst VS; clear; fsetdec).
      assert (HblkS' : forall a0, a0 `in` dom Θ1 ->
                a0 `notin` dom (Ξ ++ Θ0) -> a0 `notin` cols_l ((x, x) :: ρ)).
      { intros a0 Ha0 Hn0. simpl.
        assert (Hne0 : a0 <> x)
          by (intros Ex; rewrite Ex in Ha0; contradiction).
        pose proof (HblkS a0 Ha0 Hn0) as Hc. clear - Hc Hne0. fsetdec. }
      assert (HcovS : VS ∪ cols_r ((x, x) :: ρ) [<=] S0).
      { simpl. clear - Hcov HVS HxV. fsetdec. }
      destruct (IH S0 Θ0'' Ξ' α' P' ((x, x) :: ρ) VS HrΘS HrΞS HrαS HrPS
                  HagrS HinjS HfunS HflS HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS'
                  HdΘS HcovS HcovP HwfpS)
        as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
      assert (Hbnd1 : x `notin` dom Θ1').
      { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ D2)
          as Hup.
        clear - Hup Hbnd HbS0. fsetdec. }
      exists S1, ρe, ((x ~ abind_var_typ A2) ++ Θ1').
      split; [ apply e_assign__skip_tm_var; exact D2 | ].
      assert (Hrel1' : rel_aenv (ρe ++ ρ) V Θ1 Θ1').
      { eapply rel_aenv_drop_id; [ | exact HxV ].
        eapply rel_aenv_mono;
          [ exact HrΘ1 | intros y z Hy; exact Hy | exact HVS ]. }
      assert (Hagr1' : flex_agree_rel (ρe ++ ρ) VS Θ1 Θ1').
      { eapply flex_agree_rel_weaken;
          [ exact Hagr1
          | intros y z Hy; apply in_app_or in Hy; apply in_or_app;
            destruct Hy as [Hy | Hy];
              [ left; exact Hy | right; right; exact Hy ]
          | intros y Hy; exact Hy ]. }
      split.
      { apply rel_aenv__cons.
        - apply rel_atom__id. exact HxV.
        - constructor; eapply rel_ptyp_mono; [ exact HrA | intros y z Hy; apply in_or_app; right; exact Hy | intros y Hy; exact Hy ].
        - exact Hrel1'. }
      assert (Hinj' : rel_inj (ρe ++ ρ) V)
        by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
      assert (Hab' : rel_atom (ρe ++ ρ) V x x)
        by (apply rel_atom__id; exact HxV).
      assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V x y -> y = x).
      { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
        - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
        - exact (Hβfun y Hat0). }
      split.
      { eapply flex_agree_reattach;
          [ exact Hagr1' | exact Hab' | exact Hinj' | exact Hβfun'
          | exact HVSsplit
          | intros _; reflexivity
          | split; intros Hf; exfalso;
            [ exact (@a_flex_tvar_cons_absent x (abind_var_typ A) Θ1 x
                       ltac:(discriminate) ltac:(intros t; discriminate)
                       Hxd Hf)
            | exact (@a_flex_tvar_cons_absent x (abind_var_typ A2) Θ1' x
                       ltac:(discriminate) ltac:(intros t; discriminate)
                       Hbnd1 Hf) ] ]. }
      split.
      { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
        split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
        intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
        split; [ | exact Hb0 ].
        destruct (Hdom1 _ _ Hin) as [Hd1 _].
        assert (Hne0 : a0 <> x)
          by (intros Ex; rewrite Ex in Hd1; contradiction).
        clear - Ha0 Hne0 Hftsub. fsetdec. }
      intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
    + (* [x ∉ V]: nothing to shrink — the peeled entry was never in the
         identity support *)
      assert (HscpS : V [<=] ftvar_in_aenv (Ξ ++ Θ0)).
      { pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
        repeat rewrite dom_app in HVdom, Hds. simpl in HVdom.
        clear - HVdom Hds HxV. fsetdec. }
      assert (HVSne : forall y, y `in` V -> y <> x)
        by (intros y Hy Ex; rewrite Ex in Hy; contradiction).
      assert (HagrS : flex_agree_rel ρ V (Ξ ++ Θ0) (Ξ' ++ Θ0''))
        by (eapply flex_agree_peel;
            [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
            | exact Hbnd | intros y Hy; exact Hy | exact HVSne ]).
      destruct (IH S0 Θ0'' Ξ' α' P' ρ V Hrest HrΞ Hrα HrP HagrS Hinj HfunD
                  HflS HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS HdΘS Hcov HcovP HwfpS)
        as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
      assert (Hbnd1 : b `notin` dom Θ1').
      { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ D2)
          as Hup.
        clear - Hup Hbnd HbS0. fsetdec. }
      exists S1, ρe, ((b ~ abind_var_typ A2) ++ Θ1').
      split; [ apply e_assign__skip_tm_var; exact D2 | ].
      split.
      { apply rel_aenv__cons.
        - eapply rel_atom_incl; [ exact Hab | ].
          intros y z Hy. apply in_or_app. right. exact Hy.
        - constructor; eapply rel_ptyp_mono; [ exact HrA | intros y z Hy; apply in_or_app; right; exact Hy | intros y Hy; exact Hy ].
        - exact HrΘ1. }
      assert (Hinj' : rel_inj (ρe ++ ρ) V)
        by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
      assert (Hab' : rel_atom (ρe ++ ρ) V x b)
        by (eapply rel_atom_incl;
            [ exact Hab | intros y z Hy; apply in_or_app; right; exact Hy ]).
      assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V x y -> y = b).
      { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
        - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
        - exact (Hβfun y Hat0). }
      split.
      { eapply flex_agree_reattach;
          [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
          | intros y Hy _; exact Hy
          | intros HxV0; contradiction
          | split; intros Hf; exfalso;
            [ exact (@a_flex_tvar_cons_absent x (abind_var_typ A) Θ1 x
                       ltac:(discriminate) ltac:(intros t; discriminate)
                       Hxd Hf)
            | exact (@a_flex_tvar_cons_absent b (abind_var_typ A2) Θ1' b
                       ltac:(discriminate) ltac:(intros t; discriminate)
                       Hbnd1 Hf) ] ]. }
      split.
      { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
        split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
        intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
        split; [ | exact Hb0 ].
        destruct (Hdom1 _ _ Hin) as [Hd1 _].
        assert (Hne0 : a0 <> x)
          by (intros Ex; rewrite Ex in Hd1; contradiction).
        clear - Ha0 Hne0 Hftsub. fsetdec. }
      intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  - (* Assign-SkipTmVar (skl) — ⭐ the row with NO [x ∉ ftvar P] premise: [V] keeps [x]
       as an IDENTITY PAIR when it has to, and deletes it again after *)
    intros Θ0 Θ1 Ξ α x Q0 P Hxd HD IH.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd as [ | | | | Q1 Q2 HrQ ]; subst.
    assert (Huq1 : uniq (Ξ ++ (x ~ abind_var_skl Q0) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq (Ξ' ++ (b ~ abind_var_skl Q2) ++ Θ0''))
      by (exact Huq2p).
    assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
    assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hβnd : x `notin` dom (Ξ ++ Θ0)).
    { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
    { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hsc : ftvar_in_aenv (Ξ ++ (x ~ abind_var_skl Q0) ++ Θ0)
                  [<=] dom (Ξ ++ (x ~ abind_var_skl Q0) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom (Ξ ++ (x ~ abind_var_skl Q0) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hβd0 : x `in` dom (Ξ ++ (x ~ abind_var_skl Q0) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Hβfun : forall y, rel_atom ρ V x y -> y = b)
      by (intros y Hy; exact (Hfun x y b Hβd0 Hy Hab)).
    assert (Hne : α <> x).
    { intros Ex. rewrite Ex in Hfl.
      exact (@a_flex_tvar_mid_nonflex_absurd Ξ x (abind_var_skl Q0) Θ0 Huq1
               ltac:(discriminate) ltac:(intros t; discriminate) Hfl). }
    assert (HflS : a_flex_tvar (Ξ ++ Θ0) α)
      by (rewrite <- (@a_flex_tvar_mid_other Ξ x (abind_var_skl Q0) Θ0 α Hne);
          exact Hfl).
    (* the peeled payload is scoped in the TAIL *)
    assert (Hpay : ftvar_in_abind (abind_var_skl Q0) [<=] ftvar_in_aenv (Ξ ++ Θ0)).
    { pose proof (a_wf_pskl_ftv_dom
                    (@a_wf_aenv_mid_var_skl_inv Ξ x Q0 Θ0 Hdec Hwf)) as Hd.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      rewrite ftvar_in_aenv_app. simpl. clear - Hd Hds. fsetdec. }
    assert (Hxp : x `notin` ftvar_in_pskl P).
    { intros Hin.
      pose proof (a_wf_pskl_ftv_binds Hwfp Hin) as Htv.
      apply (@a_binds_tvar_not_var_skl
               (Ξ ++ (x ~ abind_var_skl Q0) ++ Θ0) x Q0 Huq1
               ltac:(unfold binds; apply in_or_app; right; simpl;
                     left; reflexivity)).
      exact Htv. }
    assert (HwfpS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_strip_mid; [ exact Hwfp | exact Hxp ]).
    assert (Hftsub : ftvar_in_aenv (Ξ ++ (x ~ abind_var_skl Q0) ++ Θ0)
                     [<=] add x (ftvar_in_aenv (Ξ ++ Θ0))).
    { repeat rewrite ftvar_in_aenv_app. repeat rewrite ftvar_in_aenv_app in Hpay.
      simpl. simpl in Hpay. clear - Hpay. fsetdec. }
    assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne0 : a0 <> x)
          by (intros Ex; rewrite Ex in Ha0; contradiction).
        repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne0. fsetdec. }
    assert (HdΘS : dom (Ξ' ++ Θ0'') [<=] S0)
      by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
          clear - HdΘ; fsetdec).
    assert (HbS0 : b `in` S0)
      by (repeat rewrite dom_app in HdΘ; simpl in HdΘ; clear - HdΘ; fsetdec).
    assert (HfunD : rel_fun ρ V (dom (Ξ ++ Θ0))).
    { eapply rel_fun_weaken;
        [ exact Hfun | intros y z Hy; exact Hy
        | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    destruct (AtomSetProperties.In_dec x V) as [HxV | HxV].
    + (* ⭐ [x ∈ V]: [rel_fun] forces side 2's head to be [x] too, so the
         pair the shrink needs is the IDENTITY one, and it leaves again *)
      assert (Ebx : b = x)
        by (symmetry; apply Hβfun; apply rel_atom__id; exact HxV).
      subst b.
      remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VS eqn:EVS.
      assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
      assert (HVSsplit : forall y, y `in` V -> y <> x -> y `in` VS).
      { intros y Hy Hne0. subst VS.
        pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
        assert (Hyd : y `in` dom (Ξ ++ (x ~ abind_var_skl Q0) ++ Θ0))
          by (clear - Hy HVdom; fsetdec).
        repeat rewrite dom_app in Hyd. simpl in Hyd.
        repeat rewrite dom_app in Hds.
        clear - Hy Hne0 Hyd Hds. fsetdec. }
      assert (HVSne : forall y, y `in` VS -> y <> x).
      { intros y Hy Ex. rewrite Ex in Hy.
        assert (Hin : x `in` ftvar_in_aenv (Ξ ++ Θ0))
          by (subst VS; clear - Hy; fsetdec).
        clear - Hin HscC Hβnd. fsetdec. }
      assert (HrΘS : rel_aenv ((x, x) :: ρ) VS Θ0 Θ0'').
      { eapply rel_aenv_mono;
          [ eapply rel_aenv_shrink_V; [ exact Hrest | ]
          | intros y z Hy; right; exact Hy | intros y Hy; exact Hy ].
        intros y Hy Hf. subst VS.
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
        rewrite ftvar_in_aenv_app. clear - Hy Hf Hds. fsetdec. }
      assert (HrΞS : rel_aenv ((x, x) :: ρ) VS Ξ Ξ').
      { eapply rel_aenv_mono;
          [ eapply rel_aenv_shrink_V; [ exact HrΞ | ]
          | intros y z Hy; right; exact Hy | intros y Hy; exact Hy ].
        intros y Hy Hf. subst VS.
        pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
        rewrite ftvar_in_aenv_app. clear - Hy Hf Hds. fsetdec. }
      assert (HrαS : rel_atom ((x, x) :: ρ) VS α α').
      { inversion Hrα; subst.
        - apply rel_atom__pair. right. assumption.
        - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hne ]. }
      assert (HrPS : rel_pskl ((x, x) :: ρ) VS P P').
      { eapply rel_pskl_shrink_V_id; [ exact HrP | ].
        intros y Hy Hf. destruct (y == x) as [-> | Hne0];
          [ left; reflexivity | right; apply HVSsplit; assumption ]. }
      assert (HagrS : flex_agree_rel ((x, x) :: ρ) VS (Ξ ++ Θ0) (Ξ' ++ Θ0'')).
      { apply flex_agree_rel_push_id_absent; [ | exact Hβnd | exact Hbnd ].
        eapply flex_agree_peel;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | exact HVS | exact HVSne ]. }
      assert (HinjS : rel_inj ((x, x) :: ρ) VS)
        by (eapply rel_inj_push_id; [ exact Hinj | exact HxV | exact HVS ]).
      assert (HfunS : rel_fun ((x, x) :: ρ) VS (dom (Ξ ++ Θ0)))
        by (eapply rel_fun_push_absent;
            [ exact HfunD | exact HVS | exact Hβnd ]).
      assert (HscpS : VS [<=] ftvar_in_aenv (Ξ ++ Θ0))
        by (subst VS; clear; fsetdec).
      assert (HblkS' : forall a0, a0 `in` dom Θ1 ->
                a0 `notin` dom (Ξ ++ Θ0) -> a0 `notin` cols_l ((x, x) :: ρ)).
      { intros a0 Ha0 Hn0. simpl.
        assert (Hne0 : a0 <> x)
          by (intros Ex; rewrite Ex in Ha0; contradiction).
        pose proof (HblkS a0 Ha0 Hn0) as Hc. clear - Hc Hne0. fsetdec. }
      assert (HcovS : VS ∪ cols_r ((x, x) :: ρ) [<=] S0).
      { simpl. clear - Hcov HVS HxV. fsetdec. }
      destruct (IH S0 Θ0'' Ξ' α' P' ((x, x) :: ρ) VS HrΘS HrΞS HrαS HrPS
                  HagrS HinjS HfunS HflS HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS'
                  HdΘS HcovS HcovP HwfpS)
        as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
      assert (Hbnd1 : x `notin` dom Θ1').
      { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ D2)
          as Hup.
        clear - Hup Hbnd HbS0. fsetdec. }
      exists S1, ρe, ((x ~ abind_var_skl Q2) ++ Θ1').
      split; [ apply e_assign__skip_tm_skl; exact D2 | ].
      assert (Hrel1' : rel_aenv (ρe ++ ρ) V Θ1 Θ1').
      { eapply rel_aenv_drop_id; [ | exact HxV ].
        eapply rel_aenv_mono;
          [ exact HrΘ1 | intros y z Hy; exact Hy | exact HVS ]. }
      assert (Hagr1' : flex_agree_rel (ρe ++ ρ) VS Θ1 Θ1').
      { eapply flex_agree_rel_weaken;
          [ exact Hagr1
          | intros y z Hy; apply in_app_or in Hy; apply in_or_app;
            destruct Hy as [Hy | Hy];
              [ left; exact Hy | right; right; exact Hy ]
          | intros y Hy; exact Hy ]. }
      split.
      { apply rel_aenv__cons.
        - apply rel_atom__id. exact HxV.
        - constructor; eapply rel_pskl_mono; [ exact HrQ | intros y z Hy; apply in_or_app; right; exact Hy | intros y Hy; exact Hy ].
        - exact Hrel1'. }
      assert (Hinj' : rel_inj (ρe ++ ρ) V)
        by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
      assert (Hab' : rel_atom (ρe ++ ρ) V x x)
        by (apply rel_atom__id; exact HxV).
      assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V x y -> y = x).
      { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
        - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
        - exact (Hβfun y Hat0). }
      split.
      { eapply flex_agree_reattach;
          [ exact Hagr1' | exact Hab' | exact Hinj' | exact Hβfun'
          | exact HVSsplit
          | intros _; reflexivity
          | split; intros Hf; exfalso;
            [ exact (@a_flex_tvar_cons_absent x (abind_var_skl Q0) Θ1 x
                       ltac:(discriminate) ltac:(intros t; discriminate)
                       Hxd Hf)
            | exact (@a_flex_tvar_cons_absent x (abind_var_skl Q2) Θ1' x
                       ltac:(discriminate) ltac:(intros t; discriminate)
                       Hbnd1 Hf) ] ]. }
      split.
      { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
        split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
        intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
        split; [ | exact Hb0 ].
        destruct (Hdom1 _ _ Hin) as [Hd1 _].
        assert (Hne0 : a0 <> x)
          by (intros Ex; rewrite Ex in Hd1; contradiction).
        clear - Ha0 Hne0 Hftsub. fsetdec. }
      intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
    + (* [x ∉ V]: nothing to shrink — the peeled entry was never in the
         identity support *)
      assert (HscpS : V [<=] ftvar_in_aenv (Ξ ++ Θ0)).
      { pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
        repeat rewrite dom_app in HVdom, Hds. simpl in HVdom.
        clear - HVdom Hds HxV. fsetdec. }
      assert (HVSne : forall y, y `in` V -> y <> x)
        by (intros y Hy Ex; rewrite Ex in Hy; contradiction).
      assert (HagrS : flex_agree_rel ρ V (Ξ ++ Θ0) (Ξ' ++ Θ0''))
        by (eapply flex_agree_peel;
            [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
            | exact Hbnd | intros y Hy; exact Hy | exact HVSne ]).
      destruct (IH S0 Θ0'' Ξ' α' P' ρ V Hrest HrΞ Hrα HrP HagrS Hinj HfunD
                  HflS HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS HdΘS Hcov HcovP HwfpS)
        as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
      assert (Hbnd1 : b `notin` dom Θ1').
      { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ D2)
          as Hup.
        clear - Hup Hbnd HbS0. fsetdec. }
      exists S1, ρe, ((b ~ abind_var_skl Q2) ++ Θ1').
      split; [ apply e_assign__skip_tm_skl; exact D2 | ].
      split.
      { apply rel_aenv__cons.
        - eapply rel_atom_incl; [ exact Hab | ].
          intros y z Hy. apply in_or_app. right. exact Hy.
        - constructor; eapply rel_pskl_mono; [ exact HrQ | intros y z Hy; apply in_or_app; right; exact Hy | intros y Hy; exact Hy ].
        - exact HrΘ1. }
      assert (Hinj' : rel_inj (ρe ++ ρ) V)
        by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
      assert (Hab' : rel_atom (ρe ++ ρ) V x b)
        by (eapply rel_atom_incl;
            [ exact Hab | intros y z Hy; apply in_or_app; right; exact Hy ]).
      assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V x y -> y = b).
      { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
        - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
        - exact (Hβfun y Hat0). }
      split.
      { eapply flex_agree_reattach;
          [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
          | intros y Hy _; exact Hy
          | intros HxV0; contradiction
          | split; intros Hf; exfalso;
            [ exact (@a_flex_tvar_cons_absent x (abind_var_skl Q0) Θ1 x
                       ltac:(discriminate) ltac:(intros t; discriminate)
                       Hxd Hf)
            | exact (@a_flex_tvar_cons_absent b (abind_var_skl Q2) Θ1' b
                       ltac:(discriminate) ltac:(intros t; discriminate)
                       Hbnd1 Hf) ] ]. }
      split.
      { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
        split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
        intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
        split; [ | exact Hb0 ].
        destruct (Hdom1 _ _ Hin) as [Hd1 _].
        assert (Hne0 : a0 <> x)
          by (intros Ex; rewrite Ex in Hd1; contradiction).
        clear - Ha0 Hne0 Hftsub. fsetdec. }
      intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  - (* Flex-Flex-Id *)
    intros Θ0 α Hflα.
    intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov.
    assert (Hαd : α `in` dom Θ0) by (exact (a_flex_tvar_in_dom Hflα)).
    assert (Eab : α' = β') by (exact (Hfun α α' β' Hαd Hrα Hrβ)).
    subst β'.
    assert (Hfl2' : a_flex_tvar Θ0' α')
      by (exact (proj1 (flex_agree_rel_use Hagr Hrα) Hflα)).
    exists S0, (@nil (atom * atom)%type), Θ0'.
    split; [ apply e_unify__flex_id; exact Hfl2' | ].
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* Flex-Flex-L *)
    intros Θ0 α β Hne Hflβ.
    intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Hαd : α `in` dom ((α ~ abind_flex_mono) ++ Θ0))
      by (simpl; clear; fsetdec).
    assert (Eb : α' = b) by (exact (Hfun α α' b Hαd Hrα Hab)). subst α'.
    assert (Hne2 : b <> β').
    { intros Ex. apply Hne. rewrite Ex in Hrα.
      exact (Hinj α β β' Hrα Hrβ). }
    assert (Hflβ2 : a_flex_tvar Θ0'' β').
    { assert (Hbig : a_flex_tvar ((α ~ abind_flex_mono) ++ Θ0) β)
        by (apply a_flex_tvar_prepend; exact Hflβ).
      apply (proj1 (flex_agree_rel_use Hagr Hrβ)) in Hbig.
      rewrite (@a_flex_tvar_cons_other b abind_flex_mono Θ0'' β'
                 ltac:(intros Ex; apply Hne2; symmetry; exact Ex)) in Hbig.
      exact Hbig. }
    exists S0, (@nil (atom * atom)%type),
      ((b ~ abind_flex_mono_def (ptyp_var_f β')) ++ Θ0'').
    split; [ apply e_unify__flex_l; [ exact Hne2 | exact Hflβ2 ] | ].
    simpl.
    split.
    { apply rel_aenv__cons; [ exact Hab | | exact Hrest ].
      constructor. unfold rel_ptyp. simpl. constructor. exact Hrβ. }
    split.
    { eapply flex_agree_rel_head_swap;
        [ exact Hagr | left; reflexivity | right; eexists; reflexivity
        | left; reflexivity | right; eexists; reflexivity ]. }
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* Flex-Flex-R *)
    intros Θ0 α β Hne Hflα.
    intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Hβd : β `in` dom ((β ~ abind_flex_mono) ++ Θ0))
      by (simpl; clear; fsetdec).
    assert (Eb : β' = b) by (exact (Hfun β β' b Hβd Hrβ Hab)). subst β'.
    assert (Hne2 : α' <> b).
    { intros Ex. apply Hne. rewrite Ex in Hrα.
      exact (Hinj α β b Hrα Hab). }
    assert (Hflα2 : a_flex_tvar Θ0'' α').
    { assert (Hbig : a_flex_tvar ((β ~ abind_flex_mono) ++ Θ0) α)
        by (apply a_flex_tvar_prepend; exact Hflα).
      apply (proj1 (flex_agree_rel_use Hagr Hrα)) in Hbig.
      rewrite (@a_flex_tvar_cons_other b abind_flex_mono Θ0'' α' Hne2) in Hbig.
      exact Hbig. }
    exists S0, (@nil (atom * atom)%type),
      ((b ~ abind_flex_mono_def (ptyp_var_f α')) ++ Θ0'').
    split; [ apply e_unify__flex_r; [ exact Hne2 | exact Hflα2 ] | ].
    simpl.
    split.
    { apply rel_aenv__cons; [ exact Hab | | exact Hrest ].
      constructor. unfold rel_ptyp. simpl. constructor. exact Hrα. }
    split.
    { eapply flex_agree_rel_head_swap;
        [ exact Hagr | left; reflexivity | right; eexists; reflexivity
        | left; reflexivity | right; eexists; reflexivity ]. }
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* ⭐ Flex-Flex-Assign — the unify layer's descent into CONSISTENCY *)
    intros Θ0 Θ1 α1 τ α β Q Hflα Hflβ Hα1d HD IH.
    intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'.
    inversion Hbd as [ | | t1 t2 Hrτ | A1 A2 HrA | Q1 Q2 HrQ ]; subst.
    assert (Huq1 : uniq ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq ((b ~ abind_flex_mono_def t2) ++ Θ0''))
      by (exact Huq2p).
    assert (HwfC : {{ ⊢ Θ0 }}a)
      by (eapply (@a_wf_aenv_strip_prefix ((α1 ~ abind_flex_mono_def τ)));
          exact Hwf).
    assert (Huq2C : uniq Θ0'') by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv Θ0'' [<=] S0)
      by (simpl in Hftv2; clear - Hftv2; fsetdec).
    assert (Hτdom : ftvar_in_ptyp τ [<=] dom Θ0)
      by (apply a_wf_ptyp_ftv_dom;
          exact (proj1 (@a_wf_aenv_mid_def_inv nil α1 τ Θ0 ltac:(constructor)
                          ltac:(simpl_env; exact Hwf)))).
    assert (Hτ2dom : ftvar_in_ptyp t2 [<=] S0)
      by (simpl in Hftv2; clear - Hftv2; fsetdec).
    assert (Hβnd : α1 `notin` dom Θ0)
      by (clear - Huq1; destruct_uniq; fsetdec).
    assert (Hbnd : b `notin` dom Θ0'')
      by (clear - Huq2; destruct_uniq; fsetdec).
    assert (Hsc : ftvar_in_aenv ((α1 ~ abind_flex_mono_def τ) ++ Θ0)
                  [<=] dom ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (HscC : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hα1d0 : α1 `in` dom ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      by (simpl; clear; fsetdec).
    assert (Hβfun : forall y, rel_atom ρ V α1 y -> y = b)
      by (intros y Hy; exact (Hfun α1 y b Hα1d0 Hy Hab)).
    remember (V ∩ ftvar_in_aenv Θ0) as VC eqn:EVC.
    assert (HVC : VC [<=] V) by (subst VC; clear; fsetdec).
    assert (HVCsplit : forall y, y `in` V -> y <> α1 -> y `in` VC).
    { intros y Hy Hne0. subst VC.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      assert (Hyd : y `in` dom ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
        by (clear - Hy HVdom; fsetdec).
      simpl in Hyd. clear - Hy Hne0 Hyd Hds. fsetdec. }
    assert (HVCne : forall y, y `in` VC -> y <> α1).
    { intros y Hy Ex. rewrite Ex in Hy.
      assert (Hin : α1 `in` ftvar_in_aenv Θ0)
        by (subst VC; clear - Hy; fsetdec).
      clear - Hin HscC Hβnd. fsetdec. }
    assert (HrΘC : rel_aenv ρ VC Θ0 Θ0'').
    { eapply rel_aenv_shrink_V; [ exact Hrest | ].
      intros y Hy Hf. subst VC.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hy Hf Hds. fsetdec. }
    assert (HrPsub : rel_ptyp ρ V (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β))
                       (subst_ptyp_in_ptyp t2 b (ptyp_var_f β'))).
    { apply rel_ptyp_subst;
        [ unfold rel_ptyp; simpl; constructor; exact Hrβ
        | exact Hrτ | exact Hab | exact Hinj | exact Hβfun ]. }
    assert (HrVsub : rel_ptyp ρ V (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))
                       (subst_ptyp_in_ptyp t2 b (ptyp_var_f α'))).
    { apply rel_ptyp_subst;
        [ unfold rel_ptyp; simpl; constructor; exact Hrα
        | exact Hrτ | exact Hab | exact Hinj | exact Hβfun ]. }
    assert (Hshr : forall (y0 : atom) x, x `in` V ->
              x `in` ftvar_in_pskl (ptyp_to_pskl
                        (subst_ptyp_in_ptyp τ α1 (ptyp_var_f y0))) ->
              x `in` VC).
    { intros y0 x Hx Hin.
      rewrite ftvar_ptyp_to_pskl in Hin.
      rewrite ftvar_in_ptyp_subst_ptyp_in_ptyp_upper in Hin.
      destruct (AtomSetProperties.In_dec x (ftvar_in_ptyp τ)) as [Hxτ | Hxτ].
      - subst VC.
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
        clear - Hx Hxτ Hτdom Hds. fsetdec.
      - apply HVCsplit; [ exact Hx | ].
        intros Ex. rewrite Ex in Hin, Hxτ. clear - Hin Hxτ.
        simpl in Hin. fsetdec. }
    assert (HrPsubC : rel_pskl ρ VC
              (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
              (ptyp_to_pskl (subst_ptyp_in_ptyp t2 b (ptyp_var_f β'))))
      by (eapply rel_pskl_shrink_V;
          [ exact HrPsub | intros x Hx Hf; exact (Hshr β x Hx Hf) ]).
    assert (HrVsubC : rel_pskl ρ VC
              (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α)))
              (ptyp_to_pskl (subst_ptyp_in_ptyp t2 b (ptyp_var_f α'))))
      by (eapply rel_pskl_shrink_V;
          [ exact HrVsub | intros x Hx Hf; exact (Hshr α x Hx Hf) ]).
    assert (HatomsC : rel_atoms ρ VC empty empty)
      by (intros y z _; split; intros Hin0; exfalso; clear - Hin0; fsetdec).
    assert (HagrC : flex_agree_rel ρ VC Θ0 Θ0'')
      by (eapply flex_agree_peel_cons;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | exact HVC | exact HVCne ]).
    assert (HinjC : rel_inj ρ VC)
      by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVC ]).
    assert (HfunC : rel_fun ρ VC (dom Θ0)).
    { eapply rel_fun_weaken;
        [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVC ]
        | intros y z Hy; exact Hy
        | simpl; clear; fsetdec ]. }
    assert (HblkC : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom Θ0 ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne0 : a0 <> α1)
          by (intros Ex; rewrite Ex in Ha0; contradiction).
        simpl. clear - Hn0 Hne0. fsetdec. }
    assert (HdΘC : dom Θ0'' [<=] S0)
      by (simpl in HdΘ; clear - HdΘ; fsetdec).
    assert (HcovC : VC ∪ cols_r ρ [<=] S0) by (clear - Hcov HVC; fsetdec).
    assert (Hα'S : α' `in` S0).
    { assert (Hbig : a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) α)
        by exact Hflα.
      apply (proj1 (flex_agree_rel_use Hagr Hrα)) in Hbig.
      pose proof (a_flex_tvar_in_dom Hbig) as Hin.
      simpl in HdΘ, Hin. clear - Hin HdΘ. fsetdec. }
    assert (Hβ'S : β' `in` S0).
    { assert (Hbig : a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β)
        by exact Hflβ.
      apply (proj1 (flex_agree_rel_use Hagr Hrβ)) in Hbig.
      pose proof (a_flex_tvar_in_dom Hbig) as Hin.
      simpl in HdΘ, Hin. clear - Hin HdΘ. fsetdec. }
    assert (HcovS : ftvar_in_pskl (ptyp_to_pskl
                      (subst_ptyp_in_ptyp t2 b (ptyp_var_f β')))
                    ∪ ftvar_in_pskl (ptyp_to_pskl
                      (subst_ptyp_in_ptyp t2 b (ptyp_var_f α'))) [<=] S0).
    { repeat rewrite ftvar_ptyp_to_pskl.
      repeat rewrite ftvar_in_ptyp_subst_ptyp_in_ptyp_upper.
      simpl. simpl in HdΘ.
      clear - Hτ2dom HdΘ Hα'S Hβ'S. fsetdec. }
    assert (HcovΔ : empty ∪ empty [<=] S0) by (clear; fsetdec).
    (* ---- the wf package the consis premise wants ---- *)
    assert (Hbα1 : binds α1 (abind_flex_mono_def τ)
                     ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      by (unfold binds; simpl; left; reflexivity).
    assert (Hτmono : mono_ptyp τ)
      by (exact (@a_wf_aenv_binds_def_mono _ α1 τ Hwf Hbα1)).
    assert (Hτwf : a_wf_ptyp Θ0 τ)
      by (exact (proj1 (@a_wf_aenv_mid_def_inv nil α1 τ Θ0
                          ltac:(constructor) ltac:(simpl_env; exact Hwf)))).
    assert (Hbt : forall y, a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) y ->
                  y <> α1 -> a_binds_tvar y Θ0).
    { intros y Hy Hne0.
      rewrite (@a_flex_tvar_cons_other α1 (abind_flex_mono_def τ) Θ0 y Hne0)
        in Hy.
      destruct Hy as [Hb0 | [t Hb0]];
        [ right; left | right; right; exists t ]; exact Hb0. }
    assert (Hwfsub : forall y,
              a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) y ->
              {{ Θ0 ⨟ empty ⊢ₚₛ
                 (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f y))) }}a).
    { intros y Hy. simpl.
      match goal with
      | |- context [ if ?X then _ else _ ] => destruct X as [Eyα | Hne0]
      end.
      - apply a_wf_pskl_mono_ptyp; [ exact Hτmono | exact Hτwf ].
      - apply a_wf_pskl__var. exact (Hbt y Hy Hne0). }
    assert (HΔtv : forall γ, γ `in` (empty ∪ empty) ->
                   binds γ abind_tvar Θ0)
      by (intros γ Hγ; exfalso; clear - Hγ; fsetdec).
    assert (Hnfd : no_flex_dep (empty ∪ empty) Θ0)
      by (intros γ t Hb0; clear; fsetdec).
    assert (Hfaf : flex_above_free (empty ∪ empty) Θ0)
      by (intros Θa γ bb Θb Heq Hne0; clear; fsetdec).
    assert (HΔsc : empty ∪ empty [<=] ftvar_in_aenv Θ0) by (clear; fsetdec).
    destruct (IH S0 Θ0'' empty empty
                (ptyp_to_pskl (subst_ptyp_in_ptyp t2 b (ptyp_var_f β')))
                (ptyp_to_pskl (subst_ptyp_in_ptyp t2 b (ptyp_var_f α')))
                ρ VC HrΘC HrPsubC HrVsubC HatomsC HatomsC HagrC HinjC HfunC
                HwfC Huq2C Hftv2C ltac:(subst VC; clear; fsetdec) HblkC HdΘC HcovC
                HcovS HcovΔ (Hwfsub β Hflβ) (Hwfsub α Hflα) HΔtv Hnfd Hfaf
                HΔsc)
      as (S1 & ρe & Θ1' & Q' & D2 & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
    assert (Hbnd1 : b `notin` dom Θ1').
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper)) _ _ _ _ _ _ _
                    _ _ D2) as Hup.
      assert (HbS0 : b `in` S0) by (simpl in HdΘ; clear - HdΘ; fsetdec).
      clear - Hup Hbnd HbS0. fsetdec. }
    exists S1, ρe, ((b ~ abind_flex_mono_def t2) ++ Θ1').
    split.
    { apply e_unify__flex_assign with (τ := t2) (Q := Q');
        [ | | exact D2 ].
      - assert (Hbig : a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) α)
          by exact Hflα.
        exact (proj1 (flex_agree_rel_use Hagr Hrα) Hbig).
      - assert (Hbig : a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β)
          by exact Hflβ.
        exact (proj1 (flex_agree_rel_use Hagr Hrβ) Hbig). }
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros y z Hy. apply in_or_app. right. exact Hy.
      - constructor. unfold rel_ptyp in Hrτ |- *.
        eapply rel_pskl_mono;
          [ exact Hrτ | intros y z Hy; apply in_or_app; right; exact Hy
          | intros y Hy; exact Hy ].
      - eapply rel_aenv_mono;
          [ exact HrΘ1 | intros y z Hy; exact Hy | exact HVC ]. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V α1 b)
      by (eapply rel_atom_incl;
          [ exact Hab | intros y z Hy; apply in_or_app; right; exact Hy ]).
    assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V α1 y -> y = b).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hβfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
        | exact HVCsplit
        | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
        | split; intros _; apply a_flex_tvar_head_flexish;
          right; eexists; reflexivity ]. }
    assert (Hftsub : ftvar_in_aenv ((α1 ~ abind_flex_mono_def τ) ++ Θ0)
                     [<=] add α1 (ftvar_in_aenv Θ0)).
    { simpl. pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hτdom Hds. fsetdec. }
    split.
    { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
      split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
      intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
      split; [ | exact Hb0 ].
      destruct (Hdom1 _ _ Hin) as [Hd1 _].
      assert (Hne0 : a0 <> α1)
        by (intros Ex; rewrite Ex in Hd1; contradiction).
      clear - Ha0 Hne0 Hftsub. fsetdec. }
    intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  - (* Flex-Flex-Skip *)
    intros Θ0 Θ1 c α β Hneα0 Hneβ0 Hcd HD IH.
    intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b0 & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'.
    assert (Huq1 : uniq ((c ~ abind_flex_mono) ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq ((b0 ~ bdd) ++ Θ0'')) by (exact Huq2p).
    assert (HwfC : {{ ⊢ Θ0 }}a)
      by (eapply (@a_wf_aenv_strip_prefix ((c ~ abind_flex_mono))); exact Hwf).
    assert (Huq2C : uniq Θ0'') by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv Θ0'' [<=] S0)
      by (simpl in Hftv2; clear - Hftv2; fsetdec).
    assert (Hcnd : c `notin` dom Θ0) by (clear - Huq1; destruct_uniq; fsetdec).
    assert (Hbnd : b0 `notin` dom Θ0'') by (clear - Huq2; destruct_uniq; fsetdec).
    assert (Hpay : ftvar_in_abind abind_flex_mono [<=] dom Θ0)
      by (eapply a_wf_aenv_cons_payload_ftv; exact Hwf).
    assert (Hsc : ftvar_in_aenv ((c ~ abind_flex_mono) ++ Θ0) [<=] dom ((c ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom ((c ~ abind_flex_mono) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (HscC : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hcd0 : c `in` dom ((c ~ abind_flex_mono) ++ Θ0)) by (simpl; clear; fsetdec).
    assert (Hcfun : forall y, rel_atom ρ V c y -> y = b0)
      by (intros y Hy; exact (Hfun c y b0 Hcd0 Hy Hab)).
    assert (Hneα : α <> c) by (intros Ex; apply Hneα0; symmetry; exact Ex).
    assert (Hneβ : β <> c) by (intros Ex; apply Hneβ0; symmetry; exact Ex).
    inversion Hbd; subst.
    assert (Hne2α : α' <> b0).
    { intros Ex. apply Hneα. rewrite Ex in Hrα.
      exact (Hinj α c b0 Hrα Hab). }
    assert (Hne2β : β' <> b0).
    { intros Ex. apply Hneβ. rewrite Ex in Hrβ.
      exact (Hinj β c b0 Hrβ Hab). }
    remember (V ∩ ftvar_in_aenv Θ0) as VS eqn:EVS.
    assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
    assert (HVSsplit : forall y, y `in` V -> y <> c -> y `in` VS).
    { intros y Hy Hne0. subst VS.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      assert (Hyd : y `in` dom ((c ~ abind_flex_mono) ++ Θ0)) by (clear - Hy HVdom; fsetdec).
      simpl in Hyd. clear - Hy Hne0 Hyd Hds. fsetdec. }
    assert (HVSne : forall y, y `in` VS -> y <> c).
    { intros y Hy Ex. rewrite Ex in Hy.
      assert (Hin : c `in` ftvar_in_aenv Θ0) by (subst VS; clear - Hy; fsetdec).
      clear - Hin HscC Hcnd. fsetdec. }
    assert (HrΘS : rel_aenv ρ VS Θ0 Θ0'').
    { eapply rel_aenv_shrink_V; [ exact Hrest | ].
      intros y Hy Hf. subst VS.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hy Hf Hds. fsetdec. }
    assert (HrαS : rel_atom ρ VS α α').
    { inversion Hrα; subst.
      - apply rel_atom__pair; assumption.
      - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hneα ]. }
    assert (HrβS : rel_atom ρ VS β β').
    { inversion Hrβ; subst.
      - apply rel_atom__pair; assumption.
      - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hneβ ]. }
    assert (HagrS : flex_agree_rel ρ VS Θ0 Θ0'')
      by (eapply flex_agree_peel_cons;
          [ exact Hagr | exact Hab | exact Hinj | exact Hcfun | exact Hcnd
          | exact Hbnd | exact HVS | exact HVSne ]).
    assert (HinjS : rel_inj ρ VS)
      by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVS ]).
    assert (HfunS : rel_fun ρ VS (dom Θ0)).
    { eapply rel_fun_weaken;
        [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVS ]
        | intros y z Hy; exact Hy | simpl; clear; fsetdec ]. }
    assert (HflαS : a_flex_tvar Θ0 α)
      by (rewrite <- (@a_flex_tvar_cons_other c abind_flex_mono Θ0 α Hneα); exact Hfl1).
    assert (HflβS : a_flex_tvar Θ0 β)
      by (rewrite <- (@a_flex_tvar_cons_other c abind_flex_mono Θ0 β Hneβ); exact Hfl2).
    assert (HscpS : VS [<=] ftvar_in_aenv Θ0) by (subst VS; clear; fsetdec).
    assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom Θ0 ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne0 : a0 <> c) by (intros Ex; rewrite Ex in Ha0; contradiction).
        simpl. clear - Hn0 Hne0. fsetdec. }
    assert (HdΘS : dom Θ0'' [<=] S0) by (simpl in HdΘ; clear - HdΘ; fsetdec).
    assert (HcovS : VS ∪ cols_r ρ [<=] S0) by (clear - Hcov HVS; fsetdec).
    destruct (IH S0 Θ0'' α' β' ρ VS HrΘS HrαS HrβS HagrS HinjS HfunS
                HflαS HflβS HwfC Huq2C Hftv2C HscpS HblkS HdΘS HcovS)
      as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
    assert (Hbnd1 : b0 `notin` dom Θ1').
    { pose proof ((proj1 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ D2) as Hup.
      assert (HbS0 : b0 `in` S0) by (simpl in HdΘ; clear - HdΘ; fsetdec).
      clear - Hup Hbnd HbS0. fsetdec. }
    exists S1, ρe, ((b0 ~ abind_flex_mono) ++ Θ1').
    split; [ apply e_unify__flex_skip;
             [ intros Ex; apply Hne2α; symmetry; exact Ex
             | intros Ex; apply Hne2β; symmetry; exact Ex | exact D2 ] | ].
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros y z Hy. apply in_or_app. right. exact Hy.
      - eapply rel_abind_mono;
          [ exact Hbd | intros y z Hy; apply in_or_app; right; exact Hy
          | intros y Hy; exact Hy ].
      - eapply rel_aenv_mono;
          [ exact HrΘ1 | intros y z Hy; exact Hy | exact HVS ]. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V c b0)
      by (eapply rel_atom_incl;
          [ exact Hab | intros y z Hy; apply in_or_app; right; exact Hy ]).
    assert (Hcfun' : forall y, rel_atom (ρe ++ ρ) V c y -> y = b0).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hcfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hcfun'
        | exact HVSsplit
        | intros HcV; symmetry; apply Hcfun; apply rel_atom__id; exact HcV
        | split; intros _; apply a_flex_tvar_head_flexish;
          left; reflexivity ]. }
    assert (Hftsub : ftvar_in_aenv ((c ~ abind_flex_mono) ++ Θ0)
                     [<=] add c (ftvar_in_aenv Θ0)).
    { simpl. pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hpay Hds. fsetdec. }
    split.
    { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
      split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
      intros a0 b1 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb1].
      split; [ | exact Hb1 ].
      destruct (Hdom1 _ _ Hin) as [Hd1 _].
      assert (Hne0 : a0 <> c) by (intros Ex; rewrite Ex in Hd1; contradiction).
      clear - Ha0 Hne0 Hftsub. fsetdec. }
    intros a0 b1 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  - (* Flex-Flex-Skip' *)
    intros Θ0 Θ1 c bc α β Hshape Hcd HD IH.
    intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b0 & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'.
    assert (Huq1 : uniq ((c ~ bc) ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq ((b0 ~ bdd) ++ Θ0'')) by (exact Huq2p).
    assert (HwfC : {{ ⊢ Θ0 }}a)
      by (eapply (@a_wf_aenv_strip_prefix ((c ~ bc))); exact Hwf).
    assert (Huq2C : uniq Θ0'') by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv Θ0'' [<=] S0)
      by (simpl in Hftv2; clear - Hftv2; fsetdec).
    assert (Hcnd : c `notin` dom Θ0) by (clear - Huq1; destruct_uniq; fsetdec).
    assert (Hbnd : b0 `notin` dom Θ0'') by (clear - Huq2; destruct_uniq; fsetdec).
    assert (Hpay : ftvar_in_abind bc [<=] dom Θ0)
      by (eapply a_wf_aenv_cons_payload_ftv; exact Hwf).
    assert (Hsc : ftvar_in_aenv ((c ~ bc) ++ Θ0) [<=] dom ((c ~ bc) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom ((c ~ bc) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (HscC : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hcd0 : c `in` dom ((c ~ bc) ++ Θ0)) by (simpl; clear; fsetdec).
    assert (Hcfun : forall y, rel_atom ρ V c y -> y = b0)
      by (intros y Hy; exact (Hfun c y b0 Hcd0 Hy Hab)).
    assert (Hnf : bc <> abind_flex_mono
                  /\ (forall t, bc <> abind_flex_mono_def t)).
    { destruct Hshape as [-> | [[A0 ->] | [Q0 ->]]]; split;
        solve [ discriminate | intros t; discriminate ]. }
    destruct Hnf as [Hnf1 Hnf2].
    assert (Hshape2 : bdd = abind_tvar
                      \/ (exists A, bdd = abind_var_typ A)
                      \/ (exists Q, bdd = abind_var_skl Q)).
    { destruct Hshape as [E | [[A0 E] | [Q0 E]]]; rewrite E in Hbd;
        inversion Hbd; subst;
        [ left; reflexivity | right; left; eexists; reflexivity
        | right; right; eexists; reflexivity ]. }
    assert (Hnf2' : bdd <> abind_flex_mono
                    /\ (forall t, bdd <> abind_flex_mono_def t)).
    { destruct Hshape2 as [-> | [[A0 ->] | [Q0 ->]]]; split;
        solve [ discriminate | intros t; discriminate ]. }
    destruct Hnf2' as [Hnf1b Hnf2b].
    assert (Hneα : α <> c).
    { intros Ex. rewrite Ex in Hfl1.
      exact (@a_flex_tvar_cons_absent c bc Θ0 c Hnf1 Hnf2 Hcnd Hfl1). }
    assert (Hneβ : β <> c).
    { intros Ex. rewrite Ex in Hfl2.
      exact (@a_flex_tvar_cons_absent c bc Θ0 c Hnf1 Hnf2 Hcnd Hfl2). }
    assert (Hne2α : α' <> b0).
    { intros Ex. apply Hneα. rewrite Ex in Hrα.
      exact (Hinj α c b0 Hrα Hab). }
    assert (Hne2β : β' <> b0).
    { intros Ex. apply Hneβ. rewrite Ex in Hrβ.
      exact (Hinj β c b0 Hrβ Hab). }
    remember (V ∩ ftvar_in_aenv Θ0) as VS eqn:EVS.
    assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
    assert (HVSsplit : forall y, y `in` V -> y <> c -> y `in` VS).
    { intros y Hy Hne0. subst VS.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      assert (Hyd : y `in` dom ((c ~ bc) ++ Θ0)) by (clear - Hy HVdom; fsetdec).
      simpl in Hyd. clear - Hy Hne0 Hyd Hds. fsetdec. }
    assert (HVSne : forall y, y `in` VS -> y <> c).
    { intros y Hy Ex. rewrite Ex in Hy.
      assert (Hin : c `in` ftvar_in_aenv Θ0) by (subst VS; clear - Hy; fsetdec).
      clear - Hin HscC Hcnd. fsetdec. }
    assert (HrΘS : rel_aenv ρ VS Θ0 Θ0'').
    { eapply rel_aenv_shrink_V; [ exact Hrest | ].
      intros y Hy Hf. subst VS.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hy Hf Hds. fsetdec. }
    assert (HrαS : rel_atom ρ VS α α').
    { inversion Hrα; subst.
      - apply rel_atom__pair; assumption.
      - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hneα ]. }
    assert (HrβS : rel_atom ρ VS β β').
    { inversion Hrβ; subst.
      - apply rel_atom__pair; assumption.
      - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hneβ ]. }
    assert (HagrS : flex_agree_rel ρ VS Θ0 Θ0'')
      by (eapply flex_agree_peel_cons;
          [ exact Hagr | exact Hab | exact Hinj | exact Hcfun | exact Hcnd
          | exact Hbnd | exact HVS | exact HVSne ]).
    assert (HinjS : rel_inj ρ VS)
      by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVS ]).
    assert (HfunS : rel_fun ρ VS (dom Θ0)).
    { eapply rel_fun_weaken;
        [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVS ]
        | intros y z Hy; exact Hy | simpl; clear; fsetdec ]. }
    assert (HflαS : a_flex_tvar Θ0 α)
      by (rewrite <- (@a_flex_tvar_cons_other c bc Θ0 α Hneα); exact Hfl1).
    assert (HflβS : a_flex_tvar Θ0 β)
      by (rewrite <- (@a_flex_tvar_cons_other c bc Θ0 β Hneβ); exact Hfl2).
    assert (HscpS : VS [<=] ftvar_in_aenv Θ0) by (subst VS; clear; fsetdec).
    assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom Θ0 ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne0 : a0 <> c) by (intros Ex; rewrite Ex in Ha0; contradiction).
        simpl. clear - Hn0 Hne0. fsetdec. }
    assert (HdΘS : dom Θ0'' [<=] S0) by (simpl in HdΘ; clear - HdΘ; fsetdec).
    assert (HcovS : VS ∪ cols_r ρ [<=] S0) by (clear - Hcov HVS; fsetdec).
    destruct (IH S0 Θ0'' α' β' ρ VS HrΘS HrαS HrβS HagrS HinjS HfunS
                HflαS HflβS HwfC Huq2C Hftv2C HscpS HblkS HdΘS HcovS)
      as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
    assert (Hbnd1 : b0 `notin` dom Θ1').
    { pose proof ((proj1 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ D2) as Hup.
      assert (HbS0 : b0 `in` S0) by (simpl in HdΘ; clear - HdΘ; fsetdec).
      clear - Hup Hbnd HbS0. fsetdec. }
    exists S1, ρe, ((b0 ~ bdd) ++ Θ1').
    split; [ apply e_unify__skip_other; [ exact Hshape2 | exact D2 ] | ].
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros y z Hy. apply in_or_app. right. exact Hy.
      - eapply rel_abind_mono;
          [ exact Hbd | intros y z Hy; apply in_or_app; right; exact Hy
          | intros y Hy; exact Hy ].
      - eapply rel_aenv_mono;
          [ exact HrΘ1 | intros y z Hy; exact Hy | exact HVS ]. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V c b0)
      by (eapply rel_atom_incl;
          [ exact Hab | intros y z Hy; apply in_or_app; right; exact Hy ]).
    assert (Hcfun' : forall y, rel_atom (ρe ++ ρ) V c y -> y = b0).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hcfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hcfun'
        | exact HVSsplit
        | intros HcV; symmetry; apply Hcfun; apply rel_atom__id; exact HcV
        | split; intros Hf; exfalso;
          [ exact (@a_flex_tvar_cons_absent c bc Θ1 c Hnf1 Hnf2 Hcd Hf)
          | exact (@a_flex_tvar_cons_absent b0 bdd Θ1' b0 Hnf1b Hnf2b
                     Hbnd1 Hf) ] ]. }
    assert (Hftsub : ftvar_in_aenv ((c ~ bc) ++ Θ0)
                     [<=] add c (ftvar_in_aenv Θ0)).
    { simpl. pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hpay Hds. fsetdec. }
    split.
    { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
      split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
      intros a0 b1 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb1].
      split; [ | exact Hb1 ].
      destruct (Hdom1 _ _ Hin) as [Hd1 _].
      assert (Hne0 : a0 <> c) by (intros Ex; rewrite Ex in Hd1; contradiction).
      clear - Ha0 Hne0 Hftsub. fsetdec. }
    intros a0 b1 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  - (* C-Ghost *)
    intros Δ1 Δ2 Θ0 P0 Hdisj.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', P0'.
    split.
    { apply e_consis__ghost.
      eapply rel_atoms_disjoint; [ exact Hrd2 | exact HrP0 | exact Hdisj ]. }
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ exact HrP0 | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* C-Unit *)
    intros Δ1 Δ2 Θ0.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP; subst. inversion HrP0; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', pskl_unit.
    split; [ apply e_consis__unit | ].
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ constructor | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* C-Rigid *)
    intros Δ1 Δ2 Θ0 α Hb.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP as [ | n0 | x0 a2 Hat2 | | | | ]; subst.
    inversion HrP0 as [ | n1 | x1 a1 Hat1 | | | | ]; subst.
    assert (Hαd : α `in` dom Θ0) by (eapply binds_In; exact Hb).
    assert (Ea : a1 = a2) by (exact (Hfun α a1 a2 Hαd Hat1 Hat2)). subst a1.
    destruct (@rel_aenv_binds_l ρ V Θ0 Θ0' α abind_tvar HrΘ Hb)
      as (b0 & b2 & Hat0 & Hab0 & Hbd0).
    assert (Eb : b0 = a2) by (exact (Hfun α b0 a2 Hαd Hat0 Hat2)). subst b0.
    inversion Hab0; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', (pskl_var_f a2).
    split; [ apply e_consis__rigid; exact Hbd0 | ].
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ constructor; exact Hat2 | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b1 Hin. inversion Hin.
  - (* ⭐ U-Arrow — the second half runs at the FIRST half's output, so
       everything the motive says about the context is re-established there *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 HD1 IH1 HD2 IH2.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 P0a2 P0b2 HrP0a HrP0b
                      | A3 A4 Hu1 | | A5 A6 Hu2 ]; subst.
    inversion HrP as [ | n1 | u3 v3 Hu3 | B1 B2 P12 P22 HrP1 HrP2
                     | B3 B4 Hu4 | | B5 B6 Hu5 ]; subst.
    inversion Hwfp0 as [ Θx Δx | Θx Δx αx Hbx | Θx Δx Xa Xb Hw0a Hw0b
                       | Lx Θx Δx Xp Hallx | Θx Δx
                       | Θx Δx Xp Hgx Hwix ]; subst.
    inversion Hwfp as [ Θy Δy | Θy Δy αy Hby | Θy Δy Ya Yb Hw1a Hw1b
                      | Ly Θy Δy Yp Hally | Θy Δy
                      | Θy Δy Yp Hgy Hwiy ]; subst.
    assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hdm0 : dom Θ0 [<=] dom Θ1) by (exact (auc_dom_mono_consis HD1)).
    assert (Hdm1 : dom Θ1 [<=] dom Θ2) by (exact (auc_dom_mono_consis HD2)).
    (* ---- the first premise ---- *)
    assert (Hblk1 : forall a, a `in` dom Θ1 -> a `notin` dom Θ0 ->
                    a `notin` cols_l ρ).
    { intros a Ha Hn. apply Hblk; [ clear - Ha Hdm1; fsetdec | exact Hn ]. }
    assert (HcovP1 : ftvar_in_pskl P0a2 ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    destruct (IH1 S0 Θ0' Δ1' Δ2' P0a2 P12 ρ V HrΘ HrP0a HrP1 Hrd1 Hrd2 Hagr
                Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk1 HdΘ Hcov HcovP1 HcovΔ
                Hw0a Hw1a HΔtv Hnfd Hfaf HΔsc)
      as (S1 & ρe1 & Θ1' & Q1' & D1e & HrΘ1 & Hagr1 & HrQ1 & Hext1 & Hdom1).
    pose proof (e_consis_supply_grows D1e) as Hgr1.
    (* ---- side 2's context, re-established at the first half's output ---- *)
    assert (HdΘ1 : dom Θ1' [<=] S1).
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ _ _ _ D1e) as Hup.
      clear - Hup HdΘ Hgr1. fsetdec. }
    assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl P0a2
                    ∪ ftvar_in_pskl P12 [<=] S0)
      by (clear - Hftv2 HcovP1; fsetdec).
    assert (Hftv1 : ftvar_in_aenv Θ1' [<=] S1)
      by (eapply (proj2 (proj2 e_assign_unify_consis_ctx_ftvar));
          [ exact D1e | exact HcovE ]).
    assert (HcovE2 : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl P0a2
                     ∪ ftvar_in_pskl P12 ∪ Δ1' ∪ Δ2' [<=] S0)
      by (clear - HcovE HcovΔ; fsetdec).
    assert (Huq1' : uniq Θ1').
    { pose proof (e_consis_sound D1e Huq2p HcovE2) as Ha1.
      exact ((proj2 (proj2 a_assign_unify_consis_uniq)) _ _ _ _ _ _ _ Ha1
               Huq2p). }
    (* ---- side 1's context, via SOUNDNESS ---- *)
    pose proof ((proj2 (proj2 a_assign_unify_consis_sound)) _ _ _ _ _ _ _ HD1
                  Hwf Hw0a Hw1a HΔtv Hnfd Hfaf) as Hsnd1.
    destruct Hsnd1 as (Hinc1 & HwfΘ1 & Hdm1' & HΔinv1 & Hrest1).
    assert (HΔdom : Δ1 ∪ Δ2 [<=] dom Θ0) by (clear - HΔsc Hsc0; fsetdec).
    assert (Hside1 : (Δ1 ∪ Δ2) ∩ dom Θ1 [<=] dom Θ0)
      by (clear - HΔdom; fsetdec).
    assert (Hside2 : forall α, α `in` (Δ1 ∪ Δ2) -> α `notin` dom Θ0 ->
              α `notin` (ftvar_in_pskl P0a `union` ftvar_in_pskl P1))
      by (intros α Hα Hn; exfalso; clear - HΔdom Hα Hn; fsetdec).
    destruct (HΔinv1 (Δ1 ∪ Δ2) Hnfd Hfaf Hside1 Hside2)
      as (Hnfd1 & Hfaf1 & Hdlt1).
    assert (HΔtv1 : forall α, α `in` (Δ1 ∪ Δ2) -> binds α abind_tvar Θ1).
    { intros α Hα. destruct Hinc1 as [[κ [Hid Hinc]] _].
      eapply a_inc_binds_tvar; [ exact Hinc | exact (HΔtv α Hα) ]. }
    assert (Hd1s : dom Θ1 [<=] ftvar_in_aenv Θ1)
      by (apply dom_subset_ftvar_in_aenv).
    assert (HΔsc1 : Δ1 ∪ Δ2 [<=] ftvar_in_aenv Θ1)
      by (clear - HΔdom Hdm0 Hd1s; fsetdec).
    assert (Hscp1 : V [<=] ftvar_in_aenv Θ1)
      by (clear - Hscp Hsc0 Hdm0 Hd1s; fsetdec).
    assert (Hwfp0b1 : {{ Θ1 ⨟ empty ⊢ₚₛ P0b }}a)
      by (eapply a_isub_wf_pskl; [ exact Hinc1 | exact Hw0b ]).
    assert (Hwfp21 : {{ Θ1 ⨟ empty ⊢ₚₛ P2 }}a)
      by (eapply a_isub_wf_pskl; [ exact Hinc1 | exact Hw1b ]).
    (* ---- the relation, widened by the first half's new pairs ---- *)
    assert (Hinj1 : rel_inj (ρe1 ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (HVdom0 : V [<=] dom Θ0) by (clear - Hscp Hsc0; fsetdec).
    assert (Hfun1 : rel_fun (ρe1 ++ ρ) V (dom Θ1)).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hext1 | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; exact (Hblk1 a Ha Hn)
        | intros a Ha Hn; clear - HVdom0 Hn; fsetdec ]. }
    assert (Hrd1' : rel_atoms (ρe1 ++ ρ) V Δ1 Δ1')
      by (eapply rel_atoms_app;
          [ exact Hrd1 | exact Hext1 | clear - HΔsc; fsetdec
          | clear - HcovΔ; fsetdec ]).
    assert (Hrd2' : rel_atoms (ρe1 ++ ρ) V Δ2 Δ2')
      by (eapply rel_atoms_app;
          [ exact Hrd2 | exact Hext1 | clear - HΔsc; fsetdec
          | clear - HcovΔ; fsetdec ]).
    assert (HrP0b' : rel_pskl (ρe1 ++ ρ) V P0b P0b2)
      by (apply rel_pskl_widen; exact HrP0b).
    assert (HrP2' : rel_pskl (ρe1 ++ ρ) V P2 P22)
      by (apply rel_pskl_widen; exact HrP2).
    assert (Hc1r : cols_r ρe1 [<=] S1).
    { intros y Hy. destruct (cols_r_in_inv _ _ Hy) as (a & Hin).
      destruct (Hdom1 _ _ Hin) as [_ Hd2]. clear - Hd2 HdΘ1. fsetdec. }
    assert (Hcov1 : V ∪ cols_r (ρe1 ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hcov Hc1r Hgr1. fsetdec. }
    assert (Hblk2 : forall a, a `in` dom Θ2 -> a `notin` dom Θ1 ->
                    a `notin` cols_l (ρe1 ++ ρ)).
    { intros a Ha Hn. rewrite cols_l_app.
      assert (Hc1 : a `notin` cols_l ρe1).
      { intros Hy. destruct (cols_l_in_inv _ _ Hy) as (y & Hin).
        destruct (Hdom1 _ _ Hin) as [Hd1 _]. contradiction. }
      assert (Hc2 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn Hdm0; fsetdec ]).
      clear - Hc1 Hc2. fsetdec. }
    assert (HcovP2 : ftvar_in_pskl P0b2 ∪ ftvar_in_pskl P22 [<=] S1)
      by (simpl in HcovP; clear - HcovP Hgr1; fsetdec).
    assert (HcovΔ1 : Δ1' ∪ Δ2' [<=] S1) by (clear - HcovΔ Hgr1; fsetdec).
    destruct (IH2 S1 Θ1' Δ1' Δ2' P0b2 P22 (ρe1 ++ ρ) V HrΘ1 HrP0b' HrP2'
                Hrd1' Hrd2' Hagr1 Hinj1 Hfun1 HwfΘ1 Huq1' Hftv1 Hscp1 Hblk2
                HdΘ1 Hcov1 HcovP2 HcovΔ1 Hwfp0b1 Hwfp21 HΔtv1 Hnfd1 Hfaf1
                HΔsc1)
      as (S2 & ρe2 & Θ2' & Q2' & D2e & HrΘ2 & Hagr2 & HrQ2 & Hext2 & Hdom2).
    exists S2, (ρe2 ++ ρe1), Θ2', (pskl_arrow Q1' Q2').
    split; [ eapply e_consis__arrow; [ exact D1e | exact D2e ] | ].
    rewrite app_assoc.
    split; [ exact HrΘ2 | ].
    split; [ exact Hagr2 | ].
    split.
    { constructor; [ | exact HrQ2 ].
      eapply rel_pskl_mono;
        [ exact HrQ1 | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    assert (Hsc1 : ftvar_in_aenv Θ1 [<=] dom Θ1)
      by (apply a_wf_aenv_ftv_dom; exact HwfΘ1).
    split.
    { eapply rel_ext_app;
        [ exact Hext1 | exact Hext2
        | clear - Hsc0 Hdm0 Hd1s; fsetdec
        | exact Hgr1
        | intros a b Hin; destruct (Hdom1 _ _ Hin) as [Hd1 Hd2];
          split; [ clear - Hd1 Hd1s; fsetdec | clear - Hd2 HdΘ1; fsetdec ] ]. }
    assert (Hdm2' : dom Θ1' [<=] dom Θ2').
    { pose proof (e_consis_sound D2e Huq1'
                    ltac:(clear - Hftv1 HcovP2 HcovΔ1; fsetdec)) as Ha2.
      exact (auc_dom_mono_consis Ha2). }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hdom2 _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; [ clear - Hd1 Hdm1; fsetdec | clear - Hd2 Hdm2'; fsetdec ].
  - (* ⭐⭐ C-ForallInh *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
    eapply lift_consis_forall_inh_row; [ exact Hfr | exact HD | exact IH ].
  - (* ⭐⭐ C-ForallSyn *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
    eapply lift_consis_forall_syn_row; [ exact Hfr | exact HD | exact IH ].
  - (* C-UnivGhost : ⫯ on all three positions, and the IH strips it *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q HD IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 P0b2 HrP0b ]; subst.
    inversion HrP as [ | n1 | u3 v3 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 P12 HrPb ]; subst.
    assert (HcovP1 : ftvar_in_pskl P0b2 ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hwfp01 : {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a)
      by (inversion Hwfp0; subst; rewrite aenv_minus_empty in *; assumption).
    assert (Hwfp1 : {{ Θ0 ⨟ empty ⊢ₚₛ P }}a)
      by (inversion Hwfp; subst; rewrite aenv_minus_empty in *; assumption).
    destruct (IH S0 Θ0' Δ1' Δ2' P0b2 P12 ρ V
                HrΘ HrP0b HrPb Hrd1 Hrd2 Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov
                HcovP1 HcovΔ Hwfp01 Hwfp1 HΔtv Hnfd Hfaf HΔsc)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', (pskl_tophole Q').
    split; [ apply e_consis__univ_ghost; exact De | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ apply rel_pskl__tophole; exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* ⭐⭐ C-UnivGhost1 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
    eapply lift_consis_univ_ghost1_row; [ exact Hfr | exact HD | exact IH ].
  - (* C-UnivGhost2 : the ⫯ is stripped off the SUBJECT only *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf HD IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP as [ | n1 | u3 v3 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 P12 HrPb ]; subst.
    assert (HcovP1 : ftvar_in_pskl P0' ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hwfp1 : {{ Θ0 ⨟ empty ⊢ₚₛ P }}a)
      by (inversion Hwfp; subst; rewrite aenv_minus_empty in *; assumption).
    destruct (IH S0 Θ0' Δ1' Δ2' P0' P12 ρ V
                HrΘ HrP0 HrPb Hrd1 Hrd2 Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov
                HcovP1 HcovΔ Hwfp0 Hwfp1 HΔtv Hnfd Hfaf HΔsc)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split.
    { apply e_consis__univ_ghost2;
        [ eapply rel_pskl_guarded; [ exact HrP0 | exact Hg ]
        | eapply rel_pskl_non_flex; [ exact HrP0 | exact Hagr | exact Hnf ]
        | exact De ]. }
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* C-Flex : hand to the UNIFY IH *)
    intros Δ1 Δ2 Θ0 Θ1 α β HU IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 β2 Hatβ | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 C2 Hu4 ]; subst.
    inversion HrP as [ | n1 | u1 α2 Hatα | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 F2 Hu8 ]; subst.
    destruct ((proj1 (proj2 a_assign_unify_subject_flex)) _ _ _ _ HU)
      as [Hflα Hflβ].
    destruct (IH S0 Θ0' α2 β2 ρ V HrΘ Hatα Hatβ Hagr Hinj Hfun Hflα Hflβ Hwf
                Huq2p Hftv2 Hscp Hblk HdΘ Hcov)
      as (S1 & ρe & Θ1' & De & HrΘ1 & Hagr1 & Hext & Hdom1).
    exists S1, ρe, Θ1', (pskl_var_f α2).
    split; [ apply e_consis__flex; exact De | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrP | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    split; [ exact Hext | ]. exact Hdom1.
  - (* C-FlexL : hand to the ASSIGN IH at Ξ = nil *)
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hnhole HA IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP as [ | n1 | u1 α2 Hatα | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 F2 Hu8 ]; subst.
    assert (Hflα : a_flex_tvar (nil ++ Θ0) α)
      by (exact ((proj1 a_assign_unify_subject_flex) _ _ _ _ _ HA)).
    assert (HcovP0 : ftvar_in_pskl P0' [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (HagrN : flex_agree_rel ρ V (nil ++ Θ0) (nil ++ Θ0'))
      by (simpl_env; exact Hagr).
    assert (HfunN : rel_fun ρ V (dom (nil ++ Θ0))) by (simpl_env; exact Hfun).
    assert (HwfN : {{ ⊢ (nil ++ Θ0) }}a) by (simpl_env; exact Hwf).
    assert (HuqN : uniq (nil ++ Θ0')) by (simpl_env; exact Huq2p).
    assert (HftvN : ftvar_in_aenv (nil ++ Θ0') [<=] S0)
      by (simpl_env; exact Hftv2).
    assert (HscpN : V [<=] ftvar_in_aenv (nil ++ Θ0))
      by (simpl_env; exact Hscp).
    assert (HblkN : forall a, a `in` dom Θ1 -> a `notin` dom (nil ++ Θ0) ->
                    a `notin` cols_l ρ) by (simpl_env; exact Hblk).
    assert (HdΘN : dom (nil ++ Θ0') [<=] S0) by (simpl_env; exact HdΘ).
    assert (HwfpN : {{ (nil ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (simpl_env; exact Hwfp0).
    destruct (IH S0 Θ0' nil α2 P0' ρ V HrΘ (@rel_aenv__nil ρ V) Hatα HrP0
                HagrN Hinj HfunN Hflα HwfN a_decls__nil a_decls__nil HuqN
                HftvN HscpN HblkN HdΘN Hcov HcovP0 HwfpN)
      as (S1 & ρe & Θ1' & De & HrΘ1 & Hagr1 & Hext & Hdom1).
    exists S1, ρe, Θ1', (pskl_var_f α2).
    split; [ apply e_consis__flex_l;
             [ eapply rel_pskl_non_flex; [ exact HrP0 | exact Hagr | exact Hnf ]
             | intros Ehole; subst; inversion HrP0; subst; contradiction
             | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrP | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    split; [ simpl_env in Hext; exact Hext | ]. exact Hdom1.
  - (* C-FlexR : the same, with the SUBJECT assigned *)
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hnhole HA IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 α2 Hatα | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 C2 Hu4 ]; subst.
    assert (Hflα : a_flex_tvar (nil ++ Θ0) α)
      by (exact ((proj1 a_assign_unify_subject_flex) _ _ _ _ _ HA)).
    assert (HcovP1 : ftvar_in_pskl P' [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (HagrN : flex_agree_rel ρ V (nil ++ Θ0) (nil ++ Θ0'))
      by (simpl_env; exact Hagr).
    assert (HfunN : rel_fun ρ V (dom (nil ++ Θ0))) by (simpl_env; exact Hfun).
    assert (HwfN : {{ ⊢ (nil ++ Θ0) }}a) by (simpl_env; exact Hwf).
    assert (HuqN : uniq (nil ++ Θ0')) by (simpl_env; exact Huq2p).
    assert (HftvN : ftvar_in_aenv (nil ++ Θ0') [<=] S0)
      by (simpl_env; exact Hftv2).
    assert (HscpN : V [<=] ftvar_in_aenv (nil ++ Θ0))
      by (simpl_env; exact Hscp).
    assert (HblkN : forall a, a `in` dom Θ1 -> a `notin` dom (nil ++ Θ0) ->
                    a `notin` cols_l ρ) by (simpl_env; exact Hblk).
    assert (HdΘN : dom (nil ++ Θ0') [<=] S0) by (simpl_env; exact HdΘ).
    assert (HwfpN : {{ (nil ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (simpl_env; exact Hwfp).
    destruct (IH S0 Θ0' nil α2 P' ρ V HrΘ (@rel_aenv__nil ρ V) Hatα HrP
                HagrN Hinj HfunN Hflα HwfN a_decls__nil a_decls__nil HuqN
                HftvN HscpN HblkN HdΘN Hcov HcovP1 HwfpN)
      as (S1 & ρe & Θ1' & De & HrΘ1 & Hagr1 & Hext & Hdom1).
    exists S1, ρe, Θ1', (pskl_var_f α2).
    split; [ apply e_consis__flex_r;
             [ eapply rel_pskl_non_flex; [ exact HrP | exact Hagr | exact Hnf ]
             | intros Ehole; subst; inversion HrP; subst; contradiction
             | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrP0 | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    split; [ simpl_env in Hext; exact Hext | ]. exact Hdom1.
  - (* C-GhostR : identity, and the Δ₁-disjointness TRANSPORTS *)
    intros Δ1 Δ2 Θ0 P Hdisj.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 C2 Hu4 ]; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', P'.
    split.
    { apply e_consis__ghost_r.
      eapply rel_atoms_disjoint; [ exact Hrd1 | exact HrP | exact Hdisj ]. }
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ exact HrP | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* C-UnivGhostR : the ⫯ is stripped off the COUNTERPART only *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf HD IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 P0b2 HrP0b ]; subst.
    assert (HcovP1 : ftvar_in_pskl P0b2 ∪ ftvar_in_pskl P' [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hwfp01 : {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a)
      by (inversion Hwfp0; subst; rewrite aenv_minus_empty in *; assumption).
    destruct (IH S0 Θ0' Δ1' Δ2' P0b2 P' ρ V
                HrΘ HrP0b HrP Hrd1 Hrd2 Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov
                HcovP1 HcovΔ Hwfp01 Hwfp HΔtv Hnfd Hfaf HΔsc)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split.
    { apply e_consis__univ_ghost_r;
        [ eapply rel_pskl_guarded; [ exact HrP | exact Hg ]
        | eapply rel_pskl_non_flex; [ exact HrP | exact Hagr | exact Hnf ]
        | exact De ]. }
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
Qed.

(* ===================================================================== *)
(*  §10  ⭐⭐⭐ THE a_sub RUNG — [a_sub] / [a_sub_flex] lift to [e_sub] /    *)
(*  [e_sub_flex], all 16 rows (2026-08-21, §8c.36–§8c.42)                  *)
(*                                                                        *)
(*  Same discipline as §9's consis rung: side 1 carries what               *)
(*  [subtag_sound_concl] wants, side 2 carries ONLY [uniq Θ0'] and the     *)
(*  supply bound.  ⭐ The strongest evidence the two rungs' motives line up *)
(*  is [lift_consis_nil] below — it has EXACTLY [lift_sub_concl]'s          *)
(*  hypothesis list, and its proof discharges every non-Δ premise with one  *)
(*  [try assumption].                                                      *)
(* ===================================================================== *)


(** ⭐ At the CHECK sort and mode the yield IS the check-against — every
    [a_sub_mode_ty] / [mode_tc] rule either returns [P0] outright ([Check],
    [ForallR]) or passes its premise's yield through ([ForallL]); the rest
    are at another sort or another mode.  ⚙ [a_sub__forall_r]'s lift needs
    it because [e_sub__forall_r] PINS the premise's yield, while the motive
    only relates it. *)
Lemma e_sub_tc_yield :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     NM = a_sub_mode_ty -> M = mode_tc -> Q = P0) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 -> True).
Proof.
  apply (e_sub_sub_flex_mutind
           (fun S0 NM M P0 Θ0 P Q S1 Θ1 _ =>
              NM = a_sub_mode_ty -> M = mode_tc -> Q = P0)
           (fun S0 NM M P0 Θ0 Ξ α Q S1 Θ1 _ => True));
    try solve [ intros; exact I ];
    intros; try discriminate; try reflexivity.
  - (* ForallL passes the premise's yield through *)
    match goal with IH : _ -> _ -> _ = _ |- _ => apply IH; assumption end.
Qed.

(* ===================================================================== *)
(*  THE MOTIVES                                                           *)
(*                                                                        *)
(*  Same discipline as the consis rung (§8c.32): side 1 carries the        *)
(*  package [subtag_sound_concl] wants, side 2 carries ONLY [uniq Θ0'] +   *)
(*  [ftvar_in_aenv Θ0' ⊆ S0].  ⭐ Here that is even cheaper than at consis: *)
(*  [e_sub_sub_flex_sound] re-establishes BOTH at the output in one go.    *)
(* ===================================================================== *)

Definition lift_sub_post (Θ0 : aenv) (Q : pskl) (Θ1 : aenv)
    (S0 : atoms) (NM : a_sub_mode) (M : mode) (Θ0' : aenv)
    (P0' P' : pskl) (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' Q',
    {{ S0 ↝ S1 ⊨ Θ0' ⊢[ NM | M | P0' ] P' ⩽ Q' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_sub_concl (NM : a_sub_mode) (M : mode) (P0 : pskl)
    (Θ0 : aenv) (P Q : pskl) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' P0' P' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    rel_pskl ρ V P P' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' ∪ ftvar_in_pskl P' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
    lift_sub_post Θ0 Q Θ1 S0 NM M Θ0' P0' P' ρ V.

Definition lift_sub_flex_post (Θ0 Ξ : aenv) (Θ1 : aenv) (Q : pskl)
    (S0 : atoms) (NM : a_sub_mode) (M : mode) (Θ0' Ξ' : aenv) (α' : atom)
    (P0' : pskl) (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' Q',
    e_sub_flex S0 NM M P0' Θ0' Ξ' α' Q' S1 Θ1'
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv (Ξ ++ Θ0)) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_sub_flex_concl (NM : a_sub_mode) (M : mode) (P0 : pskl)
    (Θ0 Ξ : aenv) (α : atom) (Q : pskl) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' Ξ' α' P0' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_aenv ρ V Ξ Ξ' ->
    rel_atom ρ V α α' ->
    rel_pskl ρ V P0 P0' ->
    flex_agree_rel ρ V (Ξ ++ Θ0) (Ξ' ++ Θ0') ->
    rel_inj ρ V ->
    rel_fun ρ V (dom (Ξ ++ Θ0)) ->
    {{ ⊢ (Ξ ++ Θ0) }}a ->
    a_decls Ξ ->
    a_decls Ξ' ->
    uniq (Ξ' ++ Θ0') ->
    ftvar_in_aenv (Ξ' ++ Θ0') [<=] S0 ->
    V [<=] ftvar_in_aenv (Ξ ++ Θ0) ->
    (forall a, a `in` dom Θ1 -> a `notin` dom (Ξ ++ Θ0) ->
       a `notin` cols_l ρ) ->
    dom (Ξ' ++ Θ0') [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' [<=] S0 ->
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
    a_binds_tvar α (Ξ ++ Θ0) ->
    lift_sub_flex_post Θ0 Ξ Θ1 Q S0 NM M Θ0' Ξ' α' P0' ρ V.

(* ===================================================================== *)
(*  ⭐ THE CONSIS RUNG'S LIFT, AT THE Δ = ∅ CALLS [a_sub] MAKES            *)
(*                                                                        *)
(*  [a_sub__check] (through [a_consis_chk]) and [a_sub__arrow] both run    *)
(*  consistency with both Δ-trackers empty, where EVERY Δ-side premise of  *)
(*  [lift_consis_concl] is vacuous.  What is left is exactly               *)
(*  [lift_sub_concl]'s own hypothesis list, so the two rows can hand their *)
(*  package straight through.                                             *)
(* ===================================================================== *)

Lemma lift_consis_nil : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊢[ P0 ] P ∼ Q ⊣ Θ1 }}a ->
  forall S0 Θ0' P0' P' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    rel_pskl ρ V P P' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' ∪ ftvar_in_pskl P' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
    lift_consis_post Θ0 Q Θ1 S0 Θ0' empty empty P0' P' ρ V.
Proof.
  intros Θ0 P0 P Q Θ1 Hc S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun
    Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
  apply ((proj2 (proj2 a_assign_unify_consis_rel_e)) _ _ _ _ _ _ _ Hc);
    try assumption.
  - (* rel_atoms at ∅ *)
    intros a b Hat. split; intros Hin; clear - Hin; fsetdec.
  - intros a b Hat. split; intros Hin; clear - Hin; fsetdec.
  - (* the Δ coverage *) clear; fsetdec.
  - (* every Δ-name is rigid *) intros γ Hγ. clear - Hγ. fsetdec.
  - (* no_flex_dep *) intros γ t Hb. clear; fsetdec.
  - (* flex_above_free *) intros Θa γ bb Θb Heq Hne. clear; fsetdec.
  - (* Δ ⊆ ftvar_in_aenv Θ0 *) clear; fsetdec.
Qed.

(* ===================================================================== *)
(*  ⭐⭐ THE WALK'S SHARED PEEL                                             *)
(*                                                                        *)
(*  The four skip rows of [a_sub_flex] differ ONLY in the entry they step  *)
(*  over, so the V-SHRINK, the IH and the re-attachment live here once and *)
(*  each row is left with its own [e_sub_flex] constructor.  ⭐ It is the   *)
(*  consis rung's [Assign-Skip] (prop_lift.v §9) with two deltas: the walk *)
(*  also carries a YIELD, and [rel_pskl] is MONOTONE in [V] so widening    *)
(*  the IH's [VS] back is free; and the e-side skip rules carry NO         *)
(*  Barendregt premise (def_sub.v:152-175), the supply having accounted    *)
(*  for it.                                                                *)
(* ===================================================================== *)

Lemma lift_sub_flex_peel :
  forall NM M P0 Θ0 Θ1 Ξ α Q (β : atom) (bd : abind),
  lift_sub_flex_concl NM M P0 Θ0 Ξ α Q Θ1 ->
  α <> β ->
  β `notin` ftvar_in_pskl P0 ->
  β `notin` dom Θ1 ->
  forall S0 Θ0' Ξ' α' P0' ρ V,
    rel_aenv ρ V ((β ~ bd) ++ Θ0) Θ0' ->
    rel_aenv ρ V Ξ Ξ' ->
    rel_atom ρ V α α' ->
    rel_pskl ρ V P0 P0' ->
    flex_agree_rel ρ V (Ξ ++ (β ~ bd) ++ Θ0) (Ξ' ++ Θ0') ->
    rel_inj ρ V ->
    rel_fun ρ V (dom (Ξ ++ (β ~ bd) ++ Θ0)) ->
    {{ ⊢ (Ξ ++ (β ~ bd) ++ Θ0) }}a ->
    a_decls Ξ ->
    a_decls Ξ' ->
    uniq (Ξ' ++ Θ0') ->
    ftvar_in_aenv (Ξ' ++ Θ0') [<=] S0 ->
    V [<=] ftvar_in_aenv (Ξ ++ (β ~ bd) ++ Θ0) ->
    (forall a, a `in` dom ((β ~ bd) ++ Θ1) ->
       a `notin` dom (Ξ ++ (β ~ bd) ++ Θ0) -> a `notin` cols_l ρ) ->
    dom (Ξ' ++ Θ0') [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' [<=] S0 ->
    {{ (Ξ ++ (β ~ bd) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
    a_binds_tvar α (Ξ ++ (β ~ bd) ++ Θ0) ->
  exists (b : atom) bd2 Θ0'' S1 ρe Θ1' Q',
    Θ0' = (b ~ bd2) ++ Θ0''
    /\ rel_abind ρ V bd bd2
    /\ α' <> b
    /\ b `notin` ftvar_in_pskl P0'
    /\ e_sub_flex S0 NM M P0' Θ0'' Ξ' α' Q' S1 Θ1'
    /\ rel_aenv (ρe ++ ρ) V ((β ~ bd) ++ Θ1) ((b ~ bd2) ++ Θ1')
    /\ flex_agree_rel (ρe ++ ρ) V ((β ~ bd) ++ Θ1) ((b ~ bd2) ++ Θ1')
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv (Ξ ++ (β ~ bd) ++ Θ0)) S0
    /\ (forall a b0, In (a, b0) ρe ->
          a `in` dom ((β ~ bd) ++ Θ1) /\ b0 `in` dom ((b ~ bd2) ++ Θ1')).
Proof.
  intros NM M P0 Θ0 Θ1 Ξ α Q β bd IH Hne Hβp Hβd.
  intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
    Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hbα.
  destruct (rel_aenv_cons_inv_l HrΘ)
    as (b & bd2 & Θ0'' & E0' & Hab & Hbd & Hrest).
  subst Θ0'.
  assert (Huq1 : uniq (Ξ ++ (β ~ bd) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Huq2 : uniq (Ξ' ++ (b ~ bd2) ++ Θ0'')) by (exact Huq2p).
  assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
  assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
  assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
  { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
    clear - Hftv2. fsetdec. }
  assert (Hβnd : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
    destruct_uniq. fsetdec. }
  assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
  { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
    destruct_uniq. fsetdec. }
  assert (Hsc : ftvar_in_aenv (Ξ ++ (β ~ bd) ++ Θ0)
                [<=] dom (Ξ ++ (β ~ bd) ++ Θ0))
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HVdom : V [<=] dom (Ξ ++ (β ~ bd) ++ Θ0))
    by (clear - Hscp Hsc; fsetdec).
  assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
    by (apply a_wf_aenv_ftv_dom; exact HwfC).
  assert (Hβd0 : β `in` dom (Ξ ++ (β ~ bd) ++ Θ0))
    by (repeat rewrite dom_app; simpl; clear; fsetdec).
  assert (Hβfun : forall y, rel_atom ρ V β y -> y = b)
    by (intros y Hy; exact (Hfun β y b Hβd0 Hy Hab)).
  assert (Hne2 : α' <> b).
  { intros Ex. apply Hne. rewrite Ex in Hrα. exact (Hinj α β b Hrα Hab). }
  assert (Hbdftv : ftvar_in_abind bd [<=] dom Θ0)
    by (eapply a_wf_aenv_cons_payload_ftv;
        eapply a_wf_aenv_strip_prefix; exact Hwf).
  assert (Hds0 : dom Θ0 [<=] ftvar_in_aenv Θ0)
    by (apply dom_subset_ftvar_in_aenv).
  assert (HbP : b `notin` ftvar_in_pskl P0')
    by (eapply rel_pskl_notin_r_inj;
        [ exact HrP0 | exact Hinj | exact Hab | exact Hβp ]).
  remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VS eqn:EVS.
  assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
  assert (HVSsplit : forall x, x `in` V -> x <> β -> x `in` VS).
  { intros x Hx Hne0. subst VS.
    pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
    assert (Hxd : x `in` dom (Ξ ++ (β ~ bd) ++ Θ0))
      by (clear - Hx HVdom; fsetdec).
    repeat rewrite dom_app in Hxd. simpl in Hxd.
    repeat rewrite dom_app in Hds.
    clear - Hx Hne0 Hxd Hds. fsetdec. }
  assert (HVSne : forall x, x `in` VS -> x <> β).
  { intros x Hx Ex. rewrite Ex in Hx.
    assert (Hin : β `in` ftvar_in_aenv (Ξ ++ Θ0))
      by (subst VS; clear - Hx; fsetdec).
    clear - Hin HscC Hβnd. fsetdec. }
  assert (HrΘS : rel_aenv ρ VS Θ0 Θ0'').
  { eapply rel_aenv_shrink_V; [ exact Hrest | ].
    intros x Hx Hf. subst VS.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
    rewrite ftvar_in_aenv_app. clear - Hx Hf Hds. fsetdec. }
  assert (HrΞS : rel_aenv ρ VS Ξ Ξ').
  { eapply rel_aenv_shrink_V; [ exact HrΞ | ].
    intros x Hx Hf. subst VS.
    pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
    rewrite ftvar_in_aenv_app. clear - Hx Hf Hds. fsetdec. }
  assert (HrαS : rel_atom ρ VS α α').
  { inversion Hrα; subst.
    - apply rel_atom__pair; assumption.
    - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hne ]. }
  assert (HrP0S : rel_pskl ρ VS P0 P0').
  { eapply rel_pskl_shrink_V; [ exact HrP0 | ].
    intros x Hx Hf. apply HVSsplit; [ exact Hx | ].
    intros Ex. rewrite Ex in Hf. contradiction. }
  assert (HagrS : flex_agree_rel ρ VS (Ξ ++ Θ0) (Ξ' ++ Θ0''))
    by (eapply flex_agree_peel;
        [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
        | exact Hbnd | exact HVS | exact HVSne ]).
  assert (HinjS : rel_inj ρ VS)
    by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVS ]).
  assert (HfunS : rel_fun ρ VS (dom (Ξ ++ Θ0))).
  { eapply rel_fun_weaken;
      [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVS ]
      | intros x y Hx; exact Hx
      | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
  assert (HbαS : a_binds_tvar α (Ξ ++ Θ0)).
  { eapply a_binds_tvar_strip_mid; [ exact Hbα | | | ];
      solve [ intros E; inversion E; subst; apply Hne; reflexivity
            | intros τ0 E; inversion E; subst; apply Hne; reflexivity ]. }
  assert (HscpS : VS [<=] ftvar_in_aenv (Ξ ++ Θ0))
    by (subst VS; clear; fsetdec).
  assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                  a0 `notin` cols_l ρ).
  { intros a0 Ha0 Hn0. apply Hblk.
    - simpl. clear - Ha0. fsetdec.
    - assert (Hne0 : a0 <> β)
        by (intros Ex; rewrite Ex in Ha0; contradiction).
      repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne0. fsetdec. }
  assert (HdΘS : dom (Ξ' ++ Θ0'') [<=] S0)
    by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
        clear - HdΘ; fsetdec).
  assert (HcovS : VS ∪ cols_r ρ [<=] S0) by (clear - Hcov HVS; fsetdec).
  assert (HwfpS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_strip_mid; [ exact Hwfp0 | exact Hβp ]).

  destruct (IH S0 Θ0'' Ξ' α' P0' ρ VS HrΘS HrΞS HrαS HrP0S HagrS HinjS HfunS
              HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS HdΘS HcovS HcovP
              HwfpS HbαS)
    as (S1 & ρe & Θ1' & Q' & D2 & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
  exists b, bd2, Θ0'', S1, ρe, Θ1', Q'.
  split; [ reflexivity | ].
  split; [ exact Hbd | ].
  split; [ exact Hne2 | ].
  split; [ exact HbP | ].
  split; [ exact D2 | ].
  split.
  { apply rel_aenv__cons.
    - eapply rel_atom_incl; [ exact Hab | ].
      intros x y Hx. apply in_or_app. right. exact Hx.
    - eapply rel_abind_mono; [ exact Hbd | intros x y Hx; apply in_or_app;
        right; exact Hx | intros x Hx; exact Hx ].
    - eapply rel_aenv_mono;
        [ exact HrΘ1 | intros x y Hx; exact Hx | exact HVS ]. }
  assert (Hbnd1 : b `notin` dom Θ1').
  { pose proof ((proj2 e_sub_sub_flex_dom_upper) _ _ _ _ _ _ _ _ _ _ D2)
      as Hup.
    assert (HbS0 : b `in` S0)
      by (repeat rewrite dom_app in HdΘ; simpl in HdΘ; clear - HdΘ; fsetdec).
    rewrite dom_app in Hup. clear - Hup Hbnd HbS0.
    repeat rewrite dom_app in Hbnd. fsetdec. }
  assert (Hinj' : rel_inj (ρe ++ ρ) V)
    by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
  assert (Hab' : rel_atom (ρe ++ ρ) V β b)
    by (eapply rel_atom_incl;
        [ exact Hab | intros x y Hx; apply in_or_app; right; exact Hx ]).
  assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V β y -> y = b).
  { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
    - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
    - exact (Hβfun y Hat0). }
  split.
  { eapply flex_agree_reattach;
      [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
      | exact HVSsplit
      | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
      | (* ⭐ the head agrees because [rel_abind] forces the two entries to
           have the same KIND: flexible on both sides, or rigid on both *)
        inversion Hbd; subst;
        [ (* tvar *) split; intros Hf; exfalso;
            [ apply Hβd | apply Hbnd1 ]; apply a_flex_tvar_in_dom;
            (eapply a_flex_tvar_head_tail;
               [ exact Hf | discriminate | intros ?; discriminate ])
        | (* flex *) split; intros _; left; unfold binds; simpl; left; reflexivity
        | (* flex_def *) split; intros _; right; eexists; unfold binds; simpl;
            left; reflexivity
        | (* var_typ *) split; intros Hf; exfalso;
            [ apply Hβd | apply Hbnd1 ]; apply a_flex_tvar_in_dom;
            (eapply a_flex_tvar_head_tail;
               [ exact Hf | discriminate | intros ?; discriminate ])
        | (* var_skl *) split; intros Hf; exfalso;
            [ apply Hβd | apply Hbnd1 ]; apply a_flex_tvar_in_dom;
            (eapply a_flex_tvar_head_tail;
               [ exact Hf | discriminate | intros ?; discriminate ]) ] ]. }
  assert (Hftsub : ftvar_in_aenv (Ξ ++ (β ~ bd) ++ Θ0)
                   [<=] add β (ftvar_in_abind bd ∪ ftvar_in_aenv (Ξ ++ Θ0))).
  { repeat rewrite ftvar_in_aenv_app. simpl. clear; fsetdec. }
  split.
  { eapply rel_pskl_mono;
      [ exact HrQ | intros x y Hx; exact Hx | exact HVS ]. }
  split.
  { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
    split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
    intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
    split; [ | exact Hb0 ].
    destruct (Hdom1 _ _ Hin) as [Hd1 _].
    assert (Hne0 : a0 <> β)
      by (intros Ex; rewrite Ex in Hd1; contradiction).
    repeat rewrite ftvar_in_aenv_app in Ha0 |- *. simpl.
    clear - Ha0 Hne0 Hbdftv Hds0. fsetdec. }
  intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
  split; [ clear - Hd1; simpl_env; fsetdec | clear - Hd2; simpl_env; fsetdec ].
Qed.

Theorem a_sub_sub_flex_rel_e :
  (forall NM M P0 Θ0 P Q Θ1, a_sub NM M P0 Θ0 P Q Θ1 ->
     lift_sub_concl NM M P0 Θ0 P Q Θ1) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1, a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     lift_sub_flex_concl NM M P0 Θ0 Ξ α Q Θ1).
Proof.
  apply (a_sub_sub_flex_tm_mutind
           (fun NM M P0 Θ0 P Q Θ1 _ => lift_sub_concl NM M P0 Θ0 P Q Θ1)
           (fun NM M P0 Θ0 Ξ α Q Θ1 _ =>
              lift_sub_flex_concl NM M P0 Θ0 Ξ α Q Θ1)).
  - (* S-Infer : output = subject, context unchanged *)
    intros NM P Θ0.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 C2 Hu4 ]; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', P'.
    split; [ apply e_sub__infer | ]. simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ exact HrP | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* S-Check : the consistency call, at Δ = ∅ *)
    intros Θ0 Θ1 A B Hgfa Hgfb Hga Hgb Hc.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    destruct Hc as [Qc Hc].
    destruct (lift_consis_nil Hc HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
                Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp)
      as (S1 & ρe & Θ1' & Qc' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', P0'.
    split.
    { apply e_sub__check;
        [ eapply rel_pskl_ghost_free; [ exact HrP | exact Hgfa ]
        | eapply rel_pskl_ghost_free; [ exact HrP0 | exact Hgfb ]
        | eapply rel_pskl_guarded; [ exact HrP | exact Hga ]
        | eapply rel_pskl_guarded; [ exact HrP0 | exact Hgb ]
        | exists Qc'; exact De ]. }
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrP0 | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    split; [ exact Hext | ]. exact Hdom1.
  - (* ⭐⭐ S-ForallR — PROBE: everything but [Hblk'] *)
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huq Hfr Hprem IH.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2
                      | B1 B2 HrB | | C1 C2 Hu3 ]; subst.
    destruct (atom_fresh S0) as [α2 Hα2].
    rewrite dom_app in Hfr.
    assert (Hαd : α `notin` dom Θ0) by (clear - Hfr; fsetdec).
    assert (HαΞ : α `notin` dom Ξ) by (clear - Hfr; fsetdec).
    assert (HαΘ1 : α `notin` dom Θ1) by (clear - Hfr; fsetdec).
    assert (HfrA : α `notin` ftvar_in_pskl A) by (clear - Hfr; fsetdec).
    assert (HfrB : α `notin` ftvar_in_pskl B) by (clear - Hfr; fsetdec).
    assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HfrΘ : α `notin` ftvar_in_aenv Θ0) by (clear - Hαd Hsc0; fsetdec).
    assert (HαV : α `notin` V) by (intros Hin; apply HfrΘ; apply Hscp; exact Hin).
    assert (Hα2d : α2 `notin` dom Θ0') by (clear - Hα2 HdΘ; fsetdec).
    assert (Hα2V : α2 `notin` V) by (clear - Hα2 Hcov; fsetdec).
    assert (Hα2c : α2 `notin` cols_r ρ) by (clear - Hα2 Hcov; fsetdec).
    assert (Hα2f : α2 `notin` ftvar_in_aenv Θ0') by (clear - Hα2 Hftv2; fsetdec).
    (* ⭐ FIRST restrict at the JUNK SUFFIX's domain: the rule freshens Ξ
       only against the CONTEXT, so its names can collide with ρ's left
       column — and then [Hblk'] below is underivable. *)
    assert (HΞΘ0 : dom Ξ ∩ ftvar_in_aenv Θ0 [=] empty).
    { assert (Hdisj : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
      unfold disjoint in Hdisj. clear - Hdisj Hsc0. fsetdec. }
    assert (HΞB : dom Ξ ∩ ftvar_in_pskl (pskl_all_syn B) [=] empty).
    { assert (Hsub : ftvar_in_pskl (pskl_all_syn B) [<=] dom Θ0).
      { intros x Hx. apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds Hwfp0 Hx). }
      assert (Hdisj : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
      unfold disjoint in Hdisj. clear - Hdisj Hsub. fsetdec. }
    assert (HΞA : dom Ξ ∩ ftvar_in_pskl A [=] empty).
    { assert (Hsub : ftvar_in_pskl A [<=] dom Θ0).
      { intros x Hx. apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds Hwfp Hx). }
      assert (Hdisj : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
      unfold disjoint in Hdisj. clear - Hdisj Hsub. fsetdec. }
    remember (restrict_l (dom Ξ) ρ) as ρ0 eqn:Eρ0.
    assert (Hρ0incl : forall a b, In (a, b) ρ0 -> In (a, b) ρ)
      by (subst ρ0; intros a b Hin; eapply restrict_l_incl; exact Hin).
    assert (Hρ0in : forall a b, In (a, b) ρ -> a `notin` dom Ξ ->
              In (a, b) ρ0)
      by (subst ρ0; intros a b Hin Hn; apply restrict_l_in; assumption).
    assert (Hcl00 : cols_l ρ0 [<=] cols_l ρ)
      by (subst ρ0; apply cols_l_restrict_l).
    assert (Hcr00 : cols_r ρ0 [<=] cols_r ρ)
      by (subst ρ0; apply cols_r_restrict_l).
    assert (HΞcols : forall a, a `in` dom Ξ -> a `notin` cols_l ρ0)
      by (subst ρ0; intros a Ha; apply restrict_l_notin; exact Ha).
    assert (HrΘ0 : rel_aenv ρ0 V Θ0 Θ0')
      by (subst ρ0; apply rel_aenv_restrict_l; [ exact HrΘ | exact HΞΘ0 ]).
    assert (HrB0 : rel_pskl ρ0 V B B2).
    { subst ρ0. apply rel_pskl_restrict_l; [ exact HrB | ].
      simpl in HΞB. clear - HΞB. fsetdec. }
    assert (HrA0 : rel_pskl ρ0 V A P')
      by (subst ρ0; apply rel_pskl_restrict_l; [ exact HrP | exact HΞA ]).
    assert (Hagr0 : flex_agree_rel ρ0 V Θ0 Θ0')
      by (eapply flex_agree_rel_weaken;
          [ exact Hagr | exact Hρ0incl | intros x Hx; exact Hx ]).
    assert (Hinj0 : rel_inj ρ0 V)
      by (eapply rel_inj_sub; [ exact Hinj | exact Hρ0incl ]).
    assert (Hfun0 : rel_fun ρ0 V (dom Θ0))
      by (eapply rel_fun_weaken;
          [ exact Hfun | exact Hρ0incl | intros x Hx; exact Hx ]).
    assert (Hcov0 : V ∪ cols_r ρ0 [<=] S0) by (clear - Hcov Hcr00; fsetdec).
    (* ⚠️ ρ0 must survive the row's later bare [subst]s, so drop its defining
       equation now — every fact about it is already an assert above. *)
    clear Eρ0.
    assert (Hcl0 : cols_l (restrict_pairs α α2 ρ0) [<=] cols_l ρ0)
      by apply cols_l_restrict_pairs.
    assert (Hcr0 : cols_r (restrict_pairs α α2 ρ0) [<=] cols_r ρ0)
      by apply cols_r_restrict_pairs.
    assert (Hαl : α `notin` cols_l (restrict_pairs α α2 ρ0))
      by apply restrict_pairs_notin_l.
    assert (Hα2r : α2 `notin` cols_r (restrict_pairs α α2 ρ0))
      by apply restrict_pairs_notin_r.
    assert (HrΘr : rel_aenv (restrict_pairs α α2 ρ0) V Θ0 Θ0')
      by (apply rel_aenv_restrict; [ exact HrΘ0 | exact HfrΘ | exact Hα2f ]).
    assert (HrΘ' : rel_aenv ((α, α2) :: restrict_pairs α α2 ρ0) V
                     ((α ~ abind_tvar) ++ Θ0) ((α2 ~ abind_tvar) ++ Θ0')).
    { apply rel_aenv__cons;
        [ apply rel_atom__pair; left; reflexivity | constructor | ].
      eapply rel_aenv_mono;
        [ exact HrΘr | intros x y Hx; right; exact Hx | intros x Hx; exact Hx ]. }
    assert (HrBr : rel_pskl (restrict_pairs α α2 ρ0) V B B2)
      by (apply rel_pskl_restrict;
          [ exact HrB0 | clear - HfrB; fsetdec
          | clear - Hα2 HcovP; simpl in HcovP; fsetdec ]).
    assert (HrAr : rel_pskl (restrict_pairs α α2 ρ0) V A P')
      by (apply rel_pskl_restrict;
          [ exact HrA0 | clear - HfrA; fsetdec
          | clear - Hα2 HcovP; simpl in HcovP; fsetdec ]).
    assert (HrB' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ0) V
                     (open_pskl_wrt_pskl B (pskl_var_f α))
                     (open_pskl_wrt_pskl B2 (pskl_var_f α2)))
      by (apply rel_pskl_open_pair; exact HrBr).
    assert (HrA' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ0) V A P')
      by (eapply rel_pskl_mono;
          [ exact HrAr | intros x y Hx; right; exact Hx
          | intros x Hx; exact Hx ]).
    assert (Hagr' : flex_agree_rel ((α, α2) :: restrict_pairs α α2 ρ0) V
                      ((α ~ abind_tvar) ++ Θ0) ((α2 ~ abind_tvar) ++ Θ0')).
    { apply flex_agree_rel_push_look; [ | exact Hαd | exact Hα2d ].
      eapply flex_agree_rel_weaken;
        [ exact Hagr0 | intros x y Hx; eapply restrict_pairs_incl; exact Hx
        | intros x Hx; exact Hx ]. }
    assert (Hinj' : rel_inj ((α, α2) :: restrict_pairs α α2 ρ0) V)
      by (apply rel_inj_push;
          [ eapply rel_inj_sub;
              [ exact Hinj0 | intros x y Hx; eapply restrict_pairs_incl; exact Hx ]
          | exact Hα2V | exact Hα2r ]).
    assert (Hfun' : rel_fun ((α, α2) :: restrict_pairs α α2 ρ0) V
                      (dom ((α ~ abind_tvar) ++ Θ0))).
    { simpl. apply rel_fun_push;
        [ eapply rel_fun_weaken;
            [ exact Hfun0 | intros x y Hx; eapply restrict_pairs_incl; exact Hx
            | intros x Hx; exact Hx ]
        | exact HαV | exact Hαl ]. }
    assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; [ exact Hαd | exact Hwf ]).
    assert (Huq2' : uniq ((α2 ~ abind_tvar) ++ Θ0'))
      by (clear - Huq2p Hα2d; solve_uniq).
    assert (Hftv2' : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0') [<=] add α2 S0)
      by (simpl; clear - Hftv2; fsetdec).
    assert (Hscp' : V [<=] ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0))
      by (simpl; clear - Hscp; fsetdec).
    assert (HdΘ' : dom ((α2 ~ abind_tvar) ++ Θ0') [<=] add α2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hcov' : V ∪ cols_r ((α, α2) :: restrict_pairs α α2 ρ0)
                    [<=] add α2 S0)
      by (simpl; clear - Hcov0 Hcr0; fsetdec).
    assert (HcovP' : ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f α2))
                     ∪ ftvar_in_pskl P' [<=] add α2 S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B2 (pskl_var_f α2))
        as Hu1. simpl in Hu1, HcovP. clear - Hu1 HcovP. fsetdec. }
    assert (Hwfp0' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (open_pskl_wrt_pskl B (pskl_var_f α)) }}a)
      by (apply a_wf_pskl_all_syn_open_tvar;
          [ exact Hwfp0 | clear - Hαd HfrB; fsetdec ]).
    assert (Hwfp' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ A }}a)
      by (eapply a_wf_pskl_weaken_tvarish;
          [ intros γ Hγ; apply (a_binds_tvar_weaken_mid nil (α ~ abind_tvar));
            exact Hγ
          | exact Hwfp ]).
    assert (Hblk' : forall a, a `in` dom (Ξ ++ (α ~ abind_tvar) ++ Θ1) ->
              a `notin` dom ((α ~ abind_tvar) ++ Θ0) ->
              a `notin` cols_l ((α, α2) :: restrict_pairs α α2 ρ0)).
    { intros a Ha Hn. simpl in Ha, Hn |- *.
      assert (Hne : a <> α) by (clear - Hn; fsetdec).
      repeat rewrite dom_app in Ha. simpl dom in Ha.
      assert (Hc : a `notin` cols_l ρ0).
      { destruct (AtomSetProperties.In_dec a (dom Ξ)) as [HaΞ | HaΞ].
        - exact (HΞcols a HaΞ).
        - assert (HaΘ1 : a `in` dom Θ1) by (clear - Ha HaΞ Hne; fsetdec).
          assert (Hc0 : a `notin` cols_l ρ)
            by (apply Hblk; [ exact HaΘ1 | clear - Hn; fsetdec ]).
          clear - Hc0 Hcl00. fsetdec. }
      clear - Hne Hc Hcl0. fsetdec. }
    destruct (IH (add α2 S0) ((α2 ~ abind_tvar) ++ Θ0')
                (open_pskl_wrt_pskl B2 (pskl_var_f α2)) P'
                ((α, α2) :: restrict_pairs α α2 ρ0) V
                HrΘ' HrB' HrA' Hagr' Hinj' Hfun' Hwf' Huq2' Hftv2' Hscp'
                Hblk' HdΘ' Hcov' HcovP' Hwfp0' Hwfp')
      as (S1 & ρe & Θ1out & Q' & De & HrΘout & Hagrout & HrQ & Hext & Hdomout).
    (* ---- side 1's output, via a_sub's own soundness ---- *)
    destruct ((proj1 a_sub_output_wf_bundle) _ _ _ _ _ _ _ Hprem Hwf' Hwfp0'
                Hwfp') as [Hle1 [HwfOut HwfQ]].
    assert (HuqOut : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ1))
      by (apply a_wf_aenv_uniq; exact HwfOut).
    assert (HΞΘ1 : dom Ξ ∩ dom Θ1 [=] empty).
    { assert (Hd : disjoint Ξ ((α ~ abind_tvar) ++ Θ1))
        by (clear - HuqOut; solve_uniq).
      unfold disjoint in Hd. simpl in Hd. clear - Hd. fsetdec. }
    assert (HwfΘ1 : {{ ⊢ Θ1 }}a).
    { eapply a_wf_aenv_strip_prefix.
      eapply a_wf_aenv_strip_prefix with (Ξ := Ξ). simpl_env. exact HwfOut. }
    assert (Hftv1 : ftvar_in_aenv Θ1 [<=] dom Θ1)
      by (apply a_wf_aenv_ftv_dom; exact HwfΘ1).
    assert (HΞf1 : dom Ξ ∩ ftvar_in_aenv Θ1 [=] empty)
      by (clear - HΞΘ1 Hftv1; fsetdec).
    (* ---- the pair list the premise ran at, and its injectivity ---- *)
    assert (Hinjout : rel_inj (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0) V)
      by (eapply rel_inj_app; [ exact Hinj' | exact Hext | exact Hcov' ]).
    assert (Hαρe : forall b, ~ In (α, b) ρe).
    { intros b Hin. destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin) as [Hna _].
      apply Hna. simpl. clear; fsetdec. }
    assert (Hα2ρe : forall a, ~ In (a, α2) ρe).
    { intros a Hin. destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin) as [_ Hnb].
      apply Hnb. clear; fsetdec. }
    assert (Hαonly : forall y,
              rel_atom (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0) V α y ->
              y = α2).
    { intros y Hat. inversion Hat as [ a0 b0 Hin | a0 HinV ]; subst.
      - apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
        + exfalso. exact (Hαρe _ Hin).
        + inversion Ehd; reflexivity.
        + exfalso. apply (@restrict_pairs_notin_l α α2 ρ0).
          eapply cols_l_in; exact Hin.
      - exfalso. exact (HαV HinV). }
    (* ---- SPLIT the premise's output at the junk suffix, then the opener ---- *)
    destruct (@rel_aenv_app_inv_l Ξ
                (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0) V
                ((α ~ abind_tvar) ++ Θ1) Θ1out HrΘout)
      as (Ξ2 & Θrest & Eout & HrΞ2 & HrTail).
    subst Θ1out.
    destruct (rel_aenv_cons_inv_l HrTail)
      as (b & bd2 & Θ1' & E2 & Hab2 & Hbd2 & HrΘ1').
    subst Θrest. inversion Hbd2; subst.
    assert (Eb : b = α2)
      by (apply Hαonly; exact Hab2).
    subst b.
    (* ---- side 2's junk is apart from side 2's input ---- *)
    assert (HΞ2Θ0 : forall a, a `in` dom Ξ2 -> a `notin` dom Θ0').
    { intros a Ha.
      destruct (rel_aenv_dom_r_inv HrΞ2 Ha) as (a' & Ha' & Hat').
      inversion Hat' as [ x0 y0 Hin | x0 HinV ]; subst.
      - apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
        + destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin) as [_ Hnb].
          clear - Hnb HdΘ. fsetdec.
        + exfalso. injection Ehd as E1 E2x. subst a'.
          clear - Ha' Hfr. fsetdec.
        + exfalso. apply (HΞcols a' Ha'). eapply cols_l_in.
          eapply restrict_pairs_incl; exact Hin.
      - exfalso.
        assert (Had : a `in` dom Θ0) by (apply Hscp in HinV; clear - HinV Hsc0; fsetdec).
        assert (Hd : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
        unfold disjoint in Hd. clear - Hd Ha' Had. fsetdec. }
    assert (HcovS : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0')
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f α2))
                    ∪ ftvar_in_pskl P' [<=] add α2 S0).
    { repeat apply AtomSetProperties.union_subset_3;
        [ exact Hftv2' | clear - HcovP'; fsetdec | clear - HcovP'; fsetdec ]. }
    destruct (e_sub_sub_flex_sound) as [HsndS _].
    destruct (HsndS _ _ _ _ _ _ _ _ _ De Huq2' HcovS)
      as [HaD [HuqOut2 [Hftv1out HftvQ]]].
    assert (Huq2Ξ : uniq (Ξ2 ++ Θ0')).
    { apply uniq_app_4.
      - clear - HuqOut2. solve_uniq.
      - exact Huq2p.
      - apply disjoint_from_pointwise. exact HΞ2Θ0. }
    (* ⭐ the e-rule PINS the premise's yield; the motive only relates it *)
    assert (EQ' : Q' = open_pskl_wrt_pskl B2 (pskl_var_f α2))
      by (exact ((proj1 e_sub_tc_yield) _ _ _ _ _ _ _ _ _ De eq_refl eq_refl)).
    subst Q'.
    (* ---- the e-side conclusion ---- *)
    assert (Dc : {{ S0 ↝ S1 ⊨ Θ0' ⊢[ a_sub_mode_ty | mode_tc |
                    (pskl_all_syn B2) ] P' ⩽ (pskl_all_syn B2) ⊣ Θ1' }}e).
    { apply e_sub__forall_r with (α := α2) (Ξ := Ξ2);
        [ eapply rel_pskl_ghost_free; [ exact HrP0 | exact Hgf ]
        | eapply rel_aenv_suffix; [ exact HrΞ2 | exact Hsuf ]
        | exact Huq2Ξ | exact Hα2 | exact De ]. }
    (* ---- hand back at the CALLER's pair list ---- *)
    remember (restrict_l (dom Ξ) ρe) as ρeo eqn:Eρeo.
    assert (Hρeoincl : forall a b0, In (a, b0) ρeo -> In (a, b0) ρe)
      by (subst ρeo; intros a b0 Hin; eapply restrict_l_incl; exact Hin).
    assert (HρeoΞ : forall a b0, In (a, b0) ρeo -> a `notin` dom Ξ).
    { subst ρeo. intros a b0 Hin Ha.
      apply (restrict_l_notin ρe Ha). eapply cols_l_in; exact Hin. }
    assert (Hdomeo : forall a b0, In (a, b0) ρeo ->
              a `in` dom Θ1 /\ b0 `in` dom Θ1').
    { intros a b0 Hin.
      pose proof (Hρeoincl _ _ Hin) as Hin'.
      pose proof (HρeoΞ _ _ Hin) as HaΞ.
      destruct (Hdomout _ _ Hin') as [Hd1 Hd2].
      destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin') as [Hna Hnb].
      assert (Hane : a <> α) by (intros ->; apply Hna; simpl; clear; fsetdec).
      assert (Hbne : b0 <> α2) by (intros ->; apply Hnb; clear; fsetdec).
      assert (HbΞ2 : b0 `notin` dom Ξ2).
      { intros Hb2. destruct (rel_aenv_dom_r_inv HrΞ2 Hb2) as (a'' & Ha'' & Hat'').
        assert (Ea : a'' = a).
        { apply (Hinjout a'' a b0 Hat'').
          apply rel_atom__pair. apply in_or_app; left; exact Hin'. }
        subst a''. contradiction. }
      simpl_env in Hd1. simpl_env in Hd2.
      split; [ clear - Hd1 HaΞ Hane; fsetdec
             | clear - Hd2 HbΞ2 Hbne; fsetdec ]. }
    exists S1, ρeo, Θ1', (pskl_all_syn B2).
    split; [ exact Dc | ].
    (* the CONTEXT relation: drop the JUNK pairs and the OPENER pair, then
       widen back to the caller's list *)
    assert (HαfΘ1 : α `notin` ftvar_in_aenv Θ1).
    { assert (Hd : α `notin` dom Θ1) by (clear - Hfr; fsetdec).
      clear - Hd Hftv1. fsetdec. }
    assert (Hα2fΘ1 : α2 `notin` ftvar_in_aenv Θ1').
    { intros Hin. destruct (rel_aenv_ftv_corr_r HrΘ1' Hin) as (a & Ha & Hat).
      assert (Ea : a = α).
      { apply (Hinjout a α α2 Hat). apply rel_atom__pair.
        apply in_or_app; right; left; reflexivity. }
      subst a. exact (HαfΘ1 Ha). }
    assert (Hincl : forall a b0,
              In (a, b0) (restrict_pairs α α2
                            (restrict_l (dom Ξ)
                               (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0))) ->
              In (a, b0) (ρeo ++ ρ)).
    { intros a b0 Hin.
      assert (Hane : a <> α).
      { intros ->.
        apply (@restrict_pairs_notin_l α α2
                 (restrict_l (dom Ξ)
                    (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0))).
        eapply cols_l_in; exact Hin. }
      apply restrict_pairs_incl in Hin.
      assert (HaΞ : a `notin` dom Ξ).
      { intros Ha.
        apply (restrict_l_notin
                 (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0) Ha).
        eapply cols_l_in; exact Hin. }
      apply restrict_l_incl in Hin.
      apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
      - apply in_or_app; left. subst ρeo. apply restrict_l_in; assumption.
      - exfalso. injection Ehd as E1 E2x. apply Hane. symmetry. exact E1.
      - apply in_or_app; right. apply Hρ0incl.
        eapply restrict_pairs_incl; exact Hin. }
    assert (HrΘfin : rel_aenv (ρeo ++ ρ) V Θ1 Θ1').
    { eapply rel_aenv_mono;
        [ exact (rel_aenv_restrict
                   (rel_aenv_restrict_l HrΘ1' HΞf1) HαfΘ1 Hα2fΘ1)
        | exact Hincl | intros x Hx; exact Hx ]. }
    split; [ exact HrΘfin | ].
    (* ---- THE FLEX AGREEMENT: peel the opener, peel the two suffixes, and
       answer the pairs BOTH restrictions deleted ---- *)
    assert (HcovC : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl (pskl_all_syn B2)
                    ∪ ftvar_in_pskl P' [<=] S0).
    { repeat apply AtomSetProperties.union_subset_3;
        [ exact Hftv2 | clear - HcovP; simpl in HcovP |- *; fsetdec
        | clear - HcovP; simpl in HcovP |- *; fsetdec ]. }
    pose proof (e_sub_sound Dc Huq2p HcovC) as HaDc.
    assert (Hdel : forall a b0, In (a, b0) ρ -> a `notin` dom Θ0 ->
              a `notin` dom Θ1 -> (a_flex_tvar Θ1 a <-> a_flex_tvar Θ1' b0)).
    { intros a b0 Hin Hn0 Hn1. split; intros Hf; exfalso.
      - apply Hn1. apply a_flex_tvar_in_dom. exact Hf.
      - assert (Hbd : b0 `in` dom Θ1') by (apply a_flex_tvar_in_dom; exact Hf).
        assert (HbS0 : b0 `in` S0).
        { assert (Hc : b0 `in` cols_r ρ) by (eapply cols_r_in; exact Hin).
          clear - Hc Hcov. fsetdec. }
        assert (Hb0 : b0 `in` dom Θ0').
        { pose proof ((proj1 e_sub_sub_flex_dom_upper)
                        _ _ _ _ _ _ _ _ _ Dc) as Hup.
          clear - Hbd HbS0 Hup. fsetdec. }
        assert (Hf0 : a_flex_tvar Θ0' b0)
          by (exact ((proj1 a_sub_sub_flex_flex_rev)
                       _ _ _ _ _ _ _ HaDc b0 Hb0 Hf)).
        apply Hn0. apply a_flex_tvar_in_dom.
        exact (proj2 (proj2 Hagr a b0 Hin) Hf0). }
    assert (HVdom0' : forall x, x `in` V -> x `in` dom Θ0').
    { intros x Hx.
      assert (Hxd : x `in` dom Θ0)
        by (apply Hscp in Hx; clear - Hx Hsc0; fsetdec).
      destruct (rel_aenv_dom_l_inv HrΘ Hxd) as (y & Hy & Hat).
      assert (Ey : y = x) by (exact (Hfun x y x Hxd Hat (@rel_atom__id ρ V x Hx))).
      subst y. exact Hy. }
    assert (Hαfun : forall y,
              rel_atom (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0) V α y ->
              y = α2) by exact Hαonly.
    assert (Hαnd : α `notin` dom (Ξ ++ Θ1))
      by (clear - Hfr HΞΘ1; repeat rewrite dom_app; fsetdec).
    assert (Hα2nd : α2 `notin` dom (Ξ2 ++ Θ1')).
    { assert (Hd : α2 `notin` dom Ξ2 ∪ dom Θ1')
        by (clear - HuqOut2; simpl_env in HuqOut2; destruct_uniq;
            unfold disjoint in *; simpl_env in *; fsetdec).
      clear - Hd. repeat rewrite dom_app. fsetdec. }
    assert (HagrΞ : flex_agree_rel (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0) V
                      (Ξ ++ Θ1) (Ξ2 ++ Θ1'))
      by (eapply flex_agree_peel;
          [ exact Hagrout
          | apply rel_atom__pair; apply in_or_app; right; left; reflexivity
          | exact Hinjout | exact Hαfun | exact Hαnd | exact Hα2nd
          | intros x Hx; exact Hx
          | intros y Hy Ey; subst; contradiction ]).
    assert (Hagrfin : flex_agree_rel (ρeo ++ ρ) V Θ1 Θ1').
    { destruct HagrΞ as [HagV Hagp]. split.
      - intros x HxV.
        assert (HxΞ : x `notin` dom Ξ).
        { assert (Hxd : x `in` dom Θ0)
            by (apply Hscp in HxV; clear - HxV Hsc0; fsetdec).
          assert (Hd : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
          unfold disjoint in Hd. clear - Hd Hxd. fsetdec. }
        assert (HxΞ2 : x `notin` dom Ξ2)
          by (intros Hc; exact (HΞ2Θ0 x Hc (HVdom0' x HxV))).
        rewrite <- (a_flex_tvar_app_notin Ξ Θ1 HxΞ).
        rewrite <- (a_flex_tvar_app_notin Ξ2 Θ1' HxΞ2).
        exact (HagV x HxV).
      - intros a b0 Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        + assert (HaΞ : a `notin` dom Ξ) by (exact (HρeoΞ _ _ Hin)).
          destruct (Hdomeo _ _ Hin) as [Hd1 Hd2].
          assert (HbΞ2 : b0 `notin` dom Ξ2).
          { assert (Hd : uniq (Ξ2 ++ (α2 ~ abind_tvar) ++ Θ1'))
              by exact HuqOut2.
            clear - Hd Hd2. simpl_env in Hd. destruct_uniq.
            unfold disjoint in *. simpl_env in *. fsetdec. }
          pose proof (Hagp a b0 ltac:(apply in_or_app; left;
                        exact (Hρeoincl _ _ Hin))) as Hab0.
          rewrite (a_flex_tvar_app_notin Ξ Θ1 HaΞ) in Hab0.
          rewrite (a_flex_tvar_app_notin Ξ2 Θ1' HbΞ2) in Hab0.
          exact Hab0.
        + destruct (AtomSetProperties.In_dec a (dom Ξ)) as [HaΞ | HaΞ].
          * apply Hdel; [ exact Hin | | ].
            { assert (Hd : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
              unfold disjoint in Hd. clear - Hd HaΞ. fsetdec. }
            { clear - HaΞ HΞΘ1. fsetdec. }
          * destruct (a == α) as [-> | Hane].
            { apply Hdel; [ exact Hin | exact Hαd | clear - Hfr; fsetdec ]. }
            assert (Hbne : b0 <> α2)
              by (intros ->; apply Hα2c; eapply cols_r_in; exact Hin).
            assert (Hin0 : In (a, b0) (restrict_pairs α α2 ρ0))
              by (apply restrict_pairs_in;
                  [ apply Hρ0in; assumption | exact Hane
                  | exact Hbne ]).
            assert (HbΞ2 : b0 `notin` dom Ξ2).
            { intros Hb2.
              destruct (rel_aenv_dom_r_inv HrΞ2 Hb2) as (a'' & Ha'' & Hat'').
              assert (Ea : a'' = a).
              { apply (Hinjout a'' a b0 Hat''). apply rel_atom__pair.
                apply in_or_app; right; right; exact Hin0. }
              subst a''. contradiction. }
            assert (HaΞ' : a `notin` dom Ξ) by exact HaΞ.
            pose proof (Hagp a b0 ltac:(apply in_or_app; right; right;
                          exact Hin0)) as Hab0.
            rewrite (a_flex_tvar_app_notin Ξ Θ1 HaΞ') in Hab0.
            rewrite (a_flex_tvar_app_notin Ξ2 Θ1' HbΞ2) in Hab0.
            exact Hab0. }
    split; [ exact Hagrfin | ].
    (* ---- the YIELD is the check-against, so it just widens ---- *)
    split.
    { eapply rel_pskl_mono;
        [ exact HrP0 | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    (* ---- rel_ext, weakened off the opener ---- *)
    split.
    { destruct Hext as [Hxfr [Hri Hlf]]. unfold rel_ext.
      split; [ | split ].
      - intros a b0 Hin. destruct (Hxfr _ _ (Hρeoincl _ _ Hin)) as [Hna Hnb].
        simpl in Hna. split; [ clear - Hna; fsetdec | clear - Hnb; fsetdec ].
      - intros a1 a2' b0 H1 H2.
        exact (Hri a1 a2' b0 (Hρeoincl _ _ H1) (Hρeoincl _ _ H2)).
      - intros a b1 b2 H1 H2.
        exact (Hlf a b1 b2 (Hρeoincl _ _ H1) (Hρeoincl _ _ H2)). }
    exact Hdomeo.
  - (* S-UnivGhostR : output = ⫯subject, context unchanged *)
    intros Θ0 P Hg.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 C2 Hu4 ]; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', (pskl_tophole P').
    split.
    { apply e_sub__univ_ghost_r.
      eapply rel_pskl_guarded; [ exact HrP | exact Hg ]. }
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ apply rel_pskl__tophole; exact HrP | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* S-FlexMono : hand to the WALK at the empty pending suffix *)
    intros NM M P0 Θ0 Θ1 α Q Hf IHf.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP as [ | n1 | u1 α2 Hatα | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 F2 Hu8 ]; subst.
    assert (HcovP0 : ftvar_in_pskl P0' [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion Hwfp as [ | Θz Δz αz Hd | | | | ]; subst. exact Hd. }
    destruct (IHf S0 Θ0' nil α2 P0' ρ V HrΘ (@rel_aenv__nil ρ V) Hatα HrP0
                ltac:(simpl_env; exact Hagr) Hinj
                ltac:(simpl_env; exact Hfun)
                ltac:(simpl_env; exact Hwf) a_decls__nil a_decls__nil
                ltac:(simpl_env; exact Huq2p)
                ltac:(simpl_env; exact Hftv2)
                ltac:(simpl_env; exact Hscp)
                ltac:(simpl_env; exact Hblk)
                ltac:(simpl_env; exact HdΘ) Hcov HcovP0
                ltac:(simpl_env; exact Hwfp0)
                ltac:(simpl_env; exact Hbα))
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_sub__flex_mono; exact De | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ simpl_env in Hext; exact Hext | ]. exact Hdom1.
  - (* ⭐ S-Arrow : consistency on the domain, then the codomain at ITS output *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IHs.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 P0a2 P0b2 HrP0a HrP0b
                      | A3 A4 Hu1 | | A5 A6 Hu2 ]; subst.
    inversion HrP as [ | n1 | u3 v3 Hu3 | B1 B2 P12 P22 HrP1 HrP2
                     | B3 B4 Hu4 | | B5 B6 Hu5 ]; subst.
    inversion Hwfp0 as [ Θx Δx | Θx Δx αx Hbx | Θx Δx Xa Xb Hw0a Hw0b
                       | Lx Θx Δx Xp Hallx | Θx Δx
                       | Θx Δx Xp Hgx Hwix ]; subst.
    inversion Hwfp as [ Θy Δy | Θy Δy αy Hby | Θy Δy Ya Yb Hw1a Hw1b
                      | Ly Θy Δy Yp Hally | Θy Δy
                      | Θy Δy Yp Hgy Hwiy ]; subst.
    assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hdm0 : dom Θ0 [<=] dom Θ1) by (exact (auc_dom_mono_consis Hc)).
    assert (Hdm1 : dom Θ1 [<=] dom Θ2)
      by (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hs)).
    assert (Hblk1 : forall a, a `in` dom Θ1 -> a `notin` dom Θ0 ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk; [ clear - Ha Hdm1; fsetdec | exact Hn ]).
    assert (HcovP1 : ftvar_in_pskl P0a2 ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    destruct (lift_consis_nil Hc HrΘ HrP0a HrP1 Hagr Hinj Hfun Hwf Huq2p
                Hftv2 Hscp Hblk1 HdΘ Hcov HcovP1 Hw0a Hw1a)
      as (S1 & ρe1 & Θ1' & Q1' & D1e & HrΘ1 & Hagr1 & HrQ1 & Hext1 & Hdom1).
    pose proof (e_consis_supply_grows D1e) as Hgr1.
    assert (HdΘ1 : dom Θ1' [<=] S1).
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ _ _ _ D1e) as Hup.
      clear - Hup HdΘ Hgr1. fsetdec. }
    assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl P0a2
                    ∪ ftvar_in_pskl P12 [<=] S0)
      by (clear - Hftv2 HcovP1; fsetdec).
    assert (Hftv1 : ftvar_in_aenv Θ1' [<=] S1)
      by (eapply (proj2 (proj2 e_assign_unify_consis_ctx_ftvar));
          [ exact D1e | exact HcovE ]).
    assert (HcovE2 : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl P0a2
                     ∪ ftvar_in_pskl P12 ∪ empty ∪ empty [<=] S0)
      by (clear - HcovE; fsetdec).
    assert (Huq1' : uniq Θ1').
    { pose proof (e_consis_sound D1e Huq2p HcovE2) as Ha1.
      exact ((proj2 (proj2 a_assign_unify_consis_uniq)) _ _ _ _ _ _ _ Ha1
               Huq2p). }
    (* ---- side 1's context at the first half's output ---- *)
    destruct (a_consis_isub_wf_nil Hc Hwf Hw0a Hw1a) as [Hle01 HwfΘ1].
    assert (Hd1s : dom Θ1 [<=] ftvar_in_aenv Θ1)
      by (apply dom_subset_ftvar_in_aenv).
    assert (Hscp1 : V [<=] ftvar_in_aenv Θ1)
      by (clear - Hscp Hsc0 Hdm0 Hd1s; fsetdec).
    assert (Hwfp0b1 : {{ Θ1 ⨟ empty ⊢ₚₛ P0b }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hw0b ]).
    assert (Hwfp21 : {{ Θ1 ⨟ empty ⊢ₚₛ P2 }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hw1b ]).
    (* ---- the relation, widened by the first half's new pairs ---- *)
    assert (Hinj1 : rel_inj (ρe1 ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (HVdom0 : V [<=] dom Θ0) by (clear - Hscp Hsc0; fsetdec).
    assert (Hfun1 : rel_fun (ρe1 ++ ρ) V (dom Θ1)).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hext1 | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; exact (Hblk1 a Ha Hn)
        | intros a Ha Hn; clear - HVdom0 Hn; fsetdec ]. }
    assert (HrP0b' : rel_pskl (ρe1 ++ ρ) V P0b P0b2)
      by (apply rel_pskl_widen; exact HrP0b).
    assert (HrP2' : rel_pskl (ρe1 ++ ρ) V P2 P22)
      by (apply rel_pskl_widen; exact HrP2).
    assert (Hc1r : cols_r ρe1 [<=] S1).
    { intros y Hy. destruct (cols_r_in_inv _ _ Hy) as (a & Hin).
      destruct (Hdom1 _ _ Hin) as [_ Hd2]. clear - Hd2 HdΘ1. fsetdec. }
    assert (Hcov1 : V ∪ cols_r (ρe1 ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hcov Hc1r Hgr1. fsetdec. }
    assert (Hblk2 : forall a, a `in` dom Θ2 -> a `notin` dom Θ1 ->
                    a `notin` cols_l (ρe1 ++ ρ)).
    { intros a Ha Hn. rewrite cols_l_app.
      assert (Hc1 : a `notin` cols_l ρe1).
      { intros Hy. destruct (cols_l_in_inv _ _ Hy) as (y & Hin).
        destruct (Hdom1 _ _ Hin) as [Hd1 _]. contradiction. }
      assert (Hc2 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn Hdm0; fsetdec ]).
      clear - Hc1 Hc2. fsetdec. }
    assert (HcovP2 : ftvar_in_pskl P0b2 ∪ ftvar_in_pskl P22 [<=] S1)
      by (simpl in HcovP; clear - HcovP Hgr1; fsetdec).
    destruct (IHs S1 Θ1' P0b2 P22 (ρe1 ++ ρ) V HrΘ1 HrP0b' HrP2' Hagr1
                Hinj1 Hfun1 HwfΘ1 Huq1' Hftv1 Hscp1 Hblk2 HdΘ1 Hcov1 HcovP2
                Hwfp0b1 Hwfp21)
      as (S2 & ρe2 & Θ2' & Q2' & D2e & HrΘ2 & Hagr2 & HrQ2 & Hext2 & Hdom2).
    assert (HcovE3 : ftvar_in_aenv Θ1' ∪ ftvar_in_pskl P0b2
                     ∪ ftvar_in_pskl P22 [<=] S1)
      by (clear - Hftv1 HcovP2; fsetdec).
    assert (Hdm2' : dom Θ1' [<=] dom Θ2').
    { pose proof (e_sub_sound D2e Huq1' HcovE3) as Ha2.
      exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Ha2). }
    exists S2, (ρe2 ++ ρe1), Θ2', (pskl_arrow Q1' Q2').
    split; [ eapply e_sub__arrow; [ exact D1e | exact D2e ] | ].
    rewrite app_assoc.
    split; [ exact HrΘ2 | ].
    split; [ exact Hagr2 | ].
    split.
    { constructor; [ | exact HrQ2 ].
      eapply rel_pskl_mono;
        [ exact HrQ1 | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    split.
    { eapply rel_ext_app;
        [ exact Hext1 | exact Hext2
        | clear - Hsc0 Hdm0 Hd1s; fsetdec
        | exact Hgr1
        | intros a b Hin; destruct (Hdom1 _ _ Hin) as [Hd1 Hd2];
          split; [ clear - Hd1 Hd1s; fsetdec | clear - Hd2 HdΘ1; fsetdec ] ]. }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hdom2 _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; [ clear - Hd1 Hdm1; fsetdec | clear - Hd2 Hdm2'; fsetdec ].
  - (* ⭐⭐ S-ForallL — the COMMON opener, and the extract is NOT inductive.
       [a_extract_family_of_instance] moves side 1's opener to any fresh
       atom with the SAME [Ξ ↪ P1], and side 2's is ours to pick subject
       only to [α' ∉ S0]; so both sides run at ONE atom and the relation
       carries it by IDENTITY.  ⭐ The opener never enters the subtyping
       premise's CONTEXT — the extract consumes it and leaves [Θ0] alone —
       so there is no pair to push and no junk suffix to strip. *)
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hne Hg Hfr Hex Huq Hwf1 Hs IHs.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2
                     | Pb Pb2 HrPb | | C1 C2 Hu3 ]; subst.
    (* ---- side 1's data ---- *)
    assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HfrP : α `notin` ftvar_in_pskl P) by (clear - Hfr; solve_notin_auto).
    assert (Hdm : dom (Ξ ++ Θ0) [<=] dom Θ1)
      by (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hs)).
    rewrite dom_app in Hdm.
    assert (HΞΘ0 : dom Ξ ∩ dom Θ0 [=] empty).
    { assert (Hdisj : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
      unfold disjoint in Hdisj. clear - Hdisj. fsetdec. }
    (* ⭐ THE BLOCK PREMISE [a_extract_rel_e] WANTS, read off the motive's
       own [Hblk]: the block is inside [dom Θ1] and outside [dom Θ0]. *)
    assert (HblkΞ : dom Ξ ∩ cols_l ρ [=] empty).
    { intros x. split; intros Hx; [ | clear - Hx; fsetdec ].
      exfalso.
      assert (HxΞ : x `in` dom Ξ) by (clear - Hx; fsetdec).
      assert (Hxc : x `in` cols_l ρ) by (clear - Hx; fsetdec).
      apply (Hblk x); [ clear - Hdm HxΞ; fsetdec
                      | clear - HΞΘ0 HxΞ; fsetdec | exact Hxc ]. }

    (* ---- the COMMON opener ---- *)
    assert (Hfam0 : exists L, forall a0,
              a0 `notin` (singleton α `union` ftvar_in_pskl P `union` L) ->
              {{ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f a0))
                 ⊳[ NM , a0 , M ] P0 ⤳ Ξ ↪ P1 }}a)
      by (eapply a_extract_family_of_instance; [ exact Hex | exact HfrP ]).
    destruct Hfam0 as (L & Hfam).
    destruct (atom_fresh (S0 ∪ cols_l ρ ∪ ftvar_in_aenv Θ0 ∪ dom Θ0
                            ∪ dom Ξ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P0
                            ∪ singleton α ∪ L)) as [α' Hα'].
    pose proof (Hfam α' ltac:(clear - Hα'; solve_notin_auto)) as Hex'.
    assert (Hα'S0 : α' `notin` S0) by (clear - Hα'; solve_notin_auto).
    assert (Hα'cl : α' `notin` cols_l ρ) by (clear - Hα'; solve_notin_auto).
    assert (Hα'Θ0 : α' `notin` ftvar_in_aenv Θ0)
      by (clear - Hα'; solve_notin_auto).
    assert (Hα'd0 : α' `notin` dom Θ0) by (clear - Hα'; solve_notin_auto).
    assert (Hα'Ξ : α' `notin` dom Ξ) by (clear - Hα'; solve_notin_auto).
    assert (Hα'cr : α' `notin` cols_r ρ) by (clear - Hα'S0 Hcov; fsetdec).
    assert (Hα'd0' : α' `notin` dom Θ0') by (clear - Hα'S0 HdΘ; fsetdec).
    assert (Hα'V : α' `notin` V) by (clear - Hα'Θ0 Hscp; fsetdec).

    (* ---- the extract, at [add α' V] and [add α' S0] ---- *)
    assert (HrPo : rel_pskl ρ (add α' V)
                     (open_pskl_wrt_pskl P (pskl_var_f α'))
                     (open_pskl_wrt_pskl Pb2 (pskl_var_f α')))
      by (apply rel_pskl_open_var; exact HrPb).
    assert (HrP0w : rel_pskl ρ (add α' V) P0 P0')
      by (eapply rel_pskl_mono;
          [ exact HrP0 | intros x y Hx; exact Hx | clear; fsetdec ]).
    assert (Hagr2 : flex_agree_rel ρ (add α' V) Θ0 Θ0').
    { destruct Hagr as [HagV Hagp]. split; [ | exact Hagp ].
      intros x Hx. destruct (x == α') as [-> | Hnex].
      - split; intros Hfl; exfalso; apply a_flex_tvar_in_dom in Hfl;
          [ apply Hα'd0; exact Hfl | apply Hα'd0'; exact Hfl ].
      - apply HagV. clear - Hx Hnex. fsetdec. }
    assert (Hscp' : add α' V [<=] add α' (ftvar_in_aenv Θ0))
      by (clear - Hscp; fsetdec).
    assert (HdΘ' : dom Θ0' [<=] add α' S0) by (clear - HdΘ; fsetdec).
    assert (Hcov' : add α' V ∪ cols_r ρ [<=] add α' S0)
      by (clear - Hcov; fsetdec).
    assert (HcovP' : ftvar_in_pskl (open_pskl_wrt_pskl Pb2 (pskl_var_f α'))
                     ∪ ftvar_in_pskl P0' [<=] add α' S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Pb2
                    (pskl_var_f α')) as Hup.
      simpl in Hup. simpl in HcovP. clear - Hup HcovP. fsetdec. }
    assert (Hα'in : α' `in` add α' V) by (clear; fsetdec).
    destruct (a_extract_rel_e Hex' HrPo HrP0w Hα'in Hα'cl Hα'cr Hagr2
                Hscp' HblkΞ Hα'Ξ HdΘ' Hcov' HcovP')
      as (S1e & ρx & ρn & Ξ2 & P1' & De & EΞ1 & EΞ2 & Hρx & Hxblk & HrP1).
    pose proof (e_extract_block De) as (HΞ2S1 & HΞ2S0 & HuqΞ2 & HftvΞ2).
    pose proof (e_extract_supply_grows De) as Hgre.
    assert (Hdfl : dom Ξ [=] cols_l ρn)
      by (rewrite EΞ1; apply dom_flex_pairs_l).
    assert (Hdfr : dom Ξ2 [=] cols_r ρn)
      by (rewrite EΞ2; apply dom_flex_pairs_r).
    assert (HΞ2S : dom Ξ2 ∩ S0 [=] empty) by (clear - HΞ2S0; fsetdec).

    (* ⭐⭐ THE ρx COLUMN GOES BEFORE THE IH.  [ρx] is the extract's LEAKED
       OPENERS; the motive's [Hblk] cannot keep them out of [dom Θ1], and
       a [rel_fun] extension would owe the same, so the IH must run at
       [ρn ++ ρ].  ⭐ What pays is the extract's own block conjunct
       ([Hxblk]) together with the rule's SCOPING FILTER on [P1]: every
       free variable of [P1] is bound in [Ξ ++ Θ0], and ρx's atoms are in
       NEITHER half. *)
    assert (HftP1 : ftvar_in_pskl P1 [<=] dom (Ξ ++ Θ0)).
    { intros x Hx. apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds Hwf1 Hx). }
    rewrite dom_app in HftP1.
    assert (Hdrop : rel_pskl (ρn ++ ρ) V P1 P1').
    { eapply rel_pskl_morph_ftv; [ exact HrP1 | | ].
      - intros a b Ha Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin]; [ exfalso | apply rel_atom__pair; exact Hin ].
        assert (Hal : a `in` cols_l ρx) by (eapply cols_l_in; exact Hin).
        destruct (Hρx _ _ Hin) as [Hnf _].
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds0.
        clear - Ha Hal Hnf Hxblk HftP1 Hds0. fsetdec.
      - intros a Ha Hv. apply rel_atom__id.
        assert (Hnea : a <> α')
          by (intros Ex; rewrite Ex in Ha;
              clear - Ha HftP1 Hα'd0 Hα'Ξ; fsetdec).
        clear - Hv Hnea. fsetdec. }

    (* ---- the IH, at [Ξ ++ Θ0] / [Ξ2 ++ Θ0'] ---- *)
    assert (HrΞ : rel_aenv (ρn ++ ρ) V Ξ Ξ2)
      by (rewrite EΞ1, EΞ2; apply rel_aenv_flex_pairs).
    assert (HrΘw : rel_aenv (ρn ++ ρ) V Θ0 Θ0')
      by (eapply rel_aenv_mono;
          [ exact HrΘ | intros x y Hx; apply in_or_app; right; exact Hx
          | intros x Hx; exact Hx ]).
    assert (HrΘΞ : rel_aenv (ρn ++ ρ) V (Ξ ++ Θ0) (Ξ2 ++ Θ0'))
      by (apply rel_aenv_app; [ exact HrΞ | exact HrΘw ]).
    assert (HrP0n : rel_pskl (ρn ++ ρ) V P0 P0')
      by (eapply rel_pskl_mono;
          [ exact HrP0 | intros x y Hx; apply in_or_app; right; exact Hx
          | intros x Hx; exact Hx ]).
    assert (HrPn : rel_pskl (ρn ++ ρ) V P Pb2)
      by (eapply rel_pskl_mono;
          [ exact HrPb | intros x y Hx; apply in_or_app; right; exact Hx
          | intros x Hx; exact Hx ]).
    assert (HrOpen : rel_pskl (ρn ++ ρ) V
                       (open_pskl_wrt_pskl P P1)
                       (open_pskl_wrt_pskl Pb2 P1'))
      by (apply rel_pskl_open_skl; [ exact HrPn | exact Hdrop ]).
    assert (HΞV : dom Ξ ∩ V [=] empty)
      by (clear - HΞΘ0 Hscp Hsc0; fsetdec).
    assert (Hnl : cols_l ρn ∩ (V ∪ cols_l ρ) [=] empty)
      by (clear - HΞV HblkΞ Hdfl; fsetdec).
    assert (Hnr : cols_r ρn ∩ (V ∪ cols_r ρ) [=] empty)
      by (clear - HΞ2S Hdfr Hcov; fsetdec).
    assert (HagrΞ : flex_agree_rel (ρn ++ ρ) V (Ξ ++ Θ0) (Ξ2 ++ Θ0')).
    { rewrite EΞ1, EΞ2. apply flex_agree_rel_push_pairs;
        [ exact Hagr | exact Hnl | exact Hnr ]. }
    assert (Hextn : rel_ext ρn (ftvar_in_aenv Θ0) S0).
    { apply rel_ext_flex_pairs;
        [ rewrite <- EΞ1; clear - Huq; solve_uniq
        | rewrite <- EΞ2; exact HuqΞ2
        | clear - Hdfl HΞΘ0 Hsc0; fsetdec
        | clear - Hdfr HΞ2S; fsetdec ]. }
    assert (Hinjn : rel_inj (ρn ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hextn | exact Hcov ]).
    assert (Hfunn : rel_fun (ρn ++ ρ) V (dom (Ξ ++ Θ0))).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hextn
        | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; rewrite dom_app in Ha;
          apply (Hblk a); [ clear - Hdm Ha Hn; fsetdec | exact Hn ]
        | intros a Ha Hn; rewrite dom_app in Ha;
          clear - Ha Hn Hscp Hsc0; fsetdec ]. }
    assert (HwfΞ : {{ ⊢ (Ξ ++ Θ0) }}a).
    { apply a_wf_aenv_decls_app;
        [ rewrite EΞ1; apply a_decls_flex_pairs_l | exact Huq | exact Hwf ]. }
    assert (HuqΞ2' : uniq (Ξ2 ++ Θ0')).
    { assert (Hd2 : dom Ξ2 ∩ dom Θ0' [=] empty)
        by (clear - HΞ2S HdΘ; fsetdec).
      clear - HuqΞ2 Huq2p Hd2. solve_uniq. }
    assert (Hftv2' : ftvar_in_aenv (Ξ2 ++ Θ0') [<=] S1e).
    { rewrite ftvar_in_aenv_app.
      clear - HftvΞ2 HΞ2S1 Hftv2 Hgre Hα'S0. fsetdec. }
    assert (HscpΞ : V [<=] ftvar_in_aenv (Ξ ++ Θ0))
      by (rewrite ftvar_in_aenv_app; clear - Hscp; fsetdec).
    assert (HblkIH : forall a, a `in` dom Θ1 -> a `notin` dom (Ξ ++ Θ0) ->
              a `notin` cols_l (ρn ++ ρ)).
    { intros a Ha Hn. rewrite dom_app in Hn. rewrite cols_l_app.
      assert (Hn1 : a `notin` cols_l ρn) by (clear - Hn Hdfl; fsetdec).
      assert (Hn2 : a `notin` cols_l ρ)
        by (apply (Hblk a); [ exact Ha | clear - Hn; fsetdec ]).
      clear - Hn1 Hn2. fsetdec. }
    assert (HdΘΞ : dom (Ξ2 ++ Θ0') [<=] S1e)
      by (rewrite dom_app; clear - HΞ2S1 HdΘ Hgre Hα'S0; fsetdec).
    assert (HcovΞ : V ∪ cols_r (ρn ++ ρ) [<=] S1e).
    { rewrite cols_r_app.
      clear - Hcov Hdfr HΞ2S1 Hgre Hα'S0. fsetdec. }
    assert (Hcov1 : ftvar_in_pskl (open_pskl_wrt_pskl Pb2 (pskl_var_f α'))
                    ∪ ftvar_in_pskl P0' [<=] S1e)
      by (clear - HcovP' Hgre; fsetdec).
    assert (HP1'S : ftvar_in_pskl P1' [<=] S1e).
    { pose proof (e_extract_out_ftvar De) as Hout.
      clear - Hout Hcov1. fsetdec. }
    assert (HPb2S : ftvar_in_pskl Pb2 [<=] S1e).
    { simpl in HcovP. clear - HcovP Hgre. fsetdec. }
    assert (HcovPΞ : ftvar_in_pskl P0'
                     ∪ ftvar_in_pskl (open_pskl_wrt_pskl Pb2 P1') [<=] S1e).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Pb2 P1') as Hup.
      clear - Hup HP1'S HPb2S Hcov1. fsetdec. }
    assert (Hwfp0Ξ : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_weaken;
          [ intros x b Hbd; apply binds_app_3; exact Hbd | exact Hwfp0 ]).
    assert (HwfpΞ : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                       (open_pskl_wrt_pskl P P1) }}a).
    { inversion Hwfp; subst.
      match goal with
      | Hb : forall a, a `notin` ?L0 -> _ |- _ =>
          eapply a_wf_pskl_open with (L := L0); [ | exact Hwf1 ];
          intros a0 Ha0; eapply a_wf_pskl_weaken;
            [ intros x b Hbd; apply binds_app_1 in Hbd;
              destruct Hbd as [Hbd | Hbd];
              [ apply binds_app_2; exact Hbd
              | apply binds_app_3; apply binds_app_3; exact Hbd ]
            | apply Hb; exact Ha0 ]
      end. }
    destruct (IHs S1e (Ξ2 ++ Θ0') P0'
                (open_pskl_wrt_pskl Pb2 P1') (ρn ++ ρ) V
                HrΘΞ HrP0n HrOpen HagrΞ Hinjn Hfunn HwfΞ HuqΞ2' Hftv2'
                HscpΞ HblkIH HdΘΞ HcovΞ HcovPΞ Hwfp0Ξ HwfpΞ)
      as (S2 & ρe1 & Θ1' & Q' & D2e & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).

    (* ⛔⛔ OWED (2) — side 2's scoping premise for [e_sub__forall_l]. *)
    assert (Hwf2 : {{ (Ξ2 ++ Θ0') ⨟ empty ⊢ₚₛ P1' }}a).
    { eapply a_wf_pskl_rel;
        [ exact Hwf1 | exact HrΘΞ | exact Hfunn | clear; fsetdec
        | exact Hdrop ]. }

    (* ---- the answer ---- *)
    exists S2, (ρe1 ++ ρn), Θ1', Q'.
    split.
    { eapply e_sub__forall_l with (α := α').
      - exact Hne.
      - destruct Hg as [Hgd | ->];
          [ left; eapply rel_pskl_guarded; [ exact HrP0 | exact Hgd ]
          | inversion HrP0; subst; right; reflexivity ].
      - exact Hα'S0.
      - exact De.
      - exact Hwf2.
      - exact D2e. }
    rewrite app_assoc.
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    assert (Hdm2 : dom (Ξ2 ++ Θ0') [<=] dom Θ1').
    { assert (HcovE : ftvar_in_aenv (Ξ2 ++ Θ0') ∪ ftvar_in_pskl P0'
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl Pb2 P1') [<=] S1e)
        by (clear - Hftv2' HcovPΞ; fsetdec).
      pose proof (e_sub_sound D2e HuqΞ2' HcovE) as Ha2.
      exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Ha2). }
    split.
    { eapply rel_ext_app;
        [ exact Hextn | exact Hext1
        | rewrite ftvar_in_aenv_app; clear; fsetdec
        | clear - Hgre Hα'S0; fsetdec
        | intros a b Hin;
          assert (Hal : a `in` cols_l ρn) by (eapply cols_l_in; exact Hin);
          assert (Har : b `in` cols_r ρn) by (eapply cols_r_in; exact Hin);
          split;
            [ rewrite ftvar_in_aenv_app;
              pose proof (dom_subset_ftvar_in_aenv Ξ) as Hdsx;
              clear - Hal Hdfl Hdsx; fsetdec
            | clear - Har Hdfr HΞ2S1; fsetdec ] ]. }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hdom1 _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + assert (Hal : a `in` cols_l ρn) by (eapply cols_l_in; exact Hin).
      assert (Har : b `in` cols_r ρn) by (eapply cols_r_in; exact Hin).
      split;
        [ clear - Hal Hdfl Hdm; fsetdec
        | clear - Har Hdfr Hdm2; rewrite dom_app in Hdm2; fsetdec ].
  - (* S-Ghost : output = the check-against, context unchanged *)
    intros M Θ0 P0 Hmg.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP as [ | n1 | u1 v1 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 F2 Hu8 ]; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', P0'.
    split; [ apply e_sub__ghost; exact Hmg | ]. simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ exact HrP0 | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* S-UnivGhostL : strip the subject's ⫯ *)
    intros M Θ0 Θ1 P0 P Q Hne Hs IHs.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP as [ | n1 | u1 v1 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 P12 HrPb ]; subst.
    assert (HcovP1 : ftvar_in_pskl P0' ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hwfp1 : {{ Θ0 ⨟ empty ⊢ₚₛ P }}a)
      by (inversion Hwfp; subst; rewrite aenv_minus_empty in *; assumption).
    destruct (IHs S0 Θ0' P0' P12 ρ V HrΘ HrP0 HrPb Hagr Hinj Hfun Hwf Huq2p
                Hftv2 Hscp Hblk HdΘ Hcov HcovP1 Hwfp0 Hwfp1)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_sub__univ_ghost_l; [ exact Hne | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* ⭐⭐ W-Solve — the walk's GENERATIVE row.  It invents two atoms fresh
       for the CONTEXT only, so (like the ∀ rows) ρ must be restricted at
       them first; then TWO pairs are pushed and the head gains a
       definition. *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hαf Hβf Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hbα.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b0 & bd2 & Θ0'' & E0' & Hab0 & Hbd0 & Hrest).
    subst Θ0'. inversion Hbd0; subst.
    destruct (atom_fresh S0) as [a2 Ha2].
    destruct (atom_fresh (add a2 S0)) as [b2 Hb2].
    assert (Hα0d : α0 `in` dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Eα' : α' = b0) by (exact (Hfun α0 α' b0 Hα0d Hrα Hab0)).
    subst α'.
    assert (Hsc : ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)
                  [<=] dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hαnd : α `notin` dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite dom_app in Hαf |- *. simpl. clear - Hαf. fsetdec. }
    assert (Hβnd : β `notin` dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite dom_app in Hβf |- *. simpl. clear - Hβf. fsetdec. }
    (* ⭐ NO restriction is needed here, and that is the difference from
       [S-ForallR]: the two invented atoms SURVIVE into the output, so the
       motive's own block premise already puts them off ρ's left column. *)
    assert (Hdm : dom (Ξ ++ (α0 ~ abind_flex_mono_def
                              (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                         ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                         ++ Θ0) [<=] dom Θ1)
      by (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hprem)).
    assert (HαΘ1 : α `in` dom Θ1)
      by (clear - Hdm; repeat rewrite dom_app in Hdm; simpl in Hdm; fsetdec).
    assert (HβΘ1 : β `in` dom Θ1)
      by (clear - Hdm; repeat rewrite dom_app in Hdm; simpl in Hdm; fsetdec).
    assert (Hαcl : α `notin` cols_l ρ)
      by (apply Hblk; [ exact HαΘ1 | exact Hαnd ]).
    assert (Hβcl : β `notin` cols_l ρ)
      by (apply Hblk; [ exact HβΘ1 | exact Hβnd ]).
    assert (Hρincl : forall a b, In (a, b) ρ -> In (a, b) ρ)
      by (intros a b Hin; exact Hin).
    assert (Hρin : forall a b, In (a, b) ρ -> In (a, b) ρ)
      by (intros a b Hin; exact Hin).
    assert (Hcl00 : cols_l ρ [<=] cols_l ρ)
      by (clear; fsetdec).
    assert (Hcr00 : cols_r ρ [<=] cols_r ρ)
      by (clear; fsetdec).
    assert (HrΘ00 : rel_aenv ρ V Θ0 Θ0'') by (exact Hrest).
    assert (HrΞ0 : rel_aenv ρ V Ξ Ξ') by (exact HrΞ).
    assert (HrP00 : rel_pskl ρ V P0 P0') by (exact HrP0).
    assert (Hrα0 : rel_atom ρ V α0 b0) by (exact Hab0).
    assert (Hagr0 : flex_agree_rel ρ V (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)
                      (Ξ' ++ (b0 ~ abind_flex_mono) ++ Θ0''))
      by (exact Hagr).
    assert (Hinj0 : rel_inj ρ V) by (exact Hinj).
    assert (Hfun0 : rel_fun ρ V (dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)))
      by (exact Hfun).
    assert (Hcov0 : V ∪ cols_r ρ [<=] S0) by (exact Hcov).
    assert (Hαcl0 : α `notin` cols_l ρ) by (exact Hαcl).
    assert (Hβcl0 : β `notin` cols_l ρ) by (exact Hβcl).
    (* ---- the two pairs, and the extended relation ---- *)
    assert (Ha2V : a2 `notin` V) by (clear - Ha2 Hcov; fsetdec).
    assert (Hb2V : b2 `notin` V) by (clear - Hb2 Hcov; fsetdec).
    assert (Ha2cr : a2 `notin` cols_r ρ) by (clear - Ha2 Hcov Hcr00; fsetdec).
    assert (Hb2cr : b2 `notin` cols_r ρ) by (clear - Hb2 Hcov Hcr00; fsetdec).
    assert (Hab2 : a2 <> b2) by (clear - Hb2; fsetdec).
    assert (HαV : α `notin` V)
      by (intros Hin; apply Hαnd; apply Hscp in Hin; clear - Hin Hsc; fsetdec).
    assert (HβV : β `notin` V)
      by (intros Hin; apply Hβnd; apply Hscp in Hin; clear - Hin Hsc; fsetdec).
    remember ((α, a2) :: (β, b2) :: ρ) as ρ1 eqn:Eρ1.
    assert (Hρ1incl : forall a b, In (a, b) ρ -> In (a, b) ρ1)
      by (subst ρ1; intros a b Hin; right; right; exact Hin).
    assert (Hinj1 : rel_inj ρ1 V).
    { subst ρ1. apply rel_inj_push;
        [ apply rel_inj_push; [ exact Hinj0 | exact Hb2V | exact Hb2cr ]
        | exact Ha2V | simpl; clear - Ha2cr Hab2; fsetdec ]. }
    assert (Hfun1 : rel_fun ρ1 V
              (dom (Ξ ++ (α0 ~ abind_flex_mono_def
                            (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                      ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                      ++ Θ0))).
    { subst ρ1. eapply rel_fun_weaken;
        [ apply rel_fun_push;
            [ apply rel_fun_push; [ exact Hfun0 | exact HβV | exact Hβcl0 ]
            | exact HαV | simpl; clear - Hαcl0 Hne; fsetdec ]
        | intros x y Hx; exact Hx
        | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (HrΘ1 : rel_aenv ρ1 V
              (Ξ ++ (α0 ~ abind_flex_mono_def
                       (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
              (Ξ' ++ (b0 ~ abind_flex_mono_def
                        (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
                  ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
                  ++ Θ0'')).
    { apply rel_aenv_app.
      - eapply rel_aenv_mono;
          [ exact HrΞ0 | exact Hρ1incl | intros x Hx; exact Hx ].
      - apply rel_aenv__cons.
        + eapply rel_atom_incl; [ exact Hrα0 | exact Hρ1incl ].
        + constructor. unfold rel_ptyp. simpl. constructor;
            apply rel_pskl__var_f; apply rel_atom__pair; subst ρ1;
            [ left; reflexivity | right; left; reflexivity ].
        + apply rel_aenv__cons;
            [ apply rel_atom__pair; subst ρ1; right; left; reflexivity
            | constructor | ].
          apply rel_aenv__cons;
            [ apply rel_atom__pair; subst ρ1; left; reflexivity
            | constructor | ].
          eapply rel_aenv_mono;
            [ exact HrΘ00 | exact Hρ1incl | intros x Hx; exact Hx ]. }
    assert (Hagr1 : flex_agree_rel ρ1 V
              (Ξ ++ (α0 ~ abind_flex_mono_def
                       (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
              (Ξ' ++ (b0 ~ abind_flex_mono_def
                        (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
                  ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
                  ++ Θ0'')).
    { split.
      - intros x HxV.
        assert (Hxα : x <> α) by (intros ->; contradiction).
        assert (Hxβ : x <> β) by (intros ->; contradiction).
        assert (Hxa2 : x <> a2) by (intros ->; contradiction).
        assert (Hxb2 : x <> b2) by (intros ->; contradiction).
        rewrite (a_flex_tvar_solve_shape Ξ _ _ Θ0 Hxα Hxβ).
        rewrite (a_flex_tvar_solve_shape Ξ' _ _ Θ0'' Hxa2 Hxb2).
        exact (proj1 Hagr0 x HxV).
      - intros x y Hin. subst ρ1.
        destruct Hin as [E1 | [E2 | Hin]].
        + injection E1 as -> ->. split; intros _; left; unfold binds;
            apply in_or_app; right; right; right; left; reflexivity.
        + injection E2 as -> ->. split; intros _; left; unfold binds;
            apply in_or_app; right; right; left; reflexivity.
        + assert (Hxα : x <> α)
            by (intros ->; apply Hαcl0; eapply cols_l_in; exact Hin).
          assert (Hxβ : x <> β)
            by (intros ->; apply Hβcl0; eapply cols_l_in; exact Hin).
          assert (Hya2 : y <> a2)
            by (intros ->; apply Ha2cr; eapply cols_r_in; exact Hin).
          assert (Hyb2 : y <> b2)
            by (intros ->; apply Hb2cr; eapply cols_r_in; exact Hin).
          rewrite (a_flex_tvar_solve_shape Ξ _ _ Θ0 Hxα Hxβ).
          rewrite (a_flex_tvar_solve_shape Ξ' _ _ Θ0'' Hya2 Hyb2).
          exact (proj2 Hagr0 x y Hin). }
    (* ---- the premise's wf package ---- *)
    assert (Huq1 : uniq (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hwf0 : {{ ⊢ Θ0 }}a).
    { eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (α0 ~ abind_flex_mono)).
      simpl_env. exact Hwf. }
    assert (Hwfmid : {{ ⊢ ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                           ++ Θ0) }}a).
    { apply a_wf_aenv__flex;
        [ simpl; clear - Hβf Hne; simpl_env in *; fsetdec | ].
      apply a_wf_aenv__flex;
        [ clear - Hαf; simpl_env in *; fsetdec | exact Hwf0 ]. }
    assert (HbαM : binds α abind_flex_mono
                    ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0))
      by (unfold binds; simpl; right; left; reflexivity).
    assert (HbβM : binds β abind_flex_mono
                    ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0))
      by (unfold binds; simpl; left; reflexivity).
    assert (Hwfdef : {{ ⊢ ((α0 ~ abind_flex_mono_def
                              (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                           ++ Θ0) }}a).
    { apply a_wf_aenv__flex_def.
      - simpl. clear - Hαf Hβf Huq1. simpl_env in *. solve_uniq.
      - apply a_wf_ptyp__arrow; apply a_wf_ptyp__var;
          [ right; left; exact HbαM | right; left; exact HbβM ].
      - repeat constructor.
      - exact Hwfmid. }
    assert (HwfBig : {{ ⊢ (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) }}a).
    { apply a_wf_aenv_prepend_decls;
        [ exact Hdec | clear - Huq1; solve_uniq | | exact Hwfdef ].
      intros γ Hγ. simpl_env. clear - Huq1 Hαf Hβf Hγ. destruct_uniq.
      unfold disjoint in *. simpl_env in *. fsetdec. }
    assert (Hbigmon : forall γ, a_binds_tvar γ (Ξ ++ (α0 ~ abind_flex_mono)
                                                  ++ Θ0) ->
              a_binds_tvar γ (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
    { intros γ [Hb | [Hb | [t Hb]]]; unfold binds in Hb;
        apply in_app_or in Hb; destruct Hb as [Hb | Hb];
        try (simpl in Hb; destruct Hb as [E | Hb]; [ inversion E; subst | ]);
        solve [ left; unfold binds; apply in_or_app; left; exact Hb
              | right; left; unfold binds; apply in_or_app; left; exact Hb
              | right; right; exists t; unfold binds; apply in_or_app; left;
                exact Hb
              | right; right;
                exists (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β));
                unfold binds; apply in_or_app; right; left; reflexivity
              | left; unfold binds; apply in_or_app; right;
                simpl; right; right; right; exact Hb
              | right; left; unfold binds; apply in_or_app; right;
                simpl; right; right; right; exact Hb
              | right; right; exists t; unfold binds; apply in_or_app; right;
                simpl; right; right; right; exact Hb ]. }
    assert (Hwfp01 : {{ (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_weaken_tvarish; [ exact Hbigmon | exact Hwfp0 ]).
    assert (Hwfp11 : {{ (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (pskl_arrow (pskl_var_f α) (pskl_var_f β)) }}a).
    { apply a_wf_pskl__arrow; apply a_wf_pskl__var;
        [ right; left | right; left ]; unfold binds; apply in_or_app; right;
        simpl; [ right; right; left; reflexivity
               | right; left; reflexivity ]. }
    (* ---- side 2's package at the extended context ---- *)
    assert (Ha2d : a2 `notin` dom (Ξ' ++ (b0 ~ abind_flex_mono) ++ Θ0''))
      by (clear - Ha2 HdΘ; fsetdec).
    assert (Hb2d : b2 `notin` dom (Ξ' ++ (b0 ~ abind_flex_mono) ++ Θ0''))
      by (clear - Hb2 HdΘ; fsetdec).
    assert (Huq21 : uniq (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'')).
    { assert (Hbase : uniq ((Ξ' ++ (b0 ~ abind_flex_mono_def
                               (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2))))
                            ++ Θ0''))
        by (clear - Huq2p; simpl_env in *; solve_uniq).
      assert (Hstep1 : uniq ((Ξ' ++ (b0 ~ abind_flex_mono_def
                                (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2))))
                             ++ (a2 ~ abind_flex_mono) ++ Θ0'')).
      { apply uniq_insert_mid;
          [ exact Hbase
          | simpl_env in Ha2d; simpl_env; clear - Ha2d; fsetdec
          | simpl_env in Ha2d; clear - Ha2d; fsetdec ]. }
      assert (Hstep2 : uniq ((Ξ' ++ (b0 ~ abind_flex_mono_def
                                (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2))))
                             ++ (b2 ~ abind_flex_mono)
                             ++ (a2 ~ abind_flex_mono) ++ Θ0'')).
      { apply uniq_insert_mid;
          [ exact Hstep1
          | simpl_env in Hb2d; simpl_env; clear - Hb2d; fsetdec
          | simpl_env in Hb2d; simpl_env; clear - Hb2d Hab2; fsetdec ]. }
      simpl_env in Hstep2. simpl_env. exact Hstep2. }
    assert (Hftv21 : ftvar_in_aenv (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'') [<=] add b2 (add a2 S0)).
    { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *.
      simpl ftvar_in_aenv in Hftv2 |- *. simpl ftvar_in_abind in *.
      clear - Hftv2. fsetdec. }
    assert (Hscp1 : V [<=] ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite ftvar_in_aenv_app in Hscp |- *.
      simpl ftvar_in_aenv in Hscp |- *. simpl ftvar_in_abind in *.
      clear - Hscp. fsetdec. }
    assert (Hblk1 : forall a, a `in` dom Θ1 -> a `notin` dom (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ->
              a `notin` cols_l ρ1).
    { intros a Ha Hn. subst ρ1. simpl.
      repeat rewrite dom_app in Hn. simpl in Hn.
      assert (Hnα : a <> α) by (clear - Hn; fsetdec).
      assert (Hnβ : a <> β) by (clear - Hn; fsetdec).
      assert (Hc : a `notin` cols_l ρ).
      { apply Hblk; [ exact Ha | ].
        repeat rewrite dom_app. simpl. clear - Hn. fsetdec. }
      clear - Hc Hnα Hnβ Hcl00. fsetdec. }
    assert (HdΘ1 : dom (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'') [<=] add b2 (add a2 S0)).
    { repeat rewrite dom_app in HdΘ |- *. simpl in HdΘ |- *.
      clear - HdΘ. fsetdec. }
    assert (Hcov1 : V ∪ cols_r ρ1 [<=] add b2 (add a2 S0)).
    { subst ρ1. simpl. clear - Hcov. fsetdec. }
    assert (HcovP1 : ftvar_in_pskl P0'
                     ∪ ftvar_in_pskl (pskl_arrow (pskl_var_f a2)
                                                 (pskl_var_f b2))
                     [<=] add b2 (add a2 S0))
      by (simpl; clear - HcovP; fsetdec).
    destruct (IH (add b2 (add a2 S0)) (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'') P0'
                (pskl_arrow (pskl_var_f a2) (pskl_var_f b2)) ρ1 V
                HrΘ1 (ltac:(subst ρ1; eapply rel_pskl_mono;
                            [ exact HrP00 | intros x y Hx; right; right;
                              exact Hx | intros x Hx; exact Hx ]))
                (ltac:(subst ρ1; constructor; apply rel_pskl__var_f;
                       apply rel_atom__pair;
                       [ left; reflexivity | right; left; reflexivity ]))
                Hagr1 Hinj1 Hfun1 HwfBig Huq21 Hftv21 Hscp1 Hblk1 HdΘ1
                Hcov1 HcovP1 Hwfp01 Hwfp11)
      as (S1 & ρe & Θ1' & Q' & De & HrΘout & Hagrout & HrQ & Hext & Hdomout).
    assert (HcovE : ftvar_in_aenv (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'') ∪ ftvar_in_pskl P0'
                    ∪ ftvar_in_pskl (pskl_arrow (pskl_var_f a2)
                                                (pskl_var_f b2))
                    [<=] add b2 (add a2 S0))
      by (repeat apply AtomSetProperties.union_subset_3;
          solve [ exact Hftv21 | clear - HcovP1; fsetdec ]).
    pose proof (e_sub_sound De Huq21 HcovE) as HaD.
    assert (Hdm2 : dom (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'') [<=] dom Θ1')
      by (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ HaD)).
    assert (Ha2Θ1 : a2 `in` dom Θ1')
      by (clear - Hdm2; simpl_env in Hdm2; fsetdec).
    assert (Hb2Θ1 : b2 `in` dom Θ1')
      by (clear - Hdm2; simpl_env in Hdm2; fsetdec).
    assert (HsubW : ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)
                    [<=] ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite ftvar_in_aenv_app.
      simpl ftvar_in_aenv. simpl ftvar_in_abind. clear; fsetdec. }
    assert (Hαft : α `notin` ftvar_in_aenv
                     (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (clear - Hαnd Hsc; fsetdec).
    assert (Hβft : β `notin` ftvar_in_aenv
                     (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (clear - Hβnd Hsc; fsetdec).
    assert (Hαin : α `in` ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite ftvar_in_aenv_app.
      simpl ftvar_in_aenv. simpl ftvar_in_abind. clear; fsetdec. }
    assert (Hβin : β `in` ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite ftvar_in_aenv_app.
      simpl ftvar_in_aenv. simpl ftvar_in_abind. clear; fsetdec. }
    assert (Hnew : rel_ext ((α, a2) :: (β, b2) :: nil)
                     (ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)) S0).
    { unfold rel_ext. split; [ | split ].
      - intros a b Hin. destruct Hin as [E1 | [E2 | []]];
          [ inversion E1 | inversion E2 ]; subst;
          split; solve [ exact Hαft | exact Hβft | exact Ha2
                       | clear - Hb2; fsetdec ].
      - intros a1 a3 b H1 H2.
        destruct H1 as [E1 | [E1 | []]]; destruct H2 as [E2 | [E2 | []]];
          inversion E1; inversion E2; subst; try reflexivity;
          exfalso; clear - Hb2; fsetdec.
      - intros a b1 b3 H1 H2.
        destruct H1 as [E1 | [E1 | []]]; destruct H2 as [E2 | [E2 | []]];
          inversion E1; inversion E2; subst; try reflexivity;
          exfalso; apply Hne; reflexivity. }
    (* ---- assemble: the row's TWO pairs join what the premise invented ---- *)
    exists S1, (ρe ++ ((α, a2) :: (β, b2) :: nil)), Θ1', Q'.
    split; [ apply e_sub_flex__solve with (α := a2) (β := b2);
             [ exact Ha2 | exact Hb2 | exact De ] | ].
    rewrite app_assoc. simpl. subst ρ1.
    split; [ exact HrΘout | ].
    split; [ exact Hagrout | ].
    split; [ exact HrQ | ].
    split.
    { eapply rel_ext_app;
        [ exact Hnew | exact Hext | exact HsubW | clear; fsetdec | ].
      intros a b Hin. destruct Hin as [E1 | [E2 | []]];
        [ inversion E1 | inversion E2 ]; subst;
        split; solve [ exact Hαin | exact Hβin | clear; fsetdec ]. }
    intros a b Hin. apply in_app_or in Hin.
    destruct Hin as [Hin | [E1 | [E2 | []]]].
    + exact (Hdomout _ _ Hin).
    + inversion E1; subst. split; [ exact HαΘ1 | exact Ha2Θ1 ].
    + inversion E2; subst. split; [ exact HβΘ1 | exact Hb2Θ1 ].
  - (* ⭐ W-Assign — the walk's only DESCENT, and its premise runs at
       SUBSTITUTED skeletons.  ⚙ Simpler than the consis [Assign-Assign] it
       is templated on: [e_sub_flex__assign] carries NO side condition, so
       none of that row's [a_flex_tvar] plumbing for the subject is needed. *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβd Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'.
    inversion Hbd as [ | | t1 t2 Hrτ | A1 A2 HrA | Q1 Q2 HrQ0 ]; subst.
    assert (Huq1 : uniq (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq (Ξ' ++ (b ~ abind_flex_mono_def t2) ++ Θ0''))
      by (exact Huq2p).
    assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
    assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hτdom : ftvar_in_ptyp τ [<=] dom Θ0)
      by (apply a_wf_ptyp_ftv_dom;
          exact (proj1 (@a_wf_aenv_mid_def_inv Ξ β τ Θ0 Hdec Hwf))).
    assert (Hτ2dom : ftvar_in_ptyp t2 [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hsc : ftvar_in_aenv (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0)
                  [<=] dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (Hβnd : β `notin` dom (Ξ ++ Θ0)).
    { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
    { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hβd0 : β `in` dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Hβfun : forall y, rel_atom ρ V β y -> y = b)
      by (intros y Hy; exact (Hfun β y b Hβd0 Hy Hab)).
    remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VC eqn:EVC.
    assert (HVC : VC [<=] V) by (subst VC; clear; fsetdec).
    assert (HVCsplit : forall x, x `in` V -> x <> β -> x `in` VC).
    { intros x Hx Hne. subst VC.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      assert (Hxd : x `in` dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
        by (clear - Hx HVdom; fsetdec).
      repeat rewrite dom_app in Hxd. simpl in Hxd.
      repeat rewrite dom_app in Hds.
      clear - Hx Hne Hxd Hds. fsetdec. }
    assert (HVCne : forall x, x `in` VC -> x <> β).
    { intros x Hx Ex. rewrite Ex in Hx.
      assert (Hin : β `in` ftvar_in_aenv (Ξ ++ Θ0))
        by (subst VC; clear - Hx; fsetdec).
      clear - Hin HscC Hβnd. fsetdec. }
    assert (HrΘC : rel_aenv ρ VC (Ξ ++ Θ0) (Ξ' ++ Θ0'')).
    { eapply rel_aenv_shrink_V; [ apply rel_aenv_app; eassumption | ].
      intros x Hx Hf. apply HVCsplit; [ exact Hx | ].
      intros Ex. rewrite Ex in Hf.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      clear - Hf Hds HscC Hβnd. fsetdec. }
    assert (HrPsub : rel_pskl ρ V (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
                       (subst_pskl_in_pskl (ptyp_to_pskl t2) b P0'))
      by (apply rel_pskl_subst;
          [ exact HrP0 | exact Hrτ | exact Hab | exact Hinj | exact Hβfun ]).
    assert (HrVsub : rel_pskl ρ V
                       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
                       (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α')))
      by (apply rel_pskl_subst;
          [ constructor; exact Hrα | exact Hrτ | exact Hab | exact Hinj
          | exact Hβfun ]).
    assert (Hshr : forall (R : pskl) x, x `in` V ->
              x `in` ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β R) ->
              x `in` VC).
    { intros R x Hx Hin.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper R (ptyp_to_pskl τ) β)
        as Hu.
      rewrite ftvar_ptyp_to_pskl in Hu.
      destruct (AtomSetProperties.In_dec x (ftvar_in_ptyp τ)) as [Hxτ | Hxτ].
      - subst VC.
        pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
        repeat rewrite dom_app in Hds.
        clear - Hx Hxτ Hτdom Hds. fsetdec.
      - apply HVCsplit; [ exact Hx | ].
        intros Ex. rewrite Ex in Hin. clear - Hin Hu Hxτ Ex. fsetdec. }
    assert (HrPsubC : rel_pskl ρ VC (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b P0'))
      by (eapply rel_pskl_shrink_V;
          [ exact HrPsub | intros x Hx Hf; exact (Hshr P0 x Hx Hf) ]).
    assert (HrVsubC : rel_pskl ρ VC
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α')))
      by (eapply rel_pskl_shrink_V;
          [ exact HrVsub
          | intros x Hx Hf; exact (Hshr (pskl_var_f α) x Hx Hf) ]).
    assert (HagrC : flex_agree_rel ρ VC (Ξ ++ Θ0) (Ξ' ++ Θ0''))
      by (eapply flex_agree_peel;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | exact HVC | exact HVCne ]).
    assert (HinjC : rel_inj ρ VC)
      by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVC ]).
    assert (HfunC : rel_fun ρ VC (dom (Ξ ++ Θ0))).
    { eapply rel_fun_weaken;
        [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVC ]
        | intros x y Hx; exact Hx
        | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (HblkC : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne : a0 <> β) by (intros Ex; rewrite Ex in Ha0; contradiction).
        repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne. fsetdec. }
    assert (HdΘC : dom (Ξ' ++ Θ0'') [<=] S0)
      by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
          clear - HdΘ; fsetdec).
    assert (HcovC : VC ∪ cols_r ρ [<=] S0) by (clear - Hcov HVC; fsetdec).
    assert (Hα'd : ftvar_in_pskl (pskl_var_f α') [<=] S0).
    { simpl. pose proof (rel_atom_r_in Hrα) as Hin.
      clear - Hin Hcov. fsetdec. }
    assert (HcovS : ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl t2) b P0')
                    ∪ ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b
                           (pskl_var_f α')) [<=] S0).
    { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P0' (ptyp_to_pskl t2) b)
        as Hu1.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper (pskl_var_f α')
                    (ptyp_to_pskl t2) b) as Hu2.
      rewrite ftvar_ptyp_to_pskl in Hu1, Hu2.
      clear - Hu1 Hu2 HcovP Hτ2dom Hα'd. fsetdec. }
    (* ---- the wf package the a_sub premise wants ---- *)
    assert (HbβM : binds β (abind_flex_mono_def τ)
                    (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (unfold binds; apply in_or_app; right; simpl; left; reflexivity).
    assert (Hτmono : mono_ptyp τ)
      by (exact (@a_wf_aenv_binds_def_mono _ β τ Hwf HbβM)).
    assert (Hβτ : β `notin` ftvar_in_ptyp τ).
    { repeat rewrite dom_app in Hβnd. clear - Hτdom Hβnd. fsetdec. }
    assert (HwfPsub : {{ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ⨟ empty ⊢ₚₛ
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) }}a)
      by (apply a_wf_pskl_mono_subst;
          [ exact Hwfp0 | exact Hwf | exact HbβM | exact Hτmono ]).
    assert (HwfVsub : {{ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ⨟ empty ⊢ₚₛ
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                           (pskl_var_f α)) }}a).
    { apply a_wf_pskl_mono_subst;
        [ | exact Hwf | exact HbβM | exact Hτmono ].
      apply a_wf_pskl__var. exact HbαM. }
    assert (Hstrip : forall R,
              β `notin` ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β R)).
    { intros R.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper R (ptyp_to_pskl τ) β)
        as Hu.
      rewrite ftvar_ptyp_to_pskl in Hu. clear - Hu Hβτ. fsetdec. }
    assert (HwfPsubC : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) }}a)
      by (eapply a_wf_pskl_strip_mid; [ exact HwfPsub | exact (Hstrip P0) ]).
    assert (HwfVsubC : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                         (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                            (pskl_var_f α)) }}a)
      by (eapply a_wf_pskl_strip_mid;
          [ exact HwfVsub | exact (Hstrip (pskl_var_f α)) ]).
    assert (HscpC : VC [<=] ftvar_in_aenv (Ξ ++ Θ0))
      by (subst VC; clear; fsetdec).
    destruct (IH S0 (Ξ' ++ Θ0'')
                (subst_pskl_in_pskl (ptyp_to_pskl t2) b P0')
                (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α'))
                ρ VC HrΘC HrPsubC HrVsubC HagrC HinjC HfunC HwfC Huq2C
                Hftv2C HscpC HblkC HdΘC HcovC HcovS HwfPsubC HwfVsubC)
      as (S1 & ρe & Θ1' & Q' & D2 & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
    exists S1, ρe, ((b ~ abind_flex_mono_def t2) ++ Θ1'), Q'.
    split; [ apply e_sub_flex__assign with (τ := t2); exact D2 | ].
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros x y Hx. apply in_or_app. right. exact Hx.
      - constructor. unfold rel_ptyp in Hrτ |- *.
        eapply rel_pskl_mono;
          [ exact Hrτ | intros x y Hx; apply in_or_app; right; exact Hx
          | intros x Hx; exact Hx ].
      - eapply rel_aenv_mono;
          [ exact HrΘ1 | intros x y Hx; exact Hx | exact HVC ]. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V β b)
      by (eapply rel_atom_incl;
          [ exact Hab | intros x y Hx; apply in_or_app; right; exact Hx ]).
    assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V β y -> y = b).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hβfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
        | exact HVCsplit
        | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
        | split; intros _; right; eexists; unfold binds; simpl;
          left; reflexivity ]. }
    split.
    { eapply rel_pskl_mono;
        [ exact HrQ | intros x y Hx; exact Hx | exact HVC ]. }
    assert (Hftsub : ftvar_in_aenv (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0)
                     [<=] add β (ftvar_in_aenv (Ξ ++ Θ0))).
    { repeat rewrite ftvar_in_aenv_app. simpl.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hτdom Hds. fsetdec. }
    split.
    { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
      split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
      intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
      split; [ | exact Hb0 ].
      destruct (Hdom1 _ _ Hin) as [Hd1 _].
      assert (Hne : a0 <> β) by (intros Ex; rewrite Ex in Hd1; contradiction).
      clear - Ha0 Hne Hftsub. fsetdec. }
    intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; [ clear - Hd1; simpl_env; fsetdec
           | clear - Hd2; simpl_env; fsetdec ].
  - (* W-Depend : the entry MOVES into the pending suffix *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hbin Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Hne2 : α' <> b).
    { intros Ex. apply Hne. rewrite Ex in Hrα. exact (Hinj α β b Hrα Hab). }
    assert (Hβd0 : β `in` dom (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (HbinP : b `in` ftvar_in_pskl P0').
    { destruct (rel_pskl_ftv_corr_l HrP0 Hbin) as (y & Hy & Hat).
      assert (Ey : y = b) by (exact (Hfun β y b Hβd0 Hat Hab)).
      rewrite <- Ey. exact Hy. }
    assert (HrΞ' : rel_aenv ρ V (Ξ ++ (β ~ abind_flex_mono))
                     (Ξ' ++ (b ~ abind_flex_mono))).
    { apply rel_aenv_app; [ exact HrΞ | ].
      apply rel_aenv__cons; [ exact Hab | constructor | constructor ]. }
    assert (Hagr' : flex_agree_rel ρ V ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)
                      ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0''))
      by (simpl_env; exact Hagr).
    assert (Hfun' : rel_fun ρ V (dom ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)))
      by (simpl_env; exact Hfun).
    assert (HbαM' : a_binds_tvar α ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0))
      by (simpl_env; exact HbαM).
    assert (Hwf' : {{ ⊢ ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) }}a)
      by (simpl_env; exact Hwf).
    assert (Huq2' : uniq ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0''))
      by (simpl_env; exact Huq2p).
    assert (Hftv2' : ftvar_in_aenv ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0'')
                     [<=] S0)
      by (simpl_env; exact Hftv2).
    assert (Hdec' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app; [ exact Hdec | apply a_decls_one ]).
    assert (Hdec2' : a_decls (Ξ' ++ (b ~ abind_flex_mono)))
      by (apply a_decls_app; [ exact Hdec2 | apply a_decls_one ]).
    assert (Hscp' : V [<=] ftvar_in_aenv ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0))
      by (simpl_env; exact Hscp).
    assert (Hblk' : forall a0, a0 `in` dom Θ1 ->
              a0 `notin` dom ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) ->
              a0 `notin` cols_l ρ)
      by (intros a0 Ha0 Hn0; apply Hblk;
          [ exact Ha0
          | repeat rewrite dom_app in Hn0 |- *; simpl in Hn0 |- *;
            clear - Hn0; fsetdec ]).
    assert (HdΘ' : dom ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0'') [<=] S0).
    { repeat rewrite dom_app in HdΘ |- *. simpl in HdΘ |- *.
      clear - HdΘ. fsetdec. }
    assert (Hwfp0' : {{ ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) ⨟ empty
                       ⊢ₚₛ P0 }}a)
      by (simpl_env; exact Hwfp0).
    destruct (IH S0 Θ0'' (Ξ' ++ (b ~ abind_flex_mono)) α' P0' ρ V
                Hrest HrΞ' Hrα HrP0 Hagr' Hinj Hfun' Hwf' Hdec' Hdec2'
                Huq2' Hftv2' Hscp' Hblk' HdΘ' Hcov HcovP Hwfp0' HbαM')
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_sub_flex__depend;
             [ exact Hne2 | exact HbinP | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ simpl_env in Hext1; simpl_env; exact Hext1 | exact Hdom1 ].
  - (* W-Skip : flexible head, stepped over and re-attached *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    destruct (lift_sub_flex_peel IH Hne Hni Hβ1 HrΘ HrΞ Hrα HrP0 Hagr Hinj
                Hfun Hwf Hdec Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP
                Hwfp0 HbαM)
      as (b & bd2 & Θ0'' & S1 & ρe & Θ1' & Q' & E & Hbd & Hne2 & HbP
          & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    subst Θ0'. inversion Hbd; subst.
    exists S1, ρe, ((b ~ abind_flex_mono) ++ Θ1'), Q'.
    split; [ apply e_sub_flex__skip; [ exact Hne2 | exact HbP | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* W-SkipRigid *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    destruct (lift_sub_flex_peel IH Hne Hni Hβ1 HrΘ HrΞ Hrα HrP0 Hagr Hinj
                Hfun Hwf Hdec Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP
                Hwfp0 HbαM)
      as (b & bd2 & Θ0'' & S1 & ρe & Θ1' & Q' & E & Hbd & Hne2 & HbP
          & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    subst Θ0'. inversion Hbd; subst.
    exists S1, ρe, ((b ~ abind_tvar) ++ Θ1'), Q'.
    split;
      [ apply e_sub_flex__skip_rigid; [ exact Hne2 | exact HbP | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* W-SkipTmVar (type entry) : the two side conditions the rule does NOT
       state are THEOREMS — a term entry is not tvar-ish, so it is neither the
       walk's subject nor a free variable of the check-against *)
    intros NM M P0 Θ0 Θ1 Ξ α x Apay Q Hxout Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    assert (Huq1 : uniq (Ξ ++ (x ~ abind_var_typ Apay) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hbx : binds x (abind_var_typ Apay)
                    (Ξ ++ (x ~ abind_var_typ Apay) ++ Θ0))
      by (unfold binds; apply in_or_app; right; left; reflexivity).
    assert (Hne : α <> x)
      by (intros ->; eapply a_binds_tvar_not_var_typ;
          [ exact Huq1 | exact Hbx | exact HbαM ]).
    assert (Hni : x `notin` ftvar_in_pskl P0).
    { intros Hin.
      pose proof (a_wf_pskl_ftv_binds Hwfp0 Hin) as Htv;
        eapply a_binds_tvar_not_var_typ; [ exact Huq1 | exact Hbx | exact Htv ]. }
    destruct (lift_sub_flex_peel IH Hne Hni Hxout HrΘ HrΞ Hrα HrP0 Hagr Hinj
                Hfun Hwf Hdec Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP
                Hwfp0 HbαM)
      as (b & bd2 & Θ0'' & S1 & ρe & Θ1' & Q' & E & Hbd & Hne2 & HbP
          & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    subst Θ0'. inversion Hbd; subst.
    exists S1, ρe, ((b ~ abind_var_typ A2) ++ Θ1'), Q'.
    split; [ apply e_sub_flex__skip_tm_var; exact De | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* W-SkipTmVar (skeleton entry) *)
    intros NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hxout Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    assert (Huq1 : uniq (Ξ ++ (x ~ abind_var_skl Qpay) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hbx : binds x (abind_var_skl Qpay)
                    (Ξ ++ (x ~ abind_var_skl Qpay) ++ Θ0))
      by (unfold binds; apply in_or_app; right; left; reflexivity).
    assert (Hne : α <> x)
      by (intros ->; eapply a_binds_tvar_not_var_skl;
          [ exact Huq1 | exact Hbx | exact HbαM ]).
    assert (Hni : x `notin` ftvar_in_pskl P0).
    { intros Hin.
      pose proof (a_wf_pskl_ftv_binds Hwfp0 Hin) as Htv;
        eapply a_binds_tvar_not_var_skl; [ exact Huq1 | exact Hbx | exact Htv ]. }
    destruct (lift_sub_flex_peel IH Hne Hni Hxout HrΘ HrΞ Hrα HrP0 Hagr Hinj
                Hfun Hwf Hdec Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP
                Hwfp0 HbαM)
      as (b & bd2 & Θ0'' & S1 & ρe & Θ1' & Q' & E & Hbd & Hne2 & HbP
          & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    subst Θ0'. inversion Hbd; subst.
    exists S1, ρe, ((b ~ abind_var_skl Q2) ++ Θ1'), Q'.
    split; [ apply e_sub_flex__skip_tm_skl; exact De | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
Qed.

(* ===================================================================== *)
(*  §11  ⭐⭐ THE a_split RUNG — [a_split] lifts to [e_split], all 3 rows    *)
(*  (2026-08-21)                                                          *)
(*                                                                        *)
(*  Two of the three rows invent nothing and move nothing.  The third,     *)
(*  [Split-Flex], is [W-Solve]'s shape at a smaller scale: it invents TWO  *)
(*  flexibles and calls CONSISTENCY at Δ = ∅, so [lift_consis_nil] is the  *)
(*  whole of its content.  ⭐ NO restriction is needed — the two invented   *)
(*  atoms SURVIVE into the output ([auc_dom_mono_consis]), so the motive's  *)
(*  own block premise already puts them off ρ's left column.               *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  THE MOTIVE — the §8c.32 discipline, at [a_split]'s shape              *)
(*                                                                        *)
(*  [a_split] has ONE input skeleton and TWO outputs, and its only         *)
(*  generative row calls CONSISTENCY at Δ = ∅ — so [lift_consis_nil] is    *)
(*  the whole of its content, exactly as it was for [S-Check]/[S-Arrow].   *)
(* ===================================================================== *)

Definition lift_split_post (Θ0 : aenv) (P Q : pskl) (Θ1 : aenv)
    (S0 : atoms) (Θ0' : aenv) (P0' : pskl)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' P' Q',
    {{ S0 ↝ S1 ⊨ Θ0' ⊲ P0' ▹ P' ⇢ Q' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_pskl (ρe ++ ρ) V P P'
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_split_concl (Θ0 : aenv) (P0 P Q : pskl) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' P0' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    lift_split_post Θ0 P Q Θ1 S0 Θ0' P0' ρ V.

Theorem a_split_rel_e : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a ->
  lift_split_concl Θ0 P0 P Q Θ1.
Proof.
  intros Θ0 P0 P Q Θ1 HD.
  destruct HD as [ Θa Pa Qa | Θa | Θa Θb α β α1 Qc Hβf Hα1f Hc ];
    intros S0 Θ0' P0' ρ V HrΘ HrP0 Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0.
  - (* Split-Arrow : nothing is invented, nothing moves *)
    inversion HrP0 as [ | | | A1 A2 Pa2 Qa2 HrPa HrQa | | | ]; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', Pa2, Qa2.
    split; [ apply e_split__arrow | ]. simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ exact HrPa | ].
    split; [ exact HrQa | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* Split-Hole *)
    inversion HrP0; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', pskl_hole, pskl_hole.
    split; [ apply e_split__hole | ]. simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ apply rel_pskl__hole | ].
    split; [ apply rel_pskl__hole | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* ⭐⭐ Split-Flex — the generative row.  Same shape as [W-Solve]: the two
       invented atoms SURVIVE into the output, so the motive's own block
       premise puts them off ρ's left column and NO restriction is needed. *)
    inversion HrP0 as [ | | ax α2 Hat | | | | ]; subst.
    destruct (atom_fresh S0) as [b2 Hb2].
    destruct (atom_fresh (add b2 S0)) as [a2 Ha2].
    assert (Hsc : ftvar_in_aenv Θa [<=] dom Θa)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    pose proof (dom_subset_ftvar_in_aenv Θa) as Hds.
    assert (Hβnd : β `notin` dom Θa) by (clear - Hβf Hds; fsetdec).
    assert (Hα1nd : α1 `notin` dom Θa) by (clear - Hα1f Hds; fsetdec).
    assert (Hα1β : α1 <> β) by (intros Ex; rewrite Ex in Hα1f;
                                clear - Hα1f; fsetdec).
    (* the two invented atoms reach the output *)
    assert (Hdm : dom ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θa)
                  [<=] dom Θb)
      by (exact (auc_dom_mono_consis Hc)).
    assert (HβΘ1 : β `in` dom Θb)
      by (clear - Hdm; simpl in Hdm; fsetdec).
    assert (Hα1Θ1 : α1 `in` dom Θb)
      by (clear - Hdm; simpl in Hdm; fsetdec).
    assert (Hβcl : β `notin` cols_l ρ)
      by (apply Hblk; [ exact HβΘ1 | exact Hβnd ]).
    assert (Hα1cl : α1 `notin` cols_l ρ)
      by (apply Hblk; [ exact Hα1Θ1 | exact Hα1nd ]).
    assert (HβV : β `notin` V) by (clear - Hβf Hscp; fsetdec).
    assert (Hα1V : α1 `notin` V) by (clear - Hα1f Hscp; fsetdec).
    assert (Hb2V : b2 `notin` V) by (clear - Hb2 Hcov; fsetdec).
    assert (Ha2V : a2 `notin` V) by (clear - Ha2 Hcov; fsetdec).
    assert (Hb2cr : b2 `notin` cols_r ρ) by (clear - Hb2 Hcov; fsetdec).
    assert (Ha2cr : a2 `notin` cols_r ρ) by (clear - Ha2 Hcov; fsetdec).
    assert (Ha2b2 : a2 <> b2) by (clear - Ha2; fsetdec).
    assert (Hb2d : b2 `notin` dom Θ0') by (clear - Hb2 HdΘ; fsetdec).
    assert (Ha2d : a2 `notin` dom Θ0') by (clear - Ha2 HdΘ; fsetdec).
    remember ((α1, a2) :: (β, b2) :: ρ) as ρ1 eqn:Eρ1.
    assert (Hρ1incl : forall a b, In (a, b) ρ -> In (a, b) ρ1)
      by (subst ρ1; intros a b Hin; right; right; exact Hin).
    (* ---- the extended contexts and the extended relation ---- *)
    assert (HrΘ1 : rel_aenv ρ1 V
              ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θa)
              ((a2 ~ abind_flex_mono) ++ (b2 ~ abind_flex_mono) ++ Θ0')).
    { apply rel_aenv__cons;
        [ apply rel_atom__pair; subst ρ1; left; reflexivity
        | constructor | ].
      apply rel_aenv__cons;
        [ apply rel_atom__pair; subst ρ1; right; left; reflexivity
        | constructor | ].
      eapply rel_aenv_mono;
        [ exact HrΘ | exact Hρ1incl | intros x Hx; exact Hx ]. }
    assert (Hagr1 : flex_agree_rel ρ1 V
              ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θa)
              ((a2 ~ abind_flex_mono) ++ (b2 ~ abind_flex_mono) ++ Θ0')).
    { split.
      - intros x HxV.
        assert (Hxα1 : x <> α1) by (intros ->; contradiction).
        assert (Hxβ : x <> β) by (intros ->; contradiction).
        assert (Hxa2 : x <> a2) by (intros ->; contradiction).
        assert (Hxb2 : x <> b2) by (intros ->; contradiction).
        rewrite ! a_flex_tvar_cons_other by assumption.
        exact (proj1 Hagr x HxV).
      - intros x0 y0 Hin. subst ρ1.
        destruct Hin as [E1 | [E2 | Hin]].
        + injection E1 as -> ->. split; intros _; left; unfold binds;
            simpl; left; reflexivity.
        + injection E2 as -> ->. split; intros _; left; unfold binds;
            simpl; right; left; reflexivity.
        + assert (Hxα1 : x0 <> α1)
            by (intros ->; apply Hα1cl; eapply cols_l_in; exact Hin).
          assert (Hxβ : x0 <> β)
            by (intros ->; apply Hβcl; eapply cols_l_in; exact Hin).
          assert (Hya2 : y0 <> a2)
            by (intros ->; apply Ha2cr; eapply cols_r_in; exact Hin).
          assert (Hyb2 : y0 <> b2)
            by (intros ->; apply Hb2cr; eapply cols_r_in; exact Hin).
          rewrite ! a_flex_tvar_cons_other by assumption.
          exact (proj2 Hagr x0 y0 Hin). }
    assert (Hinj1 : rel_inj ρ1 V).
    { subst ρ1. apply rel_inj_push;
        [ apply rel_inj_push; [ exact Hinj | exact Hb2V | exact Hb2cr ]
        | exact Ha2V | simpl; clear - Ha2cr Ha2b2; fsetdec ]. }
    assert (Hfun1 : rel_fun ρ1 V
              (dom ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θa))).
    { subst ρ1. eapply rel_fun_weaken;
        [ apply rel_fun_push;
            [ apply rel_fun_push; [ exact Hfun | exact HβV | exact Hβcl ]
            | exact Hα1V | simpl; clear - Hα1cl Hα1β; fsetdec ]
        | intros u v Hu; exact Hu
        | simpl; clear; fsetdec ]. }
    (* ---- the premise's packages ---- *)
    assert (Hwf1 : {{ ⊢ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono)
                          ++ Θa) }}a).
    { apply a_wf_aenv__flex; [ simpl; clear - Hα1f Hds Hα1β; fsetdec | ].
      apply a_wf_aenv__flex; [ exact Hβnd | exact Hwf ]. }
    assert (Huq2' : uniq ((a2 ~ abind_flex_mono) ++ (b2 ~ abind_flex_mono)
                           ++ Θ0'))
      by (clear - Huq2p Ha2d Hb2d Ha2b2; solve_uniq).
    assert (Hftv2' : ftvar_in_aenv ((a2 ~ abind_flex_mono)
                       ++ (b2 ~ abind_flex_mono) ++ Θ0')
                     [<=] add a2 (add b2 S0))
      by (simpl; clear - Hftv2; fsetdec).
    assert (Hscp1 : V [<=] ftvar_in_aenv ((α1 ~ abind_flex_mono)
                      ++ (β ~ abind_flex_mono) ++ Θa))
      by (simpl; clear - Hscp; fsetdec).
    assert (Hblk1 : forall a, a `in` dom Θb ->
              a `notin` dom ((α1 ~ abind_flex_mono)
                             ++ (β ~ abind_flex_mono) ++ Θa) ->
              a `notin` cols_l ρ1).
    { intros a Ha Hn. simpl in Hn. subst ρ1. simpl.
      assert (Hn0 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn; fsetdec ]).
      clear - Hn Hn0. fsetdec. }
    assert (HdΘ1 : dom ((a2 ~ abind_flex_mono) ++ (b2 ~ abind_flex_mono)
                         ++ Θ0') [<=] add a2 (add b2 S0))
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hcov1 : V ∪ cols_r ρ1 [<=] add a2 (add b2 S0))
      by (subst ρ1; simpl; clear - Hcov; fsetdec).
    assert (Hα2S : α2 `in` S0).
    { inversion Hat as [ u v Hin | u Hin ]; subst;
        [ assert (Hyr : α2 `in` cols_r ρ) by (eapply cols_r_in; exact Hin);
          clear - Hyr Hcov; fsetdec
        | clear - Hin Hcov; fsetdec ]. }
    assert (HcovP1 : ftvar_in_pskl (pskl_arrow (pskl_var_f b2)
                                      (pskl_var_f a2))
                     ∪ ftvar_in_pskl (pskl_var_f α2)
                     [<=] add a2 (add b2 S0))
      by (simpl; clear - Hα2S; fsetdec).
    assert (Hwfp1 : {{ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono)
                        ++ Θa) ⨟ empty ⊢ₚₛ
                       (pskl_arrow (pskl_var_f β) (pskl_var_f α1)) }}a).
    { apply a_wf_pskl__arrow;
        apply a_wf_pskl__var; right; left; unfold binds; simpl;
        solve [ left; reflexivity | right; left; reflexivity ]. }
    assert (Hwfp1s : {{ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono)
                         ++ Θa) ⨟ empty ⊢ₚₛ (pskl_var_f α) }}a)
      by (eapply a_wf_pskl_weaken;
          [ intros z bd Hb; apply binds_app_3; apply binds_app_3; exact Hb
          | exact Hwfp0 ]).
    assert (HrP1 : rel_pskl ρ1 V (pskl_arrow (pskl_var_f β) (pskl_var_f α1))
                     (pskl_arrow (pskl_var_f b2) (pskl_var_f a2))).
    { subst ρ1. constructor; apply rel_pskl__var_f; apply rel_atom__pair;
        [ right; left; reflexivity | left; reflexivity ]. }
    assert (HrPs : rel_pskl ρ1 V (pskl_var_f α) (pskl_var_f α2))
      by (apply rel_pskl__var_f; eapply rel_atom_incl;
          [ exact Hat | exact Hρ1incl ]).
    destruct (lift_consis_nil Hc HrΘ1 HrP1 HrPs Hagr1 Hinj1 Hfun1 Hwf1
                Huq2' Hftv2' Hscp1 Hblk1 HdΘ1 Hcov1 HcovP1 Hwfp1 Hwfp1s)
      as (S1 & ρe & Θ1' & Qc' & De & HrΘo & Hagro & HrQo & Hexto & Hdomo).
    exists S1, (ρe ++ (α1, a2) :: (β, b2) :: nil), Θ1',
      (pskl_var_f b2), (pskl_var_f a2).
    split.
    { apply e_split__flex with (Q := Qc');
        [ exact Hb2 | clear - Ha2; fsetdec | subst ρ1; exact De ]. }
    subst ρ1.
    assert (Erw : (ρe ++ (α1, a2) :: (β, b2) :: nil) ++ ρ
                  = ρe ++ (α1, a2) :: (β, b2) :: ρ)
      by (rewrite app_assoc; reflexivity).
    rewrite Erw.
    split; [ exact HrΘo | ].
    split; [ exact Hagro | ].
    split.
    { apply rel_pskl__var_f. apply rel_atom__pair.
      apply in_or_app. right. right. left. reflexivity. }
    split.
    { apply rel_pskl__var_f. apply rel_atom__pair.
      apply in_or_app. right. left. reflexivity. }
    split.
    { eapply rel_ext_app;
        [ | exact Hexto | | | ].
      - (* the two-pair rel_ext *)
        unfold rel_ext. split; [ | split ].
        + intros a b Hin. destruct Hin as [E | [E | []]];
            injection E as -> ->;
            [ split; [ clear - Hα1f; fsetdec | clear - Ha2; fsetdec ]
            | split; [ clear - Hβf; fsetdec | clear - Hb2; fsetdec ] ].
        + intros a1 a3 b Hin1 Hin2.
          destruct Hin1 as [E1 | [E1 | []]]; destruct Hin2 as [E2 | [E2 | []]];
            inversion E1; inversion E2; subst;
            solve [ reflexivity | exfalso; congruence ].
        + intros a b1 b3 Hin1 Hin2.
          destruct Hin1 as [E1 | [E1 | []]]; destruct Hin2 as [E2 | [E2 | []]];
            inversion E1; inversion E2; subst;
            solve [ reflexivity | exfalso; congruence ].
      - simpl. clear; fsetdec.
      - clear; fsetdec.
      - intros a b Hin. destruct Hin as [E | [E | []]];
          injection E as -> ->;
          [ split; [ simpl; clear; fsetdec | clear; fsetdec ]
          | split; [ simpl; clear; fsetdec | clear; fsetdec ] ]. }
    (* the two SIDE-2 atoms reach the output too, by the same route the
       [S-Arrow] row uses: soundness, then consistency's own dom-mono *)
    assert (HcovE : ftvar_in_aenv ((a2 ~ abind_flex_mono)
                      ++ (b2 ~ abind_flex_mono) ++ Θ0')
                    ∪ ftvar_in_pskl (pskl_arrow (pskl_var_f b2)
                                       (pskl_var_f a2))
                    ∪ ftvar_in_pskl (pskl_var_f α2) ∪ empty ∪ empty
                    [<=] add a2 (add b2 S0))
      by (clear - Hftv2' HcovP1; simpl in *; fsetdec).
    assert (Hdm2 : dom ((a2 ~ abind_flex_mono) ++ (b2 ~ abind_flex_mono)
                        ++ Θ0') [<=] dom Θ1').
    { pose proof (e_consis_sound De Huq2' HcovE) as Ha2s.
      exact (auc_dom_mono_consis Ha2s). }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hdomo _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + destruct Hin as [E | [E | []]]; injection E as -> ->;
        [ split; [ exact Hα1Θ1 | clear - Hdm2; simpl in Hdm2; fsetdec ]
        | split; [ exact HβΘ1 | clear - Hdm2; simpl in Hdm2; fsetdec ] ].
Qed.

(* ===================================================================== *)
(*  §12  ⭐⭐⭐ THE a_pat RUNG — [a_pat] lifts to [e_pat], all 10 rows        *)
(*  (2026-08-22, §8c.44–§8c.45)                                            *)
(*                                                                        *)
(*  ⭐ The motive relates EXPRESSIONS ([rel_exp], §13d of prop_solve_rel): *)
(*  the abs rows open the body at a term variable fresh only for the       *)
(*  CONTEXT while [e_pat]'s draw theirs from the SUPPLY, and that premise  *)
(*  is part of the induction, so the renaming route is closed (§8c.33).    *)
(*  ⚙ [a_wf_exp] and [a_sk_mode_compat] ride along as side-1 premises —    *)
(*  the first is what puts an annotation's type variables in the context,  *)
(*  the second is what makes the SK split CONTEXT-IDENTITY                 *)
(*  ([a_split_sk_shape]) at the abs rows.                                  *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  THE MOTIVE — the §8c.32 discipline, plus the EXPRESSION               *)
(*                                                                        *)
(*  ⭐ Side 2's expression is RELATED, not equal: the abs rows open at a    *)
(*  term variable the two sides choose differently (side 1 fresh for the   *)
(*  CONTEXT, side 2 fresh for the SUPPLY).  ⚙ [a_wf_exp] is what puts the  *)
(*  annotations' type variables in the context, which is what the four     *)
(*  [a_sub]-calling rows need to satisfy [lift_sub_concl]'s subject-wf.    *)
(* ===================================================================== *)

Definition lift_pat_post (Θ0 : aenv) (Q : pskl) (Θ1 : aenv)
    (S0 : atoms) (m : mode) (Θ0' : aenv) (P0' : pskl) (e' : exp)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' Q',
    {{ S0 ↝ S1 ⊨ Θ0' ⊢ˢ[ m ; P0' ] e' ⦂ Q' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_pat_concl (m : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (Q : pskl) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' P0' e' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    rel_exp ρ V e e' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' ∪ ftvar_in_exp e' ∪ fvar_in_exp e' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⊢ᵉ e }}a ->
    a_sk_mode_compat m P0 ->
    lift_pat_post Θ0 Q Θ1 S0 m Θ0' P0' e' ρ V.

(** ⚙ The four [a_sub]-calling rows, factored: they differ only in the
    SUBJECT skeleton and in the [e_pat] constructor they finish with. *)
Lemma lift_pat_sub : forall m Θ0 Θ1 P0 Ps Q,
  {{ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] Ps ⩽ Q ⊣ Θ1 }}a ->
  forall S0 Θ0' P0' Ps' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    rel_pskl ρ V Ps Ps' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' ∪ ftvar_in_pskl Ps' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ Ps }}a ->
    lift_sub_post Θ0 Q Θ1 S0 a_sub_mode_sk m Θ0' P0' Ps' ρ V.
Proof.
  intros m Θ0 Θ1 P0 Ps Q HD.
  exact ((proj1 a_sub_sub_flex_rel_e) _ _ _ _ _ _ _ HD).
Qed.

(* ===================================================================== *)
(*  ⭐⭐ THE SHARED ABS CORE — restrict at the TERM variable, push the      *)
(*  pair, run the body, then PEEL the term entry from both outputs.        *)
(*                                                                        *)
(*  The four abs rows differ only in their PRELUDE (split / consis-chk /   *)
(*  nothing) and in the [e_pat] constructor they finish with; the          *)
(*  restrict-push-run-peel is one lemma, exactly as [lift_sub_flex_peel]   *)
(*  was for the walk.  ⚙ The term variable does NOT reach the output       *)
(*  (§8c.40's discriminator), hence [restrict_pairs]; the junk suffix [Ξ]  *)
(*  DOES survive into the output, hence NO [restrict_l].                   *)
(* ===================================================================== *)

Lemma lift_pat_abs_core : forall m' Θb Q0 e Q Ξ Θc x bd,
  {{ ((x ~ bd) ++ Θb) ⊢ˢ[ m' ; Q0 ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q
     ⊣ (Ξ ++ (x ~ bd) ++ Θc) }}a ->
  lift_pat_concl m' ((x ~ bd) ++ Θb) Q0 (open_exp_wrt_exp e (exp_var_f x)) Q
    (Ξ ++ (x ~ bd) ++ Θc) ->
  a_suffix Ξ ->
  x `notin` dom (Ξ ++ Θb) ∪ dom Θc ∪ fvar_in_exp e ->
  x `notin` ftvar_in_exp e ->
  abind_is_tm bd ->
  ftvar_in_abind bd [<=] dom Θb ->
  a_sk_mode_compat m' Q0 ->
  forall S0 Θb' Q0' e' bd' ρ V,
  rel_aenv ρ V Θb Θb' ->
  rel_pskl ρ V Q0 Q0' ->
  rel_exp ρ V e e' ->
  rel_abind ρ V bd bd' ->
  abind_is_tm bd' ->
  ftvar_in_abind bd' [<=] S0 ->
  flex_agree_rel ρ V Θb Θb' ->
  rel_inj ρ V ->
  rel_fun ρ V (dom Θb) ->
  {{ ⊢ ((x ~ bd) ++ Θb) }}a ->
  {{ Θb ⨟ empty ⊢ₚₛ Q0 }}a ->
  {{ ((x ~ bd) ++ Θb) ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a ->
  uniq Θb' ->
  ftvar_in_aenv Θb' [<=] S0 ->
  V [<=] ftvar_in_aenv Θb ->
  (forall a, a `in` dom (Ξ ++ Θc) -> a `notin` dom Θb -> a `notin` cols_l ρ) ->
  dom Θb' [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl Q0' ∪ ftvar_in_exp e' ∪ fvar_in_exp e' [<=] S0 ->
  exists S1 x2 ρe Ξ2 Θc2' Q',
    x2 `notin` S0
    /\ {{ (add x2 S0) ↝ S1 ⊨ ((x2 ~ bd') ++ Θb') ⊢ˢ[ m' ; Q0' ]
          (open_exp_wrt_exp e' (exp_var_f x2)) ⦂ Q'
          ⊣ (Ξ2 ++ (x2 ~ bd') ++ Θc2') }}e
    /\ a_suffix Ξ2
    /\ rel_aenv (ρe ++ ρ) V (Ξ ++ Θc) (Ξ2 ++ Θc2')
    /\ flex_agree_rel (ρe ++ ρ) V (Ξ ++ Θc) (Ξ2 ++ Θc2')
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv Θb) S0
    /\ (forall a b, In (a, b) ρe ->
          a `in` dom (Ξ ++ Θc) /\ b `in` dom (Ξ2 ++ Θc2'))
    /\ dom Θb' [<=] dom (Ξ2 ++ Θc2').
Proof.
  intros m' Θb Q0 e Q Ξ Θc x bd Hbody IH Hsuf Hxf Hxe Htm Hbdf Hmod'.
  intros S0 Θb' Q0' e' bd' ρ V HrΘ HrQ0 HrE Hrbd Htm' Hbd'f Hagr Hinj Hfun
    HwfX HwfQ0 Hwfeo Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP.
  destruct (atom_fresh S0) as [x2 Hx2].
  simpl_env in Hxf.
  assert (HxΞ : x `notin` dom Ξ) by (clear - Hxf; fsetdec).
  assert (HxΘb : x `notin` dom Θb) by (clear - Hxf; fsetdec).
  assert (HxΘc : x `notin` dom Θc) by (clear - Hxf; fsetdec).
  assert (Hxfv : x `notin` fvar_in_exp e) by (clear - Hxf; fsetdec).
  assert (HwfΘb : {{ ⊢ Θb }}a)
    by (eapply a_wf_aenv_strip_prefix with (Ξ := x ~ bd); simpl_env;
        exact HwfX).
  assert (Hsc0 : ftvar_in_aenv Θb [<=] dom Θb)
    by (apply a_wf_aenv_ftv_dom; exact HwfΘb).
  assert (HxftvΘb : x `notin` ftvar_in_aenv Θb)
    by (clear - HxΘb Hsc0; fsetdec).
  assert (HxV : x `notin` V) by (clear - Hscp HxftvΘb; fsetdec).
  assert (Hxbd : x `notin` ftvar_in_abind bd) by (clear - Hbdf HxΘb; fsetdec).
  assert (HxQ0 : x `notin` ftvar_in_pskl Q0).
  { intros Hin. pose proof (a_wf_pskl_ftv_binds HwfQ0 Hin) as Htv;
    apply HxΘb; apply a_binds_tvar_in_dom; exact Htv. }
  assert (Hx2V : x2 `notin` V) by (clear - Hx2 Hcov; fsetdec).
  assert (Hx2cr : x2 `notin` cols_r ρ) by (clear - Hx2 Hcov; fsetdec).
  assert (Hx2Θb' : x2 `notin` dom Θb') by (clear - Hx2 HdΘ; fsetdec).
  assert (Hx2ftv : x2 `notin` ftvar_in_aenv Θb') by (clear - Hx2 Hftv2; fsetdec).
  assert (Hx2bd' : x2 `notin` ftvar_in_abind bd')
    by (clear - Hx2 Hbd'f; fsetdec).
  (* ---- the restriction, and the push ---- *)
  assert (Hρrincl : forall a b, In (a, b) (restrict_pairs x x2 ρ) ->
            In (a, b) ρ)
    by (intros a b Hin; eapply restrict_pairs_incl; exact Hin).
  assert (Hclr : cols_l (restrict_pairs x x2 ρ) [<=] cols_l ρ)
    by apply cols_l_restrict_pairs.
  assert (Hcrr : cols_r (restrict_pairs x x2 ρ) [<=] cols_r ρ)
    by apply cols_r_restrict_pairs.
  assert (Hxl : x `notin` cols_l (restrict_pairs x x2 ρ))
    by apply restrict_pairs_notin_l.
  assert (Hx2r : x2 `notin` cols_r (restrict_pairs x x2 ρ))
    by apply restrict_pairs_notin_r.
  assert (Hρ1incl : forall a b, In (a, b) (restrict_pairs x x2 ρ) ->
            In (a, b) ((x, x2) :: restrict_pairs x x2 ρ))
    by (intros a b Hin; right; exact Hin).
  assert (HrΘ1 : rel_aenv ((x, x2) :: restrict_pairs x x2 ρ) V
                   ((x ~ bd) ++ Θb) ((x2 ~ bd') ++ Θb')).
  { apply rel_aenv__cons;
      [ apply rel_atom__pair; left; reflexivity | | ].
    - eapply rel_abind_mono;
        [ eapply rel_abind_restrict; [ exact Hrbd | exact Hxbd | exact Hx2bd' ]
        | exact Hρ1incl | intros z Hz; exact Hz ].
    - eapply rel_aenv_mono;
        [ eapply rel_aenv_restrict; [ exact HrΘ | exact HxftvΘb | exact Hx2ftv ]
        | exact Hρ1incl | intros z Hz; exact Hz ]. }
  assert (Hx2Q0' : x2 `notin` ftvar_in_pskl Q0')
    by (clear - Hx2 HcovP; fsetdec).
  assert (HrQ01 : rel_pskl ((x, x2) :: restrict_pairs x x2 ρ) V Q0 Q0')
    by (eapply rel_pskl_mono;
        [ eapply rel_pskl_restrict;
            [ exact HrQ0 | exact HxQ0 | exact Hx2Q0' ]
        | exact Hρ1incl | intros z Hz; exact Hz ]).
  assert (HrEo : rel_exp ((x, x2) :: restrict_pairs x x2 ρ) V
                   (open_exp_wrt_exp e (exp_var_f x))
                   (open_exp_wrt_exp e' (exp_var_f x2))).
  { apply rel_exp_open_pair. apply rel_exp_restrict;
      [ exact HrE | clear - Hxfv Hxe; fsetdec
      | clear - Hx2 HcovP; fsetdec ]. }
  assert (Hagr1 : flex_agree_rel ((x, x2) :: restrict_pairs x x2 ρ) V
                    ((x ~ bd) ++ Θb) ((x2 ~ bd') ++ Θb')).
  { apply flex_agree_rel_push_tm;
      [ eapply flex_agree_rel_weaken;
          [ exact Hagr | exact Hρrincl | intros z Hz; exact Hz ]
      | apply abind_is_tm_nonflex; exact Htm
      | apply abind_is_tm_nonflex; exact Htm'
      | exact HxΘb | exact Hx2Θb' ]. }
  assert (Hinj1 : rel_inj ((x, x2) :: restrict_pairs x x2 ρ) V)
    by (apply rel_inj_push;
        [ eapply rel_inj_sub; [ exact Hinj | exact Hρrincl ]
        | exact Hx2V | exact Hx2r ]).
  assert (Hfun1 : rel_fun ((x, x2) :: restrict_pairs x x2 ρ) V
                    (dom ((x ~ bd) ++ Θb))).
  { simpl. apply rel_fun_push;
      [ eapply rel_fun_weaken;
          [ exact Hfun | exact Hρrincl | intros z Hz; exact Hz ]
      | exact HxV | exact Hxl ]. }
  assert (Huq2X : uniq ((x2 ~ bd') ++ Θb'))
    by (clear - Huq2p Hx2Θb'; solve_uniq).
  assert (Hftv2X : ftvar_in_aenv ((x2 ~ bd') ++ Θb') [<=] add x2 S0)
    by (simpl; clear - Hftv2 Hbd'f; fsetdec).
  assert (HscpX : V [<=] ftvar_in_aenv ((x ~ bd) ++ Θb))
    by (simpl; clear - Hscp; fsetdec).
  assert (HblkX : forall a, a `in` dom (Ξ ++ (x ~ bd) ++ Θc) ->
            a `notin` dom ((x ~ bd) ++ Θb) ->
            a `notin` cols_l ((x, x2) :: restrict_pairs x x2 ρ)).
  { intros a Ha Hn. simpl_env in Ha. simpl_env in Hn. simpl.
    assert (Hne : a <> x) by (clear - Hn; fsetdec).
    assert (Ha' : a `in` dom (Ξ ++ Θc))
      by (simpl_env; clear - Ha Hne; fsetdec).
    assert (Hc : a `notin` cols_l ρ)
      by (apply Hblk; [ exact Ha' | clear - Hn; fsetdec ]).
    clear - Hne Hc Hclr. fsetdec. }
  assert (HdΘX : dom ((x2 ~ bd') ++ Θb') [<=] add x2 S0)
    by (simpl; clear - HdΘ; fsetdec).
  assert (HcovX : V ∪ cols_r ((x, x2) :: restrict_pairs x x2 ρ)
                  [<=] add x2 S0)
    by (simpl; clear - Hcov Hcrr; fsetdec).
  assert (HcovPX : ftvar_in_pskl Q0'
                   ∪ ftvar_in_exp (open_exp_wrt_exp e' (exp_var_f x2))
                   ∪ fvar_in_exp (open_exp_wrt_exp e' (exp_var_f x2))
                   [<=] add x2 S0).
  { pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e' (exp_var_f x2)) as Hu1.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper e' (exp_var_f x2)) as Hu2.
    simpl in Hu1, Hu2. clear - HcovP Hu1 Hu2. fsetdec. }
  assert (HwfQ0X : {{ ((x ~ bd) ++ Θb) ⨟ empty ⊢ₚₛ Q0 }}a)
    by (eapply a_wf_pskl_weaken;
        [ intros z b0 Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
  destruct (IH (add x2 S0) ((x2 ~ bd') ++ Θb') Q0'
              (open_exp_wrt_exp e' (exp_var_f x2))
              ((x, x2) :: restrict_pairs x x2 ρ) V
              HrΘ1 HrQ01 HrEo Hagr1 Hinj1 Hfun1 HwfX Huq2X Hftv2X HscpX
              HblkX HdΘX HcovX HcovPX HwfQ0X Hwfeo Hmod')
    as (S1 & ρe & Θout' & Q' & De & HrΘo & Hagro & HrQo & Hexto & Hdomo).
  (* ---- side 1's output wf, and the body's dom-mono ---- *)
  destruct (a_pat_sound Hbody HwfX HwfQ0X Hmod' Hwfeo) as [Hle [HwfOut _]].
  assert (HuqOut : uniq (Ξ ++ (x ~ bd) ++ Θc))
    by (apply a_wf_aenv_uniq; exact HwfOut).
  assert (HwfΞΘc : {{ ⊢ (Ξ ++ Θc) }}a)
    by (eapply a_wf_aenv_strip_tm_mid;
        [ | exact HwfOut ];
        destruct bd; simpl in Htm |- *; intuition).
  assert (HftvΞΘc : ftvar_in_aenv (Ξ ++ Θc) [<=] dom (Ξ ++ Θc))
    by (apply a_wf_aenv_ftv_dom; exact HwfΞΘc).
  assert (HxftvOut : x `notin` ftvar_in_aenv (Ξ ++ Θc))
    by (simpl_env in HftvΞΘc; clear - HftvΞΘc HxΞ HxΘc; fsetdec).
  (* ---- side 2's packages at the body ---- *)
  pose proof (e_pat_supply_grows De) as Hgr.
  assert (HcovEX : ftvar_in_aenv ((x2 ~ bd') ++ Θb') ∪ ftvar_in_pskl Q0'
                   ∪ fvar_in_exp (open_exp_wrt_exp e' (exp_var_f x2))
                   ∪ ftvar_in_exp (open_exp_wrt_exp e' (exp_var_f x2))
                   [<=] add x2 S0)
    by (clear - Hftv2X HcovPX; fsetdec).
  destruct (e_pat_sound De Huq2X HcovEX) as (HaDe & HuqOut2 & HftvOut2 & HftQ').
  (* ---- the full pair list's injectivity, and the two exclusions ---- *)
  assert (Hinjout : rel_inj (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V)
    by (eapply rel_inj_app; [ exact Hinj1 | exact Hexto | exact HcovX ]).
  assert (Hxρe : forall b, ~ In (x, b) ρe).
  { intros b Hin. destruct Hexto as [Hxfr _].
    destruct (Hxfr _ _ Hin) as [Hna _].
    apply Hna. simpl. clear; fsetdec. }
  assert (Hx2ρe : forall a, ~ In (a, x2) ρe).
  { intros a Hin. destruct Hexto as [Hxfr _].
    destruct (Hxfr _ _ Hin) as [_ Hnb].
    apply Hnb. clear; fsetdec. }
  assert (Hxonly : forall y,
            rel_atom (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V x y ->
            y = x2).
  { intros y Hat. inversion Hat as [ a0 b0 Hin | a0 HinV ]; subst.
    - apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
      + exfalso. exact (Hxρe _ Hin).
      + inversion Ehd; reflexivity.
      + exfalso. apply Hxl. eapply cols_l_in; exact Hin.
    - exfalso. exact (HxV HinV). }
  (* ---- SPLIT the output at the junk suffix, then at the term entry ---- *)
  destruct (@rel_aenv_app_inv_l Ξ
              (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V
              ((x ~ bd) ++ Θc) Θout' HrΘo)
    as (Ξ2 & Θrest & Eout & HrΞ2 & HrTail).
  subst Θout'.
  destruct (rel_aenv_cons_inv_l HrTail)
    as (b & bd2' & Θc2' & E2 & Hab2 & Hbd2 & HrΘc2).
  subst Θrest.
  assert (Eb : b = x2) by (apply Hxonly; exact Hab2).
  subst b.
  (* ---- the term entry is PRESERVED, so side 2's mid binding is [bd'] ---- *)
  assert (Hb'out : binds x2 bd' (Ξ2 ++ (x2 ~ bd2') ++ Θc2')).
  { apply (a_pat_tm_le HaDe);
      [ exact Htm' | unfold binds; simpl; left; reflexivity ]. }
  assert (Ebd : bd2' = bd').
  { assert (Hbmid : binds x2 bd2' (Ξ2 ++ (x2 ~ bd2') ++ Θc2'))
      by (unfold binds; apply in_or_app; right; left; reflexivity).
    eapply binds_unique; [ exact Hbmid | exact Hb'out | exact HuqOut2 ]. }
  subst bd2'.
  (* ---- side 2's junk, and the term atom, off the stripped output ---- *)
  assert (Hx2out : x2 `notin` dom (Ξ2 ++ Θc2')).
  { clear - HuqOut2. simpl_env in HuqOut2. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (Hx2ftvOut : x2 `notin` ftvar_in_aenv (Ξ2 ++ Θc2')).
  { intros Hin.
    assert (HrOut : rel_aenv (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V
                      (Ξ ++ Θc) (Ξ2 ++ Θc2'))
      by (apply rel_aenv_app; [ exact HrΞ2 | exact HrΘc2 ]).
    destruct (rel_aenv_ftv_corr_r HrOut Hin) as (a & Ha & Hat).
    assert (Ea : a = x).
    { apply (Hinjout a x x2 Hat). apply rel_atom__pair.
      apply in_or_app. right. left. reflexivity. }
    subst a. exact (HxftvOut Ha). }
  (* ---- the answer's pieces ---- *)
  assert (HrOut : rel_aenv (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V
                    (Ξ ++ Θc) (Ξ2 ++ Θc2'))
    by (apply rel_aenv_app; [ exact HrΞ2 | exact HrΘc2 ]).
  assert (Hincl : forall a b0,
            In (a, b0) (restrict_pairs x x2
                          (ρe ++ (x, x2) :: restrict_pairs x x2 ρ)) ->
            In (a, b0) (ρe ++ ρ)).
  { intros a b0 Hin.
    assert (Hane : a <> x).
    { intros ->.
      apply (@restrict_pairs_notin_l x x2
               (ρe ++ (x, x2) :: restrict_pairs x x2 ρ)).
      eapply cols_l_in; exact Hin. }
    apply restrict_pairs_incl in Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
    - apply in_or_app; left; exact Hin.
    - exfalso. injection Ehd as E1 E2x. apply Hane. symmetry. exact E1.
    - apply in_or_app; right. apply Hρrincl. exact Hin. }
  assert (HrFinal : rel_aenv (ρe ++ ρ) V (Ξ ++ Θc) (Ξ2 ++ Θc2')).
  { eapply rel_aenv_mono;
      [ eapply rel_aenv_restrict;
          [ exact HrOut | exact HxftvOut | exact Hx2ftvOut ]
      | exact Hincl | intros z Hz; exact Hz ]. }
  (* ---- the yield: drop the pair via ftvar-correspondence ---- *)
  assert (HwfQout : {{ (Ξ ++ (x ~ bd) ++ Θc) ⨟ empty ⊢ₚₛ Q }}a)
    by (eapply a_pat_output_wf;
        [ exact Hbody | exact HwfX | exact HwfQ0X | exact Hmod'
        | exact Hwfeo ]).
  assert (HxQ : x `notin` ftvar_in_pskl Q).
  { intros Hin. pose proof (a_wf_pskl_ftv_binds HwfQout Hin) as Htv.
    assert (Hbx : binds x bd (Ξ ++ (x ~ bd) ++ Θc))
      by (unfold binds; apply in_or_app; right; left; reflexivity).
    destruct Htv as [Hb | [Hb | [τ Hb]]];
      pose proof (binds_unique _ _ _ _ _ Hb Hbx HuqOut) as E;
      subst bd; simpl in Htm; contradiction. }
  assert (Hx2Q' : x2 `notin` ftvar_in_pskl Q').
  { intros Hin.
    destruct (rel_pskl_ftv_corr_r HrQo Hin) as (a & Ha & Hat).
    assert (Ea : a = x).
    { apply (Hinjout a x x2 Hat). apply rel_atom__pair.
      apply in_or_app. right. left. reflexivity. }
    subst a. exact (HxQ Ha). }
  assert (HrQfin : rel_pskl (ρe ++ ρ) V Q Q').
  { eapply rel_pskl_mono;
      [ eapply rel_pskl_restrict; [ exact HrQo | exact HxQ | exact Hx2Q' ]
      | exact Hincl | intros z Hz; exact Hz ]. }
  (* ---- the agreement: PEEL the term entry, answer the deleted pairs ---- *)
  assert (HxOutd : x `notin` dom (Ξ ++ Θc))
    by (simpl_env; clear - HxΞ HxΘc; fsetdec).
  assert (HagrΞ : flex_agree_rel (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V
                    (Ξ ++ Θc) (Ξ2 ++ Θc2')).
  { eapply flex_agree_peel;
      [ exact Hagro
      | apply rel_atom__pair; apply in_or_app; right; left; reflexivity
      | exact Hinjout | exact Hxonly
      | exact HxOutd | exact Hx2out
      | intros z Hz; exact Hz
      | intros y Hy Ey; subst; contradiction ]. }
  (* the pairs [restrict_pairs] deleted: all have LEFT = x, and both
     halves of their agreement are FALSE at the outputs *)
  assert (Hdel : forall b0, In (x, b0) ρ ->
            (a_flex_tvar (Ξ ++ Θc) x <-> a_flex_tvar (Ξ2 ++ Θc2') b0)).
  { intros b0 Hin. split; intros Hf; exfalso.
    - apply HxOutd. apply a_flex_tvar_in_dom. exact Hf.
    - assert (HbS0 : b0 `in` S0).
      { assert (Hc : b0 `in` cols_r ρ) by (eapply cols_r_in; exact Hin).
        clear - Hc Hcov. fsetdec. }
      assert (Hbne : b0 <> x2) by (intros ->; clear - Hx2 HbS0; fsetdec).
      assert (Hf1 : a_flex_tvar (Ξ2 ++ (x2 ~ bd') ++ Θc2') b0)
        by (rewrite a_flex_tvar_insert_mid by exact Hbne; exact Hf).
      assert (Hbd1 : b0 `in` dom (Ξ2 ++ (x2 ~ bd') ++ Θc2'))
        by (apply a_flex_tvar_in_dom; exact Hf1).
      assert (Hb0in : b0 `in` dom Θb').
      { pose proof (e_pat_dom_upper De) as Hup.
        assert (Hbc : b0 `in` dom ((x2 ~ bd') ++ Θb'))
          by (clear - Hbd1 Hup HbS0; fsetdec).
        simpl_env in Hbc. clear - Hbc Hbne. fsetdec. }
      assert (Hb0X : b0 `in` dom ((x2 ~ bd') ++ Θb'))
        by (simpl_env; clear - Hb0in; fsetdec).
      pose proof (a_pat_flex_rev HaDe Hb0X Hf1) as Hf2.
      rewrite a_flex_tvar_cons_nonflex in Hf2
        by (apply abind_is_tm_nonflex; exact Htm').
      assert (Hnf0 : ~ a_flex_tvar Θb' b0).
      { intros Hc.
        assert (Hfx : a_flex_tvar Θb x)
          by (exact (proj2 (proj2 Hagr x b0 Hin) Hc)).
        apply HxΘb. apply a_flex_tvar_in_dom. exact Hfx. }
      exact (Hnf0 Hf2). }
  assert (Hagrfin : flex_agree_rel (ρe ++ ρ) V (Ξ ++ Θc) (Ξ2 ++ Θc2')).
  { destruct HagrΞ as [HagV Hagp]. split; [ exact HagV | ].
    intros a b0 Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - apply Hagp. apply in_or_app. left. exact Hin.
    - assert (Hbne : b0 <> x2)
      by (intros ->; apply Hx2cr; eapply cols_r_in; exact Hin).
      destruct (a == x) as [-> | Hane].
      + apply Hdel. exact Hin.
      + apply Hagp. apply in_or_app. right. right.
        apply restrict_pairs_in; [ exact Hin | exact Hane | exact Hbne ]. }
  (* ---- assemble ---- *)
  exists S1, x2, ρe, Ξ2, Θc2', Q'.
  split; [ exact Hx2 | ].
  split; [ exact De | ].
  split; [ eapply rel_aenv_suffix; [ exact HrΞ2 | exact Hsuf ] | ].
  split; [ exact HrFinal | ].
  split; [ exact Hagrfin | ].
  split; [ exact HrQfin | ].
  split.
  { destruct Hexto as [Hxfr [Hri Hlf]]. unfold rel_ext.
    split; [ | split ].
    - intros a b0 Hin. destruct (Hxfr _ _ Hin) as [Hna Hnb].
      simpl in Hna.
      split; [ clear - Hna; fsetdec | clear - Hnb; fsetdec ].
    - exact Hri.
    - exact Hlf. }
  split.
  { intros a b0 Hin.
    destruct (Hdomo _ _ Hin) as [Hd1 Hd2].
    assert (Hane : a <> x) by (intros ->; exact (Hxρe _ Hin)).
    assert (Hbne : b0 <> x2) by (intros ->; exact (Hx2ρe _ Hin)).
    simpl_env in Hd1. simpl_env in Hd2. simpl_env.
    split; [ clear - Hd1 Hane; fsetdec | clear - Hd2 Hbne; fsetdec ]. }
  (* ---- side 2's dom-mono, term entry stripped from both sides ---- *)
  pose proof (a_pat_dom_mono HaDe) as Hdm2.
  intros a Ha.
  assert (Hane : a <> x2) by (intros ->; exact (Hx2Θb' Ha)).
  assert (Ha1 : a `in` dom ((x2 ~ bd') ++ Θb'))
    by (simpl_env; clear - Ha; fsetdec).
  apply Hdm2 in Ha1. simpl_env in Ha1. simpl_env.
  clear - Ha1 Hane. fsetdec.
Qed.

Theorem a_pat_rel_e : forall m Θ0 P0 e Q Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}a ->
  lift_pat_concl m Θ0 P0 e Q Θ1.
Proof.
  intros m Θ0 P0 e Q Θ1 HD.
  induction HD as
    [ m0 Θa Θb P0a Pa Hsub
    | m0 Θa Θb P0a x A Qa Hb Hsub
    | m0 Θa Θb P0a x Ps Qa Hb Hsub
    | m0 Θa Θb P0a ea A Qa Hsub
    | Θa ea Qa Θb Hp IHp
    | x m0 Θa Θb Θc P0a Pa Q0 ea Qa Ξ Hne Hsp Hsuf Hxf Hp IHp
    | x m0 Θa Θb Θc Θd P0a Pa Q0 A ea Qa Ξ Hne Hsp Hchk Hsuf Hxf Hp IHp
    | x Θa Θb ea Qa Ξ Hsuf Hxf Hp IHp
    | x Θa Θb A ea Qa Ξ Hsuf Hxf Hp IHp
    | m0 Θa Θb Θc P0a Q0 Pa Qa e1 e2 Hp2 IHp2 Hp1 IHp1 ];
    intros S0 Θ0' P0' e' ρ V HrΘ HrP0 HrE Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfe Hmod.
  - (* AP-Unit *)
    inversion HrE; subst.
    assert (HcovS : ftvar_in_pskl P0' ∪ ftvar_in_pskl pskl_unit [<=] S0)
      by (simpl; clear - HcovP; simpl in HcovP; fsetdec).
    destruct (lift_pat_sub Hsub HrΘ HrP0 (rel_pskl__unit ρ V) Hagr Hinj Hfun
                Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovS Hwfp0
                (a_wf_pskl__unit Θa empty))
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_pat__unit; exact De | ].
    split; [ exact HrΘ1 | ]. split; [ exact Hagr1 | ].
    split; [ exact HrQ | ]. split; [ exact Hext | ]. exact Hdom1.
  - (* AP-Var, type-bound *)
    inversion HrE as [ | | x1 x2 Hax | | | | | ]; subst.
    destruct (@rel_aenv_binds_pin ρ V Θa Θ0' x x2 (abind_var_typ A)
                HrΘ Hfun Hb Hax) as (bd2 & Habd & Hb2).
    inversion Habd as [ | | | A1 A2 HrA | ]; subst.
    assert (HcovS : ftvar_in_pskl P0' ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] S0).
    { pose proof (@rel_pskl_ftv_r ρ V (ptyp_to_pskl A) (ptyp_to_pskl A2) HrA)
        as HA2.
      clear - HcovP HA2 Hcov. simpl in HcovP. fsetdec. }
    assert (HwfA : {{ Θa ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl;
          eapply a_wf_aenv_binds_var_typ_wf; [ exact Hwf | exact Hb ]).
    destruct (lift_pat_sub Hsub HrΘ HrP0 HrA Hagr Hinj Hfun
                Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovS Hwfp0 HwfA)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ eapply e_pat__var; [ exact Hb2 | exact De ] | ].
    split; [ exact HrΘ1 | ]. split; [ exact Hagr1 | ].
    split; [ exact HrQ | ]. split; [ exact Hext | ]. exact Hdom1.
  - (* AP-Var, skeleton-bound *)
    inversion HrE as [ | | x1 x2 Hax | | | | | ]; subst.
    destruct (@rel_aenv_binds_pin ρ V Θa Θ0' x x2 (abind_var_skl Ps)
                HrΘ Hfun Hb Hax) as (bd2 & Habd & Hb2).
    inversion Habd as [ | | | | Ps1 Ps2 HrPs ]; subst.
    assert (HcovS : ftvar_in_pskl P0' ∪ ftvar_in_pskl Ps2 [<=] S0).
    { pose proof (@rel_pskl_ftv_r ρ V Ps Ps2 HrPs) as HP2.
      clear - HcovP HP2 Hcov. simpl in HcovP. fsetdec. }
    assert (HwfP : {{ Θa ⨟ empty ⊢ₚₛ Ps }}a)
      by (eapply a_wf_aenv_binds_var_skl_wf; [ exact Hwf | exact Hb ]).
    destruct (lift_pat_sub Hsub HrΘ HrP0 HrPs Hagr Hinj Hfun
                Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovS Hwfp0 HwfP)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ eapply e_pat__var_skl; [ exact Hb2 | exact De ] | ].
    split; [ exact HrΘ1 | ]. split; [ exact Hagr1 | ].
    split; [ exact HrQ | ]. split; [ exact Hext | ]. exact Hdom1.
  - (* AP-Anno *)
    inversion HrE as [ | | | | | | eb1 eb2 A1 A2 HrEb HrA | ]; subst.
    inversion Hwfe as [ | | Θq eq Aq HwfAq Hwfeq | | | | ]; subst.
    assert (HcovS : ftvar_in_pskl P0' ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] S0)
      by (simpl in HcovP; rewrite ftvar_ptyp_to_pskl;
          clear - HcovP; fsetdec).
    assert (HwfA : {{ Θa ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfAq).
    destruct (lift_pat_sub Hsub HrΘ HrP0 HrA Hagr Hinj Hfun
                Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovS Hwfp0 HwfA)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_pat__anno; exact De | ].
    split; [ exact HrΘ1 | ]. split; [ exact Hagr1 | ].
    split; [ exact HrQ | ]. split; [ exact Hext | ]. exact Hdom1.
  - (* AP-Freeze *)
    inversion HrE as [ | | | | | | | eb1 eb2 HrEb ]; subst.
    inversion HrP0; subst.
    inversion Hwfe as [ | | | Θq eq Hwfeq | | | ]; subst.
    assert (HcovE : ftvar_in_pskl pskl_hole ∪ ftvar_in_exp eb2
                    ∪ fvar_in_exp eb2 [<=] S0)
      by (simpl in HcovP |- *; clear - HcovP; fsetdec).
    destruct (IHp S0 Θ0' pskl_hole eb2 ρ V HrΘ (rel_pskl__hole ρ V) HrEb
                Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovE
                (a_wf_pskl__hole Θa empty) Hwfeq a_sk_mode_compat__ti)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_pat__freeze; exact De | ].
    split; [ exact HrΘ1 | ]. split; [ exact Hagr1 | ].
    split; [ exact HrQ | ]. split; [ exact Hext | ]. exact Hdom1.
  - (* ⭐⭐ AP-Abs — the SK split is CONTEXT-IDENTITY ([a_split_sk_shape]),
       so the row is one CORE call per shape. *)
    destruct (a_split_sk_shape Hsp Hmod) as [HeqΘ Hshape]. subst Θb.
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb
                     | A1 A2 eb1 eb2 HrA HrEb
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb HrA | eb1 eb2 HrEb ]; subst.
    assert (Hfe : ftvar_in_exp ea [<=] dom Θa)
      by (pose proof (a_wf_exp_ftv_dom Hwfe) as Hd; simpl in Hd; exact Hd).
    pose proof Hxf as Hxf2. simpl_env in Hxf2.
    assert (HxΘa : x `notin` dom Θa) by (clear - Hxf2; fsetdec).
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfe HxΘa; fsetdec).
    assert (Hwfeo : {{ ((x ~ abind_var_skl Pa) ++ Θa) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a)
      by (apply a_wf_exp_weaken_cons; eapply a_wf_exp_abs_pick; exact Hwfe).
    destruct Hshape as [[EP0 [EP EQ0]] | EP0].
    + (* the ◇ shape: P0 = P = Q0 = ◇ *)
      subst P0a Pa Q0.
      inversion HrP0; subst.
      assert (Hmodc : a_sk_mode_compat (decr_mode m0) pskl_hole).
      { destruct (a_sk_mode_compat_hole_inv Hmod) as [-> | ->];
          [ apply a_sk_mode_compat__ti | congruence ]. }
      assert (HwfXc : {{ ⊢ ((x ~ abind_var_skl pskl_hole) ++ Θa) }}a)
        by (apply a_wf_aenv__var;
            [ exact HxΘa | apply a_wf_pskl__hole | exact Hwf ]).
      assert (HcovPc : ftvar_in_pskl pskl_hole ∪ ftvar_in_exp eb2
                       ∪ fvar_in_exp eb2 [<=] S0)
        by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
      assert (Hbdf0 : ftvar_in_abind (abind_var_skl pskl_hole) [<=] dom Θa)
        by (simpl; clear; fsetdec).
      assert (Hbdf0' : ftvar_in_abind (abind_var_skl pskl_hole) [<=] S0)
        by (simpl; clear; fsetdec).
      destruct (@lift_pat_abs_core (decr_mode m0) Θa pskl_hole ea Qa Ξ Θc x
                  (abind_var_skl pskl_hole)
                  Hp IHp Hsuf Hxf Hxe I Hbdf0 Hmodc
                  S0 Θ0' pskl_hole eb2 (abind_var_skl pskl_hole) ρ V
                  HrΘ (rel_pskl__hole ρ V) HrEb
                  (rel_abind__var_skl (rel_pskl__hole ρ V)) I Hbdf0'
                  Hagr Hinj Hfun HwfXc
                  (a_wf_pskl__hole Θa empty) Hwfeo Huq2p Hftv2 Hscp Hblk
                  HdΘ Hcov HcovPc)
        as (S1 & x2 & ρe & Ξ2 & Θc2' & Q' & Hx2S0 & De & HsufΞ2 & HrF
            & HagrF & HrQ' & HextF & HdomF & Hdm2).
      exists S1, ρe, (Ξ2 ++ Θc2'), (pskl_arrow pskl_hole Q').
      split.
      { eapply e_pat__abs;
          [ exact Hne | apply e_split__hole | exact HsufΞ2
          | exact Hx2S0 | exact De ]. }
      split; [ exact HrF | ].
      split; [ exact HagrF | ].
      split; [ constructor; [ apply rel_pskl__hole | exact HrQ' ] | ].
      split; [ exact HextF | ]. exact HdomF.
    + (* the ARROW shape: P0 = P → Q0 *)
      subst P0a.
      inversion HrP0 as [ | n0 | u0 v0 Hu0 | B1 B2 Pa' Q0c' HrPa HrQ0c
                        | B3 B4 Hu1 | | B5 B6 Hu2 ]; subst.
      inversion Hwfp0 as [ Θx Δx | Θx Δx αx Hbx | Θx Δx Xa Xb HwfPa HwfQ0a
                         | Lx Θx Δx Xp Hallx | Θx Δx
                         | Θx Δx Xp Hgx Hwix ]; subst.
      destruct (a_sk_mode_compat_arrow_inv Hmod) as (m'' & Em & Hmodc0).
      subst m0.
      assert (Hmodc : a_sk_mode_compat (decr_mode (mode_fn m'')) Q0)
        by (simpl; exact Hmodc0).
      assert (HbdfPa : ftvar_in_abind (abind_var_skl Pa) [<=] dom Θa).
      { simpl. intros z Hz.
        apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds HwfPa Hz). }
      assert (HwfXc : {{ ⊢ ((x ~ abind_var_skl Pa) ++ Θa) }}a)
        by (apply a_wf_aenv__var; [ exact HxΘa | exact HwfPa | exact Hwf ]).
      assert (Hbd'f : ftvar_in_abind (abind_var_skl Pa') [<=] S0)
        by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
      assert (HcovPc : ftvar_in_pskl Q0c' ∪ ftvar_in_exp eb2
                       ∪ fvar_in_exp eb2 [<=] S0)
        by (simpl in HcovP; clear - HcovP; fsetdec).
      destruct (@lift_pat_abs_core (decr_mode (mode_fn m'')) Θa Q0 ea Qa Ξ Θc
                  x (abind_var_skl Pa)
                  Hp IHp Hsuf Hxf Hxe I HbdfPa Hmodc
                  S0 Θ0' Q0c' eb2 (abind_var_skl Pa') ρ V
                  HrΘ HrQ0c HrEb
                  (rel_abind__var_skl HrPa) I Hbd'f
                  Hagr Hinj Hfun HwfXc HwfQ0a Hwfeo Huq2p Hftv2 Hscp Hblk
                  HdΘ Hcov HcovPc)
        as (S1 & x2 & ρe & Ξ2 & Θc2' & Q' & Hx2S0 & De & HsufΞ2 & HrF
            & HagrF & HrQ' & HextF & HdomF & Hdm2).
      exists S1, ρe, (Ξ2 ++ Θc2'), (pskl_arrow Pa' Q').
      split.
      { eapply e_pat__abs;
          [ exact Hne | apply e_split__arrow | exact HsufΞ2
          | exact Hx2S0 | exact De ]. }
      split; [ exact HrF | ].
      split; [ exact HagrF | ].
      split.
      { constructor; [ | exact HrQ' ].
        eapply rel_pskl_mono;
          [ exact HrPa | intros u v Hu; apply in_or_app; right; exact Hu
          | intros u Hu; exact Hu ]. }
      split; [ exact HextF | ]. exact HdomF.
  - (* ⭐⭐ AP-AbsAnno — the consis-chk between the (identity) split and the
       body: [lift_consis_nil], widen, the CORE, then [rel_ext_app] — the
       AP-App composition one binder in. *)
    destruct (a_split_sk_shape Hsp Hmod) as [HeqΘ Hshape]. subst Θb.
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb
                     | A1 A2 eb1 eb2 HrA HrEb
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb HrA | eb1 eb2 HrEb ]; subst.
    inversion Hwfe as [ | | | | | Lw Θw Aw ew HwfA Hwfb | ]; subst.
    destruct Hchk as [Qc Hcc].
    (* ---- the shapes' shared data ---- *)
    assert (Hfe : ftvar_in_exp ea ∪ ftvar_in_ptyp A [<=] dom Θa)
      by (pose proof (a_wf_exp_ftv_dom Hwfe) as Hd; simpl in Hd;
          clear - Hd; fsetdec).
    assert (HwfcA : {{ Θa ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfA).
    assert (HrAp : rel_pskl ρ V (ptyp_to_pskl A) (ptyp_to_pskl A2))
      by (exact HrA).
    assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hdmc : dom Θa [<=] dom Θc) by (exact (auc_dom_mono_consis Hcc)).
    pose proof (a_pat_dom_mono Hp) as Hdmb.
    pose proof Hxf as Hxf2. simpl_env in Hxf2.
    assert (HxΘc : x `notin` dom Θc) by (clear - Hxf2; fsetdec).
    assert (HxΘa : x `notin` dom Θa) by (clear - HxΘc Hdmc; fsetdec).
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfe HxΘa; fsetdec).
    (* the CHK output reaches the conclusion's output: the body's dom-mono
       with the term entry stripped *)
    assert (Hdmout : dom Θc [<=] dom (Ξ ++ Θd)).
    { intros a Ha.
      assert (Hax : a <> x) by (intros ->; exact (HxΘc Ha)).
      assert (Ha1 : a `in` dom ((x ~ abind_var_typ A) ++ Θc))
        by (simpl_env; clear - Ha; fsetdec).
      apply Hdmb in Ha1. simpl_env in Ha1. simpl_env.
      clear - Ha1 Hax. fsetdec. }
    (* ---- shape data: the split's two outputs ---- *)
    assert (Hpieces :
      {{ Θa ⨟ empty ⊢ₚₛ Pa }}a /\ {{ Θa ⨟ empty ⊢ₚₛ Q0 }}a /\
      a_sk_mode_compat (decr_mode m0) Q0 /\
      exists Pa' Q0',
        rel_pskl ρ V Pa Pa' /\ rel_pskl ρ V Q0 Q0' /\
        ftvar_in_pskl Pa' ∪ ftvar_in_pskl Q0' [<=] S0 /\
        {{ S0 ↝ S0 ⊨ Θ0' ⊲ P0' ▹ Pa' ⇢ Q0' ⊣ Θ0' }}e).
    { destruct Hshape as [[EP0 [EP EQ0]] | EP0].
      - subst P0a Pa Q0. inversion HrP0; subst.
        split; [ apply a_wf_pskl__hole | ].
        split; [ apply a_wf_pskl__hole | ].
        split.
        { destruct (a_sk_mode_compat_hole_inv Hmod) as [-> | ->];
            [ apply a_sk_mode_compat__ti | congruence ]. }
        exists pskl_hole, pskl_hole.
        split; [ apply rel_pskl__hole | ].
        split; [ apply rel_pskl__hole | ].
        split; [ simpl; clear; fsetdec | ].
        apply e_split__hole.
      - subst P0a.
        inversion HrP0 as [ | n0 | u0 v0 Hu0 | B1 B2 Pa' Q0c' HrPa HrQ0c
                          | B3 B4 Hu1 | | B5 B6 Hu2 ]; subst.
        inversion Hwfp0 as [ Θx Δx | Θx Δx αx Hbx | Θx Δx Xa Xb HwfPaa HwfQ0a
                           | Lx Θx Δx Xp Hallx | Θx Δx
                           | Θx Δx Xp Hgx Hwix ]; subst.
        destruct (a_sk_mode_compat_arrow_inv Hmod) as (m'' & Em & Hmodc0).
        subst m0.
        split; [ exact HwfPaa | ].
        split; [ exact HwfQ0a | ].
        split; [ simpl; exact Hmodc0 | ].
        exists Pa', Q0c'.
        split; [ exact HrPa | ].
        split; [ exact HrQ0c | ].
        split; [ simpl in HcovP; clear - HcovP; fsetdec | ].
        apply e_split__arrow. }
    destruct Hpieces as (HwfPa & HwfQ0a & Hmodc
                         & Pa' & Q0' & HrPa & HrQ0c & HftPQ & Dsp).
    (* ---- the chk lift ---- *)
    assert (Hblk1 : forall a, a `in` dom Θc -> a `notin` dom Θa ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk;
          [ apply Hdmout; exact Ha | exact Hn ]).
    assert (HcovC : ftvar_in_pskl Pa' ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] S0).
    { simpl in HcovP. rewrite ftvar_ptyp_to_pskl.
      clear - HcovP HftPQ. fsetdec. }
    destruct (lift_consis_nil Hcc HrΘ HrPa HrAp Hagr Hinj Hfun Hwf Huq2p
                Hftv2 Hscp Hblk1 HdΘ Hcov HcovC HwfPa HwfcA)
      as (S1c & ρe1 & Θc' & Qc' & Dchk & HrΘc & Hagrc & HrQcU & Hext1
          & Hdom1).
    pose proof (e_consis_supply_grows Dchk) as Hgr1.
    (* ---- side 2's package at the chk's output ---- *)
    assert (HdΘ1 : dom Θc' [<=] S1c).
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ _ _ _ Dchk) as Hup.
      clear - Hup HdΘ Hgr1. fsetdec. }
    assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl Pa'
                    ∪ ftvar_in_pskl (ptyp_to_pskl A2) [<=] S0)
      by (clear - Hftv2 HcovC; fsetdec).
    assert (Hftv1 : ftvar_in_aenv Θc' [<=] S1c)
      by (eapply (proj2 (proj2 e_assign_unify_consis_ctx_ftvar));
          [ exact Dchk | exact HcovE ]).
    assert (HcovE2 : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl Pa'
                     ∪ ftvar_in_pskl (ptyp_to_pskl A2) ∪ empty ∪ empty
                     [<=] S0)
      by (clear - HcovE; fsetdec).
    assert (Huq1' : uniq Θc').
    { pose proof (e_consis_sound Dchk Huq2p HcovE2) as Ha1.
      exact ((proj2 (proj2 a_assign_unify_consis_uniq)) _ _ _ _ _ _ _ Ha1
               Huq2p). }
    (* ---- side 1's package at the chk's output ---- *)
    destruct (a_consis_isub_wf_nil Hcc Hwf HwfPa HwfcA) as [Hle01 HwfΘc].
    assert (Hd1s : dom Θc [<=] ftvar_in_aenv Θc)
      by (apply dom_subset_ftvar_in_aenv).
    assert (Hscp1 : V [<=] ftvar_in_aenv Θc)
      by (clear - Hscp Hsc0 Hdmc Hd1s; fsetdec).
    assert (HwfAc : a_wf_ptyp Θc A)
      by (eapply a_wf_ptyp_isub; [ exact HwfA | exact Hle01 ]).
    assert (HwfXc : {{ ⊢ ((x ~ abind_var_typ A) ++ Θc) }}a)
      by (apply a_wf_aenv__var_typ; [ exact HxΘc | exact HwfAc | exact HwfΘc ]).
    assert (HbdfA : ftvar_in_abind (abind_var_typ A) [<=] dom Θc)
      by (simpl; pose proof (a_wf_ptyp_ftv_dom HwfAc) as Hd; exact Hd).
    assert (HwfQ0c : {{ Θc ⨟ empty ⊢ₚₛ Q0 }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact HwfQ0a ]).
    assert (Hwfeo : {{ ((x ~ abind_var_typ A) ++ Θc) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a)
      by (apply a_wf_exp_weaken_cons; eapply a_wf_exp_abs_anno_pick;
          eapply a_wf_exp_isub; [ exact Hwfe | exact Hle01 ]).
    (* ---- the relation, widened by the chk's pairs ---- *)
    assert (Hinj1 : rel_inj (ρe1 ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (HVdom0 : V [<=] dom Θa) by (clear - Hscp Hsc0; fsetdec).
    assert (Hfun1 : rel_fun (ρe1 ++ ρ) V (dom Θc)).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hext1 | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; exact (Hblk1 a Ha Hn)
        | intros a Ha Hn; clear - HVdom0 Hn; fsetdec ]. }
    assert (HrEb' : rel_exp (ρe1 ++ ρ) V ea eb2)
      by (eapply rel_exp_mono;
          [ exact HrEb | intros u v Hu; apply in_or_app; right; exact Hu
          | intros u Hu; exact Hu ]).
    assert (HrA' : rel_pskl (ρe1 ++ ρ) V (ptyp_to_pskl A) (ptyp_to_pskl A2))
      by (apply rel_pskl_widen; exact HrAp).
    assert (HrQ0w : rel_pskl (ρe1 ++ ρ) V Q0 Q0')
      by (apply rel_pskl_widen; exact HrQ0c).
    assert (Hc1r : cols_r ρe1 [<=] S1c).
    { intros y Hy. destruct (cols_r_in_inv _ _ Hy) as (a & Hin).
      destruct (Hdom1 _ _ Hin) as [_ Hd2]. clear - Hd2 HdΘ1. fsetdec. }
    assert (Hcov1 : V ∪ cols_r (ρe1 ++ ρ) [<=] S1c)
      by (rewrite cols_r_app; clear - Hcov Hc1r Hgr1; fsetdec).
    assert (Hblk2 : forall a, a `in` dom (Ξ ++ Θd) -> a `notin` dom Θc ->
                    a `notin` cols_l (ρe1 ++ ρ)).
    { intros a Ha Hn. rewrite cols_l_app.
      assert (Hc1 : a `notin` cols_l ρe1).
      { intros Hy. destruct (cols_l_in_inv _ _ Hy) as (y & Hin).
        destruct (Hdom1 _ _ Hin) as [Hd1 _]. contradiction. }
      assert (Hc2 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn Hdmc; fsetdec ]).
      clear - Hc1 Hc2. fsetdec. }
    assert (Hbd'fc : ftvar_in_abind (abind_var_typ A2) [<=] S1c).
    { simpl. rewrite ftvar_ptyp_to_pskl in HcovC.
      clear - HcovC Hgr1. fsetdec. }
    assert (HcovPc : ftvar_in_pskl Q0' ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S1c)
      by (simpl in HcovP; clear - HcovP HftPQ Hgr1; fsetdec).
    (* ---- the CORE ---- *)
    destruct (@lift_pat_abs_core (decr_mode m0) Θc Q0 ea Qa Ξ Θd x
                (abind_var_typ A)
                Hp IHp Hsuf Hxf Hxe I HbdfA Hmodc
                S1c Θc' Q0' eb2 (abind_var_typ A2) (ρe1 ++ ρ) V
                HrΘc HrQ0w HrEb'
                (rel_abind__var_typ HrA') I Hbd'fc
                Hagrc Hinj1 Hfun1 HwfXc HwfQ0c Hwfeo Huq1' Hftv1 Hscp1
                Hblk2 HdΘ1 Hcov1 HcovPc)
      as (S1 & x2 & ρe2 & Ξ2 & Θc2' & Q' & Hx2S1c & De & HsufΞ2 & HrF
          & HagrF & HrQ' & HextF & HdomF & Hdm2).
    (* ---- the answer ---- *)
    exists S1, (ρe2 ++ ρe1), (Ξ2 ++ Θc2'),
      (pskl_arrow (ptyp_to_pskl A2) Q').
    split.
    { eapply e_pat__abs_anno;
        [ exact Hne | exact Dsp | exists Qc'; exact Dchk | exact HsufΞ2
        | exact Hx2S1c | exact De ]. }
    rewrite app_assoc.
    split; [ exact HrF | ].
    split; [ exact HagrF | ].
    split.
    { constructor; [ | exact HrQ' ].
      eapply rel_pskl_mono;
        [ exact HrA' | intros u v Hu; apply in_or_app; right; exact Hu
        | intros u Hu; exact Hu ]. }
    split.
    { eapply rel_ext_app;
        [ exact Hext1 | exact HextF
        | clear - Hsc0 Hdmc Hd1s; fsetdec
        | exact Hgr1
        | intros a b Hin; destruct (Hdom1 _ _ Hin) as [Hd1 Hd2];
          split; [ clear - Hd1 Hd1s; fsetdec | clear - Hd2 HdΘ1; fsetdec ] ]. }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (HdomF _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; [ apply Hdmout; exact Hd1 | apply Hdm2; exact Hd2 ].
  - (* ⭐ AP-AbsCheck — no prelude at all: ONE core call *)
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb
                     | A1 A2 eb1 eb2 HrA HrEb
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb HrA | eb1 eb2 HrEb ]; subst.
    inversion HrP0; subst.
    assert (Hfe : ftvar_in_exp ea [<=] dom Θa)
      by (pose proof (a_wf_exp_ftv_dom Hwfe) as Hd; simpl in Hd; exact Hd).
    pose proof Hxf as Hxf2. simpl_env in Hxf2.
    assert (HxΘa : x `notin` dom Θa) by (clear - Hxf2; fsetdec).
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfe HxΘa; fsetdec).
    assert (Hwfeo : {{ ((x ~ abind_var_skl pskl_hole) ++ Θa) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a)
      by (apply a_wf_exp_weaken_cons; eapply a_wf_exp_abs_pick; exact Hwfe).
    assert (HwfXc : {{ ⊢ ((x ~ abind_var_skl pskl_hole) ++ Θa) }}a)
      by (apply a_wf_aenv__var;
          [ exact HxΘa | apply a_wf_pskl__hole | exact Hwf ]).
    assert (HcovPc : ftvar_in_pskl pskl_hole ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S0)
      by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hbdf0 : ftvar_in_abind (abind_var_skl pskl_hole) [<=] dom Θa)
      by (simpl; clear; fsetdec).
    assert (Hbdf0' : ftvar_in_abind (abind_var_skl pskl_hole) [<=] S0)
      by (simpl; clear; fsetdec).
    destruct (@lift_pat_abs_core mode_tc Θa pskl_hole ea Qa Ξ Θb x
                (abind_var_skl pskl_hole)
                Hp IHp Hsuf Hxf Hxe I Hbdf0 a_sk_mode_compat__tc
                S0 Θ0' pskl_hole eb2 (abind_var_skl pskl_hole) ρ V
                HrΘ (rel_pskl__hole ρ V) HrEb
                (rel_abind__var_skl (rel_pskl__hole ρ V)) I Hbdf0'
                Hagr Hinj Hfun HwfXc
                (a_wf_pskl__hole Θa empty) Hwfeo Huq2p Hftv2 Hscp Hblk
                HdΘ Hcov HcovPc)
      as (S1 & x2 & ρe & Ξ2 & Θc2' & Q' & Hx2S0 & De & HsufΞ2 & HrF
          & HagrF & HrQ' & HextF & HdomF & Hdm2).
    exists S1, ρe, (Ξ2 ++ Θc2'),
      (pskl_tophole (pskl_arrow pskl_hole Q')).
    split.
    { eapply e_pat__abs_check;
        [ exact HsufΞ2 | exact Hx2S0 | exact De ]. }
    split; [ exact HrF | ].
    split; [ exact HagrF | ].
    split.
    { constructor. constructor; [ apply rel_pskl__hole | exact HrQ' ]. }
    split; [ exact HextF | ]. exact HdomF.
  - (* ⭐ AP-AbsAnnoCheck — the annotated twin, same shape *)
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb
                     | A1 A2 eb1 eb2 HrA HrEb
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb HrA | eb1 eb2 HrEb ]; subst.
    inversion HrP0; subst.
    inversion Hwfe as [ | | | | | Lw Θw Aw ew HwfA Hwfb | ]; subst.
    assert (Hfe : ftvar_in_exp ea [<=] dom Θa)
      by (pose proof (a_wf_exp_ftv_dom Hwfe) as Hd; simpl in Hd;
          clear - Hd; fsetdec).
    pose proof Hxf as Hxf2. simpl_env in Hxf2.
    assert (HxΘa : x `notin` dom Θa) by (clear - Hxf2; fsetdec).
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfe HxΘa; fsetdec).
    assert (Hwfeo : {{ ((x ~ abind_var_typ A) ++ Θa) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a)
      by (apply a_wf_exp_weaken_cons; eapply a_wf_exp_abs_anno_pick;
          exact Hwfe).
    assert (HwfXc : {{ ⊢ ((x ~ abind_var_typ A) ++ Θa) }}a)
      by (apply a_wf_aenv__var_typ; [ exact HxΘa | exact HwfA | exact Hwf ]).
    assert (HbdfA : ftvar_in_abind (abind_var_typ A) [<=] dom Θa)
      by (simpl; apply a_wf_ptyp_ftv_dom; exact HwfA).
    assert (Hbd'f : ftvar_in_abind (abind_var_typ A2) [<=] S0).
    { simpl. simpl in HcovP.
      pose proof (@rel_pskl_ftv_r ρ V (ptyp_to_pskl A) (ptyp_to_pskl A2) HrA)
        as Hfr.
      rewrite ftvar_ptyp_to_pskl in Hfr. clear - Hfr Hcov. fsetdec. }
    assert (HcovPc : ftvar_in_pskl pskl_hole ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S0)
      by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
    destruct (@lift_pat_abs_core mode_tc Θa pskl_hole ea Qa Ξ Θb x
                (abind_var_typ A)
                Hp IHp Hsuf Hxf Hxe I HbdfA a_sk_mode_compat__tc
                S0 Θ0' pskl_hole eb2 (abind_var_typ A2) ρ V
                HrΘ (rel_pskl__hole ρ V) HrEb
                (rel_abind__var_typ HrA) I Hbd'f
                Hagr Hinj Hfun HwfXc
                (a_wf_pskl__hole Θa empty) Hwfeo Huq2p Hftv2 Hscp Hblk
                HdΘ Hcov HcovPc)
      as (S1 & x2 & ρe & Ξ2 & Θc2' & Q' & Hx2S0 & De & HsufΞ2 & HrF
          & HagrF & HrQ' & HextF & HdomF & Hdm2).
    exists S1, ρe, (Ξ2 ++ Θc2'),
      (pskl_tophole (pskl_arrow (ptyp_to_pskl A2) Q')).
    split.
    { eapply e_pat__abs_anno_check;
        [ exact HsufΞ2 | exact Hx2S0 | exact De ]. }
    split; [ exact HrF | ].
    split; [ exact HagrF | ].
    split.
    { constructor. constructor; [ | exact HrQ' ].
      eapply rel_pskl_mono;
        [ exact HrA | intros u v Hu; apply in_or_app; right; exact Hu
        | intros u Hu; exact Hu ]. }
    split; [ exact HextF | ]. exact HdomF.
  - (* ⭐ AP-App — the S-Arrow template one judgement up: the argument at
       (TC, ◇), then the function at ITS output, [rel_ext_app] composing
       the two extensions. *)
    inversion HrE as [ | | x1 y1 Hat | e1a e2a HrEa
                     | A1 A2 e1a e2a HrA HrEa
                     | a1 a2 b1 b2 HrE1 HrE2
                     | e1a e2a A1 A2 HrEa HrA | e1a e2a HrEa ]; subst.
    destruct (a_wf_exp_app_inv Hwfe) as [Hwfe1 Hwfe2].
    assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hdm0 : dom Θa [<=] dom Θb) by (exact (a_pat_dom_mono Hp2)).
    assert (Hdm1 : dom Θb [<=] dom Θc) by (exact (a_pat_dom_mono Hp1)).
    assert (Hblk1 : forall a, a `in` dom Θb -> a `notin` dom Θa ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk; [ clear - Ha Hdm1; fsetdec | exact Hn ]).
    assert (HcovP1 : ftvar_in_pskl pskl_hole ∪ ftvar_in_exp b2
                     ∪ fvar_in_exp b2 [<=] S0)
      by (simpl in HcovP |- *; clear - HcovP; fsetdec).
    destruct (IHp2 S0 Θ0' pskl_hole b2 ρ V HrΘ (rel_pskl__hole ρ V) HrE2
                Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk1 HdΘ Hcov HcovP1
                (a_wf_pskl__hole Θa empty) Hwfe2 a_sk_mode_compat__tc)
      as (S1 & ρe1 & Θb' & P0c' & D2e & HrΘ1 & Hagr1 & HrP0c & Hext1 & Hdom1).
    pose proof (e_pat_supply_grows D2e) as Hgr1.
    (* ---- side 2's package at the first call's output ---- *)
    assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl pskl_hole
                    ∪ fvar_in_exp b2 ∪ ftvar_in_exp b2 [<=] S0)
      by (simpl; simpl in HcovP; clear - Hftv2 HcovP; fsetdec).
    destruct (e_pat_sound D2e Huq2p HcovE) as (Ha2p & Huq1' & Hftv1 & HftQ1).
    assert (HdΘ1 : dom Θb' [<=] S1)
      by (pose proof (dom_subset_ftvar_in_aenv Θb') as Hd;
          clear - Hd Hftv1; fsetdec).
    (* ---- side 1's package at the first call's output ---- *)
    destruct (a_pat_sound Hp2 Hwf (a_wf_pskl__hole Θa empty)
                a_sk_mode_compat__tc Hwfe2) as [Hle01 [HwfΘb _]].
    assert (Hd1s : dom Θb [<=] ftvar_in_aenv Θb)
      by (apply dom_subset_ftvar_in_aenv).
    assert (Hscp1 : V [<=] ftvar_in_aenv Θb)
      by (clear - Hscp Hsc0 Hdm0 Hd1s; fsetdec).
    assert (HwfP0a : {{ Θb ⨟ empty ⊢ₚₛ P0a }}a)
      by (eapply a_pat_output_wf;
          [ exact Hp2 | exact Hwf | apply a_wf_pskl__hole
          | exact a_sk_mode_compat__tc | exact Hwfe2 ]).
    assert (HwfQ0b : {{ Θb ⨟ empty ⊢ₚₛ Q0 }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hwfp0 ]).
    assert (Hwfarr : {{ Θb ⨟ empty ⊢ₚₛ (pskl_arrow P0a Q0) }}a)
      by (apply a_wf_pskl__arrow; [ exact HwfP0a | exact HwfQ0b ]).
    assert (Hwfe1b : {{ Θb ⊢ᵉ e1 }}a)
      by (eapply a_wf_exp_isub; [ exact Hwfe1 | exact Hle01 ]).
    (* ---- the relation, widened by the first call's new pairs ---- *)
    assert (Hinj1 : rel_inj (ρe1 ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (HVdom0 : V [<=] dom Θa) by (clear - Hscp Hsc0; fsetdec).
    assert (Hfun1 : rel_fun (ρe1 ++ ρ) V (dom Θb)).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hext1 | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; exact (Hblk1 a Ha Hn)
        | intros a Ha Hn; clear - HVdom0 Hn; fsetdec ]. }
    assert (HrQ0' : rel_pskl (ρe1 ++ ρ) V Q0 P0')
      by (apply rel_pskl_widen; exact HrP0).
    assert (Hrarr : rel_pskl (ρe1 ++ ρ) V (pskl_arrow P0a Q0)
                      (pskl_arrow P0c' P0'))
      by (constructor; [ exact HrP0c | exact HrQ0' ]).
    assert (HrE1' : rel_exp (ρe1 ++ ρ) V e1 b1)
      by (eapply rel_exp_mono;
          [ exact HrE1 | intros u v Hu; apply in_or_app; right; exact Hu
          | intros u Hu; exact Hu ]).
    assert (Hc1r : cols_r ρe1 [<=] S1).
    { intros y Hy. destruct (cols_r_in_inv _ _ Hy) as (a & Hin).
      destruct (Hdom1 _ _ Hin) as [_ Hd2]. clear - Hd2 HdΘ1. fsetdec. }
    assert (Hcov1 : V ∪ cols_r (ρe1 ++ ρ) [<=] S1)
      by (rewrite cols_r_app; clear - Hcov Hc1r Hgr1; fsetdec).
    assert (Hblk2 : forall a, a `in` dom Θc -> a `notin` dom Θb ->
                    a `notin` cols_l (ρe1 ++ ρ)).
    { intros a Ha Hn. rewrite cols_l_app.
      assert (Hc1 : a `notin` cols_l ρe1).
      { intros Hy. destruct (cols_l_in_inv _ _ Hy) as (y & Hin).
        destruct (Hdom1 _ _ Hin) as [Hd1 _]. contradiction. }
      assert (Hc2 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn Hdm0; fsetdec ]).
      clear - Hc1 Hc2. fsetdec. }
    assert (HcovP2 : ftvar_in_pskl (pskl_arrow P0c' P0')
                     ∪ ftvar_in_exp b1 ∪ fvar_in_exp b1 [<=] S1).
    { pose proof (@rel_pskl_ftv_r (ρe1 ++ ρ) V P0a P0c' HrP0c) as HfQ.
      rewrite cols_r_app in HfQ.
      simpl. simpl in HcovP.
      clear - HfQ HcovP Hcov Hc1r Hgr1. fsetdec. }
    destruct (IHp1 S1 Θb' (pskl_arrow P0c' P0') b1 (ρe1 ++ ρ) V
                HrΘ1 Hrarr HrE1' Hagr1 Hinj1 Hfun1 HwfΘb Huq1' Hftv1
                Hscp1 Hblk2 HdΘ1 Hcov1 HcovP2 Hwfarr Hwfe1b
                (a_sk_mode_compat__fn P0a Hmod))
      as (S2 & ρe2 & Θc' & Qc' & D1e & HrΘ2 & Hagr2 & HrQ2 & Hext2 & Hdom2).
    inversion HrQ2 as [ | | u5 v5 Hu5 | C1 C2 Pa' Qa' HrPa' HrQa'
                      | C3 C4 Hu6 | | C5 C6 Hu7 ]; subst.
    (* ---- side 2's dom mono across the second call ---- *)
    assert (HcovE3 : ftvar_in_aenv Θb' ∪ ftvar_in_pskl (pskl_arrow P0c' P0')
                     ∪ fvar_in_exp b1 ∪ ftvar_in_exp b1 [<=] S1)
      by (clear - Hftv1 HcovP2; fsetdec).
    assert (Hdm2' : dom Θb' [<=] dom Θc').
    { destruct (e_pat_sound D1e Huq1' HcovE3) as (Ha1p & _).
      exact (a_pat_dom_mono Ha1p). }
    (* ---- the answer ---- *)
    exists S2, (ρe2 ++ ρe1), Θc', Qa'.
    split; [ eapply e_pat__app; [ exact D2e | exact D1e ] | ].
    rewrite app_assoc.
    split; [ exact HrΘ2 | ].
    split; [ exact Hagr2 | ].
    split; [ exact HrQa' | ].
    split.
    { eapply rel_ext_app;
        [ exact Hext1 | exact Hext2
        | clear - Hsc0 Hdm0 Hd1s; fsetdec
        | exact Hgr1
        | intros a b Hin; destruct (Hdom1 _ _ Hin) as [Hd1 Hd2];
          split; [ clear - Hd1 Hd1s; fsetdec | clear - Hd2 HdΘ1; fsetdec ] ]. }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hdom2 _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; [ clear - Hd1 Hdm1; fsetdec | clear - Hd2 Hdm2'; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §13 — THE a_typing RUNG — LIVES IN [prop_lift_typing.v]               *)
(*                                                                        *)
(*  Split out 2026-08-22: it is 3.7k of this file's 12.8k lines, it is a  *)
(*  clean PREFIX boundary (nothing above depends on it), and keeping it   *)
(*  here made every edit to the typing rung re-check the nine rungs below *)
(*  (docs/REPORT-interface-proofpath-audit.md §B4).                       *)
(* ===================================================================== *)
