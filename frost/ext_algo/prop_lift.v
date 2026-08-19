(** ext_algo — ⛔ THE CAMPAIGN'S LAST DEBT: the LIFT, [a_*] ⟹ [e_*].

    §8c.23 left exactly one link open.  Runner completeness (levels 1–8) is
    stated over the SUPPLY-THREADED relations, so the decidability corollary's
    NEGATIVE branch refutes [e_typing] and not [algo/]'s own [a_typing].  What
    closes the gap — and with it makes the extracted program SOUND AND
    COMPLETE for the paper's DECLARATIVE system — is the converse of the
    bridge, composed with what already exists:

      d_ ⟹ a_typing        a_typing_complete_decl_*   (README §III)   ✅
      a_typing ⟹ e_typing  THIS FILE                                  ⛔
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

    ⚙ At the guess the conclusion is EXISTENTIAL up to a CHAIN: the [e_]
    derivation's outputs are [swaps_*] images of the [a_] derivation's.

    ⛔⛔ AND THAT CURRENCY DIES ONE LEVEL UP — read §3 before writing any
    block above §2.  A chain is a FUNCTION on atoms, and above the guess
    the [a_] rules LEAK binders into their outputs, so one left atom can
    need two right images.  Everything from §3 on is therefore stated over
    prop_solve_det.v §1's deliberately RELATIONAL [rel_pskl] / [rel_a_cstrs]
    at a pair list ρ that GROWS — which is also the currency §8c.9's
    transport layer (prop_solve_rel.v §3-§7) already built a → a, so those
    are what §4-§7 are copied from.

    §1  the [close] rename fact the ∀ rows need
    §2  ⭐ [guess^TY] and its sort wrapper, CHAIN currency — the SCOUT
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

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_coercions.
Require Import src.frost.prop_tag.
Require Import src.frost.prop_basic.
Require Import src.frost.prop_ln.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.sub.prop_looksub.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.prop_guess.
Require Import src.frost.ext_algo.prop_termination.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.prop_solve.
Require Import src.frost.ext_algo.prop_solve_det.
Require Import src.frost.ext_algo.prop_solve_rel.
(* ⚙ for the [swaps_*] kit levels 7/8 added — [swaps_pskl_ptyp_to_pskl] here,
   and [swaps_ptyp_open] / [ptyp_to_pskl_inj] for the blocks above. *)
Require Import src.frost.ext_algo.prop_typing_complete.

Set Implicit Arguments.

Open Scope frost_a_scope.
Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  THE [close] RENAME FACT                                           *)
(*                                                                        *)
(*  ⭐ It is what makes the ∀ rows SHORTER than they look: [close] does not *)
(*  remember WHICH atom it abstracted, so the transposition that moves the *)
(*  [a_] rule's witness onto a supply-fresh one does NOT appear in the     *)
(*  conclusion's chain at all.                                            *)
(*                                                                        *)
(*  ⚙ Proved through lngen's round trips rather than by a hand induction:  *)
(*  a swap at a FRESH target IS a substitution, a substitution IS an       *)
(*  [open] of a [close], and [close] of that [open] is the identity        *)
(*  because [close]'s own free variables miss the fresh atom.              *)
(* ===================================================================== *)

Lemma close_ptyp_wrt_ptyp_rename : forall A β β',
  β' `notin` ftvar_in_ptyp A ->
  close_ptyp_wrt_ptyp β' (swap_ptyp β β' A) = close_ptyp_wrt_ptyp β A.
Proof.
  intros A β β' Hβ'.
  rewrite (swap_ptyp_as_subst β β' A Hβ').
  rewrite subst_ptyp_in_ptyp_spec.
  apply close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp.
  rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp. clear - Hβ'. fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  ⭐ [guess^TY] LIFTS — THE SCOUT                                    *)
(*                                                                        *)
(*  [a_guess_mono] carries all three hard shapes: an INVENTION row (□), a  *)
(*  BINDER row (∀), and an ARROW row whose two halves the [a_] side does   *)
(*  NOT thread.  Getting it right settles the shape of the motive for      *)
(*  every block above it.                                                 *)
(*                                                                        *)
(*  ⚠️ TWO PREMISES, AND NEITHER IS DECORATION (§8c.24).                   *)
(*                                                                        *)
(*  [uniq Ξ] — [a_guess_mono__arrow] runs BOTH halves at the SAME [Θ], so  *)
(*  the two blocks may COLLIDE (which is exactly why [AT-Abs] carries      *)
(*  [uniq (αs ++ Θ1)]), while [e_guess_mono] threads and its block is      *)
(*  [uniq] outright.  No single chain sends a colliding block to a [uniq]  *)
(*  one.  The only consumer already has the premise.                      *)
(*                                                                        *)
(*  [dom Ξ ∩ (S0 ∪ L) [=] empty] — the [a_] side's invented atoms avoid    *)
(*  [ftvar_in_aenv Θ] and NOTHING ELSE, while every step of the arrow row  *)
(*  that fixes one premise's data by the other's chain needs them off the  *)
(*  supply.  The consumer discharges it by PRE-FRESHENING.                *)
(*                                                                        *)
(*  ⭐ THE MOTIVE CARRIES TWO AVOID-SETS, and they do different jobs.      *)
(*  [L] is dodged by the chain's TARGETS and by the IMAGE BLOCK — that is  *)
(*  what lets one premise's answer be fixed by the other's chain.  [K] is  *)
(*  dodged by the OUTPUT SUPPLY — that is what lets the arrow row's SECOND *)
(*  call know the right-hand block is still off the threaded supply.  ⚙ A  *)
(*  single set cannot do both: the image block LIVES in the output supply, *)
(*  so demanding one set be disjoint from both is contradictory.          *)
(* ===================================================================== *)

Lemma e_guess_mono_lift_n : forall n P, size_pskl P <= n ->
  forall Θ Ξ A, a_guess_mono Θ P Ξ A -> uniq Ξ ->
  forall S0 (L K : atoms),
    ftvar_in_pskl P [<=] S0 ->
    dom Ξ ∩ (S0 ∪ L) [=] empty ->
    S0 ∩ K [=] empty ->
  exists S1 ps,
    e_guess_mono S0 P S1 (swaps_aenv ps Ξ) (swaps_ptyp ps A)
    /\ (forall a b, In (a, b) ps -> a `in` dom Ξ /\ b `notin` L)
    /\ dom (swaps_aenv ps Ξ) ∩ L [=] empty
    /\ S1 ∩ K [=] empty.
Proof.
  induction n as [ | n IHn ];
    intros P Hsz Θ Ξ A Hg Hu S0 L K Hcov HΞ HK.
  - exfalso. destruct P; simpl in Hsz; lia.
  - destruct Hg as [ Θ α Hα | Θ P Ξ A Hg | Θ α | Θ
                   | Θ P Q Ξ1 Ξ2 A B Hg1 Hg2 | Θ P Ξ A β Hβ Hg ];
      simpl in Hsz.

    + (* ⭐ □ — the INVENTION row: one pair, drawn outside [S0 ∪ L ∪ K] *)
      destruct (atom_fresh (S0 ∪ L ∪ K)) as [α' Hα'].
      assert (Hsα : swaps_atom ((α, α') :: nil) α = α')
        by (cbn [swaps_atom]; unfold swap_atom;
            destruct (α == α); [ reflexivity | congruence ]).
      exists (add α' S0), ((α, α') :: nil).
      rewrite swaps_aenv_app_dist, swaps_aenv_one_flex, swaps_aenv_nil.
      rewrite swaps_ptyp_var_f, Hsα.
      split; [ apply e_guess_mono__hole; clear - Hα'; fsetdec | ].
      split; [ intros a0 b0 [Heq | []]; inversion Heq; subst;
               split; [ simpl; fsetdec | clear - Hα'; fsetdec ] | ].
      split; [ simpl; clear - Hα'; fsetdec | clear - Hα' HK; fsetdec ].

    + (* ⫯ — pass through *)
      destruct (IHn P ltac:(lia) _ _ _ Hg Hu S0 L K
                  ltac:(clear - Hcov; simpl in *; fsetdec) HΞ HK)
        as [S1 [ps [He [Hav [Hdm Hsk]]]]].
      exists S1, ps.
      split; [ apply e_guess_mono__tophole; exact He | ].
      split; [ exact Hav | split; [ exact Hdm | exact Hsk ] ].

    + (* a variable — nothing is invented *)
      exists S0, nil.
      split; [ apply e_guess_mono__var | ].
      split; [ intros ? ? [] | ].
      split; [ simpl; fsetdec | exact HK ].

    + (* unit *)
      exists S0, nil.
      split; [ apply e_guess_mono__unit | ].
      split; [ intros ? ? [] | ].
      split; [ simpl; fsetdec | exact HK ].

    + (* ⭐ the ARROW row — the [a_] side does NOT thread, the [e_] side does *)
      rewrite dom_app in HΞ.
      assert (Hu1 : uniq Ξ1) by (clear - Hu; solve_uniq).
      assert (Hu2 : uniq Ξ2) by (clear - Hu; solve_uniq).
      assert (Hdis12 : dom Ξ1 ∩ dom Ξ2 [=] empty)
        by (clear - Hu; destruct_uniq; unfold disjoint in *; fsetdec).
      pose proof (a_guess_mono_generated_ftvar Hg2) as HftΞ2.
      pose proof (a_guess_mono_ftv Hg2) as HftB.
      (* ⚠️⚠️ EVERY side condition below is a NAMED hypothesis, and every
         [fsetdec] is scoped to at most FIVE set variables.  The two traps
         this row pays are the documented ones: an [fsetdec] inside an
         [ltac:] ARGUMENT does not return, and neither does one over six or
         more set variables. *)
      assert (HcovP : ftvar_in_pskl P [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      assert (HcovQ : ftvar_in_pskl Q [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      assert (HΞ1 : dom Ξ1 ∩ (S0 ∪ (L ∪ dom Ξ2 ∪ S0)) [=] empty)
        by (clear - HΞ Hdis12; fsetdec).
      assert (HK1 : S0 ∩ (K ∪ dom Ξ2) [=] empty)
        by (clear - HK HΞ; fsetdec).
      (* the LEFT half: its chain dodges the RIGHT half's DOMAIN and [S0],
         and its OUTPUT SUPPLY dodges that domain too *)
      destruct (IHn P ltac:(lia) _ _ _ Hg1 Hu1 S0 (L ∪ dom Ξ2 ∪ S0)
                  (K ∪ dom Ξ2) HcovP HΞ1 HK1)
        as [S1 [ps1 [He1 [Hav1 [Hdm1 Hsk1]]]]].
      pose proof (e_guess_mono_supply_grows He1) as Hgr1.
      pose proof (e_guess_mono_generated_ftvar He1) as HftE1.
      pose proof (e_guess_mono_ftv He1) as HftA1.
      assert (HcovQ1 : ftvar_in_pskl Q [<=] S1)
        by (clear - HcovQ Hgr1; fsetdec).
      assert (HdΞ2S1 : dom Ξ2 ∩ S1 [=] empty) by (clear - Hsk1; fsetdec).
      assert (HdΞ2D1 : dom Ξ2 ∩ dom (swaps_aenv ps1 Ξ1) [=] empty)
        by (clear - Hdm1; fsetdec).
      assert (HΞ2' : dom Ξ2 ∩ (S1 ∪ (L ∪ dom (swaps_aenv ps1 Ξ1) ∪ S1))
                     [=] empty)
        by (clear - HdΞ2S1 HdΞ2D1 HΞ; fsetdec).
      assert (HK2 : S1 ∩ K [=] empty) by (clear - Hsk1; fsetdec).
      (* the RIGHT half: its chain dodges the LEFT half's ANSWER *)
      destruct (IHn Q ltac:(lia) _ _ _ Hg2 Hu2 S1
                  (L ∪ dom (swaps_aenv ps1 Ξ1) ∪ S1) K HcovQ1 HΞ2' HK2)
        as [S2 [ps2 [He2 [Hav2 [Hdm2 Hsk2]]]]].
      (* the four steps that fix one premise's data by the other's chain *)
      assert (HfixΞ1 : swaps_aenv ps2 (swaps_aenv ps1 Ξ1)
                       = swaps_aenv ps1 Ξ1).
      { apply swaps_aenv_fresh_id. intros a0 b0 Hin.
        destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
        assert (HaD : a0 `notin` dom (swaps_aenv ps1 Ξ1))
          by (clear - Hka Hdm1; fsetdec).
        assert (HbD : b0 `notin` dom (swaps_aenv ps1 Ξ1))
          by (clear - Hkb; fsetdec).
        split; [ clear - HaD HftE1 | clear - HbD HftE1 ]; fsetdec. }
      assert (HfixA1 : swaps_ptyp ps2 (swaps_ptyp ps1 A)
                       = swaps_ptyp ps1 A).
      { apply swaps_ptyp_fresh_id. intros a0 b0 Hin.
        destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
        assert (HaS : a0 `notin` S0) by (clear - Hka HΞ; fsetdec).
        assert (HaD : a0 `notin` dom (swaps_aenv ps1 Ξ1))
          by (clear - Hka Hdm1; fsetdec).
        assert (HbS : b0 `notin` S0) by (clear - Hkb Hgr1; fsetdec).
        assert (HbD : b0 `notin` dom (swaps_aenv ps1 Ξ1))
          by (clear - Hkb; fsetdec).
        split; [ clear - HaS HaD HftA1 HcovP | clear - HbS HbD HftA1 HcovP ];
          fsetdec. }
      assert (HfixΞ2 : swaps_aenv ps1 Ξ2 = Ξ2).
      { apply swaps_aenv_fresh_id. intros a0 b0 Hin.
        destruct (Hav1 a0 b0 Hin) as [Hka Hkb].
        assert (HaD : a0 `notin` dom Ξ2) by (clear - Hka Hdis12; fsetdec).
        assert (HbD : b0 `notin` dom Ξ2) by (clear - Hkb; fsetdec).
        split; [ clear - HaD HftΞ2 | clear - HbD HftΞ2 ]; fsetdec. }
      assert (HfixB : swaps_ptyp ps1 B = B).
      { apply swaps_ptyp_fresh_id. intros a0 b0 Hin.
        destruct (Hav1 a0 b0 Hin) as [Hka Hkb].
        assert (HaD : a0 `notin` dom Ξ2) by (clear - Hka Hdis12; fsetdec).
        assert (HaS : a0 `notin` S0) by (clear - Hka HΞ; fsetdec).
        assert (HbD : b0 `notin` dom Ξ2) by (clear - Hkb; fsetdec).
        assert (HbS : b0 `notin` S0) by (clear - Hkb; fsetdec).
        split; [ clear - HaD HaS HftB HcovQ | clear - HbD HbS HftB HcovQ ];
          fsetdec. }
      exists S2, (ps1 ++ ps2).
      rewrite swaps_aenv_app, ! swaps_aenv_app_dist, HfixΞ1, HfixΞ2.
      rewrite swaps_ptyp_app, ! swaps_ptyp_arrow, HfixA1, HfixB.
      split; [ eapply e_guess_mono__arrow; eassumption | ].
      split.
      * intros a0 b0 Hin. rewrite dom_app. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin].
        -- destruct (Hav1 a0 b0 Hin) as [Hka Hkb].
           split; [ clear - Hka; fsetdec | clear - Hkb; fsetdec ].
        -- destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
           split; [ clear - Hka; fsetdec | clear - Hkb; fsetdec ].
      * split; [ rewrite dom_app; clear - Hdm1 Hdm2; fsetdec | exact Hsk2 ].

    + (* ⭐ the ∀ row — the witness is RENAMED, and §1 keeps it out of the
         conclusion's chain *)
      pose proof (a_guess_mono_generated_fresh Hg) as HfrΞ.
      pose proof (a_guess_mono_generated_ftvar Hg) as HftΞ.
      destruct (atom_fresh (S0 ∪ L ∪ K ∪ dom Ξ ∪ ftvar_in_pskl P
                            ∪ ftvar_in_ptyp A ∪ ftvar_in_aenv Θ))
        as [β' Hβ'].
      (* ⚠️ the witness is drawn against SEVEN sets at once, so every use of
         its freshness goes through [destruct_notin] rather than an
         [fsetdec] over all seven. *)
      assert (Hβ'S : β' `notin` S0) by (clear - Hβ'; destruct_notin; auto).
      assert (Hβ'L : β' `notin` L) by (clear - Hβ'; destruct_notin; auto).
      assert (Hβ'K : β' `notin` K) by (clear - Hβ'; destruct_notin; auto).
      assert (Hβ'Ξ : β' `notin` dom Ξ)
        by (clear - Hβ'; destruct_notin; auto).
      assert (Hβ'P : β' `notin` ftvar_in_pskl P)
        by (clear - Hβ'; destruct_notin; auto).
      assert (Hβ'A : β' `notin` ftvar_in_ptyp A)
        by (clear - Hβ'; destruct_notin; auto).
      assert (Hβ'Θ : β' `notin` ftvar_in_aenv Θ)
        by (clear - Hβ'; destruct_notin; auto).
      clear Hβ'.
      assert (Hβd : β `notin` dom Ξ)
        by (intro Hin; pose proof (HfrΞ β Hin) as Ho;
            clear - Ho; simpl in Ho; fsetdec).
      (* move the [a_] rule's own witness onto the fresh one *)
      pose proof (a_guess_mono_swap β β' _ _ _ _ Hg) as Hgs.
      rewrite swap_pskl_open_var in Hgs.
      assert (Hswβ : swap_atom β β' β = β')
        by (unfold swap_atom; destruct (β == β);
            [ reflexivity | congruence ]).
      assert (HfixP : swap_pskl β β' P = P)
        by (apply swap_pskl_fresh_id;
            [ clear - Hβ; fsetdec | exact Hβ'P ]).
      assert (HfixΞs : swap_aenv β β' Ξ = Ξ)
        by (apply swap_aenv_fresh_eq;
            [ clear - HftΞ Hβd; fsetdec | clear - Hβ'Ξ HftΞ; fsetdec ]).
      rewrite Hswβ, HfixP, HfixΞs in Hgs.
      assert (HcovB : ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f β'))
                      [<=] add β' S0).
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P
                      (pskl_var_f β')) as Hup.
        simpl in Hup. clear - Hup Hcov. simpl in *. fsetdec. }
      assert (HΞ' : dom Ξ ∩ (add β' S0 ∪ add β' L) [=] empty)
        by (clear - HΞ Hβ'Ξ; fsetdec).
      assert (HK' : add β' S0 ∩ K [=] empty)
        by (clear - HK Hβ'K; fsetdec).
      destruct (IHn (open_pskl_wrt_pskl P (pskl_var_f β'))
                  ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; lia)
                  _ _ _ Hgs Hu (add β' S0) (add β' L) K HcovB HΞ' HK')
        as [S1 [ps [He [Hav [Hdm Hsk]]]]].
      assert (Hfixβ' : swaps_atom ps β' = β')
        by (apply swaps_atom_notin; intros a0 b0 Hin;
            destruct (Hav a0 b0 Hin) as [Hka Hkb];
            split; intro Heq0; subst;
            [ clear - Hka Hβ'Ξ; fsetdec | clear - Hkb; fsetdec ]).
      assert (Hcl : close_ptyp_wrt_ptyp β' (swap_ptyp β β' A)
                    = close_ptyp_wrt_ptyp β A)
        by (apply close_ptyp_wrt_ptyp_rename; exact Hβ'A).
      exists S1, ps.
      split.
      * (* ⭐ §1: the conclusion's [close] is the SAME term, so the witness's
           own transposition never enters the chain *)
        rewrite <- Hcl, swaps_ptyp_all, swaps_ptyp_close, Hfixβ'.
        apply e_guess_mono__forall with (β := β'); [ exact Hβ'S | exact He ].
      * split; [ intros a0 b0 Hin; destruct (Hav a0 b0 Hin) as [Hka Hkb];
                 split; [ exact Hka | clear - Hkb; fsetdec ] | ].
        split; [ clear - Hdm; fsetdec | exact Hsk ].
Qed.

Corollary e_guess_mono_lift : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> uniq Ξ ->
  forall S0 (L K : atoms),
    ftvar_in_pskl P [<=] S0 ->
    dom Ξ ∩ (S0 ∪ L) [=] empty ->
    S0 ∩ K [=] empty ->
  exists S1 ps,
    e_guess_mono S0 P S1 (swaps_aenv ps Ξ) (swaps_ptyp ps A)
    /\ (forall a b, In (a, b) ps -> a `in` dom Ξ /\ b `notin` L)
    /\ dom (swaps_aenv ps Ξ) ∩ L [=] empty
    /\ S1 ∩ K [=] empty.
Proof.
  intros. eapply e_guess_mono_lift_n; [ apply le_n | eassumption .. ].
Qed.

(** The sort wrapper: [guess^SK] moves nothing, [guess^TY] is §2's rows read
    back through the painting. *)
Corollary e_guess_lift : forall Θ NM Q Ξ Q',
  a_guess Θ NM Q Ξ Q' -> uniq Ξ ->
  forall S0 (L K : atoms),
    ftvar_in_pskl Q [<=] S0 ->
    dom Ξ ∩ (S0 ∪ L) [=] empty ->
    S0 ∩ K [=] empty ->
  exists S1 ps,
    e_guess S0 NM Q S1 (swaps_aenv ps Ξ) (swaps_pskl ps Q')
    /\ (forall a b, In (a, b) ps -> a `in` dom Ξ /\ b `notin` L)
    /\ dom (swaps_aenv ps Ξ) ∩ L [=] empty
    /\ S1 ∩ K [=] empty.
Proof.
  intros Θ NM Q Ξ Q' Hg Hu S0 L K Hcov HΞ HK.
  destruct Hg as [ Θ0 Q0 | Θ0 Q0 Ξ0 A Hgm ].
  - exists S0, nil.
    split; [ apply e_guess__sk | ].
    split; [ intros ? ? [] | ].
    split; [ simpl; fsetdec | exact HK ].
  - destruct (e_guess_mono_lift Hgm Hu Hcov HΞ HK)
      as [S1 [ps [He [Hav [Hdm Hsk]]]]].
    exists S1, ps.
    rewrite swaps_pskl_ptyp_to_pskl.
    split; [ apply e_guess__ty; exact He | ].
    split; [ exact Hav | split; [ exact Hdm | exact Hsk ] ].
Qed.

(* ===================================================================== *)
(*  §3  ⭐⭐⭐ THE LOOK BLOCK — ALREADY CLOSED, AND IN A DIFFERENT           *)
(*      CURRENCY.  READ THIS BEFORE WRITING ANY BLOCK ABOVE §2.           *)
(*                                                                        *)
(*  §8c.24's costed plan lists the collection as the lift's next block,    *)
(*  nineteen rows in §2's CHAIN currency.  ⛔ DO NOT WRITE IT: the chain   *)
(*  currency is UNAVAILABLE here, and the block is already proved in the   *)
(*  currency that is — [a_looksub_lookeq_rel_e] (prop_solve_rel.v §7,      *)
(*  campaign §8c.9's transport 5), which is stated a → e and needs only    *)
(*  to be instantiated at the EMPTY pair list.                            *)
(*                                                                        *)
(*  ⛔⛔ WHY THE CHAIN CURRENCY CANNOT WORK ABOVE THE GUESS.  A chain is a  *)
(*  FUNCTION on atoms; [rel_pskl] is deliberately a RELATION (see          *)
(*  prop_solve_det.v §1's header).  §2 could use a chain only because      *)
(*  [a_guess_mono] leaks NOTHING: its ∀ row closes its witness away, so    *)
(*  every atom the derivation invents lands in [dom Ξ] and [uniq Ξ] — one  *)
(*  premise, available at the only consumer — makes the columns distinct.  *)
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
(*  shape, not §2's: side 2 an [e_] derivation, the outputs related at a   *)
(*  ρ that GROWS, the blocks read off as [flex_pairs_l] / [flex_pairs_r].  *)
(*  §8c.9 already built that shape a → a for guess, both solve layers and  *)
(*  the fold (prop_solve_rel.v §3-§6); those are what the a → e versions   *)
(*  should be copied from.                                                *)
(*                                                                        *)
(*  ⚙ THE LIFT PROPER is transport 5 at [ρ = nil], where [rel_pskl] is     *)
(*  reflexivity on anything the support covers ([rel_pskl_refl]) and the   *)
(*  flex agreement is two [reflexivity]s.  Both halves below.              *)
(* ===================================================================== *)

Lemma e_looksub_lift : forall Θ α m P P' Ξ C,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  forall S0 (V : atoms),
    add α (ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] V ->
    V [<=] S0 ->
  exists S1 ρx ρn Ξ' C',
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ' ⨾ C' }}e
    /\ Ξ = flex_pairs_l ρn /\ Ξ' = flex_pairs_r ρn
    /\ (forall a b, In (a, b) (ρx ++ ρn) ->
          a `notin` add α (ftvar_in_aenv Θ) /\ b `in` S1 /\ b `notin` S0)
    /\ cols_r ρx ∩ dom Ξ' [=] empty
    /\ (forall a b, In (a, b) ρx -> a `in` ftvar_in_a_cstrs C)
    /\ cols_l ρx ∩ dom Ξ [=] empty
    /\ rel_a_cstrs (ρx ++ ρn) V C C'.
Proof.
  intros Θ α m P P' Ξ C H S0 V HV HS.
  assert (HrP : rel_pskl nil V P P)
    by (apply rel_pskl_refl; clear - HV; fsetdec).
  assert (HrP' : rel_pskl nil V P' P')
    by (apply rel_pskl_refl; clear - HV; fsetdec).
  assert (HαV : α `in` V) by (clear - HV; fsetdec).
  assert (Hαl : α `notin` cols_l (@nil (atom * atom)))
    by (simpl; clear; fsetdec).
  assert (Hαr : α `notin` cols_r (@nil (atom * atom)))
    by (simpl; clear; fsetdec).
  assert (Hag : flex_agree_rel nil V Θ Θ)
    by (split; [ intros; reflexivity | intros ? ? [] ]).
  assert (Hcov : V ∪ cols_r (@nil (atom * atom))
                 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P' [<=] S0)
    by (simpl; clear - HV HS; fsetdec).
  destruct ((proj1 a_looksub_lookeq_rel_e) _ _ _ _ _ _ _ H S0 Θ P P' nil V
              HrP HrP' HαV Hαl Hαr Hag Hcov)
    as (S1 & ρx & ρn & Ξ' & C' & He & E1 & E2 & Hfr & Hdis & Hoc & Hcl
        & Hrel).
  exists S1, ρx, ρn, Ξ', C'.
  rewrite app_nil_r in Hrel.
  split; [ exact He | ]. split; [ exact E1 | ]. split; [ exact E2 | ].
  split; [ exact Hfr | ]. split; [ exact Hdis | ].
  split; [ exact Hoc | ]. split; [ exact Hcl | ]. exact Hrel.
Qed.

Lemma e_lookeq_lift : forall Θ α P P' Ξ C,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
  forall S0 (V : atoms),
    add α (ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] V ->
    V [<=] S0 ->
  exists S1 ρx ρn Ξ' C',
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ' ⨾ C' }}e
    /\ Ξ = flex_pairs_l ρn /\ Ξ' = flex_pairs_r ρn
    /\ (forall a b, In (a, b) (ρx ++ ρn) ->
          a `notin` add α (ftvar_in_aenv Θ) /\ b `in` S1 /\ b `notin` S0)
    /\ cols_r ρx ∩ dom Ξ' [=] empty
    /\ (forall a b, In (a, b) ρx -> a `in` ftvar_in_a_cstrs C)
    /\ cols_l ρx ∩ dom Ξ [=] empty
    /\ rel_a_cstrs (ρx ++ ρn) V C C'.
Proof.
  intros Θ α P P' Ξ C H S0 V HV HS.
  assert (HrP : rel_pskl nil V P P)
    by (apply rel_pskl_refl; clear - HV; fsetdec).
  assert (HrP' : rel_pskl nil V P' P')
    by (apply rel_pskl_refl; clear - HV; fsetdec).
  assert (HαV : α `in` V) by (clear - HV; fsetdec).
  assert (Hαl : α `notin` cols_l (@nil (atom * atom)))
    by (simpl; clear; fsetdec).
  assert (Hαr : α `notin` cols_r (@nil (atom * atom)))
    by (simpl; clear; fsetdec).
  assert (Hag : flex_agree_rel nil V Θ Θ)
    by (split; [ intros; reflexivity | intros ? ? [] ]).
  assert (Hcov : V ∪ cols_r (@nil (atom * atom))
                 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P' [<=] S0)
    by (simpl; clear - HV HS; fsetdec).
  destruct ((proj2 a_looksub_lookeq_rel_e) _ _ _ _ _ _ H S0 Θ P P' nil V
              HrP HrP' HαV Hαl Hαr Hag Hcov)
    as (S1 & ρx & ρn & Ξ' & C' & He & E1 & E2 & Hfr & Hdis & Hoc & Hcl
        & Hrel).
  exists S1, ρx, ρn, Ξ', C'.
  rewrite app_nil_r in Hrel.
  split; [ exact He | ]. split; [ exact E1 | ]. split; [ exact E2 | ].
  split; [ exact Hfr | ]. split; [ exact Hdis | ].
  split; [ exact Hoc | ]. split; [ exact Hcl | ]. exact Hrel.
Qed.

(* ===================================================================== *)
(*  §4  ⭐ [guess^TY] LIFTS IN THE REL CURRENCY TOO — and this is the copy *)
(*      the SOLVE layer consumes                                          *)
(*                                                                        *)
(*  §2's chain form is what a consumer holding [uniq Ξ] wants (AT-Abs).    *)
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
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  V ∪ cols_r ρ ∪ ftvar_in_pskl P2 [<=] S0 ->
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
    assert (Hcov : V ∪ cols_r ρ ∪ ftvar_in_pskl Q0 [<=] S0)
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
    assert (HcovA : V ∪ cols_r ρ ∪ ftvar_in_pskl Q0a [<=] S0)
      by (clear - Hscp2; simpl in *; fsetdec).
    destruct (IHHG1 S0 Q0a ρ V HrelA Hscp1 HcovA)
      as (S1 & ρnA & Ξ2a & A2a & HG2a & E1a & E2a & HrelA').
    pose proof (e_guess_mono_supply_grows HG2a) as Hgr1.
    assert (HcovB : V ∪ cols_r ρ ∪ ftvar_in_pskl Q0b [<=] S1)
      by (clear - Hscp2 Hgr1; simpl in *; fsetdec).
    destruct (IHHG2 S1 Q0b ρ V HrelB Hscp1 HcovB)
      as (S2 & ρnB & Ξ2b & B2b & HG2b & E1b & E2b & HrelB').
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
       openers PAIR, and the yields re-close along the shortened list *)
    inversion Hrel; subst.
    match goal with
    | Hb : rel_pskl ρ V P ?X |- _ => rename Hb into Hbody; rename X into Q0
    end.
    destruct (atom_fresh S0) as [β2 Hβ2].
    assert (Hrelo : rel_pskl ((β, β2) :: ρ) V
                      (open_pskl_wrt_pskl P (pskl_var_f β))
                      (open_pskl_wrt_pskl Q0 (pskl_var_f β2)))
      by (apply rel_pskl_open_pair; exact Hbody).
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (Hup : ftvar_in_pskl (open_pskl_wrt_pskl Q0 (pskl_var_f β2))
                  [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl Q0)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ)
                     ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q0 (pskl_var_f β2))
                       [<=] add β2 S0)
      by (simpl in *; clear - Hscp2 Hup; fsetdec).
    destruct (IHHG (add β2 S0) (open_pskl_wrt_pskl Q0 (pskl_var_f β2))
                ((β, β2) :: ρ) V Hrelo Hscp1' Hscp2')
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
    split;
      [ apply e_guess_mono__forall with (β := β2); [ exact Hβ2 | exact HG2 ] | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    simpl. rewrite ! ptyp_to_pskl_close.
    constructor.
    apply rel_pskl_close_pair.
    + apply rel_pskl_bubble_pair. exact Hrel'.
    + match goal with
      | Hf : β `notin` union _ _ |- _ => clear - Hf Hscp1; fsetdec
      end.
    + rewrite cols_l_app.
      rewrite <- ! dom_flex_pairs_l. rewrite <- E1.
      rewrite dom_flex_pairs_l.
      match goal with
      | Hf : β `notin` union _ _ |- _ => clear - Hf Hscp1 HβΞ1; fsetdec
      end.
    + clear - Hβ2 Hscp2. fsetdec.
    + rewrite cols_r_app.
      rewrite <- ! dom_flex_pairs_r. rewrite <- E2.
      rewrite dom_flex_pairs_r.
      clear - Hβ2 Hscp2 Hβ2Ξ2. fsetdec.
Qed.

(** The sort wrapper, relationally: [guess^SK] moves nothing and pairs
    nothing, [guess^TY] is §4's rows read back through the painting. *)
Lemma a_guess_rel_e : forall Θ1 NM Q1 Ξ1 Q1',
  a_guess Θ1 NM Q1 Ξ1 Q1' ->
  forall S0 Q2 ρ V,
  rel_pskl ρ V Q1 Q2 ->
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  V ∪ cols_r ρ ∪ ftvar_in_pskl Q2 [<=] S0 ->
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
  - destruct (a_guess_mono_rel_e Hgm Hrel Hscp1 Hscp2)
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
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
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
    intros S0 Θ2 P3 Q3 ρ V HrelP HrelQ Hagr Hscp1 HdΘ Hscp2 Hcov.
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
    assert (HcovG : V ∪ cols_r ρ ∪ ftvar_in_pskl P3 [<=] S0)
      by (clear - Hscp2 Hcov; fsetdec).
    destruct (a_guess_mono_rel_e Hguess HrelP Hscp1 HcovG)
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
    destruct (IHHD1 S0 Θ2 P2a Q2a ρ V HrPa HrQa Hagr Hscp1 HdΘ Hscp2 HcovA)
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
      - clear - Hd1a Hscp1 Hdfl. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V ∪ cols_l (ρnA ++ ρ) [<=] ftvar_in_aenv (Ξ1 ++ Θ)).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      clear - Hscp1 Hdfl Hds. fsetdec. }
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
    destruct (IHHD2 S1 (Ξ2a ++ Θ2) P2b Q2b (ρnA ++ ρ) V
                HrPb' HrQb' Hagr' Hscp1' HdΘ' Hscp2' HcovB)
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
    assert (Hagr' : flex_agree_rel ((β, β2) :: ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_tvar_pair; [ exact Hagr | | ].
      - clear - Hβ1 Hscp1 Hds1. fsetdec.
      - clear - Hβ2 HdΘ Hscp2. fsetdec. }
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ) [<=] add β2 S0)
      by (simpl; clear - Hscp2; fsetdec).
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
    destruct (IHHD (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                ((β, β2) :: ρ) V
                ltac:(apply rel_pskl_open_pair; exact HrP0)
                ltac:(apply rel_pskl_open_pair; exact HrQ0)
                Hagr' Hscp1' HdΘ' Hscp2' Hcov')
      as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD)).
    assert (Hd2p : dom Ξ2 ∩ add β2 S0 [=] empty)
      by (apply (proj2 e_solve_sub_eq_block) in D2p; tauto).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    exists S1, ρn, Ξ2, (pskl_all_syn (close_pskl_wrt_pskl β2 Y2)).
    split; [ apply e_solve_eq__forall with (β := β2); [ exact Hβ2 | exact D2p ] | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    constructor.
    apply rel_pskl_close_pair.
    + apply rel_pskl_bubble_pair. exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + rewrite cols_l_app. simpl in Hd1p.
      clear - Hβ1 Hscp1 Hd1p Hdfl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + rewrite cols_r_app. clear - Hβ2 Hscp2 Hd2p Hdfr. fsetdec.
  - (* SE-UnivGhost: ⫯ on both sides passes through *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa, Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    assert (Hcov' : ftvar_in_pskl P2b ∪ ftvar_in_pskl Q2b [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    destruct (IHHD S0 Θ2 P2b Q2b ρ V HrP0 HrQ0 Hagr Hscp1 HdΘ Hscp2 Hcov')
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
    assert (Hagr' : flex_agree_rel ((β, β2) :: ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_tvar_pair; [ exact Hagr | | ].
      - clear - Hβ1 Hscp1 Hds1. fsetdec.
      - clear - Hβ2 HdΘ Hscp2. fsetdec. }
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ) [<=] add β2 S0)
      by (simpl; clear - Hscp2; fsetdec).
    assert (HupQ : ftvar_in_pskl (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl Q2b)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl (pskl_tophole P2b)
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                      [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupQ; fsetdec).
    destruct (IHHD (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (pskl_tophole P2b)
                (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                ((β, β2) :: ρ) V
                ltac:(apply rel_pskl_extend_pair; constructor; exact HrP0)
                ltac:(apply rel_pskl_open_pair; exact HrQ0)
                Hagr' Hscp1' HdΘ' Hscp2' Hcov')
      as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD)).
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
    apply rel_pskl_close_pair.
    + apply rel_pskl_bubble_pair. exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + rewrite cols_l_app. simpl in Hd1p.
      clear - Hβ1 Hscp1 Hd1p Hdfl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + rewrite cols_r_app. clear - Hβ2 Hscp2 Hd2p Hdfr. fsetdec.
  - (* SE-GhostGuarded: the subject strips its ⫯ *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa |- _ =>
        rename Ha into HrP0; rename xa into P2b
    end.
    assert (Hcov' : ftvar_in_pskl P2b ∪ ftvar_in_pskl Q3 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    destruct (IHHD S0 Θ2 P2b Q3 ρ V HrP0 HrelQ Hagr Hscp1 HdΘ Hscp2 Hcov')
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
    assert (Hagr' : flex_agree_rel ((β, β2) :: ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_tvar_pair; [ exact Hagr | | ].
      - clear - Hβ1 Hscp1 Hds1. fsetdec.
      - clear - Hβ2 HdΘ Hscp2. fsetdec. }
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ) [<=] add β2 S0)
      by (simpl; clear - Hscp2; fsetdec).
    assert (HupP : ftvar_in_pskl (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl P2b)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                    ∪ ftvar_in_pskl (pskl_tophole Q2b) [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupP; fsetdec).
    destruct (IHHD (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                (pskl_tophole Q2b)
                ((β, β2) :: ρ) V
                ltac:(apply rel_pskl_open_pair; exact HrP0)
                ltac:(apply rel_pskl_extend_pair; constructor; exact HrQ0)
                Hagr' Hscp1' HdΘ' Hscp2' Hcov')
      as (S1 & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hrel').
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD)).
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
    apply rel_pskl_close_pair.
    + apply rel_pskl_bubble_pair. exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + rewrite cols_l_app. simpl in Hd1p.
      clear - Hβ1 Hscp1 Hd1p Hdfl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + rewrite cols_r_app. clear - Hβ2 Hscp2 Hd2p Hdfr. fsetdec.
  - (* SE-GuardedGhost: the target strips its ⫯ *)
    inversion HrelQ; subst.
    match goal with
    | Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Hb into HrQ0; rename xb into Q2b
    end.
    assert (Hcov' : ftvar_in_pskl P3 ∪ ftvar_in_pskl Q2b [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    destruct (IHHD S0 Θ2 P3 Q2b ρ V HrelP HrQ0 Hagr Hscp1 HdΘ Hscp2 Hcov')
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

Lemma a_solve_sub_rel_e : forall Θ1 m P1 Q1 Ξ1 P1',
  {{ Θ1 ⊢ₛ P1 ≼[ m ] Q1 ⤳ Ξ1 ⨾ P1' }}a ->
  forall S0 Θ2 P3 Q3 ρ V,
  rel_pskl ρ V P1 P3 ->
  rel_pskl ρ V Q1 Q3 ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  dom Θ2 [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P3 ∪ ftvar_in_pskl Q3 [<=] S0 ->
  exists S1 ρx ρn Ξ2 P3',
    {{ S0 ↝ S1 ⊨ Θ2 ⊢ₛ P3 ≼[ m ] Q3 ⤳ Ξ2 ⨾ P3' }}e
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 /\ b `notin` S0)
    /\ rel_pskl (ρx ++ ρn ++ ρ) V P1' P3'.
Proof.
  intros Θ1 m P1 Q1 Ξ1 P1' HD.
  induction HD;
    intros S0 Θ2 P3 Q3 ρ V HrelP HrelQ Hagr Hscp1 HdΘ Hscp2 Hcov.
  - (* SS-Var *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ => rename Ha into Hat; rename b into β0
    end.
    exists S0, nil, nil, nil, (pskl_var_f β0).
    split; [ apply e_solve_sub__var | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ intros a b Hin; inversion Hin | ].
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
    assert (Hagr' : flex_agree_rel ((β, β2) :: ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_tvar_pair; [ exact Hagr | | ].
      - clear - Hβ1 Hscp1 Hds1. fsetdec.
      - clear - Hβ2 HdΘ Hscp2. fsetdec. }
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ) [<=] add β2 S0)
      by (simpl; clear - Hscp2; fsetdec).
    assert (HupP : ftvar_in_pskl (open_pskl_wrt_pskl P3b (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl P3b)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl (open_pskl_wrt_pskl P3b (pskl_var_f β2))
                    ∪ ftvar_in_pskl Q3 [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupP; fsetdec).
    destruct (IHHD (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (open_pskl_wrt_pskl P3b (pskl_var_f β2)) Q3
                ((β, β2) :: ρ) V
                ltac:(apply rel_pskl_open_pair; exact HrP0)
                ltac:(apply rel_pskl_extend_pair; exact HrelQ)
                Hagr' Hscp1' HdΘ' Hscp2' Hcov')
      as (S1 & ρx & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hρx & Hrel').
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ HD)).
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
    constructor.
    apply rel_pskl_close_pair.
    + rel_perm Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + rewrite ! cols_l_app. simpl in Hd1p.
      clear - Hβ1 Hscp1 Hd1p Hdfl Hβcl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + rewrite ! cols_r_app.
      clear - Hβ2 Hscp2 Hd2p Hdfr Hβ2cr. fsetdec.
  - (* SS-UnivGhostL: the subject strips its ⫯; the yield re-wraps *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa |- _ =>
        rename Ha into HrP0; rename xa into P3b
    end.
    assert (Hcov' : ftvar_in_pskl P3b ∪ ftvar_in_pskl Q3 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    destruct (IHHD S0 Θ2 P3b Q3 ρ V HrP0 HrelQ Hagr Hscp1 HdΘ Hscp2 Hcov')
      as (S1 & ρx & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hρx & Hrel').
    exists S1, ρx, ρn, Ξ2, (pskl_tophole Y2).
    split; [ apply e_solve_sub__univ_ghost_l; exact D2p | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    split; [ exact Hρx | ].
    constructor. exact Hrel'.
  - (* SS-Vacuous *)
    inversion HrelQ; subst.
    exists S0, nil, nil, nil, P3.
    split;
      [ apply e_solve_sub__vacuous;
        eapply rel_pskl_peel_l_off; [ exact HrelP | assumption ] | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ intros a b Hin; inversion Hin | ].
    simpl. exact HrelP.
  - (* SS-Check: drops into §5 *)
    match goal with
    | He : a_solve_eq _ _ _ _ _ |- _ => rename He into HDeq0
    end.
    destruct (a_solve_eq_rel_e HDeq0 HrelP HrelQ Hagr Hscp1 HdΘ Hscp2 Hcov)
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
    assert (Hagr' : flex_agree_rel ((β, β2) :: ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_tvar_pair; [ exact Hagr | | ].
      - clear - Hβ1 Hscp1 Hds1. fsetdec.
      - clear - Hβ2 HdΘ Hscp2. fsetdec. }
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (HdΘ' : dom ((β2 ~ abind_tvar) ++ Θ2) [<=] add β2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ) [<=] add β2 S0)
      by (simpl; clear - Hscp2; fsetdec).
    assert (HupB : ftvar_in_pskl (open_pskl_wrt_pskl B3 (pskl_var_f β2))
                   [<=] ftvar_in_pskl (pskl_var_f β2) ∪ ftvar_in_pskl B3)
      by (apply ftvar_in_pskl_open_pskl_wrt_pskl_upper).
    assert (Hcov' : ftvar_in_pskl P3
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl B3 (pskl_var_f β2))
                      [<=] add β2 S0)
      by (simpl in *; clear - Hcov HupB; fsetdec).
    destruct (IHHD (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                P3 (open_pskl_wrt_pskl B3 (pskl_var_f β2))
                ((β, β2) :: ρ) V
                ltac:(apply rel_pskl_extend_pair; exact HrelP)
                ltac:(apply rel_pskl_open_pair; exact HrB0)
                Hagr' Hscp1' HdΘ' Hscp2' Hcov')
      as (S1 & ρx & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hρx & Hrel').
    exists S1, (ρx ++ (β, β2) :: nil), ρn, Ξ2, Y2.
    split.
    { apply e_solve_sub__forall_r with (β := β2).
      - eapply rel_pskl_ghost_free; [ exact HrelQ | assumption ].
      - eapply rel_pskl_solve_l_off; [ exact HrelP | assumption ].
      - exact Hβ2.
      - exact D2p. }
    split; [ exact E1 | split; [ exact E2 | ] ].
    split.
    { intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      - destruct (Hρx a b Hin) as [Ha Hb]. simpl in Ha.
        split; [ clear - Ha; fsetdec | clear - Hb; fsetdec ].
      - destruct Hin as [E | Hin]; [ inversion E; subst | inversion Hin ].
        split; [ clear - Hβ1; fsetdec | exact Hβ2 ]. }
    rel_perm Hrel'.
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
    destruct (a_solve_eq_rel_e HDeq HrPa HrQa Hagr Hscp1 HdΘ Hscp2 HcovA)
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
      - clear - Hd1a Hscp1 Hdfl. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V ∪ cols_l (ρnA ++ ρ) [<=] ftvar_in_aenv (Ξ1 ++ Θ)).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      clear - Hscp1 Hdfl Hds. fsetdec. }
    assert (HdΘ' : dom (Ξ2a ++ Θ2) [<=] S1)
      by (rewrite dom_app; clear - Hi2a HdΘ Hgr1; fsetdec).
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hscp2 Hdfr Hi2a Hgr1. fsetdec. }
    assert (HcovB : ftvar_in_pskl P3b ∪ ftvar_in_pskl Q3b [<=] S1)
      by (clear - Hcov Hgr1; simpl in *; fsetdec).
    destruct (IHHD S1 (Ξ2a ++ Θ2) P3b Q3b (ρnA ++ ρ) V
                ltac:(apply rel_pskl_widen; exact HrPb)
                ltac:(apply rel_pskl_widen; exact HrQb)
                Hagr' Hscp1' HdΘ' Hscp2' HcovB)
      as (S2 & ρx & ρnB & Ξ2b & P2b' & D2b & E1b & E2b & Hρx & HrelB').
    exists S2, ρx, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a), (pskl_arrow P2a' P2b').
    split; [ eapply e_solve_sub__arrow; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      rewrite ftvar_in_aenv_app in Ha.
      split; [ clear - Ha; fsetdec | clear - Hb Hgr1; fsetdec ]. }
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
    destruct (a_solve_eq_rel_e HDeq (rel_pskl__hole ρ V) HrQa Hagr Hscp1
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
      - clear - Hd1a Hscp1 Hdfl. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V ∪ cols_l (ρnA ++ ρ) [<=] ftvar_in_aenv (Ξ1 ++ Θ)).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      clear - Hscp1 Hdfl Hds. fsetdec. }
    assert (HdΘ' : dom (Ξ2a ++ Θ2) [<=] S1)
      by (rewrite dom_app; clear - Hi2a HdΘ Hgr1; fsetdec).
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hscp2 Hdfr Hi2a Hgr1. fsetdec. }
    assert (HcovB : ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl Q3b [<=] S1)
      by (clear - Hcov Hgr1; simpl in *; fsetdec).
    destruct (IHHD S1 (Ξ2a ++ Θ2) pskl_hole Q3b (ρnA ++ ρ) V
                (rel_pskl__hole (ρnA ++ ρ) V)
                ltac:(apply rel_pskl_widen; exact HrQb)
                Hagr' Hscp1' HdΘ' Hscp2' HcovB)
      as (S2 & ρx & ρnB & Ξ2b & P2b' & D2b & E1b & E2b & Hρx & HrelB').
    exists S2, ρx, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a),
      (pskl_tophole (pskl_arrow P2a' P2b')).
    split; [ eapply e_solve_sub__ghost_l_fn; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      rewrite ftvar_in_aenv_app in Ha.
      split; [ clear - Ha; fsetdec | clear - Hb Hgr1; fsetdec ]. }
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
    simpl. constructor. exact HrelQ.
Qed.

(* ===================================================================== *)
(*  §7  ⭐ THE CONSTRAINT FOLD LIFTS — three rows                          *)
(*                                                                        *)
(*  prop_solve_rel.v §6's [a_solve_cstr_rel], side 2 moved to             *)
(*  [e_solve_cstr].  ⚙ The eq-cons row is the only one with work: the head *)
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
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  dom Θ2 [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P3 ∪ ftvar_in_a_cstrs C2 [<=] S0 ->
  exists S1 ρx ρn Ξ2 P3',
    {{ S0 ↝ S1 ⊨ Θ2 ⊩ C2 ⨾ P3 ⤳ Ξ2 ⨾ P3' }}e
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 /\ b `notin` S0)
    /\ rel_pskl (ρx ++ ρn ++ ρ) V P1' P3'.
Proof.
  intros Θ1 C1 P1 Ξ1 P1' HD.
  induction HD;
    intros S0 Θ2 C3 P3 ρ V HrelP HrelC Hagr Hscp1 HdΘ Hscp2 Hcov.
  - (* SC-Empty *)
    inversion HrelC; subst.
    exists S0, nil, nil, nil, P3.
    split; [ apply e_solve_cstr__empty | ].
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ intros a b Hin; inversion Hin | ].
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
    destruct (a_solve_sub_rel_e HDsub HrelP HrelQ Hagr Hscp1 HdΘ Hscp2 HcovS)
      as (S1 & ρx & ρn & Ξ2 & Y2 & D2s & E1 & E2 & Hρx & Hrel').
    exists S1, ρx, ρn, Ξ2, Y2.
    split; [ apply e_solve_cstr__sub; exact D2s | ].
    split; [ exact E1 | split; [ exact E2 | ] ].
    split; [ exact Hρx | exact Hrel' ].
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
    destruct (a_solve_eq_rel_e HDeq HrelP HrelQ Hagr Hscp1 HdΘ Hscp2 HcovH)
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
      - clear - Hd1a Hscp1 Hdfl. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V ∪ cols_l (ρnA ++ ρ) [<=] ftvar_in_aenv (Ξ1 ++ Θ)).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      clear - Hscp1 Hdfl Hds. fsetdec. }
    assert (HdΘ' : dom (Ξ2a ++ Θ2) [<=] S1)
      by (rewrite dom_app; clear - Hi2a HdΘ Hgr1; fsetdec).
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hscp2 Hdfr Hi2a Hgr1. fsetdec. }
    assert (HcovT : ftvar_in_pskl Pmid2 ∪ ftvar_in_a_cstrs C2' [<=] S1)
      by (clear - Hout Hcov Hgr1; simpl in *; fsetdec).
    destruct (IHHD S1 (Ξ2a ++ Θ2) C2' Pmid2 (ρnA ++ ρ) V
                HrelM
                ltac:(apply rel_a_cstrs_widen; exact HrelC')
                Hagr' Hscp1' HdΘ' Hscp2' HcovT)
      as (S2 & ρx & ρnB & Ξ2b & P3' & D2b & E1b & E2b & Hρx & HrelB').
    exists S2, ρx, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a), P3'.
    split; [ eapply e_solve_cstr__eq; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      rewrite ftvar_in_aenv_app in Ha.
      split; [ clear - Ha; fsetdec | clear - Hb Hgr1; fsetdec ]. }
    rel_perm HrelB'.
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
(*  (frost/algo/def_rules.v), so the configuration above is no longer      *)
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
(*  and [e_guess_mono_lift]'s [uniq Ξ] in §2).  ⚠️ [uniq Ξ] does NOT       *)
(*  suffice here and no strengthening of it can: a leaked opener is not a  *)
(*  block member, so [uniq] cannot see it.  ⛔ Nor is it derivable from a  *)
(*  scoping hypothesis on the look's inputs — both side conditions above   *)
(*  already dodge [ftvar_in_aenv Θ] and that is all a scoping premise      *)
(*  buys.  The premise has to be about the DERIVATION, and where it is     *)
(*  discharged ([a_sub__forall_l] is the only consumer) is the design      *)
(*  question the next session opens on.  docs/PAPER-GAPS.md will want it   *)
(*  once it is machine-checked.                                            *)
(* ===================================================================== *)
