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

Require Import src.frost.ltac_utils.

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
Require Import src.frost.ext_algo.prop_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.prop_solve.
Require Import src.frost.ext_algo.prop_solve_det.
Require Import src.frost.ext_algo.prop_solve_rel.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.consis.prop_consis_rename.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.prop_consis.
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
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 /\ b `notin` S0)
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
      as (S1 & ρx & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hρx & Hrel').
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
    (* ⚙ the restriction must be UNDONE here: the leaked pair moves into ρx
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
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 /\ b `notin` S0)
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

(** ⭐ AND THE GUARD COSTS THE THREADED ENCODING NOTHING — a THEOREM, not an
    argument, exactly as [e_looksub_lookeq_cstr_old] is for the CROSS-HALF
    guard one layer down.  The collection's constraints live in the supply it
    has already spent, and the fold's block is drawn STRICTLY ABOVE that
    supply; the two cannot meet.  ⇒ if [a_extract__solve] takes the guard as
    a premise, [e_extract_sound] discharges it from facts its proof already
    computes ([e_looksub_cstr_ftvar] and [e_solve_cstr_block] are both
    already [pose proof]ed there), so the rule change is faithful to the
    implementation by construction. *)
Lemma e_extract_solve_guard : forall S0 S1 S2 Θ0 α m P P' Ξ C Ξs Q,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  {{ S1 ↝ S2 ⊨ (Ξ ++ Θ0) ⊩ C ⨾ pskl_hole ⤳ Ξs ⨾ Q }}e ->
  ftvar_in_pskl P ∪ ftvar_in_pskl P' [<=] S0 ->
  ftvar_in_a_cstrs C ∩ dom Ξs [=] empty.
Proof.
  intros * Hl Hc Hcov.
  pose proof (e_looksub_cstr_ftvar Hl Hcov) as Hcs.
  pose proof (e_solve_cstr_block Hc) as [_ [Hfr _]].
  clear - Hcs Hfr. fsetdec.
Qed.

Lemma a_extract_rel_e_gen :
  forall Θ1 α m NM P1 P1' Ξ1L C1 Ξ1F Q1 Ξ1G Q1',
  {{ Θ1 ⊢ P1 ≼[ α , m ] P1' ⤳ Ξ1L ⨾ C1 }}a ->
  {{ (Ξ1L ++ Θ1) ⊩ C1 ⨾ pskl_hole ⤳ Ξ1F ⨾ Q1 }}a ->
  a_guess (Ξ1F ++ Ξ1L ++ Θ1) NM Q1 Ξ1G Q1' ->
  (* ⛔ THE GUARD THE ROW OWES — see the box above. *)
  ftvar_in_a_cstrs C1 ∩ dom Ξ1F [=] empty ->
  forall S0 Θ2 P2 P2' ρ V,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V P1' P2' ->
  α `in` V ->
  α `notin` cols_l ρ ->
  α `notin` cols_r ρ ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  dom Θ2 [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] S0 ->
  exists S1 ρx ρn Ξ2 Q2',
    {{ S0 ↝ S1 ⊨ Θ2 ⊢ P2 ⊳[ NM , α , m ] P2' ⤳ Ξ2 ↪ Q2' }}e
    /\ (Ξ1L ++ Ξ1F ++ Ξ1G) = flex_pairs_l ρn
    /\ Ξ2 = flex_pairs_r ρn
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 /\ b `notin` S0)
    /\ rel_pskl (ρx ++ ρn ++ ρ) V Q1' Q2'.
Proof.
  intros Θ1 α m NM P1 P1' Ξ1L C1 Ξ1F Q1 Ξ1G Q1' HL HF HG Hguard.
  intros S0 Θ2 P2 P2' ρ V HrP HrP' HαV Hαl Hαr Hagr Hscp1 HdΘ Hscp2 Hcov.

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
     everything the caller knows *)
  assert (HnLl : cols_l ρnL ∩ (V ∪ cols_l ρ) [=] empty).
  { assert (Hd : cols_l ρnL ∩ ftvar_in_aenv Θ1 [=] empty).
    { intros x. split; intros Hx; [ | clear - Hx; fsetdec ].
      exfalso.
      assert (Hxl : x `in` cols_l ρnL) by (clear - Hx; fsetdec).
      destruct (cols_l_in_inv _ _ Hxl) as [b Hin].
      assert (Hin' : In (x, b) (ρxL ++ ρnL))
        by (apply in_or_app; right; exact Hin).
      destruct (HρL _ _ Hin') as [Ha _]. clear - Ha Hx. fsetdec. }
    clear - Hd Hscp1. fsetdec. }
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
  assert (Hscp1F : V [<=] ftvar_in_aenv (Ξ1L ++ Θ1))
    by (rewrite ftvar_in_aenv_app; clear - Hscp1; fsetdec).
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
  assert (HbFr : dom Ξ1F ∩ cols_l ρ [=] empty)
    by (clear - HgfF Hscp1; fsetdec).
  assert (HblkF : dom Ξ1F ∩ cols_l (ρxL ++ ρnL ++ ρ) [=] empty)
    by (rewrite ! cols_l_app; clear - HbFx HbFn HbFr; fsetdec).
  assert (HdΘF : dom (Ξ2L ++ Θ2) [<=] S1)
    by (rewrite dom_app; clear - HiL HdΘ HgL; fsetdec).
  assert (HxrS : cols_r ρxL [<=] S1).
  { intros x Hx. destruct (cols_r_in_inv _ _ Hx) as [a Hin].
    assert (Hin' : In (a, x) (ρxL ++ ρnL))
      by (apply in_or_app; left; exact Hin).
    destruct (HρL _ _ Hin') as [_ [Hb _]]. exact Hb. }
  assert (HnrS : cols_r ρnL [<=] S1)
    by (clear - HdfrL HiL; fsetdec).
  assert (Hscp2F : V ∪ cols_r (ρxL ++ ρnL ++ ρ) [<=] S1)
    by (rewrite ! cols_r_app; clear - Hscp2 HgL HxrS HnrS; fsetdec).
  assert (HcovF : ftvar_in_pskl pskl_hole ∪ ftvar_in_a_cstrs C2 [<=] S1).
  { assert (HcC : ftvar_in_a_cstrs C2 [<=] S1)
      by (eapply e_looksub_cstr_ftvar; [ exact DL | clear - Hcov; fsetdec ]).
    simpl. clear - HcC. fsetdec. }
  destruct (a_solve_cstr_rel_e HF (rel_pskl__hole (ρxL ++ ρnL ++ ρ) V) HrC
              HagrF Hscp1F HblkF HdΘF Hscp2F HcovF)
    as (S2 & ρxF & ρnF & Ξ2F & Q2 & DF & E1F & E2F & HρF & HrQ).
  pose proof (e_solve_cstr_supply_grows DF) as HgF.

  (* ---- STEP 3: the guess, §4, at the three-block context ---- *)
  assert (HrQ'' : rel_pskl (ρxF ++ ρnF ++ ρxL ++ ρnL ++ ρ) V Q1 Q2)
    by rel_perm HrQ.
  assert (Hscp1G : V [<=] ftvar_in_aenv (Ξ1F ++ Ξ1L ++ Θ1))
    by (rewrite ! ftvar_in_aenv_app; clear - Hscp1; fsetdec).
  assert (HcovG : V ∪ ftvar_in_pskl Q2 [<=] S2).
  { pose proof (e_solve_cstr_out_ftvar DF) as Hout. simpl in Hout.
    clear - Hout Hscp2 HgL HgF HcovF. fsetdec. }
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
  rel_perm HrQ'.
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
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  dom Θ2 [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] S0 ->
  exists S1 ρx ρn Ξ2 Q2',
    {{ S0 ↝ S1 ⊨ Θ2 ⊢ P2 ⊳[ NM , α , m ] P2' ⤳ Ξ2 ↪ Q2' }}e
    /\ Ξ1 = flex_pairs_l ρn
    /\ Ξ2 = flex_pairs_r ρn
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 /\ b `notin` S0)
    /\ rel_pskl (ρx ++ ρn ++ ρ) V Q1' Q2'.
Proof.
  intros Θ1 NM α m P1 P1' Ξ1 Q1' HD.
  destruct HD as
    [ Θ0 NM0 α0 m0 Ps Ps' ΞL ΞF ΞG C0 Q0 Q0' HL HF HG Hgd ].
  intros S0 Θ2 P2 P2' ρ V HrP HrP' HαV Hαl Hαr Hagr Hscp1 HdΘ Hscp2 Hcov.
  eapply a_extract_rel_e_gen;
    [ exact HL | exact HF | exact HG | exact Hgd
    | exact HrP | exact HrP' | exact HαV | exact Hαl | exact Hαr
    | exact Hagr | exact Hscp1 | exact HdΘ | exact Hscp2 | exact Hcov ].
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
      apply (proj1 (a_flex_tvar_notin_app _ _ Hα'Ξ)). exact Hbig. }
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
      apply a_wf_pskl__var. right. destruct Hfa as [Hb | [t Hb]];
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
      destruct (a_wf_pskl_ftv_tvarish Hwfp Hin) as [HΔ | Htv];
        [ clear - HΔ; fsetdec | ].
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
      destruct (a_wf_pskl_ftv_tvarish Hwfp Hin) as [HΔ | Htv];
        [ clear - HΔ; fsetdec | ].
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
      - apply a_wf_pskl__var. right. exact (Hbt y Hy Hne0). }
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
      by (inversion Hwfp0; subst; assumption).
    assert (Hwfp1 : {{ Θ0 ⨟ empty ⊢ₚₛ P }}a)
      by (inversion Hwfp; subst; assumption).
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
      by (inversion Hwfp; subst; assumption).
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
      by (inversion Hwfp0; subst; assumption).
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
