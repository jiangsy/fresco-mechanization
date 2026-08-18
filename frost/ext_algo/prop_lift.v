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

    ⚙ Either way the conclusion is EXISTENTIAL up to a CHAIN: the [e_]
    derivation's outputs are [swaps_*] images of the [a_] derivation's.

    §1  the [close] rename fact the ∀ rows need
    §2  ⭐ [guess^TY] and its sort wrapper — the SCOUT

    ⛔ §2 IS THE ONLY BLOCK BUILT.  The remaining ten (look, solve, cstr,
    extract, consis, sub, split, pat, typing) are §8c.24's costed plan. *)

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
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.prop_guess.
Require Import src.frost.ext_algo.prop_termination.
Require Import src.frost.ext_algo.prop_solve_det.
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
