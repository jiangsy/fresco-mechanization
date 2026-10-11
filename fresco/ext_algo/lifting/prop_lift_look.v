(** Constraint collection: relational lifting from [a_looksub]/[a_lookeq]
    to the supply-threaded judgements. *)

Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.ltac_utils.
Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_ln.
Require Import src.fresco.def_shapes.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.prop_look.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.

Require Import src.fresco.ext_algo.subtyping.prop_solve_rel.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §7  Transport 5 — the look layer, a → e (the hygienic rederivation)   *)
(* ===================================================================== *)

Local Ltac cstrs_perm H :=
  eapply rel_a_cstrs_mono;
    [ exact H
    | let a0 := fresh "a0" in let b0 := fresh "b0" in
      let Hi := fresh "Hi" in
      intros a0 b0 Hi; revert Hi;
      rewrite ? in_app_iff; simpl; rewrite ? in_app_iff; tauto
    | let x0 := fresh "x0" in let Hx0 := fresh "Hx0" in
      intros x0 Hx0; exact Hx0 ].

(* ---- §7 — transport 5: the look, a → e ---- *)

(** ⭐ TRANSPORT 5 — the look layer, targeting the SUPPLY-THREADED
    encoding: an [a_looksub]/[a_lookeq] derivation transports to an
    [e_looksub]/[e_lookeq] derivation on rel-related inputs, over any
    supply covering side 2's material.  This is §8c.9's HYGIENIC
    REDERIVATION: with reflexive inputs it rederives a raw look with
    pairwise-apart, supply-fresh generated names (the e-side block
    lemmas), the outputs pointwise related at fresh pairs.

    The looked-for [α] stays COMMON: it is in the identity support and
    outside both columns, so LS/LE-Var and LS/LE-Absent land on the same
    rule on side 2 ([rel_pskl_in_id] / [rel_pskl_notin_r]).

    The conclusion's [ρx] collects the LEAKED binder pairs (all five
    ∀-rows leak), [ρn] the LE-FlexR block pairs; side-2 names live in
    [S1 ∖ S0], and the leaked side-2 openers are apart from the side-2
    block ([cols_r ρx ∩ dom Ξ2]) — the facts the b-core's agreement
    extensions read off. *)
Lemma a_looksub_lookeq_rel_e :
  (forall Θ1 α m P1 P1' Ξ1 C1,
     {{ Θ1 ⊢ P1 ≼[ α , m ] P1' ⤳ Ξ1 ⨾ C1 }}a ->
     forall S0 Θ2 P2 P2' ρ V,
     rel_pskl ρ V P1 P2 ->
     rel_pskl ρ V P1' P2' ->
     α `in` V ->
     α `notin` cols_l ρ ->
     α `notin` cols_r ρ ->
     (* ⭐ FLEX AGREEMENT (2026-08-18).  Under the FlexR-PRIORITY GUARD the eq
        layer reads its context for HATTEDNESS — [LE-FlexR] wants the
        counterpart flexible and [LE-UnivGhost2] wants it not — so the two
        sides' contexts must agree about it, on [V] and along ρ.  ⚙ The
        [flex_agree_rel] kit (§ above) is the b-core's, reused verbatim. *)
     flex_agree_rel ρ V Θ1 Θ2 ->
     V ∪ cols_r ρ ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] S0 ->
     exists S1 ρx ρn Ξ2 C2,
       {{ S0 ↝ S1 ⊨ Θ2 ⊢ P2 ≼[ α , m ] P2' ⤳ Ξ2 ⨾ C2 }}e
       /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
       /\ (forall a b, In (a, b) (ρx ++ ρn) ->
             a `notin` add α (ftvar_in_aenv Θ1)
             /\ b `in` S1 /\ b `notin` S0)
       /\ cols_r ρx ∩ dom Ξ2 [=] empty
       /\ (forall a b, In (a, b) ρx -> a `in` ftvar_in_a_cstrs C1)
       /\ cols_l ρx ∩ dom Ξ1 [=] empty
       /\ rel_a_cstrs (ρx ++ ρn ++ ρ) V C1 C2) /\
  (forall Θ1 α P1 P1' Ξ1 C1,
     {{ Θ1 ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}a ->
     forall S0 Θ2 P2 P2' ρ V,
     rel_pskl ρ V P1 P2 ->
     rel_pskl ρ V P1' P2' ->
     α `in` V ->
     α `notin` cols_l ρ ->
     α `notin` cols_r ρ ->
     (* ⭐ FLEX AGREEMENT (2026-08-18).  Under the FlexR-PRIORITY GUARD the eq
        layer reads its context for HATTEDNESS — [LE-FlexR] wants the
        counterpart flexible and [LE-UnivGhost2] wants it not — so the two
        sides' contexts must agree about it, on [V] and along ρ.  ⚙ The
        [flex_agree_rel] kit (§ above) is the b-core's, reused verbatim. *)
     flex_agree_rel ρ V Θ1 Θ2 ->
     V ∪ cols_r ρ ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] S0 ->
     exists S1 ρx ρn Ξ2 C2,
       {{ S0 ↝ S1 ⊨ Θ2 ⊢ P2 ∼[ α ] P2' ⤳ Ξ2 ⨾ C2 }}e
       /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
       /\ (forall a b, In (a, b) (ρx ++ ρn) ->
             a `notin` add α (ftvar_in_aenv Θ1)
             /\ b `in` S1 /\ b `notin` S0)
       /\ cols_r ρx ∩ dom Ξ2 [=] empty
       (* ⭐⭐ THE TWO CONJUNCTS THE EXTRACT RUNG NEEDS (2026-08-19).  The
          fold's [flex_agree_rel] must know a LEAKED OPENER is not flexible
          on SIDE 1 either, and side 1 has no supply to say it with.  The
          first conjunct is what the ∀ rows' case split buys — an opener
          that never surfaces in [𝒞] is DROPPED, by
          [rel_a_cstrs_drop_head] — and it is what lets the ARROW rows'
          cross cases land on the collection's CROSS-HALF FRESHNESS GUARD. *)
       /\ (forall a b, In (a, b) ρx -> a `in` ftvar_in_a_cstrs C1)
       /\ cols_l ρx ∩ dom Ξ1 [=] empty
       /\ rel_a_cstrs (ρx ++ ρn ++ ρ) V C1 C2).
Proof.
  apply a_looksub_lookeq_mutind.
  - (* LS-Var *)
    intros Θ1 α m Pt S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst.
    match goal with
    | Ha : rel_atom ρ V α ?y |- _ =>
        inversion Ha; subst;
        [ exfalso; apply Hαl;
          match goal with
          | Hin : In (α, _) ρ |- _ => exact (cols_l_in _ _ _ Hin)
          end | ]
    end.
    exists S0, nil, nil, nil, (a_cstr_sub m P2' :: nil).
    split; [ apply e_looksub__var | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor; [ constructor; exact HrelP' | constructor ].
  - (* LS-Absent *)
    intros Θ1 α m Ps Pt Habs S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    exists S0, nil, nil, nil, nil.
    split.
    { apply e_looksub__absent.
      eapply rel_pskl_notin_r; [ exact HrelP | exact Habs | exact Hαr ]. }
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor.
  - (* LS-Vacuous *)
    intros Θ1 α m Ps Hne S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP'; subst.
    exists S0, nil, nil, nil, nil.
    split;
      [ apply e_looksub__vacuous;
        eapply rel_pskl_neq_var; [ exact HrelP | exact Hne | exact Hαr ] | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor.
  - (* LS-Check *)
    intros Θ1 α A B Ξ C Hgf Hne HgA HgB Hle IH
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    destruct (IH S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov)
      as (S1 & ρx & ρn & Ξ2 & C2 & D2 & E1 & E2 & Hpairs & Hxb & Hoc2 & Hcl2 & Hrel').
    exists S1, ρx, ρn, Ξ2, C2.
    split.
    { apply e_looksub__check.
      - eapply rel_pskl_ghost_free; [ exact HrelP' | assumption ].
      - intros ->. inversion HrelP; subst.
        match goal with
        | Ha : rel_atom ρ V ?x α |- _ =>
            inversion Ha; subst;
            [ apply Hαr;
              match goal with
              | Hin : In (_, α) ρ |- _ => exact (cols_r_in _ _ _ Hin)
              end
            | exact (Hne eq_refl) ]
        end.
      - eapply rel_pskl_guarded; [ exact HrelP | assumption ].
      - eapply rel_pskl_guarded; [ exact HrelP' | assumption ].
      - exact D2. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hpairs | ]. split; [ exact Hxb | ].
    split; [ exact Hoc2 | ]. split; [ exact Hcl2 | ].
    exact Hrel'.
  - (* LS-ForallR — leaks its opener *)
    intros Θ1 α A B Ξ C β Hgf Hβ1 Hocc Hnv Hprem IH
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP'; subst.
    match goal with
    | Hb : rel_pskl ρ V B ?x |- _ => rename Hb into HrB0; rename x into B2
    end.
    destruct (atom_fresh (S0 ∪ dom Θ2)) as [β2 Hβ2].
    assert (Hag' : flex_agree_rel ((β, β2) :: ρ) V
                     ((β ~ abind_tvar) ++ Θ1) ((β2 ~ abind_tvar) ++ Θ2))
      by (apply flex_agree_rel_push_look;
          [ exact Hag
          | pose proof (dom_subset_ftvar_in_aenv Θ1) as Hdsub;
            clear - Hβ1 Hdsub; fsetdec
          | clear - Hβ2; fsetdec ]).
    assert (Hrelo : rel_pskl ((β, β2) :: ρ) V
                      (open_pskl_wrt_pskl B (pskl_var_f β))
                      (open_pskl_wrt_pskl B2 (pskl_var_f β2)))
      by (apply rel_pskl_open_pair; exact HrB0).
    assert (HrelP2 : rel_pskl ((β, β2) :: ρ) V A P2)
      by (apply rel_pskl_extend_pair; exact HrelP).
    assert (Hαl' : α `notin` cols_l ((β, β2) :: ρ))
      by (simpl; clear - Hαl Hβ1; fsetdec).
    assert (Hαr' : α `notin` cols_r ((β, β2) :: ρ))
      by (simpl; assert (HαS0 : α `in` S0) by (clear - HαV Hcov; fsetdec);
          clear - Hαr Hβ2 HαS0; fsetdec).
    assert (Hcov' : V ∪ cols_r ((β, β2) :: ρ)
                      ∪ ftvar_in_pskl P2
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f β2))
                      [<=] add β2 S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B2
                    (pskl_var_f β2)) as Hup.
      simpl in *. clear - Hcov Hup. fsetdec. }
    destruct (IH (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2) P2
                (open_pskl_wrt_pskl B2 (pskl_var_f β2))
                ((β, β2) :: ρ) V HrelP2 Hrelo HαV Hαl' Hαr' Hag' Hcov')
      as (S1 & ρx & ρn & Ξ2 & C2 & D2 & E1 & E2 & Hpairs & Hxb & Hoc2 & Hcl2 & Hrel').
    pose proof (e_looksub_supply_grows D2) as Hgrow.
    assert (Hd2 : dom Ξ2 ∩ add β2 S0 [=] empty)
      by (apply (proj1 e_looksub_lookeq_block) in D2; tauto).
    (* ⭐ THE OPENER JOINS ρx ONLY IF IT SURFACES IN [𝒞].  One that does not
       is INERT for [rel_a_cstrs] and is dropped — which is what lets the
       conclusion promise [cols_l ρx ∩ dom Ξ [=] empty], and through that
       lets the ARROW rows read the CROSS-HALF FRESHNESS GUARD. *)
    assert (HβΞ : β `notin` dom Ξ).
    { pose proof (a_looksub_binder_not_generated Hprem) as Hbn.
      pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
      clear - Hbn Hds; fsetdec. }
    destruct (AtomSetProperties.In_dec β (ftvar_in_a_cstrs C))
      as [HβC | HβC].
    + exists S1, ((β, β2) :: ρx), ρn, Ξ2, C2.
      split.
      { apply e_looksub__forall_r with (β := β2).
        - eapply rel_pskl_ghost_free; [ exact HrelP' | assumption ].
        - clear - Hβ2; fsetdec.
        - eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ].
        - eapply rel_pskl_neq_var; [ exact HrelP | exact Hnv | exact Hαr ].
        - exact D2. }
      split; [ exact E1 | ]. split; [ exact E2 | ].
      split.
      { intros a b Hin. destruct Hin as [E | Hin].
        - inversion E; subst.
          split; [ clear - Hβ1; fsetdec | ].
          split; [ clear - Hgrow; fsetdec | clear - Hβ2; fsetdec ].
        - destruct (Hpairs a b Hin) as [Ha [Hb1 Hb2]].
          simpl in Ha.
          split; [ clear - Ha; fsetdec | ].
          split; [ exact Hb1 | clear - Hb2; fsetdec ]. }
      split; [ simpl; clear - Hxb Hd2; fsetdec | ].
      split.
      { intros a b Hin. destruct Hin as [E | Hin];
          [ inversion E; subst; exact HβC | exact (Hoc2 a b Hin) ]. }
      split; [ simpl; clear - Hcl2 HβΞ; fsetdec | ].
      cstrs_perm Hrel'.
    + exists S1, ρx, ρn, Ξ2, C2.
      split.
      { apply e_looksub__forall_r with (β := β2).
        - eapply rel_pskl_ghost_free; [ exact HrelP' | assumption ].
        - clear - Hβ2; fsetdec.
        - eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ].
        - eapply rel_pskl_neq_var; [ exact HrelP | exact Hnv | exact Hαr ].
        - exact D2. }
      split; [ exact E1 | ]. split; [ exact E2 | ].
      split.
      { intros a b Hin.
        destruct (Hpairs a b ltac:(apply in_or_app; apply in_app_or in Hin;
                                   tauto)) as [Ha [Hb1 Hb2]].
        simpl in Ha.
        split; [ clear - Ha; fsetdec | ].
        split; [ exact Hb1 | clear - Hb2; fsetdec ]. }
      split; [ exact Hxb | ].
      split; [ exact Hoc2 | ]. split; [ exact Hcl2 | ].
      assert (Hr2 : rel_a_cstrs ((β, β2) :: (ρx ++ ρn ++ ρ)) V C C2)
        by (cstrs_perm Hrel').
      eapply rel_a_cstrs_drop_head; [ exact Hr2 | exact HβC ].
  - (* LS-Arrow *)
    intros Θ1 α m P1 P2q P1' P2q' Ξ1 Ξ2q C1 C2q Hg1 Hg2 Hle IHe Hls IHs
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | Ha : rel_pskl ρ V P1 ?xa, Hb : rel_pskl ρ V P2q ?xb,
      Hc : rel_pskl ρ V P1' ?xc, Hd : rel_pskl ρ V P2q' ?xd |- _ =>
        rename Ha into HrPa; rename Hb into HrPb;
        rename Hc into HrQa; rename Hd into HrQb;
        rename xa into P3a; rename xb into P3b;
        rename xc into Q3a; rename xd into Q3b
    end.
    assert (HcovA : V ∪ cols_r ρ ∪ ftvar_in_pskl P3a ∪ ftvar_in_pskl Q3a
                      [<=] S0)
      by (simpl in Hcov; clear - Hcov; fsetdec).
    destruct (IHe S0 Θ2 P3a Q3a ρ V HrPa HrQa HαV Hαl Hαr Hag HcovA)
      as (S1 & ρxA & ρnA & Ξ2a & C2a & D2a & E1a & E2a & HpairsA & HxbA
          & HocA & HclA & HrelA).
    pose proof (e_lookeq_supply_grows D2a) as HgrowA.
    assert (HcovB : V ∪ cols_r ρ ∪ ftvar_in_pskl P3b ∪ ftvar_in_pskl Q3b
                      [<=] S1)
      by (simpl in Hcov; clear - Hcov HgrowA; fsetdec).
    destruct (IHs S1 Θ2 P3b Q3b ρ V HrPb HrQb HαV Hαl Hαr Hag HcovB)
      as (S2 & ρxB & ρnB & Ξ2b & C2b & D2b & E1b & E2b & HpairsB & HxbB
          & HocB & HclB & HrelB).
    pose proof (e_looksub_supply_grows D2b) as HgrowB.
    assert (Hd2a : dom Ξ2a ∩ S0 [=] empty)
      by (apply (proj2 e_looksub_lookeq_block) in D2a; tauto).
    assert (Hd2ain : dom Ξ2a [<=] S1)
      by (apply (proj2 e_looksub_lookeq_block) in D2a; tauto).
    assert (Hd2b : dom Ξ2b ∩ S1 [=] empty)
      by (apply (proj1 e_looksub_lookeq_block) in D2b; tauto).
    exists S2, (ρxA ++ ρxB), (ρnA ++ ρnB), (Ξ2a ++ Ξ2b), (C2a ++ C2b).
    split; [ eapply e_looksub__arrow; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { intros a b Hin.
      rewrite in_app_iff in Hin.
      rewrite ! in_app_iff in Hin.
      assert (HinA : In (a, b) (ρxA ++ ρnA) \/ In (a, b) (ρxB ++ ρnB))
        by (rewrite ! in_app_iff; tauto).
      destruct HinA as [HinA | HinB].
      - destruct (HpairsA a b HinA) as [Ha [Hb1 Hb2]].
        split; [ exact Ha | ].
        split; [ clear - Hb1 HgrowB; fsetdec | exact Hb2 ].
      - destruct (HpairsB a b HinB) as [Ha [Hb1 Hb2]].
        split; [ exact Ha | ].
        split; [ exact Hb1 | clear - Hb2 HgrowA; fsetdec ]. }
    split.
    { rewrite cols_r_app. rewrite dom_app.
      (* A-rights vs the B block: A ⊆ S1, B avoids S1; and symmetrically *)
      assert (HxAS : cols_r ρxA [<=] S1).
      { intros x Hx.
        destruct (cols_r_in_inv _ _ Hx) as [a Hin].
        destruct (HpairsA a x ltac:(rewrite in_app_iff; left; exact Hin))
          as [_ [Hb1 _]]. exact Hb1. }
      assert (HxBS : cols_r ρxB ∩ S1 [=] empty).
      { apply inter_empty_pointwise. intros x Hx.
        destruct (cols_r_in_inv _ _ Hx) as [a Hin].
        destruct (HpairsB a x ltac:(rewrite in_app_iff; left; exact Hin))
          as [_ [_ Hb2]]. exact Hb2. }
      clear - HxbA HxbB HxAS HxBS Hd2a Hd2ain Hd2b. fsetdec. }
    (* ⭐ THE TWO NEW CONJUNCTS.  (A) is monotone.  (B) is the FOUR-CASE
       analysis, and its two CROSS cases are exactly the collection's
       CROSS-HALF FRESHNESS GUARD: an opener of one half occurring in that
       half's constraints cannot be a block name of the other. *)
    split.
    { intros a b Hin. apply in_app_or in Hin.
      rewrite ftvar_in_a_cstrs_app.
      destruct Hin as [Hin | Hin];
        [ pose proof (HocA a b Hin) | pose proof (HocB a b Hin) ];
        clear - H; fsetdec. }
    split.
    { rewrite cols_l_app, dom_app.
      assert (HxAC : cols_l ρxA [<=] ftvar_in_a_cstrs C1).
      { intros x Hx.
        destruct (cols_l_in_inv _ _ Hx) as [b Hin]. exact (HocA x b Hin). }
      assert (HxBC : cols_l ρxB [<=] ftvar_in_a_cstrs C2q).
      { intros x Hx.
        destruct (cols_l_in_inv _ _ Hx) as [b Hin]. exact (HocB x b Hin). }
      clear - HclA HclB HxAC HxBC Hg1 Hg2. fsetdec. }
    apply Forall2_app.
    + cstrs_perm HrelA.
    + cstrs_perm HrelB.
  - (* LS-ForallL — leaks its opener *)
    intros Θ1 α m Pb Pt Ξ C β Hβ1 Hocc Hnh Hfr3 Hprem IH
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst.
    match goal with
    | Hb : rel_pskl ρ V Pb ?x |- _ => rename Hb into HrP0; rename x into P2b
    end.
    destruct (atom_fresh (S0 ∪ dom Θ2)) as [β2 Hβ2].
    assert (Hag' : flex_agree_rel ((β, β2) :: ρ) V
                     ((β ~ abind_tvar) ++ Θ1) ((β2 ~ abind_tvar) ++ Θ2))
      by (apply flex_agree_rel_push_look;
          [ exact Hag
          | pose proof (dom_subset_ftvar_in_aenv Θ1) as Hdsub;
            clear - Hβ1 Hdsub; fsetdec
          | clear - Hβ2; fsetdec ]).
    assert (Hrelo : rel_pskl ((β, β2) :: ρ) V
                      (open_pskl_wrt_pskl Pb (pskl_var_f β))
                      (open_pskl_wrt_pskl P2b (pskl_var_f β2)))
      by (apply rel_pskl_open_pair; exact HrP0).
    assert (HrelP2' : rel_pskl ((β, β2) :: ρ) V Pt P2')
      by (apply rel_pskl_extend_pair; exact HrelP').
    assert (Hαl' : α `notin` cols_l ((β, β2) :: ρ))
      by (simpl; clear - Hαl Hβ1; fsetdec).
    assert (Hαr' : α `notin` cols_r ((β, β2) :: ρ))
      by (simpl; assert (HαS0 : α `in` S0) by (clear - HαV Hcov; fsetdec);
          clear - Hαr Hβ2 HαS0; fsetdec).
    assert (Hcov' : V ∪ cols_r ((β, β2) :: ρ)
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                      ∪ ftvar_in_pskl P2'
                      [<=] add β2 S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P2b
                    (pskl_var_f β2)) as Hup.
      simpl in *. clear - Hcov Hup. fsetdec. }
    destruct (IH (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (open_pskl_wrt_pskl P2b (pskl_var_f β2)) P2'
                ((β, β2) :: ρ) V Hrelo HrelP2' HαV Hαl' Hαr' Hag' Hcov')
      as (S1 & ρx & ρn & Ξ2 & C2 & D2 & E1 & E2 & Hpairs & Hxb & Hoc2 & Hcl2 & Hrel').
    pose proof (e_looksub_supply_grows D2) as Hgrow.
    assert (Hd2 : dom Ξ2 ∩ add β2 S0 [=] empty)
      by (apply (proj1 e_looksub_lookeq_block) in D2; tauto).
    (* ⭐ THE OPENER JOINS ρx ONLY IF IT SURFACES IN [𝒞] — one that does not
       is INERT for [rel_a_cstrs] and is DROPPED.  That is what lets the
       conclusion promise [cols_l ρx ∩ dom Ξ [=] empty], and through it lets
       the ARROW rows read the CROSS-HALF FRESHNESS GUARD. *)
    assert (HβΞ : β `notin` dom Ξ).
    { assert (Hbn : β `notin` ftvar_in_aenv Ξ)
        by (first [ eapply a_looksub_binder_not_generated; exact Hprem
                  | eapply a_lookeq_binder_not_generated; exact Hprem ]).
      pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
      clear - Hbn Hds; fsetdec. }
    destruct (AtomSetProperties.In_dec β (ftvar_in_a_cstrs C))
      as [HβC | HβC].
    + exists S1, ((β, β2) :: ρx), ρn, Ξ2, C2.
      split.
      { apply e_looksub__forall_l with (β := β2);
          [ clear - Hβ2; fsetdec
          | eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ]
          | eapply rel_pskl_neq_ghost; [ exact HrelP' | exact Hnh ]
          | eapply rel_pskl_forall_r_off; [ exact HrelP' | exact Hfr3 ]
          | exact D2 ]. }
      split; [ exact E1 | ]. split; [ exact E2 | ].
      split.
      { intros a b Hin. destruct Hin as [E | Hin].
        - inversion E; subst.
          split; [ clear - Hβ1; fsetdec | ].
          split; [ clear - Hgrow; fsetdec | clear - Hβ2; fsetdec ].
        - destruct (Hpairs a b Hin) as [Ha [Hb1 Hb2]].
          simpl in Ha.
          split; [ clear - Ha; fsetdec | ].
          split; [ exact Hb1 | clear - Hb2; fsetdec ]. }
      split; [ simpl; clear - Hxb Hd2; fsetdec | ].
      split.
      { intros a b Hin. destruct Hin as [E | Hin];
          [ inversion E; subst; exact HβC | exact (Hoc2 a b Hin) ]. }
      split; [ simpl; clear - Hcl2 HβΞ; fsetdec | ].
      cstrs_perm Hrel'.
    + exists S1, ρx, ρn, Ξ2, C2.
      split.
      { apply e_looksub__forall_l with (β := β2);
          [ clear - Hβ2; fsetdec
          | eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ]
          | eapply rel_pskl_neq_ghost; [ exact HrelP' | exact Hnh ]
          | eapply rel_pskl_forall_r_off; [ exact HrelP' | exact Hfr3 ]
          | exact D2 ]. }
      split; [ exact E1 | ]. split; [ exact E2 | ].
      split.
      { intros a b Hin.
        destruct (Hpairs a b ltac:(apply in_or_app; apply in_app_or in Hin;
                                   tauto)) as [Ha [Hb1 Hb2]].
        simpl in Ha.
        split; [ clear - Ha; fsetdec | ].
        split; [ exact Hb1 | clear - Hb2; fsetdec ]. }
      split; [ exact Hxb | ].
      split; [ exact Hoc2 | ]. split; [ exact Hcl2 | ].
      assert (Hr2 : rel_a_cstrs ((β, β2) :: (ρx ++ ρn ++ ρ)) V C C2)
        by (cstrs_perm Hrel').
      eapply rel_a_cstrs_drop_head; [ exact Hr2 | exact HβC ].
  - (* LS-UnivGhostL *)
    intros Θ1 α m Pb Pt Ξ C Hnh Hfr3 Hprem IH
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst.
    match goal with
    | Hb : rel_pskl ρ V Pb ?x |- _ => rename Hb into HrP0; rename x into P2b
    end.
    assert (Hcov' : V ∪ cols_r ρ ∪ ftvar_in_pskl P2b ∪ ftvar_in_pskl P2'
                      [<=] S0)
      by (simpl in Hcov; clear - Hcov; fsetdec).
    destruct (IH S0 Θ2 P2b P2' ρ V HrP0 HrelP' HαV Hαl Hαr Hag Hcov')
      as (S1 & ρx & ρn & Ξ2 & C2 & D2 & E1 & E2 & Hpairs & Hxb & Hoc2 & Hcl2 & Hrel').
    exists S1, ρx, ρn, Ξ2, C2.
    split;
      [ apply e_looksub__univ_ghost_l;
          [ eapply rel_pskl_neq_ghost; [ exact HrelP' | exact Hnh ]
          | eapply rel_pskl_forall_r_off; [ exact HrelP' | exact Hfr3 ]
          | exact D2 ] | ].
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hpairs | ]. split; [ exact Hxb | ].
    split; [ exact Hoc2 | ]. split; [ exact Hcl2 | ].
    exact Hrel'.
  - (* LE-Var *)
    intros Θ1 α Pt S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst.
    match goal with
    | Ha : rel_atom ρ V α ?y |- _ =>
        inversion Ha; subst;
        [ exfalso; apply Hαl;
          match goal with
          | Hin : In (α, _) ρ |- _ => exact (cols_l_in _ _ _ Hin)
          end | ]
    end.
    exists S0, nil, nil, nil, (a_cstr_eq P2' :: nil).
    split; [ apply e_lookeq__var | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor; [ constructor; exact HrelP' | constructor ].
  - (* LE-Absent *)
    intros Θ1 α Ps Pt Habs S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    exists S0, nil, nil, nil, nil.
    split.
    { apply e_lookeq__absent.
      eapply rel_pskl_notin_r; [ exact HrelP | exact Habs | exact Hαr ]. }
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor.
  - (* LE-Vacuous *)
    intros Θ1 α Ps Hne S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP'; subst.
    exists S0, nil, nil, nil, nil.
    split;
      [ apply e_lookeq__vacuous;
        eapply rel_pskl_neq_var; [ exact HrelP | exact Hne | exact Hαr ] | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor.
  - (* LE-FlexR — the generating row *)
    intros Θ1 α Ps β α1 Hα1 Hflx Hne Hocc
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    pose proof HrelP' as HrelPsaved.
    inversion HrelP'; subst.
    destruct (atom_fresh (S0 ∪ dom Θ2)) as [α1h Hα1h].
    exists (add α1h S0), nil, ((α1, α1h) :: nil),
      ((α1h ~ abind_flex_mono) ++ nil),
      (a_cstr_eq (pskl_var_f α1h) :: nil).
    split.
    { apply e_lookeq__flex_r.
      - clear - Hα1h; fsetdec.
      - (* ⭐ the counterpart's HATTEDNESS transports along the agreement:
           side 2's counterpart is [β]'s image, related either by identity on
           [V] or by a ρ-pair, and [flex_agree_rel] covers both. *)
        inversion HrelPsaved as [ | | ? ? Hra | | | | ]; subst.
        destruct Hra as [ a0 b0 Hin | a0 Hin ];
          [ exact (proj1 (proj2 Hag a0 b0 Hin) Hflx)
          | exact (proj1 (proj1 Hag a0 Hin) Hflx) ].
      - intros ->. inversion HrelP; subst.
        match goal with
        | Ha : rel_atom ρ V ?x α |- _ =>
            inversion Ha; subst;
            [ apply Hαr;
              match goal with
              | Hin : In (_, α) ρ |- _ => exact (cols_r_in _ _ _ Hin)
              end
            | exact (Hne eq_refl) ]
        end.
      - eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ]. }
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split.
    { intros a b Hin. simpl in Hin.
      destruct Hin as [E | Hin]; [ inversion E; subst | inversion Hin ].
      split; [ clear - Hα1; fsetdec | ].
      split; [ clear; fsetdec | clear - Hα1h; fsetdec ]. }
    split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor; [ | constructor ].
    constructor. constructor. apply rel_atom__pair. left. reflexivity.
  - (* LE-Arrow *)
    intros Θ1 α P1 P2q P1' P2q' Ξ1 Ξ2q C1 C2q Hg1 Hg2 Hle1 IH1 Hle2 IH2
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | Ha : rel_pskl ρ V P1 ?xa, Hb : rel_pskl ρ V P2q ?xb,
      Hc : rel_pskl ρ V P1' ?xc, Hd : rel_pskl ρ V P2q' ?xd |- _ =>
        rename Ha into HrPa; rename Hb into HrPb;
        rename Hc into HrQa; rename Hd into HrQb;
        rename xa into P3a; rename xb into P3b;
        rename xc into Q3a; rename xd into Q3b
    end.
    assert (HcovA : V ∪ cols_r ρ ∪ ftvar_in_pskl P3a ∪ ftvar_in_pskl Q3a
                      [<=] S0)
      by (simpl in Hcov; clear - Hcov; fsetdec).
    destruct (IH1 S0 Θ2 P3a Q3a ρ V HrPa HrQa HαV Hαl Hαr Hag HcovA)
      as (S1 & ρxA & ρnA & Ξ2a & C2a & D2a & E1a & E2a & HpairsA & HxbA
          & HocA & HclA & HrelA).
    pose proof (e_lookeq_supply_grows D2a) as HgrowA.
    assert (HcovB : V ∪ cols_r ρ ∪ ftvar_in_pskl P3b ∪ ftvar_in_pskl Q3b
                      [<=] S1)
      by (simpl in Hcov; clear - Hcov HgrowA; fsetdec).
    destruct (IH2 S1 Θ2 P3b Q3b ρ V HrPb HrQb HαV Hαl Hαr Hag HcovB)
      as (S2 & ρxB & ρnB & Ξ2b & C2b & D2b & E1b & E2b & HpairsB & HxbB
          & HocB & HclB & HrelB).
    pose proof (e_lookeq_supply_grows D2b) as HgrowB.
    assert (Hd2a : dom Ξ2a ∩ S0 [=] empty)
      by (apply (proj2 e_looksub_lookeq_block) in D2a; tauto).
    assert (Hd2ain : dom Ξ2a [<=] S1)
      by (apply (proj2 e_looksub_lookeq_block) in D2a; tauto).
    assert (Hd2b : dom Ξ2b ∩ S1 [=] empty)
      by (apply (proj2 e_looksub_lookeq_block) in D2b; tauto).
    exists S2, (ρxA ++ ρxB), (ρnA ++ ρnB), (Ξ2a ++ Ξ2b), (C2a ++ C2b).
    split; [ eapply e_lookeq__arrow; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { intros a b Hin.
      assert (HinA : In (a, b) (ρxA ++ ρnA) \/ In (a, b) (ρxB ++ ρnB))
        by (revert Hin; rewrite ! in_app_iff; tauto).
      destruct HinA as [HinA | HinB].
      - destruct (HpairsA a b HinA) as [Ha [Hb1 Hb2]].
        split; [ exact Ha | ].
        split; [ clear - Hb1 HgrowB; fsetdec | exact Hb2 ].
      - destruct (HpairsB a b HinB) as [Ha [Hb1 Hb2]].
        split; [ exact Ha | ].
        split; [ exact Hb1 | clear - Hb2 HgrowA; fsetdec ]. }
    split.
    { rewrite cols_r_app. rewrite dom_app.
      assert (HxAS : cols_r ρxA [<=] S1).
      { intros x Hx.
        destruct (cols_r_in_inv _ _ Hx) as [a Hin].
        destruct (HpairsA a x ltac:(rewrite in_app_iff; left; exact Hin))
          as [_ [Hb1 _]]. exact Hb1. }
      assert (HxBS : cols_r ρxB ∩ S1 [=] empty).
      { apply inter_empty_pointwise. intros x Hx.
        destruct (cols_r_in_inv _ _ Hx) as [a Hin].
        destruct (HpairsB a x ltac:(rewrite in_app_iff; left; exact Hin))
          as [_ [_ Hb2]]. exact Hb2. }
      clear - HxbA HxbB HxAS HxBS Hd2a Hd2ain Hd2b. fsetdec. }
    (* ⭐ THE TWO NEW CONJUNCTS.  (A) is monotone.  (B) is the FOUR-CASE
       analysis, and its two CROSS cases are exactly the collection's
       CROSS-HALF FRESHNESS GUARD: an opener of one half occurring in that
       half's constraints cannot be a block name of the other. *)
    split.
    { intros a b Hin. apply in_app_or in Hin.
      rewrite ftvar_in_a_cstrs_app.
      destruct Hin as [Hin | Hin];
        [ pose proof (HocA a b Hin) | pose proof (HocB a b Hin) ];
        clear - H; fsetdec. }
    split.
    { rewrite cols_l_app, dom_app.
      assert (HxAC : cols_l ρxA [<=] ftvar_in_a_cstrs C1).
      { intros x Hx.
        destruct (cols_l_in_inv _ _ Hx) as [b Hin]. exact (HocA x b Hin). }
      assert (HxBC : cols_l ρxB [<=] ftvar_in_a_cstrs C2q).
      { intros x Hx.
        destruct (cols_l_in_inv _ _ Hx) as [b Hin]. exact (HocB x b Hin). }
      clear - HclA HclB HxAC HxBC Hg1 Hg2. fsetdec. }
    apply Forall2_app.
    + cstrs_perm HrelA.
    + cstrs_perm HrelB.
  - (* LE-ForallInh — leaks; BOTH sides open at the opener *)
    intros Θ1 α Pb Pb' Ξ C β Hβ1 Hocc Hprem IH
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | Ha : rel_pskl ρ V Pb ?xa, Hb : rel_pskl ρ V Pb' ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    destruct (atom_fresh (S0 ∪ dom Θ2)) as [β2 Hβ2].
    assert (Hag' : flex_agree_rel ((β, β2) :: ρ) V
                     ((β ~ abind_tvar) ++ Θ1) ((β2 ~ abind_tvar) ++ Θ2))
      by (apply flex_agree_rel_push_look;
          [ exact Hag
          | pose proof (dom_subset_ftvar_in_aenv Θ1) as Hdsub;
            clear - Hβ1 Hdsub; fsetdec
          | clear - Hβ2; fsetdec ]).
    assert (Hrelo1 : rel_pskl ((β, β2) :: ρ) V
                      (open_pskl_wrt_pskl Pb (pskl_var_f β))
                      (open_pskl_wrt_pskl P2b (pskl_var_f β2)))
      by (apply rel_pskl_open_pair; exact HrP0).
    assert (Hrelo2 : rel_pskl ((β, β2) :: ρ) V
                      (open_pskl_wrt_pskl Pb' (pskl_var_f β))
                      (open_pskl_wrt_pskl Q2b (pskl_var_f β2)))
      by (apply rel_pskl_open_pair; exact HrQ0).
    assert (Hαl' : α `notin` cols_l ((β, β2) :: ρ))
      by (simpl; clear - Hαl Hβ1; fsetdec).
    assert (Hαr' : α `notin` cols_r ((β, β2) :: ρ))
      by (simpl; assert (HαS0 : α `in` S0) by (clear - HαV Hcov; fsetdec);
          clear - Hαr Hβ2 HαS0; fsetdec).
    assert (Hcov' : V ∪ cols_r ((β, β2) :: ρ)
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                      [<=] add β2 S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P2b
                    (pskl_var_f β2)) as Hup1.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q2b
                    (pskl_var_f β2)) as Hup2.
      simpl in *. clear - Hcov Hup1 Hup2. fsetdec. }
    destruct (IH (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                ((β, β2) :: ρ) V Hrelo1 Hrelo2 HαV Hαl' Hαr' Hag' Hcov')
      as (S1 & ρx & ρn & Ξ2 & C2 & D2 & E1 & E2 & Hpairs & Hxb & Hoc2 & Hcl2 & Hrel').
    pose proof (e_lookeq_supply_grows D2) as Hgrow.
    assert (Hd2 : dom Ξ2 ∩ add β2 S0 [=] empty)
      by (apply (proj2 e_looksub_lookeq_block) in D2; tauto).
    (* ⭐ THE OPENER JOINS ρx ONLY IF IT SURFACES IN [𝒞] — one that does not
       is INERT for [rel_a_cstrs] and is DROPPED.  That is what lets the
       conclusion promise [cols_l ρx ∩ dom Ξ [=] empty], and through it lets
       the ARROW rows read the CROSS-HALF FRESHNESS GUARD. *)
    assert (HβΞ : β `notin` dom Ξ).
    { assert (Hbn : β `notin` ftvar_in_aenv Ξ)
        by (first [ eapply a_looksub_binder_not_generated; exact Hprem
                  | eapply a_lookeq_binder_not_generated; exact Hprem ]).
      pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
      clear - Hbn Hds; fsetdec. }
    destruct (AtomSetProperties.In_dec β (ftvar_in_a_cstrs C))
      as [HβC | HβC].
    + exists S1, ((β, β2) :: ρx), ρn, Ξ2, C2.
      split.
      { apply e_lookeq__forall_inh with (β := β2);
          [ clear - Hβ2; fsetdec
        | eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ]
          | exact D2 ]. }
      split; [ exact E1 | ]. split; [ exact E2 | ].
      split.
      { intros a b Hin. destruct Hin as [E | Hin].
        - inversion E; subst.
          split; [ clear - Hβ1; fsetdec | ].
          split; [ clear - Hgrow; fsetdec | clear - Hβ2; fsetdec ].
        - destruct (Hpairs a b Hin) as [Ha [Hb1 Hb2]].
          simpl in Ha.
          split; [ clear - Ha; fsetdec | ].
          split; [ exact Hb1 | clear - Hb2; fsetdec ]. }
      split; [ simpl; clear - Hxb Hd2; fsetdec | ].
      split.
      { intros a b Hin. destruct Hin as [E | Hin];
          [ inversion E; subst; exact HβC | exact (Hoc2 a b Hin) ]. }
      split; [ simpl; clear - Hcl2 HβΞ; fsetdec | ].
      cstrs_perm Hrel'.
    + exists S1, ρx, ρn, Ξ2, C2.
      split.
      { apply e_lookeq__forall_inh with (β := β2);
          [ clear - Hβ2; fsetdec
        | eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ]
          | exact D2 ]. }
      split; [ exact E1 | ]. split; [ exact E2 | ].
      split.
      { intros a b Hin.
        destruct (Hpairs a b ltac:(apply in_or_app; apply in_app_or in Hin;
                                   tauto)) as [Ha [Hb1 Hb2]].
        simpl in Ha.
        split; [ clear - Ha; fsetdec | ].
        split; [ exact Hb1 | clear - Hb2; fsetdec ]. }
      split; [ exact Hxb | ].
      split; [ exact Hoc2 | ]. split; [ exact Hcl2 | ].
      assert (Hr2 : rel_a_cstrs ((β, β2) :: (ρx ++ ρn ++ ρ)) V C C2)
        by (cstrs_perm Hrel').
      eapply rel_a_cstrs_drop_head; [ exact Hr2 | exact HβC ].
  - (* LE-ForallSyn — leaks; only the SUBJECT opens *)
    intros Θ1 α Pb Pb' Ξ C β Hβ1 Hocc Hprem IH
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | Ha : rel_pskl ρ V Pb ?xa, Hb : rel_pskl ρ V Pb' ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    destruct (atom_fresh (S0 ∪ dom Θ2)) as [β2 Hβ2].
    assert (Hag' : flex_agree_rel ((β, β2) :: ρ) V
                     ((β ~ abind_tvar) ++ Θ1) ((β2 ~ abind_tvar) ++ Θ2))
      by (apply flex_agree_rel_push_look;
          [ exact Hag
          | pose proof (dom_subset_ftvar_in_aenv Θ1) as Hdsub;
            clear - Hβ1 Hdsub; fsetdec
          | clear - Hβ2; fsetdec ]).
    assert (Hrelo1 : rel_pskl ((β, β2) :: ρ) V
                      (open_pskl_wrt_pskl Pb (pskl_var_f β))
                      (open_pskl_wrt_pskl P2b (pskl_var_f β2)))
      by (apply rel_pskl_open_pair; exact HrP0).
    assert (Hrelo2 : rel_pskl ((β, β2) :: ρ) V
                      (pskl_univ_ghost Pb') (pskl_univ_ghost Q2b))
      by (apply rel_pskl_extend_pair; constructor; exact HrQ0).
    assert (Hαl' : α `notin` cols_l ((β, β2) :: ρ))
      by (simpl; clear - Hαl Hβ1; fsetdec).
    assert (Hαr' : α `notin` cols_r ((β, β2) :: ρ))
      by (simpl; assert (HαS0 : α `in` S0) by (clear - HαV Hcov; fsetdec);
          clear - Hαr Hβ2 HαS0; fsetdec).
    assert (Hcov' : V ∪ cols_r ((β, β2) :: ρ)
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                      ∪ ftvar_in_pskl (pskl_univ_ghost Q2b)
                      [<=] add β2 S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P2b
                    (pskl_var_f β2)) as Hup1.
      simpl in *. clear - Hcov Hup1. fsetdec. }
    destruct (IH (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                (pskl_univ_ghost Q2b)
                ((β, β2) :: ρ) V Hrelo1 Hrelo2 HαV Hαl' Hαr' Hag' Hcov')
      as (S1 & ρx & ρn & Ξ2 & C2 & D2 & E1 & E2 & Hpairs & Hxb & Hoc2 & Hcl2 & Hrel').
    pose proof (e_lookeq_supply_grows D2) as Hgrow.
    assert (Hd2 : dom Ξ2 ∩ add β2 S0 [=] empty)
      by (apply (proj2 e_looksub_lookeq_block) in D2; tauto).
    (* ⭐ THE OPENER JOINS ρx ONLY IF IT SURFACES IN [𝒞] — one that does not
       is INERT for [rel_a_cstrs] and is DROPPED.  That is what lets the
       conclusion promise [cols_l ρx ∩ dom Ξ [=] empty], and through it lets
       the ARROW rows read the CROSS-HALF FRESHNESS GUARD. *)
    assert (HβΞ : β `notin` dom Ξ).
    { assert (Hbn : β `notin` ftvar_in_aenv Ξ)
        by (first [ eapply a_looksub_binder_not_generated; exact Hprem
                  | eapply a_lookeq_binder_not_generated; exact Hprem ]).
      pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
      clear - Hbn Hds; fsetdec. }
    destruct (AtomSetProperties.In_dec β (ftvar_in_a_cstrs C))
      as [HβC | HβC].
    + exists S1, ((β, β2) :: ρx), ρn, Ξ2, C2.
      split.
      { apply e_lookeq__forall_syn with (β := β2);
          [ clear - Hβ2; fsetdec
        | eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ]
          | exact D2 ]. }
      split; [ exact E1 | ]. split; [ exact E2 | ].
      split.
      { intros a b Hin. destruct Hin as [E | Hin].
        - inversion E; subst.
          split; [ clear - Hβ1; fsetdec | ].
          split; [ clear - Hgrow; fsetdec | clear - Hβ2; fsetdec ].
        - destruct (Hpairs a b Hin) as [Ha [Hb1 Hb2]].
          simpl in Ha.
          split; [ clear - Ha; fsetdec | ].
          split; [ exact Hb1 | clear - Hb2; fsetdec ]. }
      split; [ simpl; clear - Hxb Hd2; fsetdec | ].
      split.
      { intros a b Hin. destruct Hin as [E | Hin];
          [ inversion E; subst; exact HβC | exact (Hoc2 a b Hin) ]. }
      split; [ simpl; clear - Hcl2 HβΞ; fsetdec | ].
      cstrs_perm Hrel'.
    + exists S1, ρx, ρn, Ξ2, C2.
      split.
      { apply e_lookeq__forall_syn with (β := β2);
          [ clear - Hβ2; fsetdec
        | eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ]
          | exact D2 ]. }
      split; [ exact E1 | ]. split; [ exact E2 | ].
      split.
      { intros a b Hin.
        destruct (Hpairs a b ltac:(apply in_or_app; apply in_app_or in Hin;
                                   tauto)) as [Ha [Hb1 Hb2]].
        simpl in Ha.
        split; [ clear - Ha; fsetdec | ].
        split; [ exact Hb1 | clear - Hb2; fsetdec ]. }
      split; [ exact Hxb | ].
      split; [ exact Hoc2 | ]. split; [ exact Hcl2 | ].
      assert (Hr2 : rel_a_cstrs ((β, β2) :: (ρx ++ ρn ++ ρ)) V C C2)
        by (cstrs_perm Hrel').
      eapply rel_a_cstrs_drop_head; [ exact Hr2 | exact HβC ].
  - (* LE-UnivGhost *)
    intros Θ1 α Pb Pb' Ξ C Hprem IH
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | Ha : rel_pskl ρ V Pb ?xa, Hb : rel_pskl ρ V Pb' ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    assert (Hcov' : V ∪ cols_r ρ ∪ ftvar_in_pskl P2b ∪ ftvar_in_pskl Q2b
                      [<=] S0)
      by (simpl in Hcov; clear - Hcov; fsetdec).
    destruct (IH S0 Θ2 P2b Q2b ρ V HrP0 HrQ0 HαV Hαl Hαr Hag Hcov')
      as (S1 & ρx & ρn & Ξ2 & C2 & D2 & E1 & E2 & Hpairs & Hxb & Hoc2 & Hcl2 & Hrel').
    exists S1, ρx, ρn, Ξ2, C2.
    split; [ apply e_lookeq__univ_ghost; exact D2 | ].
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hpairs | ]. split; [ exact Hxb | ].
    split; [ exact Hoc2 | ]. split; [ exact Hcl2 | ].
    exact Hrel'.
  - (* LE-UnivGhost1 — leaks; only the TARGET opens *)
    intros Θ1 α Pb Pb' Ξ C β Hβ1 Hocc Hprem IH
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | Ha : rel_pskl ρ V Pb ?xa, Hb : rel_pskl ρ V Pb' ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    destruct (atom_fresh (S0 ∪ dom Θ2)) as [β2 Hβ2].
    assert (Hag' : flex_agree_rel ((β, β2) :: ρ) V
                     ((β ~ abind_tvar) ++ Θ1) ((β2 ~ abind_tvar) ++ Θ2))
      by (apply flex_agree_rel_push_look;
          [ exact Hag
          | pose proof (dom_subset_ftvar_in_aenv Θ1) as Hdsub;
            clear - Hβ1 Hdsub; fsetdec
          | clear - Hβ2; fsetdec ]).
    assert (Hrelo1 : rel_pskl ((β, β2) :: ρ) V
                      (pskl_univ_ghost Pb) (pskl_univ_ghost P2b))
      by (apply rel_pskl_extend_pair; constructor; exact HrP0).
    assert (Hrelo2 : rel_pskl ((β, β2) :: ρ) V
                      (open_pskl_wrt_pskl Pb' (pskl_var_f β))
                      (open_pskl_wrt_pskl Q2b (pskl_var_f β2)))
      by (apply rel_pskl_open_pair; exact HrQ0).
    assert (Hαl' : α `notin` cols_l ((β, β2) :: ρ))
      by (simpl; clear - Hαl Hβ1; fsetdec).
    assert (Hαr' : α `notin` cols_r ((β, β2) :: ρ))
      by (simpl; assert (HαS0 : α `in` S0) by (clear - HαV Hcov; fsetdec);
          clear - Hαr Hβ2 HαS0; fsetdec).
    assert (Hcov' : V ∪ cols_r ((β, β2) :: ρ)
                      ∪ ftvar_in_pskl (pskl_univ_ghost P2b)
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                      [<=] add β2 S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q2b
                    (pskl_var_f β2)) as Hup2.
      simpl in *. clear - Hcov Hup2. fsetdec. }
    destruct (IH (add β2 S0) ((β2 ~ abind_tvar) ++ Θ2)
                (pskl_univ_ghost P2b)
                (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                ((β, β2) :: ρ) V Hrelo1 Hrelo2 HαV Hαl' Hαr' Hag' Hcov')
      as (S1 & ρx & ρn & Ξ2 & C2 & D2 & E1 & E2 & Hpairs & Hxb & Hoc2 & Hcl2 & Hrel').
    pose proof (e_lookeq_supply_grows D2) as Hgrow.
    assert (Hd2 : dom Ξ2 ∩ add β2 S0 [=] empty)
      by (apply (proj2 e_looksub_lookeq_block) in D2; tauto).
    (* ⭐ THE OPENER JOINS ρx ONLY IF IT SURFACES IN [𝒞] — one that does not
       is INERT for [rel_a_cstrs] and is DROPPED.  That is what lets the
       conclusion promise [cols_l ρx ∩ dom Ξ [=] empty], and through it lets
       the ARROW rows read the CROSS-HALF FRESHNESS GUARD. *)
    assert (HβΞ : β `notin` dom Ξ).
    { assert (Hbn : β `notin` ftvar_in_aenv Ξ)
        by (first [ eapply a_looksub_binder_not_generated; exact Hprem
                  | eapply a_lookeq_binder_not_generated; exact Hprem ]).
      pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
      clear - Hbn Hds; fsetdec. }
    destruct (AtomSetProperties.In_dec β (ftvar_in_a_cstrs C))
      as [HβC | HβC].
    + exists S1, ((β, β2) :: ρx), ρn, Ξ2, C2.
      split.
      { apply e_lookeq__univ_ghost1 with (β := β2);
          [ clear - Hβ2; fsetdec
        | eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ]
          | exact D2 ]. }
      split; [ exact E1 | ]. split; [ exact E2 | ].
      split.
      { intros a b Hin. destruct Hin as [E | Hin].
        - inversion E; subst.
          split; [ clear - Hβ1; fsetdec | ].
          split; [ clear - Hgrow; fsetdec | clear - Hβ2; fsetdec ].
        - destruct (Hpairs a b Hin) as [Ha [Hb1 Hb2]].
          simpl in Ha.
          split; [ clear - Ha; fsetdec | ].
          split; [ exact Hb1 | clear - Hb2; fsetdec ]. }
      split; [ simpl; clear - Hxb Hd2; fsetdec | ].
      split.
      { intros a b Hin. destruct Hin as [E | Hin];
          [ inversion E; subst; exact HβC | exact (Hoc2 a b Hin) ]. }
      split; [ simpl; clear - Hcl2 HβΞ; fsetdec | ].
      cstrs_perm Hrel'.
    + exists S1, ρx, ρn, Ξ2, C2.
      split.
      { apply e_lookeq__univ_ghost1 with (β := β2);
          [ clear - Hβ2; fsetdec
        | eapply rel_pskl_in_id; [ exact HrelP | exact Hocc | exact Hαl ]
          | exact D2 ]. }
      split; [ exact E1 | ]. split; [ exact E2 | ].
      split.
      { intros a b Hin.
        destruct (Hpairs a b ltac:(apply in_or_app; apply in_app_or in Hin;
                                   tauto)) as [Ha [Hb1 Hb2]].
        simpl in Ha.
        split; [ clear - Ha; fsetdec | ].
        split; [ exact Hb1 | clear - Hb2; fsetdec ]. }
      split; [ exact Hxb | ].
      split; [ exact Hoc2 | ]. split; [ exact Hcl2 | ].
      assert (Hr2 : rel_a_cstrs ((β, β2) :: (ρx ++ ρn ++ ρ)) V C C2)
        by (cstrs_perm Hrel').
      eapply rel_a_cstrs_drop_head; [ exact Hr2 | exact HβC ].
  - (* LE-UnivGhost2 *)
    intros Θ1 α Pb Pt Ξ C Hg Hfx Hprem IH
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP; subst.
    match goal with
    | Ha : rel_pskl ρ V Pb ?xa |- _ =>
        rename Ha into HrP0; rename xa into P2b
    end.
    assert (Hcov' : V ∪ cols_r ρ ∪ ftvar_in_pskl P2b ∪ ftvar_in_pskl P2'
                      [<=] S0)
      by (simpl in Hcov; clear - Hcov; fsetdec).
    destruct (IH S0 Θ2 P2b P2' ρ V HrP0 HrelP' HαV Hαl Hαr Hag Hcov')
      as (S1 & ρx & ρn & Ξ2 & C2 & D2 & E1 & E2 & Hpairs & Hxb & Hoc2 & Hcl2 & Hrel').
    exists S1, ρx, ρn, Ξ2, C2.
    split.
    { apply e_lookeq__univ_ghost2.
      - eapply rel_pskl_guarded; [ exact HrelP' | assumption ].
      - (* ⭐ the guard transports along the agreement, in the OTHER
           direction: side 2's counterpart is flexible only if side 1's is. *)
        intros b Heq Hf. subst P2'.
        inversion HrelP' as [ | | ? ? Hra | | | | ]; subst.
        apply (Hfx _ eq_refl).
        destruct Hra as [ a0 b0 Hin | a0 Hin ];
          [ exact (proj2 (proj2 Hag a0 b0 Hin) Hf)
          | exact (proj2 (proj1 Hag a0 Hin) Hf) ].
      - exact D2. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hpairs | ]. split; [ exact Hxb | ].
    split; [ exact Hoc2 | ]. split; [ exact Hcl2 | ].
    exact Hrel'.
  - (* LE-UnivGhostR *)
    intros Θ1 α Ps Pt Ξ C Hne Hg Hprem IH
      S0 Θ2 P2 P2' ρ V HrelP HrelP' HαV Hαl Hαr Hag Hcov.
    inversion HrelP'; subst.
    match goal with
    | Hb : rel_pskl ρ V Pt ?xb |- _ =>
        rename Hb into HrQ0; rename xb into Q2b
    end.
    assert (Hcov' : V ∪ cols_r ρ ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2b
                      [<=] S0)
      by (simpl in Hcov; clear - Hcov; fsetdec).
    destruct (IH S0 Θ2 P2 Q2b ρ V HrelP HrQ0 HαV Hαl Hαr Hag Hcov')
      as (S1 & ρx & ρn & Ξ2 & C2 & D2 & E1 & E2 & Hpairs & Hxb & Hoc2 & Hcl2 & Hrel').
    exists S1, ρx, ρn, Ξ2, C2.
    split.
    { apply e_lookeq__univ_ghost_r.
      - intros ->. inversion HrelP; subst.
        match goal with
        | Ha : rel_atom ρ V ?x α |- _ =>
            inversion Ha; subst;
            [ apply Hαr;
              match goal with
              | Hin : In (_, α) ρ |- _ => exact (cols_r_in _ _ _ Hin)
              end
            | exact (Hne eq_refl) ]
        end.
      - eapply rel_pskl_guarded; [ exact HrelP | assumption ].
      - exact D2. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hpairs | ]. split; [ exact Hxb | ].
    split; [ exact Hoc2 | ]. split; [ exact Hcl2 | ].
    exact Hrel'.
Qed.
