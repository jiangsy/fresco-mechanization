(** ext_algo — THE LIFT KIT: the relational currency the a ⟹ e lift
    (prop_lift.v, prop_lift_typing.v) is stated in, on top of
    prop_solve_rel.v's four a → a transports.  Section numbers continue
    prop_solve_rel.v's.

    §7   transport 5 — the look layer, a → e (the hygienic rederivation),
         [a_looksub_lookeq_rel_e];
    §8   the CONTEXT relation [rel_aenv] and the atom-set relation;
    §9   the two shape conditions on ρ ([rel_inj] / [rel_fun]) and their
         growth spec [rel_ext];
    §10  the consistency trio's walk kit — the [a_flex_tvar] algebra of
         the context surgery;
    §11  the walk's two remaining moves — the identity pair, and the
         binder-shape algebra the skip rows read;
    §12  the consistency rung's prerequisites;
    §13  what the consistency rung's ∀ rows added; §13c the [a_sub] rung's
         currency; §13d the relation on expressions ([rel_exp], the
         [a_pat] rung). *)

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
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.sub.prop_looksub.
Require Import src.fresco.algo.sub.prop_solve_sub.
Require Import src.fresco.algo.consis.prop_soundness_consis.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.prop_look.
Require Import src.fresco.ext_algo.prop_solve_det.

Require Import src.fresco.ext_algo.prop_solve_rel.

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
  apply (a_looksub_lookeq_mutind
    (fun Θ1 α m P1 P1' Ξ1 C1 _ =>
       forall S0 Θ2 P2 P2' ρ V,
       rel_pskl ρ V P1 P2 ->
       rel_pskl ρ V P1' P2' ->
       α `in` V ->
       α `notin` cols_l ρ ->
       α `notin` cols_r ρ ->
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
         /\ rel_a_cstrs (ρx ++ ρn ++ ρ) V C1 C2)
    (fun Θ1 α P1 P1' Ξ1 C1 _ =>
       forall S0 Θ2 P2 P2' ρ V,
       rel_pskl ρ V P1 P2 ->
       rel_pskl ρ V P1' P2' ->
       α `in` V ->
       α `notin` cols_l ρ ->
       α `notin` cols_r ρ ->
       flex_agree_rel ρ V Θ1 Θ2 ->
       V ∪ cols_r ρ ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] S0 ->
       exists S1 ρx ρn Ξ2 C2,
         {{ S0 ↝ S1 ⊨ Θ2 ⊢ P2 ∼[ α ] P2' ⤳ Ξ2 ⨾ C2 }}e
         /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
         /\ (forall a b, In (a, b) (ρx ++ ρn) ->
               a `notin` add α (ftvar_in_aenv Θ1)
               /\ b `in` S1 /\ b `notin` S0)
         /\ cols_r ρx ∩ dom Ξ2 [=] empty
         /\ (forall a b, In (a, b) ρx -> a `in` ftvar_in_a_cstrs C1)
         /\ cols_l ρx ∩ dom Ξ1 [=] empty
         /\ rel_a_cstrs (ρx ++ ρn ++ ρ) V C1 C2)).
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

(* ===================================================================== *)
(*  §8  ⭐⭐ THE CONTEXT RELATION — what every rung ABOVE the extract needs *)
(*                                                                        *)
(*  [a_extract] and everything below it outputs SKELETONS, so [rel_pskl]   *)
(*  plus [flex_agree_rel] was the whole interface.  [a_consis] and its two *)
(*  companions output a CONTEXT, and the rows READ the payloads —          *)
(*  [Assign-Assign] and [Flex-Flex-Assign] SUBSTITUTE the definition they   *)
(*  find — so the two sides' contexts must be related entry by entry.      *)
(*                                                                        *)
(*  ⭐ [rel_aenv] IS POSITIONAL: the two contexts have the same SHAPE and   *)
(*  their entries correspond pairwise.  That is exactly what the           *)
(*  algorithm's own discipline gives — every rule that grows a context     *)
(*  grows it on both sides at once — and it is what makes the walk rows    *)
(*  ([Assign-Skip] and friends), which peel ONE entry, one [inversion].    *)
(*                                                                        *)
(*  ⚠️ IT DOES NOT SUBSUME [flex_agree_rel], and the two must be CARRIED    *)
(*  TOGETHER.  A left atom may have two right images (§8c.25's Finding 1), *)
(*  so from "entry [i] of [Θ1] is flexible at [a]" one cannot conclude     *)
(*  that [b] is flexible in [Θ2] for an ARBITRARY pair [(a,b)] — only for  *)
(*  the pair that entry [i] itself carries.  Making [rel_aenv] imply the   *)
(*  agreement would need ρ to be a FUNCTION on [dom Θ1], which is the      *)
(*  currency the campaign already retired.                                 *)
(* ===================================================================== *)

(** A [ptyp] is related through its PAINTING — [ptyp_to_pskl] is injective
    ([ptyp_to_pskl_inj]), so nothing is lost, and every [rel_pskl] lemma
    applies without a second inductive. *)
Definition rel_ptyp (ρ : list (atom * atom)) (V : atoms) (A1 A2 : ptyp)
  : Prop := rel_pskl ρ V (ptyp_to_pskl A1) (ptyp_to_pskl A2).

Inductive rel_abind (ρ : list (atom * atom)) (V : atoms) : abind -> abind -> Prop :=
| rel_abind__tvar : rel_abind ρ V abind_tvar abind_tvar
| rel_abind__flex : rel_abind ρ V abind_flex_mono abind_flex_mono
| rel_abind__flex_def : forall τ1 τ2,
    rel_ptyp ρ V τ1 τ2 ->
    rel_abind ρ V (abind_flex_mono_def τ1) (abind_flex_mono_def τ2)
| rel_abind__var_typ : forall A1 A2,
    rel_ptyp ρ V A1 A2 ->
    rel_abind ρ V (abind_var_typ A1) (abind_var_typ A2)
| rel_abind__var_skl : forall Q1 Q2,
    rel_pskl ρ V Q1 Q2 ->
    rel_abind ρ V (abind_var_skl Q1) (abind_var_skl Q2).

Inductive rel_aenv (ρ : list (atom * atom)) (V : atoms) : aenv -> aenv -> Prop :=
| rel_aenv__nil : rel_aenv ρ V nil nil
| rel_aenv__cons : forall a b b1 b2 Θ1 Θ2,
    rel_atom ρ V a b ->
    rel_abind ρ V b1 b2 ->
    rel_aenv ρ V Θ1 Θ2 ->
    rel_aenv ρ V ((a ~ b1) ++ Θ1) ((b ~ b2) ++ Θ2).

#[export] Hint Constructors rel_abind rel_aenv : core.

(** Monotonicity, mirroring [rel_pskl_mono]. *)
Lemma rel_ptyp_mono : forall ρ ρ' V V' A1 A2,
  rel_ptyp ρ V A1 A2 ->
  (forall α β, In (α, β) ρ -> In (α, β) ρ') ->
  V [<=] V' ->
  rel_ptyp ρ' V' A1 A2.
Proof. intros * H Hi Hs; eapply rel_pskl_mono; eauto. Qed.

Lemma rel_abind_mono : forall ρ ρ' V V' b1 b2,
  rel_abind ρ V b1 b2 ->
  (forall α β, In (α, β) ρ -> In (α, β) ρ') ->
  V [<=] V' ->
  rel_abind ρ' V' b1 b2.
Proof.
  intros * H Hi Hs; inversion H; subst; constructor;
    solve [ eapply rel_ptyp_mono; eauto | eapply rel_pskl_mono; eauto ].
Qed.

Lemma rel_aenv_mono : forall ρ ρ' V V' Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 ->
  (forall α β, In (α, β) ρ -> In (α, β) ρ') ->
  V [<=] V' ->
  rel_aenv ρ' V' Θ1 Θ2.
Proof.
  intros * H; induction H; intros Hi Hs; constructor; auto.
  - match goal with
    | Ha : rel_atom _ _ _ _ |- _ =>
        inversion Ha; subst;
        [ apply rel_atom__pair; auto | apply rel_atom__id; fsetdec ]
    end.
  - eapply rel_abind_mono; eauto.
Qed.

Lemma rel_aenv_widen : forall ρn ρ V Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 -> rel_aenv (ρn ++ ρ) V Θ1 Θ2.
Proof.
  intros * H. eapply rel_aenv_mono;
    [ exact H | intros a b Hin; apply in_or_app; right; exact Hin
    | intros x Hx; exact Hx ].
Qed.

(** The two contexts have the same SHAPE, so an append splits on both
    sides at the same place. *)
Lemma rel_aenv_app : forall ρ V Θ1a Θ1b Θ2a Θ2b,
  rel_aenv ρ V Θ1a Θ2a -> rel_aenv ρ V Θ1b Θ2b ->
  rel_aenv ρ V (Θ1a ++ Θ1b) (Θ2a ++ Θ2b).
Proof.
  intros * Ha Hb; induction Ha; simpl; [ exact Hb | ].
  change (((a, b1) :: Θ1) ++ Θ1b) with ((a ~ b1) ++ (Θ1 ++ Θ1b)).
  change (((b, b2) :: Θ2) ++ Θ2b) with ((b ~ b2) ++ (Θ2 ++ Θ2b)).
  constructor; auto.
Qed.

(** ⭐ THE BLOCK PUSH: the two [flex_pairs] blocks of one pair list are
    related along it — what [Assign-SolveM]'s [guess^TY] hands back. *)
Lemma rel_aenv_flex_pairs : forall ρn ρ V,
  rel_aenv (ρn ++ ρ) V (flex_pairs_l ρn) (flex_pairs_r ρn).
Proof.
  intros ρn. induction ρn as [ | [a b] ρn IH ]; intros ρ V; simpl;
    [ constructor | ].
  change ((a, abind_flex_mono) :: flex_pairs_l ρn)
    with ((a ~ abind_flex_mono) ++ flex_pairs_l ρn).
  change ((b, abind_flex_mono) :: flex_pairs_r ρn)
    with ((b ~ abind_flex_mono) ++ flex_pairs_r ρn).
  apply rel_aenv__cons;
    [ apply rel_atom__pair; left; reflexivity
    | apply rel_abind__flex
    | eapply rel_aenv_mono;
        [ apply (IH ρ V)
        | intros x y Hin; right; exact Hin
        | intros x Hx; exact Hx ] ].
Qed.

(** A [binds] on either side finds a partner on the other, at the SAME
    position — this is how the rows read a definition off the context. *)
Lemma rel_aenv_binds_l : forall ρ V Θ1 Θ2 a b1,
  rel_aenv ρ V Θ1 Θ2 ->
  binds a b1 Θ1 ->
  exists b b2, rel_atom ρ V a b /\ rel_abind ρ V b1 b2 /\ binds b b2 Θ2.
Proof.
  intros * H; induction H; intros Hb; [ inversion Hb | ].
  unfold binds in Hb; simpl in Hb; destruct Hb as [Heq | Hb].
  - inversion Heq; subst. exists b, b2. repeat split; try assumption.
    unfold binds; simpl; left; reflexivity.
  - destruct (IHrel_aenv Hb) as (b' & b2' & Hat & Hab & Hbd).
    exists b', b2'. repeat split; try assumption.
    unfold binds in Hbd |- *; simpl; right; exact Hbd.
Qed.

(** ⭐ THE CORRESPONDENCE ON FREE VARIABLES — sharper than [rel_pskl_ftv_r]
    (prop_solve_det.v), which only bounds an ftvar set by [V ∪ cols].
    Every free variable of one side is RELATED to one of the other, which is what
    transports a DISJOINTNESS (the consis rows' [Δ ∩ ftvar P [=] empty]
    guards) across the relation. *)
Lemma rel_pskl_ftv_corr_r : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  forall b, b `in` ftvar_in_pskl P2 ->
  exists a, a `in` ftvar_in_pskl P1 /\ rel_atom ρ V a b.
Proof.
  intros ρ V P1 P2 H; induction H; intros c Hc; simpl in Hc;
    try solve [ exfalso; clear - Hc; fsetdec ].
  - exists α. simpl. split; [ clear; fsetdec | ].
    assert (c = β) by (clear - Hc; fsetdec). subst c. assumption.
  - destruct (AtomSetProperties.In_dec c (ftvar_in_pskl Q1)) as [Hin | Hni].
    + destruct (IHrel_pskl1 c Hin) as (a & Ha & Hat).
      exists a. simpl. split; [ clear - Ha; fsetdec | exact Hat ].
    + destruct (IHrel_pskl2 c ltac:(clear - Hc Hni; fsetdec)) as (a & Ha & Hat).
      exists a. simpl. split; [ clear - Ha; fsetdec | exact Hat ].
  - destruct (IHrel_pskl c Hc) as (a & Ha & Hat).
    exists a. simpl. split; [ exact Ha | exact Hat ].
  - destruct (IHrel_pskl c Hc) as (a & Ha & Hat).
    exists a. simpl. split; [ exact Ha | exact Hat ].
Qed.

Lemma rel_pskl_ftv_corr_l : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  forall a, a `in` ftvar_in_pskl P1 ->
  exists b, b `in` ftvar_in_pskl P2 /\ rel_atom ρ V a b.
Proof.
  intros ρ V P1 P2 H; induction H; intros c Hc; simpl in Hc;
    try solve [ exfalso; clear - Hc; fsetdec ].
  - exists β. simpl. split; [ clear; fsetdec | ].
    assert (c = α) by (clear - Hc; fsetdec). subst c. assumption.
  - destruct (AtomSetProperties.In_dec c (ftvar_in_pskl P1)) as [Hin | Hni].
    + destruct (IHrel_pskl1 c Hin) as (b & Hb & Hat).
      exists b. simpl. split; [ clear - Hb; fsetdec | exact Hat ].
    + destruct (IHrel_pskl2 c ltac:(clear - Hc Hni; fsetdec)) as (b & Hb & Hat).
      exists b. simpl. split; [ clear - Hb; fsetdec | exact Hat ].
  - destruct (IHrel_pskl c Hc) as (b & Hb & Hat).
    exists b. simpl. split; [ exact Hb | exact Hat ].
  - destruct (IHrel_pskl c Hc) as (b & Hb & Hat).
    exists b. simpl. split; [ exact Hb | exact Hat ].
Qed.

(** ⭐⭐ THE Δ RELATION — the consis rows carry two atom SETS of bound
    variables ([Δ1], [Δ2]) and read them ONLY through a disjointness
    ([Ghost]'s [Δ2 ∩ ftvar P0 [=] empty], [GhostR]'s
    [Δ1 ∩ ftvar P [=] empty]).  The three ∀ rows GROW them, with the side-1
    opener on one side and the supply-fresh side-2 opener on the other, so
    the two sets DIFFER and have to be related.  Shape copied from
    [flex_agree_rel]: agreement along the relation. *)
Definition rel_atoms (ρ : list (atom * atom)) (V : atoms) (D1 D2 : atoms)
  : Prop := forall a b, rel_atom ρ V a b -> (a `in` D1 <-> b `in` D2).

Lemma rel_atoms_weaken : forall ρ ρ' V V' D1 D2,
  rel_atoms ρ V D1 D2 ->
  (forall a b, In (a, b) ρ' -> In (a, b) ρ) ->
  V' [<=] V ->
  rel_atoms ρ' V' D1 D2.
Proof.
  intros * H Hincl Hsub a b Hat. apply H.
  inversion Hat; subst;
    [ apply rel_atom__pair; auto | apply rel_atom__id; fsetdec ].
Qed.

(** ⭐ THE TRANSPORT: a disjointness from [Δ] moves across the relation.
    This is what [rel_pskl_ftv_corr_r] exists for. *)
Lemma rel_atoms_disjoint : forall ρ V D1 D2 P1 P2,
  rel_atoms ρ V D1 D2 ->
  rel_pskl ρ V P1 P2 ->
  D1 ∩ ftvar_in_pskl P1 [=] empty ->
  D2 ∩ ftvar_in_pskl P2 [=] empty.
Proof.
  intros * Hd Hr Hdisj.
  apply AtomSetProperties.empty_is_empty_1.
  intros x Hx. apply AtomSetFacts.inter_iff in Hx. destruct Hx as [HxD HxP].
  destruct (rel_pskl_ftv_corr_r Hr HxP) as (a & Ha & Hat).
  assert (HaD : a `in` D1) by (apply (Hd a x Hat); exact HxD).
  clear - Hdisj Ha HaD. fsetdec.
Qed.

(** ⭐ AND THE ∀ ROWS' PUSH.  ⚠️ It needs the two openers OFF the pair
    columns — which is exactly the PAIR RESTRICTION's job (§6), the same
    move the solve layer's ∀ rows make.  Without it a left atom already
    paired elsewhere would land in [add α D1] without its partner landing
    in [add α2 D2]. *)
(** ⚙ Two shape facts about [rel_atom] the push needs, and neither existed:
    peeling one head pair, and locating a related atom in [V ∪ cols]. *)
Lemma rel_atom_cons_inv : forall β1 β2 ρ V a b,
  rel_atom ((β1, β2) :: ρ) V a b ->
  (a = β1 /\ b = β2) \/ rel_atom ρ V a b.
Proof.
  intros * H. inversion H; subst.
  - match goal with
    | Hin : In _ _ |- _ =>
        destruct Hin as [Heq | Hin];
          [ left; inversion Heq; split; reflexivity
          | right; apply rel_atom__pair; exact Hin ]
    end.
  - right. apply rel_atom__id. assumption.
Qed.

Lemma rel_atom_l_in : forall ρ V a b,
  rel_atom ρ V a b -> a `in` V ∪ cols_l ρ.
Proof.
  intros ρ V a b H; inversion H; subst.
  - match goal with
    | Hin : In _ _ |- _ => apply cols_l_in in Hin
    end. fsetdec.
  - fsetdec.
Qed.

Lemma rel_atom_r_in : forall ρ V a b,
  rel_atom ρ V a b -> b `in` V ∪ cols_r ρ.
Proof.
  intros ρ V a b H; inversion H; subst.
  - match goal with
    | Hin : In _ _ |- _ => apply cols_r_in in Hin
    end. fsetdec.
  - fsetdec.
Qed.

Lemma rel_atoms_push : forall ρ V D1 D2 β1 β2,
  rel_atoms ρ V D1 D2 ->
  β1 `notin` V -> β1 `notin` cols_l ρ ->
  β2 `notin` V -> β2 `notin` cols_r ρ ->
  rel_atoms ((β1, β2) :: ρ) V (add β1 D1) (add β2 D2).
Proof.
  intros * Hd Hb1V Hb1c Hb2V Hb2c a b Hat.
  destruct (rel_atom_cons_inv Hat) as [[-> ->] | Hat'].
  - split; intros _; clear; fsetdec.
  - pose proof (rel_atom_l_in Hat') as Hal.
    pose proof (rel_atom_r_in Hat') as Har.
    assert (Hne1 : a <> β1) by (clear - Hal Hb1V Hb1c; fsetdec).
    assert (Hne2 : b <> β2) by (clear - Har Hb2V Hb2c; fsetdec).
    destruct (Hd a b Hat') as [Hf Hg].
    split; intros Hin2.
    + assert (Ha1 : a `in` D1) by (clear - Hin2 Hne1; fsetdec).
      pose proof (Hf Ha1) as Hb2. clear - Hb2. fsetdec.
    + assert (Hb1 : b `in` D2) by (clear - Hin2 Hne2; fsetdec).
      pose proof (Hg Hb1) as Ha2. clear - Ha2. fsetdec.
Qed.

(** ⭐⭐ SHRINKING THE IDENTITY SUPPORT — the ASSIGN WALK's move, and the
    third instance of the same idea as [restrict_pairs] (§6) and
    [rel_atoms_push]'s side conditions.

    ⛔ WHY IT IS FORCED.  The consis ∀ rows need their side-1 opener OFF
    [V], and the only source for that is the rule's own
    [α ∉ ftvar_in_aenv Θ0] — so the transport must carry [V [<=] dom Θ0].
    But the ASSIGN WALK SHRINKS the context: [Assign-Skip] runs its premise
    at the TAIL, with [β] gone, so a [V] tied to the caller's context is too
    big there — and [Assign-Assign] hands that smaller context to a
    CONSISTENCY derivation, whose ∀ rows may then legitimately pick the
    dropped [β] as their opener.

    ⭐ The repair is not to weaken the ∀ rows but to shrink [V] alongside
    the context, which is free exactly when the dropped atom does not occur
    — and [Assign-Skip]'s own premise is [β ∉ ftvar_in_pskl P].  ⚙ Stated
    with an arbitrary [V'] and a USED-PART condition rather than with
    [remove], so one lemma covers every row. *)
Lemma rel_pskl_shrink_V : forall ρ V V' P1 P2,
  rel_pskl ρ V P1 P2 ->
  (forall a, a `in` V -> a `in` ftvar_in_pskl P1 -> a `in` V') ->
  rel_pskl ρ V' P1 P2.
Proof.
  intros ρ V V' P1 P2 H; induction H; intros Hu; simpl in Hu;
    constructor;
    try (apply IHrel_pskl || (apply IHrel_pskl1 + apply IHrel_pskl2));
    try (intros a Ha Hf; apply Hu; [ exact Ha | simpl; clear - Hf; fsetdec ]).
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
  end.
  - apply rel_atom__pair; assumption.
  - apply rel_atom__id. apply Hu; [ assumption | simpl; clear; fsetdec ].
Qed.

Lemma rel_ptyp_shrink_V : forall ρ V V' A1 A2,
  rel_ptyp ρ V A1 A2 ->
  (forall a, a `in` V -> a `in` ftvar_in_ptyp A1 -> a `in` V') ->
  rel_ptyp ρ V' A1 A2.
Proof.
  intros * H Hu. unfold rel_ptyp in *.
  eapply rel_pskl_shrink_V; [ exact H | ].
  intros a Ha Hf. apply Hu; [ exact Ha | ].
  rewrite ftvar_ptyp_to_pskl in Hf. exact Hf.
Qed.

Lemma rel_abind_shrink_V : forall ρ V V' b1 b2,
  rel_abind ρ V b1 b2 ->
  (forall a, a `in` V -> a `in` ftvar_in_abind b1 -> a `in` V') ->
  rel_abind ρ V' b1 b2.
Proof.
  intros * H Hu; inversion H; subst; constructor;
    solve [ eapply rel_ptyp_shrink_V; [ eassumption | exact Hu ]
          | eapply rel_pskl_shrink_V; [ eassumption | exact Hu ] ].
Qed.

Lemma rel_aenv_shrink_V : forall ρ V V' Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 ->
  (forall a, a `in` V -> a `in` dom Θ1 ∪ ftvar_in_aenv Θ1 -> a `in` V') ->
  rel_aenv ρ V' Θ1 Θ2.
Proof.
  intros ρ V V' Θ1 Θ2 H; induction H; intros Hu; [ constructor | ].
  simpl in Hu. constructor.
  - match goal with
    | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
    end.
    + apply rel_atom__pair; assumption.
    + apply rel_atom__id. apply Hu; [ assumption | simpl; clear; fsetdec ].
  - eapply rel_abind_shrink_V; [ eassumption | ].
    intros x Hx Hf. apply Hu; [ exact Hx | simpl; clear - Hf; fsetdec ].
  - apply IHrel_aenv.
    intros x Hx Hf. apply Hu; [ exact Hx | simpl; clear - Hf; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §9  ⭐⭐ THE TWO SHAPE CONDITIONS ON ρ — the TRIO's fourth obstruction *)
(*                                                                        *)
(*  ⛔ THE SOLVE LAYER NEVER READ AN ATOM'S IMAGE BACK.  Everything up to  *)
(*  [a_extract] dispatches on the SHAPE of a skeleton, so an arbitrary    *)
(*  [rel_atom] was all its rows ever asked of a variable.  The trio       *)
(*  dispatches on atom EQUALITY — [Assign-SolveM] and                     *)
(*  [Assign-UnivGhost-Id] fire only when the context HEAD *is* the        *)
(*  subject, [Assign-Skip] only when it is NOT — and both                 *)
(*  [Assign-Assign] and [Flex-Flex-Assign] SUBSTITUTE at the head's atom. *)
(*  A relation alone cannot answer those: with [α] related to two         *)
(*  different right atoms, side 2's head and side 2's subject need not    *)
(*  coincide, and the walk would take a DIFFERENT rule.                   *)
(*                                                                        *)
(*  ⭐ SO ρ NEEDS TWO SHAPE CONDITIONS, and they are of different          *)
(*  strengths on purpose:                                                 *)
(*                                                                        *)
(*    [rel_inj ρ V]     — GLOBAL.  Two left atoms never share a right     *)
(*      image.  True by construction: every right atom is drawn ONCE,     *)
(*      from a supply that only grows, so no two invention events can     *)
(*      produce it.  ⚙ It subsumes [V ∩ cols_r ρ [=] empty], which is the *)
(*      same statement for the identity pairs.                            *)
(*                                                                        *)
(*    [rel_fun ρ V D]   — LOCAL, on a set [D].  A left atom in [D] has    *)
(*      ONE image.  ⚠️ It CANNOT be global: §8c.25's Finding 1 is exactly  *)
(*      a left atom with two right images, and that configuration is      *)
(*      REACHABLE above the extract ([a_extract_rel_e] hands back a ρx    *)
(*      column of leaked openers).  What saves the trio is that a leaked  *)
(*      opener is bound NOWHERE — not in [Θ0], not in [Ξ] — so [D] is     *)
(*      taken to be the CONTEXT's domain, where every pair was created by *)
(*      a row that pushed an entry on BOTH sides at once.                 *)
(* ===================================================================== *)

Definition rel_inj (ρ : list (atom * atom)) (V : atoms) : Prop :=
  forall a1 a2 b, rel_atom ρ V a1 b -> rel_atom ρ V a2 b -> a1 = a2.

Definition rel_fun (ρ : list (atom * atom)) (V : atoms) (D : atoms) : Prop :=
  forall a b1 b2, a `in` D -> rel_atom ρ V a b1 -> rel_atom ρ V a b2 -> b1 = b2.

(** Both are ANTITONE in the pair list — deleting pairs (which is what
    [restrict_pairs] does) can only help — and [rel_fun] is antitone in
    [D] as well. *)
(** ⚙ One inclusion move for [rel_atom], which the two antitonicities and
    every later restriction step share. *)
Lemma rel_atom_incl : forall ρ ρ' V a b,
  rel_atom ρ' V a b ->
  (forall x y, In (x, y) ρ' -> In (x, y) ρ) ->
  rel_atom ρ V a b.
Proof.
  intros ρ ρ' V a b H Hincl. inversion H; subst;
    [ apply rel_atom__pair; apply Hincl; assumption
    | apply rel_atom__id; assumption ].
Qed.

Lemma rel_inj_sub : forall ρ ρ' V,
  rel_inj ρ V ->
  (forall a b, In (a, b) ρ' -> In (a, b) ρ) ->
  rel_inj ρ' V.
Proof.
  intros ρ ρ' V H Hincl a1 a2 b H1 H2.
  exact (H a1 a2 b (rel_atom_incl ρ H1 Hincl) (rel_atom_incl ρ H2 Hincl)).
Qed.

Lemma rel_fun_weaken : forall ρ ρ' V D D',
  rel_fun ρ V D ->
  (forall a b, In (a, b) ρ' -> In (a, b) ρ) ->
  D' [<=] D ->
  rel_fun ρ' V D'.
Proof.
  intros ρ ρ' V D D' H Hincl Hsub a b1 b2 Ha H1 H2.
  exact (H a b1 b2 ltac:(clear - Ha Hsub; fsetdec)
           (rel_atom_incl ρ H1 Hincl) (rel_atom_incl ρ H2 Hincl)).
Qed.

(** ⭐ THE BINDER ROWS' PUSH — and it is the SAME pair of side conditions
    [rel_atoms_push] already asks for, on the same two columns.  Side 2's
    opener misses [V ∪ cols_r ρ] because it is drawn from the supply;
    side 1's misses [V ∪ cols_l ρ] by the rule's freshness together with
    the PAIR RESTRICTION.  ⚙ The fourth appearance of the one idea. *)
Lemma rel_inj_push : forall β1 β2 ρ V,
  rel_inj ρ V ->
  β2 `notin` V ->
  β2 `notin` cols_r ρ ->
  rel_inj ((β1, β2) :: ρ) V.
Proof.
  intros β1 β2 ρ V H Hb2V Hb2c a1 a2 b H1 H2.
  destruct (rel_atom_cons_inv H1) as [[Ea1 Eb1] | H1'];
    destruct (rel_atom_cons_inv H2) as [[Ea2 Eb2] | H2']; subst.
  - reflexivity.
  - exfalso. pose proof (rel_atom_r_in H2') as Hr. clear - Hr Hb2V Hb2c. fsetdec.
  - exfalso. pose proof (rel_atom_r_in H1') as Hr. clear - Hr Hb2V Hb2c. fsetdec.
  - exact (H _ _ _ H1' H2').
Qed.

Lemma rel_fun_push : forall β1 β2 ρ V D,
  rel_fun ρ V D ->
  β1 `notin` V ->
  β1 `notin` cols_l ρ ->
  rel_fun ((β1, β2) :: ρ) V (add β1 D).
Proof.
  intros β1 β2 ρ V D H Hb1V Hb1c a b1 b2 Ha H1 H2.
  destruct (rel_atom_cons_inv H1) as [[Ea Eb] | H1'];
    destruct (rel_atom_cons_inv H2) as [[Ea2 Eb2] | H2']; subst.
  - reflexivity.
  - exfalso. pose proof (rel_atom_l_in H2') as Hl. clear - Hl Hb1V Hb1c. fsetdec.
  - exfalso. pose proof (rel_atom_l_in H1') as Hl. clear - Hl Hb1V Hb1c. fsetdec.
  - assert (Hne : a <> β1).
    { intros Heq. subst a. pose proof (rel_atom_l_in H1') as Hl.
      clear - Hl Hb1V Hb1c. fsetdec. }
    assert (Ha' : a `in` D) by (clear - Ha Hne; fsetdec).
    exact (H a b1 b2 Ha' H1' H2').
Qed.

(** [rel_inj] is what makes an atom's ABSENCE travel backwards: side 2's
    atom is [β2] only if side 1's was [β1]. *)
Lemma rel_atom_inj_eq_r : forall ρ V β1 β2 a,
  rel_inj ρ V ->
  rel_atom ρ V β1 β2 ->
  rel_atom ρ V a β2 ->
  a = β1.
Proof. intros * Hinj H1 H2. exact (Hinj _ _ _ H2 H1). Qed.

(** ⭐⭐ THE SUBSTITUTION TRANSPORT — [Assign-Assign] and
    [Flex-Flex-Assign] both rewrite BOTH of their skeleton slots by the
    definition they found, and the two sides must rewrite at CORRESPONDING
    atoms.  That is precisely "[a = β1] iff [b = β2]" for every related
    pair, i.e. the two conditions above, and it is why they exist. *)
Lemma rel_pskl_subst : forall ρ V P1 P2 T1 T2 β1 β2,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V T1 T2 ->
  rel_atom ρ V β1 β2 ->
  rel_inj ρ V ->
  (forall b, rel_atom ρ V β1 b -> b = β2) ->
  rel_pskl ρ V (subst_pskl_in_pskl T1 β1 P1) (subst_pskl_in_pskl T2 β2 P2).
Proof.
  intros ρ V P1 P2 T1 T2 β1 β2 H HT Hβ Hinj Hfun.
  induction H as [ | n | a b Hat | Pa Pb Qa Qb Ha IHa Hb IHb
                 | Pa Qa Ha IHa | | Pa Qa Ha IHa ]; simpl;
    try solve [ constructor; auto ].
  (* ⚠️ [destruct (a == β1)] does NOT abstract the goal here: [subst_pskl_
     in_pskl] elaborates its [eq_var] at [psklvar], a DEFINITION, so the
     instance term differs from the one [atom] elaborates to — convertible,
     not syntactically equal.  Match the goal instead. *)
  match goal with
  | |- context [ if ?X then _ else _ ] => destruct X as [Heq1 | Hne1]
  end;
  match goal with
  | |- context [ if ?X then _ else _ ] => destruct X as [Heq2 | Hne2]
  end.
  - exact HT.
  - exfalso. subst a. apply Hne2. exact (Hfun _ Hat).
  - exfalso. subst b. apply Hne1. exact (rel_atom_inj_eq_r Hinj Hβ Hat).
  - constructor. exact Hat.
Qed.

(** …and its [ptyp] twin, through the painting. *)
Lemma rel_ptyp_subst : forall ρ V A1 A2 τ1 τ2 β1 β2,
  rel_ptyp ρ V A1 A2 ->
  rel_ptyp ρ V τ1 τ2 ->
  rel_atom ρ V β1 β2 ->
  rel_inj ρ V ->
  (forall b, rel_atom ρ V β1 b -> b = β2) ->
  rel_ptyp ρ V (subst_ptyp_in_ptyp τ1 β1 A1) (subst_ptyp_in_ptyp τ2 β2 A2).
Proof.
  intros ρ V A1 A2 τ1 τ2 β1 β2 H HT Hβ Hinj Hfun. unfold rel_ptyp in *.
  rewrite <- 2 subst_ptyp_to_pskl_comm.
  apply rel_pskl_subst; assumption.
Qed.

(** ⚙ THE WALK'S INVERSION.  Every [Assign-*] / [Flex-Flex-*] row peels ONE
    head off side 1's context; [rel_aenv] is positional, so side 2's context
    peels in lockstep and the row is one [destruct]. *)
Lemma rel_aenv_cons_inv_l : forall ρ V a b1 Θ1 Θ2,
  rel_aenv ρ V ((a ~ b1) ++ Θ1) Θ2 ->
  exists b b2 Θ2',
    Θ2 = (b ~ b2) ++ Θ2'
    /\ rel_atom ρ V a b /\ rel_abind ρ V b1 b2 /\ rel_aenv ρ V Θ1 Θ2'.
Proof.
  intros ρ V a b1 Θ1 Θ2 H. inversion H; subst.
  do 3 eexists.
  split; [ reflexivity | ].
  split; [ eassumption | ].
  split; eassumption.
Qed.

(* --------------------------------------------------------------------- *)
(*  ⚙ THE PAIR RESTRICTION, ON A CONTEXT.  A ∀ row of the trio STRIPS its  *)
(*  opener off the output context, so the conclusion must hand the caller  *)
(*  a relation that no longer speaks about it — and dropping the head      *)
(*  pair is not enough, because by then the row's own generated pairs sit  *)
(*  in FRONT of the opener's.  [restrict_pairs] deletes it wherever it is.    *)
(* --------------------------------------------------------------------- *)

Lemma rel_ptyp_restrict : forall ρ V A1 A2 β1 β2,
  rel_ptyp ρ V A1 A2 ->
  β1 `notin` ftvar_in_ptyp A1 ->
  β2 `notin` ftvar_in_ptyp A2 ->
  rel_ptyp (restrict_pairs β1 β2 ρ) V A1 A2.
Proof.
  intros ρ V A1 A2 β1 β2 H H1 H2. unfold rel_ptyp in *.
  apply rel_pskl_restrict;
    [ exact H
    | rewrite ftvar_ptyp_to_pskl; exact H1
    | rewrite ftvar_ptyp_to_pskl; exact H2 ].
Qed.

Lemma rel_abind_restrict : forall ρ V b1 b2 β1 β2,
  rel_abind ρ V b1 b2 ->
  β1 `notin` ftvar_in_abind b1 ->
  β2 `notin` ftvar_in_abind b2 ->
  rel_abind (restrict_pairs β1 β2 ρ) V b1 b2.
Proof.
  intros ρ V b1 b2 β1 β2 H Hf1 Hf2; inversion H; subst; simpl in Hf1, Hf2;
    constructor;
    solve [ apply rel_ptyp_restrict; assumption
          | apply rel_pskl_restrict; assumption ].
Qed.

Lemma rel_aenv_restrict : forall ρ V Θ1 Θ2 β1 β2,
  rel_aenv ρ V Θ1 Θ2 ->
  β1 `notin` ftvar_in_aenv Θ1 ->
  β2 `notin` ftvar_in_aenv Θ2 ->
  rel_aenv (restrict_pairs β1 β2 ρ) V Θ1 Θ2.
Proof.
  intros ρ V Θ1 Θ2 β1 β2 H; induction H; intros Hf1 Hf2; [ constructor | ].
  simpl in Hf1, Hf2. constructor.
  - match goal with
    | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
    end.
    + apply rel_atom__pair. apply List.filter_In. split; [ assumption | ].
      simpl.
      match goal with
      | |- context [ if ?X then _ else _ ] => destruct X as [Heq | Hne]
      end; [ exfalso; subst; clear - Hf1; fsetdec | ].
      match goal with
      | |- context [ if ?X then _ else _ ] => destruct X as [Heq' | Hne']
      end; [ exfalso; subst; clear - Hf2; fsetdec | ].
      reflexivity.
    + apply rel_atom__id. assumption.
  - apply rel_abind_restrict; [ assumption | clear - Hf1; fsetdec
                              | clear - Hf2; fsetdec ].
  - apply IHrel_aenv; [ clear - Hf1; fsetdec | clear - Hf2; fsetdec ].
Qed.

(* --------------------------------------------------------------------- *)
(*  ⭐⭐ WHAT A ROW HANDS BACK: the pair list it ADDED, and the spec that   *)
(*  lets its caller re-derive [rel_inj] / [rel_fun] at the BIGGER list.    *)
(*                                                                        *)
(*  ⚠️ Neither predicate can simply be carried through as an output        *)
(*  conjunct: both put [rel_atom] in a HYPOTHESIS position, so both are    *)
(*  ANTITONE in ρ and in [V] — a premise that ran at a smaller [V] (the    *)
(*  assign walk's V-shrink) or at a restricted ρ cannot hand them back at  *)
(*  the caller's.  What DOES travel is a statement about the new pairs     *)
(*  alone, and the two derivations below rebuild the predicates from it.   *)
(* --------------------------------------------------------------------- *)

Definition rel_ext (ρe : list (atom * atom)) (W S : atoms) : Prop :=
  (forall a b, In (a, b) ρe -> a `notin` W /\ b `notin` S)
  /\ (forall a1 a2 b, In (a1, b) ρe -> In (a2, b) ρe -> a1 = a2)
  /\ (forall a b1 b2, In (a, b1) ρe -> In (a, b2) ρe -> b1 = b2).

Lemma rel_atom_app_inv : forall ρe ρ V a b,
  rel_atom (ρe ++ ρ) V a b -> In (a, b) ρe \/ rel_atom ρ V a b.
Proof.
  intros ρe ρ V a b H. inversion H; subst.
  - match goal with
    | Hin : In _ (ρe ++ ρ) |- _ =>
        apply in_app_or in Hin; destruct Hin as [Hin | Hin];
          [ left; exact Hin | right; apply rel_atom__pair; exact Hin ]
    end.
  - right. apply rel_atom__id. assumption.
Qed.

Lemma rel_inj_app : forall ρe ρ V W S,
  rel_inj ρ V ->
  rel_ext ρe W S ->
  V ∪ cols_r ρ [<=] S ->
  rel_inj (ρe ++ ρ) V.
Proof.
  intros ρe ρ V W S Hinj [Hfr [Hri _]] Hcov a1 a2 b H1 H2.
  destruct (rel_atom_app_inv ρe ρ H1) as [Hin1 | Hat1];
    destruct (rel_atom_app_inv ρe ρ H2) as [Hin2 | Hat2].
  - exact (Hri _ _ _ Hin1 Hin2).
  - exfalso. destruct (Hfr _ _ Hin1) as [_ Hb].
    pose proof (rel_atom_r_in Hat2) as Hr. clear - Hb Hr Hcov. fsetdec.
  - exfalso. destruct (Hfr _ _ Hin2) as [_ Hb].
    pose proof (rel_atom_r_in Hat1) as Hr. clear - Hb Hr Hcov. fsetdec.
  - exact (Hinj _ _ _ Hat1 Hat2).
Qed.

(** An atom off BOTH the left column and [V] is related to nothing. *)
Lemma rel_atom_off_l : forall ρ V a,
  a `notin` cols_l ρ -> a `notin` V -> forall b, ~ rel_atom ρ V a b.
Proof.
  intros ρ V a Hc Hv b Hat.
  pose proof (rel_atom_l_in Hat) as Hin. clear - Hin Hc Hv. fsetdec.
Qed.

Lemma rel_fun_app : forall ρe ρ V D0 D1 W S,
  rel_fun ρ V D0 ->
  rel_ext ρe W S ->
  D0 [<=] W ->
  (forall a, a `in` D1 -> a `notin` D0 -> a `notin` cols_l ρ) ->
  (forall a, a `in` D1 -> a `notin` D0 -> a `notin` V) ->
  rel_fun (ρe ++ ρ) V D1.
Proof.
  intros ρe ρ V D0 D1 W S Hfun [Hfr [_ Hlf]] Hsub Hnc Hnv a b1 b2 Ha H1 H2.
  destruct (AtomSetProperties.In_dec a D0) as [HaD | HaD].
  - assert (Hnl : a `notin` cols_l ρe).
    { intros Hc. destruct (cols_l_in_inv _ _ Hc) as [y Hin].
      destruct (Hfr _ _ Hin) as [Hna _]. clear - Hna HaD Hsub. fsetdec. }
    assert (Hr1 : rel_atom ρ V a b1).
    { destruct (rel_atom_app_inv ρe ρ H1) as [Hin | Hat]; [ | exact Hat ].
      exfalso. apply Hnl. eapply cols_l_in; exact Hin. }
    assert (Hr2 : rel_atom ρ V a b2).
    { destruct (rel_atom_app_inv ρe ρ H2) as [Hin | Hat]; [ | exact Hat ].
      exfalso. apply Hnl. eapply cols_l_in; exact Hin. }
    exact (Hfun a b1 b2 HaD Hr1 Hr2).
  - pose proof (rel_atom_off_l (Hnc a Ha HaD) (Hnv a Ha HaD)) as Hoff.
    assert (Hin1 : In (a, b1) ρe).
    { destruct (rel_atom_app_inv ρe ρ H1) as [Hin | Hat]; [ exact Hin | ].
      exfalso. exact (Hoff b1 Hat). }
    assert (Hin2 : In (a, b2) ρe).
    { destruct (rel_atom_app_inv ρe ρ H2) as [Hin | Hat]; [ exact Hin | ].
      exfalso. exact (Hoff b2 Hat). }
    exact (Hlf _ _ _ Hin1 Hin2).
Qed.

(* ===================================================================== *)
(*  §10  ⭐⭐ THE TRIO'S WALK KIT — the currency the [a_assign] /           *)
(*       [a_unify] rows consume, and it is NOT the same as §8-§9's        *)
(*                                                                        *)
(*  §8 and §9 are about the RELATION.  The walk rows also need to reason  *)
(*  about the CONTEXT SURGERY itself — an entry is peeled off both sides, *)
(*  a block is deposited, the head goes from undefined to defined — and   *)
(*  every one of those moves is a statement about [a_flex_tvar], which    *)
(*  had no algebra at all.  §10 gives it one:                             *)
(*                                                                        *)
(*    [a_flex_tvar_app_iff]      flexibility distributes over [++]         *)
(*    [a_flex_tvar_one_*]        …at a SINGLETON, which is where the       *)
(*                               binder shapes are read                    *)
(*    [a_flex_tvar_cons_other]   …and hence peeling one entry               *)
(*    [a_flex_tvar_mid_other]    …anywhere under a pending suffix          *)
(*                               (these two in algo/prop_basic.v)          *)
(*    [a_flex_tvar_solve_m]      [Assign-SolveM]'s surgery, in one line    *)
(*                                                                        *)
(*  ⭐⭐ AND THE TWO MOVES EVERY WALK ROW MAKES, factored:                  *)
(*  [flex_agree_peel] takes the agreement DOWN to the tails (with [V]      *)
(*  shrunk so the peeled atom is out of it) and [flex_agree_reattach]      *)
(*  puts the entry back on both sides.  Between them they are what the     *)
(*  four skip rows, [Assign-Assign] and [Flex-Flex-Assign] all do.         *)
(*                                                                        *)
(*  ⚙ What the V-SHRINK needs beyond this — the walk's SUBJECT is          *)
(*  flexible in its own context, so it cannot be the rigid or              *)
(*  term-variable entry a skip row is peeling — ALREADY EXISTS as          *)
(*  [a_assign_unify_subject_flex] (algo/consis/prop_consis_rename.v:334),  *)
(*  next to [a_assign_unify_consis_uniq] (:408).  Neither had a consumer.  *)
(* ===================================================================== *)

Lemma rel_pskl_notin_r_inj : forall ρ V P1 P2 a b,
  rel_pskl ρ V P1 P2 ->
  rel_inj ρ V ->
  rel_atom ρ V a b ->
  a `notin` ftvar_in_pskl P1 ->
  b `notin` ftvar_in_pskl P2.
Proof.
  intros ρ V P1 P2 a b Hr Hinj Hat Ha Hb.
  destruct (rel_pskl_ftv_corr_r Hr Hb) as (a0 & Ha0 & Hat0).
  assert (a0 = a) by (exact (Hinj a0 a b Hat0 Hat)). subst a0. contradiction.
Qed.

Lemma rel_ptyp_mono_ptyp : forall ρ V A1 A2,
  rel_ptyp ρ V A1 A2 -> mono_ptyp A1 -> mono_ptyp A2.
Proof.
  intros ρ V A1 A2 H Hm. unfold rel_ptyp in H.
  generalize dependent A2.
  induction Hm as [ | a | B1 B2 Hm1 IH1 Hm2 IH2 ]; intros C H;
    destruct C; simpl in H;
    try solve [ inversion H ];
    try solve [ constructor ].
  inversion H; subst. constructor;
    [ eapply IH1; eassumption | eapply IH2; eassumption ].
Qed.

Lemma nodup_snd_inj : forall (ρ : list (atom * atom)) a1 a2 b,
  NoDup (List.map snd ρ) -> In (a1, b) ρ -> In (a2, b) ρ -> a1 = a2.
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros a1 a2 b Hnd H1 H2;
    [ contradiction | ].
  simpl in Hnd. inversion Hnd as [ | z l Hni Hnd' ]; subst.
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - injection E1 as Ex1 Ey1. injection E2 as Ex2 Ey2. subst. reflexivity.
  - exfalso. injection E1 as Ex1 Ey1. apply Hni. rewrite Ey1.
    exact (List.in_map snd ρ (a2, b) H2).
  - exfalso. injection E2 as Ex2 Ey2. apply Hni. rewrite Ey2.
    exact (List.in_map snd ρ (a1, b) H1).
  - exact (IH _ _ _ Hnd' H1 H2).
Qed.

Lemma nodup_fst_fun : forall (ρ : list (atom * atom)) a b1 b2,
  NoDup (List.map fst ρ) -> In (a, b1) ρ -> In (a, b2) ρ -> b1 = b2.
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros a b1 b2 Hnd H1 H2;
    [ contradiction | ].
  simpl in Hnd. inversion Hnd as [ | z l Hni Hnd' ]; subst.
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - injection E1 as Ex1 Ey1. injection E2 as Ex2 Ey2. subst. reflexivity.
  - exfalso. injection E1 as Ex1 Ey1. apply Hni. rewrite Ex1.
    exact (List.in_map fst ρ (a, b2) H2).
  - exfalso. injection E2 as Ex2 Ey2. apply Hni. rewrite Ex2.
    exact (List.in_map fst ρ (a, b1) H1).
  - exact (IH _ _ _ Hnd' H1 H2).
Qed.

(** An entry list of UNDEFINED flexibles is flexible exactly on its domain. *)
Lemma a_flex_tvar_decls : forall Ξ x,
  a_decls Ξ -> (a_flex_tvar Ξ x <-> x `in` dom Ξ).
Proof.
  intros Ξ x H; induction H as [ | α1 Ξ H IH ]; split.
  - intros [Hb | [t Hb]]; inversion Hb.
  - simpl; intros Hx; exfalso; clear - Hx; fsetdec.
  - rewrite a_flex_tvar_app_iff. intros [Hh | Ht]; simpl.
    + assert (Hx : x = α1).
      { destruct Hh as [Hb | [t Hb]]; unfold binds in Hb; simpl in Hb;
          destruct Hb as [E | E]; try contradiction; inversion E; reflexivity. }
      subst; clear; fsetdec.
    + apply IH in Ht. clear - Ht. fsetdec.
  - intros Hx; simpl in Hx. rewrite a_flex_tvar_app_iff.
    destruct (x == α1) as [-> | Hne].
    + left. left. unfold binds; simpl; left; reflexivity.
    + right. apply IH. clear - Hx Hne. fsetdec.
Qed.


Lemma a_flex_tvar_one_flex : forall α (b : abind) x,
  (b = abind_flex_mono \/ exists t, b = abind_flex_mono_def t) ->
  (a_flex_tvar (α ~ b) x <-> x = α).
Proof.
  intros α b x Hb. split.
  - intros [Hbd | [t Hbd]]; unfold binds in Hbd; simpl in Hbd;
      destruct Hbd as [E | E]; try contradiction; inversion E; reflexivity.
  - intros ->. destruct Hb as [-> | [t ->]];
      [ left | right; exists t ]; unfold binds; simpl; left; reflexivity.
Qed.

(** ⭐ [Assign-SolveM]'s context surgery, as seen by FLEXIBILITY: the head
    goes from undefined to defined (both flexible), and the guess's block is
    new — so outside [dom βs] nothing moves. *)
Lemma a_flex_tvar_solve_m : forall α (τ : ptyp) βs Ξ Θ0 x,
  x `notin` dom βs ->
  (a_flex_tvar ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0) x
   <-> a_flex_tvar (Ξ ++ (α ~ abind_flex_mono) ++ Θ0) x).
Proof.
  intros α τ βs Ξ Θ0 x Hx.
  rewrite ! a_flex_tvar_app_iff.
  rewrite (@a_flex_tvar_one_flex α (abind_flex_mono_def τ) x
             ltac:(right; exists τ; reflexivity)).
  rewrite (@a_flex_tvar_one_flex α abind_flex_mono x
             ltac:(left; reflexivity)).
  assert (Hnb := fun Hf => Hx (a_flex_tvar_in_dom Hf)).
  tauto.
Qed.

Lemma a_decls_flex_pairs_l : forall ρ, a_decls (flex_pairs_l ρ).
Proof.
  induction ρ as [ | [a b] ρ IH ]; simpl; [ constructor | ].
  change ((a, abind_flex_mono) :: flex_pairs_l ρ)
    with ((a ~ abind_flex_mono) ++ flex_pairs_l ρ).
  constructor. exact IH.
Qed.

Lemma a_decls_flex_pairs_r : forall ρ, a_decls (flex_pairs_r ρ).
Proof.
  induction ρ as [ | [a b] ρ IH ]; simpl; [ constructor | ].
  change ((b, abind_flex_mono) :: flex_pairs_r ρ)
    with ((b ~ abind_flex_mono) ++ flex_pairs_r ρ).
  constructor. exact IH.
Qed.

Lemma rel_aenv_dom_r_inv : forall ρ V Θ1 Θ2 b,
  rel_aenv ρ V Θ1 Θ2 -> b `in` dom Θ2 ->
  exists a, a `in` dom Θ1 /\ rel_atom ρ V a b.
Proof.
  intros ρ V Θ1 Θ2 b H; induction H; intros Hb; simpl in Hb;
    [ exfalso; clear - Hb; fsetdec | ].
  destruct (b == b0) as [-> | Hne].
  - exists a. split; [ simpl; clear; fsetdec | assumption ].
  - destruct (IHrel_aenv ltac:(clear - Hb Hne; fsetdec)) as (x & Hx & Hat).
    exists x. split; [ simpl; clear - Hx; fsetdec | exact Hat ].
Qed.

Lemma rel_aenv_dom_l_inv : forall ρ V Θ1 Θ2 a,
  rel_aenv ρ V Θ1 Θ2 -> a `in` dom Θ1 ->
  exists b, b `in` dom Θ2 /\ rel_atom ρ V a b.
Proof.
  intros ρ V Θ1 Θ2 a H; induction H; intros Ha; simpl in Ha;
    [ exfalso; clear - Ha; fsetdec | ].
  destruct (a == a0) as [-> | Hne].
  - exists b. split; [ simpl; clear; fsetdec | assumption ].
  - destruct (IHrel_aenv ltac:(clear - Ha Hne; fsetdec)) as (y & Hy & Hat).
    exists y. split; [ simpl; clear - Hy; fsetdec | exact Hat ].
Qed.

Lemma rel_atom_mono_V : forall ρ V V' a b,
  rel_atom ρ V' a b -> V' [<=] V -> rel_atom ρ V a b.
Proof.
  intros ρ V V' a b H Hs; inversion H; subst;
    [ apply rel_atom__pair; assumption | apply rel_atom__id; fsetdec ].
Qed.

Lemma rel_inj_weaken_V : forall ρ V V',
  rel_inj ρ V -> V' [<=] V -> rel_inj ρ V'.
Proof.
  intros ρ V V' H Hs a1 a2 b H1 H2.
  exact (H a1 a2 b (rel_atom_mono_V H1 Hs) (rel_atom_mono_V H2 Hs)).
Qed.

Lemma rel_fun_weaken_V : forall ρ V V' D,
  rel_fun ρ V D -> V' [<=] V -> rel_fun ρ V' D.
Proof.
  intros ρ V V' D H Hs a b1 b2 Ha H1 H2.
  exact (H a b1 b2 Ha (rel_atom_mono_V H1 Hs) (rel_atom_mono_V H2 Hs)).
Qed.

Lemma flex_agree_rel_use : forall ρ V Θ1 Θ2 a b,
  flex_agree_rel ρ V Θ1 Θ2 ->
  rel_atom ρ V a b ->
  (a_flex_tvar Θ1 a <-> a_flex_tvar Θ2 b).
Proof.
  intros ρ V Θ1 Θ2 a b [HV Hp] Hat.
  inversion Hat as [x y Hin | x Hv]; subst.
  - exact (Hp _ _ Hin).
  - exact (HV _ Hv).
Qed.

Lemma a_flex_tvar_head_flexish : forall (c : atom) (bd : abind) (Θ : aenv),
  (bd = abind_flex_mono \/ exists t, bd = abind_flex_mono_def t) ->
  a_flex_tvar ((c ~ bd) ++ Θ) c.
Proof.
  intros c bd Θ [-> | [t ->]];
    [ left | right; exists t ]; unfold binds; simpl; left; reflexivity.
Qed.

Lemma a_decls_one : forall (α : atom), a_decls (α ~ abind_flex_mono).
Proof. intros α. simpl_env. constructor. constructor. Qed.

(** ⭐⭐ THE WALK'S FLEX-AGREEMENT SURGERY, factored — every skip row and
    [Assign-Assign] make exactly these two moves.  [_peel] takes the
    agreement DOWN to the tails (with [V] shrunk so the peeled atom is out
    of it); [_reattach] puts the entry back on both sides. *)
Lemma flex_agree_peel : forall ρ V V' Ξ Ξ' Θ0 Θ0'' (β b : atom) bd bd',
  flex_agree_rel ρ V (Ξ ++ (β ~ bd) ++ Θ0) (Ξ' ++ (b ~ bd') ++ Θ0'') ->
  rel_atom ρ V β b ->
  rel_inj ρ V ->
  (forall y, rel_atom ρ V β y -> y = b) ->
  β `notin` dom (Ξ ++ Θ0) ->
  b `notin` dom (Ξ' ++ Θ0'') ->
  V' [<=] V ->
  (forall x, x `in` V' -> x <> β) ->
  flex_agree_rel ρ V' (Ξ ++ Θ0) (Ξ' ++ Θ0'').
Proof.
  intros ρ V V' Ξ Ξ' Θ0 Θ0'' β b bd bd' Hagr Hab Hinj Hβfun Hβnd Hbnd HV Hne.
  split.
  - intros x HxV'.
    assert (HxV : x `in` V) by (clear - HxV' HV; fsetdec).
    pose proof (Hne x HxV') as Hnb.
    assert (Hnb2 : x <> b).
    { intros Ey. apply Hnb. rewrite Ey in HxV |- *. symmetry.
      exact (Hinj β b b Hab (@rel_atom__id ρ V b HxV)). }
    pose proof (proj1 Hagr x HxV) as Hx0.
    rewrite (@a_flex_tvar_mid_other Ξ β bd Θ0 x Hnb) in Hx0.
    rewrite (@a_flex_tvar_mid_other Ξ' b bd' Θ0'' x Hnb2) in Hx0.
    exact Hx0.
  - intros x y Hin.
    pose proof (proj2 Hagr x y Hin) as Hxy.
    destruct (x == β) as [Exβ | Hnb].
    + assert (Ey : y = b)
        by (apply Hβfun; rewrite <- Exβ; apply rel_atom__pair; exact Hin).
      rewrite Exβ, Ey.
      split; intros Hf; exfalso;
        [ exact (Hβnd (a_flex_tvar_in_dom Hf))
        | exact (Hbnd (a_flex_tvar_in_dom Hf)) ].
    + assert (Hnb2 : y <> b).
      { intros Ey. apply Hnb. rewrite Ey in Hin.
        exact (Hinj x β b (@rel_atom__pair ρ V x b Hin) Hab). }
      rewrite (@a_flex_tvar_mid_other Ξ β bd Θ0 x Hnb) in Hxy.
      rewrite (@a_flex_tvar_mid_other Ξ' b bd' Θ0'' y Hnb2) in Hxy.
      exact Hxy.
Qed.

Lemma flex_agree_reattach : forall ρ' V V' Θ1 Θ1' (β b : atom) bd bd',
  flex_agree_rel ρ' V' Θ1 Θ1' ->
  rel_atom ρ' V β b ->
  rel_inj ρ' V ->
  (forall y, rel_atom ρ' V β y -> y = b) ->
  (forall x, x `in` V -> x <> β -> x `in` V') ->
  (β `in` V -> b = β) ->
  (a_flex_tvar ((β ~ bd) ++ Θ1) β <-> a_flex_tvar ((b ~ bd') ++ Θ1') b) ->
  flex_agree_rel ρ' V ((β ~ bd) ++ Θ1) ((b ~ bd') ++ Θ1').
Proof.
  intros ρ' V V' Θ1 Θ1' β b bd bd' Hagr Hab Hinj Hβfun Hsplit Hβb Hhead.
  split.
  - intros x HxV. destruct (x == β) as [Ex | Hnb].
    + rewrite Ex in HxV |- *. pose proof (Hβb HxV) as Eb.
      rewrite Eb in Hhead. rewrite Eb. exact Hhead.
    + assert (Hnb2 : x <> b).
      { intros Ey. apply Hnb. rewrite Ey in HxV |- *. symmetry.
        exact (Hinj β b b Hab (@rel_atom__id ρ' V b HxV)). }
      rewrite (@a_flex_tvar_cons_other β bd Θ1 x Hnb).
      rewrite (@a_flex_tvar_cons_other b bd' Θ1' x Hnb2).
      apply (proj1 Hagr x). apply Hsplit; assumption.
  - intros x y Hin.
    destruct (x == β) as [Exβ | Hnb].
    + assert (Ey : y = b)
        by (apply Hβfun; rewrite <- Exβ; apply rel_atom__pair; exact Hin).
      rewrite Exβ, Ey. exact Hhead.
    + assert (Hnb2 : y <> b).
      { intros Ey. apply Hnb. rewrite Ey in Hin.
        exact (Hinj x β b (@rel_atom__pair ρ' V x b Hin) Hab). }
      rewrite (@a_flex_tvar_cons_other β bd Θ1 x Hnb).
      rewrite (@a_flex_tvar_cons_other b bd' Θ1' y Hnb2).
      exact (proj2 Hagr x y Hin).
Qed.

(* ===================================================================== *)
(*  §11  ⭐⭐ THE WALK'S TWO REMAINING MOVES — the IDENTITY PAIR, and the   *)
(*       binder-shape algebra the skip rows read                          *)
(*                                                                        *)
(*  ⛔ [Assign-SkipTmVar] (both sorts) peels an entry with NO              *)
(*  [x ∉ ftvar_in_pskl P] premise — unlike [Assign-Skip] and              *)
(*  [Assign-SkipRigid], which have one — so the V-SHRINK cannot            *)
(*  re-establish [rel_pskl ρ V' P P'] by freshness there.                  *)
(*                                                                        *)
(*  ⭐ THE REPAIR, and it is the same DELETE-don't-strengthen move one     *)
(*  more time, run backwards: [V] keeps [x] as an IDENTITY PAIR while the  *)
(*  premise runs, and the pair is deleted again at the conclusion, where   *)
(*  it is redundant.  It is legal exactly because [rel_fun] forces side    *)
(*  2's head to be [x] as well whenever [x ∈ V] — and when [x ∉ V] there   *)
(*  is nothing to shrink at all, which is the row's other branch.          *)
(*                                                                        *)
(*  ⚙ The rest is the binder-shape algebra: a NON-flexish singleton is     *)
(*  flexible at nothing ([_one_nonflex], [_cons_absent]), a rigid mid      *)
(*  entry is not flexible at itself ([_mid_nonflex_absurd] — what gives    *)
(*  [α <> β] at the rows that carry no such premise), and swapping a       *)
(*  flexish head for another is invisible to the agreement                 *)
(*  ([_head_swap_flexish], [flex_agree_rel_head_swap] — [Flex-Flex-L/R]'s  *)
(*  whole output move).                                                    *)
(* ===================================================================== *)

Lemma rel_pskl_shrink_V_id : forall ρ V V' P1 P2 x,
  rel_pskl ρ V P1 P2 ->
  (forall a, a `in` V -> a `in` ftvar_in_pskl P1 -> a = x \/ a `in` V') ->
  rel_pskl ((x, x) :: ρ) V' P1 P2.
Proof.
  intros ρ V V' P1 P2 x H; induction H; intros Hu; simpl in Hu;
    constructor;
    try (apply IHrel_pskl || (apply IHrel_pskl1 + apply IHrel_pskl2));
    try (intros a Ha Hf; apply Hu; [ exact Ha | simpl; clear - Hf; fsetdec ]).
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
  end.
  - apply rel_atom__pair. right. assumption.
  - match goal with
    | Hv : ?a `in` V |- _ =>
        destruct (Hu a Hv ltac:(simpl; clear; fsetdec)) as [Ex | HV']
    end.
    + subst. apply rel_atom__pair. left. reflexivity.
    + apply rel_atom__id. exact HV'.
Qed.

(** …and the pair leaves again: at an atom of [V] an identity pair says
    nothing [rel_atom__id] does not already say. *)
Lemma rel_atom_drop_id : forall ρa ρb V x a b,
  rel_atom (ρa ++ (x, x) :: ρb) V a b ->
  x `in` V ->
  rel_atom (ρa ++ ρb) V a b.
Proof.
  intros ρa ρb V x a b H Hx.
  inversion H as [x0 y0 Hin | x0 Hv]; subst.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply rel_atom__pair. apply in_or_app. left. exact Hin.
    + destruct Hin as [E | Hin].
      * inversion E; subst. apply rel_atom__id. exact Hx.
      * apply rel_atom__pair. apply in_or_app. right. exact Hin.
  - apply rel_atom__id. assumption.
Qed.

Lemma rel_pskl_drop_id : forall ρa ρb V x P1 P2,
  rel_pskl (ρa ++ (x, x) :: ρb) V P1 P2 ->
  x `in` V ->
  rel_pskl (ρa ++ ρb) V P1 P2.
Proof.
  intros ρa ρb V x P1 P2 H Hx.
  remember (ρa ++ (x, x) :: ρb) as ρ eqn:Eρ.
  induction H; subst; constructor; auto.
  eapply rel_atom_drop_id; [ eassumption | exact Hx ].
Qed.

Lemma rel_ptyp_drop_id : forall ρa ρb V x A1 A2,
  rel_ptyp (ρa ++ (x, x) :: ρb) V A1 A2 ->
  x `in` V ->
  rel_ptyp (ρa ++ ρb) V A1 A2.
Proof.
  intros * H Hx. unfold rel_ptyp in *. eapply rel_pskl_drop_id; eauto.
Qed.

Lemma rel_abind_drop_id : forall ρa ρb V x b1 b2,
  rel_abind (ρa ++ (x, x) :: ρb) V b1 b2 ->
  x `in` V ->
  rel_abind (ρa ++ ρb) V b1 b2.
Proof.
  intros * H Hx; inversion H; subst; constructor;
    solve [ eapply rel_ptyp_drop_id; eauto | eapply rel_pskl_drop_id; eauto ].
Qed.

Lemma rel_aenv_drop_id : forall ρa ρb V x Θ1 Θ2,
  rel_aenv (ρa ++ (x, x) :: ρb) V Θ1 Θ2 ->
  x `in` V ->
  rel_aenv (ρa ++ ρb) V Θ1 Θ2.
Proof.
  intros ρa ρb V x Θ1 Θ2 H Hx.
  remember (ρa ++ (x, x) :: ρb) as ρ eqn:Eρ.
  induction H; subst; constructor; auto.
  - eapply rel_atom_drop_id; [ eassumption | exact Hx ].
  - eapply rel_abind_drop_id; [ eassumption | exact Hx ].
Qed.

Lemma a_flex_tvar_one_nonflex : forall (c : atom) (bd : abind) x,
  bd <> abind_flex_mono ->
  (forall t, bd <> abind_flex_mono_def t) ->
  ~ a_flex_tvar (c ~ bd) x.
Proof.
  intros c bd x H1 H2 [Hb | [t Hb]]; unfold binds in Hb; simpl in Hb;
    destruct Hb as [E | E]; try contradiction; inversion E; subst.
  - apply H1; reflexivity.
  - apply (H2 t); reflexivity.
Qed.

Lemma a_flex_tvar_cons_absent : forall (c : atom) (bd : abind) (Θ : aenv) x,
  bd <> abind_flex_mono ->
  (forall t, bd <> abind_flex_mono_def t) ->
  x `notin` dom Θ ->
  ~ a_flex_tvar ((c ~ bd) ++ Θ) x.
Proof.
  intros c bd Θ x H1 H2 Hx Hf. rewrite a_flex_tvar_app_iff in Hf.
  destruct Hf as [Hf | Hf];
    [ exact (@a_flex_tvar_one_nonflex c bd x H1 H2 Hf)
    | exact (Hx (a_flex_tvar_in_dom Hf)) ].
Qed.

Lemma flex_agree_rel_push_id_absent : forall ρ V x Θ1 Θ2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  x `notin` dom Θ1 -> x `notin` dom Θ2 ->
  flex_agree_rel ((x, x) :: ρ) V Θ1 Θ2.
Proof.
  intros ρ V x Θ1 Θ2 [HV Hp] H1 H2. split; [ exact HV | ].
  intros a b Hin. destruct Hin as [E | Hin].
  - inversion E; subst. split; intros Hf; exfalso;
      [ exact (H1 (a_flex_tvar_in_dom Hf))
      | exact (H2 (a_flex_tvar_in_dom Hf)) ].
  - exact (Hp a b Hin).
Qed.

Lemma rel_inj_push_id : forall ρ V V' x,
  rel_inj ρ V -> x `in` V -> V' [<=] V -> rel_inj ((x, x) :: ρ) V'.
Proof.
  intros ρ V V' x Hinj Hx HV a1 a2 b H1 H2.
  destruct (rel_atom_cons_inv H1) as [[E1a E1b] | H1'];
    destruct (rel_atom_cons_inv H2) as [[E2a E2b] | H2']; subst.
  - reflexivity.
  - symmetry. exact (Hinj a2 x x (rel_atom_mono_V H2' HV)
                       (@rel_atom__id ρ V x Hx)).
  - exact (Hinj a1 x x (rel_atom_mono_V H1' HV) (@rel_atom__id ρ V x Hx)).
  - exact (Hinj a1 a2 b (rel_atom_mono_V H1' HV) (rel_atom_mono_V H2' HV)).
Qed.

Lemma rel_fun_push_absent : forall ρ V V' D x,
  rel_fun ρ V D -> V' [<=] V -> x `notin` D -> rel_fun ((x, x) :: ρ) V' D.
Proof.
  intros ρ V V' D x Hfun HV Hx a b1 b2 Ha H1 H2.
  destruct (rel_atom_cons_inv H1) as [[E1a E1b] | H1'];
    destruct (rel_atom_cons_inv H2) as [[E2a E2b] | H2']; subst;
    try (exfalso; contradiction).
  exact (Hfun a b1 b2 Ha (rel_atom_mono_V H1' HV) (rel_atom_mono_V H2' HV)).
Qed.

Lemma a_flex_tvar_mid_nonflex_absurd : forall Ξ (c : atom) (bd : abind) Θ,
  uniq (Ξ ++ (c ~ bd) ++ Θ) ->
  bd <> abind_flex_mono ->
  (forall t, bd <> abind_flex_mono_def t) ->
  ~ a_flex_tvar (Ξ ++ (c ~ bd) ++ Θ) c.
Proof.
  intros Ξ c bd Θ Huq H1 H2 Hf.
  assert (HcΞ : c `notin` dom Ξ).
  { assert (Hd : disjoint Ξ ((c ~ bd) ++ Θ)) by (clear - Huq; solve_uniq).
    unfold disjoint in Hd. repeat rewrite dom_app in Hd. simpl in Hd.
    clear - Hd. fsetdec. }
  assert (HcΘ : c `notin` dom Θ).
  { assert (Hd : uniq ((c ~ bd) ++ Θ)) by (clear - Huq; solve_uniq).
    clear - Hd. destruct_uniq. fsetdec. }
  rewrite ! a_flex_tvar_app_iff in Hf.
  destruct Hf as [Hf | [Hf | Hf]].
  - exact (HcΞ (a_flex_tvar_in_dom Hf)).
  - exact (@a_flex_tvar_one_nonflex c bd c H1 H2 Hf).
  - exact (HcΘ (a_flex_tvar_in_dom Hf)).
Qed.

Lemma a_wf_aenv_mid_var_typ_inv : forall Ξ x A Θ,
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ (x ~ abind_var_typ A) ++ Θ) }}a ->
  a_wf_ptyp Θ A.
Proof.
  intros Ξ x A Θ Hdecl; revert x A Θ; induction Hdecl; intros * Hwf;
    simpl_env in *.
  - inversion Hwf; subst. assumption.
  - inversion Hwf; subst.
    match goal with
    | Hw : {{ ⊢ _ }}a |- _ => eapply IHHdecl; exact Hw
    end.
Qed.

Lemma a_wf_aenv_mid_var_skl_inv : forall Ξ x Q Θ,
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ (x ~ abind_var_skl Q) ++ Θ) }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ Q }}a.
Proof.
  intros Ξ x Q Θ Hdecl; revert x Q Θ; induction Hdecl; intros * Hwf;
    simpl_env in *.
  - inversion Hwf; subst. assumption.
  - inversion Hwf; subst.
    match goal with
    | Hw : {{ ⊢ _ }}a |- _ => eapply IHHdecl; exact Hw
    end.
Qed.

Lemma a_flex_tvar_head_swap_flexish : forall (c : atom) bd bd2 (Θ : aenv) y,
  (bd = abind_flex_mono \/ exists t, bd = abind_flex_mono_def t) ->
  (bd2 = abind_flex_mono \/ exists t, bd2 = abind_flex_mono_def t) ->
  (a_flex_tvar ((c ~ bd) ++ Θ) y <-> a_flex_tvar ((c ~ bd2) ++ Θ) y).
Proof.
  intros c bd bd2 Θ y H1 H2.
  rewrite ! a_flex_tvar_app_iff.
  rewrite (@a_flex_tvar_one_flex c bd y H1).
  rewrite (@a_flex_tvar_one_flex c bd2 y H2).
  tauto.
Qed.

Lemma flex_agree_peel_cons : forall ρ V V' Θ0 Θ0'' (β b : atom) bd bd',
  flex_agree_rel ρ V ((β ~ bd) ++ Θ0) ((b ~ bd') ++ Θ0'') ->
  rel_atom ρ V β b ->
  rel_inj ρ V ->
  (forall y, rel_atom ρ V β y -> y = b) ->
  β `notin` dom Θ0 ->
  b `notin` dom Θ0'' ->
  V' [<=] V ->
  (forall y, y `in` V' -> y <> β) ->
  flex_agree_rel ρ V' Θ0 Θ0''.
Proof.
  intros ρ V V' Θ0 Θ0'' β b bd bd' Hagr Hab Hinj Hfun Hβn Hbn HV Hne.
  eapply (@flex_agree_peel ρ V V' nil nil Θ0 Θ0'' β b bd bd');
    simpl_env; eassumption.
Qed.

Lemma flex_agree_rel_head_swap : forall ρ V (c d : atom) bd bd' bd2 bd2' Θ1 Θ2,
  flex_agree_rel ρ V ((c ~ bd) ++ Θ1) ((d ~ bd') ++ Θ2) ->
  (bd = abind_flex_mono \/ exists t, bd = abind_flex_mono_def t) ->
  (bd2 = abind_flex_mono \/ exists t, bd2 = abind_flex_mono_def t) ->
  (bd' = abind_flex_mono \/ exists t, bd' = abind_flex_mono_def t) ->
  (bd2' = abind_flex_mono \/ exists t, bd2' = abind_flex_mono_def t) ->
  flex_agree_rel ρ V ((c ~ bd2) ++ Θ1) ((d ~ bd2') ++ Θ2).
Proof.
  intros ρ V c d bd bd' bd2 bd2' Θ1 Θ2 [HV Hp] F1 F2 F3 F4. split.
  - intros y Hy.
    rewrite <- (@a_flex_tvar_head_swap_flexish c bd bd2 Θ1 y F1 F2).
    rewrite <- (@a_flex_tvar_head_swap_flexish d bd' bd2' Θ2 y F3 F4).
    exact (HV y Hy).
  - intros a b0 Hin.
    rewrite <- (@a_flex_tvar_head_swap_flexish c bd bd2 Θ1 a F1 F2).
    rewrite <- (@a_flex_tvar_head_swap_flexish d bd' bd2' Θ2 b0 F3 F4).
    exact (Hp a b0 Hin).
Qed.

(** A well-formed context's HEAD payload is scoped in its tail — one
    statement for all five binder shapes, which is what lets the walk rows
    be written once instead of per shape. *)
Lemma a_wf_aenv_cons_payload_ftv : forall (c : atom) bd (Θ : aenv),
  {{ ⊢ ((c ~ bd) ++ Θ) }}a -> ftvar_in_abind bd [<=] dom Θ.
Proof.
  intros c bd Θ H; inversion H; subst; simpl;
    try solve [ clear; fsetdec ].
  - apply a_wf_ptyp_ftv_dom; assumption.
  - pose proof (a_wf_pskl_ftv_dom ltac:(eassumption)) as Hs.
    clear - Hs. fsetdec.
  - apply a_wf_ptyp_ftv_dom; assumption.
Qed.

(* ===================================================================== *)
(*  §12  ⭐ THE CONSIS RUNG's PREREQUISITES — the facts the trio's rows    *)
(*       consume that are neither about the RELATION nor about the WALK   *)
(*                                                                        *)
(*  ⚙ Three groups, and their natural homes are noted because they are    *)
(*  general facts that happened to be missing:                            *)
(*                                                                        *)
(*  - [a_wf_pskl_ftv_binds] / [a_binds_tvar_not_var_{typ,skl}]            *)
(*    (algo/prop_basic.v's neighbourhood): every free variable of a       *)
(*    wf skeleton is TVAR-ISH, so a TERM entry cannot                     *)
(*    occur in it — what [Assign-SkipTmVar] needs and its rule does not   *)
(*    state.                                                              *)
(*  - [a_wf_pskl_tvar_mono] / [a_isub_wf_pskl] (algo/prop_inc.v's):      *)
(*    the information increase carries tvar-ishness, so a skeleton        *)
(*    well-formed in the input is well-formed in the OUTPUT — what        *)
(*    [C-Arrow]'s second premise needs of the first premise's context.    *)
(*    ⚙ [a_wf_pskl_weaken] itself is too strong: it asks for [binds]      *)
(*    preservation, and the run turns [α̂] into [α̂ ≔ τ].                   *)
(*  - [a_wf_aenv_mid_var_{typ,skl}_inv] / [a_wf_aenv_cons_payload_ftv]:   *)
(*    a context entry's payload is scoped in its OWN TAIL — the [_def]    *)
(*    twin already existed ([a_wf_aenv_mid_def_inv]).                     *)
(*                                                                        *)
(*  ⭐⭐ And the two REL facts the rung's binder and arrow rows need:       *)
(*  [rel_atoms_app] / [rel_ext_app] (both ANTITONE predicates re-proved   *)
(*  at a WIDER pair list, from the new pairs' spec) and                    *)
(*  [rel_aenv_ftv_corr_r] — [rel_pskl_ftv_corr_r] one layer up, which is  *)
(*  how a ∀ row learns that side 2's opener did not escape into side 2's  *)
(*  output context.                                                       *)
(* ===================================================================== *)

Lemma a_binds_tvar_not_var_typ : forall (Θ : aenv) x A,
  uniq Θ -> binds x (abind_var_typ A) Θ -> ~ a_binds_tvar x Θ.
Proof.
  intros Θ x A Hu Hb [Hb2 | [Hb2 | [t Hb2]]];
    pose proof (binds_unique _ _ _ _ _ Hb Hb2 Hu) as E; discriminate.
Qed.

Lemma a_binds_tvar_not_var_skl : forall (Θ : aenv) x Q,
  uniq Θ -> binds x (abind_var_skl Q) Θ -> ~ a_binds_tvar x Θ.
Proof.
  intros Θ x Q Hu Hb [Hb2 | [Hb2 | [t Hb2]]];
    pose proof (binds_unique _ _ _ _ _ Hb Hb2 Hu) as E; discriminate.
Qed.

Lemma rel_atoms_app : forall ρe ρ V D1 D2 W S,
  rel_atoms ρ V D1 D2 ->
  rel_ext ρe W S ->
  D1 [<=] W -> D2 [<=] S ->
  rel_atoms (ρe ++ ρ) V D1 D2.
Proof.
  intros ρe ρ V D1 D2 W S Hd [Hfr _] H1 H2 a b Hat.
  destruct (rel_atom_app_inv ρe ρ Hat) as [Hin | Hat'].
  - destruct (Hfr _ _ Hin) as [Ha Hb].
    split; intros Hc; exfalso; [ clear - Ha H1 Hc | clear - Hb H2 Hc ];
      fsetdec.
  - exact (Hd a b Hat').
Qed.

(** ⭐ The information increase carries TVAR-ISHNESS, so a skeleton
    well-formed in the input is well-formed in the output — what
    [a_consis__arrow]'s second premise needs of the FIRST premise's
    output context. *)
Lemma a_isub_wf_pskl : forall Θ Θ' Δ P,
  a_isub Θ Θ' -> {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> {{ Θ' ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Θ' Δ P [[κ [Hid Hinc]] _] Hwf.
  eapply a_wf_pskl_tvar_mono; [ exact Hwf | ].
  intros α Htv. eapply a_inc_binds_tvarish; eassumption.
Qed.

Lemma rel_ext_app : forall ρe2 ρe1 W1 W2 S1 S2,
  rel_ext ρe1 W1 S1 ->
  rel_ext ρe2 W2 S2 ->
  W1 [<=] W2 -> S1 [<=] S2 ->
  (forall a b, In (a, b) ρe1 -> a `in` W2 /\ b `in` S2) ->
  rel_ext (ρe2 ++ ρe1) W1 S1.
Proof.
  intros ρe2 ρe1 W1 W2 S1 S2 [Hfr1 [Hri1 Hlf1]] [Hfr2 [Hri2 Hlf2]] HW HS Hin1.
  unfold rel_ext. split; [ | split ].
  - intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hfr2 _ _ Hin) as [Ha Hb].
      split; [ clear - Ha HW; fsetdec | clear - Hb HS; fsetdec ].
    + exact (Hfr1 _ _ Hin).
  - intros a1 a2 b Hi1 Hi2. apply in_app_or in Hi1. apply in_app_or in Hi2.
    destruct Hi1 as [Hi1 | Hi1]; destruct Hi2 as [Hi2 | Hi2].
    + exact (Hri2 _ _ _ Hi1 Hi2).
    + exfalso. destruct (Hfr2 _ _ Hi1) as [_ Hb].
      destruct (Hin1 _ _ Hi2) as [_ Hb2]. contradiction.
    + exfalso. destruct (Hfr2 _ _ Hi2) as [_ Hb].
      destruct (Hin1 _ _ Hi1) as [_ Hb2]. contradiction.
    + exact (Hri1 _ _ _ Hi1 Hi2).
  - intros a b1 b2 Hi1 Hi2. apply in_app_or in Hi1. apply in_app_or in Hi2.
    destruct Hi1 as [Hi1 | Hi1]; destruct Hi2 as [Hi2 | Hi2].
    + exact (Hlf2 _ _ _ Hi1 Hi2).
    + exfalso. destruct (Hfr2 _ _ Hi1) as [Ha _].
      destruct (Hin1 _ _ Hi2) as [Ha2 _]. contradiction.
    + exfalso. destruct (Hfr2 _ _ Hi2) as [Ha _].
      destruct (Hin1 _ _ Hi1) as [Ha2 _]. contradiction.
    + exact (Hlf1 _ _ _ Hi1 Hi2).
Qed.

(** ⭐ THE CORRESPONDENCE ON A CONTEXT's FREE VARIABLES — [rel_pskl_ftv_corr_r]
    one layer up.  It is what tells a ∀ row that side 2's opener cannot have
    escaped into side 2's output context: if it had, [rel_inj] would put side
    1's opener into side 1's, which well-formedness forbids. *)
Lemma rel_ptyp_ftv_corr_r : forall ρ V A1 A2,
  rel_ptyp ρ V A1 A2 ->
  forall b, b `in` ftvar_in_ptyp A2 ->
  exists a, a `in` ftvar_in_ptyp A1 /\ rel_atom ρ V a b.
Proof.
  intros ρ V A1 A2 H b Hb. unfold rel_ptyp in H.
  rewrite <- ftvar_ptyp_to_pskl in Hb.
  destruct (rel_pskl_ftv_corr_r H Hb) as (a & Ha & Hat).
  exists a. rewrite ftvar_ptyp_to_pskl in Ha. split; assumption.
Qed.

Lemma rel_abind_ftv_corr_r : forall ρ V b1 b2,
  rel_abind ρ V b1 b2 ->
  forall b, b `in` ftvar_in_abind b2 ->
  exists a, a `in` ftvar_in_abind b1 /\ rel_atom ρ V a b.
Proof.
  intros ρ V b1 b2 H b Hb; inversion H; subst; simpl in Hb |- *;
    try solve [ exfalso; clear - Hb; fsetdec ];
    solve [ eapply rel_ptyp_ftv_corr_r; eassumption
          | eapply rel_pskl_ftv_corr_r; eassumption ].
Qed.

Lemma rel_aenv_ftv_corr_r : forall ρ V Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 ->
  forall b, b `in` ftvar_in_aenv Θ2 ->
  exists a, a `in` ftvar_in_aenv Θ1 /\ rel_atom ρ V a b.
Proof.
  intros ρ V Θ1 Θ2 H; induction H; intros y Hy; simpl in Hy;
    [ exfalso; clear - Hy; fsetdec | ].
  simpl.
  destruct (y == b) as [-> | Hne].
  - exists a. split; [ clear; fsetdec | assumption ].
  - destruct (AtomSetProperties.In_dec y (ftvar_in_abind b2)) as [Hin | Hni].
    + destruct (rel_abind_ftv_corr_r H0 Hin) as (x & Hx & Hat).
      exists x. split; [ clear - Hx; fsetdec | exact Hat ].
    + destruct (IHrel_aenv y ltac:(clear - Hy Hne Hni; fsetdec))
        as (x & Hx & Hat).
      exists x. split; [ clear - Hx; fsetdec | exact Hat ].
Qed.

(* ===================================================================== *)
(*  §13  WHAT THE CONSIS RUNG'S ∀ ROWS ADDED                              *)
(*                                                                        *)
(*  Three small facts the binder rows of [a_consis]'s lift needed and §9   *)
(*  did not have: membership in a RESTRICTED pair list, a pair pushed at   *)
(*  two atoms neither Δ contains, and the two set moves that keep the      *)
(*  [flex_above_free] obligation out of a six-atom [fsetdec].              *)
(* ===================================================================== *)

Lemma restrict_pairs_in : forall b1 b2 rho a b,
  In (a, b) rho -> a <> b1 -> b <> b2 -> In (a, b) (restrict_pairs b1 b2 rho).
Proof.
  intros b1 b2 rho a b Hin H1 H2. unfold restrict_pairs.
  apply List.filter_In. split; [ exact Hin | ]. simpl.
  match goal with |- context [ if ?X then _ else _ ] => destruct X end;
    [ contradiction | ].
  match goal with |- context [ if ?X then _ else _ ] => destruct X end;
    [ contradiction | reflexivity ].
Qed.

Lemma rel_atoms_push_absent : forall ρ V D1 D2 β1 β2,
  rel_atoms ρ V D1 D2 ->
  β1 `notin` V -> β1 `notin` cols_l ρ ->
  β2 `notin` V -> β2 `notin` cols_r ρ ->
  β1 `notin` D1 -> β2 `notin` D2 ->
  rel_atoms ((β1, β2) :: ρ) V D1 D2.
Proof.
  intros ρ V D1 D2 β1 β2 Hd Hb1V Hb1c Hb2V Hb2c Hb1D Hb2D a b Hat.
  destruct (rel_atom_cons_inv Hat) as [[-> ->] | Hat'].
  - split; intros Hin; exfalso; [ exact (Hb1D Hin) | exact (Hb2D Hin) ].
  - exact (Hd a b Hat').
Qed.

(* ⚠️ PERF: the ∀ rows' [flex_above_free] obligation is
   [(add α Δ1 ∪ add α Δ2) ∩ (add γ (dom Θb)) [=] empty] — six set atoms, and
   a direct [fsetdec] there costs 40 s PER ROW.  Split at the [add]. *)
Lemma inter_empty_add : forall D X (a : atom),
  D ∩ X [=] empty -> a `notin` X -> (add a D) ∩ X [=] empty.
Proof. intros D X a H Ha. fsetdec. Qed.

Lemma inter_empty_cong_l : forall D D' X,
  D [=] D' -> D ∩ X [=] empty -> D' ∩ X [=] empty.
Proof. intros D D' X Heq H. fsetdec. Qed.

(* --------------------------------------------------------------------- *)
(*  ⭐⭐ §13b  THE LEFT-SET RESTRICTION — what `a_sub__forall_r` needs and    *)
(*  `restrict_pairs` cannot give                                          *)
(*                                                                        *)
(*  That row's premise hands back its output as `Ξ ++ (α ~ ⌢) ++ Θ1`, and  *)
(*  the rule freshens the junk suffix `Ξ` only against the CONTEXT         *)
(*  (`uniq (Ξ ++ Θ0)`) — never against ρ.  So a junk name CAN sit in ρ's   *)
(*  left column, and the lift's motive premise "the run's new atoms are    *)
(*  off `cols_l ρ`" is then underivable at exactly those atoms.            *)
(*                                                                        *)
(*  ⭐ The fix is the same move `restrict_pairs` makes, at a SET rather     *)
(*  than one atom — and it is cheaper, because only the LEFT column has to *)
(*  be filtered: a pair is consulted by `rel_aenv` only at an atom the     *)
(*  context binds or a payload mentions, i.e. inside `ftvar_in_aenv Θ1`.   *)
(*  ⚙ The deleted pairs are answered by the SAME argument the ∀ rows use   *)
(*  for their opener — a deleted left atom is off `dom Θ0`, so the input   *)
(*  agreement makes its partner rigid, and `a_sub_sub_flex_flex_rev`       *)
(*  carries that to the output.                                           *)
(* --------------------------------------------------------------------- *)

(* ⭐ THE LEFT-SET RESTRICTION.  [restrict_pairs] deletes the pairs at ONE
   left atom; [a_sub__forall_r] needs them deleted at a whole SET — its
   premise's output carries a junk suffix whose names the rule freshens
   only against the CONTEXT, so they can collide with ρ's left column. *)
Definition restrict_l (D : atoms) (ρ : list (atom * atom))
  : list (atom * atom) :=
  List.filter (fun p => negb (AtomSetImpl.mem (fst p) D)) ρ.

Arguments restrict_l : simpl never.

Lemma restrict_l_incl : forall D ρ a b,
  In (a, b) (restrict_l D ρ) -> In (a, b) ρ.
Proof. intros * Hin. apply List.filter_In in Hin. tauto. Qed.

Lemma restrict_l_in : forall D ρ a b,
  In (a, b) ρ -> a `notin` D -> In (a, b) (restrict_l D ρ).
Proof.
  intros D ρ a b Hin Hn. unfold restrict_l. apply List.filter_In.
  split; [ exact Hin | ]. simpl.
  destruct (AtomSetImpl.mem a D) eqn:E; [ | reflexivity ].
  exfalso. apply Hn. apply AtomSetFacts.mem_iff. exact E.
Qed.

Lemma restrict_l_notin : forall D ρ a,
  a `in` D -> a `notin` cols_l (restrict_l D ρ).
Proof.
  intros D ρ a Ha. apply cols_l_fresh. intros x y Hin Ex. subst x.
  apply List.filter_In in Hin. destruct Hin as [_ Hb]. simpl in Hb.
  destruct (AtomSetImpl.mem a D) eqn:E; [ discriminate | ].
  rewrite <- AtomSetFacts.not_mem_iff in E. contradiction.
Qed.

Lemma cols_l_restrict_l : forall D ρ, cols_l (restrict_l D ρ) [<=] cols_l ρ.
Proof.
  intros D ρ x Hx. destruct (cols_l_in_inv _ _ Hx) as [y Hin].
  eapply cols_l_in. eapply restrict_l_incl. exact Hin.
Qed.

Lemma cols_r_restrict_l : forall D ρ, cols_r (restrict_l D ρ) [<=] cols_r ρ.
Proof.
  intros D ρ x Hx. destruct (cols_r_in_inv _ _ Hx) as [y Hin].
  eapply cols_r_in. eapply restrict_l_incl. exact Hin.
Qed.

(** Deleting pairs whose LEFT atom the relation never consults. *)
Lemma rel_atom_restrict_l : forall D ρ V a b,
  rel_atom ρ V a b -> a `notin` D -> rel_atom (restrict_l D ρ) V a b.
Proof.
  intros D ρ V a b Hat Hn. inversion Hat; subst;
    [ apply rel_atom__pair; apply restrict_l_in; assumption
    | apply rel_atom__id; assumption ].
Qed.

Lemma rel_pskl_restrict_l : forall D ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> D ∩ ftvar_in_pskl P1 [=] empty ->
  rel_pskl (restrict_l D ρ) V P1 P2.
Proof.
  intros D ρ V P1 P2 H; induction H; intros Hd; simpl in Hd;
    try solve [ constructor ].
  - apply rel_pskl__var_f. apply rel_atom_restrict_l;
      [ assumption | clear - Hd; fsetdec ].
  - constructor; [ apply IHrel_pskl1 | apply IHrel_pskl2 ];
      clear - Hd; fsetdec.
  - constructor; apply IHrel_pskl; clear - Hd; fsetdec.
  - constructor; apply IHrel_pskl; clear - Hd; fsetdec.
Qed.

Lemma rel_ptyp_restrict_l : forall D ρ V A1 A2,
  rel_ptyp ρ V A1 A2 -> D ∩ ftvar_in_ptyp A1 [=] empty ->
  rel_ptyp (restrict_l D ρ) V A1 A2.
Proof.
  intros D ρ V A1 A2 H Hd. unfold rel_ptyp in H |- *.
  apply rel_pskl_restrict_l; [ exact H | ].
  rewrite ftvar_ptyp_to_pskl. exact Hd.
Qed.

Lemma rel_abind_restrict_l : forall D ρ V b1 b2,
  rel_abind ρ V b1 b2 -> D ∩ ftvar_in_abind b1 [=] empty ->
  rel_abind (restrict_l D ρ) V b1 b2.
Proof.
  intros D ρ V b1 b2 H Hd; inversion H; subst; simpl in Hd; constructor;
    solve [ apply rel_ptyp_restrict_l; assumption
          | apply rel_pskl_restrict_l; assumption ].
Qed.

Lemma rel_aenv_restrict_l : forall D ρ V Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 -> D ∩ ftvar_in_aenv Θ1 [=] empty ->
  rel_aenv (restrict_l D ρ) V Θ1 Θ2.
Proof.
  intros D ρ V Θ1 Θ2 H; induction H; intros Hd; [ constructor | ].
  simpl in Hd. constructor.
  - apply rel_atom_restrict_l; [ assumption | clear - Hd; fsetdec ].
  - apply rel_abind_restrict_l; [ assumption | clear - Hd; fsetdec ].
  - apply IHrel_aenv. clear - Hd. fsetdec.
Qed.

(* ===================================================================== *)
(*  §13c  ⭐ THE a_sub RUNG'S REL CURRENCY (2026-08-20 / 2026-08-21)       *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  NEW CURRENCY for the a_sub rung (§8c.34 (i) and (ii))                 *)
(* ===================================================================== *)

(** ⭐ The APP-INVERSION [rel_aenv] did not have: [a_sub__forall_r]'s premise
    hands back its output as [Ξ ++ (α ~ ⌢) ++ Θ1], so the row must SPLIT the
    correspondence at the junk suffix before it can peel the opener. *)
Lemma rel_aenv_app_inv_l : forall Ξ ρ V Θ1 Θ2,
  rel_aenv ρ V (Ξ ++ Θ1) Θ2 ->
  exists Ξ2 Θ2', Θ2 = Ξ2 ++ Θ2'
    /\ rel_aenv ρ V Ξ Ξ2 /\ rel_aenv ρ V Θ1 Θ2'.
Proof.
  induction Ξ as [ | [c bd] Ξ IH ]; intros ρ V Θ1 Θ2 H.
  - exists (@nil (atom * abind)), Θ2. simpl_env.
    split; [ reflexivity | split; [ constructor | exact H ] ].
  - simpl_env in H.
    destruct (rel_aenv_cons_inv_l H) as (b & b2 & Θ2b & E & Hab & Hbd & Hrest).
    subst Θ2.
    destruct (IH _ _ _ _ Hrest) as (Ξ2 & Θ2' & E2 & HΞ & HΘ).
    subst Θ2b.
    exists ((b ~ b2) ++ Ξ2), Θ2'. simpl_env.
    split; [ reflexivity
           | split; [ apply rel_aenv__cons; assumption | exact HΘ ] ].
Qed.

(** ⭐ A pending SUFFIX stays a suffix across the correspondence:
    [rel_abind] relates only bindings of the SAME kind. *)
Lemma rel_aenv_suffix : forall ρ V Ξ Ξ2,
  rel_aenv ρ V Ξ Ξ2 -> a_suffix Ξ -> a_suffix Ξ2.
Proof.
  intros ρ V Ξ Ξ2 H; induction H; intros Hs; [ constructor | ].
  inversion Hs; subst.
  apply a_suffix__cons; [ apply IHrel_aenv; assumption | ].
  match goal with Hsb : a_suffix_binding _ |- _ => inversion Hsb; subst end;
    match goal with Hb : rel_abind _ _ _ _ |- _ => inversion Hb; subst end;
    constructor.
Qed.

(* ===================================================================== *)
(*  ⚙ ROW CURRENCY FOR [S-ForallL] — three small facts nothing above      *)
(*  needed.                                                              *)
(* ===================================================================== *)

(** Opening at RELATED SKELETONS (the tree has only the atom forms,
    [rel_pskl_open_pair] and [rel_pskl_open_var]).  [S-ForallL] substitutes
    the extract's INSTANTIATION, not an opener. *)
Lemma rel_pskl_open_rec_skl : forall ρ V P1 P2 Q1 Q2 k,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V Q1 Q2 ->
  rel_pskl ρ V (open_pskl_wrt_pskl_rec k Q1 P1)
               (open_pskl_wrt_pskl_rec k Q2 P2).
Proof.
  intros ρ V P1 P2 Q1 Q2 k Hrel HQ; revert k;
    induction Hrel; intros k; simpl; try (constructor; auto; fail).
  destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt];
    [ constructor | exact HQ | constructor ].
Qed.

Lemma rel_pskl_open_skl : forall ρ V P1 P2 Q1 Q2,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V Q1 Q2 ->
  rel_pskl ρ V (open_pskl_wrt_pskl P1 Q1) (open_pskl_wrt_pskl P2 Q2).
Proof.
  intros. unfold open_pskl_wrt_pskl. apply rel_pskl_open_rec_skl; assumption.
Qed.

(** ⭐ A BLOCK PAIR LIST IS A [rel_ext]: the two [uniq]s give the two
    injectivities, and the two column bounds give the freshness.  This is
    what lets a row that hands a whole BLOCK to its IH rebuild [rel_inj]
    and [rel_fun] at the widened list ([rel_inj_app] / [rel_fun_app]). *)
Lemma rel_ext_flex_pairs : forall ρn W S,
  uniq (flex_pairs_l ρn) ->
  uniq (flex_pairs_r ρn) ->
  cols_l ρn ∩ W [=] empty ->
  cols_r ρn ∩ S [=] empty ->
  rel_ext ρn W S.
Proof.
  intros ρn W S Hul Hur Hcl Hcr. unfold rel_ext. split; [ | split ].
  - intros a b Hin.
    assert (Hal : a `in` cols_l ρn) by (eapply cols_l_in; exact Hin).
    assert (Har : b `in` cols_r ρn) by (eapply cols_r_in; exact Hin).
    split; [ clear - Hal Hcl; fsetdec | clear - Har Hcr; fsetdec ].
  - intros a1 a2 b H1 H2.
    exact (nodup_snd_inj _ _ _ _ (uniq_flex_pairs_r_nodup _ Hur) H1 H2).
  - intros a b1 b2 H1 H2.
    exact (nodup_fst_fun _ _ _ _ (uniq_flex_pairs_l_nodup _ Hul) H1 H2).
Qed.

(* ===================================================================== *)
(*  ⭐⭐ THE SCOPING TRANSPORT — [a_wf_pskl] ALONG THE CORRESPONDENCE      *)
(*                                                                        *)
(*  ⛔ [e_sub__forall_l] is the ONE e-side rule that carries an            *)
(*  [a_wf_pskl] premise (ext_algo/def_sub.v:111) — it is the SCOPING       *)
(*  FILTER the solve layer's ForallR row leans on — its own comment says   *)
(*  ill-scoped results are filtered downstream.  Side 2 of the lift is     *)
(*  otherwise WF-FREE (§8c.32/§8c.34 (iii)), so the row has to BUILD that  *)
(*  premise, and the only source is side 1's own.                          *)
(*                                                                        *)
(*  ⚙ Two things make the transport go: [rel_abind] relates only bindings *)
(*  of the SAME KIND, so tvar-ish stays tvar-ish; and the Δ slot is a set  *)
(*  of atoms shared by both sides, which is sound because the ∀ case opens *)
(*  BOTH sides at the SAME atom (chosen off [cols_l ρ]) and the ∀◇ case's  *)
(*  [aenv_minus Θ Δ] only needs no image of ρ in Δ — the                   *)
(*  [Δ ∩ cols_r ρ [=] empty] invariant (at the call site Δ is [empty]).    *)
(* ===================================================================== *)

Lemma rel_atom_shrink_add : forall ρ V a0 a b,
  rel_atom ρ (add a0 V) a b -> a <> a0 -> rel_atom ρ V a b.
Proof.
  intros ρ V a0 a b H Hne. inversion H; subst;
    [ apply rel_atom__pair; assumption | ].
  apply rel_atom__id.
  match goal with
  | Hin : _ `in` add a0 V |- _ => clear - Hin Hne; fsetdec
  end.
Qed.

(** A tvar-ish binding transports: [rel_abind] preserves the KIND, and
    [rel_fun] on the context's domain is what pins the image atom. *)
Lemma a_binds_tvar_rel : forall ρ V Θ1 Θ2 a b,
  rel_aenv ρ V Θ1 Θ2 ->
  rel_fun ρ V (dom Θ1) ->
  a_binds_tvar a Θ1 ->
  rel_atom ρ V a b ->
  a_binds_tvar b Θ2.
Proof.
  intros ρ V Θ1 Θ2 a b Hrel Hfun Hbt Hat.
  assert (Had : a `in` dom Θ1) by (apply a_binds_tvar_in_dom; exact Hbt).
  assert (Hstep : forall bd, binds a bd Θ1 ->
            exists bd2, rel_abind ρ V bd bd2 /\ binds b bd2 Θ2).
  { intros bd Hb.
    destruct (@rel_aenv_binds_l ρ V Θ1 Θ2 a bd Hrel Hb)
      as (b' & bd2 & Hat' & Habd & Hb2).
    assert (Eb : b' = b) by (exact (Hfun a b' b Had Hat' Hat)).
    subst b'. exists bd2. split; [ exact Habd | exact Hb2 ]. }
  destruct Hbt as [Hb | [Hb | [τ Hb]]];
    destruct (Hstep _ Hb) as (bd2 & Habd & Hb2);
    inversion Habd; subst.
  - left. exact Hb2.
  - right. left. exact Hb2.
  - right. right. eexists. exact Hb2.
Qed.

(** The core transport: all it needs from the two contexts is that a
    tvar-ish binding on side 1 has a tvar-ish image on side 2.  The ∀ case
    opens BOTH sides at the SAME atom (legal once it is off [cols_l ρ]) and
    pushes it into BOTH contexts; the ∀◇ case strips Δ from both sides,
    which is sound because no image of [ρ] lies in Δ. *)
Lemma a_wf_pskl_rel_gen : forall Θ1 Δ P1,
  {{ Θ1 ⨟ Δ ⊢ₚₛ P1 }}a ->
  forall ρ V Θ2 P2,
  (forall a b, a_binds_tvar a Θ1 -> rel_atom ρ V a b -> a_binds_tvar b Θ2) ->
  Δ ∩ cols_r ρ [=] empty ->
  rel_pskl ρ V P1 P2 ->
  {{ Θ2 ⨟ Δ ⊢ₚₛ P2 }}a.
Proof.
  intros Θ1 Δ P1 Hwf.
  induction Hwf as [ Θ Δ | Θ Δ a0 Hd | Θ Δ Pa Pb Hwfa IHa Hwfb IHb
                   | L Θ Δ Pa Hbody IHbody | Θ Δ | Θ Δ Pa Hg Hwfa IHa ];
    intros ρ V Θ2 P2 Htv HΔ Hp.
  - (* unit *) inversion Hp; subst. apply a_wf_pskl__unit.
  - (* var *)
    inversion Hp as [ | | x y Hat | | | | ]; subst.
    apply a_wf_pskl__var. exact (Htv _ _ Hd Hat).
  - (* arrow *)
    inversion Hp as [ | | | Q1 Q2 Q3 Q4 Hpa Hpb | | | ]; subst.
    apply a_wf_pskl__arrow;
      [ eapply IHa; [ exact Htv | exact HΔ | exact Hpa ]
      | eapply IHb; [ exact Htv | exact HΔ | exact Hpb ] ].
  - (* all *)
    inversion Hp as [ | | | | Q1 Q2 Hpb | | ]; subst.
    apply a_wf_pskl__all with (L := L ∪ cols_l ρ ∪ cols_r ρ).
    intros a0 Ha0.
    eapply IHbody with (ρ := ρ) (V := add a0 V);
      [ clear - Ha0; solve_notin_auto
      | | clear - HΔ Ha0; fsetdec
      | apply rel_pskl_open_var; exact Hpb ].
    intros a b Ha Hab. apply a_binds_tvar_cons_tvar.
    destruct (a == a0) as [-> | Hne].
    + left. inversion Hab as [ x1 y1 Hin | x1 Hin ]; subst; [ | reflexivity ].
      exfalso. apply cols_l_in in Hin. clear - Hin Ha0. solve_notin_auto.
    + right. destruct (a_binds_tvar_cons_tvar_inv Ha) as [E | Ha'];
        [ contradiction | ].
      eapply Htv; [ exact Ha' | eapply rel_atom_shrink_add; eassumption ].
  - (* ghost *) inversion Hp; subst. apply a_wf_pskl__ghost.
  - (* univ_ghost *)
    inversion Hp as [ | | | | | | Q1 Q2 Hpb ]; subst.
    apply a_wf_pskl__univ_ghost;
      [ eapply rel_pskl_guarded; [ exact Hpb | exact Hg ]
      | eapply IHa; [ | clear; fsetdec | exact Hpb ] ].
    intros a b Ha Hab.
    apply a_binds_tvar_aenv_minus in Ha. destruct Ha as [Ha HaΔ].
    apply a_binds_tvar_aenv_minus. split; [ exact (Htv _ _ Ha Hab) | ].
    inversion Hab as [ x1 y1 Hin | x1 Hin ]; subst; [ | exact HaΔ ].
    apply cols_r_in in Hin. clear - Hin HΔ. fsetdec.
Qed.

Lemma a_wf_pskl_rel : forall Θ1 Δ P1,
  {{ Θ1 ⨟ Δ ⊢ₚₛ P1 }}a ->
  forall ρ V Θ2 P2,
  rel_aenv ρ V Θ1 Θ2 ->
  rel_fun ρ V (dom Θ1) ->
  Δ ∩ cols_r ρ [=] empty ->
  rel_pskl ρ V P1 P2 ->
  {{ Θ2 ⨟ Δ ⊢ₚₛ P2 }}a.
Proof.
  intros Θ1 Δ P1 Hwf ρ V Θ2 P2 Hrel Hfun HΔ Hp.
  eapply a_wf_pskl_rel_gen; [ exact Hwf | | exact HΔ | exact Hp ].
  intros a b Hbt Hat.
  eapply a_binds_tvar_rel; [ exact Hrel | exact Hfun | exact Hbt | exact Hat ].
Qed.

(* ===================================================================== *)
(*  §13d  ⭐⭐ THE RELATION ON EXPRESSIONS (2026-08-22, the a_pat rung)      *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  ⭐⭐ THE RELATION ON EXPRESSIONS                                        *)
(*                                                                        *)
(*  [a_pat]'s four abs rows OPEN the body at a TERM variable that is fresh *)
(*  only for the CONTEXT, while [e_pat]'s draw theirs from the SUPPLY — so *)
(*  the two sides' premises are at DIFFERENT expressions and the motive    *)
(*  must relate them.  ⚙ Term and type variables share one atom space, so  *)
(*  this rides on the SAME ρ / V: [exp_var_f] goes through [rel_atom] and  *)
(*  the annotations through [rel_ptyp].                                   *)
(* ===================================================================== *)

Inductive rel_exp (ρ : list (atom * atom)) (V : atoms) : exp -> exp -> Prop :=
| rel_exp__unit : rel_exp ρ V exp_unit exp_unit
| rel_exp__var_b : forall n, rel_exp ρ V (exp_var_b n) (exp_var_b n)
| rel_exp__var_f : forall x y,
    rel_atom ρ V x y -> rel_exp ρ V (exp_var_f x) (exp_var_f y)
| rel_exp__abs : forall e1 e2,
    rel_exp ρ V e1 e2 -> rel_exp ρ V (exp_abs e1) (exp_abs e2)
| rel_exp__abs_anno : forall A1 A2 e1 e2,
    rel_ptyp ρ V A1 A2 -> rel_exp ρ V e1 e2 ->
    rel_exp ρ V (exp_abs_anno A1 e1) (exp_abs_anno A2 e2)
| rel_exp__app : forall a1 a2 b1 b2,
    rel_exp ρ V a1 b1 -> rel_exp ρ V a2 b2 ->
    rel_exp ρ V (exp_app a1 a2) (exp_app b1 b2)
| rel_exp__anno : forall e1 e2 A1 A2,
    rel_exp ρ V e1 e2 -> rel_ptyp ρ V A1 A2 ->
    rel_exp ρ V (exp_anno e1 A1) (exp_anno e2 A2)
| rel_exp__freeze : forall e1 e2,
    rel_exp ρ V e1 e2 -> rel_exp ρ V (exp_freeze e1) (exp_freeze e2).

#[export] Hint Constructors rel_exp : core.

Lemma rel_exp_mono : forall ρ ρ' V V' e1 e2,
  rel_exp ρ V e1 e2 ->
  (forall a b, In (a, b) ρ -> In (a, b) ρ') ->
  V [<=] V' ->
  rel_exp ρ' V' e1 e2.
Proof.
  intros ρ ρ' V V' e1 e2 H Hin Hs; induction H; constructor; auto;
    try (unfold rel_ptyp in *; eapply rel_pskl_mono; eauto; fail).
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ =>
      inversion Ha; subst;
        [ apply rel_atom__pair; auto | apply rel_atom__id; fsetdec ]
  end.
Qed.

(** Reflexivity on anything the support covers — [rel_pskl_refl] one
    syntax over.  At [V = ∅] it is what relates a CLOSED program to
    itself, which is how the lift composes with the closed-program
    corollaries. *)
Lemma rel_exp_refl : forall ρ V e,
  fvar_in_exp e ∪ ftvar_in_exp e [<=] V ->
  rel_exp ρ V e e.
Proof.
  intros ρ V e; induction e; intros Hsub; simpl in Hsub;
    constructor;
    try (apply rel_atom__id; clear - Hsub; fsetdec);
    try (unfold rel_ptyp; apply rel_pskl_refl;
         match goal with
         | |- ftvar_in_pskl (ptyp_to_pskl ?A0) [<=] _ =>
             pose proof (ftvar_ptyp_to_pskl A0) as He
         end; clear - Hsub He; fsetdec);
    try (match goal with
         | IH : _ -> rel_exp _ _ ?x ?x |- rel_exp _ _ ?x ?x => apply IH
         end; clear - Hsub; fsetdec).
Qed.

(** Opening at a TERM-variable PAIR — [rel_pskl_open_pair] one syntax over. *)
Lemma rel_exp_open_rec_pair : forall ρ V e1 e2 x y k,
  rel_exp ρ V e1 e2 ->
  rel_exp ((x, y) :: ρ) V
    (open_exp_wrt_exp_rec k (exp_var_f x) e1)
    (open_exp_wrt_exp_rec k (exp_var_f y) e2).
Proof.
  intros ρ V e1 e2 x y k H; revert k; induction H; intros k; simpl;
    try (constructor; auto;
         (unfold rel_ptyp in *; eapply rel_pskl_mono;
          [ eassumption | intros ?a ?b Hi; right; exact Hi
          | intros ?z Hz; exact Hz ]); fail).
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt];
      [ constructor | | constructor ].
    apply rel_exp__var_f. apply rel_atom__pair. left. reflexivity.
  - (* var_f *)
    apply rel_exp__var_f.
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ =>
        inversion Ha; subst;
          [ apply rel_atom__pair; right; assumption
          | apply rel_atom__id; assumption ]
    end.
Qed.

Lemma rel_exp_open_pair : forall ρ V e1 e2 x y,
  rel_exp ρ V e1 e2 ->
  rel_exp ((x, y) :: ρ) V
    (open_exp_wrt_exp e1 (exp_var_f x)) (open_exp_wrt_exp e2 (exp_var_f y)).
Proof.
  intros. unfold open_exp_wrt_exp. apply rel_exp_open_rec_pair. assumption.
Qed.

Lemma rel_exp_restrict : forall x y ρ V e1 e2,
  rel_exp ρ V e1 e2 ->
  x `notin` fvar_in_exp e1 ∪ ftvar_in_exp e1 ->
  y `notin` fvar_in_exp e2 ∪ ftvar_in_exp e2 ->
  rel_exp (restrict_pairs x y ρ) V e1 e2.
Proof.
  intros x y ρ V e1 e2 H; induction H; intros Hx Hy; simpl in Hx, Hy.
  - apply rel_exp__unit.
  - apply rel_exp__var_b.
  - apply rel_exp__var_f.
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ =>
        inversion Ha; subst;
          [ apply rel_atom__pair; apply restrict_pairs_in;
              [ assumption | clear - Hx; fsetdec | clear - Hy; fsetdec ]
          | apply rel_atom__id; assumption ]
    end.
  - apply rel_exp__abs. apply IHrel_exp;
      [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  - apply rel_exp__abs_anno.
    + unfold rel_ptyp in *. apply rel_pskl_restrict;
        [ assumption
        | rewrite ftvar_ptyp_to_pskl; clear - Hx; fsetdec
        | rewrite ftvar_ptyp_to_pskl; clear - Hy; fsetdec ].
    + apply IHrel_exp; [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  - apply rel_exp__app;
      [ apply IHrel_exp1 | apply IHrel_exp2 ];
      solve [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  - apply rel_exp__anno.
    + apply IHrel_exp; [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
    + unfold rel_ptyp in *. apply rel_pskl_restrict;
        [ assumption
        | rewrite ftvar_ptyp_to_pskl; clear - Hx; fsetdec
        | rewrite ftvar_ptyp_to_pskl; clear - Hy; fsetdec ].
  - apply rel_exp__freeze. apply IHrel_exp;
      [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
Qed.

(** ⭐ [rel_exp] survives a LEFT-SET restriction — [rel_pskl_restrict_l]
    one syntax over (prop_lift_kit §13d).  The [_check] rows restrict at
    the junk suffix's domain, and [a_typing_fvar_binds] +
    [a_wf_exp_ftv_dom] are what pay the disjointness premise. *)
Lemma rel_exp_restrict_l : forall D ρ V e1 e2,
  rel_exp ρ V e1 e2 ->
  D ∩ (fvar_in_exp e1 ∪ ftvar_in_exp e1) [=] empty ->
  rel_exp (restrict_l D ρ) V e1 e2.
Proof.
  intros D ρ V e1 e2 H; induction H; intros Hd; simpl in Hd.
  - apply rel_exp__unit.
  - apply rel_exp__var_b.
  - apply rel_exp__var_f.
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ =>
        inversion Ha; subst;
          [ apply rel_atom__pair; apply restrict_l_in;
              [ assumption | clear - Hd; fsetdec ]
          | apply rel_atom__id; assumption ]
    end.
  - apply rel_exp__abs. apply IHrel_exp. clear - Hd. fsetdec.
  - apply rel_exp__abs_anno.
    + apply rel_ptyp_restrict_l; [ assumption | clear - Hd; fsetdec ].
    + apply IHrel_exp. clear - Hd. fsetdec.
  - apply rel_exp__app;
      [ apply IHrel_exp1 | apply IHrel_exp2 ]; clear - Hd; fsetdec.
  - apply rel_exp__anno.
    + apply IHrel_exp. clear - Hd. fsetdec.
    + apply rel_ptyp_restrict_l; [ assumption | clear - Hd; fsetdec ].
  - apply rel_exp__freeze. apply IHrel_exp. clear - Hd. fsetdec.
Qed.

(** ⭐ Pinning the IMAGE of a bound atom: [rel_aenv_binds_l] hands back SOME
    image, and [rel_fun] on the context's domain says it is the one the
    caller already has.  ⚙ This is [a_binds_tvar_rel]'s inner step, made
    first-class — [AP-Var] needs it at a TERM entry. *)
Lemma rel_aenv_binds_pin : forall ρ V Θ1 Θ2 a b bd,
  rel_aenv ρ V Θ1 Θ2 ->
  rel_fun ρ V (dom Θ1) ->
  binds a bd Θ1 ->
  rel_atom ρ V a b ->
  exists bd2, rel_abind ρ V bd bd2 /\ binds b bd2 Θ2.
Proof.
  intros ρ V Θ1 Θ2 a b bd Hrel Hfun Hb Hat.
  assert (Had : a `in` dom Θ1) by (eapply binds_In; exact Hb).
  destruct (@rel_aenv_binds_l ρ V Θ1 Θ2 a bd Hrel Hb)
    as (b' & bd2 & Hat' & Habd & Hb2).
  assert (Eb : b' = b) by (exact (Hfun a b' b Had Hat' Hat)).
  subst b'. exists bd2. split; [ exact Habd | exact Hb2 ].
Qed.

Lemma flex_agree_rel_push_tm : forall ρ V Θ1 Θ2 x x2 (bd bd' : abind),
  flex_agree_rel ρ V Θ1 Θ2 ->
  abind_nonflex bd ->
  abind_nonflex bd' ->
  x `notin` dom Θ1 ->
  x2 `notin` dom Θ2 ->
  flex_agree_rel ((x, x2) :: ρ) V ((x ~ bd) ++ Θ1) ((x2 ~ bd') ++ Θ2).
Proof.
  intros ρ V Θ1 Θ2 x x2 bd bd' [HagV Hagp] Hnf1 Hnf2 Hx1 Hx2.
  split.
  - intros v Hv.
    rewrite (a_flex_tvar_cons_nonflex _ _ _ Hnf1).
    rewrite (a_flex_tvar_cons_nonflex _ _ _ Hnf2).
    exact (HagV v Hv).
  - intros a b Hin.
    rewrite (a_flex_tvar_cons_nonflex _ _ _ Hnf1).
    rewrite (a_flex_tvar_cons_nonflex _ _ _ Hnf2).
    destruct Hin as [E | Hin].
    + injection E as -> ->.
      split; intros Hf; exfalso;
        [ apply Hx1 | apply Hx2 ]; apply a_flex_tvar_in_dom; exact Hf.
    + exact (Hagp a b Hin).
Qed.

