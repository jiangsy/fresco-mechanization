(** ext_algo — campaign level 8: the TYPE-INFERENCE runner's COMPLETENESS,
    and with it the last judgement of the extractable encoding.

    §1  the kit this level adds — [guess^TY]'s determinism up to a chain,
        the [⌈⌉]-commutation and free-variable transports, and the
        [e_typing] chain iteration
    §2  the ROOT INVERSIONS — one per clause of the runner's dispatch,
        the three [exp_abs] cells stated as ONE disjunction (level 7's
        idiom, with a third arm for the check-mode BASE row)
    §3  THE MOTIVE
    §4  THE MAIN INDUCTION
    §5  the headlines, over [e_typing_impl] and [e_typing_run]

    ⭐ THE CHECK-MODE DISPATCH IS DECIDED BY [pskl_readback_all], AND THE
    RULES AGREE.  At [P0 = ⌈∀A0⌉] the BASE row would need a SPLIT of
    [pskl_all_syn ⌈A0⌉], and [e_split] has no ∀ row — so the STEP row is
    the only one, which is what the runner picks.  At any other readback
    image the STEP row's own premise [P0 = ⌈∀A0⌉] fails.  Neither cell
    needs a new side condition; the overlap is closed by [e_split]'s own
    shape.

    ⭐⭐ ONE PIECE OF UPSTREAM METATHEORY WAS MISSING AND IS BUILT HERE:
    [e_guess_mono_det] — [guess^TY] is deterministic UP TO A FRESH-PAIR
    CHAIN.  [AT-Abs] runs it, the runner runs its own copy, and the two
    invent different atoms; every other recursive call in this file is a
    runner whose completeness is already stated in that form.  ⚙ It sits
    here rather than in prop_guess.v because the [swaps_*] family it is
    stated over (prop_solve_det.v §2) is downstream of that file. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

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
Require Import src.fresco.algo.sub.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_dec.
Require Import src.fresco.ext_algo.prop_dec.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.prop_guess.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.prop_consis.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.prop_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.prop_solve.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.prop_extract.
Require Import src.fresco.ext_algo.def_sub.
Require Import src.fresco.ext_algo.prop_sub.
Require Import src.fresco.ext_algo.def_pat.
Require Import src.fresco.ext_algo.prop_pat.
Require Import src.fresco.ext_algo.def_typing.
Require Import src.fresco.ext_algo.prop_typing.
Require Import src.fresco.ext_algo.def_order.
Require Import src.fresco.ext_algo.prop_termination.
Require Import src.fresco.ext_algo.prop_solve_det.
Require Import src.fresco.ext_algo.prop_run_invariants.
Require Import src.fresco.ext_algo.def_guess_impl.
Require Import src.fresco.ext_algo.def_consis_impl.
Require Import src.fresco.ext_algo.prop_consis_complete.
Require Import src.fresco.ext_algo.def_extract_impl.
Require Import src.fresco.ext_algo.prop_extract_det.
Require Import src.fresco.ext_algo.prop_look_pair.
Require Import src.fresco.ext_algo.def_sub_impl.
Require Import src.fresco.ext_algo.prop_sub_complete.
Require Import src.fresco.ext_algo.def_pat_impl.
Require Import src.fresco.ext_algo.prop_pat_complete.
Require Import src.fresco.ext_algo.def_typing_impl.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §1  THE KIT THIS LEVEL ADDS                                           *)
(* ===================================================================== *)

(** A name a type does not mention is not mentioned by its image either —
    what the check-mode STEP rows need of their [close]. *)
Lemma swaps_ptyp_ftv_notin : forall ps A x,
  x `notin` ftvar_in_ptyp A ->
  swaps_atom ps x `notin` ftvar_in_ptyp (swaps_ptyp ps A).
Proof.
  induction ps as [ | [a b] ps IH ]; intros A x Hx; simpl; [ exact Hx | ].
  apply IH. apply swap_ptyp_ftv_notin. exact Hx.
Qed.

(** The check rows' KEPT scoping filter, along a chain (algo/prop_swap.v's
    [swap_block_ftv_filter], iterated). *)
Lemma swaps_block_ftv_filter : forall ps (Ξ : aenv) A,
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
  forall γ, γ `in` dom (swaps_aenv ps Ξ) ->
            γ `notin` ftvar_in_ptyp (swaps_ptyp ps A).
Proof.
  induction ps as [ | [a b] ps IH ]; intros Ξ A Hf; simpl; [ exact Hf | ].
  apply IH. apply swap_block_ftv_filter. exact Hf.
Qed.

Lemma e_typing_swaps : forall ps S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0) ⊢[ m ; (swaps_pskl ps P0) ]
       (swaps_exp ps e) ⦂ (swaps_ptyp ps B) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_typing_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_typing_swap (a := a) (b := b) Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

(* Use the shared embedding's injectivity with the equation explicit. *)
Arguments ptyp_to_pskl_inj {A B} _.

Lemma swaps_aenv_one_tvar : forall ps x,
  swaps_aenv ps (x ~ abind_tvar) = (swaps_atom ps x ~ abind_tvar).
Proof.
  intros. unfold one.
  rewrite swaps_aenv_cons, swaps_abind_tvar, swaps_aenv_nil. reflexivity.
Qed.

Lemma swaps_ptyp_open : forall ps A1 A2,
  swaps_ptyp ps (open_ptyp_wrt_ptyp A1 A2)
  = open_ptyp_wrt_ptyp (swaps_ptyp ps A1) (swaps_ptyp ps A2).
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; [ reflexivity | ].
  rewrite swap_ptyp_open. apply IH.
Qed.

(** The KEPT scoping filter, as the intersection the runner tests. *)
Lemma notin_all_inter_empty : forall S1 S2,
  (forall γ, γ `in` S1 -> γ `notin` S2) -> S1 ∩ S2 [=] empty.
Proof.
  intros S1 S2 Hf γ. split; intros Hγ; [ | clear - Hγ; fsetdec ].
  assert (Hin1 : γ `in` S1) by (clear - Hγ; fsetdec).
  pose proof (Hf γ Hin1) as Hout. clear - Hγ Hout. fsetdec.
Qed.

(** [close] under a ∀ is locally closed — the [ptyp] twin of
    prop_run_invariants.v §2's [lc_pskl_all_syn_close]. *)
Lemma lc_ptyp_all_close : forall α A,
  lc_ptyp A -> lc_ptyp (ptyp_all (close_ptyp_wrt_ptyp α A)).
Proof.
  intros α A HA. apply (lc_ptyp_all_exists α).
  rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp. exact HA.
Qed.

(** [guess^TY] returns a locally-closed type — [AT-Abs] pushes it into the
    context, where §8c.22's invariant needs it. *)
Lemma e_guess_mono_lc_type : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> lc_pskl P -> lc_ptyp A.
Proof.
  intros * Hg; induction Hg; intros Hlc.
  - apply lc_ptyp_var_f.
  - apply IHHg. exact (lc_pskl_univ_ghost_inv Hlc).
  - apply lc_ptyp_var_f.
  - apply lc_ptyp_unit.
  - destruct (lc_pskl_arrow_inv Hlc) as [Hl1 Hl2].
    apply lc_ptyp_arrow; auto.
  - apply lc_ptyp_all_close. apply IHHg.
    exact (lc_pskl_all_syn_inv Hlc β).
Qed.

(** [guess^TY]'s block holds BARE flexibles, so both context invariants
    §8c.22 threads are immediate on it. *)
Lemma e_guess_mono_block_binding : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A ->
  forall x b, In (x, b) Ξ -> b = abind_flex_mono.
Proof.
  intros * Hg x b Hin.
  pose proof (e_guess_mono_block_flex Hg) as Hflex.
  unfold src.fresco.algo.prop_metasubst.all_flex_mono in Hflex.
  rewrite Forall_forall in Hflex.
  exact (Hflex (x, b) Hin).
Qed.

Lemma e_guess_mono_block_lc : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> lc_aenv Ξ.
Proof.
  intros * Hg. unfold lc_aenv. apply Forall_forall.
  intros [y b] Hin. rewrite (e_guess_mono_block_binding Hg y b Hin).
  exact I.
Qed.

Lemma e_guess_mono_block_defs_mono : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> aenv_defs_mono Ξ.
Proof.
  intros * Hg. apply Forall_forall.
  intros [y b] Hin. rewrite (e_guess_mono_block_binding Hg y b Hin).
  apply entry_def_mono_flex.
Qed.

(** What the guessed type can mention, closed under the OUTPUT supply — the
    form [AT-Abs]'s chain bookkeeping wants. *)
Lemma e_guess_mono_ftv_supply : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> ftvar_in_pskl P [<=] S0 ->
  ftvar_in_ptyp A [<=] S1.
Proof.
  intros * Hg Hcov.
  pose proof (e_guess_mono_ftv Hg) as Hftv.
  pose proof (e_guess_mono_generated_in_supply Hg) as Hdom.
  pose proof (e_guess_mono_supply_grows Hg) as Hgr.
  clear - Hftv Hdom Hgr Hcov. fsetdec.
Qed.

(** ⭐⭐ [guess^TY] IS DETERMINISTIC UP TO A FRESH-PAIR CHAIN.  ⚙ The
    coverage hypothesis is not decoration: at a VARIABLE subject the row
    returns [α] itself, so without [ftv P ⊆ S0] the answer could mention a
    name the chain is free to move.  Every call site has it — [AT-Abs] runs
    [guess^TY] on a SPLIT's domain, and prop_pat.v §2 bounds that by the
    split's output supply. *)
Lemma e_guess_mono_det_n : forall n P, size_pskl P <= n ->
  forall S0 S1 Ξ1 A1 S2 Ξ2 A2,
  ftvar_in_pskl P [<=] S0 ->
  e_guess_mono S0 P S1 Ξ1 A1 -> e_guess_mono S0 P S2 Ξ2 A2 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps S1 [=] S2
    /\ swaps_aenv ps Ξ1 = Ξ2
    /\ swaps_ptyp ps A1 = A2.
Proof.
  induction n as [ | n IHn ];
    intros P Hsz S0 S1 Ξ1 A1 S2 Ξ2 A2 Hcov D1 D2.
  - (* no skeleton has size 0 *)
    exfalso. destruct P; simpl in Hsz; lia.
  - destruct P as [ | k | α | P1 P2 | B0 | | P1 ]; simpl in Hsz.
    + (* unit *)
      destruct (e_guess_mono_inv_unit D1) as [-> [-> ->]].
      destruct (e_guess_mono_inv_unit D2) as [-> [-> ->]].
      exists nil. split; [ intros ? ? [] | ].
      split; [ reflexivity | ]. split; reflexivity.
    + (* a bound index is not a skeleton any run is given *)
      exfalso. exact (e_guess_mono_inv_var_b D1).
    + (* var *)
      destruct (e_guess_mono_inv_var D1) as [-> [-> ->]].
      destruct (e_guess_mono_inv_var D2) as [-> [-> ->]].
      exists nil. split; [ intros ? ? [] | ].
      split; [ reflexivity | ]. split; reflexivity.
    + (* arrow — THREADED, so the two chains compose *)
      destruct (e_guess_mono_inv_arrow D1)
        as [S1a [Ξ1a [Ξ1b [A1a [A1b [-> [-> [D1a D1b]]]]]]]].
      destruct (e_guess_mono_inv_arrow D2)
        as [S2a [Ξ2a [Ξ2b [A2a [A2b [-> [-> [D2a D2b]]]]]]]].
      (* ⚠️⚠️ NEVER an [fsetdec] inside an [ltac:] ARGUMENT: at that point
         the recursive call's own [S0] is still an EVAR and the search does
         not return.  Every coverage side condition here is a NAMED
         hypothesis. *)
      assert (HcP1 : ftvar_in_pskl P1 [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      destruct (IHn P1 ltac:(lia) _ _ _ _ _ _ _ HcP1 D1a D2a)
        as [psa [Hava [HSa [HTa HAa]]]].
      (* move the CODOMAIN's run onto the first answer's rails *)
      destruct (e_guess_mono_swaps psa D1b (S0' := S2a))
        as [Sm [HSm D1b']]; [ symmetry; exact HSa | ].
      pose proof (e_guess_mono_supply_grows D2a) as Hgra.
      assert (HfixP2 : swaps_pskl psa P2 = P2)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct (Hava a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
      rewrite HfixP2 in D1b'.
      assert (HcP2 : ftvar_in_pskl P2 [<=] S2a)
        by (clear - Hcov Hgra; simpl in *; fsetdec).
      destruct (IHn P2 ltac:(lia) _ _ _ _ _ _ _ HcP2 D1b' D2b)
        as [psb [Havb [HSb [HTb HAb]]]].
      exists (psa ++ psb).
      assert (Hav : forall a b, In (a, b) (psa ++ psb) ->
                    a `notin` S0 /\ b `notin` S0).
      { intros a0 b0 Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin]; [ exact (Hava _ _ Hin) | ].
        destruct (Havb _ _ Hin) as [Hka Hkb].
        split; clear - Hka Hkb Hgra; fsetdec. }
      (* the first answer's block and type live inside [S2a], so the second
         chain fixes them *)
      pose proof (e_guess_mono_generated_in_supply D2a) as HdomA.
      pose proof (e_guess_mono_generated_ftvar D2a) as HftA.
      pose proof (e_guess_mono_ftv D2a) as HftvA.
      assert (HfixT : swaps_aenv psb Ξ2a = Ξ2a)
        by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct (Havb a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb HdomA HftA; fsetdec).
      (* ⚠️ in TWO steps: one [fsetdec] over all six set variables at once
         does not return (the ⚠️⚠️ at 6 atoms). *)
      assert (HcovP1 : ftvar_in_pskl P1 [<=] S2a)
        by (clear - HcP1 Hgra; fsetdec).
      assert (HftvA2 : ftvar_in_ptyp A2a [<=] S2a)
        by (clear - HftvA HdomA HcovP1; fsetdec).
      assert (HfixA : swaps_ptyp psb A2a = A2a)
        by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
            destruct (Havb a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb HftvA2; fsetdec).
      split; [ exact Hav | ].
      split; [ rewrite swaps_atoms_app; rewrite <- HSb;
               apply swaps_atoms_cong; symmetry; exact HSm | ].
      split.
      * rewrite swaps_aenv_app, ! swaps_aenv_app_dist, HTa, HTb, HfixT.
        reflexivity.
      * rewrite swaps_ptyp_app, ! swaps_ptyp_arrow, HAa, HAb, HfixA.
        reflexivity.
    + (* ∀ — the witness is drawn from the supply on both sides *)
      destruct (e_guess_mono_inv_all_syn D1) as [β1 [A1' [Hβ1 [-> D1']]]].
      destruct (e_guess_mono_inv_all_syn D2) as [β2 [A2' [Hβ2 [-> D2']]]].
      destruct (e_guess_mono_swaps ((β1, β2) :: nil) D1'
                  (S0' := add β2 S0)) as [Sm [HSm D1'']].
      { cbn [swaps_atoms]. rewrite swap_atoms_add.
        rewrite (swap_atoms_notin β1 β2 S0) by (clear - Hβ1 Hβ2; fsetdec).
        unfold swap_atom. destruct (β1 == β1); [ reflexivity | congruence ]. }
      assert (HfixP : swaps_pskl ((β1, β2) :: nil) B0 = B0)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hβ1 Hβ2 Hcov; simpl in *; fsetdec).
      assert (Hsβ1 : swaps_atom ((β1, β2) :: nil) β1 = β2)
        by (cbn [swaps_atom]; unfold swap_atom;
            destruct (β1 == β1); [ reflexivity | congruence ]).
      rewrite swaps_pskl_open, swaps_pskl_var_f, HfixP, Hsβ1 in D1''.
      assert (HcovB : ftvar_in_pskl (open_pskl_wrt_pskl B0 (pskl_var_f β2))
                      [<=] add β2 S0).
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B0
                      (pskl_var_f β2)) as Hup.
        simpl in Hup. clear - Hup Hcov. simpl in *. fsetdec. }
      assert (Hszb : size_pskl (open_pskl_wrt_pskl B0 (pskl_var_f β2)) <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
      destruct (IHn (open_pskl_wrt_pskl B0 (pskl_var_f β2)) Hszb
                  _ _ _ _ _ _ _ HcovB D1'' D2')
        as [psb [Havb [HSb [HTb HAb]]]].
      exists (((β1, β2) :: nil) ++ psb).
      assert (Hav : forall a b, In (a, b) (((β1, β2) :: nil) ++ psb) ->
                    a `notin` S0 /\ b `notin` S0).
      { intros a0 b0 Hin. apply in_app_or in Hin.
        destruct Hin as [ [Heq0 | []] | Hin ];
          [ inversion Heq0; subst; split; assumption | ].
        destruct (Havb _ _ Hin) as [Hka Hkb].
        split; clear - Hka Hkb; fsetdec. }
      assert (Hsβ : swaps_atom (((β1, β2) :: nil) ++ psb) β1 = β2).
      { rewrite swaps_atom_app, Hsβ1.
        apply swaps_atom_notin. intros a0 b0 Hin.
        destruct (Havb a0 b0 Hin) as [Hka Hkb].
        split; intro Heq0; [ apply Hka | apply Hkb ];
          rewrite <- Heq0; clear; fsetdec. }
      split; [ exact Hav | ].
      split; [ rewrite swaps_atoms_app; rewrite <- HSb;
               apply swaps_atoms_cong; symmetry; exact HSm | ].
      split.
      * rewrite swaps_aenv_app. exact HTb.
      * rewrite swaps_ptyp_all, swaps_ptyp_close, Hsβ.
        rewrite swaps_ptyp_app, HAb. reflexivity.
    + (* ghost — the row that INVENTS *)
      destruct (e_guess_mono_inv_ghost D1) as [α1 [Hα1 [-> [-> ->]]]].
      destruct (e_guess_mono_inv_ghost D2) as [α2 [Hα2 [-> [-> ->]]]].
      exists ((α1, α2) :: nil).
      assert (Hsα : swaps_atom ((α1, α2) :: nil) α1 = α2)
        by (cbn [swaps_atom]; unfold swap_atom;
            destruct (α1 == α1); [ reflexivity | congruence ]).
      split; [ intros a0 b0 [Heq0 | []]; inversion Heq0; subst;
               split; assumption | ].
      split.
      * cbn [swaps_atoms]. rewrite swap_atoms_add.
        rewrite (swap_atoms_notin α1 α2 S0) by (clear - Hα1 Hα2; fsetdec).
        unfold swap_atom. destruct (α1 == α1); [ reflexivity | congruence ].
      * split.
        -- rewrite swaps_aenv_app_dist, swaps_aenv_one_flex, swaps_aenv_nil,
             Hsα.
           reflexivity.
        -- rewrite swaps_ptyp_var_f, Hsα. reflexivity.
    + (* ⫯ *)
      pose proof (e_guess_mono_inv_univ_ghost D1) as D1'.
      pose proof (e_guess_mono_inv_univ_ghost D2) as D2'.
      assert (HcP1 : ftvar_in_pskl P1 [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      exact (IHn P1 ltac:(lia) _ _ _ _ _ _ _ HcP1 D1' D2').
Qed.

Corollary e_guess_mono_det : forall P S0 S1 Ξ1 A1 S2 Ξ2 A2,
  ftvar_in_pskl P [<=] S0 ->
  e_guess_mono S0 P S1 Ξ1 A1 -> e_guess_mono S0 P S2 Ξ2 A2 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps S1 [=] S2
    /\ swaps_aenv ps Ξ1 = Ξ2
    /\ swaps_ptyp ps A1 = A2.
Proof. intros. eapply e_guess_mono_det_n; [ apply le_n | eassumption .. ]. Qed.

(* ===================================================================== *)
(*  §2  ROOT INVERSIONS — the case backbone                               *)
(*                                                                        *)
(*  One per clause of the runner's dispatch.  ⭐ Eight of the eleven rows  *)
(*  are keyed by the subject's head constructor; the three that share      *)
(*  [exp_abs] (and the three that share [exp_abs_anno]) are stated as ONE  *)
(*  DISJUNCTION, level 7's idiom, so each branch of the mode/readback      *)
(*  dispatch kills the arms it does not want by [congruence] instead of    *)
(*  having to produce the discriminating premise first.                    *)
(* ===================================================================== *)

Lemma e_typing_inv_unit : forall S0 m Θ0 P0 Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] exp_unit ⦂ Bd ⊣ Θd }}e ->
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ a_sub_mode_ty | m | P0 ]
     pskl_unit ⩽ (ptyp_to_pskl Bd) ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. assumption. Qed.

Lemma e_typing_inv_var_b : forall S0 m Θ0 P0 n Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_var_b n) ⦂ Bd ⊣ Θd }}e -> False.
Proof. intros * H. inversion H. Qed.

Lemma e_typing_inv_var : forall S0 m Θ0 P0 x Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_var_f x) ⦂ Bd ⊣ Θd }}e ->
  exists A, binds x (abind_var_typ A) Θ0
    /\ {{ S0 ↝ Sd ⊨ Θ0 ⊢[ a_sub_mode_ty | m | P0 ]
          (ptyp_to_pskl A) ⩽ (ptyp_to_pskl Bd) ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. eauto. Qed.

Lemma e_typing_inv_anno : forall S0 m Θ0 P0 e1 A Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_anno e1 A) ⦂ Bd ⊣ Θd }}e ->
  exists S1 Θ1,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A) ] e1 ⦂ A ⊣ Θ1 }}e
    /\ {{ S1 ↝ Sd ⊨ Θ1 ⊢[ a_sub_mode_ty | m | P0 ]
          (ptyp_to_pskl A) ⩽ (ptyp_to_pskl Bd) ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. eauto. Qed.

Lemma e_typing_inv_freeze : forall S0 m Θ0 P0 e1 Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_freeze e1) ⦂ Bd ⊣ Θd }}e ->
  m = mode_tc /\ P0 = ptyp_to_pskl Bd
  /\ exists S1 Θ1 B,
       {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_ti ; pskl_ghost ] e1 ⦂ B ⊣ Θ1 }}e
       /\ e_consis_chk S1 Θ1 (ptyp_to_pskl B) (ptyp_to_pskl Bd) Sd Θd.
Proof.
  intros * H. inversion H; subst.
  split; [ reflexivity | ]. split; [ reflexivity | ]. eauto.
Qed.

Lemma e_typing_inv_app : forall S0 m Θ0 P0 e1 e2 Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_app e1 e2) ⦂ Bd ⊣ Θd }}e ->
  exists S1 S2 Θ1 Θ2 P A A',
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] e2 ⦂ P ⊣ Θ1 }}e
    /\ {{ S1 ↝ S2 ⊨ Θ1 ⊢[ (mode_fn m) ; (pskl_arrow P P0) ] e1
          ⦂ (ptyp_arrow A Bd) ⊣ Θ2 }}e
    /\ {{ S2 ↝ Sd ⊨ Θ2 ⊢[ mode_tc ; (ptyp_to_pskl A) ] e2 ⦂ A' ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. eauto 12. Qed.

Lemma e_typing_inv_abs_all : forall S0 m Θ0 P0 e1 Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_abs e1) ⦂ Bd ⊣ Θd }}e ->
  (m <> mode_tc /\
   exists x S1 S2 Θ1 Θ2 P Q αs A B Ξ,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e
     /\ e_guess_mono S1 P S2 αs A
     /\ a_suffix Ξ /\ x `notin` S2
     /\ {{ (add x S2) ↝ Sd ⊨ ((x ~ abind_var_typ A) ++ αs ++ Θ1)
           ⊢[ (decr_mode m) ; Q ] (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ B
           ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) }}e
     /\ Bd = ptyp_arrow A B /\ Θd = Ξ ++ Θ2)
  \/ (m = mode_tc /\
      exists α A0 A Ξ,
        P0 = ptyp_to_pskl (ptyp_all A0) /\ Bd = ptyp_all A
        /\ a_suffix Ξ /\ uniq (Ξ ++ Θ0)
        /\ (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A)
        /\ α `notin` ftvar_in_ptyp A /\ α `notin` S0
        /\ {{ (add α S0) ↝ Sd ⊨ ((α ~ abind_tvar) ++ Θ0)
              ⊢[ mode_tc ;
                 (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
              (exp_abs e1) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
              ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θd) }}e)
  \/ (m = mode_tc /\
      exists x S1 Θ1 A0 A B B1 Ξ,
        P0 = ptyp_to_pskl A0 /\ Bd = ptyp_arrow A B1
        /\ {{ S0 ↝ S1 ⊨ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A)
              ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}e
        /\ a_suffix Ξ /\ uniq (Ξ ++ Θ1)
        /\ (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1)
        /\ x `notin` S1
        /\ {{ (add x S1) ↝ Sd ⊨ ((x ~ abind_var_typ A) ++ Θ1)
              ⊢[ mode_tc ; (ptyp_to_pskl B) ]
              (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ B1
              ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θd) }}e).
Proof.
  intros * H. inversion H; subst;
    [ left; split; [ assumption | eauto 20 ]
    | right; left; split; [ reflexivity | eauto 20 ]
    | right; right; split; [ reflexivity | eauto 20 ] ].
Qed.

Lemma e_typing_inv_abs_anno_all : forall S0 m Θ0 P0 Aan e1 Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_abs_anno Aan e1) ⦂ Bd ⊣ Θd }}e ->
  (m <> mode_tc /\
   exists x S1 S2 Θ1 Θ2 Θ3 P Q B Ξ,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e
     /\ e_consis_chk S1 Θ1 (ptyp_to_pskl Aan) P S2 Θ2
     /\ a_suffix Ξ /\ x `notin` S2
     /\ {{ (add x S2) ↝ Sd ⊨ ((x ~ abind_var_typ Aan) ++ Θ2)
           ⊢[ (decr_mode m) ; Q ] (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ B
           ⊣ (Ξ ++ (x ~ abind_var_typ Aan) ++ Θ3) }}e
     /\ Bd = ptyp_arrow Aan B /\ Θd = Ξ ++ Θ3)
  \/ (m = mode_tc /\
      exists α A0 A Ξ,
        P0 = ptyp_to_pskl (ptyp_all A0) /\ Bd = ptyp_all A
        /\ a_suffix Ξ /\ uniq (Ξ ++ Θ0)
        /\ (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A)
        /\ α `notin` ftvar_in_ptyp A /\ α `notin` S0
        /\ {{ (add α S0) ↝ Sd ⊨ ((α ~ abind_tvar) ++ Θ0)
              ⊢[ mode_tc ;
                 (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
              (exp_abs_anno Aan e1) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
              ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θd) }}e)
  \/ (m = mode_tc /\
      exists x S1 S2 Θ1 Θ2 A0 A' B B1 Ξ,
        P0 = ptyp_to_pskl A0 /\ Bd = ptyp_arrow A' B1
        /\ {{ S0 ↝ S1 ⊨ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A')
              ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}e
        /\ e_consis_chk S1 Θ1 (ptyp_to_pskl A') (ptyp_to_pskl Aan) S2 Θ2
        /\ a_suffix Ξ /\ uniq (Ξ ++ Θ2)
        /\ (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1)
        /\ x `notin` S2
        /\ {{ (add x S2) ↝ Sd ⊨ ((x ~ abind_var_typ Aan) ++ Θ2)
              ⊢[ mode_tc ; (ptyp_to_pskl B) ]
              (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ B1
              ⊣ (Ξ ++ (x ~ abind_var_typ Aan) ++ Θd) }}e).
Proof.
  intros * H. inversion H; subst;
    [ left; split; [ assumption | eauto 20 ]
    | right; left; split; [ reflexivity | eauto 20 ]
    | right; right; split; [ reflexivity | eauto 25 ] ].
Qed.

(* --------------------------------------------------------------------- *)
(*  §2b  THE DECOMPOSERS, WITH THE EQUATION AS A PREMISE                   *)
(*                                                                         *)
(*  prop_pat_complete.v §4b's reason, for this level's three: the runner    *)
(*  applies them to a recursive answer's PROJECTION, which must not be      *)
(*  rewritten into the shape prop_dec.v §6 states them at.                  *)
(* --------------------------------------------------------------------- *)

Lemma pskl_readback_complete_eq : forall P A,
  P = ptyp_to_pskl A ->
  exists r, pskl_readback P = Some r /\ proj1_sig r = A.
Proof. intros P A ->. apply pskl_readback_complete. Qed.

(* ⚠️ [Set Implicit Arguments] leaves the payload EXPLICIT — it occurs only
   under [ptyp_to_pskl], a FUNCTION, which is not a rigid position. *)
Arguments pskl_readback_complete_eq {P A} _.

Lemma pskl_readback_all_complete_eq : forall P A0,
  P = ptyp_to_pskl (ptyp_all A0) ->
  exists r, pskl_readback_all P = Some r /\ proj1_sig r = A0.
Proof. intros P A0 ->. apply pskl_readback_all_complete. Qed.

Arguments pskl_readback_all_complete_eq {P A0} _.

Lemma ptyp_arrow_split_complete_eq : forall A A1 A2,
  A = ptyp_arrow A1 A2 ->
  exists r, ptyp_arrow_split A = Some r /\ proj1_sig r = (A1, A2).
Proof. intros A A1 A2 ->. apply ptyp_arrow_split_complete. Qed.

(* ===================================================================== *)
(*  §3  THE MOTIVE                                                        *)
(*                                                                        *)
(*  prop_pat_complete.v §5's, with a [ptyp] output — so the chain member   *)
(*  is [swaps_ptyp] (prop_solve_det.v §2 has it).                          *)
(* ===================================================================== *)

Definition typing_answer {S0 : supply} {m : mode} {Θ0 : aenv} {P0 : pskl}
    {e : exp} (o : option (sig (typing_spec S0 m Θ0 P0 e)))
    : option typing_result :=
  match o with None => None | Some r => Some (proj1_sig r) end.

Definition typing_complete (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) : Prop :=
  forall (H : e_typing_order S0 m Θ0 P0 e),
    lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
    ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
      [<=] S0 ->
    forall Sd Θd Bd,
      {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e ->
    exists r ps,
      typing_answer (e_typing_impl S0 m Θ0 P0 e H) = Some r
      /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
      /\ swaps_atoms ps Sd [=] ty_supply r
      /\ swaps_aenv ps Θd = ty_ctx r
      /\ swaps_ptyp ps Bd = ty_out r.

(* ===================================================================== *)
(*  §4  THE MAIN INDUCTION                                                *)
(* ===================================================================== *)

Local Ltac split4 := split; [ | split; [ | split ] ].

Local Ltac ck_leaf_ty :=
  solve [ apply defs_mono_ck_complete; assumption
        | apply lc_pskl_ck_complete; assumption
        | apply lc_ptyp_ck_complete; assumption
        | apply suffix_ck_complete; assumption
        | apply uniq_ck_complete; assumption
        | apply pskl_eqb_complete; congruence
        | apply ptyp_eqb_complete; congruence
        | apply inter_is_empty_complete; assumption ].

Local Ltac ck_true_ty :=
  repeat (ck_leaf_ty || (apply andb_true_intro; split)).

Local Ltac bool_true_ty :=
  match goal with
  | |- context [ sumbool_of_bool ?b ] =>
      let Hbt := fresh "Hbt" in let Hb := fresh "Hb" in
      assert (Hbt : b = true) by ck_true_ty;
      destruct (sumbool_of_bool b) as [Hb | Hb];
      [ cbv beta iota | congruence ]
  end.

Local Ltac kill_sub Hder Hu0 Hcov0 r Hr ps Hav HS HT HQ :=
  match goal with
  | |- context [ e_sub_impl ?S ?nm ?mm ?p0 ?T ?p ?hp ?hp0 ?hd ?h ] =>
      let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
      let r0 := fresh "r0" in let Heqr := fresh "Heqr" in
      destruct (e_sub_impl_complete hp hp0 hd h Hder Hu0 Hcov0)
        as [r0 [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_sub_impl S nm mm p0 T p hp hp0 hd h)
        as [ [r Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx;
      [ assert (Heqr : r0 = exist (sub_spec S nm mm p0 T p) r Hr)
          by congruence;
        subst r0; cbn [proj1_sig] in HS, HT, HQ;
        clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

Local Ltac kill_typing Hmot Hp0 He0 HΘ0 HD0 Hu0 Hcov0 Hder r Hr ps
    Hav HS HT HQ :=
  match goal with
  | |- context [ e_typing_impl ?S ?mm ?T ?p0 ?ee ?h ] =>
      let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
      let r0 := fresh "r0" in let Heqr := fresh "Heqr" in
      destruct (Hmot h Hp0 He0 HΘ0 HD0 Hu0 Hcov0 _ _ _ Hder)
        as [r0 [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_typing_impl S mm T p0 ee h) as [ [r Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx; cbn [typing_answer proj1_sig] in Hx;
      [ assert (Heqr : r0 = r) by congruence;
        subst r0; clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

Local Ltac kill_pat_call Hp0 He0 HΘ0 HD0 Hu0 Hcov0 Hder r Hr ps
    Hav HS HT HQ :=
  match goal with
  | |- context [ e_pat_impl ?S ?mm ?T ?p0 ?ee ?h ] =>
      let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
      let r0 := fresh "r0" in let Heqr := fresh "Heqr" in
      destruct (e_pat_impl_complete h Hder Hp0 He0 HΘ0 HD0 Hu0 Hcov0)
        as [r0 [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_pat_impl S mm T p0 ee h) as [ [r Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx;
      [ assert (Heqr : r0 = exist (pat_spec S mm T p0 ee) r Hr)
          by congruence;
        subst r0; cbn [proj1_sig] in HS, HT, HQ;
        clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

Local Ltac kill_dec Hcomp t Ht :=
  let t0 := fresh "t0" in let Hs := fresh "Hs" in
  let Hpr := fresh "Hpr" in let Hcl := fresh "Hcl" in
  let Heq0 := fresh "Heq0" in
  destruct Hcomp as [t0 [Hs Hpr]];
  match type of Hs with
  | ?f = Some _ =>
      destruct f as [ [t Ht] | ] eqn:Hcl;
      try rewrite Hcl in Hs;
      [ injection Hs; intro Heq0; subst t0;
        cbn [proj1_sig] in Hpr; subst t; clear Hs Hcl; cbv beta iota
      | discriminate ]
  end.

Local Ltac open_exp_lc x :=
  match goal with
  | Hx : forall _ : _, lc_exp (open_exp_wrt_exp _ (exp_var_f _)) |- _ =>
      exact (Hx x)
  end.

Lemma e_typing_impl_complete_ind : forall S0 m Θ0 P0 e,
  e_typing_order S0 m Θ0 P0 e -> typing_complete S0 m Θ0 P0 e.
Proof.
  intros S0 m Θ0 P0 e H0.
  apply (e_typing_order_ind typing_complete); [ | exact H0 ].
  clear S0 m Θ0 P0 e H0.
  intros S0 m Θ0 P0 e hano Hano hfz Hfz habs Habs habsa Habsa
    hstep Hstep hbase Hbase hbasea Hbasea hpat happ1 Happ1 happ2 Happ2.
  unfold typing_complete.
  intros H HP0 He HΘ HD Hu Hcov Sd Θd Bd Hd.
  destruct e as [ | n0 | x | e1 | A e1 | e1 e2 | e1 A | e1 ].

  - (* ================= AT-Unit ================= *)
    rewrite e_typing_impl_equation_1.
    pose proof (e_typing_inv_unit Hd) as Ds.
    bool_true_ty.
    assert (Hcovs : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl pskl_unit [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    kill_sub Ds Hu Hcovs r Hr ps Hav HS HT HQ.
    assert (Hout : sb_out r = ptyp_to_pskl (swaps_ptyp ps Bd))
      by (rewrite <- HQ; apply swaps_pskl_ptyp_to_pskl).
    kill_dec (pskl_readback_complete_eq Hout) A0 HA0.
    eexists; exists ps.
    split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
    split4; [ exact Hav | cbn [ty_supply]; exact HS
            | cbn [ty_ctx]; exact HT | cbn [ty_out]; reflexivity ].

  - (* ============ a bound index is unreachable ============ *)
    exfalso. exact (e_typing_inv_var_b Hd).

  - (* ================= AT-Var ================= *)
    rewrite e_typing_impl_equation_3.
    destruct (e_typing_inv_var Hd) as [A [Hbd Ds]].
    assert (HA : lc_ptyp A) by (exact (lc_aenv_binds HΘ Hbd)).
    destruct (lookup_binding_complete _ _ _ Hu Hbd) as [[b Hb] [Hlk Hpr]].
    simpl in Hpr; subst b.
    rewrite Hlk. cbv beta iota.
    destruct (abind_var_typ_get_complete A) as [[A' HA'] [Hgt Hgpr]].
    simpl in Hgpr; subst A'.
    rewrite Hgt. cbv beta iota.
    bool_true_ty.
    pose proof (@ftvar_in_aenv_binds_ftv _ _ _ Hbd) as Hbf. simpl in Hbf.
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    assert (Hcovs : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl (ptyp_to_pskl A) [<=] S0)
      by (clear - Hcov Hbf HAe; simpl in *; fsetdec).
    kill_sub Ds Hu Hcovs r Hr ps Hav HS HT HQ.
    assert (Hout : sb_out r = ptyp_to_pskl (swaps_ptyp ps Bd))
      by (rewrite <- HQ; apply swaps_pskl_ptyp_to_pskl).
    kill_dec (pskl_readback_complete_eq Hout) B0 HB0.
    eexists; exists ps.
    split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
    split4; [ exact Hav | cbn [ty_supply]; exact HS
            | cbn [ty_ctx]; exact HT | cbn [ty_out]; reflexivity ].

  - (* ============ AT-Abs, and the two check-mode abs rows ============ *)
    assert (Hbody : forall y, lc_exp (open_exp_wrt_exp e1 (exp_var_f y)))
      by (inversion He; subst; assumption).
    destruct m as [ | | m' ];
      [ rewrite e_typing_impl_equation_4 | | rewrite e_typing_impl_equation_6 ].

    2: { (* -------- the CHECK-mode abs rows: STEP, then BASE -------- *)
      rewrite e_typing_impl_equation_5.
      pose proof (supply_fresh_notin S0) as Hsf.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdom0.
      destruct (pskl_readback_all P0) as [ [A0 HA0] | ] eqn:Hrba;
        cbv beta iota.

      - (* ⭐ the STEP row — the ∀ pattern is PEELED, subject unchanged *)
        destruct (e_typing_inv_abs_all Hd)
          as [ [Hm _] | [ [_ Hstepd] | [_ Hbased] ] ];
          [ exfalso; exact (Hm eq_refl) | | ].
        2: { (* the BASE row cannot fire: [⌈∀A0⌉] has no SPLIT *)
          exfalso.
          destruct Hbased
            as [xd [S1 [Θ1 [A0' [A [B [B1 [Ξ [HP0eq [_ [Dsp _]]]]]]]]]]].
          assert (Heqp : ptyp_to_pskl (ptyp_all A0) = ptyp_to_pskl A0')
            by (rewrite <- HA0; exact HP0eq).
          pose proof (ptyp_to_pskl_inj Heqp) as HeqA. subst A0'.
          cbn [ptyp_to_pskl] in Dsp.
          exact (e_split_inv_all_syn Dsp). }
        destruct Hstepd
          as [αd [A0' [A [Ξ [HP0eq [HBd [Hsuf [HuΞ [Hfil [HαA [Hαd Db]]]]]]]]]]].
        assert (Heqp : ptyp_to_pskl (ptyp_all A0)
                       = ptyp_to_pskl (ptyp_all A0'))
          by (rewrite <- HA0; exact HP0eq).
        assert (HeqA : A0' = A0)
          by (pose proof (ptyp_to_pskl_inj Heqp) as He0; congruence).
        subst A0'.
        subst Bd.
        (* ⚠️ [HA0] is the sig's own proof and is named by [Hrba]; the
           pattern's shape is read off COPIES of the motive's hypotheses. *)
        pose proof HP0 as HP0c. rewrite HA0 in HP0c.
        pose proof Hcov as Hcovc. rewrite HA0 in Hcovc.
        (* the opener, transposed onto the runner's own draw *)
        assert (Hav0 : forall a b, In (a, b) ((αd, supply_fresh S0) :: nil) ->
                       a `notin` S0 /\ b `notin` S0)
          by (intros a0 b0 [Heq0 | []]; inversion Heq0; subst;
              split; assumption).
        assert (Hsαd : swaps_atom ((αd, supply_fresh S0) :: nil) αd
                       = supply_fresh S0)
          by (cbn [swaps_atom]; unfold swap_atom;
              destruct (αd == αd); [ reflexivity | congruence ]).
        assert (HfixΘ : swaps_aenv ((αd, supply_fresh S0) :: nil) Θ0 = Θ0)
          by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
              destruct (Hav0 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
        assert (HcA0 : ftvar_in_ptyp A0 [<=] S0).
        { pose proof (ftvar_ptyp_to_pskl (ptyp_all A0)) as Hpa.
          simpl in Hpa. clear - Hcovc Hpa. simpl in *. fsetdec. }
        assert (HfixA0 : swaps_ptyp ((αd, supply_fresh S0) :: nil) A0 = A0)
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              destruct (Hav0 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb HcA0; fsetdec).
        assert (Hfixe : swaps_exp ((αd, supply_fresh S0) :: nil)
                          (exp_abs e1) = exp_abs e1)
          by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
              destruct (Hav0 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
        destruct (e_typing_swaps ((αd, supply_fresh S0) :: nil) Db
                    (S0' := add (supply_fresh S0) S0)) as [Sd1 [HSd1 Db1]].
        { cbn [swaps_atoms]. rewrite swap_atoms_add.
          rewrite (swap_atoms_notin αd (supply_fresh S0) S0)
            by (clear - Hαd Hsf; fsetdec).
          unfold swap_atom.
          destruct (αd == αd); [ reflexivity | congruence ]. }
        rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_tvar in Db1.
        rewrite ! swaps_pskl_ptyp_to_pskl, ! swaps_ptyp_open,
          ! swaps_ptyp_var_f in Db1.
        rewrite Hsαd, HfixΘ, HfixA0, Hfixe in Db1.
        (* the recursive call's own side conditions *)
        assert (HA0lc : lc_ptyp (ptyp_all A0))
          by (eapply ptyp_to_pskl_lc_inv; exact HP0c).
        assert (Hlcop : lc_pskl (ptyp_to_pskl
                  (open_ptyp_wrt_ptyp A0 (ptyp_var_f (supply_fresh S0)))))
          by (apply ptyp_to_pskl_lc; inversion HA0lc; subst; auto).
        assert (Hsfd : supply_fresh S0 `notin` dom Θ0)
          by (clear - Hsf Hdom0 Hcov; simpl in *; fsetdec).
        assert (Hu1 : uniq ((supply_fresh S0 ~ abind_tvar) ++ Θ0))
          by (clear - Hu Hsfd; solve_uniq).
        assert (HΘ1 : lc_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ0))
          by (apply lc_aenv_app_intro;
              [ constructor; [ exact I | apply lc_aenv_nil ] | exact HΘ ]).
        assert (HD1 : aenv_defs_mono ((supply_fresh S0 ~ abind_tvar) ++ Θ0))
          by (simpl; constructor; [ apply entry_def_mono_tvar | exact HD ]).
        assert (Hcov1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ0)
                        ∪ ftvar_in_pskl (ptyp_to_pskl
                             (open_ptyp_wrt_ptyp A0
                                (ptyp_var_f (supply_fresh S0))))
                        ∪ fvar_in_exp (exp_abs e1)
                        ∪ ftvar_in_exp (exp_abs e1)
                        [<=] add (supply_fresh S0) S0).
        { pose proof (ftvar_ptyp_to_pskl (open_ptyp_wrt_ptyp A0
                        (ptyp_var_f (supply_fresh S0)))) as Hpa.
          pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A0
                        (ptyp_var_f (supply_fresh S0))) as Hup.
          simpl in Hup.
          assert (Hcpat : ftvar_in_pskl (ptyp_to_pskl
                    (open_ptyp_wrt_ptyp A0 (ptyp_var_f (supply_fresh S0))))
                  [<=] add (supply_fresh S0) S0)
            by (clear - Hpa Hup HcA0; fsetdec).
          clear - Hcov Hcpat. simpl in *. fsetdec. }
        kill_typing (Hstep A0 HA0) Hlcop He HΘ1 HD1 Hu1 Hcov1 Db1
          r Hr ps2 Hav2 HS2 HT2 HQ2.
        unfold typing_spec in Hr.
        destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]].
        assert (Hfix2a : swaps_atom ps2 (supply_fresh S0) = supply_fresh S0)
          by (apply swaps_atom_notin; intros a0 b0 Hin;
              destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
              split; intro Heq0; [ apply Hka | apply Hkb ];
              rewrite <- Heq0; clear; fsetdec).
        (* the answer's context, split at the runner's own marker *)
        assert (Hctx : ty_ctx r
                  = swaps_aenv ps2 (swaps_aenv ((αd, supply_fresh S0) :: nil)
                      Ξ)
                    ++ (supply_fresh S0 ~ abind_tvar)
                    ++ swaps_aenv ps2 (swaps_aenv
                         ((αd, supply_fresh S0) :: nil) Θd))
          by (rewrite <- HT2;
              rewrite ! swaps_aenv_app_dist, swaps_aenv_one_tvar;
              rewrite Hfix2a; reflexivity).
        kill_dec (split_at_tvar_complete Hctx Hur) p Hp.
        cbn [fst snd].
        (* the ∀ body, reconstructed by CLOSING the answer *)
        assert (Hsα : swaps_atom (((αd, supply_fresh S0) :: nil) ++ ps2) αd
                      = supply_fresh S0)
          by (rewrite swaps_atom_app, Hsαd; exact Hfix2a).
        assert (HnotA : supply_fresh S0
                  `notin` ftvar_in_ptyp
                    (swaps_ptyp ps2 (swaps_ptyp
                       ((αd, supply_fresh S0) :: nil) A))).
        { assert (Hn1 : swaps_atom ((αd, supply_fresh S0) :: nil) αd
                    `notin` ftvar_in_ptyp (swaps_ptyp
                       ((αd, supply_fresh S0) :: nil) A))
            by (apply swaps_ptyp_ftv_notin; exact HαA).
          rewrite Hsαd in Hn1.
          assert (Hn2 : swaps_atom ps2 (supply_fresh S0)
                    `notin` ftvar_in_ptyp (swaps_ptyp ps2 (swaps_ptyp
                       ((αd, supply_fresh S0) :: nil) A)))
            by (apply swaps_ptyp_ftv_notin; exact Hn1).
          rewrite Hfix2a in Hn2. exact Hn2. }
        assert (Hclose : close_ptyp_wrt_ptyp (supply_fresh S0) (ty_out r)
                  = swaps_ptyp ps2 (swaps_ptyp
                      ((αd, supply_fresh S0) :: nil) A)).
        { rewrite <- HQ2. rewrite ! swaps_ptyp_open, ! swaps_ptyp_var_f.
          rewrite Hfix2a.
          apply close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp. exact HnotA. }
        (* ⚠️ [Hclose] is NOT rewritten into the goal: the [Equations]
           obligation in this branch has a type that mentions the answer's
           [close] (§8c.21's fourth trap).  It is used at the two places
           that consume it instead. *)
        assert (Hsufr : a_suffix (swaps_aenv ps2
                  (swaps_aenv ((αd, supply_fresh S0) :: nil) Ξ)))
          by (repeat apply a_suffix_swaps; exact Hsuf).
        assert (HuΞr : uniq (swaps_aenv ps2
                  (swaps_aenv ((αd, supply_fresh S0) :: nil) Ξ) ++ Θ0)).
        { assert (HfixΘ2 : swaps_aenv ps2 (swaps_aenv
                    ((αd, supply_fresh S0) :: nil) Θ0) = Θ0).
          { rewrite HfixΘ. apply swaps_aenv_fresh_id. intros a0 b0 Hin.
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
            split; clear - Hka Hkb Hcov; simpl in *; fsetdec. }
          rewrite <- HfixΘ2. rewrite <- ! swaps_aenv_app_dist.
          apply swaps_aenv_uniq. apply swaps_aenv_uniq. exact HuΞ. }
        assert (Hfilr : (dom (swaps_aenv ps2 (swaps_aenv
                    ((αd, supply_fresh S0) :: nil) Ξ)))
                  ∩ (ftvar_in_ptyp (close_ptyp_wrt_ptyp (supply_fresh S0)
                       (ty_out r))) [=] empty)
          by (rewrite Hclose; apply notin_all_inter_empty;
              repeat apply swaps_block_ftv_filter; exact Hfil).
        bool_true_ty.
        eexists; exists (((αd, supply_fresh S0) :: nil) ++ ps2).
        split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
        split4.
        + intros a0 b0 Hin. apply in_app_or in Hin.
          destruct Hin as [Hin | Hin]; [ exact (Hav0 _ _ Hin) | ].
          destruct (Hav2 _ _ Hin) as [Hka Hkb]. split; fsetdec.
        + cbn [ty_supply]. rewrite swaps_atoms_app. rewrite <- HS2.
          apply swaps_atoms_cong. symmetry. exact HSd1.
        + cbn [ty_ctx]. rewrite swaps_aenv_app. reflexivity.
        + cbn [ty_out]. rewrite swaps_ptyp_all, Hclose, swaps_ptyp_app.
          reflexivity.

      - (* ⭐ the BASE row — the pattern SPLITS, and the suffix is dropped *)
        destruct (e_typing_inv_abs_all Hd)
          as [ [Hm _] | [ [_ Hstepd] | [_ Hbased] ] ];
          [ exfalso; exact (Hm eq_refl) | | ].
        1: { (* the STEP row cannot fire: the readback would have SUCCEEDED *)
          exfalso.
          destruct Hstepd as [αd [A0' [A [Ξ [HP0eq _]]]]].
          destruct (pskl_readback_all_complete_eq HP0eq) as [rr [Hrr _]].
          rewrite Hrba in Hrr. discriminate. }
        destruct Hbased
          as [xd [S1 [Θ1 [A0 [A [B [B1 [Ξ
             [HP0eq [HBd [Dsp [Hsuf [HuΞ [Hfil [Hxd Db]]]]]]]]]]]]]]].
        subst Bd.
        kill_dec (pskl_readback_complete_eq HP0eq) A0r HA0r.
        (* the SPLIT, at the runner's own call *)
        assert (Hcovsp : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0)
          by (clear - Hcov; simpl in *; fsetdec).
        rewrite <- HP0eq in Dsp.
        destruct (e_split_impl_complete Dsp HD Hu Hcovsp)
          as [rs0 [ps1 [Hxs [Hav1 [HS1 [HT1 [HP1 HQ1]]]]]]].
        destruct (e_split_impl S0 Θ0 P0) as [ [rs Hrs] | ] eqn:Hcls;
          try rewrite Hcls in Hxs; [ | discriminate ].
        assert (Heqrs : rs0 = exist (split_spec S0 Θ0 P0) rs Hrs)
          by congruence.
        subst rs0. cbn [proj1_sig] in HS1, HT1, HP1, HQ1.
        clear Hxs Hcls. cbv beta iota.
        unfold split_spec in Hrs.
        destruct (e_split_sound Hrs Hu Hcovsp) as [Hsa [Hus [Hcvs Hpqs]]].
        pose proof (e_split_defs_mono Hrs HD) as HDs.
        pose proof (e_split_env_lc Hrs HΘ) as HΘs.
        destruct (e_split_lc Hrs HP0) as [Hlcd Hlcc].
        pose proof (e_split_supply_grows Hrs) as Hgrs.
        pose proof (e_split_supply_grows Dsp) as Hgrd.
        pose proof (supply_fresh_notin (sp_supply rs)) as Hsfs.
        pose proof (dom_subset_ftvar_in_aenv (sp_ctx rs)) as Hdoms.
        (* the two readbacks the runner performs *)
        assert (HdomR : sp_dom rs = ptyp_to_pskl (swaps_ptyp ps1 A))
          by (rewrite <- HP1; apply swaps_pskl_ptyp_to_pskl).
        assert (HcodR : sp_cod rs = ptyp_to_pskl (swaps_ptyp ps1 B))
          by (rewrite <- HQ1; apply swaps_pskl_ptyp_to_pskl).
        kill_dec (pskl_readback_complete_eq HdomR) Ad HAd.
        kill_dec (pskl_readback_complete_eq HcodR) Bd0 HBd0.
        (* the binder, along the split's chain and onto the draw *)
        assert (Hx1S : swaps_atom ps1 xd `notin` sp_supply rs)
          by (eapply swaps_notin_eq; [ symmetry; exact HS1 | exact Hxd ]).
        assert (Hx10 : swaps_atom ps1 xd `notin` S0)
          by (apply swaps_atom_dodge with (S := S0);
              [ exact Hav1 | clear - Hxd Hgrd; fsetdec ]).
        assert (Hfixe1 : swaps_exp ps1 e1 = e1)
          by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
              destruct (Hav1 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
        destruct (e_typing_swaps ps1 Db
                    (S0' := add (swaps_atom ps1 xd) (sp_supply rs)))
          as [Sd1 [HSd1 Db1]];
          [ rewrite swaps_atoms_add, HS1; reflexivity | ].
        rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_var_typ in Db1.
        rewrite ! swaps_exp_open_var, ! swaps_pskl_ptyp_to_pskl in Db1.
        rewrite HT1, Hfixe1 in Db1.
        (* onto the runner's own draw *)
        assert (Hsx1 : swaps_atom ((swaps_atom ps1 xd,
                          supply_fresh (sp_supply rs)) :: nil)
                         (swaps_atom ps1 xd) = supply_fresh (sp_supply rs))
          by (cbn [swaps_atom]; unfold swap_atom;
              destruct (swaps_atom ps1 xd == swaps_atom ps1 xd);
              [ reflexivity | congruence ]).
        assert (HcAd : ftvar_in_ptyp (swaps_ptyp ps1 A) [<=] sp_supply rs).
        { pose proof (ftvar_ptyp_to_pskl (swaps_ptyp ps1 A)) as Hpa.
          rewrite HdomR in Hpqs. clear - Hpqs Hpa. fsetdec. }
        assert (HcBd : ftvar_in_ptyp (swaps_ptyp ps1 B) [<=] sp_supply rs).
        { pose proof (ftvar_ptyp_to_pskl (swaps_ptyp ps1 B)) as Hpb.
          rewrite HcodR in Hpqs. clear - Hpqs Hpb. fsetdec. }
        assert (HfixCtx : swaps_aenv ((swaps_atom ps1 xd,
                            supply_fresh (sp_supply rs)) :: nil) (sp_ctx rs)
                          = sp_ctx rs)
          by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
              destruct Hin as [Heq0 | []]; inversion Heq0; subst;
              split; clear - Hx1S Hsfs Hcvs; fsetdec).
        assert (HfixAd : swaps_ptyp ((swaps_atom ps1 xd,
                           supply_fresh (sp_supply rs)) :: nil)
                           (swaps_ptyp ps1 A) = swaps_ptyp ps1 A)
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              destruct Hin as [Heq0 | []]; inversion Heq0; subst;
              split; clear - Hx1S Hsfs HcAd; fsetdec).
        assert (HfixBd : swaps_ptyp ((swaps_atom ps1 xd,
                           supply_fresh (sp_supply rs)) :: nil)
                           (swaps_ptyp ps1 B) = swaps_ptyp ps1 B)
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              destruct Hin as [Heq0 | []]; inversion Heq0; subst;
              split; clear - Hx1S Hsfs HcBd; fsetdec).
        assert (Hfixe2 : swaps_exp ((swaps_atom ps1 xd,
                           supply_fresh (sp_supply rs)) :: nil) e1 = e1)
          by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
              destruct Hin as [Heq0 | []]; inversion Heq0; subst;
              split; clear - Hx10 Hsfs Hgrs Hcov; simpl in *; fsetdec).
        destruct (e_typing_swaps ((swaps_atom ps1 xd,
                      supply_fresh (sp_supply rs)) :: nil) Db1
                    (S0' := add (supply_fresh (sp_supply rs))
                              (sp_supply rs))) as [Sd2 [HSd2 Db2]].
        { cbn [swaps_atoms]. rewrite swap_atoms_add,
            (swap_atoms_notin (swaps_atom ps1 xd)
               (supply_fresh (sp_supply rs)) (sp_supply rs))
              by (clear - Hx1S Hsfs; fsetdec).
          unfold swap_atom.
          destruct (swaps_atom ps1 xd == swaps_atom ps1 xd);
            [ reflexivity | congruence ]. }
        rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_var_typ in Db2.
        rewrite ! swaps_exp_open_var, ! swaps_pskl_ptyp_to_pskl in Db2.
        rewrite ! Hsx1, ! HfixCtx, ! HfixAd, ! HfixBd, ! Hfixe2 in Db2.
        (* the recursive call's own side conditions *)
        assert (Hsfd : supply_fresh (sp_supply rs) `notin` dom (sp_ctx rs))
          by (clear - Hsfs Hdoms Hcvs; fsetdec).
        assert (Hu1 : uniq ((supply_fresh (sp_supply rs)
                               ~ abind_var_typ (swaps_ptyp ps1 A))
                            ++ sp_ctx rs))
          by (clear - Hus Hsfd; solve_uniq).
        assert (HlcAd : lc_ptyp (swaps_ptyp ps1 A))
          by (rewrite HdomR in Hlcd; eapply ptyp_to_pskl_lc_inv; exact Hlcd).
        assert (HΘ1 : lc_aenv ((supply_fresh (sp_supply rs)
                                  ~ abind_var_typ (swaps_ptyp ps1 A))
                               ++ sp_ctx rs))
          by (apply lc_aenv_app_intro;
              [ constructor; [ apply lc_abind_var_typ; exact HlcAd
                             | apply lc_aenv_nil ]
              | exact HΘs ]).
        assert (HD1 : aenv_defs_mono ((supply_fresh (sp_supply rs)
                         ~ abind_var_typ (swaps_ptyp ps1 A)) ++ sp_ctx rs))
          by (simpl; constructor;
              [ apply entry_def_mono_var_typ | exact HDs ]).
        assert (Hcov1 : ftvar_in_aenv ((supply_fresh (sp_supply rs)
                            ~ abind_var_typ (swaps_ptyp ps1 A))
                         ++ sp_ctx rs)
                        ∪ ftvar_in_pskl (ptyp_to_pskl (swaps_ptyp ps1 B))
                        ∪ fvar_in_exp (open_exp_wrt_exp e1
                             (exp_var_f (supply_fresh (sp_supply rs))))
                        ∪ ftvar_in_exp (open_exp_wrt_exp e1
                             (exp_var_f (supply_fresh (sp_supply rs))))
                        [<=] add (supply_fresh (sp_supply rs))
                               (sp_supply rs)).
        { pose proof (fvar_in_exp_open_exp_wrt_exp_upper e1
                        (exp_var_f (supply_fresh (sp_supply rs)))) as Hfo.
          pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e1
                        (exp_var_f (supply_fresh (sp_supply rs)))) as Hto.
          pose proof (ftvar_ptyp_to_pskl (swaps_ptyp ps1 B)) as Hpb.
          simpl in Hfo, Hto.
          assert (Hcove : fvar_in_exp e1 ∪ ftvar_in_exp e1
                          [<=] sp_supply rs)
            by (clear - Hcov Hgrs; simpl in *; fsetdec).
          assert (Hcf : fvar_in_exp (open_exp_wrt_exp e1
                          (exp_var_f (supply_fresh (sp_supply rs))))
                        [<=] add (supply_fresh (sp_supply rs))
                               (sp_supply rs))
            by (clear - Hfo Hcove; fsetdec).
          assert (Hct : ftvar_in_exp (open_exp_wrt_exp e1
                          (exp_var_f (supply_fresh (sp_supply rs))))
                        [<=] add (supply_fresh (sp_supply rs))
                               (sp_supply rs))
            by (clear - Hto Hcove; fsetdec).
          rewrite ftvar_in_aenv_app. simpl.
          clear - Hcvs HcAd HcBd Hpb Hcf Hct. fsetdec. }
        assert (Hlccod : lc_pskl (ptyp_to_pskl (swaps_ptyp ps1 B)))
          by (rewrite <- HcodR; exact Hlcc).
        kill_typing (Hbase e1 eq_refl _ _ _ _ Hrs _ _ HdomR HcodR)
          Hlccod (Hbody (supply_fresh (sp_supply rs)))
          HΘ1 HD1 Hu1 Hcov1 Db2 r Hr ps2 Hav2 HS2 HT2 HQ2.
        unfold typing_spec in Hr.
        destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]].
        assert (Hfix2a : swaps_atom ps2 (supply_fresh (sp_supply rs))
                         = supply_fresh (sp_supply rs))
          by (apply swaps_atom_notin; intros a0 b0 Hin;
              destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
              split; intro Heq0; [ apply Hka | apply Hkb ];
              rewrite <- Heq0; clear; fsetdec).
        assert (Hfix2A : swaps_ptyp ps2 (swaps_ptyp ps1 A)
                         = swaps_ptyp ps1 A)
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb HcAd; fsetdec).
        assert (Hfix2C : swaps_aenv ps2 (sp_ctx rs) = sp_ctx rs)
          by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
              destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hcvs; fsetdec).
        assert (Hctx : ty_ctx r
                  = swaps_aenv ps2 (swaps_aenv ((swaps_atom ps1 xd,
                        supply_fresh (sp_supply rs)) :: nil)
                        (swaps_aenv ps1 Ξ))
                    ++ (supply_fresh (sp_supply rs)
                          ~ abind_var_typ (swaps_ptyp ps1 A))
                    ++ swaps_aenv ps2 (swaps_aenv ((swaps_atom ps1 xd,
                         supply_fresh (sp_supply rs)) :: nil)
                         (swaps_aenv ps1 Θd)))
          by (rewrite <- HT2;
              rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_typ;
              rewrite Hfix2a, Hfix2A; reflexivity).
        kill_dec (split_at_key_typ_complete_eq Hctx Hur) t Ht.
        cbn [fst snd].
        assert (Hsufr : a_suffix (swaps_aenv ps2 (swaps_aenv
                  ((swaps_atom ps1 xd, supply_fresh (sp_supply rs)) :: nil)
                  (swaps_aenv ps1 Ξ))))
          by (repeat apply a_suffix_swaps; exact Hsuf).
        assert (HuΞr : uniq (swaps_aenv ps2 (swaps_aenv
                  ((swaps_atom ps1 xd, supply_fresh (sp_supply rs)) :: nil)
                  (swaps_aenv ps1 Ξ)) ++ sp_ctx rs)).
        { assert (HfixΘ1 : swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom ps1 xd,
                      supply_fresh (sp_supply rs)) :: nil)
                    (swaps_aenv ps1 Θ1)) = sp_ctx rs)
            by (rewrite HT1, HfixCtx; exact Hfix2C).
          rewrite <- HfixΘ1. rewrite <- ! swaps_aenv_app_dist.
          repeat apply swaps_aenv_uniq. exact HuΞ. }
        assert (Hfilr : (dom (swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom ps1 xd,
                      supply_fresh (sp_supply rs)) :: nil)
                    (swaps_aenv ps1 Ξ))))
                  ∩ (ftvar_in_ptyp (ty_out r)) [=] empty).
        { rewrite <- HQ2. apply notin_all_inter_empty.
          repeat apply swaps_block_ftv_filter. exact Hfil. }
        bool_true_ty.
        eexists;
        exists ((ps1 ++ ((swaps_atom ps1 xd,
                  supply_fresh (sp_supply rs)) :: nil)) ++ ps2).
        split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
        split4.
        + intros a0 b0 Hin. repeat (apply in_app_or in Hin;
            destruct Hin as [Hin | Hin]).
          * exact (Hav1 _ _ Hin).
          * destruct Hin as [Heq0 | []]; inversion Heq0; subst.
            split; [ exact Hx10 | clear - Hsfs Hgrs; fsetdec ].
          * destruct (Hav2 _ _ Hin) as [Hka Hkb]. split;
              clear - Hka Hkb Hgrs; fsetdec.
        + cbn [ty_supply]. rewrite ! swaps_atoms_app. rewrite <- HS2.
          apply swaps_atoms_cong. rewrite HSd2.
          apply swaps_atoms_cong. symmetry. exact HSd1.
        + cbn [ty_ctx]. rewrite ! swaps_aenv_app. reflexivity.
        + cbn [ty_out]. rewrite swaps_ptyp_arrow. f_equal.
          * rewrite ! swaps_ptyp_app, HfixAd. exact Hfix2A.
          * rewrite ! swaps_ptyp_app. exact HQ2. }

    all: (
      (* ---------------- AT-Abs, at both non-check modes ---------------- *)
      destruct (e_typing_inv_abs_all Hd) as [ [Hm Hdat] | [ [Hmc _] | [Hmc _] ] ];
        [ | discriminate | discriminate ];
      destruct Hdat as [xd [S1 [S2 [Θ1 [Θ2 [P [Q [αs [A [B [Ξ
        [Dsp [Hg [Hsuf [Hxd [Db [HBd HΘd]]]]]]]]]]]]]]]]];
      subst Bd Θd;
      (* the SPLIT, at the runner's own call *)
      assert (Hcovsp : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec);
      destruct (e_split_impl_complete Dsp HD Hu Hcovsp)
        as [rs0 [ps1 [Hxs [Hav1 [HS1 [HT1 [HP1 HQ1]]]]]]];
      destruct (e_split_impl S0 Θ0 P0) as [ [rs Hrs] | ] eqn:Hcls;
      try rewrite Hcls in Hxs;
      [ | discriminate ];
      assert (Heqrs : rs0 = exist (split_spec S0 Θ0 P0) rs Hrs)
        by congruence;
      subst rs0; cbn [proj1_sig] in HS1, HT1, HP1, HQ1;
      clear Hxs Hcls; cbv beta iota;
      unfold split_spec in Hrs;
      destruct (e_split_sound Hrs Hu Hcovsp) as [Hsa [Hus [Hcvs Hpqs]]];
      pose proof (e_split_defs_mono Hrs HD) as HDs;
      pose proof (e_split_env_lc Hrs HΘ) as HΘs;
      destruct (e_split_lc Hrs HP0) as [Hlcd Hlcc];
      pose proof (e_split_supply_grows Hrs) as Hgrs;
      pose proof (e_split_supply_grows Dsp) as Hgrd;
      bool_true_ty;
      (* the GUESS — the runner runs its own copy, and §1's determinism
         realigns the derivation's *)
      match goal with
      | |- context [ e_guess_mono_impl ?S ?p ?h ] =>
          destruct (e_guess_mono_impl S p h) as [rg Hrg]
      end;
      cbv beta iota;
      unfold guess_spec in Hrg;
      assert (HcovD : ftvar_in_pskl (sp_dom rs) [<=] sp_supply rs)
        by (clear - Hpqs; fsetdec);
      destruct (e_guess_mono_swaps ps1 Hg (S0' := sp_supply rs))
        as [Sg1 [HSg1 Hg1]]; [ symmetry; exact HS1 | ];
      rewrite HP1 in Hg1;
      destruct (e_guess_mono_det HcovD Hg1 Hrg)
        as [psg [Havg [HSg [HTg HAg]]]];
      pose proof (e_guess_mono_supply_grows Hrg) as Hgrg;
      pose proof (e_guess_mono_generated_in_supply Hrg) as HdomG;
      pose proof (e_guess_mono_generated_ftvar Hrg) as HftG;
      pose proof (e_guess_mono_ftv_supply Hrg HcovD) as HftyG;
      pose proof (supply_fresh_notin (gr_supply rg)) as Hsf;
      pose proof (dom_subset_ftvar_in_aenv (sp_ctx rs)) as Hdoms;
      (* the binder, along BOTH chains and then onto the runner's draw *)
      assert (Hx1S : swaps_atom psg (swaps_atom ps1 xd)
                     `notin` gr_supply rg)
        by (eapply swaps_notin_eq;
            [ symmetry; rewrite <- HSg; apply swaps_atoms_cong;
              symmetry; exact HSg1
            | eapply swaps_notin_eq; [ reflexivity | exact Hxd ] ]);
      assert (Hx10 : swaps_atom psg (swaps_atom ps1 xd) `notin` S0)
        by (apply swaps_atom_dodge with (S := S0);
            [ intros a0 b0 Hin; destruct (Havg a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hgrs; fsetdec
            | apply swaps_atom_dodge with (S := S0);
              [ exact Hav1
              | pose proof (e_guess_mono_supply_grows Hg) as Hgg;
                clear - Hxd Hgrd Hgg; fsetdec ] ]);
      assert (HfixCtx1 : swaps_aenv psg (sp_ctx rs) = sp_ctx rs)
        by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct (Havg a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hcvs; fsetdec);
      assert (HfixCod1 : swaps_pskl psg (sp_cod rs) = sp_cod rs)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct (Havg a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hpqs; fsetdec);
      assert (Hfixe1 : swaps_exp (ps1 ++ psg) e1 = e1)
        by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
            apply in_app_or in Hin; destruct Hin as [Hin | Hin];
            [ destruct (Hav1 a0 b0 Hin) as [Hka Hkb]
            | destruct (Havg a0 b0 Hin) as [Hka Hkb] ];
            split; clear - Hka Hkb Hcov Hgrs; simpl in *; fsetdec);
      destruct (e_typing_swaps (ps1 ++ psg) Db
                  (S0' := add (swaps_atom psg (swaps_atom ps1 xd))
                            (gr_supply rg))) as [Sd1 [HSd1 Db1]];
      [ rewrite swaps_atoms_app;
        assert (Heq2 : swaps_atoms psg (swaps_atoms ps1 (add xd S2))
                       [=] swaps_atoms psg
                             (add (swaps_atom ps1 xd) (swaps_atoms ps1 S2)))
          by (apply swaps_atoms_cong; apply swaps_atoms_add);
        rewrite Heq2, swaps_atoms_add;
        assert (Heq3 : swaps_atoms psg (swaps_atoms ps1 S2)
                       [=] gr_supply rg)
          by (rewrite <- HSg; apply swaps_atoms_cong; symmetry; exact HSg1);
        rewrite Heq3; reflexivity
      | ];
      rewrite ! swaps_aenv_app_dist in Db1;
      rewrite ! swaps_aenv_one_var_typ in Db1;
      rewrite ! swaps_exp_open_var in Db1;
      rewrite ! swaps_aenv_app, ! swaps_pskl_app, ! swaps_atom_app,
        ! swaps_ptyp_app, ! swaps_exp_app in Db1;
      rewrite HT1, HQ1, HTg, HAg, HfixCtx1, HfixCod1 in Db1;
      rewrite swaps_exp_app in Hfixe1;
      rewrite Hfixe1 in Db1;
      (* onto the runner's own draw *)
      assert (Hsx1 : swaps_atom ((swaps_atom psg (swaps_atom ps1 xd),
                        supply_fresh (gr_supply rg)) :: nil)
                       (swaps_atom psg (swaps_atom ps1 xd))
                     = supply_fresh (gr_supply rg))
        by (cbn [swaps_atom]; unfold swap_atom;
            destruct (swaps_atom psg (swaps_atom ps1 xd)
                      == swaps_atom psg (swaps_atom ps1 xd));
            [ reflexivity | congruence ]);
      assert (HfixCtx : swaps_aenv ((swaps_atom psg (swaps_atom ps1 xd),
                          supply_fresh (gr_supply rg)) :: nil) (sp_ctx rs)
                        = sp_ctx rs)
        by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx1S Hsf Hcvs Hgrs Hgrg; fsetdec);
      assert (HfixBlk : swaps_aenv ((swaps_atom psg (swaps_atom ps1 xd),
                          supply_fresh (gr_supply rg)) :: nil) (gr_block rg)
                        = gr_block rg)
        by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx1S Hsf HdomG HftG; fsetdec);
      assert (HfixTy : swaps_ptyp ((swaps_atom psg (swaps_atom ps1 xd),
                         supply_fresh (gr_supply rg)) :: nil) (gr_type rg)
                       = gr_type rg)
        by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx1S Hsf HftyG; fsetdec);
      assert (HfixCod : swaps_pskl ((swaps_atom psg (swaps_atom ps1 xd),
                          supply_fresh (gr_supply rg)) :: nil) (sp_cod rs)
                        = sp_cod rs)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx1S Hsf Hpqs Hgrg; fsetdec);
      assert (Hfixe2 : swaps_exp ((swaps_atom psg (swaps_atom ps1 xd),
                         supply_fresh (gr_supply rg)) :: nil) e1 = e1)
        by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx10 Hsf Hgrs Hgrg Hcov; simpl in *; fsetdec);
      destruct (e_typing_swaps ((swaps_atom psg (swaps_atom ps1 xd),
                    supply_fresh (gr_supply rg)) :: nil) Db1
                  (S0' := add (supply_fresh (gr_supply rg)) (gr_supply rg)))
        as [Sd2 [HSd2 Db2]];
      [ cbn [swaps_atoms];
        rewrite swap_atoms_add,
          (swap_atoms_notin (swaps_atom psg (swaps_atom ps1 xd))
             (supply_fresh (gr_supply rg)) (gr_supply rg))
            by (clear - Hx1S Hsf; fsetdec);
        unfold swap_atom;
        destruct (swaps_atom psg (swaps_atom ps1 xd)
                  == swaps_atom psg (swaps_atom ps1 xd));
        [ reflexivity | congruence ]
      | ];
      rewrite ! swaps_aenv_app_dist in Db2;
      rewrite ! swaps_aenv_one_var_typ in Db2;
      rewrite ! swaps_exp_open_var in Db2;
      rewrite ! Hsx1, ! HfixCtx, ! HfixBlk, ! HfixTy, ! HfixCod,
        ! Hfixe2 in Db2;
      (* the recursive call's own side conditions *)
      assert (Hublk : uniq (gr_block rg ++ sp_ctx rs))
        by (eapply e_guess_mono_uniq_app;
            [ exact Hrg | exact Hcvs | exact Hus ]);
      assert (Hsfblk : supply_fresh (gr_supply rg) `notin` dom (gr_block rg))
        by (clear - Hsf HdomG; fsetdec);
      assert (Hsfctx : supply_fresh (gr_supply rg) `notin` dom (sp_ctx rs))
        by (clear - Hsf Hdoms Hcvs Hgrg; fsetdec);
      assert (Hsfd : supply_fresh (gr_supply rg)
                     `notin` dom (gr_block rg ++ sp_ctx rs))
        by (rewrite dom_app; clear - Hsfblk Hsfctx; fsetdec);
      assert (Hu1 : uniq ((supply_fresh (gr_supply rg)
                             ~ abind_var_typ (gr_type rg))
                          ++ gr_block rg ++ sp_ctx rs))
        by (clear - Hublk Hsfd; solve_uniq);
      assert (HΘ1 : lc_aenv ((supply_fresh (gr_supply rg)
                                ~ abind_var_typ (gr_type rg))
                             ++ gr_block rg ++ sp_ctx rs))
        by (apply lc_aenv_app_intro;
            [ constructor;
              [ apply lc_abind_var_typ;
                eapply e_guess_mono_lc_type; [ exact Hrg | exact Hlcd ]
              | apply lc_aenv_nil ]
            | apply lc_aenv_app_intro;
              [ eapply e_guess_mono_block_lc; exact Hrg | exact HΘs ] ]);
      assert (HD1 : aenv_defs_mono ((supply_fresh (gr_supply rg)
                       ~ abind_var_typ (gr_type rg))
                    ++ gr_block rg ++ sp_ctx rs))
        by (simpl; constructor;
            [ apply entry_def_mono_var_typ
            | apply Forall_app_intro;
              [ eapply e_guess_mono_block_defs_mono; exact Hrg | exact HDs ] ]);
      (* ⚠️⚠️ the coverage side condition is assembled SUMMAND BY SUMMAND:
         one [fsetdec] over the seven set variables at once does not
         return.  Each step below stays at four or five. *)
      assert (HS0g : S0 [<=] gr_supply rg) by (clear - Hgrs Hgrg; fsetdec);
      assert (Hcove : fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] gr_supply rg)
        by (clear - Hcov HS0g; simpl in *; fsetdec);
      assert (Hblk1 : ftvar_in_aenv (gr_block rg) [<=] gr_supply rg)
        by (clear - HftG HdomG; fsetdec);
      assert (Hctx1 : ftvar_in_aenv (sp_ctx rs) [<=] gr_supply rg)
        by (clear - Hcvs Hgrg; fsetdec);
      assert (HcQ : ftvar_in_pskl (sp_cod rs) [<=] gr_supply rg)
        by (clear - Hpqs Hgrg; fsetdec);
      assert (HcA : ftvar_in_aenv ((supply_fresh (gr_supply rg)
                        ~ abind_var_typ (gr_type rg))
                     ++ gr_block rg ++ sp_ctx rs)
                    [<=] add (supply_fresh (gr_supply rg)) (gr_supply rg))
        by (rewrite ! ftvar_in_aenv_app; simpl;
            clear - HftyG Hblk1 Hctx1; fsetdec);
      assert (Hcov1 : ftvar_in_aenv ((supply_fresh (gr_supply rg)
                          ~ abind_var_typ (gr_type rg))
                       ++ gr_block rg ++ sp_ctx rs)
                      ∪ ftvar_in_pskl (sp_cod rs)
                      ∪ fvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh (gr_supply rg))))
                      ∪ ftvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh (gr_supply rg))))
                      [<=] add (supply_fresh (gr_supply rg)) (gr_supply rg));
      [ pose proof (fvar_in_exp_open_exp_wrt_exp_upper e1
                      (exp_var_f (supply_fresh (gr_supply rg)))) as Hfo;
        pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e1
                      (exp_var_f (supply_fresh (gr_supply rg)))) as Hto;
        simpl in Hfo, Hto;
        assert (Hcf : fvar_in_exp (open_exp_wrt_exp e1
                        (exp_var_f (supply_fresh (gr_supply rg))))
                      [<=] add (supply_fresh (gr_supply rg)) (gr_supply rg))
          by (clear - Hfo Hcove; fsetdec);
        assert (Hct : ftvar_in_exp (open_exp_wrt_exp e1
                        (exp_var_f (supply_fresh (gr_supply rg))))
                      [<=] add (supply_fresh (gr_supply rg)) (gr_supply rg))
          by (clear - Hto Hcove; fsetdec);
        clear - HcA HcQ Hcf Hct; fsetdec
      | ];
      kill_typing (Habs e1 eq_refl _ _ _ _ Hrs _ _ _ Hrg) Hlcc
        (Hbody (supply_fresh (gr_supply rg))) HΘ1 HD1 Hu1 Hcov1 Db2
        r Hr ps2 Hav2 HS2 HT2 HQ2;
      unfold typing_spec in Hr;
      destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]];
      assert (Hfix2a : swaps_atom ps2 (supply_fresh (gr_supply rg))
                       = supply_fresh (gr_supply rg))
        by (apply swaps_atom_notin; intros a0 b0 Hin;
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
            split; intro Heq0; [ apply Hka | apply Hkb ];
            rewrite <- Heq0; clear; fsetdec);
      assert (Hfix2T : swaps_ptyp ps2 (gr_type rg) = gr_type rg)
        by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb HftyG; fsetdec);
      (* the answer's context, split at the runner's own marker *)
      assert (Hctx : ty_ctx r
                = swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom psg (swaps_atom ps1 xd),
                      supply_fresh (gr_supply rg)) :: nil)
                    (swaps_aenv psg (swaps_aenv ps1 Ξ)))
                  ++ (supply_fresh (gr_supply rg)
                        ~ abind_var_typ (gr_type rg))
                  ++ swaps_aenv ps2 (swaps_aenv
                       ((swaps_atom psg (swaps_atom ps1 xd),
                         supply_fresh (gr_supply rg)) :: nil)
                       (swaps_aenv psg (swaps_aenv ps1 Θ2))))
        by (rewrite <- HT2;
            rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_typ;
            rewrite Hfix2a, Hfix2T; reflexivity);
      kill_dec (split_at_key_typ_complete_eq Hctx Hur) t Ht;
      cbn [fst snd];
      assert (Hsufr : a_suffix (swaps_aenv ps2 (swaps_aenv
                ((swaps_atom psg (swaps_atom ps1 xd),
                  supply_fresh (gr_supply rg)) :: nil)
                (swaps_aenv psg (swaps_aenv ps1 Ξ)))))
        by (repeat apply a_suffix_swaps; exact Hsuf);
      bool_true_ty;
      eexists;
      exists (((ps1 ++ psg) ++ ((swaps_atom psg (swaps_atom ps1 xd),
                supply_fresh (gr_supply rg)) :: nil)) ++ ps2);
      split; [ cbn [typing_answer proj1_sig]; reflexivity | ];
      split4;
      [ intros a0 b0 Hin; repeat (apply in_app_or in Hin;
          destruct Hin as [Hin | Hin]);
        [ exact (Hav1 _ _ Hin)
        | destruct (Havg _ _ Hin) as [Hka Hkb]; split;
          clear - Hka Hkb Hgrs; fsetdec
        | destruct Hin as [Heq0 | []]; inversion Heq0; subst;
          split; [ exact Hx10 | clear - Hsf Hgrs Hgrg; fsetdec ]
        | destruct (Hav2 _ _ Hin) as [Hka Hkb]; split;
          clear - Hka Hkb Hgrs Hgrg; fsetdec ]
      | cbn [ty_supply]; rewrite ! swaps_atoms_app; rewrite <- HS2;
        apply swaps_atoms_cong; rewrite HSd2;
        apply swaps_atoms_cong; symmetry;
        rewrite <- swaps_atoms_app; exact HSd1
      | cbn [ty_ctx]; rewrite swaps_aenv_app_dist, ! swaps_aenv_app;
        reflexivity
      | cbn [ty_out]; rewrite swaps_ptyp_arrow; f_equal;
        [ rewrite ! swaps_ptyp_app, HAg, HfixTy; exact Hfix2T
        | rewrite ! swaps_ptyp_app; exact HQ2 ] ]
    ).

  - (* ======== AT-AbsAnno, and the two check-mode abs_anno rows ======== *)
    assert (Hbody : forall y, lc_exp (open_exp_wrt_exp e1 (exp_var_f y)))
      by (inversion He; subst; assumption).
    assert (HAan : lc_ptyp A) by (inversion He; subst; assumption).
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    destruct m as [ | | m' ];
      [ rewrite e_typing_impl_equation_7 | | rewrite e_typing_impl_equation_9 ].

    2: { (* ---- the CHECK-mode abs_anno rows: STEP, then BASE ---- *)
      rewrite e_typing_impl_equation_8.
      pose proof (supply_fresh_notin S0) as Hsf.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdom0.
      destruct (pskl_readback_all P0) as [ [A0 HA0] | ] eqn:Hrba;
        cbv beta iota.

      - (* the STEP row — the ∀ pattern is PEELED, subject unchanged *)
        destruct (e_typing_inv_abs_anno_all Hd)
          as [ [Hm _] | [ [_ Hstepd] | [_ Hbased] ] ];
          [ exfalso; exact (Hm eq_refl) | | ].
        2: { exfalso.
          destruct Hbased
            as [xd [S1 [S2 [Θ1 [Θ2 [A0' [A' [B [B1 [Ξ
               [HP0eq [_ [Dsp _]]]]]]]]]]]]].
          assert (Heqp : ptyp_to_pskl (ptyp_all A0) = ptyp_to_pskl A0')
            by (rewrite <- HA0; exact HP0eq).
          pose proof (ptyp_to_pskl_inj Heqp) as HeqA. subst A0'.
          cbn [ptyp_to_pskl] in Dsp.
          exact (e_split_inv_all_syn Dsp). }
        destruct Hstepd
          as [αd [A0' [A1 [Ξ [HP0eq [HBd [Hsuf [HuΞ [Hfil [HαA [Hαd Db]]]]]]]]]]].
        assert (Heqp : ptyp_to_pskl (ptyp_all A0)
                       = ptyp_to_pskl (ptyp_all A0'))
          by (rewrite <- HA0; exact HP0eq).
        assert (HeqA : A0' = A0)
          by (pose proof (ptyp_to_pskl_inj Heqp) as He0; congruence).
        subst A0'. subst Bd.
        pose proof HP0 as HP0c. rewrite HA0 in HP0c.
        pose proof Hcov as Hcovc. rewrite HA0 in Hcovc.
        assert (Hav0 : forall a b, In (a, b) ((αd, supply_fresh S0) :: nil) ->
                       a `notin` S0 /\ b `notin` S0)
          by (intros a0 b0 [Heqi | []]; inversion Heqi; subst;
              split; assumption).
        assert (Hsαd : swaps_atom ((αd, supply_fresh S0) :: nil) αd
                       = supply_fresh S0)
          by (cbn [swaps_atom]; unfold swap_atom;
              destruct (αd == αd); [ reflexivity | congruence ]).
        assert (HfixΘ : swaps_aenv ((αd, supply_fresh S0) :: nil) Θ0 = Θ0)
          by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
              destruct (Hav0 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
        assert (HcA0 : ftvar_in_ptyp A0 [<=] S0).
        { pose proof (ftvar_ptyp_to_pskl (ptyp_all A0)) as Hpa.
          simpl in Hpa. clear - Hcovc Hpa. simpl in *. fsetdec. }
        assert (HfixA0 : swaps_ptyp ((αd, supply_fresh S0) :: nil) A0 = A0)
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              destruct (Hav0 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb HcA0; fsetdec).
        assert (Hfixe : swaps_exp ((αd, supply_fresh S0) :: nil)
                          (exp_abs_anno A e1) = exp_abs_anno A e1)
          by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
              destruct (Hav0 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
        destruct (e_typing_swaps ((αd, supply_fresh S0) :: nil) Db
                    (S0' := add (supply_fresh S0) S0)) as [Sd1 [HSd1 Db1]].
        { cbn [swaps_atoms]. rewrite swap_atoms_add.
          rewrite (swap_atoms_notin αd (supply_fresh S0) S0)
            by (clear - Hαd Hsf; fsetdec).
          unfold swap_atom.
          destruct (αd == αd); [ reflexivity | congruence ]. }
        rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_tvar in Db1.
        rewrite ! swaps_pskl_ptyp_to_pskl, ! swaps_ptyp_open,
          ! swaps_ptyp_var_f in Db1.
        rewrite Hsαd, HfixΘ, HfixA0, Hfixe in Db1.
        assert (HA0lc : lc_ptyp (ptyp_all A0))
          by (eapply ptyp_to_pskl_lc_inv; exact HP0c).
        assert (Hlcop : lc_pskl (ptyp_to_pskl
                  (open_ptyp_wrt_ptyp A0 (ptyp_var_f (supply_fresh S0)))))
          by (apply ptyp_to_pskl_lc; inversion HA0lc; subst; auto).
        assert (Hsfd : supply_fresh S0 `notin` dom Θ0)
          by (clear - Hsf Hdom0 Hcov; simpl in *; fsetdec).
        assert (Hu1 : uniq ((supply_fresh S0 ~ abind_tvar) ++ Θ0))
          by (clear - Hu Hsfd; solve_uniq).
        assert (HΘ1 : lc_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ0))
          by (apply lc_aenv_app_intro;
              [ constructor; [ exact I | apply lc_aenv_nil ] | exact HΘ ]).
        assert (HD1 : aenv_defs_mono ((supply_fresh S0 ~ abind_tvar) ++ Θ0))
          by (simpl; constructor; [ apply entry_def_mono_tvar | exact HD ]).
        assert (Hcov1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ0)
                        ∪ ftvar_in_pskl (ptyp_to_pskl
                             (open_ptyp_wrt_ptyp A0
                                (ptyp_var_f (supply_fresh S0))))
                        ∪ fvar_in_exp (exp_abs_anno A e1)
                        ∪ ftvar_in_exp (exp_abs_anno A e1)
                        [<=] add (supply_fresh S0) S0).
        { pose proof (ftvar_ptyp_to_pskl (open_ptyp_wrt_ptyp A0
                        (ptyp_var_f (supply_fresh S0)))) as Hpa.
          pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A0
                        (ptyp_var_f (supply_fresh S0))) as Hup.
          simpl in Hup.
          assert (Hcpat : ftvar_in_pskl (ptyp_to_pskl
                    (open_ptyp_wrt_ptyp A0 (ptyp_var_f (supply_fresh S0))))
                  [<=] add (supply_fresh S0) S0)
            by (clear - Hpa Hup HcA0; fsetdec).
          clear - Hcov Hcpat. simpl in *. fsetdec. }
        kill_typing (Hstep A0 HA0) Hlcop He HΘ1 HD1 Hu1 Hcov1 Db1
          r Hr ps2 Hav2 HS2 HT2 HQ2.
        unfold typing_spec in Hr.
        destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]].
        assert (Hfix2a : swaps_atom ps2 (supply_fresh S0) = supply_fresh S0)
          by (apply swaps_atom_notin; intros a0 b0 Hin;
              destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
              split; intro Heqi; [ apply Hka | apply Hkb ];
              rewrite <- Heqi; clear; fsetdec).
        assert (Hctx : ty_ctx r
                  = swaps_aenv ps2 (swaps_aenv ((αd, supply_fresh S0) :: nil)
                      Ξ)
                    ++ (supply_fresh S0 ~ abind_tvar)
                    ++ swaps_aenv ps2 (swaps_aenv
                         ((αd, supply_fresh S0) :: nil) Θd))
          by (rewrite <- HT2;
              rewrite ! swaps_aenv_app_dist, swaps_aenv_one_tvar;
              rewrite Hfix2a; reflexivity).
        kill_dec (split_at_tvar_complete Hctx Hur) p Hp.
        cbn [fst snd].
        assert (HnotA : supply_fresh S0
                  `notin` ftvar_in_ptyp
                    (swaps_ptyp ps2 (swaps_ptyp
                       ((αd, supply_fresh S0) :: nil) A1))).
        { assert (Hn1 : swaps_atom ((αd, supply_fresh S0) :: nil) αd
                    `notin` ftvar_in_ptyp (swaps_ptyp
                       ((αd, supply_fresh S0) :: nil) A1))
            by (apply swaps_ptyp_ftv_notin; exact HαA).
          rewrite Hsαd in Hn1.
          assert (Hn2 : swaps_atom ps2 (supply_fresh S0)
                    `notin` ftvar_in_ptyp (swaps_ptyp ps2 (swaps_ptyp
                       ((αd, supply_fresh S0) :: nil) A1)))
            by (apply swaps_ptyp_ftv_notin; exact Hn1).
          rewrite Hfix2a in Hn2. exact Hn2. }
        assert (Hclose : close_ptyp_wrt_ptyp (supply_fresh S0) (ty_out r)
                  = swaps_ptyp ps2 (swaps_ptyp
                      ((αd, supply_fresh S0) :: nil) A1)).
        { rewrite <- HQ2. rewrite ! swaps_ptyp_open, ! swaps_ptyp_var_f.
          rewrite Hfix2a.
          apply close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp. exact HnotA. }
        assert (Hsufr : a_suffix (swaps_aenv ps2
                  (swaps_aenv ((αd, supply_fresh S0) :: nil) Ξ)))
          by (repeat apply a_suffix_swaps; exact Hsuf).
        assert (HuΞr : uniq (swaps_aenv ps2
                  (swaps_aenv ((αd, supply_fresh S0) :: nil) Ξ) ++ Θ0)).
        { assert (HfixΘ2 : swaps_aenv ps2 (swaps_aenv
                    ((αd, supply_fresh S0) :: nil) Θ0) = Θ0).
          { rewrite HfixΘ. apply swaps_aenv_fresh_id. intros a0 b0 Hin.
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
            split; clear - Hka Hkb Hcov; simpl in *; fsetdec. }
          rewrite <- HfixΘ2. rewrite <- ! swaps_aenv_app_dist.
          repeat apply swaps_aenv_uniq. exact HuΞ. }
        assert (Hfilr : (dom (swaps_aenv ps2 (swaps_aenv
                    ((αd, supply_fresh S0) :: nil) Ξ)))
                  ∩ (ftvar_in_ptyp (close_ptyp_wrt_ptyp (supply_fresh S0)
                       (ty_out r))) [=] empty)
          by (rewrite Hclose; apply notin_all_inter_empty;
              repeat apply swaps_block_ftv_filter; exact Hfil).
        bool_true_ty.
        eexists; exists (((αd, supply_fresh S0) :: nil) ++ ps2).
        split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
        split4.
        + intros a0 b0 Hin. apply in_app_or in Hin.
          destruct Hin as [Hin | Hin]; [ exact (Hav0 _ _ Hin) | ].
          destruct (Hav2 _ _ Hin) as [Hka Hkb]. split; fsetdec.
        + cbn [ty_supply]. rewrite swaps_atoms_app. rewrite <- HS2.
          apply swaps_atoms_cong. symmetry. exact HSd1.
        + cbn [ty_ctx]. rewrite swaps_aenv_app. reflexivity.
        + cbn [ty_out]. rewrite swaps_ptyp_all, Hclose, swaps_ptyp_app.
          reflexivity.

      - (* the BASE row — the pattern SPLITS, the annotation is CHECKED *)
        destruct (e_typing_inv_abs_anno_all Hd)
          as [ [Hm _] | [ [_ Hstepd] | [_ Hbased] ] ];
          [ exfalso; exact (Hm eq_refl) | | ].
        1: { exfalso.
          destruct Hstepd as [αd [A0' [A1 [Ξ [HP0eq _]]]]].
          destruct (pskl_readback_all_complete_eq HP0eq) as [rr [Hrr _]].
          rewrite Hrba in Hrr. discriminate. }
        destruct Hbased
          as [xd [S1 [S2 [Θ1 [Θ2 [A0 [A' [B [B1 [Ξ
             [HP0eq [HBd [Dsp [Dch [Hsuf [HuΞ [Hfil [Hxd Db]]]]]]]]]]]]]]]]]].
        subst Bd.
        destruct Dch as [Qc Dc].
        kill_dec (pskl_readback_complete_eq HP0eq) A0r HA0r.
        assert (Hcovsp : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0)
          by (clear - Hcov; simpl in *; fsetdec).
        rewrite <- HP0eq in Dsp.
        destruct (e_split_impl_complete Dsp HD Hu Hcovsp)
          as [rs0 [ps1 [Hxs [Hav1 [HS1 [HT1 [HP1 HQ1]]]]]]].
        destruct (e_split_impl S0 Θ0 P0) as [ [rs Hrs] | ] eqn:Hcls;
          try rewrite Hcls in Hxs; [ | discriminate ].
        assert (Heqrs : rs0 = exist (split_spec S0 Θ0 P0) rs Hrs)
          by congruence.
        subst rs0. cbn [proj1_sig] in HS1, HT1, HP1, HQ1.
        clear Hxs Hcls. cbv beta iota.
        unfold split_spec in Hrs.
        destruct (e_split_sound Hrs Hu Hcovsp) as [Hsa [Hus [Hcvs Hpqs]]].
        pose proof (e_split_defs_mono Hrs HD) as HDs.
        pose proof (e_split_env_lc Hrs HΘ) as HΘs.
        destruct (e_split_lc Hrs HP0) as [Hlcd Hlcc].
        pose proof (e_split_supply_grows Hrs) as Hgrs.
        pose proof (e_split_supply_grows Dsp) as Hgrd.
        assert (HdomR : sp_dom rs = ptyp_to_pskl (swaps_ptyp ps1 A'))
          by (rewrite <- HP1; apply swaps_pskl_ptyp_to_pskl).
        assert (HcodR : sp_cod rs = ptyp_to_pskl (swaps_ptyp ps1 B))
          by (rewrite <- HQ1; apply swaps_pskl_ptyp_to_pskl).
        kill_dec (pskl_readback_complete_eq HdomR) Ad HAd.
        kill_dec (pskl_readback_complete_eq HcodR) Bd0 HBd0.
        assert (HcAd : ftvar_in_ptyp (swaps_ptyp ps1 A') [<=] sp_supply rs).
        { pose proof (ftvar_ptyp_to_pskl (swaps_ptyp ps1 A')) as Hpa.
          rewrite HdomR in Hpqs. clear - Hpqs Hpa. fsetdec. }
        assert (HcBd : ftvar_in_ptyp (swaps_ptyp ps1 B) [<=] sp_supply rs).
        { pose proof (ftvar_ptyp_to_pskl (swaps_ptyp ps1 B)) as Hpb.
          rewrite HcodR in Hpqs. clear - Hpqs Hpb. fsetdec. }
        bool_true_ty.
        (* the ANNOTATION's consistency run *)
        assert (HfixA1 : swaps_pskl ps1 (ptyp_to_pskl A) = ptyp_to_pskl A)
          by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
              destruct (Hav1 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hcov HAe; simpl in *; fsetdec).
        destruct (e_consis_swaps ps1 Dc (Δ1' := empty) (Δ2' := empty)
                    (S0' := sp_supply rs)) as [Sc1 [HSc1 Dc1]];
          [ symmetry; apply swaps_atoms_empty
          | symmetry; apply swaps_atoms_empty
          | symmetry; exact HS1 | ].
        rewrite HT1, HfixA1, HP1 in Dc1.
        assert (Hcovc : ftvar_in_aenv (sp_ctx rs)
                        ∪ ftvar_in_pskl (ptyp_to_pskl A)
                        ∪ ftvar_in_pskl (sp_dom rs)
                        ∪ empty ∪ empty [<=] sp_supply rs)
          by (clear - Hcvs Hpqs Hcov HAe Hgrs; simpl in *; fsetdec).
        match goal with
        | |- context [ e_consis_impl ?d1 ?d2 ?S ?T ?p0 ?p ?h0 ?h1 ?hd ?h ] =>
            let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
            let rc0 := fresh "rc0" in let Heqr := fresh "Heqr" in
            destruct (e_consis_impl_complete h0 h1 hd h Dc1 Hus Hcovc)
              as [rc0 [psc [Hx [Havc [HSc [HTc HQc]]]]]];
            destruct (e_consis_impl d1 d2 S T p0 p h0 h1 hd h)
              as [ [rc Hrc] | ] eqn:Hcl;
            try rewrite Hcl in Hx;
            [ assert (Heqr : rc0 = exist (consis_spec d1 d2 S T p0 p) rc Hrc)
                by congruence;
              subst rc0; cbn [proj1_sig] in HSc, HTc, HQc;
              clear Hx Hcl; cbv beta iota
            | discriminate ]
        end.
        unfold consis_spec in Hrc.
        destruct ((proj2 (proj2 e_assign_unify_consis_sound))
                    _ _ _ _ _ _ _ _ _ Hrc Hus Hcovc) as [Hca [Huc Hcvc]].
        pose proof (e_consis_defs_mono Hrc HDs) as HDc.
        pose proof (e_consis_env_lc Hrc HΘs) as HΘc.
        pose proof (e_consis_supply_grows Hrc) as Hgrc.
        pose proof (supply_fresh_notin (cs_supply rc)) as Hsfc.
        pose proof (dom_subset_ftvar_in_aenv (cs_ctx rc)) as Hdoms.
        (* the binder, along both chains and onto the runner's draw *)
        assert (HScc : swaps_atoms psc (swaps_atoms ps1 S2) [=] cs_supply rc)
          by (rewrite <- HSc; apply swaps_atoms_cong; symmetry; exact HSc1).
        assert (Hx1S : swaps_atom psc (swaps_atom ps1 xd)
                       `notin` cs_supply rc)
          by (eapply swaps_notin_eq;
              [ symmetry; exact HScc
              | eapply swaps_notin_eq; [ reflexivity | exact Hxd ] ]).
        assert (Hx10 : swaps_atom psc (swaps_atom ps1 xd) `notin` S0)
          by (apply swaps_atom_dodge with (S := S0);
              [ intros a0 b0 Hin; destruct (Havc a0 b0 Hin) as [Hka Hkb];
                split; clear - Hka Hkb Hgrs; fsetdec
              | apply swaps_atom_dodge with (S := S0);
                [ exact Hav1
                | pose proof (e_consis_supply_grows Dc) as Hgc0;
                  clear - Hxd Hgrd Hgc0; fsetdec ] ]).
        assert (Hfixe1 : swaps_exp (ps1 ++ psc) e1 = e1)
          by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
              apply in_app_or in Hin; destruct Hin as [Hin | Hin];
              [ destruct (Hav1 a0 b0 Hin) as [Hka Hkb]
              | destruct (Havc a0 b0 Hin) as [Hka Hkb] ];
              split; clear - Hka Hkb Hcov Hgrs; simpl in *; fsetdec).
        assert (HfixA2 : swaps_ptyp (ps1 ++ psc) A = A)
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              apply in_app_or in Hin; destruct Hin as [Hin | Hin];
              [ destruct (Hav1 a0 b0 Hin) as [Hka Hkb]
              | destruct (Havc a0 b0 Hin) as [Hka Hkb] ];
              split; clear - Hka Hkb Hcov Hgrs; simpl in *; fsetdec).
        assert (HfixB1 : swaps_ptyp psc (swaps_ptyp ps1 B)
                         = swaps_ptyp ps1 B)
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              destruct (Havc a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb HcBd; fsetdec).
        assert (HfixA1c : swaps_ptyp psc (swaps_ptyp ps1 A')
                          = swaps_ptyp ps1 A')
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              destruct (Havc a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb HcAd; fsetdec).
        destruct (e_typing_swaps (ps1 ++ psc) Db
                    (S0' := add (swaps_atom psc (swaps_atom ps1 xd))
                              (cs_supply rc))) as [Sd1 [HSd1 Db1]];
          [ rewrite swaps_atoms_app;
            assert (Heq2 : swaps_atoms psc (swaps_atoms ps1 (add xd S2))
                           [=] swaps_atoms psc
                                 (add (swaps_atom ps1 xd)
                                    (swaps_atoms ps1 S2)))
              by (apply swaps_atoms_cong; apply swaps_atoms_add);
            rewrite Heq2, swaps_atoms_add, HScc; reflexivity
          | ].
        rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_var_typ in Db1.
        rewrite ! swaps_exp_open_var, ! swaps_pskl_ptyp_to_pskl in Db1.
        rewrite ! swaps_aenv_app, ! swaps_atom_app, ! swaps_ptyp_app,
          ! swaps_exp_app in Db1.
        rewrite HTc, HfixB1 in Db1.
        rewrite swaps_exp_app in Hfixe1. rewrite Hfixe1 in Db1.
        rewrite ! swaps_ptyp_app in HfixA2. rewrite HfixA2 in Db1.
        (* onto the runner's own draw *)
        assert (Hsx1 : swaps_atom ((swaps_atom psc (swaps_atom ps1 xd),
                          supply_fresh (cs_supply rc)) :: nil)
                         (swaps_atom psc (swaps_atom ps1 xd))
                       = supply_fresh (cs_supply rc))
          by (cbn [swaps_atom]; unfold swap_atom;
              destruct (swaps_atom psc (swaps_atom ps1 xd)
                        == swaps_atom psc (swaps_atom ps1 xd));
              [ reflexivity | congruence ]).
        assert (HfixCtx : swaps_aenv ((swaps_atom psc (swaps_atom ps1 xd),
                            supply_fresh (cs_supply rc)) :: nil) (cs_ctx rc)
                          = cs_ctx rc)
          by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
              destruct Hin as [Heqi | []]; inversion Heqi; subst;
              split; clear - Hx1S Hsfc Hcvc; fsetdec).
        assert (HfixAnn : swaps_ptyp ((swaps_atom psc (swaps_atom ps1 xd),
                            supply_fresh (cs_supply rc)) :: nil) A = A)
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              destruct Hin as [Heqi | []]; inversion Heqi; subst;
              split; clear - Hx10 Hsfc Hgrs Hgrc Hcov; simpl in *; fsetdec).
        assert (HfixBb : swaps_ptyp ((swaps_atom psc (swaps_atom ps1 xd),
                           supply_fresh (cs_supply rc)) :: nil)
                           (swaps_ptyp ps1 B) = swaps_ptyp ps1 B)
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              destruct Hin as [Heqi | []]; inversion Heqi; subst;
              split; clear - Hx1S Hsfc HcBd Hgrc; fsetdec).
        assert (Hfixe2 : swaps_exp ((swaps_atom psc (swaps_atom ps1 xd),
                           supply_fresh (cs_supply rc)) :: nil) e1 = e1)
          by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
              destruct Hin as [Heqi | []]; inversion Heqi; subst;
              split; clear - Hx10 Hsfc Hgrs Hgrc Hcov; simpl in *; fsetdec).
        destruct (e_typing_swaps ((swaps_atom psc (swaps_atom ps1 xd),
                      supply_fresh (cs_supply rc)) :: nil) Db1
                    (S0' := add (supply_fresh (cs_supply rc))
                              (cs_supply rc))) as [Sd2 [HSd2 Db2]].
        { cbn [swaps_atoms]. rewrite swap_atoms_add,
            (swap_atoms_notin (swaps_atom psc (swaps_atom ps1 xd))
               (supply_fresh (cs_supply rc)) (cs_supply rc))
              by (clear - Hx1S Hsfc; fsetdec).
          unfold swap_atom.
          destruct (swaps_atom psc (swaps_atom ps1 xd)
                    == swaps_atom psc (swaps_atom ps1 xd));
            [ reflexivity | congruence ]. }
        rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_var_typ in Db2.
        rewrite ! swaps_exp_open_var, ! swaps_pskl_ptyp_to_pskl in Db2.
        rewrite ! Hsx1, ! HfixCtx, ! HfixAnn, ! HfixBb, ! Hfixe2 in Db2.
        (* the recursive call's own side conditions *)
        assert (Hsfd : supply_fresh (cs_supply rc) `notin` dom (cs_ctx rc))
          by (clear - Hsfc Hdoms Hcvc; fsetdec).
        assert (Hu1 : uniq ((supply_fresh (cs_supply rc)
                               ~ abind_var_typ A) ++ cs_ctx rc))
          by (clear - Huc Hsfd; solve_uniq).
        assert (HΘ1 : lc_aenv ((supply_fresh (cs_supply rc)
                                  ~ abind_var_typ A) ++ cs_ctx rc))
          by (apply lc_aenv_app_intro;
              [ constructor; [ apply lc_abind_var_typ; exact HAan
                             | apply lc_aenv_nil ]
              | exact HΘc ]).
        assert (HD1 : aenv_defs_mono ((supply_fresh (cs_supply rc)
                         ~ abind_var_typ A) ++ cs_ctx rc))
          by (simpl; constructor;
              [ apply entry_def_mono_var_typ | exact HDc ]).
        assert (Hlccod : lc_pskl (ptyp_to_pskl (swaps_ptyp ps1 B)))
          by (rewrite <- HcodR; exact Hlcc).
        assert (Hcov1 : ftvar_in_aenv ((supply_fresh (cs_supply rc)
                            ~ abind_var_typ A) ++ cs_ctx rc)
                        ∪ ftvar_in_pskl (ptyp_to_pskl (swaps_ptyp ps1 B))
                        ∪ fvar_in_exp (open_exp_wrt_exp e1
                             (exp_var_f (supply_fresh (cs_supply rc))))
                        ∪ ftvar_in_exp (open_exp_wrt_exp e1
                             (exp_var_f (supply_fresh (cs_supply rc))))
                        [<=] add (supply_fresh (cs_supply rc))
                               (cs_supply rc)).
        { pose proof (fvar_in_exp_open_exp_wrt_exp_upper e1
                        (exp_var_f (supply_fresh (cs_supply rc)))) as Hfo.
          pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e1
                        (exp_var_f (supply_fresh (cs_supply rc)))) as Hto.
          pose proof (ftvar_ptyp_to_pskl (swaps_ptyp ps1 B)) as Hpb.
          simpl in Hfo, Hto.
          assert (HS0c : S0 [<=] cs_supply rc)
            by (clear - Hgrs Hgrc; fsetdec).
          assert (Hcove : fvar_in_exp e1 ∪ ftvar_in_exp e1
                          [<=] cs_supply rc)
            by (clear - Hcov HS0c; simpl in *; fsetdec).
          assert (HcAnn : ftvar_in_ptyp A [<=] cs_supply rc)
            by (clear - Hcov HS0c; simpl in *; fsetdec).
          assert (HcB1 : ftvar_in_ptyp (swaps_ptyp ps1 B)
                         [<=] cs_supply rc)
            by (clear - HcBd Hgrc; fsetdec).
          assert (Hcf : fvar_in_exp (open_exp_wrt_exp e1
                          (exp_var_f (supply_fresh (cs_supply rc))))
                        [<=] add (supply_fresh (cs_supply rc))
                               (cs_supply rc))
            by (clear - Hfo Hcove; fsetdec).
          assert (Hct : ftvar_in_exp (open_exp_wrt_exp e1
                          (exp_var_f (supply_fresh (cs_supply rc))))
                        [<=] add (supply_fresh (cs_supply rc))
                               (cs_supply rc))
            by (clear - Hto Hcove; fsetdec).
          rewrite ftvar_in_aenv_app. simpl.
          clear - Hcvc HcAnn HcB1 Hpb Hcf Hct. fsetdec. }
        kill_typing (Hbasea A e1 eq_refl _ _ _ _ Hrs _ _ _ Hrc _ HcodR)
          Hlccod (Hbody (supply_fresh (cs_supply rc)))
          HΘ1 HD1 Hu1 Hcov1 Db2 r Hr ps2 Hav2 HS2 HT2 HQ2.
        unfold typing_spec in Hr.
        destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]].
        assert (Hfix2a : swaps_atom ps2 (supply_fresh (cs_supply rc))
                         = supply_fresh (cs_supply rc))
          by (apply swaps_atom_notin; intros a0 b0 Hin;
              destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
              split; intro Heqi; [ apply Hka | apply Hkb ];
              rewrite <- Heqi; clear; fsetdec).
        assert (Hfix2A : swaps_ptyp ps2 A = A)
          by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
              destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hcov Hgrs Hgrc; simpl in *; fsetdec).
        assert (Hfix2C : swaps_aenv ps2 (cs_ctx rc) = cs_ctx rc)
          by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
              destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hcvc; fsetdec).
        assert (Hctx : ty_ctx r
                  = swaps_aenv ps2 (swaps_aenv
                      ((swaps_atom psc (swaps_atom ps1 xd),
                        supply_fresh (cs_supply rc)) :: nil)
                      (swaps_aenv psc (swaps_aenv ps1 Ξ)))
                    ++ (supply_fresh (cs_supply rc) ~ abind_var_typ A)
                    ++ swaps_aenv ps2 (swaps_aenv
                         ((swaps_atom psc (swaps_atom ps1 xd),
                           supply_fresh (cs_supply rc)) :: nil)
                         (swaps_aenv psc (swaps_aenv ps1 Θd))))
          by (rewrite <- HT2;
              rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_typ;
              rewrite Hfix2a, Hfix2A; reflexivity).
        kill_dec (split_at_key_typ_complete_eq Hctx Hur) t Ht.
        cbn [fst snd].
        assert (Hsufr : a_suffix (swaps_aenv ps2 (swaps_aenv
                  ((swaps_atom psc (swaps_atom ps1 xd),
                    supply_fresh (cs_supply rc)) :: nil)
                  (swaps_aenv psc (swaps_aenv ps1 Ξ)))))
          by (repeat apply a_suffix_swaps; exact Hsuf).
        assert (HuΞr : uniq (swaps_aenv ps2 (swaps_aenv
                  ((swaps_atom psc (swaps_atom ps1 xd),
                    supply_fresh (cs_supply rc)) :: nil)
                  (swaps_aenv psc (swaps_aenv ps1 Ξ))) ++ cs_ctx rc)).
        { assert (HfixΘ2 : swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom psc (swaps_atom ps1 xd),
                      supply_fresh (cs_supply rc)) :: nil)
                    (swaps_aenv psc (swaps_aenv ps1 Θ2))) = cs_ctx rc)
            by (rewrite HTc, HfixCtx; exact Hfix2C).
          rewrite <- HfixΘ2. rewrite <- ! swaps_aenv_app_dist.
          repeat apply swaps_aenv_uniq. exact HuΞ. }
        assert (Hfilr : (dom (swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom psc (swaps_atom ps1 xd),
                      supply_fresh (cs_supply rc)) :: nil)
                    (swaps_aenv psc (swaps_aenv ps1 Ξ)))))
                  ∩ (ftvar_in_ptyp (ty_out r)) [=] empty).
        { rewrite <- HQ2. apply notin_all_inter_empty.
          repeat apply swaps_block_ftv_filter. exact Hfil. }
        bool_true_ty.
        eexists;
        exists (((ps1 ++ psc) ++ ((swaps_atom psc (swaps_atom ps1 xd),
                  supply_fresh (cs_supply rc)) :: nil)) ++ ps2).
        split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
        split4.
        + intros a0 b0 Hin. repeat (apply in_app_or in Hin;
            destruct Hin as [Hin | Hin]).
          * exact (Hav1 _ _ Hin).
          * destruct (Havc _ _ Hin) as [Hka Hkb]. split;
              clear - Hka Hkb Hgrs; fsetdec.
          * destruct Hin as [Heqi | []]; inversion Heqi; subst.
            split; [ exact Hx10 | clear - Hsfc Hgrs Hgrc; fsetdec ].
          * destruct (Hav2 _ _ Hin) as [Hka Hkb]. split;
              clear - Hka Hkb Hgrs Hgrc; fsetdec.
        + cbn [ty_supply]. rewrite ! swaps_atoms_app. rewrite <- HS2.
          apply swaps_atoms_cong. rewrite HSd2.
          apply swaps_atoms_cong. symmetry.
          rewrite <- swaps_atoms_app. exact HSd1.
        + cbn [ty_ctx]. rewrite ! swaps_aenv_app. reflexivity.
        + cbn [ty_out]. rewrite swaps_ptyp_arrow. f_equal.
          * rewrite ! swaps_ptyp_app, HfixA1c.
            assert (Hfx : swaps_ptyp ((swaps_atom psc (swaps_atom ps1 xd),
                            supply_fresh (cs_supply rc)) :: nil)
                            (swaps_ptyp ps1 A') = swaps_ptyp ps1 A')
              by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
                  destruct Hin as [Heqi | []]; inversion Heqi; subst;
                  split; clear - Hx1S Hsfc HcAd Hgrc; fsetdec).
            rewrite Hfx.
            apply swaps_ptyp_fresh_id. intros a0 b0 Hin.
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
            split; clear - Hka Hkb HcAd Hgrc; fsetdec.
          * rewrite ! swaps_ptyp_app. exact HQ2. }

    all: (
      (* ------------ AT-AbsAnno, at both non-check modes ------------ *)
      destruct (e_typing_inv_abs_anno_all Hd)
        as [ [Hm Hdat] | [ [Hmc _] | [Hmc _] ] ];
        [ | discriminate | discriminate ];
      destruct Hdat as [xd [S1 [S2 [Θ1 [Θ2 [Θ3 [P [Q [B [Ξ
        [Dsp [Dch [Hsuf [Hxd [Db [HBd HΘd]]]]]]]]]]]]]]]];
      subst Bd Θd;
      destruct Dch as [Qc Dc];
      assert (Hcovsp : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec);
      destruct (e_split_impl_complete Dsp HD Hu Hcovsp)
        as [rs0 [ps1 [Hxs [Hav1 [HS1 [HT1 [HP1 HQ1]]]]]]];
      destruct (e_split_impl S0 Θ0 P0) as [ [rs Hrs] | ] eqn:Hcls;
      try rewrite Hcls in Hxs;
      [ | discriminate ];
      assert (Heqrs : rs0 = exist (split_spec S0 Θ0 P0) rs Hrs)
        by congruence;
      subst rs0; cbn [proj1_sig] in HS1, HT1, HP1, HQ1;
      clear Hxs Hcls; cbv beta iota;
      unfold split_spec in Hrs;
      destruct (e_split_sound Hrs Hu Hcovsp) as [Hsa [Hus [Hcvs Hpqs]]];
      pose proof (e_split_defs_mono Hrs HD) as HDs;
      pose proof (e_split_env_lc Hrs HΘ) as HΘs;
      destruct (e_split_lc Hrs HP0) as [Hlcd Hlcc];
      pose proof (e_split_supply_grows Hrs) as Hgrs;
      pose proof (e_split_supply_grows Dsp) as Hgrd;
      bool_true_ty;
      assert (HfixA1 : swaps_pskl ps1 (ptyp_to_pskl A) = ptyp_to_pskl A)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct (Hav1 a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hcov HAe; simpl in *; fsetdec);
      destruct (e_consis_swaps ps1 Dc (Δ1' := empty) (Δ2' := empty)
                  (S0' := sp_supply rs)) as [Sc1 [HSc1 Dc1]];
      [ symmetry; apply swaps_atoms_empty
      | symmetry; apply swaps_atoms_empty
      | symmetry; exact HS1
      | ];
      rewrite HT1, HP1, HfixA1 in Dc1;
      assert (Hcovc : ftvar_in_aenv (sp_ctx rs) ∪ ftvar_in_pskl (sp_dom rs)
                      ∪ ftvar_in_pskl (ptyp_to_pskl A) ∪ empty ∪ empty
                      [<=] sp_supply rs)
        by (clear - Hcvs Hpqs Hcov HAe Hgrs; simpl in *; fsetdec);
      match goal with
      | |- context [ e_consis_impl ?d1 ?d2 ?S ?T ?p0 ?p ?h0 ?h1 ?hd ?h ] =>
          destruct (e_consis_impl_complete h0 h1 hd h Dc1 Hus Hcovc)
            as [rc0 [psc [Hxc [Havc [HSc [HTc HQc]]]]]];
          destruct (e_consis_impl d1 d2 S T p0 p h0 h1 hd h)
            as [ [rc Hrc] | ] eqn:Hclc;
          try rewrite Hclc in Hxc;
          [ | discriminate ];
          assert (Heqrc : rc0 = exist (consis_spec d1 d2 S T p0 p) rc Hrc)
            by congruence;
          subst rc0; cbn [proj1_sig] in HSc, HTc, HQc;
          clear Hxc Hclc; cbv beta iota
      end;
      unfold consis_spec in Hrc;
      destruct ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hrc Hus Hcovc) as [Hca [Huc Hcvc]];
      pose proof (e_consis_defs_mono Hrc HDs) as HDc;
      pose proof (e_consis_env_lc Hrc HΘs) as HΘc;
      pose proof (e_consis_supply_grows Hrc) as Hgrc;
      pose proof (supply_fresh_notin (cs_supply rc)) as Hsfc;
      pose proof (dom_subset_ftvar_in_aenv (cs_ctx rc)) as Hdoms;
      assert (HScc : swaps_atoms psc (swaps_atoms ps1 S2) [=] cs_supply rc)
        by (rewrite <- HSc; apply swaps_atoms_cong; symmetry; exact HSc1);
      assert (Hx1S : swaps_atom psc (swaps_atom ps1 xd)
                     `notin` cs_supply rc)
        by (eapply swaps_notin_eq;
            [ symmetry; exact HScc
            | eapply swaps_notin_eq; [ reflexivity | exact Hxd ] ]);
      assert (Hx10 : swaps_atom psc (swaps_atom ps1 xd) `notin` S0)
        by (apply swaps_atom_dodge with (S := S0);
            [ intros a0 b0 Hin; destruct (Havc a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hgrs; fsetdec
            | apply swaps_atom_dodge with (S := S0);
              [ exact Hav1
              | pose proof (e_consis_supply_grows Dc) as Hgc0;
                clear - Hxd Hgrd Hgc0; fsetdec ] ]);
      assert (Hfixe1 : swaps_exp (ps1 ++ psc) e1 = e1)
        by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
            apply in_app_or in Hin; destruct Hin as [Hin | Hin];
            [ destruct (Hav1 a0 b0 Hin) as [Hka Hkb]
            | destruct (Havc a0 b0 Hin) as [Hka Hkb] ];
            split; clear - Hka Hkb Hcov Hgrs; simpl in *; fsetdec);
      assert (HfixA2 : swaps_ptyp (ps1 ++ psc) A = A)
        by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
            apply in_app_or in Hin; destruct Hin as [Hin | Hin];
            [ destruct (Hav1 a0 b0 Hin) as [Hka Hkb]
            | destruct (Havc a0 b0 Hin) as [Hka Hkb] ];
            split; clear - Hka Hkb Hcov Hgrs; simpl in *; fsetdec);
      assert (HfixQ0 : swaps_pskl psc (sp_cod rs) = sp_cod rs)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct (Havc a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hpqs; fsetdec);
      destruct (e_typing_swaps (ps1 ++ psc) Db
                  (S0' := add (swaps_atom psc (swaps_atom ps1 xd))
                            (cs_supply rc))) as [Sd1 [HSd1 Db1]];
      [ rewrite swaps_atoms_app;
        assert (Heq2 : swaps_atoms psc (swaps_atoms ps1 (add xd S2))
                       [=] swaps_atoms psc
                             (add (swaps_atom ps1 xd) (swaps_atoms ps1 S2)))
          by (apply swaps_atoms_cong; apply swaps_atoms_add);
        rewrite Heq2, swaps_atoms_add, HScc; reflexivity
      | ];
      rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_var_typ in Db1;
      rewrite ! swaps_exp_open_var in Db1;
      rewrite ! swaps_aenv_app, ! swaps_pskl_app, ! swaps_atom_app,
        ! swaps_ptyp_app, ! swaps_exp_app in Db1;
      rewrite swaps_exp_app in Hfixe1;
      rewrite ! swaps_ptyp_app in HfixA2;
      rewrite HQ1, HTc, HfixQ0, Hfixe1, HfixA2 in Db1;
      assert (Hsx1 : swaps_atom ((swaps_atom psc (swaps_atom ps1 xd),
                        supply_fresh (cs_supply rc)) :: nil)
                       (swaps_atom psc (swaps_atom ps1 xd))
                     = supply_fresh (cs_supply rc))
        by (cbn [swaps_atom]; unfold swap_atom;
            destruct (swaps_atom psc (swaps_atom ps1 xd)
                      == swaps_atom psc (swaps_atom ps1 xd));
            [ reflexivity | congruence ]);
      assert (HfixCtx : swaps_aenv ((swaps_atom psc (swaps_atom ps1 xd),
                          supply_fresh (cs_supply rc)) :: nil) (cs_ctx rc)
                        = cs_ctx rc)
        by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heqi | []]; inversion Heqi; subst;
            split; clear - Hx1S Hsfc Hcvc; fsetdec);
      assert (HfixCod : swaps_pskl ((swaps_atom psc (swaps_atom ps1 xd),
                          supply_fresh (cs_supply rc)) :: nil) (sp_cod rs)
                        = sp_cod rs)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heqi | []]; inversion Heqi; subst;
            split; clear - Hx1S Hsfc Hpqs Hgrc; fsetdec);
      assert (HfixAnn : swaps_ptyp ((swaps_atom psc (swaps_atom ps1 xd),
                          supply_fresh (cs_supply rc)) :: nil) A = A)
        by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heqi | []]; inversion Heqi; subst;
            split; clear - Hx10 Hsfc Hgrs Hgrc Hcov; simpl in *; fsetdec);
      assert (Hfixe2 : swaps_exp ((swaps_atom psc (swaps_atom ps1 xd),
                         supply_fresh (cs_supply rc)) :: nil) e1 = e1)
        by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heqi | []]; inversion Heqi; subst;
            split; clear - Hx10 Hsfc Hgrs Hgrc Hcov; simpl in *; fsetdec);
      destruct (e_typing_swaps ((swaps_atom psc (swaps_atom ps1 xd),
                    supply_fresh (cs_supply rc)) :: nil) Db1
                  (S0' := add (supply_fresh (cs_supply rc)) (cs_supply rc)))
        as [Sd2 [HSd2 Db2]];
      [ cbn [swaps_atoms];
        rewrite swap_atoms_add,
          (swap_atoms_notin (swaps_atom psc (swaps_atom ps1 xd))
             (supply_fresh (cs_supply rc)) (cs_supply rc))
            by (clear - Hx1S Hsfc; fsetdec);
        unfold swap_atom;
        destruct (swaps_atom psc (swaps_atom ps1 xd)
                  == swaps_atom psc (swaps_atom ps1 xd));
        [ reflexivity | congruence ]
      | ];
      rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_var_typ in Db2;
      rewrite ! swaps_exp_open_var in Db2;
      rewrite ! Hsx1, ! HfixCtx, ! HfixCod, ! HfixAnn, ! Hfixe2 in Db2;
      assert (Hsfd : supply_fresh (cs_supply rc) `notin` dom (cs_ctx rc))
        by (clear - Hsfc Hdoms Hcvc; fsetdec);
      assert (Hu1 : uniq ((supply_fresh (cs_supply rc)
                             ~ abind_var_typ A) ++ cs_ctx rc))
        by (clear - Huc Hsfd; solve_uniq);
      assert (HΘ1 : lc_aenv ((supply_fresh (cs_supply rc)
                                ~ abind_var_typ A) ++ cs_ctx rc))
        by (apply lc_aenv_app_intro;
            [ constructor; [ apply lc_abind_var_typ; exact HAan
                           | apply lc_aenv_nil ]
            | exact HΘc ]);
      assert (HD1 : aenv_defs_mono ((supply_fresh (cs_supply rc)
                       ~ abind_var_typ A) ++ cs_ctx rc))
        by (simpl; constructor;
            [ apply entry_def_mono_var_typ | exact HDc ]);
      assert (Hcov1 : ftvar_in_aenv ((supply_fresh (cs_supply rc)
                          ~ abind_var_typ A) ++ cs_ctx rc)
                      ∪ ftvar_in_pskl (sp_cod rs)
                      ∪ fvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh (cs_supply rc))))
                      ∪ ftvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh (cs_supply rc))))
                      [<=] add (supply_fresh (cs_supply rc)) (cs_supply rc));
      [ pose proof (fvar_in_exp_open_exp_wrt_exp_upper e1
                      (exp_var_f (supply_fresh (cs_supply rc)))) as Hfo;
        pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e1
                      (exp_var_f (supply_fresh (cs_supply rc)))) as Hto;
        simpl in Hfo, Hto;
        assert (HS0c : S0 [<=] cs_supply rc)
          by (clear - Hgrs Hgrc; fsetdec);
        assert (Hcove : fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] cs_supply rc)
          by (clear - Hcov HS0c; simpl in *; fsetdec);
        assert (HcAnn : ftvar_in_ptyp A [<=] cs_supply rc)
          by (clear - Hcov HS0c; simpl in *; fsetdec);
        assert (HcQ : ftvar_in_pskl (sp_cod rs) [<=] cs_supply rc)
          by (clear - Hpqs Hgrc; fsetdec);
        assert (Hcf : fvar_in_exp (open_exp_wrt_exp e1
                        (exp_var_f (supply_fresh (cs_supply rc))))
                      [<=] add (supply_fresh (cs_supply rc)) (cs_supply rc))
          by (clear - Hfo Hcove; fsetdec);
        assert (Hct : ftvar_in_exp (open_exp_wrt_exp e1
                        (exp_var_f (supply_fresh (cs_supply rc))))
                      [<=] add (supply_fresh (cs_supply rc)) (cs_supply rc))
          by (clear - Hto Hcove; fsetdec);
        rewrite ftvar_in_aenv_app; simpl;
        clear - Hcvc HcAnn HcQ Hcf Hct; fsetdec
      | ];
      kill_typing (Habsa A e1 eq_refl _ _ _ _ Hrs _ _ _ Hrc) Hlcc
        (Hbody (supply_fresh (cs_supply rc))) HΘ1 HD1 Hu1 Hcov1 Db2
        r Hr ps2 Hav2 HS2 HT2 HQ2;
      unfold typing_spec in Hr;
      destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]];
      assert (Hfix2a : swaps_atom ps2 (supply_fresh (cs_supply rc))
                       = supply_fresh (cs_supply rc))
        by (apply swaps_atom_notin; intros a0 b0 Hin;
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
            split; intro Heqi; [ apply Hka | apply Hkb ];
            rewrite <- Heqi; clear; fsetdec);
      assert (Hfix2A : swaps_ptyp ps2 A = A)
        by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hcov Hgrs Hgrc; simpl in *; fsetdec);
      assert (Hctx : ty_ctx r
                = swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom psc (swaps_atom ps1 xd),
                      supply_fresh (cs_supply rc)) :: nil)
                    (swaps_aenv psc (swaps_aenv ps1 Ξ)))
                  ++ (supply_fresh (cs_supply rc) ~ abind_var_typ A)
                  ++ swaps_aenv ps2 (swaps_aenv
                       ((swaps_atom psc (swaps_atom ps1 xd),
                         supply_fresh (cs_supply rc)) :: nil)
                       (swaps_aenv psc (swaps_aenv ps1 Θ3))))
        by (rewrite <- HT2;
            rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_typ;
            rewrite Hfix2a, Hfix2A; reflexivity);
      kill_dec (split_at_key_typ_complete_eq Hctx Hur) t Ht;
      cbn [fst snd];
      assert (Hsufr : a_suffix (swaps_aenv ps2 (swaps_aenv
                ((swaps_atom psc (swaps_atom ps1 xd),
                  supply_fresh (cs_supply rc)) :: nil)
                (swaps_aenv psc (swaps_aenv ps1 Ξ)))))
        by (repeat apply a_suffix_swaps; exact Hsuf);
      bool_true_ty;
      eexists;
      exists (((ps1 ++ psc) ++ ((swaps_atom psc (swaps_atom ps1 xd),
                supply_fresh (cs_supply rc)) :: nil)) ++ ps2);
      split; [ cbn [typing_answer proj1_sig]; reflexivity | ];
      split4;
      [ intros a0 b0 Hin; repeat (apply in_app_or in Hin;
          destruct Hin as [Hin | Hin]);
        [ exact (Hav1 _ _ Hin)
        | destruct (Havc _ _ Hin) as [Hka Hkb]; split;
          clear - Hka Hkb Hgrs; fsetdec
        | destruct Hin as [Heqi | []]; inversion Heqi; subst;
          split; [ exact Hx10 | clear - Hsfc Hgrs Hgrc; fsetdec ]
        | destruct (Hav2 _ _ Hin) as [Hka Hkb]; split;
          clear - Hka Hkb Hgrs Hgrc; fsetdec ]
      | cbn [ty_supply]; rewrite ! swaps_atoms_app; rewrite <- HS2;
        apply swaps_atoms_cong; rewrite HSd2;
        apply swaps_atoms_cong; symmetry;
        rewrite <- swaps_atoms_app; exact HSd1
      | cbn [ty_ctx]; rewrite swaps_aenv_app_dist, ! swaps_aenv_app;
        reflexivity
      | cbn [ty_out]; rewrite swaps_ptyp_arrow; f_equal;
        [ rewrite ! swaps_ptyp_app, HfixA2, HfixAnn; exact Hfix2A
        | rewrite ! swaps_ptyp_app; exact HQ2 ] ]
    ).

  - (* ================= AT-App ================= *)
    rewrite e_typing_impl_equation_10.
    destruct (e_typing_inv_app Hd)
      as [S1 [S2 [Θ1 [Θ2 [P [A [A' [D1 [D2 D3]]]]]]]]].
    assert (He1 : lc_exp e1) by (inversion He; subst; assumption).
    assert (He2 : lc_exp e2) by (inversion He; subst; assumption).
    (* the ARGUMENT's skeleton — level 7's headline *)
    assert (Hcov1 : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl pskl_ghost
                    ∪ fvar_in_exp e2 ∪ ftvar_in_exp e2 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    kill_pat_call lc_pskl_ghost He2 HΘ HD Hu Hcov1 D1
      r2 Hr2 ps1 Hav1 HS1 HT1 HQ1.
    unfold pat_spec in Hr2.
    destruct (e_pat_sound Hr2 Hu Hcov1) as [Ha2 [Hu2 [Hcv2 Hq2]]].
    pose proof (e_pat_defs_mono Hr2 HD) as HD2.
    destruct (e_pat_lc_env Hr2 lc_pskl_ghost He2 HΘ HD) as [Hlc2 HΘ2].
    pose proof (e_pat_supply_grows Hr2) as Hgr2.
    (* the FUNCTION, at the argument's answer *)
    assert (HfixP : forall X, ftvar_in_pskl X [<=] S0 -> swaps_pskl ps1 X = X)
      by (intros X HX; apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Hka Hkb]; split; fsetdec).
    assert (Hfixe : forall E, fvar_in_exp E ∪ ftvar_in_exp E [<=] S0 ->
              swaps_exp ps1 E = E)
      by (intros E HE; apply swaps_exp_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Hka Hkb]; split; fsetdec).
    destruct (e_typing_swaps ps1 D2 (S0' := pt_supply r2))
      as [Sd2 [HSd2 D2t]]; [ symmetry; exact HS1 | ].
    rewrite HT1 in D2t.
    rewrite swaps_pskl_arrow, HQ1 in D2t.
    rewrite (HfixP P0) in D2t by (clear - Hcov; simpl in *; fsetdec).
    rewrite (Hfixe e1) in D2t by (clear - Hcov; simpl in *; fsetdec).
    rewrite swaps_ptyp_arrow in D2t.
    assert (Hcov2 : ftvar_in_aenv (pt_ctx r2)
                    ∪ ftvar_in_pskl (pskl_arrow (pt_skel r2) P0)
                    ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] pt_supply r2)
      by (clear - Hcov Hcv2 Hq2 Hgr2; simpl in *; fsetdec).
    kill_typing (Happ1 e1 e2 eq_refl _ _ _ Hr2)
      (lc_pskl_arrow _ _ Hlc2 HP0) He1 HΘ2 HD2 Hu2 Hcov2 D2t
      r1 Hr1 ps2 Hav2 HS2 HT2 HQ2.
    unfold typing_spec in Hr1.
    destruct (e_typing_sound Hr1 Hu2 Hcov2) as [Ha1 [Hu1 [Hcv1 Hq1]]].
    pose proof (e_typing_defs_mono Hr1 HD2) as HD1.
    destruct (e_typing_lc_env Hr1 (lc_pskl_arrow _ _ Hlc2 HP0) He1 HΘ2 HD2)
      as [Hlc1 HΘ1].
    pose proof (e_typing_supply_grows Hr1) as Hgr1.
    (* the function's arrow, decomposed AT the runner's answer *)
    assert (Hout : ty_out r1
              = ptyp_arrow (swaps_ptyp ps2 (swaps_ptyp ps1 A))
                  (swaps_ptyp ps2 (swaps_ptyp ps1 Bd)))
      by (rewrite <- HQ2; rewrite ! swaps_ptyp_arrow; reflexivity).
    kill_dec (ptyp_arrow_split_complete_eq Hout) p Hp.
    cbn [fst snd].
    (* the ARGUMENT again, at the function's domain *)
    assert (Hfixe2 : swaps_exp ps2 (swaps_exp ps1 e2) = e2).
    { rewrite (Hfixe e2) by (clear - Hcov; simpl in *; fsetdec).
      apply swaps_exp_fresh_id. intros a0 b0 Hin.
      destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
      split; clear - Hka Hkb Hcov Hgr2; simpl in *; fsetdec. }
    destruct (e_typing_swaps (ps1 ++ ps2) D3 (S0' := ty_supply r1))
      as [Sd3 [HSd3 D3t]];
      [ rewrite swaps_atoms_app; rewrite <- HS2;
        apply swaps_atoms_cong; exact HSd2 | ].
    rewrite ! swaps_aenv_app, ! swaps_pskl_app, ! swaps_exp_app in D3t.
    rewrite HT2, ! swaps_pskl_ptyp_to_pskl, Hfixe2 in D3t.
    assert (Hcov3 : ftvar_in_aenv (ty_ctx r1)
                    ∪ ftvar_in_pskl
                        (ptyp_to_pskl (swaps_ptyp ps2 (swaps_ptyp ps1 A)))
                    ∪ fvar_in_exp e2 ∪ ftvar_in_exp e2 [<=] ty_supply r1).
    { pose proof (ftvar_ptyp_to_pskl
                    (swaps_ptyp ps2 (swaps_ptyp ps1 A))) as Hpa.
      rewrite Hout in Hq1. simpl in Hq1.
      clear - Hcov Hcv1 Hq1 Hpa Hgr1 Hgr2; simpl in *; fsetdec. }
    assert (Hlcdom : lc_ptyp (swaps_ptyp ps2 (swaps_ptyp ps1 A))).
    { rewrite Hout in Hlc1. inversion Hlc1; subst; assumption. }
    (* ⚠️ a COPY: [Hr1] is bound by the runner's own [match], and the
       obligation in that branch has a type that mentions it. *)
    pose proof Hr1 as Hr1'. unfold typing_spec in Hr1'.
    rewrite Hout in Hr1'.
    kill_typing (Happ2 e1 e2 eq_refl _ _ _ Hr2 _ _ _ _ Hr1')
      (ptyp_to_pskl_lc Hlcdom) He2 HΘ1 HD1 Hu1 Hcov3 D3t
      r3 Hr3 ps3 Hav3 HS3 HT3 HQ3.
    unfold typing_spec in Hr3.
    eexists; exists ((ps1 ++ ps2) ++ ps3).
    split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
    split4.
    + intros a0 b0 Hin. repeat (apply in_app_or in Hin;
        destruct Hin as [Hin | Hin]).
      * exact (Hav1 _ _ Hin).
      * destruct (Hav2 _ _ Hin) as [Hka Hkb]. split;
          clear - Hka Hkb Hgr2; fsetdec.
      * destruct (Hav3 _ _ Hin) as [Hka Hkb]. split;
          clear - Hka Hkb Hgr1 Hgr2; fsetdec.
    + cbn [ty_supply]. rewrite swaps_atoms_app. rewrite <- HS3.
      apply swaps_atoms_cong. symmetry. exact HSd3.
    + cbn [ty_ctx]. rewrite ! swaps_aenv_app. exact HT3.
    + cbn [ty_out].
      assert (Hfix3 : swaps_ptyp ps3 (swaps_ptyp ps2 (swaps_ptyp ps1 Bd))
                      = swaps_ptyp ps2 (swaps_ptyp ps1 Bd)).
      { apply swaps_ptyp_fresh_id. intros a0 b0 Hin.
        destruct (Hav3 a0 b0 Hin) as [Hka Hkb].
        rewrite Hout in Hq1. simpl in Hq1.
        split; clear - Hka Hkb Hq1; fsetdec. }
      rewrite ! swaps_ptyp_app. exact Hfix3.

  - (* ================= AT-Anno ================= *)
    rewrite e_typing_impl_equation_11.
    destruct (e_typing_inv_anno Hd) as [S1 [Θ1 [D1 D2]]].
    assert (HA : lc_ptyp A) by (inversion He; subst; assumption).
    assert (He1 : lc_exp e1) by (inversion He; subst; assumption).
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    assert (Hcov1 : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl (ptyp_to_pskl A)
                    ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] S0)
      by (clear - Hcov HAe; simpl in *; fsetdec).
    kill_typing (Hano e1 A eq_refl) (ptyp_to_pskl_lc HA) He1 HΘ HD Hu Hcov1 D1
      r1 Hr1 ps1 Hav1 HS1 HT1 HQ1.
    unfold typing_spec in Hr1.
    destruct (e_typing_sound Hr1 Hu Hcov1) as [Ha1 [Hu1 [Hcv1 Hq1]]].
    pose proof (e_typing_defs_mono Hr1 HD) as HD1.
    destruct (e_typing_lc_env Hr1 (ptyp_to_pskl_lc HA) He1 HΘ HD)
      as [Hlc1 HΘ1].
    pose proof (e_typing_supply_grows Hr1) as Hgr1.
    (* the annotation is an INPUT, so the chain fixes it *)
    assert (HfixA : swaps_ptyp ps1 A = A)
      by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Hka Hkb];
          split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
    rewrite HfixA in HQ1.
    bool_true_ty.
    bool_true_ty.
    destruct (e_sub_swaps ps1 D2 (S0' := ty_supply r1))
      as [Sd2 [HSd2 D2t]]; [ symmetry; exact HS1 | ].
    rewrite HT1, ! swaps_pskl_ptyp_to_pskl, HfixA in D2t.
    assert (HfixP0 : swaps_pskl ps1 P0 = P0)
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Hka Hkb];
          split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
    rewrite HfixP0 in D2t.
    assert (Hcovs : ftvar_in_aenv (ty_ctx r1) ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl (ptyp_to_pskl A) [<=] ty_supply r1)
      by (clear - Hcov Hcv1 HAe Hgr1; simpl in *; fsetdec).
    kill_sub D2t Hu1 Hcovs r Hr ps2 Hav2 HS2 HT2 HQ2.
    assert (Hout : sb_out r
              = ptyp_to_pskl (swaps_ptyp ps2 (swaps_ptyp ps1 Bd)))
      by (rewrite <- HQ2; rewrite ! swaps_pskl_ptyp_to_pskl; reflexivity).
    kill_dec (pskl_readback_complete_eq Hout) B0 HB0.
    eexists; exists (ps1 ++ ps2).
    split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
    split4.
    + intros a0 b0 Hin. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin]; [ exact (Hav1 _ _ Hin) | ].
      destruct (Hav2 _ _ Hin) as [Hka Hkb]. split;
        clear - Hka Hkb Hgr1; fsetdec.
    + cbn [ty_supply]. rewrite swaps_atoms_app. rewrite <- HS2.
      apply swaps_atoms_cong. symmetry. exact HSd2.
    + cbn [ty_ctx]. rewrite swaps_aenv_app. exact HT2.
    + cbn [ty_out]. rewrite swaps_ptyp_app. reflexivity.

  - (* ================= AT-Freeze ================= *)
    destruct (e_typing_inv_freeze Hd)
      as [-> [HP0eq [S1 [Θ1 [B [D1 Dc]]]]]].
    subst P0.
    rewrite e_typing_impl_equation_13.
    assert (He1 : lc_exp e1) by (inversion He; subst; assumption).
    assert (HBd : lc_ptyp Bd)
      by (eapply ptyp_to_pskl_lc_inv; exact HP0).
    pose proof (ftvar_ptyp_to_pskl Bd) as HBe.
    kill_dec (pskl_readback_complete_eq
                (eq_refl : ptyp_to_pskl Bd = ptyp_to_pskl Bd)) A0 HA0.
    assert (Hcov1 : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl pskl_ghost
                    ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    kill_typing (Hfz e1 eq_refl) lc_pskl_ghost He1 HΘ HD Hu Hcov1 D1
      r1 Hr1 ps1 Hav1 HS1 HT1 HQ1.
    unfold typing_spec in Hr1.
    destruct (e_typing_sound Hr1 Hu Hcov1) as [Ha1 [Hu1 [Hcv1 Hq1]]].
    pose proof (e_typing_defs_mono Hr1 HD) as HD1.
    destruct (e_typing_lc_env Hr1 lc_pskl_ghost He1 HΘ HD) as [Hlc1 HΘ1].
    pose proof (e_typing_supply_grows Hr1) as Hgr1.
    bool_true_ty.
    destruct Dc as [Qc Dc].
    destruct (e_consis_swaps ps1 Dc (Δ1' := empty) (Δ2' := empty)
                (S0' := ty_supply r1)) as [Sc1 [HSc1 Dc1]];
      [ symmetry; apply swaps_atoms_empty
      | symmetry; apply swaps_atoms_empty
      | symmetry; exact HS1 | ].
    rewrite HT1, ! swaps_pskl_ptyp_to_pskl, HQ1 in Dc1.
    assert (HfixBd : swaps_ptyp ps1 Bd = Bd)
      by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Hka Hkb];
          split; clear - Hka Hkb Hcov HBe; simpl in *; fsetdec).
    rewrite HfixBd in Dc1.
    assert (Hcovc : ftvar_in_aenv (ty_ctx r1)
                    ∪ ftvar_in_pskl (ptyp_to_pskl Bd)
                    ∪ ftvar_in_pskl (ptyp_to_pskl (ty_out r1))
                    ∪ empty ∪ empty [<=] ty_supply r1).
    { pose proof (ftvar_ptyp_to_pskl (ty_out r1)) as Ho1.
      clear - Hcov Hcv1 Hq1 HBe Ho1 Hgr1; simpl in *; fsetdec. }
    match goal with
    | |- context [ e_consis_impl ?d1 ?d2 ?S ?T ?p0 ?p ?h0 ?h1 ?hd ?h ] =>
        let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
        let rc0 := fresh "rc0" in let Heqr := fresh "Heqr" in
        destruct (e_consis_impl_complete h0 h1 hd h Dc1 Hu1 Hcovc)
          as [rc0 [ps2 [Hx [Hav2 [HS2 [HT2 HQ2]]]]]];
        destruct (e_consis_impl d1 d2 S T p0 p h0 h1 hd h)
          as [ [rc Hrc] | ] eqn:Hcl;
        try rewrite Hcl in Hx;
        [ assert (Heqr : rc0 = exist (consis_spec d1 d2 S T p0 p) rc Hrc)
            by congruence;
          subst rc0; cbn [proj1_sig] in HS2, HT2, HQ2;
          clear Hx Hcl; cbv beta iota
        | discriminate ]
    end.
    eexists; exists (ps1 ++ ps2).
    split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
    split4.
    + intros a0 b0 Hin. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin]; [ exact (Hav1 _ _ Hin) | ].
      destruct (Hav2 _ _ Hin) as [Hka Hkb]. split;
        clear - Hka Hkb Hgr1; fsetdec.
    + cbn [ty_supply]. rewrite swaps_atoms_app. rewrite <- HS2.
      apply swaps_atoms_cong. symmetry. exact HSc1.
    + cbn [ty_ctx]. rewrite swaps_aenv_app. exact HT2.
    + cbn [ty_out]. rewrite swaps_ptyp_app, HfixBd.
      apply swaps_ptyp_fresh_id. intros a0 b0 Hin.
      destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
      split; clear - Hka Hkb Hcov HBe Hgr1; simpl in *; fsetdec.
Qed.

(* ===================================================================== *)
(*  §5  THE HEADLINES                                                     *)
(*                                                                        *)
(*  prop_pat_complete.v §7's shape, for the LAST judgement of the          *)
(*  extractable encoding — the twins of [e_typing_run_sound], and the      *)
(*  top of the completeness ladder.                                       *)
(* ===================================================================== *)

Corollary e_typing_impl_complete : forall S0 m Θ0 P0 e
    (H : e_typing_order S0 m Θ0 P0 e) Sd Θd Bd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e ->
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
    [<=] S0 ->
  exists r ps,
    e_typing_impl S0 m Θ0 P0 e H = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] ty_supply (proj1_sig r)
    /\ swaps_aenv ps Θd = ty_ctx (proj1_sig r)
    /\ swaps_ptyp ps Bd = ty_out (proj1_sig r).
Proof.
  intros * Hd HP0 He HΘ HD Hu Hcov.
  pose proof (e_typing_impl_complete_ind
                (e_typing_order_total S0 m Θ0 P0 e)) as Hmot.
  destruct (Hmot H HP0 He HΘ HD Hu Hcov Sd Θd Bd Hd)
    as [r0 [ps [Hx [Hav [HS [HT HQ]]]]]].
  destruct (e_typing_impl S0 m Θ0 P0 e H) as [ [rr Hrr] | ] eqn:Hcl;
    try rewrite Hcl in Hx; cbn [typing_answer proj1_sig] in Hx;
    [ | discriminate ].
  assert (Heqr : r0 = rr) by congruence. subst r0.
  eexists; exists ps.
  split; [ reflexivity | ].
  split; [ exact Hav | ]. split; [ exact HS | ].
  split; [ exact HT | exact HQ ].
Qed.

(** ⭐⭐ The type-inference headline, over the argument-free runner of
    def_typing_impl.v §5 — the ENTRY POINT of the extracted algorithm, and
    the twin of [e_typing_run_sound]. *)
Theorem e_typing_run_complete : forall S0 m Θ0 P0 e Sd Θd Bd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e ->
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
    [<=] S0 ->
  exists r ps,
    e_typing_run S0 m Θ0 P0 e = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] ty_supply r
    /\ swaps_aenv ps Θd = ty_ctx r
    /\ swaps_ptyp ps Bd = ty_out r.
Proof.
  intros * Hd HP0 He HΘ HD Hu Hcov. unfold e_typing_run.
  destruct (e_typing_impl_complete (e_typing_order_total S0 m Θ0 P0 e)
              Hd HP0 He HΘ HD Hu Hcov)
    as [r [ps [Heq [Hav [HS [HT HQ]]]]]].
  rewrite Heq.
  exists (proj1_sig r), ps.
  split; [ reflexivity | ].
  split; [ exact Hav | ]. split; [ exact HS | ].
  split; [ exact HT | exact HQ ].
Qed.
