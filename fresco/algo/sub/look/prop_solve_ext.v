(** P6 — THE SOLVE-EXTENSION PACKAGES.

    Second of the three shared-substrate files under [algo/sub/look/]
    ([prop_rsubst.v] is first, [prop_flex_apart.v] third).

    What the SolE-FlexR repair costs the completeness proofs.  The repaired
    row returns [guess^TY(P_i)] rather than the target flexible, and
    [guess^TY] INVENTS a fresh flexible per ghost of [P_i] — so every P6
    statement has to carry, and every caller has to rebuild, the block those
    inventions live in.  This file is the algebra of that block:

    - the FLEX-BLOCK EXTENSION KIT — prepending an aligned, wf-mono flexible
      block to a metasubstitution and to its source context;
    - [guess^TY] reads its context only as an AVOID-SET, and a solve survives
      a fresh flexible block inserted in the middle;
    - the three packages the five P6 lemmas are actually stated over:
      [solve_ext], its subtyping twin [solve_sub_ext], and [solve_eq_mono_concl];
    - the per-case kits (GhostG, Flex, Topholeg) built directly on them.

    ⚙ SPLIT 2026-08-09 out of prop_kit.v.  "kit" named nothing: the file was
    6952 lines and three separable concerns, and the audit had already found
    it to be the source of most duplicate names in the tree. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_normal.
Require Import src.fresco.algo.prop_stability.
Require Import src.fresco.algo.prop_refine.
Require Import src.fresco.algo.consis.prop_soundness_consis.
Require Import src.fresco.algo.consis.prop_completeness_consis.
Require Import src.fresco.algo.prop_mono_bridge.
Require Import src.fresco.algo.prop_precise.
Require Import src.fresco.algo.prop_pat_sub.
Require Import src.fresco.algo.consis.prop_consis_precise.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.sub.prop_looksub.
Require Import src.fresco.algo.sub.prop_solve_sub.
Require Import src.fresco.algo.sub.prop_completeness_sub_precise.
Require Import src.fresco.algo.prop_metasubst.
Require Import src.fresco.algo.prop_compose.   (* a_inc_dom_flex, a_inc_lookup_mono *)
Require Import src.fresco.algo.sub.look.prop_rsubst.

(* ⚠️ Per-FILE flag — see prop_flex_apart.v's note.  It was line 84 of the old
   prop_kit.v, so each half of the split needs its own copy. *)
Set Implicit Arguments.

(* ===================================================================== *)
(*  THE FLEX-BLOCK EXTENSION KIT — moved up from                          *)
(*  sub/look/prop_eq_cstr.v (2026-08-04).                               *)
(*                                                                        *)
(*  Nothing in it is specific to the collection layer: it is the algebra   *)
(*  of prepending an ALIGNED, wf-mono flexible block to a metasubstitution *)
(*  and to its source context.  Before the repair the only blocks around   *)
(*  were the collection's and the final guess's, both below this file;     *)
(*  the repaired [SolE-FlexR] makes the SOLVE emit one, and [SE-Arrow]     *)
(*  THREADS — its second premise runs at [Ξ1 ++ Θ] — so the arrow case of  *)
(*  [a_solve_eq_mono] right below is now the FIRST consumer.           *)
(* ===================================================================== *)

(** Split off an all-flex_mono prefix from an [a_inc]: the aligned images are
    wf monotypes in the target, and the remaining substitution increments Θ0. *)
Lemma a_inc_flex_prefix_split : forall Ξ κa Θ0 κb Θ,
  all_flex_mono Ξ ->
  keys κa = keys Ξ ->
  (κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ ->
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa /\ κb ∷ Θ0 ⊑ Θ.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros κa Θ0 κb Θ Hfm Hmap Hinc.
  - destruct κa as [ | ? ? ]; simpl in Hmap; [ | discriminate ].
    simpl in Hinc. split; [ constructor | exact Hinc ].
  - inversion Hfm as [ | ph pt Hb Hfm' ]; subst; simpl in Hb; subst b.
    destruct κa as [ | [y τ] κa' ]; simpl in Hmap; [ discriminate | ].
    injection Hmap as Hxy Hmap'; subst y.
    simpl in Hinc.
    inversion Hinc as [ | Θ2 κ2 Θ3 x2 τ2 Hinc2 Hwf2 Hmono2 | | | | ]; subst.
    destruct (IH κa' Θ0 κb Θ Hfm' Hmap' Hinc2) as [Hfa Hrest].
    split; [ constructor; [ split; assumption | exact Hfa ] | exact Hrest ].
Qed.

(** Prepend an aligned, wf-mono flex_mono prefix onto an [a_inc]. *)
Lemma a_inc_flex_prefix_build : forall Ξ κa Θ0 κb Θ,
  all_flex_mono Ξ ->
  keys κa = keys Ξ ->
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa ->
  κb ∷ Θ0 ⊑ Θ ->
  (κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros κa Θ0 κb Θ Hfm Hmap Hwm Hinc.
  - destruct κa as [ | ? ? ]; simpl in Hmap; [ | discriminate ].
    simpl. exact Hinc.
  - inversion Hfm as [ | ph pt Hb Hfm' ]; subst; simpl in Hb; subst b.
    destruct κa as [ | [y τ] κa' ]; simpl in Hmap; [ discriminate | ].
    injection Hmap as Hxy Hmap'; subst y.
    inversion Hwm as [ | ph2 pt2 Hwmh Hwm' ]; subst; destruct Hwmh as [Hwfτ Hmτ].
    simpl. apply a_inc__flex; [ apply IH; assumption | exact Hwfτ | exact Hmτ ].
Qed.

Lemma all_flex_mono_decls : forall Ξ, all_flex_mono Ξ -> a_decls Ξ.
Proof.
  intros Ξ H; induction H as [ | [α b] Ξ' Hb Hall IH ]; [ constructor | ].
  simpl in Hb; subst b. apply (a_decls__cons α). exact IH.
Qed.

Lemma all_flex_mono_ftvar_in_aenv : forall Ξ,
  all_flex_mono Ξ -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros Ξ H; induction H as [ | [α b] Ξ' Hb Hall IH ]; simpl in *.
  - fsetdec.
  - subst b. simpl. clear - IH; fsetdec.
Qed.

(** The extended context is well-formed as soon as the block is uniq and
    apart from the old domain.  (A local copy of [a_wf_aenv_prepend_decls],
    which lives in prop_soundness_subtag.v — a file this one does not import.) *)
Lemma a_wf_aenv_prepend_flex_block : forall Ξ Θ,
  all_flex_mono Ξ ->
  uniq Ξ ->
  (forall α, α `in` dom Ξ -> α `notin` dom Θ) ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ (Ξ ++ Θ) }}a.
Proof.
  intros Ξ; induction Ξ as [ | [α b] Ξ' IH ]; intros Θ Hfm Hu Hfr Hwf;
    [ exact Hwf | ].
  pose proof (Forall_inv Hfm) as Hb; simpl in Hb; subst b.
  pose proof (Forall_inv_tail Hfm) as Hfm'.
  assert (HαΘ : α `notin` dom Θ) by (apply Hfr; simpl; fsetdec).
  assert (HαΞ : α `notin` dom Ξ') by (clear - Hu; solve_uniq).
  simpl_env. apply a_wf_aenv__flex.
  - rewrite dom_app. clear - HαΘ HαΞ; fsetdec.
  - apply IH; [ exact Hfm' | clear - Hu; solve_uniq | | exact Hwf ].
    intros α0 Hα0. apply Hfr. simpl. clear - Hα0; fsetdec.
Qed.

(* ===================================================================== *)
(*  ⭐ [guess^TY] READS ITS CONTEXT ONLY AS AN AVOID-SET.                  *)
(*                                                                        *)
(*  [a_guess_mono_ctx_shrink] (prop_solve_sub.v) already says the guess    *)
(*  transports to a context that MENTIONS LESS.  What the SolE-FlexR       *)
(*  repair needs is the GROWING direction: SE-FlexR now calls the guess,   *)
(*  and the solve's flex-block weakening — a threading row's second        *)
(*  premise runs at [Ξ1 ++ Θ] — enlarges the avoid-set.  The only thing    *)
(*  that can go wrong is a name COLLISION, so that is exactly the premise: *)
(*  the block already generated must dodge whatever the new context        *)
(*  mentions.  (Not an artefact — it says you may not retroactively add a  *)
(*  context entry colliding with a name the algorithm invented, which the  *)
(*  implementation's global counter enforces.)                             *)
(* ===================================================================== *)

(** The [pskl] twin of [close_ptyp_subst_var] (algo/prop_basic.v).  The
    CLOSE-after-rename step is what keeps a ∀ row's output untouched when its
    recorded binder has to be re-picked. *)
Lemma close_pskl_subst_var : forall P α β,
  β `notin` ftvar_in_pskl P ->
  close_pskl_wrt_pskl β (subst_pskl_in_pskl (pskl_var_f β) α P)
  = close_pskl_wrt_pskl α P.
Proof.
  intros P α β Hβ.
  rewrite subst_pskl_in_pskl_spec.
  apply close_pskl_wrt_pskl_open_pskl_wrt_pskl.
  assert (Hcl : ftvar_in_pskl (close_pskl_wrt_pskl α P)
                  [=] AtomSetImpl.remove α (ftvar_in_pskl P))
    by (apply ftvar_in_pskl_close_pskl_wrt_pskl).
  clear - Hβ Hcl. fsetdec.
Qed.

Lemma a_guess_mono_ctx_change_size : forall n Θ Θ' P Ξ A,
  size_pskl P <= n ->
  a_guess_mono Θ P Ξ A ->
  (forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ') ->
  a_guess_mono Θ' P Ξ A.
Proof.
  induction n as [ | n IH ]; intros Θ Θ' P Ξ A Hsz H Hfr;
    [ exfalso; pose proof (size_pskl_min P); lia | ].
  destruct H as [ Θ0 α Hα | Θ0 Pb Ξb Ab Hg | Θ0 α | Θ0
                | Θ0 Pa Pb Ξa Ξb Aa Ab Hga Hgb
                | Θ0 Pb Ξb Ab b0 Hfrb Hg ]; cbn in Hsz.
  - (* ◇: the invented name IS the block, so the premise is the rule's own *)
    apply a_guess_mono__hole. apply Hfr. simpl; clear; fsetdec.
  - (* ∀◇ *) apply a_guess_mono__tophole.
    eapply IH; [ lia | exact Hg | exact Hfr ].
  - (* var *) apply a_guess_mono__var.
  - (* unit *) apply a_guess_mono__unit.
  - (* arrow: both halves run at the SAME context, so both inherit [Hfr] *)
    apply a_guess_mono__arrow.
    + eapply IH; [ lia | exact Hga | ].
      intros α Hα; apply Hfr; rewrite dom_app; clear - Hα; fsetdec.
    + eapply IH; [ lia | exact Hgb | ].
      intros α Hα; apply Hfr; rewrite dom_app; clear - Hα; fsetdec.
  - (* ∀: the recorded witness may collide with the NEW context, so RE-PICK
       it.  The move is a SWAP, not a rename — [b0] sits IN the premise's
       own context, so "the source dodges the context" cannot hold (§4a of
       the hand-off).  It is harmless because the IH's target context is
       arbitrary: [swap_aenv b0 δ Θ0] never has to collapse to anything. *)
    destruct (atom_fresh (ftvar_in_aenv Θ' `union` ftvar_in_pskl Pb
                `union` dom Ξb `union` ftvar_in_ptyp Ab
                `union` singleton b0)) as [δ Hδ].
    assert (Hb0Ξ : b0 `notin` dom Ξb)
      by (eapply a_guess_mono_generated_fresh_binder; exact Hg).
    assert (HΞftv : ftvar_in_aenv Ξb [<=] dom Ξb)
      by (eapply a_guess_mono_generated_ftvar; exact Hg).
    pose proof (@a_guess_mono_swap b0 δ _ _ _ _ Hg) as Hsw.
    rewrite swap_aenv_app, swap_aenv_one_tvar in Hsw.
    rewrite swap_pskl_open_var, swap_atom_l in Hsw.
    rewrite (swap_pskl_fresh_id b0 δ Pb) in Hsw
      by (clear - Hfrb Hδ; fsetdec).
    rewrite (swap_aenv_fresh_id b0 δ Ξb) in Hsw
      by (clear - Hb0Ξ Hδ HΞftv; fsetdec).
    rewrite (@swap_ptyp_as_subst b0 δ Ab) in Hsw
      by (clear - Hδ; fsetdec).
    assert (Hgδ : a_guess_mono ((δ ~ abind_tvar) ++ Θ')
                    (open_pskl_wrt_pskl Pb (pskl_var_f δ)) Ξb
                    (subst_ptyp_in_ptyp (ptyp_var_f δ) b0 Ab)).
    { eapply IH;
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
        | exact Hsw
        | intros α Hα; specialize (Hfr α Hα); simpl;
          assert (Hne : α `notin` singleton δ) by (clear - Hα Hδ; fsetdec);
          clear - Hfr Hne; fsetdec ]. }
    rewrite <- (@close_ptyp_subst_var Ab b0 δ ltac:(clear - Hδ; solve_notin_auto)).
    apply a_guess_mono__forall with (β := δ);
      [ clear - Hδ; fsetdec | exact Hgδ ].
Qed.

Lemma a_guess_mono_ctx_change : forall Θ Θ' P Ξ A,
  a_guess_mono Θ P Ξ A ->
  (forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ') ->
  a_guess_mono Θ' P Ξ A.
Proof.
  intros Θ Θ' P Ξ A H Hfr.
  eapply a_guess_mono_ctx_change_size; [ reflexivity | exact H | exact Hfr ].
Qed.

(* ===================================================================== *)
(*  ⭐ WEAKENING A SOLVE BY A FRESH FLEXIBLE BLOCK IN THE MIDDLE.          *)
(*                                                                        *)
(*  MOVED UP from sub/look/prop_eq_cstr.v (P6-Cs) and REPAIRED for the   *)
(*  SolE-FlexR threading, 2026-08-04.  Why it moved: every completeness    *)
(*  file's ARROW case now has to put its two branches at DIFFERENT         *)
(*  contexts, because [SS-Arrow] / [SE-Arrow] / [a_solve_cstr__eq] thread  *)
(*  — the second premise runs at [Ξ1 ++ Θ].  The branches themselves are   *)
(*  produced by induction hypotheses stated at [Θ0], so each file needs    *)
(*  exactly this: push the first branch's block underneath the second      *)
(*  branch's derivation.                                                   *)
(*                                                                        *)
(*  THREE THINGS THE REPAIR CHANGED.                                       *)
(*  · The generated block [Ξ] threads through untouched — a solve does not *)
(*    read the context to decide WHAT to invent, only to decide what NOT   *)
(*    to invent.                                                           *)
(*  · ⭐ A NEW PREMISE [dom Ξm ∩ dom Ξ = ∅].  SE-FlexR calls [guess^TY],   *)
(*    whose invented names avoid [ftvar_in_aenv Θ]; inserting [Ξm]         *)
(*    ENLARGES that set, so a run that happened to generate an atom of     *)
(*    [Ξm] cannot be replayed.  Discharged at every call site out of the   *)
(*    package's own freshness component.  ([a_guess_mono_ctx_change]       *)
(*    above is what makes it sufficient.)                                  *)
(*  · ⚠️ The ∀ rows re-freshen by SWAP, not by the double RENAME the        *)
(*    pre-repair proof used: the witness now sits IN the premise's own     *)
(*    context, so [a_solve_*_rename_var]'s "the source dodges the context" *)
(*    can never hold.  [a_solve_*_move_binder*] (prop_solve_sub.v §4a) is  *)
(*    the replacement, and the two [swap_aenv … = …] collapses it leaves   *)
(*    are exactly [swap_aenv_fresh_id] at the rule's own freshness.        *)
(* ===================================================================== *)

Lemma binds_strengthen_mid : forall (x : atom) (b : abind) Ξl Ξm Θ0,
  binds x b (Ξl ++ Ξm ++ Θ0) -> x `notin` dom Ξm -> binds x b (Ξl ++ Θ0).
Proof.
  intros x b Ξl Ξm Θ0 H Hx. apply binds_app_1 in H as [H | H].
  - apply binds_app_2; exact H.
  - apply binds_app_1 in H as [H | H].
    + exfalso. apply Hx. eapply binds_In; exact H.
    + apply binds_app_3; exact H.
Qed.

Lemma a_non_flex_weaken_mid : forall Ξl Ξm Θ0 P,
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  a_non_flex (Ξl ++ Θ0) P -> a_non_flex (Ξl ++ Ξm ++ Θ0) P.
Proof.
  intros Ξl Ξm Θ0 P Hftv [Hlc Hnf]. split; [ exact Hlc | ].
  intro Hf. apply Hnf. inversion Hf as [ Θx αx Hb | Θx αx τ Hb ]; subst.
  - assert (Hin : αx `notin` dom Ξm)
      by (intro Hc; apply (Hftv _ Hc); simpl; fsetdec).
    apply a_flex__var with (α := αx).
    eapply binds_strengthen_mid; [ exact Hb | exact Hin ].
  - assert (Hin : αx `notin` dom Ξm)
      by (intro Hc; apply (Hftv _ Hc); simpl; fsetdec).
    apply a_flex__var_def with (α := αx) (τ := τ).
    eapply binds_strengthen_mid; [ exact Hb | exact Hin ].
Qed.

(** The mid-insertion enlarges [ftvar_in_aenv] by exactly [dom Ξm] — which
    is what the guess and the ∀ rows' freshness conditions read. *)
Lemma ftvar_in_aenv_weaken_mid : forall Ξl Ξm Θ0,
  all_flex_mono Ξm ->
  ftvar_in_aenv (Ξl ++ Ξm ++ Θ0)
    [<=] ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm.
Proof.
  intros Ξl Ξm Θ0 Hfm.
  rewrite ! ftvar_in_aenv_app.
  pose proof (all_flex_mono_ftvar_in_aenv Hfm) as Hm.
  clear - Hm; fsetdec.
Qed.

(* The mutual subject-solve weakening, by SIZE INDUCTION (freshness
   campaign, DESIGN.md §4.3).  The binder rules are exists-fresh: each PINS
   one witness, and an inserted block can CAPTURE it, so every ∀ case first
   re-freshens the recorded binder away from [Ξm] — and a re-freshened
   premise is no sub-derivation, which is what forces the size measure (the
   sub half's [+1] tag absorbs SS-Check's sub ⤳ eq move at unchanged sizes).

   The OUTPUT-freshness premise is load-bearing: [SS-ForallR] LEAKS its
   binder, so THAT binder cannot be moved without changing the output, and
   the only way to keep it out of [Ξm] is to say so.  This is the paper's
   Barendregt convention made explicit, not a weakening of the statement. *)
Lemma a_solve_sub_eq_weaken_mid_flex_size : forall n,
  (forall Θ m P P0 Ξ P',
     2 * (size_pskl P + size_pskl P0) + 1 <= n ->
     {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     forall Ξl Ξm Θ0, Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
     (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
     (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
     {{ (Ξl ++ Ξm ++ Θ0) ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a) /\
  (forall Θ P P0 Ξ P',
     2 * (size_pskl P + size_pskl P0) <= n ->
     {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     forall Ξl Ξm Θ0, Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
     (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
     (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
     {{ (Ξl ++ Ξm ++ Θ0) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a).
Proof.
  induction n as [| n IHall];
    [ split; intros * Hsz Hd; inversion Hd; subst; cbn in Hsz; lia | ].
  destruct IHall as [IHs IHe].
  split.
  (* ================= the [a_solve_sub] half ================= *)
  { intros Θ m P P0 Ξ P' Hsz Hd.
    destruct Hd as
      [ Θ m α Q                                     (* SS-Var *)
      | Θ m P Q Ξ P' b Hfr Hp                       (* SS-ForallL *)
      | Θ m P Q Ξ P' Hp                             (* SS-UnivGhostL *)
      | Θ m P Hoff                                  (* SS-Vacuous *)
      | Θ P Q Ξ P' Hgf0 Hg1 Hg2 Hp                  (* SS-Check *)
      | Θ A B Ξ P' b Hgf0 Hoff Hfr Hp               (* SS-ForallR *)
      | Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2       (* SS-Arrow *)
      | Θ m Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2             (* SS-GhostLF *)
      | Θ B Hgf0 Hg ];                              (* SS-GhostL *)
      intros Ξl Ξm Θ0 Heq Hfm Hdisj Hftv Hout Hblk; subst; cbn in Hsz.
    - (* SS-Var *) apply a_solve_sub__var.
    - (* SS-ForallL — CLOSE: move the witness to a δ outside Ξm, which
         leaves the closed output untouched ([close_pskl_subst_var]) *)
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_sub_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj1 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_sub_move_binder_l _ _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; solve_notin_auto)
                    ltac:(clear - Fr; solve_notin_auto)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; solve_notin_auto)).
      apply a_solve_sub__forall_l with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHs with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ)
            by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx);
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f δ))
            as Hup2;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hftv, Hup2; clear - Hftv Hup2 Hxδ; fsetdec
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    - (* SS-UnivGhostL *)
      apply a_solve_sub__univ_ghost_l.
      eapply IHs with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
        | intros x Hx; specialize (Hout x Hx); cbn in Hout; exact Hout
        | exact Hblk ].
    - (* SS-Vacuous *) apply a_solve_sub__vacuous; exact Hoff.
    - (* SS-Check *)
      apply a_solve_sub__check; [ exact Hgf0 | exact Hg1 | exact Hg2 | ].
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | exact Hftv | exact Hout | exact Hblk ].
    - (* SS-ForallR — the LEAK.  If the witness sits inside Ξm it did NOT
         leak (the output premise), so it can be moved; otherwise it stays. *)
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_sub_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj1 a_solve_sub_eq_generated_ftvar); exact Hp).
      destruct (AtomSetProperties.In_dec b (dom Ξm)) as [Hin | Hnin].
      + pose proof (Hout b Hin) as HbP'.
        pick fresh δ for
          (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
             `union` ftvar_in_pskl A `union` ftvar_in_pskl B
             `union` ftvar_in_pskl P' `union` singleton b).
        pose proof (@a_solve_sub_move_binder_r _ _ _ _ _ _ δ Hp
                      ltac:(clear - Hfr; solve_notin_auto)
                      ltac:(clear - Fr; solve_notin_auto)) as Hr.
        rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
          by (clear - Hfr Fr; fsetdec).
        rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
          by (clear - HbΞ Fr HΞf; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq P') in Hr
          by (clear - HbP'; fsetdec).
        apply a_solve_sub__forall_r with (β := δ);
          [ exact Hgf0 | exact Hoff
          | rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
            clear - Fr; fsetdec | ].
        eapply IHs with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hr | reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx);
            assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
            simpl_env in Hdisj; simpl_env;
            clear - Hdisj Hxδ; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
          | exact Hout | exact Hblk ].
      + apply a_solve_sub__forall_r with (β := b);
          [ exact Hgf0 | exact Hoff
          | rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
            clear - Hfr Hnin; fsetdec | ].
        eapply IHs with (Ξl := ((b ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hp | reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx);
            assert (Hxb : x `notin` singleton b)
              by (clear - Hnin Hx; fsetdec);
            simpl_env in Hdisj; simpl_env;
            clear - Hdisj Hxb; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
          | exact Hout | exact Hblk ].
    - (* SS-Arrow — THREADS: the tail runs at [Ξ1 ++ Θ], so the insertion
         goes UNDER [Ξ1] for the second premise *)
      apply a_solve_sub__arrow with (Ξ1 := Ξ1).
      + eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp1 | reflexivity | exact Hfm | exact Hdisj
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
      + rewrite <- (list_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
        eapply IHs with (Ξl := (Ξ1 ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp2 | rewrite list_app_assoc; reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx); specialize (Hblk x Hx);
            rewrite dom_app in Hblk; rewrite ! dom_app;
            clear - Hdisj Hblk; rewrite dom_app in Hdisj; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
    - (* SS-GhostLF — same threading *)
      apply a_solve_sub__ghost_l_fn with (Ξ1 := Ξ1).
      + eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp1 | reflexivity | exact Hfm | exact Hdisj
          | intros x Hx; cbn; clear; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
      + rewrite <- (list_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
        eapply IHs with (Ξl := (Ξ1 ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp2 | rewrite list_app_assoc; reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx); specialize (Hblk x Hx);
            rewrite dom_app in Hblk; rewrite ! dom_app;
            clear - Hdisj Hblk; rewrite dom_app in Hdisj; fsetdec
          | intros x Hx; cbn; clear; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
    - (* SS-GhostL *) apply a_solve_sub__ghost_l; [ exact Hgf0 | exact Hg ]. }
  (* ================= the [a_solve_eq] half ================= *)
  { intros Θ P P0 Ξ P' Hsz Hd.
    destruct Hd as
      [ Θ                                           (* SE-Unit *)
      | Θ α Q                                       (* SE-Var *)
      | Θ α P Ξ A Hflex Hnf Hng Hgu                 (* SE-FlexR *)
      | Θ Q                                         (* SE-GhostL *)
      | Θ P                                         (* SE-VacuousR *)
      | Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2         (* SE-Arrow *)
      | Θ P Q Ξ P' b Hfr Hp                         (* SE-Forall *)
      | Θ P Q Ξ P' Hp                               (* SE-UnivGhost *)
      | Θ P Q Ξ P' b Hfr Hp                         (* SE-GhostForall *)
      | Θ P Q Ξ P' Hg Hp                            (* SE-GhostGuarded *)
      | Θ P Q Ξ P' b Hfr Hp                         (* SE-ForallGhost *)
      | Θ P Q Ξ P' Hg Hp ];                         (* SE-GuardedGhost *)
      intros Ξl Ξm Θ0 Heq Hfm Hdisj Hftv Hout Hblk; subst; cbn in Hsz.
    - (* SE-Unit *) apply a_solve_eq__unit.
    - (* SE-Var *) apply a_solve_eq__var.
    - (* ⭐ SE-FlexR: [guess^TY] reads the context as an AVOID-SET, so the
         insertion is legal exactly when the block it generated dodges the
         inserted names — which is [Hblk]. *)
      apply a_solve_eq__flex_r;
        [ apply a_flex_tvar_weaken_mid; exact Hflex
        | apply a_non_flex_weaken_mid; [ exact Hftv | exact Hnf ]
        | exact Hng
        | eapply a_guess_mono_ctx_change; [ exact Hgu | ] ].
      intros α0 Hα0.
      pose proof (a_guess_mono_generated_fresh Hgu Hα0) as Hf0.
      rewrite ftvar_in_aenv_weaken_mid by exact Hfm.
      assert (Hne : α0 `notin` dom Ξm)
        by (intro Hc; exact (Hblk α0 Hc Hα0)).
      clear - Hf0 Hne; fsetdec.
    - (* SE-GhostL *) apply a_solve_eq__hole_l.
    - (* SE-VacuousR *) apply a_solve_eq__hole_r.
    - (* SE-Arrow — THREADS *)
      apply a_solve_eq__arrow with (Ξ1 := Ξ1).
      + eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp1 | reflexivity | exact Hfm | exact Hdisj
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
      + rewrite <- (list_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
        eapply IHe with (Ξl := (Ξ1 ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp2 | rewrite list_app_assoc; reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx); specialize (Hblk x Hx);
            rewrite dom_app in Hblk; rewrite ! dom_app;
            clear - Hdisj Hblk; rewrite dom_app in Hdisj; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
    - (* SE-Forall — CLOSE; re-freshen by SWAP *)
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_eq_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj2 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_eq_move_binder _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; solve_notin_auto)
                    ltac:(clear - Fr; solve_notin_auto)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; solve_notin_auto)).
      apply a_solve_eq__forall with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHe with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx);
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f δ))
            as Hup2;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hftv, Hup2; clear - Hftv Hup2 Hxδ; fsetdec
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    - (* SE-UnivGhost *)
      apply a_solve_eq__tophole_both.
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
        | intros x Hx; specialize (Hout x Hx); cbn in Hout; exact Hout
        | exact Hblk ].
    - (* SE-GhostForall — CLOSE; the ∀◇ subject rides along unopened *)
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_eq_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj2 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_eq_move_binder_tophole_l _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; cbn in Hfr; solve_notin_auto)
                    ltac:(clear - Fr; solve_notin_auto)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; solve_notin_auto)).
      apply a_solve_eq__tophole_l_all with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHe with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv |- *; exact Hftv
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    - (* SE-GhostGuarded *)
      apply a_solve_eq__tophole_l_guarded; [ exact Hg | ].
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
        | exact Hout | exact Hblk ].
    - (* SE-ForallGhost — CLOSE; the ∀◇ target rides along unopened *)
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_eq_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj2 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_eq_move_binder_tophole_r _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; cbn in Hfr; solve_notin_auto)
                    ltac:(clear - Fr; solve_notin_auto)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; solve_notin_auto)).
      apply a_solve_eq__all_l_tophole with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHe with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx);
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f δ))
            as Hup2;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hftv, Hup2; clear - Hftv Hup2 Hxδ; fsetdec
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    - (* SE-GuardedGhost *)
      apply a_solve_eq__tophole_r_guarded; [ exact Hg | ].
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | exact Hftv | exact Hout | exact Hblk ]. }
Qed.

Lemma a_solve_sub_weaken_mid_flex : forall Θ m P P0 Ξ P' Ξl Ξm Θ0,
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
  Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  {{ (Ξl ++ Ξm ++ Θ0) ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a.
Proof.
  intros. eapply (proj1 (a_solve_sub_eq_weaken_mid_flex_size
                           (2 * (size_pskl P + size_pskl P0) + 1)));
    eauto.
Qed.

Lemma a_solve_eq_weaken_mid_flex : forall Θ P P0 Ξ P' Ξl Ξm Θ0,
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  {{ (Ξl ++ Ξm ++ Θ0) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a.
Proof.
  intros. eapply (proj2 (a_solve_sub_eq_weaken_mid_flex_size
                           (2 * (size_pskl P + size_pskl P0))));
    eauto.
Qed.

(** The shape the completeness ARROW cases want: prepend a block, no [Ξl]. *)
Lemma a_solve_eq_weaken_flex_block : forall Θ0 P P0 Ξ P' Ξm,
  {{ Θ0 ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom Θ0) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  {{ (Ξm ++ Θ0) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a.
Proof.
  intros Θ0 P P0 Ξ P' Ξm H Hfm Hd HP HP' Hblk.
  exact (@a_solve_eq_weaken_mid_flex Θ0 P P0 Ξ P' nil Ξm Θ0
           H eq_refl Hfm Hd HP HP' Hblk).
Qed.

(* ⭐ WHERE THE κ-EXTENSION'S wf OBLIGATION COMES FROM (2026-08-04).
   [a_guess_ty_witness_mono] sends the flexible it invents at a ◇ to the
   monotype standing at that position, and [a_inc__flex] admits only a
   monotype WELL-FORMED IN THE TARGET.  So every consumer owes
   [a_wf_ptyp Θ τ] for the counterpart monotype — and every consumer has it,
   because the counterpart is a CONSISTENCY SUBJECT, and consistency's own
   [var] row carries [a_binds_tvar α Θ].  (The [flex_l] row does too, via the
   definition it looks up: a defined flexible is tvar-ish.)  No new external
   side condition — the fact was already in the derivation. *)
Lemma ad_pat_consis_mono_subject_wf : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall τ, R = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  a_wf_ptyp Θ τ.
Proof.
  (* every GHOST-headed and ∀-headed row dies: a ghost is never a paint, and
     a ∀ paint is not a monotype (that is what [Hm] rules out) *)
  intros Ψ Θ R Q H; induction H; intros τ0 Heq Hm;
    try solve [ destruct τ0; simpl in Heq;
                solve [ discriminate Heq | inversion Hm ] ].
  - (* unit *) destruct τ0; simpl in Heq; try discriminate Heq.
    apply a_wf_ptyp__unit.
  - (* var: the rule's OWN premise *)
    destruct τ0; simpl in Heq; try discriminate Heq.
    inversion Heq; subst. apply a_wf_ptyp__var; assumption.
  - (* arrow *)
    destruct τ0; simpl in Heq; try discriminate Heq.
    inversion Heq; subst. inversion Hm; subst.
    apply a_wf_ptyp__arrow;
      [ eapply IHad_pat_consis1 | eapply IHad_pat_consis2 ];
      solve [ reflexivity | assumption ].
  - (* flex_l: the subject IS a variable, and the definition it looks up
       makes that variable tvar-ish *)
    destruct τ0; simpl in Heq; try discriminate Heq.
    inversion Heq; subst. apply a_wf_ptyp__var. right; right; eauto.
  - (* flex_r: the subject passes through *)
    eapply IHad_pat_consis; [ exact Heq | exact Hm ].
Qed.

(* ===================================================================== *)
(*  ⭐ THE κ-EXTENSION PACKAGE, ONCE.                                      *)
(*                                                                        *)
(*  Every P6 conclusion from here down has the SAME first six components   *)
(*  — the solve, its generated block, and the aligned extension of the     *)
(*  metasubstitution over that block — and differs only in the seventh,    *)
(*  its own precision/refinement post-condition.  Naming the shape lets    *)
(*  the four downstream files state their conclusions in one line and,     *)
(*  more importantly, share the two glue lemmas below: [solve_ext_nil]     *)
(*  for a row that generates nothing and [solve_ext_step] for a row that   *)
(*  passes its premise through.  Between them they cover every case that   *)
(*  is not the arrow merge or SE-FlexR itself.                            *)
(*                                                                        *)
(*  [L] is an avoid-set PARAMETER, not an output: at a binder row the      *)
(*  witness must be fixed BEFORE the block is picked (that is what makes   *)
(*  [a_guess_ty_witness_mono]'s ∀ case provable), and at the arrow row the *)
(*  second branch is run at an [L] widened by the first branch's block.   *)
(* ===================================================================== *)
Definition solve_ext (Θ0 Θ : aenv) (Pi P0 : pskl) (L : atoms)
    (Post : metasubst -> pskl -> Prop) : Prop :=
  exists (Ξ : aenv) (Pa : pskl) (κ' : metasubst),
    {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a /\
    all_flex_mono Ξ /\
    uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    Post κ' Pa.

(** The package's wf component transports to any context that has all the
    bindings — the direction a ∀ row needs when it hands its body's package
    back out from [(α ~ tvar) ++ Θ]'s point of view to [Θ]'s. *)
Lemma forall_wf_mono_weaken : forall (Θ Θ' : aenv) (κ' : metasubst),
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' ->
  Forall (fun p => a_wf_ptyp Θ' (snd p) /\ mono_ptyp (snd p)) κ'.
Proof.
  intros Θ Θ' κ' Hmon H; induction H as [ | p l0 Hp Hl IH ]; [ constructor | ].
  constructor; [ | exact IH ].
  destruct Hp as [Hw Hm]; split;
    [ eapply a_wf_ptyp_weaken; [ exact Hmon | exact Hw ] | exact Hm ].
Qed.

(** A row that GENERATES NOTHING needs no extension. *)
Lemma solve_ext_nil : forall Θ0 Θ Pi P0 L Post Pa,
  {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa }}a ->
  Post nil Pa ->
  solve_ext Θ0 Θ Pi P0 L Post.
Proof.
  intros Θ0 Θ Pi P0 L Post Pa Hs Hq.
  exists nil, Pa, nil.
  split; [ exact Hs | ].
  split; [ apply Forall_nil | ].
  split; [ apply uniq_nil | ].
  split; [ reflexivity | ].
  split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
  split; [ apply Forall_nil | ].
  exact Hq.
Qed.

(** A row that PASSES ITS PREMISE THROUGH keeps the whole package: the block,
    the extension and the freshness are the premise's, and only the solve
    step and the post-condition change.  This is the shape of every ∀◇ row
    and of every "peel one constructor" row. *)
Lemma solve_ext_step : forall Θ0 Θ Pi P0 Pi' P0' L Post Post',
  (forall Ξ Pa, {{ Θ0 ⊢ₑ Pi' ∼ P0' ⤳ Ξ ⨾ Pa }}a -> {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a) ->
  (forall κ' Pa, Post' κ' Pa -> Post κ' Pa) ->
  solve_ext Θ0 Θ Pi' P0' L Post' ->
  solve_ext Θ0 Θ Pi P0 L Post.
Proof.
  intros Θ0 Θ Pi P0 Pi' P0' L Post Post' Hstep Hpost
         (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
  exists Ξ, Pa, κ'.
  repeat (split; [ solve [ apply Hstep; exact Hs | exact Hfm | exact Hu
                         | exact Hk | exact Hfr | exact HF ] | ]).
  apply Hpost; exact Hq.
Qed.

(** The same, with the SOLVE DERIVATION still in hand — several rows read a
    structural fact off it (hole-freedom, the ftv bound) while strengthening
    the post-condition. *)
Lemma solve_ext_post_solve : forall Θ0 Θ Pi P0 L Post Post',
  (forall Ξ κ' Pa, {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a -> Post' κ' Pa -> Post κ' Pa) ->
  solve_ext Θ0 Θ Pi P0 L Post' ->
  solve_ext Θ0 Θ Pi P0 L Post.
Proof.
  intros Θ0 Θ Pi P0 L Post Post' Hpost
         (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
  exists Ξ, Pa, κ'.
  repeat (split; [ solve [ exact Hs | exact Hfm | exact Hu
                         | exact Hk | exact Hfr | exact HF ] | ]).
  eapply Hpost; [ exact Hs | exact Hq ].
Qed.

(* ===================================================================== *)
(*  The SUBTYPING twin of [solve_ext] (2026-08-04).  P6-Sv and P6-Ss     *)
(*  state their conclusions with it.  Two differences from the eq one:   *)
(*  the judgment is [≼[m]] and carries a MODE, and the package includes  *)
(*  the output's WELL-FORMEDNESS — which on the sub side is a genuine    *)
(*  conclusion of the completeness lemma rather than a derivable fact    *)
(*  (there is no "solving preserves wf" once SS-ForallR is faithful:     *)
(*  cex/cex_solve_sub_wf_leak.v).  It is stated at [Ξ ++ Θ0], since the  *)
(*  repaired SolE-FlexR lets the output mention the generated block.     *)
(* ===================================================================== *)
Definition solve_sub_ext (Θ0 Θ : aenv) (m : mode) (Pi P0 : pskl) (L : atoms)
    (Post : metasubst -> pskl -> Prop) : Prop :=
  exists (Ξ : aenv) (Pa : pskl) (κ' : metasubst),
    {{ Θ0 ⊢ₛ Pi ≼[ m ] P0 ⤳ Ξ ⨾ Pa }}a /\
    all_flex_mono Ξ /\
    uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    Post κ' Pa.

Lemma solve_sub_ext_nil : forall Θ0 Θ m Pi P0 L Post Pa,
  {{ Θ0 ⊢ₛ Pi ≼[ m ] P0 ⤳ nil ⨾ Pa }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pa }}a ->
  Post nil Pa ->
  solve_sub_ext Θ0 Θ m Pi P0 L Post.
Proof.
  intros Θ0 Θ m Pi P0 L Post Pa Hs Hwf Hq.
  exists nil, Pa, nil.
  split; [ exact Hs | ].
  split; [ apply Forall_nil | ].
  split; [ apply uniq_nil | ].
  split; [ reflexivity | ].
  split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
  split; [ apply Forall_nil | ].
  split; [ cbn [app]; exact Hwf | ].
  exact Hq.
Qed.

(** The conclusion, named — it recurs at every site below. *)
Definition solve_eq_mono_concl (Θ0 Θ Θw : aenv) (κ : metasubst) (Δ Ψi : atoms)
    (τ : ptyp) (Pi P0 : pskl) (L : atoms) : Prop :=
  solve_ext Θ0 Θw Pi P0 L
    (fun κ' Pa =>
       {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad).

Lemma solve_eq_mono_nil : forall Θ0 Θ Θw κ Δ Ψi τ Pi P0 L Pa,
  {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa }}a ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad ->
  solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τ Pi P0 L.
Proof.
  intros Θ0 Θ Θw κ Δ Ψi τ Pi P0 L Pa Hs Hq.
  eapply solve_ext_nil; [ exact Hs | cbn [app]; exact Hq ].
Qed.

(** The ∀◇ rows: the solve peels a constructor and the target hops one
    definition chain. *)
Lemma solve_eq_mono_wrap : forall Θ0 Θ Θw κ Δ Ψi τ τe Pi P0 Pi' P0' L,
  a_def_chain Θ τ τe ->
  (forall Ξ Pa, {{ Θ0 ⊢ₑ Pi' ∼ P0' ⤳ Ξ ⨾ Pa }}a -> {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a) ->
  solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τe Pi' P0' L ->
  solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τ Pi P0 L.
Proof.
  intros Θ0 Θ Θw κ Δ Ψi τ τe Pi P0 Pi' P0' L Hc Hstep H.
  eapply solve_ext_step;
    [ exact Hstep
    | intros κ' Pa Hq; eapply ad_ppre_chain_fold; [ exact Hc | exact Hq ]
    | exact H ].
Qed.

Lemma a_solve_eq_mono : forall n Θ0 Θ Θw κ Δ Ψi τ Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  mono_ptyp τ ->
  (* ⭐ the target is wf in the EXTENSION's context, OR it is a rigid variable
     of [Θ].  The second disjunct is what a P6 ∀ row supplies when the target
     is the BOUND rigid itself, which is not in [Θw] at all — and it costs
     nothing, because every branch that consumes this premise first unfolds a
     definition chain out of [τ], and a rigid variable has none
     ([a_def_chain_rigid_var_inv]). *)
  (a_wf_ptyp Θw τ \/ (exists α0, τ = ptyp_var_f α0 /\ binds α0 abind_tvar Θ)) ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (ptyp_to_bskl_syn τ) }}ad ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τ Pi P0 L.
Proof.
  induction n; intros Θ0 Θ Θw κ Δ Ψi τ Pi P0 Hn
    HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi HwfP0 Hκ Hmτ Hwfτ Hdf Hpre Hrefine L HL.
  { pose proof (size_pskl_min Pi); pose proof (size_pskl_min P0); lia. }
  destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
  - (* Pi = unit: resolve the chain to 1, delegate to the Unit case lemma *)
    simpl in Hpre.
    destruct (ad_ppre_unit_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as [Hc HΨi].
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine) as Href'.
    simpl in Href'.
    assert (Hpre_u : {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ pskl_unit) ⊑ᵖ[ Ψi ] uskl_unit }}ad)
      by (simpl; apply ad_ppre__unit; exact HΨi).
    destruct (a_solve_eq_unit (n := S n) (Θ := Θ) (Δ := Δ)
                Hn HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre_u Href')
      as (Pa & Hsolve & Hprec).
    eapply solve_eq_mono_nil;
      [ exact Hsolve | eapply ad_ppre_chain_fold; [ exact Hc | exact Hprec ] ].
  - (* Pi = var_b: not wf *) inversion HwfPi.
  - (* Pi = var_f α: SE-Var / SE-FlexL *)
    eapply solve_eq_mono_nil; [ apply a_solve_eq__var | exact Hpre ].
  - (* Pi = arrow Pi1 Pi2 *)
    assert (HwfPi1 : {{ Θ0 ⨟ empty ⊢ₚₛ Pi1 }}a) by (inversion HwfPi; assumption).
    assert (HwfPi2 : {{ Θ0 ⨟ empty ⊢ₚₛ Pi2 }}a) by (inversion HwfPi; assumption).
    simpl in Hpre.
    destruct (ad_ppre_arrow_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τ1 & τ2 & Ψ1 & Ψ2 & Hc & Hm1 & Hm2 & Hp1 & Hp2 & HΨ).
    (* the target really is wf at [Θw] here: the chain out of [τ] REACHED an
       arrow, so [τ] is not a rigid variable *)
    assert (Hwfτ' : a_wf_ptyp Θw τ).
    { destruct Hwfτ as [Hw | (α0 & Heqτ & Hrig0)]; [ exact Hw | ].
      exfalso. subst τ.
      pose proof (a_def_chain_rigid_var_inv Hc HwfΘ Hrig0) as Hcc.
      discriminate Hcc. }
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine) as Href'.
    destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
    + (* P0 = unit: refinement absurd *)
      simpl in Href'. inversion Href'.
    + (* P0 = var_b: not wf *) inversion HwfP0.
    + (* P0 = var β: rigid absurd / flexible SE-FlexR + Bridge A *)
      inversion HwfP0; subst;
      match goal with H : _ \/ a_binds_tvar β _ |- _ =>
        destruct H as [Hemp | Habt] end; [ clear - Hemp; fsetdec | ].
      destruct Habt as [Hrig | Hflx].
      * (* rigid: no refinement into an arrow *)
        exfalso.
        assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
          by (eapply msubst_pskl_tvar_id;
                [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
        rewrite Hmid in Href'. simpl in Href'.
        eapply ad_refine_syn_rigid_var_nonvar_absurd;
          [ exact HwfΘ | eapply a_inc_binds_tvar; eauto | exact Href'
          | intros β0 Hcc; discriminate Hcc ].
      * (* flexible: SE-FlexR, precision via Bridge A *)
        assert (HΨi : Ψi [=] empty)
          by (eapply ad_ppre_mono_tags_empty;
                [ exact HwfΘ | exact Hpre | reflexivity | exact Hmτ ]).
        (* ⭐ SE-FlexR, REPAIRED.  The output is [guess^TY(P_i)] — the
           accumulated pattern — not the flexible, so the witness is the
           guess and the extension is the one [a_guess_ty_witness_mono]
           builds alongside it.  The old proof went the other way: its
           witness was [β̂] and the obligation needed the whole
           [ad_refine_mono_paint_lhs_ppre] bridge through the refinement.
           Here the precision obligation IS the witness's own output. *)
        assert (Hszg : size_pskl (pskl_arrow Pi1 Pi2) <= S n)
          by (cbn in Hn |- *; lia).
        destruct (@a_guess_ty_witness_mono (S n) Θ0 Θ Θw κ Δ Ψi τ
                    (pskl_arrow Pi1 Pi2) Hszg HwfΘ HwfΘw Hmon Hdefs
                    HwfPi Hmτ Hwfτ' Hpre L)
          as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
        exists Ξg, (ptyp_to_pskl Ag), κg.
        split; [ apply a_solve_eq__flex_r;
                   [ exact Hflx
                   | split; [ eapply a_wf_pskl_lc; exact HwfPi
                            | intros Hf; inversion Hf ]
                   | apply nonghost_pskl__arrow
                   | apply Hgu; exact HL ] | ].
        split; [ exact Hfmg | ].
        split; [ exact Hug | ].
        split; [ exact Hkg | ].
        split; [ exact Hfrg | ].
        split; [ exact HFg | ].
        exact Hqg.
    + (* ⭐ P0 = arrow P01 P02: SE-Arrow, and THE TWO IHs' EXTENSIONS MERGE.
         This is the one case in the file with real content.

         SE-Arrow THREADS (algo/def_rules.v, §2(2) of the hand-off): its second
         premise runs at [Ξ1 ++ Θ0] and its output block is [Ξ2 ++ Ξ1].  So
         the second IH is invoked AT THAT CONTEXT, under the metasubstitution
         the first branch has ALREADY extended — which is exactly what the
         first branch's package licenses ([a_inc_flex_prefix_build]).  Running
         both at [Θ0] instead is not merely inconvenient, it is unsound
         bookkeeping: the two blocks could pick the same atom and conflate two
         independently-invented flexibles.

         The avoid-sets are the witness lemma's ([a_guess_ty_witness_mono]'s
         arrow case): BOTH IHs avoid BOTH branches' sources, and the second
         additionally avoids [dom Ξ1].  That is what makes each branch's
         extension invisible to the other's result below — [Heq1] here, and
         [Heqi2]/[Heqp2] for the second IH's own premises. *)
      assert (HwfP01 : {{ Θ0 ⨟ empty ⊢ₚₛ P01 }}a) by (inversion HwfP0; assumption).
      assert (HwfP02 : {{ Θ0 ⨟ empty ⊢ₚₛ P02 }}a) by (inversion HwfP0; assumption).
      assert (Hwfar : a_wf_ptyp Θw (ptyp_arrow τ1 τ2))
        by (eapply a_def_chain_wf_at;
              [ exact Hc | exact HwfΘw | exact Hdefs | exact Hwfτ' ]).
      assert (Hwf1 : a_wf_ptyp Θw τ1) by (inversion Hwfar; assumption).
      assert (Hwf2 : a_wf_ptyp Θw τ2) by (inversion Hwfar; assumption).
      simpl in Href'.
      inversion Href'; subst.
      match goal with
      | Hr1 : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P01) ⊳ _ }}ad,
        Hr2 : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P02) ⊳ _ }}ad |- _ =>
        rename Hr1 into Href1; rename Hr2 into Href2
      end.
      (* ---- branch 1, at [Θ0], avoiding both sources ---- *)
      assert (HL1 : ftvar_in_aenv Θ0
                    [<=] L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                           `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02)
        by (clear - HL; fsetdec).
      destruct (IHn Θ0 Θ Θw κ Δ Ψ1 τ1 Pi1 P01
                  ltac:(simpl in Hn; lia)
                  HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi1 HwfP01 Hκ Hm1 (or_introl Hwf1) Hdf Hp1 Href1
                  (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                     `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02)
                  HL1)
        as (Ξ1 & Pa1 & κa & Hs1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hq1).
      assert (Hdκa : dom κa [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
      (* ---- move everything the second IH needs to [Ξ1 ++ Θ0] ---- *)
      assert (HΞ1Θ0 : forall α0, α0 `in` dom Ξ1 -> α0 `notin` dom Θ0).
      { intros α0 Hα0. specialize (Hfr1 α0 Hα0).
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd.
        clear - Hfr1 Hd HL; fsetdec. }
      assert (Hwfblk : {{ ⊢ (Ξ1 ++ Θ0) }}a)
        by (apply a_wf_aenv_prepend_flex_block; assumption).
      assert (Hκ1 : (κa ++ κ) ∷ (Ξ1 ++ Θ0) ⊑ Θ)
        by (apply a_inc_flex_prefix_build;
              [ exact Hfm1 | exact Hk1
              | eapply forall_wf_mono_weaken; [ exact Hmon | exact HF1 ]
              | exact Hκ ]).
      assert (HwfPi2' : {{ (Ξ1 ++ Θ0) ⨟ empty ⊢ₚₛ Pi2 }}a)
        by (apply a_wf_pskl_app_weaken; exact HwfPi2).
      assert (HwfP02' : {{ (Ξ1 ++ Θ0) ⨟ empty ⊢ₚₛ P02 }}a)
        by (apply a_wf_pskl_app_weaken; exact HwfP02).
      assert (Heqi2 : msubst_pskl (nil ++ κa ++ κ) Pi2
                      = msubst_pskl (nil ++ κ) Pi2).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
        specialize (Hfr1 α0 Hin). clear - Hfr1; fsetdec. }
      assert (Heqp2 : msubst_pskl (nil ++ κa ++ κ) P02
                      = msubst_pskl (nil ++ κ) P02).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
        specialize (Hfr1 α0 Hin). clear - Hfr1; fsetdec. }
      cbn [app] in Heqi2, Heqp2.
      assert (Hp2' : {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κa ++ κ) Pi2)
                             ⊑ᵖ[ Ψ2 ] (ptyp_to_uskl_syn τ2) }}ad)
        by (rewrite Heqi2; exact Hp2).
      assert (Href2' : {{ Θ ⨟ empty ⊢ᵣ
                (pskl_to_bskl_inh (msubst_pskl (κa ++ κ) P02))
                ⊳ (ptyp_to_bskl_syn τ2) }}ad)
        by (rewrite Heqp2; exact Href2).
      assert (HL2 : ftvar_in_aenv (Ξ1 ++ Θ0)
                    [<=] L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                           `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02
                           `union` dom Ξ1).
      { rewrite ftvar_in_aenv_app.
        pose proof (all_flex_mono_ftvar_in_aenv Hfm1) as Hf1.
        clear - HL Hf1; fsetdec. }
      (* ---- branch 2, at [Ξ1 ++ Θ0], additionally avoiding [dom Ξ1] ---- *)
      destruct (IHn (Ξ1 ++ Θ0) Θ Θw (κa ++ κ) Δ Ψ2 τ2 Pi2 P02
                  ltac:(simpl in Hn; lia)
                  HwfΘ Hwfblk HwfΘw Hmon Hdefs HwfPi2' HwfP02' Hκ1 Hm2 (or_introl Hwf2) Hdf Hp2' Href2'
                  (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                     `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02
                     `union` dom Ξ1)
                  HL2)
        as (Ξ2 & Pa2 & κb & Hs2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hq2).
      assert (Hdκb : dom κb [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
      assert (Hdisj : disjoint Ξ2 Ξ1).
      { unfold disjoint. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hα0 Hfr2; fsetdec. }
      (* the FIRST branch's result is bounded by its own inputs plus its own
         block, all three of which the second block was told to dodge *)
      assert (HPa1 : ftvar_in_pskl Pa1
                     [<=] ftvar_in_pskl Pi1 `union` ftvar_in_pskl P01
                            `union` dom Ξ1)
        by (eapply a_solve_eq_ftv; exact Hs1).
      assert (Heq1 : msubst_pskl (nil ++ κb ++ (κa ++ κ)) Pa1
                     = msubst_pskl (nil ++ (κa ++ κ)) Pa1).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0 Hdκb; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hfr2 HPa1; fsetdec. }
      cbn [app] in Heq1.
      exists (Ξ2 ++ Ξ1), (pskl_arrow Pa1 Pa2), (κb ++ κa).
      split; [ apply a_solve_eq__arrow; [ exact Hs1 | exact Hs2 ] | ].
      split; [ apply all_flex_mono_app; assumption | ].
      split; [ clear - Hu1 Hu2 Hdisj; solve_uniq | ].
      split; [ rewrite ! keys_app; rewrite Hk1, Hk2; reflexivity | ].
      split; [ intros α0 Hα0; rewrite dom_app in Hα0;
               destruct (union_1 Hα0) as [Hin2 | Hin1];
                 [ specialize (Hfr2 α0 Hin2); clear - Hfr2; fsetdec
                 | specialize (Hfr1 α0 Hin1); clear - Hfr1; fsetdec ] | ].
      split; [ apply Forall_app; split; assumption | ].
      eapply ad_ppre_chain_fold; [ exact Hc | ].
      rewrite list_app_assoc. cbn [msubst_pskl ptyp_to_uskl_syn].
      rewrite Heq1.
      apply ad_ppre__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
        [ exact Hq1 | exact Hq2 | exact HΨ ].
    + (* P0 = all_syn: refinement absurd *)
      simpl in Href'.
      exfalso.
      eapply ad_refine_allinh_lhs_mono_absurd;
        [ exact HwfΘ | exact Href' | reflexivity | reflexivity
        | apply mono_ptyp__arrow; assumption ].
    + (* P0 = hole: SE-VacuousR *)
      eapply solve_eq_mono_nil; [ apply a_solve_eq__hole_r | exact Hpre ].
    + (* P0 = tophole P0': GuardedGhost-right, recurse at the resolved arrow *)
      assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a) by (inversion HwfP0; assumption).
      assert (Hwfar : a_wf_ptyp Θw (ptyp_arrow τ1 τ2))
        by (eapply a_def_chain_wf_at;
              [ exact Hc | exact HwfΘw | exact Hdefs | exact Hwfτ' ]).
      simpl in Href'.
      inversion Href'; subst.
      assert (Hpre' : {{ Θ ⨟ Δ ⊢ˢ msubst_pskl κ (pskl_arrow Pi1 Pi2) ⊑ᵖ[ Ψi ]
                        (ptyp_to_uskl_syn (ptyp_arrow τ1 τ2)) }}ad)
        by (simpl; eapply ad_ppre__arrow;
              [ exact Hp1 | exact Hp2 | exact HΨ ]).
      assert (Hcv : solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi (ptyp_arrow τ1 τ2)
                      (pskl_arrow Pi1 Pi2) P0' L).
      { match goal with
        | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _ }}ad |- _ =>
          apply (IHn Θ0 Θ Θw κ Δ Ψi (ptyp_arrow τ1 τ2) (pskl_arrow Pi1 Pi2) P0'
                   ltac:(simpl in Hn; simpl; lia)
                   HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi HwfP0' Hκ
                   ltac:(apply mono_ptyp__arrow; assumption)
                   (or_introl Hwfar) Hdf Hpre' Hin L HL)
        end. }
      eapply solve_eq_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__tophole_r_guarded;
        [ apply guarded_pskl__arrow;
            [ eapply a_wf_pskl_lc; exact HwfPi1
            | eapply a_wf_pskl_lc; exact HwfPi2 ]
        | exact Hs ].
  - (* Pi = all_syn: precision absurd *)
    simpl in Hpre.
    exfalso.
    eapply ad_ppre_allsyn_subject_mono_absurd;
      [ exact HwfΘ | exact Hpre | reflexivity | reflexivity | exact Hmτ ].
  - (* Pi = □: SE-GhostL, precision via Bridge B *)
    simpl in Hpre.
    eapply solve_eq_mono_nil; [ apply a_solve_eq__hole_l | ].
    eapply ad_refine_inh_hole_ppre with (Δr := empty);
      [ exact HwfΘ | clear; fsetdec | exact Hrefine | reflexivity | reflexivity
      | exact Hmτ | exact Hdf | exact Hpre ].
  - (* Pi = ∀◇.Pi' — every row here is a PASS-THROUGH, which is what
       [solve_eq_mono_wrap] is for: the block, the extension and the freshness are
       the premise's, and only the solve step and the target move. *)
    assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
    assert (HwfPi' : {{ Θ0 ⨟ empty ⊢ₚₛ Pi' }}a) by (inversion HwfPi; assumption).
    simpl in Hpre.
    destruct (ad_ppre_tophole_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τe & Hc & Hme & Hp').
    (* the disjunction PROPAGATES along the chain — no need to resolve it *)
    assert (Hwfe : a_wf_ptyp Θw τe \/
                   (exists α0, τe = ptyp_var_f α0 /\ binds α0 abind_tvar Θ))
      by (eapply a_def_chain_wf_or_rigid;
            [ exact Hc | exact HwfΘ | exact HwfΘw | exact Hdefs | exact Hwfτ ]).
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine) as Href'.
    destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
    + (* P0 = unit: GhostGuarded *)
      assert (Hcv : solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τe Pi' pskl_unit L)
        by (apply (IHn Θ0 Θ Θw κ Δ Ψi τe Pi' pskl_unit
                     ltac:(simpl in Hn; simpl; lia)
                     HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi' HwfP0 Hκ Hme Hwfe
                     Hdf Hp' Href' L HL)).
      eapply solve_eq_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__tophole_l_guarded;
        [ apply guarded_pskl__unit | exact Hs ].
    + (* P0 = var_b: not wf *) inversion HwfP0.
    + (* P0 = var β: GhostGuarded (var is guarded) *)
      assert (Hcv : solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τe Pi' (pskl_var_f β) L)
        by (apply (IHn Θ0 Θ Θw κ Δ Ψi τe Pi' (pskl_var_f β)
                     ltac:(simpl in Hn; simpl; lia)
                     HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi' HwfP0 Hκ Hme Hwfe
                     Hdf Hp' Href' L HL)).
      eapply solve_eq_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__tophole_l_guarded;
        [ apply guarded_pskl__var | exact Hs ].
    + (* P0 = arrow: GhostGuarded *)
      assert (HwfP01 : {{ Θ0 ⨟ empty ⊢ₚₛ P01 }}a) by (inversion HwfP0; assumption).
      assert (HwfP02 : {{ Θ0 ⨟ empty ⊢ₚₛ P02 }}a) by (inversion HwfP0; assumption).
      assert (Hcv : solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τe Pi' (pskl_arrow P01 P02) L)
        by (apply (IHn Θ0 Θ Θw κ Δ Ψi τe Pi' (pskl_arrow P01 P02)
                     ltac:(simpl in Hn; simpl; lia)
                     HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi' HwfP0 Hκ Hme Hwfe
                     Hdf Hp' Href' L HL)).
      eapply solve_eq_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__tophole_l_guarded;
        [ apply guarded_pskl__arrow;
            [ eapply a_wf_pskl_lc; exact HwfP01
            | eapply a_wf_pskl_lc; exact HwfP02 ]
        | exact Hs ].
    + (* P0 = all_syn: refinement absurd *)
      simpl in Href'.
      exfalso.
      eapply ad_refine_allinh_lhs_mono_absurd;
        [ exact HwfΘ | exact Href' | reflexivity | reflexivity | exact Hme ].
    + (* P0 = hole: SE-VacuousR *)
      eapply solve_eq_mono_nil; [ apply a_solve_eq__hole_r | exact Hpre ].
    + (* P0 = ∀◇.P0': SE-UnivGhost, second chain hop off the ∀◇ counterpart.
         NOT a [solve_eq_mono_wrap]: this row RE-WRAPS its premise's output in a
         [∀◇], so the package has to be rebuilt by hand — but the block and
         the extension still pass through untouched. *)
      assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a) by (inversion HwfP0; assumption).
      simpl in Href'.
      destruct (ad_refine_tophole_lhs_chain_inv HwfΘ Href' eq_refl eq_refl Hme)
        as (τf & Hc2 & Hmf & Hin).
      assert (Hwff : a_wf_ptyp Θw τf \/
                     (exists α0, τf = ptyp_var_f α0 /\ binds α0 abind_tvar Θ))
        by (eapply a_def_chain_wf_or_rigid;
              [ exact Hc2 | exact HwfΘ | exact HwfΘw | exact Hdefs
              | exact Hwfe ]).
      pose proof (ad_ppre_chain_unfold Hc2 HwfΘ Hdf Hp') as Hp''.
      destruct (IHn Θ0 Θ Θw κ Δ Ψi τf Pi' P0'
                  ltac:(simpl in Hn; simpl; lia)
                  HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi' HwfP0' Hκ Hmf Hwff
                  Hdf Hp'' Hin L HL)
        as (Ξ0 & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
      exists Ξ0, (pskl_tophole Pa), κ'.
      split; [ apply a_solve_eq__tophole_both; exact Hs | ].
      split; [ exact Hfm | ].
      split; [ exact Hu | ].
      split; [ exact Hk | ].
      split; [ exact Hfr | ].
      split; [ exact HF | ].
      eapply ad_ppre_chain_fold;
        [ eapply a_def_chain_trans; [ exact Hc | exact Hc2 ] | ].
      simpl. apply ad_ppre__tophole_remove. exact Hq.
Qed.

(* ==== the Var consistency case: the τ = α instance ====

   ⚠️ [a_binds_tvar α Θ] is a NEW premise (2026-08-04).  It is the [τ = α]
   reading of [a_solve_eq_mono]'s own [a_wf_ptyp Θ τ], which the repaired
   SE-FlexR forces: [guess^TY]'s κ-extension sends the flexible it invents at
   a [◇] to the monotype standing at that position, and [a_inc__flex] admits
   only a monotype WELL-FORMED IN THE TARGET.  It is the paper's usual
   external wf side condition (docs/WF-SIDE-CONDITIONS.md), not a weakening:
   the counterpart of a completeness statement is always assumed well-formed
   in prose. *)
Lemma a_solve_eq_var : forall n Θ0 Θ Θw κ Δ Ψi α Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
     binds α0 (abind_flex_mono_def τ0) Θw) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (a_binds_tvar α Θw \/ binds α abind_tvar Θ) ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f α) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (bskl_var_f α) }}ad ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi (ptyp_var_f α) Pi P0 L.
Proof.
  intros n Θ0 Θ Θw κ Δ Ψi α Pi P0 Hn HwfΘ HwfΘ0 HwfΘw Hmon Hdefs
         HwfPi HwfP0 Hκ Hbα Hdf Hpre Hrefine L HL.
  eapply a_solve_eq_mono with (τ := ptyp_var_f α) (Θw := Θw); eauto.
  - auto with fresco.
  - destruct Hbα as [Hb | Hb];
      [ left; apply a_wf_ptyp__var; exact Hb
      | right; exists α; split; [ reflexivity | exact Hb ] ].
Qed.

(* ===================================================================== *)
(*  GhostG case kit: a dotted-ghost target [holeg] / refinement into a    *)
(*  bare [□] admit ONLY a [□] on the other side — mono paints and         *)
(*  guarded shapes have no rule into them.                                 *)
(* ===================================================================== *)

Lemma d_tags_skl_holeg_inv : forall Ψ,
  d_tags_skl Ψ uskl_holeg -> Ψ [=] empty.
Proof. intros Ψ H; inversion H; subst; auto. Qed.

Lemma ad_ppre_mono_paint_holeg_absurd : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  ψ = uskl_holeg ->
  forall τb, P = ptyp_to_pskl τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros Heqψ τb HeqS Hmb;
    try discriminate Heqψ.
  - (* hole: subject □ is never a paint *)
    destruct τb; simpl in HeqS; discriminate HeqS.
  - (* tophole_remove: subject ∀◇ is never a paint *)
    destruct τb; simpl in HeqS; discriminate HeqS.
  - (* flex_l: unfold the definition, still a mono paint *)
    destruct τb; simpl in HeqS; try discriminate HeqS.
    inversion HeqS; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_mono_paint_hole_rhs_absurd : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  Q = bskl_hole ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  - (* hole: LHS □ is never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove: LHS ∀◇ is never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* ==== the GhostG consistency case, as a standalone lemma ==== *)
(* No size induction: both sides are forced to [□]; every other shape is
   premise-absurd (a ∀◇'s guarded body dies one level down). *)
Lemma a_solve_eq_ghostg : forall Θ0 Θ κ Δ Ψi Pi P0,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] uskl_holeg }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_hole }}ad ->
  (* the block is pinned to [nil]: the only non-absurd row is SE-GhostL,
     which generates nothing, so no κ-extension is needed here *)
  exists Pa, {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa }}a /\
             {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi ] uskl_holeg }}ad.
Proof.
  intros Θ0 Θ κ Δ Ψi Pi P0 HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine.
  assert (Habs_pre_var : forall v Ψ',
            {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ (pskl_var_f v)) ⊑ᵖ[ Ψ' ] uskl_holeg }}ad ->
            False).
  { intros v Ψ' Hp. simpl in Hp.
    eapply ad_ppre_mono_paint_holeg_absurd;
      [ exact HwfΘ | exact Hp | reflexivity | reflexivity
      | eapply a_inc_lookup_mono; eauto ]. }
  assert (Habs_ref_var : forall v,
            {{ Θ ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f v))) ⊳ bskl_hole }}ad ->
            False).
  { intros v Hr. simpl in Hr.
    assert (Hml : mono_ptyp (msubst_lookup κ v))
      by (eapply a_inc_lookup_mono; eauto).
    rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hr.
    eapply ad_refine_mono_paint_hole_rhs_absurd;
      [ exact HwfΘ | exact Hr | reflexivity | reflexivity | exact Hml ]. }
  destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
  - (* Pi = unit: no precision rule into holeg *)
    simpl in Hpre. inversion Hpre.
  - (* Pi = var_b: not wf *) inversion HwfPi.
  - (* Pi = var: a mono paint, absurd *)
    exfalso. eapply Habs_pre_var. exact Hpre.
  - (* Pi = arrow: absurd *) simpl in Hpre. inversion Hpre.
  - (* Pi = all_syn: absurd *) simpl in Hpre. inversion Hpre.
  - (* Pi = □: the live column *)
    destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
    + (* P0 = unit: no refinement into □ *)
      simpl in Hrefine. inversion Hrefine.
    + (* P0 = var_b: not wf *) inversion HwfP0.
    + (* P0 = var: a mono paint, absurd *)
      exfalso. eapply Habs_ref_var. exact Hrefine.
    + (* P0 = arrow: absurd *) simpl in Hrefine. inversion Hrefine.
    + (* P0 = all_syn: absurd *) simpl in Hrefine. inversion Hrefine.
    + (* P0 = □: SE-GhostL, Pa := □ *)
      exists pskl_hole; split; [ apply a_solve_eq__hole_l | exact Hpre ].
    + (* P0 = ∀◇.P0': strip; the guarded body dies *)
      simpl in Hrefine. inversion Hrefine; subst.
      exfalso.
      assert (HgP0' : guarded_pskl P0') by (inversion HwfP0; assumption).
      inversion HgP0'; subst.
      * (* unit *)
        match goal with
        | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ }}ad
          |- _ => simpl in Hin; inversion Hin
        end.
      * (* var *)
        match goal with
        | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f _)) ⊳ _ }}ad
          |- _ => eapply Habs_ref_var; exact Hin
        end.
      * (* arrow *)
        match goal with
        | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _ }}ad
          |- _ => simpl in Hin; inversion Hin
        end.
  - (* Pi = ∀◇.Pi': strip; the guarded body dies *)
    simpl in Hpre. inversion Hpre; subst.
    exfalso.
    assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
    inversion HgPi'; subst.
    + (* unit *)
      match goal with
      | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ pskl_unit ⊑ᵖ[ _ ] _ }}ad |- _ =>
          simpl in Hp'; inversion Hp'
      end.
    + (* var *)
      match goal with
      | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ (pskl_var_f _) ⊑ᵖ[ _ ] _ }}ad |- _ =>
          eapply Habs_pre_var; exact Hp'
      end.
    + (* arrow *)
      match goal with
      | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ (pskl_arrow _ _) ⊑ᵖ[ _ ] _ }}ad |- _ =>
          simpl in Hp'; inversion Hp'
      end.
Qed.

(* ===================================================================== *)
(*  Flex-case kit: a mono paint is a tag-sorted (empty-tag) decorated     *)
(*  skeleton — the ψa-side payload for the flex_l target switch.          *)
(* ===================================================================== *)

Lemma d_tags_skl_mono_paint : forall τ,
  mono_ptyp τ -> d_tags_skl empty (ptyp_to_uskl_syn τ).
Proof.
  intros τ Hm; induction Hm; simpl.
  - apply d_tags_skl__unit; fsetdec.
  - apply d_tags_skl__var; fsetdec.
  - apply d_tags_skl__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ assumption | assumption | fsetdec | fsetdec ].
Qed.

Lemma a_tags_sort_mono_paint : forall NM τ,
  mono_ptyp τ -> a_tags_sort NM empty (ptyp_to_uskl_syn τ).
Proof.
  intros NM τ Hm; destruct NM; constructor;
    auto using mono_ptyp_to_uskl_syn_is_tskl, d_tags_skl_mono_paint,
               mono_ptyp_to_uskl_syn_ghost_free.
Qed.

(* ===================================================================== *)
(*  Topholeg case kit: component tags-sort, and the two mono-paint         *)
(*  absurdities against dotted-∀◇ targets / plain-∀◇ refinement RHS.       *)
(* ===================================================================== *)

Lemma a_tags_sort_topholeg_inv : forall NM Ψ ψ,
  a_tags_sort NM Ψ (uskl_topholeg ψ) -> a_tags_sort NM Ψ ψ.
Proof.
  intros NM Ψ ψ H; inversion H; subst.
  - apply a_tags_sort__sk;
      [ match goal with Ht : is_tskl (uskl_topholeg _) |- _ =>
          inversion Ht; subst; assumption end
      | match goal with Hd : d_tags_skl _ (uskl_topholeg _) |- _ =>
          inversion Hd; subst; assumption end ].
  - match goal with Hg : uskl_ghost_free (uskl_topholeg _) |- _ =>
      inversion Hg end.
Qed.

Lemma ad_ppre_mono_paint_topholeg_absurd : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall ψ0, ψ = uskl_topholeg ψ0 ->
  forall τb, P = ptyp_to_pskl τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros ψ0' Heqψ τb HeqS Hmb;
    try discriminate Heqψ.
  - (* hole *) destruct τb; simpl in HeqS; discriminate HeqS.
  - (* tophole_remove *) destruct τb; simpl in HeqS; discriminate HeqS.
  - (* tophole_keep *) destruct τb; simpl in HeqS; discriminate HeqS.
  - (* flex_l *)
    destruct τb; simpl in HeqS; try discriminate HeqS.
    inversion HeqS; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_mono_paint_tophole_rhs_absurd : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Q0, Q = bskl_tophole Q0 ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Q0' HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  - (* hole *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_keep *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.
