(** P7c — THE DISPATCHER for subtyping completeness
    ([thm:complete-subtyping], algorithmic.tex:1446).

    P7b's seven row lemmas and P7a's five walk rows are all [Qed] in
    prop_sub_complete_thm.v; what is missing is the bundle that ASSEMBLES
    them.  This file is that assembly.

    ⭐ THE DISPATCH IS ON THE JOIN, and it determines the subject.  Each row
    lemma reads its premises off one [ad_pat_sub_gv] constructor; the
    dispatcher inverts the join and delegates.  What the join does NOT fix is
    the UNRESOLVED subject [R] — the motive relates it only by the ≡ᵘ slack
    [Θ ⊢ R' ≡ᵘ κR] — so every shape-fixing row owes a transfer from [R'] to
    [R].  §1 below is that kit.  The transfer is total except at an ARROW,
    where [R] may instead be a bare flexible whose IMAGE is the arrow: that,
    and only that, is where P7a is entered.

    ⚠️ THE TERMINATION IS NOT lex(fuel, |Θ0|).  The two halves call each other
    at the SAME fuel — [a_sub__flex_mono] enters P7a at the same context, and
    P7a's [Flex-Solve] re-enters P7b at the same fuel with a context TWO
    ENTRIES LARGER (it deposits [α̂0 ≔ α̂→β̂] plus the two fresh flexibles).  So
    neither the fuel nor the context decreases on that cycle.  What breaks it
    is the SUBJECT: Flex-Solve re-enters at the subject [α̂ → β̂], an ARROW, and
    a main call at an arrow subject can never come back — the R-variable
    escape into P7a needs a VARIABLE subject, and no join row shrinks an arrow
    to a variable.  So the layering is

      §3  [sub_complete_arrow_subject]  — the main half at an ARROW subject, from the
          fuel IH ALONE (no P7a, no context induction);
      §4  the flex half, by induction on |Θ0| inside an induction on the FULL
          context, using §3 for Flex-Solve and the main half at a SMALLER
          context for Flex-Assign;
      §5  the main half at the same context, using §4 for the R-variable
          escape and the fuel IH for the shrinking rows.

    ⚠️ P7a's walk owes ONE obligation no row carries, because no RULE has it as
    a premise: the STUCK-CHECK.  A RIGID head [β] with [β ∈ ftv P0] matches no
    [a_sub_flex] rule (it cannot enter Ξ — Ξ is [a_decls] — and it cannot be
    dropped, P0 depends on it), so the dispatcher must REFUTE that
    configuration from the solution.  §4.1 is that refutation; it is the twin
    of consistency's ([assign_complete_step]'s rigid-head case,
    prop_consis_complete.v:5000-5090). *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_sub_hyg.
Require Import src.frost.prop_basic.

Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_soundness_consis.
Require Import src.frost.algo.prop_completeness_consis.
Require Import src.frost.algo.prop_sub_msubst_equiv.
Require Import src.frost.algo.prop_precise.       (* ad_precise, ⊢ₚᵣᵃ *)
Require Import src.frost.decorated_algo.prop_decorate.      (* uskl_to_pskl_pskl_to_uskl *)
Require Import src.frost.algo.prop_pat_sub.       (* mono_ptyp_to_uskl_syn_ghost_free *)
Require Import src.frost.algo.prop_completeness_sub_gen.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  THE SHAPE TRANSFER — from the JOIN's subject to the MOTIVE's       *)
(*                                                                        *)
(*  [msubst_uskl_syn] is structural except at a free variable, where it    *)
(*  installs a MONOTYPE PAINTING.  A painting is [unit] / a variable / an   *)
(*  arrow — never a ∀, never a ghost — so a κ-image of any OTHER shape     *)
(*  pins the pre-image's shape exactly, and only the arrow (and unit, and  *)
(*  variable) case admits the variable escape.                            *)
(* ===================================================================== *)

Lemma ptyp_to_uskl_syn_shape : forall τ,
  (exists n, ptyp_to_uskl_syn τ = uskl_var_b n)
  \/ ptyp_to_uskl_syn τ = uskl_unit
  \/ (exists α, ptyp_to_uskl_syn τ = uskl_var_f α)
  \/ (exists A B, ptyp_to_uskl_syn τ = uskl_arrow A B)
  \/ (exists A, ptyp_to_uskl_syn τ = uskl_all_syn A).
Proof.
  intros τ; destruct τ; unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; cbn.
  - right; left; reflexivity.
  - left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; right; left; do 2 eexists; reflexivity.
  - right; right; right; right; eexists; reflexivity.
Qed.

(** A painting is never an ε-tagged ∀, never a ghost. *)
Lemma ptyp_to_uskl_syn_not_etag : forall τ ε R,
  ptyp_to_uskl_syn τ <> uskl_all_etag ε R.
Proof.
  intros τ ε R.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma ptyp_to_uskl_syn_not_hole : forall τ, ptyp_to_uskl_syn τ <> uskl_hole.
Proof.
  intros τ.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma ptyp_to_uskl_syn_not_holeg : forall τ, ptyp_to_uskl_syn τ <> uskl_holeg.
Proof.
  intros τ.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma ptyp_to_uskl_syn_not_tophole : forall τ R,
  ptyp_to_uskl_syn τ <> uskl_tophole R.
Proof.
  intros τ R.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma ptyp_to_uskl_syn_not_topholeg : forall τ R,
  ptyp_to_uskl_syn τ <> uskl_topholeg R.
Proof.
  intros τ R.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

(** …hence the κ-image pins the pre-image at every shape the paintings miss. *)

Lemma msubst_uskl_syn_all_etag_inv : forall κ R ε X,
  msubst_uskl_syn κ R = uskl_all_etag ε X ->
  exists R0, R = uskl_all_etag ε R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros κ R ε X He; destruct R; cbn in He; try discriminate He.
  - exfalso; eapply ptyp_to_uskl_syn_not_etag; exact He.
  - injection He as <- <-. eexists; split; reflexivity.
Qed.

Lemma msubst_uskl_syn_all_syn_inv : forall κ R X,
  msubst_uskl_syn κ R = uskl_all_syn X ->
  (exists R0, R = uskl_all_syn R0 /\ msubst_uskl_syn κ R0 = X)
  \/ (exists α, R = uskl_var_f α).
Proof.
  intros κ R X He; destruct R; cbn in He; try discriminate He.
  - right; eexists; reflexivity.
  - left; injection He as <-; eexists; split; reflexivity.
Qed.

Lemma msubst_uskl_syn_tophole_inv : forall κ R X,
  msubst_uskl_syn κ R = uskl_tophole X ->
  exists R0, R = uskl_tophole R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros κ R X He; destruct R; cbn in He; try discriminate He.
  - exfalso; eapply ptyp_to_uskl_syn_not_tophole; exact He.
  - injection He as <-. eexists; split; reflexivity.
Qed.

Lemma msubst_uskl_syn_topholeg_inv : forall κ R X,
  msubst_uskl_syn κ R = uskl_topholeg X ->
  exists R0, R = uskl_topholeg R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros κ R X He; destruct R; cbn in He; try discriminate He.
  - exfalso; eapply ptyp_to_uskl_syn_not_topholeg; exact He.
  - injection He as <-. eexists; split; reflexivity.
Qed.

(** The ARROW is the one shape a painting CAN have, so here — and only here —
    the pre-image may be a bare variable.  That is exactly the [a_sub__flex_mono]
    entry into P7a. *)
Lemma msubst_uskl_syn_arrow_inv : forall κ R X Y,
  msubst_uskl_syn κ R = uskl_arrow X Y ->
  (exists Ra Rb, R = uskl_arrow Ra Rb /\
     msubst_uskl_syn κ Ra = X /\ msubst_uskl_syn κ Rb = Y)
  \/ (exists α, R = uskl_var_f α).
Proof.
  intros κ R X Y He; destruct R; cbn in He; try discriminate He.
  - right; eexists; reflexivity.
  - left; injection He as <- <-. do 2 eexists; repeat split.
Qed.

(* --------------------------------------------------------------------- *)
(*  …and the ≡ᵘ layer on top: the join's subject is only EQUIVALENT to the *)
(*  κ-image, and [a_uskl_tyequiv__mono] relates two paintings across a     *)
(*  definition chase.  A painting has none of the four shapes below, so    *)
(*  that row cannot fire and the equivalence is structural.                *)
(* --------------------------------------------------------------------- *)

Lemma a_uskl_tyequiv_all_etag_l_inv : forall Θ ε R X,
  Θ ⊢ (uskl_all_etag ε R) ≡ᵘ X ->
  exists X0, X = uskl_all_etag ε X0.
Proof.
  intros Θ ε R X H; inversion H; subst;
    [ exfalso; eapply ptyp_to_uskl_syn_not_etag; eassumption | eexists; reflexivity ].
Qed.

Lemma a_uskl_tyequiv_all_syn_l_inv : forall Θ R X,
  Θ ⊢ (uskl_all_syn R) ≡ᵘ X ->
  exists X0, X = uskl_all_syn X0.
Proof.
  intros Θ R X H; inversion H; subst.
  - exfalso.
    match goal with
    | Hm : mono_ptyp ?t, He : ptyp_to_uskl_syn ?t = uskl_all_syn _ |- _ =>
        destruct Hm; cbn in He; discriminate He
    end.
  - eexists; reflexivity.
Qed.

Lemma a_uskl_tyequiv_tophole_l_inv : forall Θ R X,
  Θ ⊢ (uskl_tophole R) ≡ᵘ X ->
  exists X0, X = uskl_tophole X0 /\ Θ ⊢ R ≡ᵘ X0.
Proof.
  intros Θ R X H; inversion H; subst;
    [ exfalso; eapply ptyp_to_uskl_syn_not_tophole; eassumption
    | eexists; split; [ reflexivity | assumption ] ].
Qed.

Lemma a_uskl_tyequiv_topholeg_l_inv : forall Θ R X,
  Θ ⊢ (uskl_topholeg R) ≡ᵘ X ->
  exists X0, X = uskl_topholeg X0 /\ Θ ⊢ R ≡ᵘ X0.
Proof.
  intros Θ R X H; inversion H; subst;
    [ exfalso; eapply ptyp_to_uskl_syn_not_topholeg; eassumption
    | eexists; split; [ reflexivity | assumption ] ].
Qed.

(** The ARROW case, where the [__mono] row DOES fire.  Either the image is a
    syntactic arrow, or both sides are monotype PAINTINGS — and a painting is
    [unit] / a variable / an arrow, with [unit] excluded because ⇓ is a
    congruence ([a_tyequiv_downarrow]) and [⇓unit] is not an arrow.  The
    surviving variable is exactly the [__flex_mono] escape into P7a. *)
Lemma a_uskl_tyequiv_arrow_l_inv : forall Θ R1 R2 X,
  a_wf_aenv Θ ->
  Θ ⊢ (uskl_arrow R1 R2) ≡ᵘ X ->
  (exists X1 X2, X = uskl_arrow X1 X2) \/ (exists β, X = uskl_var_f β).
Proof.
  intros Θ R1 R2 X Hwf H; inversion H; subst;
    [ | left; do 2 eexists; reflexivity ].
  (* __mono : τ1 is an arrow (its painting is), so ⇓τ2 is an arrow too *)
  match goal with
  | Hm1 : mono_ptyp ?t1, He1 : ptyp_to_uskl_syn ?t1 = uskl_arrow R1 R2,
    Hm2 : mono_ptyp ?t2, Heq : _ ⊢ ?t1 ≡ᵗ ?t2 |- _ =>
      destruct Hm1; cbn in He1; try discriminate He1;
      pose proof (a_tyequiv_downarrow Hwf Heq) as Hdn;
      destruct Hm2; cbn in Hdn |- *;
        [ (* unit : ⇓ of an arrow is an arrow *) exfalso; discriminate Hdn
        | right; eexists; reflexivity
        | left; do 2 eexists; reflexivity ]
  end.
Qed.

(* ===================================================================== *)
(*  §2  THE DISPATCH, SCOPED — the case map and the TERMINATION            *)
(*                                                                        *)
(*  ⚠️ This section is NOT yet proof; it is the scoping the kit above was   *)
(*  built for, recorded here so the next session starts from it rather     *)
(*  than re-deriving it.  docs/DESIGN-completeness-subtyping.md §12.1      *)
(*  carries the same content in prose.                                     *)
(*                                                                        *)
(*  THE CASE MAP.  Inverting [ad_pat_sub_gv] gives twelve rows.  What the  *)
(*  join does NOT fix is the motive's UNRESOLVED subject [R]; §1 is the    *)
(*  transfer, and it is total except at [__arrow]:                         *)
(*                                                                        *)
(*    __infer / __check / __univ_ghost_r / __forall_r   R arbitrary — the  *)
(*        row lemma takes any [R] and does its own transfer internally.    *)
(*    __ghost / __ghostg                                [R' = ◇ / ◈], and  *)
(*        the row lemma takes [R'] directly.                               *)
(*    __arrow                     [R' = R1'→R2'] ⟹ (§1) [κR] is an arrow   *)
(*        or a VARIABLE.  Arrow ⟹ [a_sub_complete_arrow]; variable ⟹ P7a   *)
(*        ([a_sub__flex_mono]).  ⭐ THIS IS THE ONLY ENTRY INTO P7a.        *)
(*    __forall_l_tagged / _untagged   [R] is the same ∀ (a painting is     *)
(*        never a ∀, so the variable escape cannot fire) ⟹ the two ForallL *)
(*        rows, each of which owes TASK 0's [sub_shield].                  *)
(*    __univ_ghost_l / __univ_ghost_lg   [R] is the same ghost ⟹ NO row    *)
(*        lemma exists; strip [pskl_tophole] with [a_sub__univ_ghost_l]    *)
(*        and recurse.  Both preserve the FUEL, so the fuel IH cannot      *)
(*        serve them — they are the inner induction's real work.           *)
(*    __flex_mono                  a pure PEEL: it chases a Θ-definition on *)
(*        the join's side and leaves [R] alone, so the ≡ᵘ slack is         *)
(*        re-established by [flex_def_paint_tyequiv] + transitivity.       *)
(*                                                                        *)
(*  ⚠️⚠️ THE TERMINATION IS **NOT** lex(fuel, |Θ0|) — §12's first cut is    *)
(*  wrong, and this is the finding that reshapes the assembly.  The two    *)
(*  halves call each other at the SAME fuel: [a_sub__flex_mono] enters P7a *)
(*  at the same context, and P7a's [Flex-Solve] re-enters P7b at the same  *)
(*  fuel with a context TWO ENTRIES LARGER (it deposits [α̂0 ≔ α̂→β̂] plus    *)
(*  the two fresh flexibles — prop_sub_complete_thm.v:4586).  So on that   *)
(*  cycle neither component decreases.  [Flex-Assign] is fine (it consumes *)
(*  the definition, so the context shrinks by one).                        *)
(*                                                                        *)
(*  ⭐ WHAT BREAKS THE CYCLE IS THE SUBJECT.  Flex-Solve re-enters at the   *)
(*  subject [α̂ → β̂] — an ARROW — and a main call at an arrow subject can   *)
(*  NEVER come back into P7a: the escape needs a VARIABLE subject, and no  *)
(*  join row shrinks an arrow to a variable ([__univ_ghost_l] needs a ∀◇    *)
(*  subject, [__flex_mono] leaves [R] alone).  So the layering that works  *)
(*  is                                                                     *)
(*                                                                        *)
(*    (a) [sub_complete_arrow_subject] — the main half at an ARROW subject, from   *)
(*        the fuel IH ALONE: no P7a, no context induction.                 *)
(*    (b) the flex half at |Ξ ++ Θ0| = k, by an inner induction on |Θ0|    *)
(*        (Flex-Depend keeps the total and shrinks Θ0), using (a) for      *)
(*        Flex-Solve and the main half at k-1 for Flex-Assign.             *)
(*    (c) the main half at k, using (b) for the R-variable escape and the  *)
(*        fuel IH for the fuel-consuming rows; its inner induction on the  *)
(*        join handles the three fuel-preserving ones.                     *)
(*    (d) strong induction on k, then on the fuel.                         *)
(*                                                                        *)
(*  TWO OBLIGATIONS ARE STILL OPEN, and neither is mechanical:             *)
(*                                                                        *)
(*  ⭕ (1) TASK 0's residual, at the two ForallL rows.  The premise is now  *)
(*     POSITIONALLY indexed and machine-checked SATISFIABLE at the node     *)
(*     that used to refute it ([p7_sub_shield_repaired_holds]), but        *)
(*     prop_sub_shield_supply.v still discharges it only for a flex-free / *)
(*     atomic / mono-counterpart / inh-free-counterpart / ∀-free [P0].     *)
(*     A [P0] carrying a ∀ below its head has no general route, so the     *)
(*     dispatcher must take it as a hypothesis (DESIGN §12 item 3).        *)
(*                                                                        *)
(*  ⭕ (2) P7a's STUCK-CHECK.  A RIGID head [β] with [β ∈ ftv P0] matches   *)
(*     no [a_sub_flex] rule — it cannot enter Ξ ([a_decls] holds only      *)
(*     flexible declarations) and it cannot be dropped ([Flex-SkipRigid]   *)
(*     needs [β ∉ ftv P0]) — so the dispatcher must REFUTE it from the      *)
(*     solution.  Consistency's twin is [assign_complete_step]'s rigid     *)
(*     head case (prop_consis_complete.v:5000-5090): [rigid_survives_      *)
(*     solution] puts β in [ftv (κP)], and [ad_pat_consis_rigid_ftv_rev_   *)
(*     scoped] confines the subject's rigid ftv to [κα̂]'s scope.           *)
(*     ⚠️ THE SUBTYPING CHAIN IS NOT THE SAME.  There the pattern IS the    *)
(*     join's subject; here [P0] sits on the FILL side ([Θ ⊢ᵣ inh{κP0} ⊳    *)
(*     Q]) and the join's subject is [κα̂].  So the chain must run          *)
(*     β ∈ ftv P0 ⟹ β ∈ ftv (κP0) ⟹ β ∈ ftv Q ⟹ β ∈ ftv (κα̂) — and its     *)
(*     last step is the direction "the SUBJECT confines the TARGET", which *)
(*     is FALSE for the join in general ([ad_pat_sub_gv__ghost] gives a ◇   *)
(*     subject an arbitrary target).  It has to be re-derived for the      *)
(*     MONOTYPE subject the walk actually has, where every row carries a   *)
(*     refinement premise off the subject's HOLE-FREE erasure.  That is    *)
(*     the piece to build first.                                          *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §3  THE TRANSFER, COMPLETED — the two shapes §1 left open              *)
(*                                                                        *)
(*  §1 pins the pre-image at every shape a monotype PAINTING misses.  Two  *)
(*  shapes it does NOT miss still have to be settled, because the join     *)
(*  reaches them: a VARIABLE image (only a variable can have one) and an   *)
(*  [uskl_all_syn] image (which a painting could have, were the image not  *)
(*  a MONOTYPE — that is what [a_inc] supplies).                           *)
(* ===================================================================== *)

(** Only a variable's image is a variable: every other node of
    [msubst_uskl_syn] is a congruence. *)
Lemma msubst_uskl_syn_var_inv : forall κ R β,
  msubst_uskl_syn κ R = uskl_var_f β ->
  exists α, R = uskl_var_f α.
Proof.
  intros κ R β He; destruct R; cbn in He; try discriminate He.
  eexists; reflexivity.
Qed.

(** …and the [uskl_all_syn] escape of [msubst_uskl_syn_all_syn_inv] is
    CLOSED once the images are known to be monotypes: [ptyp_to_uskl_syn τ]
    is a ∀ only for [τ = ptyp_all _], which is not [mono_ptyp]. *)
Lemma msubst_uskl_syn_all_syn_inv_mono : forall Θ0 κ Θ R X,
  κ ∷ Θ0 ⊑ Θ ->
  msubst_uskl_syn κ R = uskl_all_syn X ->
  exists R0, R = uskl_all_syn R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros Θ0 κ Θ R X Hinc He.
  destruct (@msubst_uskl_syn_all_syn_inv κ R X He) as [Hall | [α ->]];
    [ exact Hall | exfalso ].
  cbn in He.
  pose proof (@a_inc_lookup_mono Θ0 κ Θ α Hinc) as Hm.
  destruct (msubst_lookup κ α); cbn in He; try discriminate He.
  inversion Hm.
Qed.

(* ===================================================================== *)
(*  §4  THE RIGID-SUBJECT REFUTATION                                       *)
(*                                                                        *)
(*  At the [__arrow] row the motive's subject [R] may be a bare VARIABLE   *)
(*  (§1).  If that variable is FLEXIBLE in [Θ0] the dispatcher enters P7a  *)
(*  through [a_sub__flex_mono]; if it is RIGID, NO [a_sub] rule fires at   *)
(*  an FN mode, so the configuration must be refuted from the solution.    *)
(*  It is: a rigid variable is untouched by [κ], and ⇓ separates it from   *)
(*  an arrow ([a_tyequiv_downarrow] is a congruence and ⇓ of an arrow is    *)
(*  an arrow).                                                            *)
(* ===================================================================== *)

(** ⇓ only ever rewrites FLEXIBLE variables. *)
Lemma aenv_msubst_dom_flex : forall Θ α,
  α `in` dom (aenv_msubst Θ) ->
  a_flex_tvar Θ α.
Proof.
  induction Θ as [ | [β b] Θ' IH ]; intros α Hin; cbn in Hin;
    [ exfalso; clear - Hin; fsetdec | ].
  destruct b as [ | A | P | | τ ]; cbn in Hin;
    try (destruct (IH α Hin) as [Hb | [τ0 Hb]];
         [ left | right; exists τ0 ]; unfold binds; cbn; right; exact Hb).
  - (* β ~ flex_mono *)
    destruct (α == β) as [-> | Hne];
      [ left; unfold binds; cbn; left; reflexivity | ].
    assert (Hin' : α `in` dom (aenv_msubst Θ')) by (clear - Hin Hne; fsetdec).
    destruct (IH α Hin') as [Hb | [τ0 Hb]];
      [ left | right; exists τ0 ]; unfold binds; cbn; right; exact Hb.
  - (* β ~ flex_mono_def τ *)
    destruct (α == β) as [-> | Hne];
      [ right; exists τ; unfold binds; cbn; left; reflexivity | ].
    assert (Hin' : α `in` dom (aenv_msubst Θ')) by (clear - Hin Hne; fsetdec).
    destruct (IH α Hin') as [Hb | [τ0 Hb]];
      [ left | right; exists τ0 ]; unfold binds; cbn; right; exact Hb.
Qed.

(** …so a rigid variable is its own ⇓-normal form. *)
Lemma downarrow_rigid : forall Θ α,
  uniq Θ ->
  binds α abind_tvar Θ ->
  ⇓ᵗ[Θ] (ptyp_var_f α) = ptyp_var_f α.
Proof.
  intros Θ α Huq Hb. cbn.
  apply msubst_lookup_notin.
  intro Hin.
  destruct (@aenv_msubst_dom_flex Θ α Hin) as [Hbf | [τ Hbf]];
    pose proof (binds_unique _ _ _ _ _ Hb Hbf Huq) as Hc; discriminate Hc.
Qed.

(** THE REFUTATION.  A rigid [α] is never ≡ᵗ an arrow. *)
Lemma tyequiv_arrow_rigid_absurd : forall Θ α τ1 τ2,
  a_wf_aenv Θ ->
  binds α abind_tvar Θ ->
  Θ ⊢ (ptyp_arrow τ1 τ2) ≡ᵗ (ptyp_var_f α) ->
  False.
Proof.
  intros Θ α τ1 τ2 Hwf Hb Heq.
  pose proof (a_tyequiv_downarrow Hwf Heq) as Hdn.
  rewrite (@downarrow_rigid Θ α (a_wf_aenv_uniq Hwf) Hb) in Hdn.
  cbn in Hdn. discriminate Hdn.
Qed.

(** …and hence a rigid subject cannot meet the join's ARROW row.  This is
    the sub-case of §1's arrow escape that does NOT go into P7a. *)
Lemma slack_arrow_rigid_absurd : forall Θ0 κ Θ α R1' R2',
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  binds α abind_tvar Θ0 ->
  Θ ⊢ (uskl_arrow R1' R2') ≡ᵘ (msubst_uskl_syn κ (uskl_var_f α)) ->
  False.
Proof.
  intros Θ0 κ Θ α R1' R2' Hwf0 Hwf Hinc Hb Hslack.
  assert (Hnd : α `notin` dom κ)
    by (eapply a_inc_tvar_notin_dom; [ exact Hinc | exact Hwf0 | exact Hb ]).
  assert (HbΘ : binds α abind_tvar Θ)
    by (eapply a_inc_binds_tvar; [ exact Hinc | exact Hb ]).
  cbn in Hslack. rewrite (msubst_lookup_notin κ Hnd) in Hslack.
  destruct (@a_uskl_tyequiv_mono_r_inv Θ _ _ Hslack (ptyp_var_f α) eq_refl
              (mono_ptyp__var α) (@a_wf_ptyp__var Θ α (or_introl HbΘ)))
    as [τ' [Heqτ' [Hm' [Hwf' Heq']]]].
  destruct τ'; cbn in Heqτ'; try discriminate Heqτ'.
  eapply tyequiv_arrow_rigid_absurd; [ exact Hwf | exact HbΘ | exact Heq' ].
Qed.

(* ===================================================================== *)
(*  §5  THE STUCK-CHECK — a RIGID head that [P0] depends on is REFUTED     *)
(*                                                                        *)
(*  A rigid head [β] with [β ∈ ftv P0] matches NO [a_sub_flex] rule: it    *)
(*  cannot enter Ξ ([a_decls] holds only flexible declarations) and        *)
(*  [Flex-SkipRigid] needs [β ∉ ftv P0].  So the dispatcher must refute    *)
(*  that configuration from the SOLUTION.                                  *)
(*                                                                        *)
(*  ⚠️ THE CHAIN IS NOT CONSISTENCY'S.  There ([assign_complete_step]'s     *)
(*  rigid-head case, prop_consis_complete.v:5000-5090) the pattern IS the  *)
(*  join's subject, so [ad_pat_consis_rigid_ftv_rev_scoped] closes it in   *)
(*  one step.  Here [P0] sits on the FILL side ([Θ ⊢ᵣ inh{κP0} ⊳ Q]) and   *)
(*  the join's subject is [κα̂], so the chain must run                      *)
(*                                                                        *)
(*    β ∈ ftv P0  ⟹  β ∈ ftv (κP0)  ⟹  β ∈ ftv Q  ⟹  β ∈ ftv (κα̂)         *)
(*                                                                        *)
(*  whose last step is "the SUBJECT confines the TARGET" — FALSE for the   *)
(*  join in general ([ad_pat_sub_gv__ghost] gives a ◇ subject an arbitrary *)
(*  target).  ⭐ What makes it TRUE here is that the walk's subject is a    *)
(*  MONOTYPE, and P7a's [Flex-SkipRigid] row already built exactly that    *)
(*  confinement: [sub_gv_bskl_downarrow_mono_scoped] (the ⇓-form, which is *)
(*  also what absorbs the motive's ≡ᵘ slack — ≡ᵗ does not preserve         *)
(*  ftv-scoping but it does preserve ⇓) composed with the FILL's           *)
(*  [refine_syn_f_downarrow_source_ftv].  So §5 is steps 0–4 of            *)
(*  [a_sub_flex_complete_skip_rigid] read as a REFUTATION.                 *)
(* ===================================================================== *)

Lemma sub_flex_rigid_head_absurd :
  forall n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q,
  a_decls Ξ ->
  dom Ξ [<=] ftvar_in_pskl P0 ->
  a_wf_aenv (Ξ ++ (β ~ abind_tvar) ++ Θ0) ->
  a_wf_aenv Θ ->
  (Ξ ++ (β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  a_flex_tvar Θ0 α ->
  β `in` ftvar_in_pskl P0 ->                       (* the STUCK configuration *)
  κ ∷ (Ξ ++ (β ~ abind_tvar) ++ Θ0) ⊑ Θ ->
  Θ ⊢ R' ≡ᵘ (ptyp_to_uskl_syn (msubst_lookup κ α)) ->
  ad_pat_sub_gv n NM (mode_fn M) Ψ Θ R' Q ->
  ad_refine_syn_f empty Θ empty (pskl_to_bskl_inh (msubst_pskl κ P0)) Q ->
  False.
Proof.
  intros n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q
         HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα Hβin Hinc Hslack HD Hrs.
  (* ---- 0. the context, and the subject's binding ---- *)
  assert (Huq : uniq (Ξ ++ (β ~ abind_tvar) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
  assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
    by (eapply a_wf_aenv_strip_mid; [ exact HdeclsΞ | exact Hwf ]).
  assert (HwfΘ0 : a_wf_aenv Θ0) by (eapply a_wf_aenv_app_r; exact Hwf').
  assert (Hαb0 : a_binds_tvar α Θ0)
    by (destruct Hfα as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (Hαbfull : a_binds_tvar α (Ξ ++ (β ~ abind_tvar) ++ Θ0)).
  { destruct (a_flex_tvar_app_weaken (Ξ ++ (β ~ abind_tvar)) Hfα)
      as [h | [τ0 h]];
      [ right; left | right; right; exists τ0 ]; simpl_env in h; exact h. }
  assert (Hbβ : binds β abind_tvar (Ξ ++ (β ~ abind_tvar) ++ Θ0))
    by (simpl_env; apply binds_app_3; apply binds_app_2;
        unfold binds; simpl; left; reflexivity).
  (* ---- 1. peel Ξ off κ, then invert the RIGID middle ---- *)
  destruct (@a_inc_strip_decls_prefix Ξ ((β ~ abind_tvar) ++ Θ0) κ Θ HdeclsΞ
              Hinc)
    as [κa [κb [Heqκ [Hdκa Hincxb]]]].
  destruct (a_inc_tvar_inv Hincxb) as [Ξv [Θ' [HeqΘ [HsufΞv Hincb]]]].
  assert (HwfΘ' : a_wf_aenv Θ').
  { rewrite HeqΘ in Hwfth.
    eapply a_wf_aenv_app_r with (Θp := Ξv ++ (β ~ abind_tvar)).
    simpl_env. simpl_env in Hwfth. exact Hwfth. }
  assert (HeqW : (Ξv ++ (β ~ abind_tvar)) ++ Θ' = Θ)
    by (rewrite HeqΘ; simpl_env; reflexivity).
  assert (HβΘ' : β `notin` dom Θ').
  { rewrite HeqΘ in HuqΘ. clear - HuqΘ. simpl_env in HuqΘ. solve_uniq. }
  (* ---- 2. the subject is a MONO painting, and ⇓ pins it to [κα̂] ---- *)
  assert (Hmκα : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact Hinc).
  assert (Hwfκα : a_wf_ptyp Θ (msubst_lookup κ α))
    by (eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact Hαbfull ]).
  destruct (a_uskl_tyequiv_mono_r_inv Hslack
              (eq_refl (ptyp_to_uskl_syn (msubst_lookup κ α))) Hmκα Hwfκα)
    as [τ' [HeqR' [Hmτ' [Hwfτ' Heqττ']]]].
  subst R'.
  assert (Hddτ' : ⇓ᵗ[ Θ ] τ' = ⇓ᵗ[ Θ ] (msubst_lookup κ α))
    by (apply a_tyequiv_downarrow; [ exact Hwfth | exact Heqττ' ]).
  (* ---- 3. the subject's image is scoped in the TRUNCATION ---- *)
  assert (Hακa : α `notin` dom κa).
  { rewrite Hdκa.
    assert (hd : α `in` dom Θ0)
      by (destruct Hfα as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
    clear - Huq hd. simpl_env in Huq. solve_uniq. }
  assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup κ α)).
  { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb Hακa).
    eapply a_inc_lookup_wf; [ exact Hincb | exact HwfΘ0 | exact Hαb0 ]. }
  assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ')
    by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
  assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup κ α) = ⇓ᵗ[ Θ' ] (msubst_lookup κ α)).
  { rewrite <- HeqW.
    apply downarrow_app_agree_ptyp; [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
  assert (HO1 : ftvar_in_ptyp (⇓ᵗ[ Θ ] τ') [<=] dom Θ').
  { rewrite Hddτ'. rewrite Hddα. apply a_wf_ptyp_ftv_dom.
    apply a_wf_ptyp_downarrow_mono;
      [ exact HwfΘ' | exact Hwfα' | exact Hmκα ]. }
  (* ---- 4. the JOIN's ⇓-confinement, and the FILL's source below it ---- *)
  assert (Hmono_img : forall γ, mono_ptyp (msubst_lookup (aenv_msubst Θ) γ))
    by (intros; apply aenv_msubst_image_mono; exact Hwfth).
  assert (HO2 : ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] dom Θ').
  { eapply sub_gv_bskl_downarrow_mono_scoped;
      [ exact HD | exact Hwfth | reflexivity | exact Hmτ' | exact HO1 ]. }
  assert (Heqinh : ⇓ᵇ[ Θ ] (pskl_to_bskl_inh (msubst_pskl κ P0))
                   = pskl_to_bskl_inh (⇓ˢ[ Θ ] (msubst_pskl κ P0)))
    by (apply msubst_bskl_pskl_to_bskl_inh; exact Hmono_img).
  assert (HO3 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P0)) [<=] dom Θ').
  { pose proof (refine_syn_f_downarrow_source_ftv Hrs Hwfth
                  ltac:(intros x Hx; exfalso; clear - Hx; fsetdec)) as h.
    rewrite Heqinh in h. rewrite ftvar_in_bskl_inh in h.
    clear - h HO2. fsetdec. }
  (* ---- 5. …but β SURVIVES the solution, and it is NOT in the truncation ---- *)
  assert (HβκP0 : β `in` ftvar_in_pskl (msubst_pskl κ P0))
    by (eapply rigid_survives_solution;
        [ exact Hinc | exact Hwf | exact Hbβ | exact Hβin ]).
  assert (HβΘdn : β `notin` dom (aenv_msubst Θ)).
  { intro Hin.
    assert (HbβΘ : binds β abind_tvar Θ)
      by (eapply a_inc_binds_tvar; [ exact Hinc | exact Hbβ ]).
    destruct (@aenv_msubst_dom_flex Θ β Hin) as [Hbf | [τ0 Hbf]];
      pose proof (binds_unique _ _ _ _ _ HbβΘ Hbf HuqΘ) as Hc; discriminate Hc. }
  assert (Hβdn : β `in` ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P0)))
    by (apply msubst_pskl_ftv_notin_dom; [ exact HβΘdn | exact HβκP0 ]).
  clear - Hβdn HO3 HβΘ'. fsetdec.
Qed.

(* ===================================================================== *)
(* ===================================================================== *)
(*  §6  ⚠️ THE PAPER GAP THIS ASSEMBLY EXPOSED — NOW CLOSED, BOTH HALVES    *)
(*                                                                        *)
(*  [fig:alg-subtyping]'s second box (full-algo-spec.tex:883-912) has five *)
(*  rules and NONE matches a term entry [x : P], while the paper's twin     *)
(*  walk has [Assign-SkipTmVar] (full-algo-spec.tex:1791).  That makes     *)
(*  [thm:complete-subtyping] FALSE for the printed rule set, at a          *)
(*  configuration `fun x -> x 1` produces and the reference implementation *)
(*  CRASHES on — cex/cex_p7_flex_walk_tm_var.v, docs/PAPER-GAPS.md.        *)
(*                                                                        *)
(*  ⭐ THE RULES ARE IN THE TREE (2026-08-03): [a_sub_flex__skip_tm_var] /   *)
(*  [__skip_tm_skl] (algo/def_extra.v) with decorated mirrors, and the      *)
(*  three mutual inductions over the [a_sub] / [a_sub_flex] pair — the      *)
(*  soundness bundle, the decoration bundle and equivariance — all carry    *)
(*  their two new cases.                                                   *)
(*                                                                        *)
(*  ⭐ AND SO ARE THEIR COMPLETENESS ROWS (2026-08-03):                      *)
(*  [a_sub_flex_complete_skip_tm_var] / [_skip_tm_skl]                      *)
(*  (prop_sub_complete_thm.v §(N)/§(O)), so [sub_flex_complete_holds] below dispatches a  *)
(*  term-variable head like any other and needs no side condition on [Θ0].  *)
(*  Each row is [a_sub_flex_complete_skip_rigid]'s ⇓-truncation apparatus   *)
(*  with the tvar pieces swapped for the var ones ([a_inc_var_inv],         *)
(*  [a_inc_var_mid_strip_id], [a_inc_equiv_mid_insert_var]) plus the        *)
(*  SEMANTIC MIDDLE [Θ' ⊢ A' ≡ᵗ κ A] that a payload-free rigid entry does   *)
(*  not have, cribbed from the consistency twin's [Assign-SkipTmVar]        *)
(*  (prop_consis_complete.v:5595-5690) and read back through the junk swap  *)
(*  with [msubst_ptyp_kswap].  ⭐ Neither row carries the rigid row's        *)
(*  [α ≠ β] / [β ∉ ftv P0] premises: a term entry is never [a_binds_tvar],  *)
(*  so under [uniq] both are DERIVED — which is why the RULES carry none    *)
(*  either, exactly as the twin walk's [Assign-SkipTmVar] does not.         *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §7  THE FLEX HALF (P7a's assembly) — DESIGN §12.1's layer (b)          *)
(*                                                                        *)
(*  Structural induction on [Θ0] with the suffix [Ξ] GENERALIZED and the   *)
(*  TOTAL context length bounded by [k]: Flex-Depend keeps the total and   *)
(*  shrinks [Θ0] (so it is the structural IH), Flex-Skip / Flex-SkipRigid  *)
(*  shrink both, Flex-Assign CONSUMES the definition and re-enters the     *)
(*  main half one entry SHORTER, and Flex-Solve re-enters it at an ARROW   *)
(*  subject over a LARGER context — which is why [sub_complete_arrow] is a         *)
(*  separate hypothesis, discharged from the FUEL IH alone.                *)
(* ===================================================================== *)

Definition sub_complete_arrow (n : nat) : Prop :=
  forall NM M Θ0 P0 P Ra Rb R' Ψ Θ κ Q,
    sub_complete_concl n NM M Θ0 P0 P (uskl_arrow Ra Rb) R' Ψ Θ κ Q.

Definition sub_complete_ctx_lt (n k : nat) : Prop :=
  forall NM M Θ0 P0 P R R' Ψ Θ κ Q,
    length Θ0 < k ->
    sub_complete_concl n NM M Θ0 P0 P R R' Ψ Θ κ Q.

Lemma sub_flex_complete_holds : forall n k,
  sub_complete_arrow n ->
  sub_complete_ctx_lt n k ->
  forall NM M Θ0 Ξ α P0 R' Ψ Θ κ Q,
    length Ξ + length Θ0 <= k ->
    sub_flex_complete_concl n NM M Θ0 Ξ α P0 R' Ψ Θ κ Q.
Proof.
  intros n k Harrow Hmain NM M Θ0.
  induction Θ0 as [ | [β b] Θ0' IHΘ0 ];
    intros Ξ α P0 R' Ψ Θ κ Q Hlen.
  - (* the empty context: the subject cannot be flexible there *)
    unfold sub_flex_complete_concl.
    intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
           HwfQ.
    exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb.
  - (* the head decides the row *)
    assert (IH' : forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
              length Ξ' <= S (length Ξ) ->
              sub_flex_complete_concl n NM M Θ0' Ξ' α' P0' R'' Ψ' Θ'' κ' Q').
    { intros Ξ' α' P0' R'' Ψ' Θ'' κ' Q' HlenΞ.
      apply IHΘ0; simpl in Hlen; lia. }
    destruct b as [ | A | P | | τ ].
    + (* β RIGID: the STUCK configuration, or Flex-SkipRigid *)
      destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P0))
        as [Hβin | Hβni];
        [ | destruct (α == β) as [Heqαβ | Hne] ].
      * (* ⭕ β ∈ ftv P0 : NO RULE FIRES — refute the solution (§5) *)
        unfold sub_flex_complete_concl.
        intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD
               Hrs HwfQ.
        exfalso.
        assert (Hne : α <> β).
        { intro Heq; subst β.
          assert (Huq : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ0'))
            by (apply a_wf_aenv_uniq; exact Hwf).
          destruct Hfα as [Hb | [τ0 Hb]];
            (apply binds_cons_1 in Hb as [[_ Hc] | Hb];
             [ discriminate Hc
             | apply binds_In in Hb; simpl_env in Huq; solve_uniq ]). }
        assert (Hfα0 : a_flex_tvar Θ0' α)
          by (eapply a_flex_tvar_strip_head; [ exact Hne | exact Hfα ]).
        eapply sub_flex_rigid_head_absurd;
          [ exact HdeclsΞ | exact HdomΞ | exact Hwf | exact Hwfth | exact HwfP0
          | exact Hfα0 | exact Hβin | exact Hinc | exact Hslack | exact HD
          | exact Hrs ].
      * (* the subject cannot BE the rigid head *)
        subst α.
        unfold sub_flex_complete_concl.
        intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD
               Hrs HwfQ.
        exfalso.
        assert (Huq : uniq (Ξ ++ (β ~ abind_tvar) ++ Θ0'))
          by (apply a_wf_aenv_uniq; exact Hwf).
        destruct Hfα as [Hb | [τ0 Hb]];
          (apply binds_cons_1 in Hb as [[_ Hc] | Hb];
           [ discriminate Hc
           | apply binds_In in Hb; simpl_env in Huq; solve_uniq ]).
      * apply (a_sub_flex_complete_skip_rigid IH' Hne Hβni).
    + (* β a TERM variable, type binding: Flex-SkipTmVar (§6).  Unlike the
         rigid head there is no stuck configuration and no side condition —
         the row derives [α ≠ β] and [β ∉ ftv P0] itself. *)
      apply (a_sub_flex_complete_skip_tm_var IH').
    + (* β a TERM variable, skeleton binding: Flex-SkipTmVar (skl) *)
      apply (a_sub_flex_complete_skip_tm_skl IH').
    + (* β an UNDEFINED flexible: Flex-Solve (β = α) / Depend / Skip *)
      destruct (β == α) as [-> | Hne].
      * apply (a_sub_flex_complete_solve Harrow).
      * destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P0))
          as [Hβin | Hβni].
        -- apply (a_sub_flex_complete_depend IH' (not_eq_sym Hne) Hβin).
        -- apply (a_sub_flex_complete_skip IH' (not_eq_sym Hne) Hβni).
    + (* β a DEFINED flexible: Flex-Assign (covers β = α, by design) *)
      apply (a_sub_flex_complete_assign (n := n) (Ξ := Ξ) (Θ0 := Θ0')).
      intros NM' M' Θ0'' P0' P' R'' T'' Ψ' Θ' κ' Q' Hle.
      apply (Hmain NM' M' Θ0'' P0' P' R'' T'' Ψ' Θ' κ' Q').
      simpl in Hlen. lia.
Qed.

Print Assumptions sub_flex_rigid_head_absurd.
Print Assumptions slack_arrow_rigid_absurd.
Print Assumptions sub_flex_complete_holds.

(* ===================================================================== *)
(*  §8  THE CHECK ROW's ONE OBLIGATION — [guarded_pskl P0]                 *)
(*                                                                        *)
(*  [a_sub_complete_check] demands it (the algorithm's Check/ForallR split *)
(*  is on exactly this), and the JOIN does not supply it.  Mode            *)
(*  compatibility gives [P0 = ptyp_to_pskl A], so the only unguarded shape *)
(*  left is a ∀-headed [A]; that is refuted against the FILL.  A           *)
(*  [bskl_all_inh] SOURCE refines only to a [bskl_all_inh] TARGET — the    *)
(*  only rows with such a source are [__all] and [__flex_r], and           *)
(*  [__flex_r]'s chain cannot bottom out because a monotype painting is    *)
(*  never [bskl_all_inh] — while the Check row's counterpart is            *)
(*  [pskl_to_bskl_inh B] with [guarded_pskl B].  This is the SOURCE-side   *)
(*  mirror of [ad_refine_syn_f_all_inh_r_shape].                          *)
(* ===================================================================== *)

Lemma ad_refine_syn_f_all_inh_l_shape : forall F Θ Δ A Qt,
  ad_refine_syn_f F Θ Δ (bskl_all_inh A) Qt ->
  exists B, Qt = bskl_all_inh B.
Proof.
  intros F Θ Δ A Qt H.
  remember (bskl_all_inh A) as S eqn:HS. revert A HS.
  induction H; intros A0 HS; try discriminate HS.
  - (* all *) eexists; reflexivity.
  - (* flex_r : the target's definition is a MONOTYPE painting, never ∀-inh *)
    exfalso.
    destruct (IHad_refine_syn_f _ HS) as [B HB].
    destruct τ; cbn in HB; discriminate HB.
Qed.

Lemma check_row_guarded_p0 : forall Θ0 κ Θ P0 B,
  κ ∷ Θ0 ⊑ Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat mode_tc P0 ->
  guarded_pskl B ->
  ad_refine_syn_f empty Θ empty (pskl_to_bskl_inh (msubst_pskl κ P0))
    (pskl_to_bskl_inh B) ->
  guarded_pskl P0.
Proof.
  intros Θ0 κ Θ P0 B Hinc HwfP0 Hmod HgB Hrs.
  pose proof (a_wf_pskl_lc HwfP0) as Hlc.
  inversion Hmod as [ | A HeqP0 | ]; subst.
  destruct A; cbn in *.
  - apply guarded_pskl__unit.
  - (* var_b : excluded by local closure *) inversion Hlc.
  - apply guarded_pskl__var.
  - inversion Hlc; subst. apply guarded_pskl__arrow; assumption.
  - (* ∀ : the fill forces a ∀-inh counterpart, which is not guarded *)
    exfalso.
    destruct (ad_refine_syn_f_all_inh_l_shape Hrs) as [B0 HB0].
    destruct (@pskl_to_bskl_inh_all_inh_inv B B0 HB0) as [X [HX _]].
    subst B. inversion HgB.
Qed.

(* ===================================================================== *)
(*  §8b  A2 — THE JOIN PERMUTATION (the paper's WLOG, mechanized)         *)
(* ===================================================================== *)

(** Fuel monotonicity for the leaf-valid hygienic join.  The fuel is the
    declarative derivation's HEIGHT, so a derivation of height [n] is also
    one of every larger height.  Needed because the permutation below
    returns the family at whatever height the extraction yields, while
    [a_sub_complete_forall_r] wants it at exactly [n] for a conclusion at
    [S n]. *)
Lemma ad_pat_sub_gv_fuel_weaken : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  forall m, n <= m -> ad_pat_sub_gv m NM M Ψ Θ R Q.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; intros m Hle;
    try solve [ econstructor; eauto ].
  - (* forall_r : the conclusion's fuel is [S n] *)
    destruct m as [ | m' ]; [ lia | ].
    apply ad_pat_sub_gv__forall_r with (L := L).
    intros α Hα. apply H0; [ exact Hα | lia ].
  - (* arrow *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_gv__arrow;
      [ exact H | exact H0 | apply IHad_pat_sub_gv; lia | assumption ].
  - (* forall_l_tagged *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_gv__forall_l_tagged;
      [ eassumption | eassumption | eassumption | eassumption | eassumption
      | apply IHad_pat_sub_gv; lia ].
  - (* forall_l_untagged *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_gv__forall_l_untagged;
      [ eassumption | eassumption | eassumption | eassumption | eassumption
      | apply IHad_pat_sub_gv; lia ].
Qed.

(** ⭐ THE JOIN PERMUTATION.  From ANY TY/TC join onto a [bskl_all_inh]
    target — however many ForallL steps sit on top of it — recover the
    cofinite ForallR family that [a_sub_complete_forall_r] consumes, with
    the ForallL instantiations re-applied under the new binder.

    The ForallL chain must bottom out in [__forall_r]: [__check] is the only
    other TY/TC row that can carry this target, and its [guarded_pskl]
    premise refutes a ∀-inh counterpart (the same step §8 makes, read the
    other way round). *)
Lemma sub_gv_all_inh_forall_r_family : forall n NM M Ψ Θ R Qt,
  ad_pat_sub_gv n NM M Ψ Θ R Qt ->
  forall B, NM = a_sub_mode_ty -> M = mode_tc -> Qt = bskl_all_inh B ->
  exists L m, m < n /\
    forall α, α `notin` L ->
      ad_pat_sub_gv m a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ) R
        (open_bskl_wrt_bskl B (bskl_var_f α)).
Proof.
  intros n NM M Ψ Θ R Qt H; induction H; intros B0 HNM HM HQ;
    try discriminate.
  - (* check : a ∀-inh counterpart is not [guarded_pskl] *)
    exfalso.
    destruct (@pskl_to_bskl_inh_all_inh_inv _ _ HQ) as [X [HX _]].
    subst B. match goal with Hg : guarded_pskl _ |- _ => inversion Hg end.
  - (* forall_r : the family is the premise itself *)
    inversion HQ; subst.
    exists L, n. split; [ lia | ].
    intros α Hα.
    match goal with
    | Hf : forall α, α `notin` L -> ad_pat_sub_gv _ _ _ _ _ _ _ |- _ =>
        exact (Hf α Hα)
    end.
  - (* forall_l_tagged : PERMUTE — the IH's family, re-instantiated under
       the new binder ([ψ]'s wf weakens along the added rigid) *)
    subst.
    match goal with
    | IHx : forall B, _ -> _ -> _ -> _ |- _ =>
        destruct (IHx B0 eq_refl eq_refl eq_refl) as [L [m [Hlt Hfam]]]
    end.
    exists L, (S m). split; [ lia | ].
    intros α Hα.
    eapply ad_pat_sub_gv__forall_l_tagged;
      [ eassumption | eassumption | eassumption | eassumption
      | eapply a_wf_pskl_weaken;
          [ intros y c Hb; simpl_env; apply binds_app_3; exact Hb
          | eassumption ]
      | exact (Hfam α Hα) ].
  - (* forall_l_untagged : as above *)
    subst.
    match goal with
    | IHx : forall B, _ -> _ -> _ -> _ |- _ =>
        destruct (IHx B0 eq_refl eq_refl eq_refl) as [L [m [Hlt Hfam]]]
    end.
    exists L, (S m). split; [ lia | ].
    intros α Hα.
    eapply ad_pat_sub_gv__forall_l_untagged;
      [ eassumption | eassumption | eassumption | eassumption
      | eapply a_wf_pskl_weaken;
          [ intros y c Hb; simpl_env; apply binds_app_3; exact Hb
          | eassumption ]
      | exact (Hfam α Hα) ].
Qed.

(** ⭐ A2, DISCHARGED.  Whenever the counterpart is ∀-inh the row goes
    through ForallR — WHATEVER the join's last rule and whatever [P0].  So
    the ForallL rows' [guarded_pskl P0 \/ P0 = pskl_hole] premise costs
    nothing: the configuration it excludes is exactly the one this lemma
    covers, and a ∀-headed [P0] forces a ∀-inh counterpart through the FILL
    ([ad_refine_syn_f_all_inh_l_shape], §8). *)
Lemma sub_complete_all_inh_counterpart : forall n Θ0 P0 P R R' Ψ Θ κ B,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  sub_complete_concl (S n) a_sub_mode_ty mode_tc Θ0 P0 P R R' Ψ Θ κ
    (bskl_all_inh B).
Proof.
  intros n Θ0 P0 P R R' Ψ Θ κ B IH.
  intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
         Hgf.
  destruct (@sub_gv_all_inh_forall_r_family _ _ _ _ _ _ _ HDj B
              eq_refl eq_refl eq_refl)
    as [L [m [Hlt Hfam]]].
  refine (@a_sub_complete_forall_r n Θ0 P0 P R R' Ψ Θ κ B L IH _
            Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
            HwfQ Hgf).
  intros α Hα.
  eapply ad_pat_sub_gv_fuel_weaken; [ exact (Hfam α Hα) | lia ].
Qed.

(** The WLOG's TRICHOTOMY, straight off mode compatibility.  At [NM = SK]
    every compatible [P0] is a hole or an arrow; at [NM = TY] the only
    non-guarded, non-hole shape a compatible [P0] can take is a ∀ — and it can
    take it only at [M = TC], because [__ti] forces the hole and [__fn] forces
    an arrow.  That last case is exactly what §8b covers. *)
Lemma p0_wlog_trichotomy : forall NM M P0,
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  lc_pskl P0 ->
  guarded_pskl P0 \/ P0 = pskl_hole \/
  (NM = a_sub_mode_ty /\ M = mode_tc /\ exists Pb, P0 = pskl_all_syn Pb).
Proof.
  intros NM M P0 Hsk Hty Hlc; destruct NM.
  - (* TY *)
    specialize (Hty eq_refl).
    inversion Hty as [ HeqM HeqP | A HeqM HeqP | M0 Pd Pc Hc HeqM HeqP ]; subst.
    + right; left; reflexivity.
    + destruct A; cbn in *.
      * left; apply guarded_pskl__unit.
      * inversion Hlc.                       (* var_b : excluded by lc *)
      * left; apply guarded_pskl__var.
      * left; inversion Hlc; subst; apply guarded_pskl__arrow; assumption.
      * right; right; repeat split; eexists; reflexivity.
    + left; inversion Hlc; subst; apply guarded_pskl__arrow; assumption.
  - (* SK *)
    specialize (Hsk eq_refl).
    inversion Hsk as [ HeqM HeqP | HeqM HeqP | M0 Pd Pc Hc HeqM HeqP ]; subst.
    + right; left; reflexivity.
    + right; left; reflexivity.
    + left; inversion Hlc; subst; apply guarded_pskl__arrow; assumption.
Qed.

(* ===================================================================== *)
(*  §9  THE MAIN HALF's JOIN DISPATCH — DESIGN §12.1's case map            *)
(*                                                                        *)
(*  Induction on the JOIN.  Nine rows delegate to their [Qed] row lemma    *)
(*  (using the FUEL IH where the row consumes fuel); the two UnivGhostL    *)
(*  rows and [__flex_mono] preserve the fuel and are the structural IH's   *)
(*  real work.                                                            *)
(*                                                                        *)
(*  [PIH] carries the P7a escape.  It is needed only where the motive's    *)
(*  subject is a bare VARIABLE — the [__arrow] row — but the two           *)
(*  tophole-stripping rows can EXPOSE such a subject, so the hypothesis    *)
(*  must be closed under stripping.  Instantiating [PIH] with a constant   *)
(*  gives the general assembly; instantiating it with "is an arrow" makes  *)
(*  all three side conditions vacuous and yields [sub_complete_arrow] —     *)
(*  DESIGN §12.1's layer (a) — from the FUEL IH alone.                      *)
(* ===================================================================== *)

Definition sub_complete (n : nat) : Prop :=
  forall NM M Θ0 P0 P R R' Ψ Θ κ Q,
    sub_complete_concl n NM M Θ0 P0 P R R' Ψ Θ κ Q.

Definition sub_flex_complete (n : nat) (Θ0 : aenv) : Prop :=
  forall NM M α P0 R' Ψ Θ κ Q,
    sub_flex_complete_concl n NM M Θ0 nil α P0 R' Ψ Θ κ Q.

(* ⭕⭕ [uskl_forall_headed] and [main_forall] DELETED (2026-08-05).

   [main_forall] was the assembly's ONE hypothesis for most of this campaign:
   the two ForallL rows, isolated because they demanded TASK 0's [sub_shield]
   on top of the join's own premises.  §10 records why that gate is gone.
   With it gone the row lemmas take exactly the join rule's premises, §9's two
   ForallL branches apply them directly, and nothing referred to either
   definition any more.

   ⚠️ The retracted counterexamples state their conclusions against
   [main_forall]'s shape; their headers carry the statement inline.  Coq text
   at commit `4351531`. *)

(** ⭐ [sub_complete_assemble] ASSEMBLES [sub_complete_concl] from the join's
    twelve rows, by induction on the join derivation.  It is a proof engine;
    its neighbours [sub_complete] / [sub_complete_arrow] / [sub_complete_ctx_lt]
    are STATEMENTS.

    ⚙ NAMING (2026-08-05).  This family used to be [main_*] — [main_all],
    [main_arrow], [main_below], [main_join] — where "main" named nothing.  It
    meant completeness of [a_sub], as opposed to the auxiliary judgment
    [a_sub_flex] it is mutual with (def_extra.v's two boxes).  The motive was
    already called [sub_complete_concl], so the family now says the same
    thing, and each name says what RESTRICTS it: [_arrow] to arrow subjects,
    [_ctx_lt] to contexts shorter than [k], [sub_flex_complete] to the
    auxiliary judgment.

    ⭐ [PIH] is the induction's subject-shape parameter: which subjects this
    invocation is proved for.  Its three conditions read

      [PIH (∀◇R0) -> PIH R0]                       the class survives stripping
      [PIH (∀◈R0) -> PIH R0]                                 ” ”
      [PIH (uskl_var_f α) -> sub_flex_complete n Θ0]   if a BARE VARIABLE is
                                                      admitted, the auxiliary
                                                      judgment is OWED

    and restricting it is what buys the recursion: instantiated with "is an
    arrow", the two tophole-stripping rows can never expose a bare variable,
    so the third condition is vacuous, the P7a entry into [a_sub_flex] is
    unreachable, and [sub_complete_arrow] follows from the FUEL IH alone —
    which is what breaks §12's non-decreasing cycle between the two
    judgments.  Instantiated with the constant [True] it gives the general
    assembly, and the third condition hands back [sub_flex_complete]. *)
Lemma sub_complete_assemble : forall n NM M Ψ Θ R' Q,
  ad_pat_sub_gv n NM M Ψ Θ R' Q ->
  (forall n', n' < n -> sub_complete n') ->
  forall Θ0 (PIH : uskl -> Prop),
    (forall R0, PIH (uskl_tophole R0) -> PIH R0) ->
    (forall R0, PIH (uskl_topholeg R0) -> PIH R0) ->
    (forall α, PIH (uskl_var_f α) -> sub_flex_complete n Θ0) ->
    forall P0 P R κ, PIH R ->
      sub_complete_concl n NM M Θ0 P0 P R R' Ψ Θ κ Q.
Proof.
  intros n NM M Ψ Θ R' Q HD.
  induction HD as
    [ n0 NM0 Ψ0 Θa Ra Qa HΨ Hc Hss Hr
    | n0 Ψ0 Θa Ta Ba HgT HgB Hc Hr
    | n0 La Ψ0 Θa Ta Ba Hfam IHfam
    | n0 Ψ0 Θa Ra Qa HΨ HgR HgQ Hss Hc Hr
    | n0 NM0 Ψ0 Ψ1 Ψ2 Θa Ma R1 R2 Q1 Q2 Hc1 Hr1 Hsub2 IH2 HΨ
    | n0 NM0 Ψ0 Ψ' Θa Ma εa Rj ψj Qa HM HΨ1 HΨ2 Htg Hwfψ Hsub IHsub
    | n0 NM0 Ψ0 Ψ' Θa Ma Rj ψj Qa HM HΨ1 HΨ2 Htg Hwfψ Hsub IHsub
    | n0 Ψ0 Θa Ma Pa HΨ HwfPa Hmodg
    | n0 Ψ0 Θa Ma HΨ Hmodg
    | n0 Ψ0 Θa Ma Rg Qg HM Hsub IHsub
    | n0 Ψ0 Θa Ma Rg Qg HM Hsub IHsub
    | n0 NM0 Ψ0 Θa Ma αd τd Qa Hbd Hsub IHsub ];
    intros Hfuel Θ0 PIH He1 He2 He3 P0 P R κ HPIH.
  - (* __infer : the row lemma takes any [R] *)
    apply a_sub_complete_infer.
  - (* __check : the row lemma owes [guarded_pskl P0] and the wf of [B] *)
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    assert (HwfB : Θa ⨟ empty ⊢ₚₛᵃ Ba)
      by (rewrite bskl_to_pskl_pskl_to_bskl_inh in HwfQ; exact HwfQ).
    assert (HgP0 : guarded_pskl P0)
      by (eapply check_row_guarded_p0;
          [ exact Hinc | exact HwfP0 | apply Hmodty; reflexivity
          | exact HgB | exact Hrs ]).
    exact (@a_sub_complete_check n0 Θ0 P0 P R Ta Ψ0 Θa κ Ba
             HgT HgB Hc Hr HgP0 HwfB
             Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
             HwfQ Hgf).
  - (* __forall_r : the fuel IH plus the row's cofinite family *)
    exact (@a_sub_complete_forall_r n0 Θ0 P0 P R Ta Ψ0 Θa κ Ba La
             (Hfuel n0 ltac:(lia)) Hfam).
  - (* __univ_ghost_r *)
    exact (@a_sub_complete_univ_ghost_r n0 Θ0 P0 P R Ra Ψ0 Θa κ Qa
             HgR HgQ Hc Hr).
  - (* __arrow : the ONE row where [R]'s shape is not forced — an arrow, or a
       bare variable whose IMAGE is the arrow (the entry into P7a) *)
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    assert (Hsh : (exists Rx Ry, R = uskl_arrow Rx Ry)
                  \/ (exists γ, R = uskl_var_f γ)).
    { destruct (@a_uskl_tyequiv_arrow_l_inv Θa R1 R2 _ Hwfth Hslack)
        as [[X1 [X2 HX]] | [γ HX]].
      - destruct (@msubst_uskl_syn_arrow_inv κ R X1 X2 HX)
          as [[Rx [Ry [HR _]]] | [γ HR]];
          [ left; exists Rx, Ry; exact HR | right; exists γ; exact HR ].
      - destruct (@msubst_uskl_syn_var_inv κ R γ HX) as [γ0 HR].
        right; exists γ0; exact HR. }
    destruct Hsh as [[Rx [Ry HR]] | [γ HR]]; subst R.
    + exact (@a_sub_complete_arrow n0 NM0 Ma Θ0 P0 P Rx Ry R1 R2 Ψ0 Θa κ
               Q1 Q2 (Hfuel n0 ltac:(lia))
               Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
               HwfQ Hgf).
    + (* a bare variable: RIGID ⟹ refuted (§4); FLEXIBLE ⟹ into P7a *)
      cbn in HeqR. subst P.
      assert (Hbt : a_binds_tvar γ Θ0)
        by (inversion HwfP as [ | ? ? ? Hor | | | | ]; subst;
            destruct Hor as [Hemp | Hb];
            [ exfalso; clear - Hemp; fsetdec | exact Hb ]).
      destruct Hbt as [Hrig | Hfl].
      * exfalso.
        eapply slack_arrow_rigid_absurd;
          [ exact Hwf0 | exact Hwfth | exact Hinc | exact Hrig | exact Hslack ].
      * assert (Hfγ : a_flex_tvar Θ0 γ)
          by (destruct Hfl as [Hb | [τ0 Hb]];
              [ left; exact Hb | right; exists τ0; exact Hb ]).
        destruct (He3 γ HPIH NM0 Ma γ P0 (uskl_arrow R1 R2) Ψ0 Θa κ
                    (bskl_arrow Q1 Q2)
                    a_decls__nil ltac:(simpl; clear; fsetdec)
                    Hwf0 Hwfth HwfP0 Hfγ Hmodsk Hmodty Hinc Hslack HDj Hrs
                    HwfQ)
          as [P1 [Θ1 [Hrun Hopt]]].
        exists P1, Θ1. split;
          [ apply a_sub__flex_mono; exact Hrun | exact Hopt ].
  - (* __forall_l_tagged : [R] is the SAME ∀ — the residual (§10), but only
       after §8b has taken the WLOG's escaping shape off its hands *)
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    (* ⭐⭐⭐ (2026-08-05) THE ROW LEMMA APPLIES DIRECTLY.  It used to owe
       TASK 0's [sub_shield] on top of the join's own premises, which is why
       this branch had to defer to the [main_forall] hypothesis.  That gate is
       gone ([sub_shield_empty]), so the row's premises are EXACTLY the join
       rule's — [HM], [HΨ1], [HΨ2], [Htg], [Hwfψ], [Hsub] — plus the fuel IH
       and the WLOG the trichotomy supplies. *)
    assert (Hhd : exists R0, R = uskl_all_etag εa R0).
    { destruct (@a_uskl_tyequiv_all_etag_l_inv Θa εa Rj _ Hslack) as [X0 HX].
      destruct (@msubst_uskl_syn_all_etag_inv κ R εa X0 HX) as [R0 [HR _]].
      exists R0; exact HR. }
    destruct Hhd as [R0 HR0]. subst R.
    destruct (p0_wlog_trichotomy Hmodsk Hmodty (a_wf_pskl_lc HwfP0))
      as [Hwlog | [Hwlog | [HeqNM [HeqM [Pb HeqP0]]]]].
    + exact (@a_sub_complete_forall_l_tagged n0 NM0 Ma Θ0 P0 P R0 Rj Ψ0 Θa κ
               Qa εa Ψ' ψj (Hfuel n0 ltac:(lia)) HM HΨ1 HΨ2 Htg Hwfψ Hsub
               (or_introl Hwlog)
               Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
               HwfQ Hgf).
    + exact (@a_sub_complete_forall_l_tagged n0 NM0 Ma Θ0 P0 P R0 Rj Ψ0 Θa κ
               Qa εa Ψ' ψj (Hfuel n0 ltac:(lia)) HM HΨ1 HΨ2 Htg Hwfψ Hsub
               (or_intror Hwlog)
               Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
               HwfQ Hgf).
    + (* ⭐ the WLOG's escaping shape: a ∀-headed [P0] forces a ∀-inh
         counterpart through the FILL, and §8b sends the row through ForallR *)
      subst NM0 Ma P0.
      cbn in Hrs.
      destruct (ad_refine_syn_f_all_inh_l_shape Hrs) as [B HB]. subst Qa.
      exact (@sub_complete_all_inh_counterpart n0 Θ0 (pskl_all_syn Pb) P
               (uskl_all_etag εa R0)
               (uskl_all_etag εa Rj) Ψ0 Θa κ B (Hfuel n0 ltac:(lia))
               Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
               HwfQ Hgf).
  - (* __forall_l_untagged : as above *)
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    (* ⭐⭐⭐ as the tagged row above: TASK 0's gate is gone, so the row lemma
       takes exactly the join rule's own premises. *)
    assert (Hhd : exists R0, R = uskl_all_syn R0).
    { destruct (@a_uskl_tyequiv_all_syn_l_inv Θa Rj _ Hslack) as [X0 HX].
      destruct (@msubst_uskl_syn_all_syn_inv_mono Θ0 κ Θa R X0 Hinc HX)
        as [R0 [HR _]].
      exists R0; exact HR. }
    destruct Hhd as [R0 HR0]. subst R.
    destruct (p0_wlog_trichotomy Hmodsk Hmodty (a_wf_pskl_lc HwfP0))
      as [Hwlog | [Hwlog | [HeqNM [HeqM [Pb HeqP0]]]]].
    + exact (@a_sub_complete_forall_l_untagged n0 NM0 Ma Θ0 P0 P R0 Rj Ψ0 Θa κ
               Qa Ψ' ψj (Hfuel n0 ltac:(lia)) HM HΨ1 HΨ2 Htg Hwfψ Hsub
               (or_introl Hwlog)
               Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
               HwfQ Hgf).
    + exact (@a_sub_complete_forall_l_untagged n0 NM0 Ma Θ0 P0 P R0 Rj Ψ0 Θa κ
               Qa Ψ' ψj (Hfuel n0 ltac:(lia)) HM HΨ1 HΨ2 Htg Hwfψ Hsub
               (or_intror Hwlog)
               Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
               HwfQ Hgf).
    + subst NM0 Ma P0.
      cbn in Hrs.
      destruct (ad_refine_syn_f_all_inh_l_shape Hrs) as [B HB]. subst Qa.
      exact (@sub_complete_all_inh_counterpart n0 Θ0 (pskl_all_syn Pb) P
               (uskl_all_syn R0)
               (uskl_all_syn Rj) Ψ0 Θa κ B (Hfuel n0 ltac:(lia))
               Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
               HwfQ Hgf).
  - (* __ghost : the row lemma takes [R'] directly *)
    exact (@a_sub_complete_ghost n0 Ma Θ0 P0 P R uskl_hole Ψ0 Θa κ
             (pskl_to_bskl_inh Pa) eq_refl).
  - (* __ghostg *)
    exact (@a_sub_complete_ghostg n0 Ma Θ0 P0 P R uskl_holeg Ψ0 Θa κ
             bskl_hole eq_refl).
  - (* __univ_ghost_l : NO row lemma — strip [∀◇] and recurse (same fuel) *)
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    destruct (@a_uskl_tyequiv_tophole_l_inv Θa Rg _ Hslack)
      as [X [HX Hslack0]].
    destruct (@msubst_uskl_syn_tophole_inv κ R X HX) as [R00 [HR HmX]].
    subst R. cbn in HeqR. subst P.
    rewrite <- HmX in Hslack0.
    assert (HwfP' : Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ R00 ⌋ˢ)
      by (inversion HwfP; subst; assumption).
    (* the row is SK-only, so the motive's TY ghost-freeness is VACUOUS *)
    assert (Hgf0 : a_sub_mode_sk = a_sub_mode_ty -> uskl_ghost_free Rg)
      by (intro Habs; discriminate Habs).
    destruct (IHsub Hfuel Θ0 PIH He1 He2 He3 P0 (⌊ R00 ⌋ˢ) R00 κ
                (He1 R00 HPIH)
                Hwf0 Hwfth HwfP0 HwfP' Hmodsk Hmodty eq_refl Hinc Hslack0
                Hsub Hrs HwfQ Hgf0)
      as [P1 [Θ1 [Hrun Hopt]]].
    exists P1, Θ1. split;
      [ apply a_sub__univ_ghost_l; [ exact HM | exact Hrun ] | exact Hopt ].
  - (* __univ_ghost_lg : ⌊∀◈ R⌋ˢ IS ∀◇⌊R⌋ˢ, so the SAME rule applies *)
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    destruct (@a_uskl_tyequiv_topholeg_l_inv Θa Rg _ Hslack)
      as [X [HX Hslack0]].
    destruct (@msubst_uskl_syn_topholeg_inv κ R X HX) as [R00 [HR HmX]].
    subst R. cbn in HeqR. subst P.
    rewrite <- HmX in Hslack0.
    assert (HwfP' : Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ R00 ⌋ˢ)
      by (inversion HwfP; subst; assumption).
    (* SK-only, as above *)
    assert (Hgf0 : a_sub_mode_sk = a_sub_mode_ty -> uskl_ghost_free Rg)
      by (intro Habs; discriminate Habs).
    destruct (IHsub Hfuel Θ0 PIH He1 He2 He3 P0 (⌊ R00 ⌋ˢ) R00 κ
                (He2 R00 HPIH)
                Hwf0 Hwfth HwfP0 HwfP' Hmodsk Hmodty eq_refl Hinc Hslack0
                Hsub Hrs HwfQ Hgf0)
      as [P1 [Θ1 [Hrun Hopt]]].
    exists P1, Θ1. split;
      [ apply a_sub__univ_ghost_l; [ exact HM | exact Hrun ] | exact Hopt ].
  - (* __flex_mono : a pure PEEL — chase the Θ-definition on the JOIN's side
       and re-establish the ≡ᵘ slack; [R] is untouched *)
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    assert (Hslack' : Θa ⊢ (ptyp_to_uskl_syn τd) ≡ᵘ (msubst_uskl_syn κ R)).
    { eapply a_uskl_tyequiv_trans;
        [ apply flex_def_paint_tyequiv; [ exact Hbd | exact Hwfth ]
        | exact Hslack ]. }
    (* the peeled subject IS a monotype painting, ghost-free outright *)
    assert (Hgfd : NM0 = a_sub_mode_ty ->
              uskl_ghost_free (ptyp_to_uskl_syn τd))
      by (intros _; apply mono_ptyp_to_uskl_syn_ghost_free;
          eapply a_wf_aenv_binds_def_mono; [ exact Hwfth | exact Hbd ]).
    exact (IHsub Hfuel Θ0 PIH He1 He2 He3 P0 P R κ HPIH
             Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack'
             Hsub Hrs HwfQ Hgfd).
Qed.

(** ⭐ DESIGN §12.1's LAYER (a).  Instantiating [PIH] with "is an arrow" makes
    all three escape side conditions VACUOUS: an arrow is neither a [∀◇] nor a
    [∀◈] nor a variable, so the two tophole-stripping rows can never expose a
    variable subject and the P7a entry is unreachable.  So the main half at an
    ARROW subject follows from the FUEL IH alone — no P7a, no induction on the
    context.  That is exactly what [a_sub_flex_complete_solve] needs, and it
    is what breaks §12's non-decreasing main ⇄ flex cycle. *)
Lemma sub_complete_arrow_holds : forall n,
  (forall n', n' < n -> sub_complete n') ->
  sub_complete_arrow n.
Proof.
  intros n Hfuel NM M Θ0 P0 P Ra Rb R' Ψ Θ κ Q.
  intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
         Hgf.
  exact (@sub_complete_assemble n NM M Ψ Θ R' Q HDj Hfuel Θ0
           (fun R0 => exists Rx Ry, R0 = uskl_arrow Rx Ry)
           ltac:(intros R0 [Rx [Ry HH]]; discriminate HH)
           ltac:(intros R0 [Rx [Ry HH]]; discriminate HH)
           ltac:(intros γ [Rx [Ry HH]]; discriminate HH)
           P0 P (uskl_arrow Ra Rb) κ
           (ex_intro _ Ra (ex_intro _ Rb eq_refl))
           Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf).
Qed.

(* ===================================================================== *)
(* ===================================================================== *)
(*  §10  WHAT THE ASSEMBLY OWES — ⭐⭐⭐ NOTHING (2026-08-05)                *)
(*                                                                        *)
(*  The three layers of DESIGN §12.1 are in the tree and all [Qed]:        *)
(*                                                                        *)
(*    (a) [sub_complete_arrow_holds] — the main half at an ARROW subject, from the *)
(*        FUEL IH alone.  This is what breaks §12's non-decreasing cycle.  *)
(*    (b) [sub_flex_complete_holds]        — the flex half, structural on [Θ0] with [Ξ]  *)
(*        generalized and the total context length bounded.                *)
(*    (c) [sub_complete_assemble]        — the main half's twelve-row join dispatch.   *)
(*                                                                        *)
(*  ⭐⭐⭐ AND THE RESIDUAL IS DISCHARGED.  [main_forall] — the two ForallL   *)
(*  rows — was the assembly's ONE hypothesis for a year of this campaign.  *)
(*  Its single unsupplied premise was TASK 0's [sub_shield]                *)
(*  (RESIDUAL A1), for which no general supply route existed once [P0]     *)
(*  carried a ∀ below its head.  Under the authors' repaired [SolE-FlexR]  *)
(*  that gate is GONE, for a reason that has nothing to do with supplying  *)
(*  it: P6-Cv stopped consuming [flex_apart], so P6-Sv stopped needing     *)
(*  [flex_apart_walk], so [sub_shield] lost its guess-descending conjunct  *)
(*  — and what remains is Δρ-CONSTANT, hence at the Δρ = ∅ these rows      *)
(*  instantiate it at, unconditionally TRUE ([sub_shield_empty],           *)
(*  prop_look_complete_sub_cstr.v).  P6-L discharges it internally and no  *)
(*  longer takes it; §9's two ForallL branches now apply their row lemmas  *)
(*  DIRECTLY, on exactly the join rule's own premises.                     *)
(*                                                                        *)
(*  ⭕ The other former components, for the record:                         *)
(*    · RESIDUAL A2 (the WLOG [guarded P0 ∨ P0 = □]) — CLOSED 2026-08-03,  *)
(*      §8b: [p0_wlog_trichotomy] leaves exactly one escaping shape (a     *)
(*      ∀-headed [P0] at NM = TY, M = TC) and [sub_complete_all_inh_counterpart]   *)
(*      sends it through ForallR.  That is the mechanical content of the   *)
(*      paper's one-sentence WLOG, subtyping-proofs.tex:3385.              *)
(*    · The TY-only ghost-freeness of the join's subject — CLOSED, it sits *)
(*      ON THE MOTIVE ([sub_complete_concl]'s last premise) and            *)
(*      [a_sub_complete_thm] carries it as a paper-facing EXTERNAL side    *)
(*      condition (docs/WF-SIDE-CONDITIONS.md).                            *)
(*    · RESIDUAL B (the TERM-VARIABLE gap of §6) — CLOSED 2026-08-03:      *)
(*      both the rules and P7a's two completeness rows are in the tree.    *)
(*                                                                        *)
(*  ⚠️ HISTORY, so the retraction is not lost.  This block used to record   *)
(*  that [main_forall] is FALSE (cex/probe_double_occ_run.v,               *)
(*  [probe_main_forall_false]) and that the two flagships were therefore   *)
(*  VACUOUS.  That refutation is RETRACTED: it ran through the double-     *)
(*  occurrence configuration, where the OLD [SolE-FlexR] discarded the     *)
(*  accumulated pattern so no [a_sub] run existed.  The repaired row       *)
(*  returns [guess^TY(P)], the run exists (cex/probe_flexr_repair.v), and  *)
(*  the shield at that very configuration now HOLDS                        *)
(*  ([p7_sub_shield_double_occ_holds]).  Both flagships are UNCONDITIONAL  *)
(*  and are indexed in README.v.                                           *)
(* ===================================================================== *)


(* ===================================================================== *)
(*  §12  THE ASSEMBLY — [a_sub_complete_bundle], UNCONDITIONAL            *)
(*                                                                        *)
(*  DESIGN §12.1's three layers, glued: strong induction on the FUEL, and  *)
(*  inside it strong induction on the CONTEXT LENGTH.                      *)
(*                                                                        *)
(*    · [sub_complete_arrow_holds]  from the fuel IH alone                         *)
(*    · [sub_complete_ctx_lt n k]    the main half at contexts SHORTER than k, by   *)
(*                          the length IH                                  *)
(*    · [sub_flex_complete_holds]         from the two above                             *)
(*    · [sub_complete_assemble]         from the fuel IH and [sub_flex_complete_holds] at [Ξ = ·]    *)
(*                                                                        *)
(*  [sub_complete_assemble]'s [PIH] is instantiated with the constant [fun _ => True]: *)
(*  its three closure conditions become trivial and the third hands back   *)
(*  [sub_flex_complete n Θ0], which is [sub_flex_complete_holds] at [Ξ = nil].                   *)
(* ===================================================================== *)

(** ⭐⭐⭐ UNCONDITIONAL (2026-08-05).  This used to take
    [forall n, main_forall n] — the two ForallL rows, whose one unsupplied
    premise was TASK 0's [sub_shield].  That gate is gone: under the authors'
    repaired [SolE-FlexR] the shield lost its guess-descending conjunct and,
    at the Δρ = ∅ these rows instantiate it at, is unconditionally true
    ([sub_shield_empty]).  So §9's two ForallL branches apply their row
    lemmas DIRECTLY and the hypothesis has no consumer left. *)
Theorem a_sub_complete_bundle_holds : a_sub_complete_bundle.
Proof.
  intros n.
  induction n as [n IHfuel] using lt_wf_ind.
  assert (Hfuel : forall n', n' < n -> sub_complete n')
    by (intros n' Hn'; exact (proj1 (IHfuel n' Hn'))).
  assert (Harrow : sub_complete_arrow n)
    by (apply sub_complete_arrow_holds; exact Hfuel).
  (* the main half at every context, by strong induction on the LENGTH *)
  assert (Hbelow : forall k, sub_complete_ctx_lt n k).
  { intro k. induction k as [k IHk] using lt_wf_ind.
    intros NM M Θ0 P0 P R R' Ψ Θ κ Q Hlen.
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    refine (@sub_complete_assemble n NM M Ψ Θ R' Q HDj Hfuel Θ0
              (fun _ => True) _ _ _ P0 P R κ I
              Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
              HwfQ Hgf);
      [ intros; exact I | intros; exact I | ].
    intros γ _ NM' M' α' P0' R'' Ψ' Θ' κ' Q'.
    apply (@sub_flex_complete_holds n (length Θ0) Harrow
             (IHk (length Θ0) Hlen) NM' M' Θ0 nil α' P0' R'' Ψ' Θ' κ' Q').
    simpl. lia. }
  split.
  - intros NM M Θ0 P0 P R R' Ψ Θ κ Q.
    apply (Hbelow (S (length Θ0)) NM M Θ0 P0 P R R' Ψ Θ κ Q). lia.
  - intros NM M Θ0 Ξ α P0 R' Ψ Θ κ Q.
    apply (@sub_flex_complete_holds n (length Ξ + length Θ0) Harrow
             (Hbelow (length Ξ + length Θ0))
             NM M Θ0 Ξ α P0 R' Ψ Θ κ Q). lia.
Qed.

(** thm:complete-subtyping (algorithmic.tex:1446) — the P7c instance of the
    bundle's main half: [Ψ := ∅] and [R := ⌈P⌉ᵘ], the unresolved skeleton
    the top-level problem starts from.  The join is kept at the ≡ᵘ-slack
    subject the motive carries; the paper's own form is the REFLEXIVE
    instance [R' := κ⌈P⌉ᵘ], so this statement is the weaker-premise one.

    ⭐⭐⭐ UNCONDITIONAL (2026-08-05).  It used to inherit
    [forall n, main_forall n], whose one unsupplied premise was TASK 0's
    [sub_shield]; the authors' repaired [SolE-FlexR] retired that gate
    ([sub_shield_empty]).  The premises below are the paper's own plus the
    EXTERNAL wf side conditions registered in docs/WF-SIDE-CONDITIONS.md. *)
Theorem a_sub_complete_thm :
  forall n NM M Θ0 P0 P R' Θ κ Q,
    a_wf_aenv Θ0 -> a_wf_aenv Θ ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
    (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
    κ ∷ Θ0 ⊑ Θ ->
    Θ ⊢ R' ≡ᵘ (msubst_uskl_syn κ (pskl_to_uskl P)) ->
    ad_pat_sub_gv n NM M empty Θ R' Q ->
    ad_refine_syn_f empty Θ empty (pskl_to_bskl_inh (msubst_pskl κ P0)) Q ->
    Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
    (* the subject's TY ghost-freeness — the motive's EXTERNAL side
       condition (WF-SIDE-CONDITIONS.md); at the paper's own reflexive
       instance [R' := κ⌈P⌉ᵘ] it is the ghost-freeness of the input [P] *)
    (NM = a_sub_mode_ty -> uskl_ghost_free R') ->
    exists P1 Θ1,
      a_sub NM M P0 Θ0 P P1 Θ1 /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           Θ ⨟ empty ⊢ₚᵣᵃ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Q)).
Proof.
  intros n NM M Θ0 P0 P R' Θ κ Q
    Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty Hinc Hslack HDj Hrs HwfQ Hgf.
  exact (proj1 (a_sub_complete_bundle_holds n)
           NM M Θ0 P0 P (pskl_to_uskl P) R' empty Θ κ Q
           Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty
           (uskl_to_pskl_pskl_to_uskl P) Hinc Hslack HDj Hrs HwfQ Hgf).
Qed.

Print Assumptions sub_complete_assemble.
Print Assumptions sub_complete_arrow_holds.
Print Assumptions sub_flex_complete_holds.
Print Assumptions check_row_guarded_p0.
Print Assumptions sub_flex_rigid_head_absurd.
Print Assumptions sub_gv_all_inh_forall_r_family.
Print Assumptions sub_complete_all_inh_counterpart.
Print Assumptions a_sub_complete_bundle_holds.
Print Assumptions a_sub_complete_thm.
