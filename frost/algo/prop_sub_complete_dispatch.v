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

      §3  [main_arrow_subject]  — the main half at an ARROW subject, from the
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
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.prop_basic.

Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_sub_msubst_equiv.
Require Import src.frost.algo.prop_sub_complete_thm.

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
(*    (a) [main_arrow_subject] — the main half at an ARROW subject, from   *)
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
(*  §6  ⚠️⚠️ A PAPER GAP THE ASSEMBLY EXPOSES — the flexible SUBTYPING     *)
(*      walk has NO rule for a TERM-VARIABLE head                         *)
(*                                                                        *)
(*  The paper's algorithmic contexts contain term entries [x : P]          *)
(*  (algorithmic.tex:60-66), and the ASSIGNMENT walk has a rule for them   *)
(*  — [Assign-SkipTmVar], full-algo-spec.tex:1791, mechanized as           *)
(*  [a_assign__skip_tm_var] / [a_assign__skip_tm_skl].  The SUBTYPING walk *)
(*  (fig:alg-subtyping's second box, full-algo-spec.tex:883-912) has FIVE  *)
(*  rules — Flex-Solve / Assign / Depend / Skip / SkipRigid — and NONE     *)
(*  of them matches a term entry, so the walk is STUCK there.  The         *)
(*  reference implementation agrees with the paper and therefore with the  *)
(*  gap: [assign] has [U-Assign-SkipTmVar] for [BVar _ | Marker | Lock _]  *)
(*  (type.ml:386-390) while [sub_flex] falls through to                    *)
(*  [Errors.type_mismatch] (type.ml:1047-1050).                            *)
(*                                                                        *)
(*  Nothing in [thm:complete-subtyping]'s problem definition excludes the  *)
(*  configuration: [a_wf_aenv] happily puts a term entry ABOVE a flexible  *)
(*  variable.  So the theorem is not provable for the rule set as printed; *)
(*  the repair is to add [Flex-SkipTmVar] in the paper's own idiom, exactly *)
(*  mirroring the twin walk's.  That is a rule change with a tree-wide     *)
(*  blast radius ([a_subtag_flex], the decoration and equivariance mutual  *)
(*  inductions, and two new P7a rows carrying [Flex-SkipRigid]'s whole     *)
(*  ⇓-truncation apparatus), so it is left to the authors' decision and    *)
(*  the assembly below takes the configuration as an EXPLICIT premise.     *)
(*  [a_sub_flex_walkable] is that premise, and it is the ONE place the     *)
(*  development departs from the paper's statement.                        *)
(* ===================================================================== *)

Definition a_sub_flex_walkable (Θ0 : aenv) : Prop :=
  forall x b, binds x b Θ0 ->
    b = abind_tvar \/ b = abind_flex_mono \/
    (exists τ, b = abind_flex_mono_def τ).

Lemma a_sub_flex_walkable_tail : forall x b Θ0,
  a_sub_flex_walkable ((x ~ b) ++ Θ0) -> a_sub_flex_walkable Θ0.
Proof.
  intros x b Θ0 H y c Hb. apply (H y c). unfold binds in *; simpl; right; exact Hb.
Qed.

Lemma a_sub_flex_walkable_head : forall x b Θ0,
  a_sub_flex_walkable ((x ~ b) ++ Θ0) ->
  b = abind_tvar \/ b = abind_flex_mono \/ (exists τ, b = abind_flex_mono_def τ).
Proof.
  intros x b Θ0 H. apply (H x b). unfold binds; simpl; left; reflexivity.
Qed.

(* ===================================================================== *)
(*  §7  THE FLEX HALF (P7a's assembly) — DESIGN §12.1's layer (b)          *)
(*                                                                        *)
(*  Structural induction on [Θ0] with the suffix [Ξ] GENERALIZED and the   *)
(*  TOTAL context length bounded by [k]: Flex-Depend keeps the total and   *)
(*  shrinks [Θ0] (so it is the structural IH), Flex-Skip / Flex-SkipRigid  *)
(*  shrink both, Flex-Assign CONSUMES the definition and re-enters the     *)
(*  main half one entry SHORTER, and Flex-Solve re-enters it at an ARROW   *)
(*  subject over a LARGER context — which is why [main_arrow] is a         *)
(*  separate hypothesis, discharged from the FUEL IH alone.                *)
(* ===================================================================== *)

Definition main_arrow (n : nat) : Prop :=
  forall NM M Θ0 P0 P Ra Rb R' Ψ Θ κ Q,
    sub_complete_concl n NM M Θ0 P0 P (uskl_arrow Ra Rb) R' Ψ Θ κ Q.

Definition main_below (n k : nat) : Prop :=
  forall NM M Θ0 P0 P R R' Ψ Θ κ Q,
    length Θ0 < k ->
    sub_complete_concl n NM M Θ0 P0 P R R' Ψ Θ κ Q.

Lemma flex_step : forall n k,
  main_arrow n ->
  main_below n k ->
  forall NM M Θ0 Ξ α P0 R' Ψ Θ κ Q,
    a_sub_flex_walkable Θ0 ->
    length Ξ + length Θ0 <= k ->
    sub_flex_complete_concl n NM M Θ0 Ξ α P0 R' Ψ Θ κ Q.
Proof.
  intros n k Harrow Hmain NM M Θ0.
  induction Θ0 as [ | [β b] Θ0' IHΘ0 ];
    intros Ξ α P0 R' Ψ Θ κ Q Hwalk Hlen.
  - (* the empty context: the subject cannot be flexible there *)
    unfold sub_flex_complete_concl.
    intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
           HwfQ.
    exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb.
  - (* the head decides the row *)
    assert (Hwalk' : a_sub_flex_walkable Θ0')
      by (eapply a_sub_flex_walkable_tail; exact Hwalk).
    assert (IH' : forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
              length Ξ' <= S (length Ξ) ->
              sub_flex_complete_concl n NM M Θ0' Ξ' α' P0' R'' Ψ' Θ'' κ' Q').
    { intros Ξ' α' P0' R'' Ψ' Θ'' κ' Q' HlenΞ.
      apply IHΘ0; [ exact Hwalk' | simpl in Hlen; lia ]. }
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
    + (* ⚠️ β is a TERM variable — see §6; NO [a_sub_flex] rule applies *)
      exfalso.
      destruct (a_sub_flex_walkable_head Hwalk) as [Hc | [Hc | [τ Hc]]];
        discriminate Hc.
    + (* ⚠️ β is a TERM variable (skeleton entry) — see §6 *)
      exfalso.
      destruct (a_sub_flex_walkable_head Hwalk) as [Hc | [Hc | [τ Hc]]];
        discriminate Hc.
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
Print Assumptions flex_step.
