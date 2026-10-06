(** PROBE (2026-08-17): FEASIBILITY of §8c.12 route (B) — at the exact
    configuration that refuted §8c.10's first scoping, the RUNNER's answer
    is ⊑-below the alias answer in the tree's EXISTING [a_inc].
    The reverse witness below (2026-10-06) shows that this comparison is
    NON-STRICT: the two concrete answers are equigeneral.
    (docs/HANDOFF-extractable-algo-encoding.md §8c.12.)

    §8c.10b refuted the renaming-shaped output relation with
    `cex/probe_consis_ghost_flex.v`: at (pattern ◇, subject α̂) BOTH
    [U-GhostR] and [U-FlexL] fire, the runner takes GhostR, and the two
    output CONTEXTS differ by a solution rather than by a renaming —

        runner      (U-GhostR)   α̂                        (untouched)
        derivation  (U-FlexL)    α̂ := β̂, β̂               (α̂ SOLVED)

    — so the divergence is information-free but is NOT a renaming, and the
    note recorded that lifting the level off [pskl_no_hole] needs a
    generalization argument.  This probe pins the direction of that
    argument with the metasubstitution [β̂/α̂].  For fresh β, the reverse
    witness [α̂/α̂, α̂/β̂] also exists, and the round trip fixes α.
    This is a fact about these concrete contexts, not a general transport
    theorem for subsequent consistency derivations.

    ⭐⭐ AND NO NEW RELATION IS OWED.  [ext_algo] shares [aenv] with [algo/],
    so [a_inc] (algo/def_meta.v:213, the paper's fig:information-increase)
    applies to a threaded run's contexts verbatim — as does its metatheory,
    which is where the route's cost estimate was wrong.  Already Qed in the
    tree and directly usable:

      a_inc_compose      prop_compose.v:778   ζ ∷ Θ1 ⊑ Θ  ⇒  ζ∘κ ∷ Θ0 ⊑ Θ
                                              (GENERAL, not identity-only —
                                               this is what U-Arrow's chain
                                               composes with)
      a_inc_trans        prop_inc.v:491       the identity shorthand
      a_isub_refl        prop_basic.v:222     Θ ⊴ Θ at a well-formed Θ
      a_isub_cons_*      prop_basic.v:109-166 the four entry-extension rows

    What §8c.12 still owes is the trio's ⊑-MONOTONICITY itself — the runner
    run at a more general context succeeds and stays more general — which is
    new, and is the induction. *)

From Coq Require Import Lists.List.
From Metalib Require Import Metatheory.

From src Require Import frost.notations.
From src Require Import frost.def_shapes.
From src Require Import frost.algo.def_rules.
From src Require Import frost.algo.def_meta.

Open Scope frost_a_scope.

(** The two contexts of `cex/probe_consis_ghost_flex.v`, verbatim. *)
Definition gf_ctx (α : atom) : aenv := (α ~ abind_flex_mono) ++ nil.
Definition gf_ctx_solved (α β : atom) : aenv :=
  (α ~ abind_flex_mono_def (ptyp_var_f β)) ++ (β ~ abind_flex_mono) ++ nil.

(** The runner's output (U-GhostR: α̂ untouched) is ⊑-below the derivation's
    (U-FlexL: α̂ := β̂), witnessed by κ = [β̂/α̂]. *)
Lemma probe_inc_runner_more_general : forall α β,
  ((α, ptyp_var_f β) :: nil) ∷ (gf_ctx α) ⊑ (gf_ctx_solved α β).
Proof.
  intros. unfold gf_ctx, gf_ctx_solved.
  apply a_inc__flex.
  - apply a_inc__empty.
    apply a_suffix__cons; [ | apply a_suffix_binding__flex_mono_def ].
    apply a_suffix__cons; [ | apply a_suffix_binding__flex_mono ].
    apply a_suffix__nil.
  - (* β̂ is flexible in the solved context, so the witness is well-formed *)
    apply a_wf_ptyp__var. right. left. simpl. auto.
  - apply mono_ptyp__var.
Qed.

(** The alias can be eliminated without adding information.  Freshness
    ensures that substituting for β does not first match the α entry. *)
Lemma probe_inc_alias_to_runner : forall α β, α <> β ->
  ((α, ptyp_var_f α) :: (β, ptyp_var_f α) :: nil)
    ∷ gf_ctx_solved α β ⊑ gf_ctx α.
Proof.
  intros α β Hneq. unfold gf_ctx_solved, gf_ctx.
  apply a_inc__flex_def.
  - apply a_inc__flex.
    + apply a_inc__empty. apply a_suffix__cons; constructor.
    + apply a_wf_ptyp__var. right. left. unfold binds; simpl; auto.
    + constructor.
  - apply a_wf_ptyp__var. right. left. unfold binds; simpl; auto.
  - constructor.
  - simpl. destruct (β == β); [ | contradiction ].
    apply a_tyequiv__refl. constructor.
Qed.

(** The forward and reverse witnesses preserve the original variable. *)
Lemma probe_inc_alias_round_trip : forall α β, α <> β ->
  msubst_ptyp ((α, ptyp_var_f α) :: (β, ptyp_var_f α) :: nil)
    (msubst_ptyp ((α, ptyp_var_f β) :: nil) (ptyp_var_f α)) = ptyp_var_f α.
Proof.
  intros α β Hneq. cbv [msubst_ptyp msubst_lookup].
  repeat match goal with
  | |- context [if ?d then _ else _] => destruct d; try congruence
  end.
Qed.

Print Assumptions probe_inc_runner_more_general.
Print Assumptions probe_inc_alias_to_runner.
Print Assumptions probe_inc_alias_round_trip.
