(** THE ALIAS LAYER — kit for lifting the consistency runner's completeness
    off its hole-free restriction along the PRE-NORMALISATION route
    (docs/HANDOFF-close-consis-unrestricted.md §5 (R1)).

    ⭐ THE SHAPE OF THE CAMPAIGN.  At the two divergent cells —
    (pattern [◇], subject [α̂]) and its mirror — the runner answers with its
    context UNCHANGED ([U-GhostR] / [U-Ghost]) while a derivation may
    instead run the assignment walk [Θ ⊲[nil] α ≔ ◇ ⊣ Θ1] ([U-FlexL] /
    [U-FlexR]).  cex/probe_pat_presents_hole_flex.v shows the cells are
    REACHED by skeleton inference, so completeness must RELATE the two
    outcomes rather than exclude them.  This file supplies the two ends of
    that relation:

    §1  the walk's output is EXACTLY an alias insertion — either an inner
        [U-GhostR] stops the walk with everything unchanged, or the chase
        ends at some undefined flexible [γ̂] and [Assign-SolveM] replaces
        its entry by [γ̂ ≔ ε̂, ε̂] with [ε̂ := guess^TY(◇)] fresh
        ([e_assign_hole_out]).  ⚙ The payload [◇] has NO free variables,
        so [Assign-Depend] never fires and the pending block never grows —
        which is why the insertion is POSITIONAL here even though walks in
        general migrate entries (cex/probe_assign_migrates.v).
        ⚠️ The walk may CHASE aliases: [a_flex_tvar] admits DEFINED
        targets, so [Assign-Assign] can fire at the target itself
        ([β = α]) and re-enter at the definition's image.  The insertion
        therefore lands at the END of the chase, not necessarily at [α] —
        the lemma existentially quantifies the solved variable.

    §2  [collapse1] — the alias-collapse: drop the alias entry
        [γ ≔ ε̂] and rename [ε̂] back to [γ] everywhere (keys and
        payloads).  [collapse1_insert] computes it on §1's insertion shape:
        collapsing recovers the input context, which is the runner's
        answer.  ⚙ [rename_aenv] is the DIRECTED rename, kept by
        prop_swap.v's own header "where a proof genuinely needs the
        one-way form": a collapse MERGES [ε̂] into [γ] — it is not
        injective on {γ, ε̂} — so no transposition can express it.

    ⛔ NOT here yet (the campaign's step 3, see the handover): the
    transport of a derivation across [collapse1] — that is the induction
    the completeness motive's [U-Arrow] threading will consume. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.prop_consis_inc.

Set Implicit Arguments.

Open Scope frost_a_scope.
Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  THE ◇-PAYLOAD WALK IS AN ALIAS INSERTION                          *)
(* ===================================================================== *)

(** The output shape shared by the walk and its consis re-entries: nothing
    moved, or one undefined flexible [γ̂] got solved to a fresh alias. *)
Definition alias_insert_out (S0 : supply) (Θ : aenv)
    (S1 : supply) (Θ1 : aenv) : Prop :=
  (S1 = S0 /\ Θ1 = Θ) \/
  (exists γ ε Θa Θb,
      ε `notin` S0 /\ S1 = add ε S0
      /\ Θ  = Θa ++ (γ ~ abind_flex_mono) ++ Θb
      /\ Θ1 = Θa ++ (γ ~ abind_flex_mono_def (ptyp_var_f ε))
              ++ (ε ~ abind_flex_mono) ++ Θb).

(** Prepending a skipped entry preserves the shape. *)
Lemma alias_insert_out_cons : forall S0 S1 Θ0 Θ1 (β : atom) (b : abind),
  alias_insert_out S0 Θ0 S1 Θ1 ->
  alias_insert_out S0 ((β ~ b) ++ Θ0) S1 ((β ~ b) ++ Θ1).
Proof.
  intros * [ [-> ->] | [γ [ε [Θa [Θb [Hε [-> [-> ->]]]]]]] ].
  - left; auto.
  - right; exists γ, ε, ((β ~ b) ++ Θa), Θb.
    simpl_env. repeat split; auto.
Qed.

(** The two var-instance subst reductions, packaged once — the scrutinee
    is fetched from the goal's own [if] (the [eq_dec] term does not
    survive [simpl] in a matchable form; prop_consis_complete.v §7 records
    the same trap for the runner's tests). *)
Local Lemma subst_pskl_var_same : forall u (α : atom),
  subst_pskl_in_pskl u α (pskl_var_f α) = u.
Proof.
  intros. simpl.
  match goal with |- context [ if ?t then _ else _ ] => destruct t end;
    [ reflexivity | congruence ].
Qed.

Local Lemma subst_pskl_var_other : forall u (α β : atom),
  α <> β ->
  subst_pskl_in_pskl u β (pskl_var_f α) = pskl_var_f α.
Proof.
  intros * Hne. simpl.
  match goal with |- context [ if ?t then _ else _ ] => destruct t end;
    [ congruence | reflexivity ].
Qed.

Lemma e_assign_unify_consis_hole_walk :
  (forall S0 Θ Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
     Ξ = nil -> P = pskl_hole -> uniq Θ ->
     alias_insert_out S0 Θ S1 Θ1) /\
  (forall S0 Θ α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ1 }}e -> True) /\
  (forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
     P0 = pskl_hole -> (exists β, P = pskl_var_f β) -> uniq Θ ->
     Q = P /\ alias_insert_out S0 Θ S1 Θ1).
Proof.
  apply (e_assign_unify_consis_mutind
           (fun S0 Θ Ξ α P S1 Θ1 _ =>
              Ξ = nil -> P = pskl_hole -> uniq Θ ->
              alias_insert_out S0 Θ S1 Θ1)
           (fun S0 Θ α β S1 Θ1 _ => True)
           (fun Δ1 Δ2 S0 Θ P0 P Q S1 Θ1 _ =>
              P0 = pskl_hole -> (exists β, P = pskl_var_f β) -> uniq Θ ->
              Q = P /\ alias_insert_out S0 Θ S1 Θ1));
    (* the unify motive, and every row whose shape contradicts a guard *)
    try (now (intros; exact I));
    try (now (intros; match goal with
              | H : _ = pskl_hole |- _ => discriminate H end));
    try (now (intros; match goal with
              | H : exists _, _ = pskl_var_f _ |- _ =>
                  destruct H as [? H]; discriminate H end)).
  - (* Assign-SolveM: the insertion itself, [guess^TY(◇)] fresh *)
    intros S0 S1 Θ0 Ξ α P βs τ Hocc Hg Hmono HΞ HP Hu. subst.
    inversion Hg; subst.
    right.
    match goal with
    | Hfr : ?e `notin` S0 |- _ =>
        exists α, e, (@nil (atom * abind)), Θ0
    end.
    simpl_env. repeat split; auto.
  - (* Assign-Assign: a DEFINED head — substitute and re-enter; the
       target itself may be the head (the alias chase). *)
    intros S0 S1 Θ0 Θ1 Ξ α β τ P Q Hft D IH HΞ HP Hu. subst.
    assert (Hu0 : uniq (nil ++ Θ0)) by (clear - Hu; solve_uniq).
    destruct (α == β) as [Heq | Hne].
    + (* the chase: the definition's image becomes the subject *)
      subst β. rewrite subst_pskl_var_same in D.
      destruct τ as [ | n | γ' | τ1 τ2 | τ0 ];
        (* the four non-variable images: only [U-GhostR]; unchanged *)
        try (destruct (e_consis_inv_hole_pattern D
                         ltac:(intros ? Habs; simpl in Habs;
                               discriminate Habs))
               as [-> [-> _]];
             left; auto).
      (* τ = γ' — the chase continues at γ' *)
      assert (Hsubj : exists β',
          subst_pskl_in_pskl (ptyp_to_pskl (ptyp_var_f γ')) α
            (pskl_var_f α) = pskl_var_f β').
      { exists γ'. rewrite subst_pskl_var_same. simpl. reflexivity. }
      specialize (IH eq_refl Hsubj Hu0).
      destruct IH as [_ Hout].
      apply alias_insert_out_cons. exact Hout.
    + (* head ≠ target: the subject survives the substitution *)
      assert (Hsubj : exists β',
          subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)
          = pskl_var_f β').
      { exists α. rewrite subst_pskl_var_other by exact Hne. reflexivity. }
      specialize (IH eq_refl Hsubj Hu0).
      destruct IH as [_ Hout].
      apply alias_insert_out_cons. exact Hout.
  - (* Assign-Depend: [◇] mentions nothing, so the row cannot fire *)
    intros S0 S1 Θ0 Θ1 Ξ α β P Hne Hin D IH HΞ HP Hu. subst.
    simpl in Hin. exfalso. clear - Hin. fsetdec.
  - (* Assign-Skip *)
    intros S0 S1 Θ0 Θ1 Ξ α β P Hne Hnin D IH HΞ HP Hu. subst.
    apply alias_insert_out_cons.
    apply IH; auto. clear - Hu. solve_uniq.
  - (* Assign-SkipRigid *)
    intros S0 S1 Θ0 Θ1 Ξ α β P Hnin D IH HΞ HP Hu. subst.
    apply alias_insert_out_cons.
    apply IH; auto. clear - Hu. solve_uniq.
  - (* Assign-SkipTmVar *)
    intros S0 S1 Θ0 Θ1 Ξ α x A P D IH HΞ HP Hu. subst.
    apply alias_insert_out_cons.
    apply IH; auto. clear - Hu. solve_uniq.
  - (* Assign-SkipTmVar (skl) *)
    intros S0 S1 Θ0 Θ1 Ξ α x Q P D IH HΞ HP Hu. subst.
    apply alias_insert_out_cons.
    apply IH; auto. clear - Hu. solve_uniq.
  - (* U-FlexL: the walk *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P0 Hnf D IH HP0 Hvar Hu. subst.
    split; [ reflexivity | ]. apply IH; auto.
  - (* U-GhostR: the runner's route — unchanged *)
    intros Δ1 Δ2 S Θ0 P Hdis HP0 Hvar Hu.
    split; [ reflexivity | ]. left; auto.
Qed.

(** ⭐ What the divergent cells consume, composed with §3 of
    prop_consis_inc.v: after [e_consis_inv_flex_subject_hole] (or its
    mirror) exposes the walk, THIS is its output, ready for
    [collapse1_insert] below. *)
Corollary e_assign_hole_out : forall S0 Θ α S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ ⊲[ nil ] α ≔ pskl_hole ⊣ Θ1 }}e ->
  uniq Θ ->
  alias_insert_out S0 Θ S1 Θ1.
Proof.
  intros * Hd Hu.
  exact (proj1 e_assign_unify_consis_hole_walk
           _ _ _ _ _ _ _ Hd eq_refl eq_refl Hu).
Qed.

(* ===================================================================== *)
(*  §2  THE COLLAPSE                                                      *)
(* ===================================================================== *)

(** Remove every [α]-keyed entry (under [uniq] there is at most one). *)
Fixpoint aenv_remove (α : atom) (Θ : aenv) : aenv :=
  match Θ with
  | nil => nil
  | (x, b) :: Θ' =>
      if x == α then aenv_remove α Θ' else (x, b) :: aenv_remove α Θ'
  end.

(** Collapse the alias [γ ≔ ε̂]: drop [γ]'s entry, rename [ε̂] back to [γ]
    (keys and payloads — [ε̂]'s own entry becomes [γ]'s). *)
Definition collapse1 (γ ε : atom) (Θ : aenv) : aenv :=
  rename_aenv γ ε (aenv_remove γ Θ).

Lemma aenv_remove_app : forall α Θ1 Θ2,
  aenv_remove α (Θ1 ++ Θ2) = aenv_remove α Θ1 ++ aenv_remove α Θ2.
Proof.
  intros. induction Θ1 as [ | [x b] Θ1' IH ]; simpl; auto.
  destruct (x == α); [ auto | simpl; f_equal; auto ].
Qed.

Lemma aenv_remove_notin_id : forall α Θ,
  α `notin` dom Θ ->
  aenv_remove α Θ = Θ.
Proof.
  intros α Θ. induction Θ as [ | [x b] Θ' IH ]; intros Hα; simpl; auto.
  simpl in Hα. destruct (x == α); [ subst; fsetdec | ].
  f_equal. apply IH. fsetdec.
Qed.

Lemma rename_aenv_app : forall γ β Θ1 Θ2,
  rename_aenv γ β (Θ1 ++ Θ2) = rename_aenv γ β Θ1 ++ rename_aenv γ β Θ2.
Proof.
  intros. induction Θ1 as [ | [x b] Θ1' IH ]; simpl; [ reflexivity | ].
  f_equal. exact IH.
Qed.

(** ⭐ THE CELL COMPUTATION: collapsing §1's insertion recovers the input —
    which is the RUNNER's answer at the divergent cells.  The freshness of
    [ε̂] against the surroundings is exactly what the motive's coverage
    ([consis_call_cover [<=] S0], with [ε̂ ∉ S0]) will supply. *)
Lemma collapse1_insert : forall Θa Θb γ ε,
  γ `notin` dom Θa ∪ dom Θb ->
  ε `notin` add γ (ftvar_in_aenv Θa ∪ ftvar_in_aenv Θb) ->
  collapse1 γ ε (Θa ++ (γ ~ abind_flex_mono_def (ptyp_var_f ε))
                 ++ (ε ~ abind_flex_mono) ++ Θb)
  = Θa ++ (γ ~ abind_flex_mono) ++ Θb.
Proof.
  intros * Hγ Hε. unfold collapse1.
  rewrite !aenv_remove_app.
  rewrite (aenv_remove_notin_id Θa) by fsetdec.
  rewrite (aenv_remove_notin_id Θb) by fsetdec.
  simpl. destruct (γ == γ) as [_ | Hn]; [ | congruence ].
  destruct (ε == γ) as [Heq | _]; [ exfalso; clear - Hε Heq; fsetdec | ].
  rewrite rename_aenv_app.
  rewrite (rename_aenv_fresh_eq _ γ) by (clear - Hε; fsetdec).
  simpl. destruct (ε == ε) as [_ | Hn]; [ | congruence ].
  rewrite (rename_aenv_fresh_eq _ γ) by (clear - Hε; fsetdec).
  reflexivity.
Qed.
