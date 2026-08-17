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

    §3  [e_assign_absorb] — a NIL-blocked walk at [Ξ ++ Θ] IS the
        [Ξ]-blocked walk at [Θ], when every entry of [Ξ] is an undefined
        flexible the payload mentions.  ⭐ The piece §8c.12c predicted
        ("an ABSORPTION lemma for insert-headed walks"); it is what makes
        the re-walk [Assign-Assign] triggers harmless, and it is a
        statement about ONE side, so it is independent of the ⛔ below.

    ⛔⛔ WHAT THIS FILE DOES **NOT** SUPPORT, and must not be used for:
    an EXACT transport of a derivation across [collapse1] — i.e. "the
    collapsed derivation's output is [collapse1] of the original's".
    That is REFUTED, machine-checked, by cex/probe_collapse_orientation.v:
    at the alias entry a walk must take [Assign-Assign], which converts it
    to a CONSIS, and when the payload is the alias variable itself that
    consis is a UNIFY whose [Flex-Flex-R] orients the new definition the
    OPPOSITE way from the collapsed walk's [SolveM] — [(α̂ ≔ γ̂, γ̂)]
    against [(γ̂ ≔ α̂, α̂)], the same equivalence class with a different
    REPRESENTATIVE.  ⚙ The handover records this as dead end 5 and derives
    constraint C6 (orientation-tolerance) from it, which is what rules out
    ANY relation that is a function of the context. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.consis.prop_consis_rename.
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

(* ⚙ The two var-instance subst reductions this file needs already exist,
   as [subst_pskl_var_eq] / [subst_pskl_var_neq]
   (algo/consis/prop_consis_rename.v §0) — imported above rather than
   restated, per CLAUDE.md's one-fact-one-name rule. *)

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
      subst β. rewrite subst_pskl_var_eq in D.
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
      { exists γ'. rewrite subst_pskl_var_eq. simpl. reflexivity. }
      specialize (IH eq_refl Hsubj Hu0).
      destruct IH as [_ Hout].
      apply alias_insert_out_cons. exact Hout.
    + (* head ≠ target: the subject survives the substitution *)
      assert (Hsubj : exists β',
          subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)
          = pskl_var_f β').
      { exists α. rewrite subst_pskl_var_neq by exact Hne. reflexivity. }
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
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P0 Hnf Hnhole D IH HP0 Hvar Hu. subst.
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

(* ===================================================================== *)
(*  §3  ABSORPTION — a re-walked block is the SAME block                  *)
(*                                                                        *)
(*  ⭐ THE LEMMA §8c.12c PREDICTED — an ABSORPTION lemma for              *)
(*  insert-headed walks — and the one the transport's hardest row needs.  *)
(*                                                                        *)
(*  At the alias entry a walk MUST take [Assign-Assign] (a defined head    *)
(*  has no skip row), which PREPENDS the pending block to the context and  *)
(*  re-enters CONSISTENCY there — so the collapsed side, which has no      *)
(*  such entry, is left holding a walk at [Ξ ++ Θ] with an EMPTY block     *)
(*  where it wants one at [Θ] with block [Ξ].  Those are not the same      *)
(*  judgement in general (a skipped entry is re-attached ABOVE the output, *)
(*  a blocked one is dumped BELOW the solved target).  They ARE the same   *)
(*  when every entry of [Ξ] is an undefined flexible the payload MENTIONS: *)
(*  then the re-walk can only [Assign-Depend] each one, rebuilding [Ξ] in  *)
(*  order.  ⚙ And that is exactly the block's own invariant — [Ξ] grows    *)
(*  ONLY by [Assign-Depend], whose premises are those two conditions.      *)
(* ===================================================================== *)

(** What [Assign-Depend] puts in the block, as a property of a slice. *)
Definition block_absorbable (Ξ0 : aenv) (α : atom) (P : pskl) : Prop :=
  List.Forall (fun e => snd e = abind_flex_mono /\ fst e <> α
                        /\ fst e `in` ftvar_in_pskl P) Ξ0.

(** One entry.  ⚙ The inversion is CLEAN: at a [flex_mono] head that is
    neither the target nor absent from the payload, [Assign-Depend] is the
    only row that can fire — [SolveM] and [UnivGhost-Id] want the head to
    BE the target, [Assign-Skip] wants it OUT of the payload,
    [Assign-Assign] wants it DEFINED, and the three [Skip*] rows want a
    rigid or term binding. *)
Lemma e_assign_absorb_one : forall S0 S1 Θ Ξ α β P Θ',
  α <> β ->
  β `in` ftvar_in_pskl P ->
  {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ) ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e ->
  {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ++ (β ~ abind_flex_mono) ] α ≔ P ⊣ Θ' }}e.
Proof.
  intros * Hne Hin Hd. inversion Hd; subst;
    (* [UnivGhost-Id] and [SolveM] both force the head to BE the target *)
    try congruence;
    (* [Assign-Skip] wants the head OUT of the payload *)
    try (match goal with
         | Hout : ?b `notin` ftvar_in_pskl ?p |- _ =>
             exfalso; clear - Hin Hout; fsetdec
         end).
  (* ⚙ [Assign-Depend], the only survivor, is closed by the [congruence]
     above — its goal IS its own premise. *)
Qed.

(** The slice.  ⚙ Induction on [Ξ0]; the block accumulates on the RIGHT,
    which is the order [Assign-Depend] itself builds. *)
Lemma e_assign_absorb : forall Ξ0 S0 S1 Θ Ξ α P Θ',
  block_absorbable Ξ0 α P ->
  {{ S0 ↝ S1 ⊨ (Ξ0 ++ Θ) ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e ->
  {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ++ Ξ0 ] α ≔ P ⊣ Θ' }}e.
Proof.
  induction Ξ0 as [ | [β b] Ξ0' IH ]; intros * Hok Hd.
  - simpl_env in *. assumption.
  - unfold block_absorbable in Hok. inversion Hok as [ | ? ? Hhd Htl ]; subst.
    simpl in Hhd. destruct Hhd as [-> [Hne Hin]].
    simpl_env in Hd.
    apply (e_assign_absorb_one (not_eq_sym Hne) Hin) in Hd.
    apply IH in Hd; [ | exact Htl ].
    simpl_env in *. assumption.
Qed.

(** ⭐ The form the transport consumes: a NIL-blocked walk at the prepended
    context is the SAME derivation as the [Ξ]-blocked walk below it. *)
Corollary e_assign_absorb_nil : forall S0 S1 Θ Ξ α P Θ',
  block_absorbable Ξ α P ->
  {{ S0 ↝ S1 ⊨ (Ξ ++ Θ) ⊲[ nil ] α ≔ P ⊣ Θ' }}e ->
  {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e.
Proof.
  intros * Hok Hd.
  (* ⚠️ Pin the block index from the GOAL's shape ([nil ++ Ξ]) and let
     unification split it — a named-argument application does not bind
     here, and an [eapply] would leave the list-valued index as an evar
     (the >900 s trap the handover records). *)
  assert (Hd' : {{ S0 ↝ S1 ⊨ Θ ⊲[ (nil ++ Ξ) ] α ≔ P ⊣ Θ' }}e)
    by (apply e_assign_absorb; [ exact Hok | simpl_env; exact Hd ]).
  simpl_env in Hd'. exact Hd'.
Qed.
