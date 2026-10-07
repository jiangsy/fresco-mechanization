(** ⚠️ CONSTRAINT COLLECTION IS NOT STABLE UNDER A SOURCE SUBSTITUTION THAT
    INTRODUCES A *NEW* NAME — once look's ∀ rules are faithful, i.e.
    exists-fresh with a LEAKING binder (DESIGN.md §4.3, cluster 3).

    The mech carried the unconditional form (prop_looksub.v §4, the forward
    direction of the paper's lemma:constraint-collection-stable-substitution,
    algorithmic-proofs tex:504-520):

      {{ Θ ⊢ P ∼[α] P' ⤳ Ξ ⨾ 𝒞 }}a  ->  β <> α -> α ∉ ftv P0 -> lc P0 ->
      {{ Θ ⊢ (subst P0 β P) ∼[α] P' ⤳ Ξ ⨾ 𝒞          (* SAME Ξ, SAME 𝒞 *)

    Under the COFINITE encoding that was true }}a: the shared 𝒞 could not mention
    any binder, so the family could simply be rebuilt at binders avoiding
    [P0].  With LE-ForallInh exists-fresh, the derivation OWNS one binder
    [β0] and LEAKS it into 𝒞 — and a [P0] that happens to contain [β0] is
    exactly what no rule can re-derive: every binder the rule may pick avoids
    [ftv (subst P0 β P)], hence differs from [β0], hence changes 𝒞.

    THE WITNESS (Θ arbitrary, α β β0 distinct and outside it):

        Θ ⊢ ∀. (α → β)  ∼[α]  ∀. (0 → 0)   ⤳  ·  ⨾  [ β0 ≐ ]

    by LE-ForallInh at β0 then LE-Arrow (LE-Var on the left, LE-Absent on the
    right).  Substituting [P0 := β0] for [β] rewrites the SOURCE to
    [∀. (α → β0)], and now every LE-ForallInh binder δ must avoid
    [ftv (∀. (α → β0)) ∋ β0], so the collected constraint is [δ ≐] for some
    δ ≠ β0 — never the [β0 ≐] the statement demands.

    WHAT THIS DOES *NOT* SAY.  The paper's lemma is fine: it is stated under
    the Barendregt convention, where the derivation's bound names are chosen
    apart from everything else in sight, [P0] included.  What the mech must
    do — and now does — is SPELL THAT OUT, as the smallest premise that makes
    the rule's own side condition supply it:

        ftv P0 [<=] add α (ftvar_in_aenv Θ ∪ ftv P ∪ ftv P')

    i.e. THE SUBSTITUTED SKELETON INTRODUCES NO NAME THE JUDGMENT DOES NOT
    ALREADY MENTION.  Every ∀ rule picks its binder outside exactly that
    union, so [β0 ∉ ftv P0] is DERIVED, and the union only grows as the
    induction descends.  This is the same move cluster 2 made for
    [a_solve_sub_eq_weaken_mid_flex]'s output-freshness premise — Barendregt
    spelled out, never a weakening. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.def_shapes.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.

Set Implicit Arguments.

(* ===================================================================== *)
(*  The run:  ∀. (α → β)  ∼[α]  ∀. (0 → 0)  ⤳  ·  ⨾  [ β0 ≐ ]            *)
(* ===================================================================== *)

Definition cex_src (α β : atom) : pskl :=
  pskl_all_syn (pskl_arrow (pskl_var_f α) (pskl_var_f β)).
Definition cex_tgt : pskl :=
  pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)).

Lemma cex_run : forall Θ α β β0,
  β0 <> α -> β0 <> β -> β0 `notin` ftvar_in_aenv Θ -> α <> β ->
  {{ Θ ⊢ (cex_src α β) ∼[ α ] cex_tgt
    ⤳ nil ⨾ (a_cstr_eq (pskl_var_f β0) :: nil) }}a.
Proof.
  intros Θ α β β0 Hβ0α Hβ0β Hβ0Θ Hαβ.
  apply a_lookeq__forall_inh with (β := β0);
    [ cbn; clear - Hβ0α Hβ0β Hβ0Θ; fsetdec
    | (* the absence-first guard: α occurs in the subject *)
      cbn; clear; fsetdec | ].
  unfold open_pskl_wrt_pskl; cbn.
  assert (Harr : {{ ((β0 ~ abind_tvar) ++ Θ) ⊢
                   (pskl_arrow (pskl_var_f α) (pskl_var_f β)) ∼[ α ]
                   (pskl_arrow (pskl_var_f β0) (pskl_var_f β0))
                 ⤳ (nil ++ nil)
                 ⨾ ((a_cstr_eq (pskl_var_f β0) :: nil) ++ nil) }}a)
    by (apply a_lookeq__arrow;
        [ cbn; clear; fsetdec | cbn; clear; fsetdec
        | apply a_lookeq__var
        | apply a_lookeq__absent; cbn; clear - Hαβ; fsetdec ]).
  cbn in Harr. exact Harr.
Qed.

(* ===================================================================== *)
(*  … but the substituted source cannot collect that constraint.          *)
(* ===================================================================== *)

(** [subst β0 β (∀. (α → β)) = ∀. (α → β0)] — the new name is now FREE in
    the source, so no ∀ rule may open at it. *)
Lemma cex_subst_src : forall α β β0,
  α <> β ->
  subst_pskl_in_pskl (pskl_var_f β0) β (cex_src α β) = cex_src α β0.
Proof.
  intros α β β0 Hαβ. unfold cex_src; cbn.
  destruct (α == β) as [-> | _]; [ contradiction | ].
  destruct (β == β) as [_ | Hne]; [ reflexivity | contradiction ].
Qed.

Lemma cex_subst_no_run : forall Θ α β0,
  β0 <> α ->
  ~ ({{ Θ ⊢ (cex_src α β0) ∼[ α ] cex_tgt
       ⤳ nil ⨾ (a_cstr_eq (pskl_var_f β0) :: nil) }}a).
Proof.
  intros Θ α β0 Hβ0α Hd.
  unfold cex_src, cex_tgt in Hd.
  inversion Hd; subst;
    (* LE-Absent is the only non-∀ rule that can fire, and α DOES occur *)
    try solve [ cbn in *; match goal with
                | Habs : _ `notin` _ |- _ => clear - Habs; fsetdec end ].
  (* LE-ForallInh at some δ.  Its side condition forces δ ≠ β0 … *)
  match goal with
  | Hδ : ?δ `notin` add _ _ , Hprem : {{ _ ⊢ _ ∼[ _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
      assert (Hδβ0 : δ <> β0) by (cbn in Hδ; clear - Hδ; fsetdec);
      unfold open_pskl_wrt_pskl in Hprem; cbn in Hprem;
      inversion Hprem; subst
  end;
    (* … again LE-Absent is refuted … *)
    try solve [ cbn in *; match goal with
                | Habs : _ `notin` _ |- _ => clear - Habs; fsetdec end ].
  (* … and the ARROW row's left leg can only be LE-Var, which deposits the
     rule's OWN binder δ — so the collected list is [δ ≐], never [β0 ≐]. *)
  match goal with
  | Hl : {{ _ ⊢ (pskl_var_f ?a) ∼[ ?a ] _ ⤳ _ ⨾ _ }}a |- _ =>
      inversion Hl; subst
  end;
    try solve [ cbn in *; match goal with
                | Habs : _ `notin` _ |- _ => clear - Habs; fsetdec end ];
    try solve [ match goal with
                | Hne : _ <> _ |- _ => contradiction Hne; reflexivity end ].
  cbn in *; congruence.
Qed.

(** THE REFUTATION. *)
Theorem look_subst_stable_unconditional_is_false :
  ~ (forall Θ α P P' Ξ 𝒞,
       {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
       forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
       {{ Θ ⊢ (subst_pskl_in_pskl P0 β P) ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a).
Proof.
  intro Hclaim.
  (* three distinct atoms, all outside the (empty) context *)
  destruct (atom_fresh empty) as [α _].
  destruct (atom_fresh (singleton α)) as [β Hβ].
  destruct (atom_fresh (singleton α `union` singleton β)) as [β0 Hβ0].
  pose proof (@cex_run nil α β β0
                ltac:(clear - Hβ0; fsetdec) ltac:(clear - Hβ0; fsetdec)
                ltac:(cbn; clear; fsetdec) ltac:(clear - Hβ; fsetdec)) as Hrun.
  specialize (Hclaim _ _ _ _ _ _ Hrun β (pskl_var_f β0)
                ltac:(clear - Hβ; fsetdec)
                ltac:(cbn; clear - Hβ0; fsetdec)
                ltac:(constructor)).
  rewrite (@cex_subst_src α β β0 ltac:(clear - Hβ; fsetdec)) in Hclaim.
  exact (@cex_subst_no_run nil α β0 ltac:(clear - Hβ0; fsetdec) Hclaim).
Qed.
