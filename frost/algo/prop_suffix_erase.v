(** SUFFIX ERASURE — section D, lemma:suffix-erasure (paper proofs.tex).

        If  typp[M]{Θ,Ξ}{M}{bid A}  and Ξ is fresh for bid{A},
        then typp[M]{Θ}{M}{bid A}.

    ⛔ The paper proves this by "straightforward induction on the typing
    derivation", and that induction does not go through.  The obstruction is
    the all-in-one subtyping's [ForallL] row (full-decl-spec.tex:71): it
    instantiates with a decorated skeleton [ψ] the rule CHOOSES FREELY —
    the only conditions are [Γ ⊢^N tags{Ψ'}{ψ}] and well-formedness — so the
    recursive premise sits at [S[ψ/α]], which is NOT Ξ-fresh even when the
    conclusion is.  The configuration is reachable: with a DEFINED [α̂ ∈ Ξ]
    the sub-derivation genuinely consumes the Ξ entry, through its
    definition, while the conclusion never mentions Ξ.

    ⭐ THE PAPER'S INTUITION IS RIGHT — "the entries in Ξ are junk the
    derivation does not need" — and the repair is to make that precise
    rather than to weaken the statement: **erase by SOLVING, not by
    dropping**.  A flexible entry always admits a monotype to stand for it
    in the tail (its own definition if it has one, [1] if it does not), so
    the induction is generalized to

        Θa,α̂,Θ0 ⊢ J   ⟹   [τ/α̂]Θa,Θ0 ⊢ [τ/α̂]J

    and the paper's statement is the special case where the conclusion's
    types are Ξ-free, so the substitution is the identity on them.  At
    [ForallL] the instantiation becomes [ [τ/α̂]ψ ], which is Ξ-free, still
    a decorated skeleton and still carries the same tags — because τ is a
    MONOTYPE: no quantifiers, no ghosts, no tags.

    This file builds that generalization one judgement at a time.  §1 is the
    substitution on contexts, §2 the coercion commutations it needs. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_typing.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.prop_ctx_mono.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_pat_sub.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Substituting a MONOTYPE for a flexible variable, in a context     *)
(* ===================================================================== *)

(** The `rename_abind` shape (algo/def_extra.v) with a general monotype in
    place of a variable.  A skeleton payload takes the skeleton reading of
    τ; every other payload is a type or has none. *)
Definition subst_abind (τ : ptyp) (α : atom) (bd : abind) : abind :=
  match bd with
  | abind_tvar            => abind_tvar
  | abind_var_typ A       => abind_var_typ (subst_ptyp_in_ptyp τ α A)
  | abind_var_skl P       => abind_var_skl
                               (subst_pskl_in_pskl (ptyp_to_pskl τ) α P)
  | abind_flex_mono       => abind_flex_mono
  | abind_flex_mono_def A => abind_flex_mono_def (subst_ptyp_in_ptyp τ α A)
  end.

Fixpoint subst_aenv (τ : ptyp) (α : atom) (Θ : aenv) : aenv :=
  match Θ with
  | nil           => nil
  | (x, bd) :: Θ' => (x, subst_abind τ α bd) :: subst_aenv τ α Θ'
  end.

Lemma subst_aenv_app : forall τ α Θ1 Θ2,
  subst_aenv τ α (Θ1 ++ Θ2) = subst_aenv τ α Θ1 ++ subst_aenv τ α Θ2.
Proof.
  intros τ α Θ1; induction Θ1 as [ | [x bd] Θ1' IH ]; intros Θ2; simpl;
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma dom_subst_aenv : forall τ α Θ, dom (subst_aenv τ α Θ) [=] dom Θ.
Proof.
  intros τ α Θ; induction Θ as [ | [x bd] Θ' IH ]; simpl;
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma binds_subst_aenv : forall τ α x bd Θ,
  binds x bd Θ -> binds x (subst_abind τ α bd) (subst_aenv τ α Θ).
Proof.
  intros τ α x bd Θ; induction Θ as [ | [y bd'] Θ' IH ]; intros Hb.
  - inversion Hb.
  - simpl. unfold binds in *; simpl in *.
    destruct Hb as [Heq | Hb].
    + inversion Heq; subst. left; reflexivity.
    + right. apply IH. exact Hb.
Qed.

(** The two shapes the lookup rules need, in the direction the proofs use:
    a binding BELOW the substituted variable is untouched, because the
    context's well-formedness scopes its payload in the tail. *)
Lemma binds_subst_aenv_mid : forall τ α x bd Θa Θ0,
  binds x bd (Θa ++ Θ0) ->
  x <> α ->
  binds x (subst_abind τ α bd) (subst_aenv τ α Θa ++ subst_aenv τ α Θ0).
Proof.
  intros. rewrite <- subst_aenv_app. apply binds_subst_aenv. assumption.
Qed.

(* ===================================================================== *)
(*  §2  Substitution commutes with every coercion in play                 *)
(* ===================================================================== *)

(** The PLAIN commutations first — each coercion is structural, so it
    commutes with substitution when the substituted term is coerced too.
    [pskl_to_uskl_subst] is already in prop_flex.v. *)

Lemma ptyp_to_pskl_subst : forall A0 α A,
  ptyp_to_pskl (subst_ptyp_in_ptyp A0 α A)
  = subst_pskl_in_pskl (ptyp_to_pskl A0) α (ptyp_to_pskl A).
Proof.
  intros A0 α A; induction A; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma pskl_to_bskl_syn_subst : forall P0 α P,
  pskl_to_bskl_syn (subst_pskl_in_pskl P0 α P)
  = subst_bskl_in_bskl (pskl_to_bskl_syn P0) α (pskl_to_bskl_syn P).
Proof.
  intros P0 α P; induction P; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma pskl_to_bskl_inh_subst : forall P0 α P,
  pskl_to_bskl_inh (subst_pskl_in_pskl P0 α P)
  = subst_bskl_in_bskl (pskl_to_bskl_inh P0) α (pskl_to_bskl_inh P).
Proof.
  intros P0 α P; induction P; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma bskl_to_uskl_subst : forall Q0 α Q,
  bskl_to_uskl (subst_bskl_in_bskl Q0 α Q)
  = subst_bskl_in_uskl (bskl_to_uskl Q0) α (bskl_to_uskl Q).
Proof.
  intros Q0 α Q; induction Q; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma btyp_to_bskl_subst : forall B0 α B,
  btyp_to_bskl (subst_btyp_in_btyp B0 α B)
  = subst_bskl_in_bskl (btyp_to_bskl B0) α (btyp_to_bskl B).
Proof.
  intros B0 α B; induction B; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma btyp_to_ptyp_subst : forall B0 α B,
  btyp_to_ptyp (subst_btyp_in_btyp B0 α B)
  = subst_ptyp_in_ptyp (btyp_to_ptyp B0) α (btyp_to_ptyp B).
Proof.
  intros B0 α B; induction B; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma ptyp_to_btyp_syn_subst : forall A0 α A,
  ptyp_to_btyp_syn (subst_ptyp_in_ptyp A0 α A)
  = subst_btyp_in_btyp (ptyp_to_btyp_syn A0) α (ptyp_to_btyp_syn A).
Proof.
  intros A0 α A; induction A; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma ptyp_to_btyp_inh_subst : forall A0 α A,
  ptyp_to_btyp_inh (subst_ptyp_in_ptyp A0 α A)
  = subst_btyp_in_btyp (ptyp_to_btyp_inh A0) α (ptyp_to_btyp_inh A).
Proof.
  intros A0 α A; induction A; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

(** ⭐ A MONOTYPE HAS ONE COLOURING, so a single [τ] serves every sort at
    once: the inherited painting of the substituted variable is the
    synthesised one, which is what lets the [inh] and [syn] rows of the
    same derivation be substituted with the same object. *)
Lemma ptyp_to_btyp_inh_mono_syn : forall τ,
  mono_ptyp τ -> ptyp_to_btyp_inh τ = ptyp_to_btyp_syn τ.
Proof. intros τ Hm; induction Hm; simpl; congruence. Qed.

(** The composite coercions, derived. *)
Lemma ptyp_to_bskl_syn_subst : forall τ α A,
  ptyp_to_bskl_syn (subst_ptyp_in_ptyp τ α A)
  = subst_bskl_in_bskl (ptyp_to_bskl_syn τ) α (ptyp_to_bskl_syn A).
Proof.
  intros. unfold ptyp_to_bskl_syn.
  rewrite ptyp_to_pskl_subst, pskl_to_bskl_syn_subst. reflexivity.
Qed.

Lemma ptyp_to_uskl_syn_subst : forall τ α A,
  ptyp_to_uskl_syn (subst_ptyp_in_ptyp τ α A)
  = subst_bskl_in_uskl (ptyp_to_uskl_syn τ) α (ptyp_to_uskl_syn A).
Proof.
  intros. unfold ptyp_to_uskl_syn.
  rewrite ptyp_to_bskl_syn_subst, bskl_to_uskl_subst. reflexivity.
Qed.

(** The two mono-specific readings the lookup rules produce: substituting a
    monotype into an INHERITED painting is the same substitution as into a
    synthesised one. *)
Lemma pskl_to_bskl_inh_subst_mono : forall τ α P,
  mono_ptyp τ ->
  pskl_to_bskl_inh (subst_pskl_in_pskl (ptyp_to_pskl τ) α P)
  = subst_bskl_in_bskl (ptyp_to_bskl_syn τ) α (pskl_to_bskl_inh P).
Proof.
  intros τ α P Hm. rewrite pskl_to_bskl_inh_subst.
  f_equal. unfold ptyp_to_bskl_syn.
  clear - Hm; induction Hm; simpl; congruence.
Qed.

Lemma ptyp_to_btyp_inh_subst_mono : forall τ α A,
  mono_ptyp τ ->
  ptyp_to_btyp_inh (subst_ptyp_in_ptyp τ α A)
  = subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α (ptyp_to_btyp_inh A).
Proof.
  intros τ α A Hm.
  rewrite ptyp_to_btyp_inh_subst, (ptyp_to_btyp_inh_mono_syn Hm). reflexivity.
Qed.

(* ===================================================================== *)
(*  §3  The solving hypothesis, and the well-formedness judgements        *)
(* ===================================================================== *)

(** [τ] SOLVES the flexible entry [α ~ b] into the tail [Θ0]: a monotype
    well-formed there, and — if the entry carries a definition — τ IS that
    definition.  ⭐ Taking τ to BE the definition (rather than merely
    equivalent to it) is what makes the FlexL/FlexR rows collapse to their
    own premise instead of needing an equivalence transport: after the
    substitution the lookup's subject and its unfolding are the SAME term. *)
Definition solves_flex (τ : ptyp) (α : atom) (b : abind) (Θ0 : aenv) : Prop :=
  mono_ptyp τ /\ a_wf_ptyp Θ0 τ /\ α `notin` ftvar_in_ptyp τ /\
  (b = abind_flex_mono \/ b = abind_flex_mono_def τ).

Lemma solves_flex_mono : forall τ α b Θ0, solves_flex τ α b Θ0 -> mono_ptyp τ.
Proof. intros τ α b Θ0 [Hm _]. exact Hm. Qed.

Lemma solves_flex_lc : forall τ α b Θ0, solves_flex τ α b Θ0 -> lc_ptyp τ.
Proof. intros. apply mono_ptyp_lc. eapply solves_flex_mono; eassumption. Qed.

Lemma solves_flex_wf : forall τ α b Θ0, solves_flex τ α b Θ0 -> a_wf_ptyp Θ0 τ.
Proof. intros τ α b Θ0 [_ [Hw _]]. exact Hw. Qed.

(** ⭐ [τ] is α-FREE, so substituting it into itself is the identity — this
    is what makes the DEFINED case of a lookup row collapse: the rule's
    unfolding and its subject become the same term. *)
Lemma solves_flex_self : forall τ α b Θ0,
  solves_flex τ α b Θ0 -> subst_ptyp_in_ptyp τ α τ = τ.
Proof.
  intros τ α b Θ0 [_ [_ [Hfr _]]].
  apply subst_ptyp_in_ptyp_fresh_eq; exact Hfr.
Qed.

(** ⚙ THE SUBSTITUTION IS APPLIED TO THE WHOLE REMAINING CONTEXT, not just
    to the prefix above [α].  Leaving the tail alone would be sound — its
    payloads are scoped below [α] — but only after an "α does not occur in
    the tail" argument at every lookup row.  Substituting uniformly costs
    nothing (the tail's payloads are α-free, so the substitution is the
    identity there) and is discharged ONCE, at the erasure corollary. *)

Lemma binds_subst_strip_mid : forall τ α (b : abind) Θa Θ0 x bd,
  binds x bd (Θa ++ (α ~ b) ++ Θ0) ->
  x <> α ->
  binds x (subst_abind τ α bd) (subst_aenv τ α (Θa ++ Θ0)).
Proof.
  intros τ α b Θa Θ0 x bd Hb Hne.
  apply binds_subst_aenv.
  apply binds_app_1 in Hb as [Hb | Hb]; [ apply binds_app_2; exact Hb | ].
  apply binds_app_1 in Hb as [Hb | Hb]; [ | apply binds_app_3; exact Hb ].
  destruct Hb as [Heq | []]. inversion Heq; subst. contradiction.
Qed.

Lemma a_binds_tvar_subst_mid : forall τ α (b : abind) Θa Θ0 β,
  a_binds_tvar β (Θa ++ (α ~ b) ++ Θ0) ->
  β <> α ->
  a_binds_tvar β (subst_aenv τ α (Θa ++ Θ0)).
Proof.
  intros τ α b Θa Θ0 β H Hne.
  destruct H as [Hb | [Hb | [τ0 Hb]]];
    pose proof (binds_subst_strip_mid τ _ _ _ _ Hb Hne) as Hb'; simpl in Hb'.
  - left; exact Hb'.
  - right; left; exact Hb'.
  - right; right; eexists; exact Hb'.
Qed.

Lemma a_binds_tvar_subst_tail : forall τ α Θa Θ0 β,
  a_binds_tvar β Θ0 -> a_binds_tvar β (subst_aenv τ α (Θa ++ Θ0)).
Proof.
  intros τ α Θa Θ0 β H.
  destruct H as [Hb | [Hb | [τ0 Hb]]].
  - left. change abind_tvar with (subst_abind τ α abind_tvar).
    apply binds_subst_aenv. apply binds_app_3. exact Hb.
  - right; left.
    change abind_flex_mono with (subst_abind τ α abind_flex_mono).
    apply binds_subst_aenv. apply binds_app_3. exact Hb.
  - right; right. exists (subst_ptyp_in_ptyp τ α τ0).
    change (abind_flex_mono_def (subst_ptyp_in_ptyp τ α τ0))
      with (subst_abind τ α (abind_flex_mono_def τ0)).
    apply binds_subst_aenv. apply binds_app_3. exact Hb.
Qed.

(** The judgements below read the context only through [a_binds_tvar], so
    they travel along a map of type-level occurrences — payloads may change
    under it, which plain [binds]-monotonicity would not allow. *)
Lemma a_wf_ptyp_tbinds_mono : forall Θ A,
  a_wf_ptyp Θ A ->
  forall Θ', (forall β, a_binds_tvar β Θ -> a_binds_tvar β Θ') ->
  a_wf_ptyp Θ' A.
Proof.
  intros Θ A H; induction H; intros Θ' Hmon.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var; auto.
  - apply a_wf_ptyp__arrow; auto.
  - apply a_wf_ptyp__all with (L := L). intros β Hβ. apply H0; [ exact Hβ | ].
    intros γ Hγ. destruct (γ == β) as [-> | Hne].
    + unfold a_binds_tvar. left. unfold binds; simpl; left; reflexivity.
    + apply a_binds_tvar_weaken_cons. apply Hmon.
      unfold a_binds_tvar in Hγ |- *.
      destruct Hγ as [Hb | [Hb | [τ0 Hb]]];
        [ left | right; left | right; right; exists τ0 ];
        (unfold binds in Hb; simpl in Hb;
         destruct Hb as [He | Hb];
         [ inversion He; subst; contradiction | exact Hb ]).
Qed.

Lemma a_wf_ptyp_subst_tail : forall τ α Θa Θ0,
  a_wf_ptyp Θ0 τ -> a_wf_ptyp (subst_aenv τ α (Θa ++ Θ0)) τ.
Proof.
  intros. eapply a_wf_ptyp_tbinds_mono; [ eassumption | ].
  intros β Hβ. eapply a_binds_tvar_subst_tail; eassumption.
Qed.

Lemma a_wf_ptyp_subst_mid : forall Θ A,
  a_wf_ptyp Θ A ->
  forall τ α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τ α0 b Θ0 ->
  a_wf_ptyp (subst_aenv τ α0 (Θa ++ Θ0)) (subst_ptyp_in_ptyp τ α0 A).
Proof.
  (* [α0]: the rules' own binder is [α] (CLAUDE.md metavariable note). *)
  intros Θ A H; induction H; intros τ α0 b Θa Θ0 Heq Hs; subst; simpl.
  - apply a_wf_ptyp__unit.
  - destruct_if as [Heqα | Hne].
    + subst. apply a_wf_ptyp_subst_tail. eapply solves_flex_wf; eassumption.
    + apply a_wf_ptyp__var. eapply a_binds_tvar_subst_mid; eassumption.
  - apply a_wf_ptyp__arrow; eauto.
  - apply a_wf_ptyp__all with (L := L `union` singleton α0). intros β Hβ.
    rewrite subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var;
      [ | clear - Hβ; fsetdec | eapply solves_flex_lc; eassumption ].
    apply (H0 β ltac:(clear - Hβ; fsetdec) τ α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs ].
Qed.

Lemma guarded_pskl_mono : forall τ,
  mono_ptyp τ -> guarded_pskl (ptyp_to_pskl τ).
Proof.
  intros τ Hm; destruct Hm; simpl; auto with frost.
  apply guarded_pskl__arrow; apply lc_ptyp_to_pskl; apply mono_ptyp_lc;
    assumption.
Qed.

Lemma a_wf_pskl_subst_mid : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall τ α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τ α0 b Θ0 ->
  α0 `notin` Δ ->
  (subst_aenv τ α0 (Θa ++ Θ0)) ⨟ Δ
    ⊢ₚₛᵃ (subst_pskl_in_pskl (ptyp_to_pskl τ) α0 P).
Proof.
  intros Θ Δ P H; induction H; intros τ α0 b Θa Θ0 Heq Hs Hα0; subst; simpl.
  - apply a_wf_pskl__unit.
  - destruct_if as [Heqα | Hne].
    + subst. apply a_wf_pskl_mono_ptyp;
        [ eapply solves_flex_mono; eassumption | apply a_wf_ptyp_subst_tail;
                             eapply solves_flex_wf; eassumption ].
    + apply a_wf_pskl__var.
      destruct H as [HΔ | Htv];
        [ left; exact HΔ | right; eapply a_binds_tvar_subst_mid; eassumption ].
  - apply a_wf_pskl__arrow; eauto.
  - apply a_wf_pskl__all with (L := L `union` singleton α0). intros β Hβ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ; fsetdec
      | apply lc_ptyp_to_pskl; eapply solves_flex_lc; eassumption ].
    apply (H0 β ltac:(clear - Hβ; fsetdec) τ α0 b Θa Θ0);
      [ reflexivity | exact Hs | clear - Hα0 Hβ; fsetdec ].
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole.
    + apply guarded_pskl_subst;
        [ exact H
        | apply guarded_pskl_mono; eapply solves_flex_mono; eassumption
        | apply lc_ptyp_to_pskl; eapply solves_flex_lc; eassumption ].
    + match goal with
      | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
          apply (IH τ α0 b Θa Θ0); [ reflexivity | exact Hs | clear; fsetdec ]
      end.
Qed.

(* ===================================================================== *)
(*  §4  Type equivalence                                                  *)
(* ===================================================================== *)

(** ⭐ Note the shape of the [flex_def] row under the substitution.  When
    the looked-up variable IS the one being eliminated, the row's premise
    and its conclusion become the SAME type — because [τs] is chosen to BE
    the definition — so the row disappears rather than needing an
    equivalence to bridge it.  When it is a different variable, the row
    re-applies at the substituted definition. *)
Lemma a_tyequiv_subst_mid : forall Θ A A',
  Θ ⊢ A ≡ᵗ A' ->
  forall τs α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τs α0 b Θ0 ->
  uniq (Θa ++ (α0 ~ b) ++ Θ0) ->
  (subst_aenv τs α0 (Θa ++ Θ0))
    ⊢ (subst_ptyp_in_ptyp τs α0 A) ≡ᵗ (subst_ptyp_in_ptyp τs α0 A').
Proof.
  (* [τs] / [α0]: the rules' own binders are [τ] and [α]. *)
  intros Θ A A' H; induction H; intros τs α0 b Θa Θ0 Heq Hs Hu; subst.
  - (* refl *)
    apply a_tyequiv__refl. apply subst_ptyp_in_ptyp_lc_ptyp;
      [ exact H | eapply solves_flex_lc; eassumption ].
  - (* sym *) apply a_tyequiv__sym; eauto.
  - (* trans *) eapply a_tyequiv__trans; eauto.
  - (* flex_def *)
    simpl. destruct_if as [Heqα | Hne].
    + (* the eliminated variable: the row COLLAPSES *)
      subst α.
      assert (Hb : abind_flex_mono_def τ = b)
        by (eapply binds_mid_eq; eassumption).
      destruct Hs as [Hm [Hw [Hfrτ [Heqb | Heqb]]]];
        [ rewrite Heqb in Hb; discriminate | ].
      rewrite Heqb in Hb. inversion Hb; subst τ.
      rewrite subst_ptyp_in_ptyp_fresh_eq by exact Hfrτ.
      apply a_tyequiv__refl. apply mono_ptyp_lc; exact Hm.
    + apply a_tyequiv__flex_def with (α := α).
      change (abind_flex_mono_def (subst_ptyp_in_ptyp τs α0 τ))
        with (subst_abind τs α0 (abind_flex_mono_def τ)).
      eapply binds_subst_strip_mid; eassumption.
  - (* arrow *) simpl. apply a_tyequiv__arrow; eauto.
  - (* all *)
    simpl. apply a_tyequiv__all
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    repeat rewrite subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var;
      try solve [ clear - Hβ; fsetdec | eapply solves_flex_lc; eassumption ].
    apply (H0 β ltac:(clear - Hβ; fsetdec) τs α0 b Θa Θ0);
      [ reflexivity | exact Hs | exact Hu ].
Qed.

(* ===================================================================== *)
(*  §5  Refinement                                                        *)
(* ===================================================================== *)

(** Refinement is reflexive on a monotype painting — the shape the [var]
    row turns into once the variable has been replaced by [τ]. *)
Lemma ad_refine_syn_mono_refl : forall Θ Δ τ,
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  Θ ⨟ Δ ⊢ᵣᵃ (ptyp_to_bskl_syn τ) ⊳ (ptyp_to_bskl_syn τ).
Proof.
  intros Θ Δ τ Hm; revert Δ; induction Hm; intros Δ Hw; simpl.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var. inversion Hw; subst. right; assumption.
  - inversion Hw; subst. apply ad_refine_syn__arrow; auto.
Qed.

(** The fresh binder a cofinite row pushes joins the PREFIX, so the
    substituted-context statement stays in shape; the [uniq] hypothesis
    travels with it. *)
Ltac push_uniq Hu Hβ :=
  simpl_env; apply uniq_push;
    [ exact Hu | repeat rewrite dom_app; simpl; clear - Hβ; fsetdec ].

Lemma ad_refine_syn_subst_mid : forall Θ Δ Qs Qt,
  Θ ⨟ Δ ⊢ᵣᵃ Qs ⊳ Qt ->
  forall τs α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τs α0 b Θ0 ->
  uniq (Θa ++ (α0 ~ b) ++ Θ0) ->
  α0 `notin` Δ ->
  (subst_aenv τs α0 (Θa ++ Θ0)) ⨟ Δ
    ⊢ᵣᵃ (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 Qs)
      ⊳ (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 Qt).
Proof.
  intros Θ Δ Qs Qt H; induction H;
    intros τs α0 b Θa Θ0 Heq Hs Hu Hα0; subst; simpl.
  - (* unit *) apply ad_refine_syn__unit.
  - (* var *)
    destruct_if as [Heqα | Hne].
    + subst α. apply ad_refine_syn_mono_refl;
        [ eapply solves_flex_mono; eassumption
        | apply a_wf_ptyp_subst_tail; eapply solves_flex_wf; eassumption ].
    + apply ad_refine_syn__var.
      destruct H as [HΔ | Htv];
        [ left; exact HΔ | right; eapply a_binds_tvar_subst_mid; eassumption ].
  - (* arrow *) apply ad_refine_syn__arrow; eauto.
  - (* all : the witness joins Δ *)
    apply ad_refine_syn__all with (L := L `union` singleton α0). intros β Hβ.
    repeat rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      try solve [ clear - Hβ; fsetdec
                | apply mono_ptyp_to_bskl_syn_lc;
                  eapply solves_flex_mono; eassumption ].
    apply (H0 β ltac:(clear - Hβ; fsetdec) τs α0 b Θa Θ0);
      [ reflexivity | exact Hs | exact Hu | clear - Hα0 Hβ; fsetdec ].
  - (* hole : the fill is substituted, and stays well-formed *)
    unfold ptyp_to_bskl_syn at 1. rewrite <- pskl_to_bskl_syn_subst.
    apply ad_refine_syn__hole.
    eapply a_wf_pskl_subst_mid;
      [ eassumption | reflexivity | exact Hs | clear; fsetdec ].
  - (* tophole_remove *) apply ad_refine_syn__tophole_remove; eauto.
  - (* tophole_fill : the witness joins the PREFIX *)
    apply ad_refine_syn__tophole_fill
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | clear - Hβ; fsetdec
        | apply mono_ptyp_to_bskl_syn_lc; eapply solves_flex_mono;
          eassumption ].
    apply (H0 β ltac:(clear - Hβ; fsetdec) τs α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ | exact Hα0 ].
  - (* tophole_keep *)
    apply ad_refine_syn__tophole_keep;
      [ apply guarded_bskl_subst_mono;
        [ exact H | eapply solves_flex_mono; eassumption ]
      | eauto ].
  - (* flex_l *)
    destruct_if as [Heqα | Hne].
    + (* the eliminated variable: the lookup COLLAPSES into its premise *)
      subst α.
      assert (Hb : abind_flex_mono_def τ = b)
        by (eapply binds_mid_eq; eassumption).
      assert (Hfrτs : α0 `notin` ftvar_in_ptyp τs)
        by (destruct Hs as [_ [_ [Hf _]]]; exact Hf).
      assert (Hττ : τ = τs).
      { destruct Hs as [_ [_ [_ [Heqb | Heqb]]]];
          rewrite Heqb in Hb; [ discriminate | inversion Hb; reflexivity ]. }
      subst τ.
      assert (Hid : subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0
                      (ptyp_to_bskl_syn τs) = ptyp_to_bskl_syn τs)
        by (apply subst_bskl_in_bskl_fresh_eq;
            rewrite ftvar_in_bskl_ptyp_to_bskl_syn; exact Hfrτs).
      match goal with
      | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
          pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu Hα0) as IHx
      end.
      rewrite Hid in IHx. exact IHx.
    + apply ad_refine_syn__flex_l
        with (α := α) (τ := subst_ptyp_in_ptyp τs α0 τ).
      * change (abind_flex_mono_def (subst_ptyp_in_ptyp τs α0 τ))
          with (subst_abind τs α0 (abind_flex_mono_def τ)).
        eapply binds_subst_strip_mid; eassumption.
      * rewrite ptyp_to_bskl_syn_subst. eauto.
  - (* flex_r : the mirror *)
    destruct_if as [Heqα | Hne].
    + subst α.
      assert (Hb : abind_flex_mono_def τ = b)
        by (eapply binds_mid_eq; eassumption).
      assert (Hfrτs : α0 `notin` ftvar_in_ptyp τs)
        by (destruct Hs as [_ [_ [Hf _]]]; exact Hf).
      assert (Hττ : τ = τs).
      { destruct Hs as [_ [_ [_ [Heqb | Heqb]]]];
          rewrite Heqb in Hb; [ discriminate | inversion Hb; reflexivity ]. }
      subst τ.
      assert (Hid : subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0
                      (ptyp_to_bskl_syn τs) = ptyp_to_bskl_syn τs)
        by (apply subst_bskl_in_bskl_fresh_eq;
            rewrite ftvar_in_bskl_ptyp_to_bskl_syn; exact Hfrτs).
      match goal with
      | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
          pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu Hα0) as IHx
      end.
      rewrite Hid in IHx. exact IHx.
    + apply ad_refine_syn__flex_r
        with (α := α) (τ := subst_ptyp_in_ptyp τs α0 τ).
      * change (abind_flex_mono_def (subst_ptyp_in_ptyp τs α0 τ))
          with (subst_abind τs α0 (abind_flex_mono_def τ)).
        eapply binds_subst_strip_mid; eassumption.
      * rewrite ptyp_to_bskl_syn_subst. eauto.
Qed.
