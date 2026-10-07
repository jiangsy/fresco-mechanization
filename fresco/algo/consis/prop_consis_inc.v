(** THE CONSISTENCY TRIO ONLY ADDS INFORMATION — [Θ0 ⊴ Θ1] for
    [a_assign] / [a_unify] / [a_consis].

    ⭐ WHY IT EXISTS.  §8c.12 of docs/HANDOFF-extractable-algo-encoding.md
    lifts the threaded consistency runner's completeness off its hole-free
    restriction.  The restriction buys exactly six case-kills, and only TWO
    of them are genuinely divergent — (pattern [β̂] flexible, subject [◇])
    and its mirror (pattern [◇], subject [α̂] flexible), where the relation
    may take [U-FlexR] / [U-FlexL] while the runner takes [U-Ghost] /
    [U-GhostR].  At BOTH the runner returns its input context UNCHANGED, so
    the whole obligation is that the derivation's assignment walk only
    ADDED information — which is this file.

    ⭐ THE RELATION IS THE IDENTITY SHORTHAND [⊴], NOT A GENERAL [a_inc].
    Pushing the SAME entry through both sides is FALSE for an arbitrary [κ]:
    [a_inc__flex_def] demands [τ' ≡ᵗ msubst_ptyp κ τ], and [a_inc] permits a
    [κ] that solves variables the TARGET leaves flexible (take
    [Θ = Θ' = (α̂)] and [κ = [1/α̂]]), so [τ] and [κτ] need not be equivalent
    there.  [⊴] carries exactly the paper's "all entries of flexible
    variables in Θ are preserved in Θ'" (algorithmic.tex:135), and its
    congruence family already exists — [a_isub_cons_{flex,flex_def,var_typ,
    var_skl}] (algo/prop_basic.v) and [a_isub_cons_tvar]
    (algo/prop_stability.v).

    ⭐ THE MOTIVE DROPS THE PENDING BLOCK FROM THE SOURCE ([Θ0 ⊴ Θ1], not
    [(Ξ ++ Θ0) ⊴ Θ1]).  That is what makes almost every row a one-liner: the
    other reading forces a REORDERING argument at [Assign-SolveM],
    [Assign-Assign] and the three skips, all of which move an entry past
    [Ξ].  [a_suffix Ξ] rides along because SolveM deposits the block BELOW
    the solved head and must weaken past it; it is [nil] at the top and
    [Assign-Depend] only ever extends it with a flexible.

    ⚙ Three hypotheses, all of them structural: [a_suffix] of the block,
    [lc_aenv] of the context, and — §2b — [aenv_defs_lc], because
    [lc_abind] sends [flex_mono_def τ] to [True] (algo/prop_inc.v:75) and so
    says nothing about a definition's payload, while
    [a_isub_cons_flex_def] needs [lc_ptyp τ].  The [e_] layer gets that last
    one free from [e_assign_unify_consis_defs_mono]
    (ext_algo/prop_termination.v), whose [aenv_defs_mono] is already an
    INPUT of every runner call.

    ⚙ Sections: §1 the [lc_aenv] / [⊴] plumbing the rows need, §2 output
    local closure (a SEPARATE induction, as ext_algo/prop_consis.v §7 is —
    [U-Arrow]'s second premise runs at the FIRST's output, so §3 cannot
    supply its own side condition), §2b output definition-closure, §3 the
    increase. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.prop_basic.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_inc_strengthen.
Require Import src.fresco.algo.prop_stability.
Require Import src.fresco.algo.consis.prop_soundness_consis.

Set Implicit Arguments.
Open Scope fresco_a_scope.

(* ===================================================================== *)
(*  §1  [lc_aenv] plumbing — it is a [Forall], so [++] and the singleton  *)
(*      need one wrapper each in both directions.                         *)
(* ===================================================================== *)

Lemma lc_aenv_app_l : forall Θ1 Θ2, lc_aenv (Θ1 ++ Θ2) -> lc_aenv Θ1.
Proof. intros * H; unfold lc_aenv in *; apply Forall_app in H; tauto. Qed.

Lemma lc_aenv_app_r : forall Θ1 Θ2, lc_aenv (Θ1 ++ Θ2) -> lc_aenv Θ2.
Proof. intros * H; unfold lc_aenv in *; apply Forall_app in H; tauto. Qed.

Lemma lc_aenv_sing_inv : forall (x : atom) b, lc_aenv (x ~ b) -> lc_abind b.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma lc_aenv_sing : forall (x : atom) b, lc_abind b -> lc_aenv (x ~ b).
Proof. intros * H; unfold lc_aenv; repeat constructor; auto. Qed.

Lemma lc_aenv_var_typ_inv : forall (x : atom) A Θ,
  lc_aenv ((x ~ abind_var_typ A) ++ Θ) -> lc_ptyp A.
Proof. intros * H; apply lc_aenv_app_l in H; exact (lc_aenv_sing_inv H). Qed.

Lemma lc_aenv_var_skl_inv : forall (x : atom) P Θ,
  lc_aenv ((x ~ abind_var_skl P) ++ Θ) -> lc_pskl P.
Proof. intros * H; apply lc_aenv_app_l in H; exact (lc_aenv_sing_inv H). Qed.

Lemma a_decls_lc : forall Ξ, a_decls Ξ -> lc_aenv Ξ.
Proof.
  intros Ξ H; induction H; [ constructor | ].
  apply lc_aenv_app_intro; auto. apply lc_aenv_sing; constructor.
Qed.

(** Take every [lc_aenv] hypothesis apart into its entries. *)
Local Ltac lc_crack :=
  repeat match goal with
  | H : lc_aenv (?A ++ ?B) |- _ =>
      let H1 := fresh "Hl" in let H2 := fresh "Hl" in
      pose proof (lc_aenv_app_l H) as H1;
      pose proof (lc_aenv_app_r H) as H2; clear H
  end;
  repeat match goal with
  | H : lc_aenv (?x ~ ?b) |- _ =>
      let H1 := fresh "Hb" in
      pose proof (lc_aenv_sing_inv H) as H1; clear H
  end.

(** [Assign-SolveM]'s block is a declaration list, which [lc_mk] then uses. *)
Local Ltac lc_pre :=
  repeat match goal with
  | Hg : a_guess_mono _ _ ?bs _ |- _ =>
      lazymatch goal with
      | _ : a_decls bs |- _ => fail
      | _ => assert (a_decls bs) by (eapply a_guess_mono_decls; eauto)
      end
  end.

(** Put one back together. *)
Local Ltac lc_mk :=
  repeat first [ assumption
               | solve [ eauto 8 using lc_aenv_app_l, lc_aenv_app_r ]
               | solve [ apply a_decls_lc; assumption ]
               | apply lc_aenv_app_intro
               | apply lc_aenv_sing
               | exact I
               | solve [ simpl; auto using mono_ptyp_lc ]
               | solve [ eapply lc_aenv_var_typ_inv;
                         eauto 8 using lc_aenv_app_l, lc_aenv_app_r ]
               | solve [ eapply lc_aenv_var_skl_inv;
                         eauto 8 using lc_aenv_app_l, lc_aenv_app_r ] ].

(** Discharge a goal by an induction hypothesis, stripping the binder the
    binder rows put on BOTH sides of their premise. *)
Local Ltac lc_ih_strip :=
  match goal with
  | IH : lc_aenv _ -> lc_aenv (?X ++ ?B) |- lc_aenv ?B =>
      apply (@lc_aenv_app_r X B); apply IH; lc_mk
  | IH : lc_aenv _ -> lc_aenv ?B |- lc_aenv ?B => apply IH; lc_mk
  end.

(* ===================================================================== *)
(*  §2  the output context is locally closed                              *)
(*                                                                        *)
(*  ⚙ A SEPARATE INDUCTION, as prop_consis.v §7 is: [Arrow]'s second      *)
(*  premise runs at the FIRST's output, so the increase's own induction   *)
(*  cannot supply its [lc] side condition without this.                   *)
(* ===================================================================== *)

Lemma a_assign_unify_consis_lc :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
     lc_aenv (Ξ ++ Θ0) -> lc_aenv Θ1) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> lc_aenv Θ0 -> lc_aenv Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a -> lc_aenv Θ0 -> lc_aenv Θ1).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun Θ0 Ξ α P Θ1 _ => lc_aenv (Ξ ++ Θ0) -> lc_aenv Θ1)
           (fun Θ0 α β Θ1 _ => lc_aenv Θ0 -> lc_aenv Θ1)
           (fun Δ1 Δ2 Θ0 P0 P P' Θ1 _ => lc_aenv Θ0 -> lc_aenv Θ1));
    intros; simpl_env in *; lc_pre; lc_crack; lc_mk.
  all: lc_ih_strip.
Qed.

(* ===================================================================== *)
(*  §2b  every DEFINITION in the output is locally closed                 *)
(*                                                                        *)
(*  ⚠️ [lc_aenv] does NOT give this: [lc_abind] sends [flex_mono_def τ] to *)
(*  [True] (algo/prop_inc.v:75), so a definition's payload carries no      *)
(*  local-closure obligation at all.  But [a_isub_cons_flex_def] needs     *)
(*  [lc_ptyp τ] — its equational premise rewrites [msubst κ τ = τ] — so    *)
(*  the increase has to carry this separately.                            *)
(*  ⚙ The [e_] layer gets the same content free from                      *)
(*  [e_assign_unify_consis_defs_mono] (ext_algo/prop_termination.v), whose *)
(*  [aenv_defs_mono] is already an INPUT of every runner call; at the [a_] *)
(*  layer there is no such lemma, hence this one.                         *)
(* ===================================================================== *)

Definition aenv_defs_lc (Θ : aenv) : Prop :=
  forall α τ, binds α (abind_flex_mono_def τ) Θ -> lc_ptyp τ.

Lemma aenv_defs_lc_nil : aenv_defs_lc nil.
Proof. intros α τ Hb; inversion Hb. Qed.

Lemma aenv_defs_lc_app_l : forall Θ1 Θ2, aenv_defs_lc (Θ1 ++ Θ2) -> aenv_defs_lc Θ1.
Proof. intros * H α τ Hb; eapply H; unfold binds; apply in_or_app; left; exact Hb. Qed.

Lemma aenv_defs_lc_app_r : forall Θ1 Θ2, aenv_defs_lc (Θ1 ++ Θ2) -> aenv_defs_lc Θ2.
Proof. intros * H α τ Hb; eapply H; unfold binds; apply in_or_app; right; exact Hb. Qed.

Lemma aenv_defs_lc_app_intro : forall Θ1 Θ2,
  aenv_defs_lc Θ1 -> aenv_defs_lc Θ2 -> aenv_defs_lc (Θ1 ++ Θ2).
Proof.
  intros * H1 H2 α τ Hb; unfold binds in Hb; apply in_app_or in Hb.
  destruct Hb as [H | H]; [ eapply H1 | eapply H2 ]; exact H.
Qed.

Lemma aenv_defs_lc_sing : forall (x : atom) b,
  (forall τ, b = abind_flex_mono_def τ -> lc_ptyp τ) -> aenv_defs_lc (x ~ b).
Proof.
  intros * H α τ Hb.
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
    [ apply H; auto | inversion Hb' ].
Qed.

Lemma aenv_defs_lc_head : forall (x : atom) τ Θ,
  aenv_defs_lc ((x ~ abind_flex_mono_def τ) ++ Θ) -> lc_ptyp τ.
Proof. intros * H; eapply H; unfold binds; left; reflexivity. Qed.

Lemma a_decls_defs_lc : forall Ξ, a_decls Ξ -> aenv_defs_lc Ξ.
Proof.
  intros Ξ H; induction H; [ apply aenv_defs_lc_nil | ].
  apply aenv_defs_lc_app_intro; auto.
  apply aenv_defs_lc_sing; intros ? Heq; discriminate.
Qed.

Local Ltac dl_mk :=
  repeat first [ assumption
               | solve [ eauto 8 using aenv_defs_lc_app_l, aenv_defs_lc_app_r ]
               | solve [ apply a_decls_defs_lc; assumption ]
               | apply aenv_defs_lc_app_intro
               | apply aenv_defs_lc_nil
               | apply aenv_defs_lc_sing
               | solve [ intros ? Heq; discriminate ]
               | solve [ intros ? Heq; inversion Heq; subst;
                         auto using mono_ptyp_lc; constructor ] ].

(** The payload of a definition ENTRY, from the ambient invariant. *)
Local Ltac def_lc :=
  solve [ eapply aenv_defs_lc_head;
          eauto 8 using aenv_defs_lc_app_l, aenv_defs_lc_app_r ].

Local Ltac dl_ih_strip :=
  match goal with
  | IH : aenv_defs_lc _ -> aenv_defs_lc (?X ++ ?B) |- aenv_defs_lc ?B =>
      apply (@aenv_defs_lc_app_r X B); apply IH; dl_mk
  | IH : aenv_defs_lc _ -> aenv_defs_lc ?B |- aenv_defs_lc ?B => apply IH; dl_mk
  end.

Lemma a_assign_unify_consis_defs_lc :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
     aenv_defs_lc (Ξ ++ Θ0) -> aenv_defs_lc Θ1) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> aenv_defs_lc Θ0 -> aenv_defs_lc Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
     aenv_defs_lc Θ0 -> aenv_defs_lc Θ1).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun Θ0 Ξ α P Θ1 _ => aenv_defs_lc (Ξ ++ Θ0) -> aenv_defs_lc Θ1)
           (fun Θ0 α β Θ1 _ => aenv_defs_lc Θ0 -> aenv_defs_lc Θ1)
           (fun Δ1 Δ2 Θ0 P0 P P' Θ1 _ => aenv_defs_lc Θ0 -> aenv_defs_lc Θ1));
    intros; simpl_env in *; lc_pre; dl_mk.
  all: dl_ih_strip.
Qed.

(* ===================================================================== *)
(*  §3  THE TRIO ONLY ADDS INFORMATION                                    *)
(*                                                                        *)
(*  ⭐ The assign motive drops the pending block from the SOURCE — that   *)
(*  is what makes almost every row a one-liner.  The alternative          *)
(*  [(Ξ ++ Θ0) ⊴ Θ1] forces a reordering argument at SolveM, Assign and   *)
(*  the three skips, because those rules move an entry past [Ξ].          *)
(*  ⚙ [a_suffix Ξ] must ride along: SolveM deposits the block BELOW the   *)
(*  solved head and has to weaken past it.  It is [nil] at the top and    *)
(*  [Depend] only ever extends it with a flexible.                        *)
(* ===================================================================== *)

Local Ltac suf_mk :=
  repeat first [ assumption
               | solve [ apply a_decls_suffix; assumption ]
               | apply a_suffix_app
               | apply (a_suffix__cons _ (b := abind_flex_mono))
               | apply a_suffix__nil
               | constructor ].

(** The two output invariants, at every premise's output context. *)
Local Ltac out_props :=
  repeat match goal with
  | H : {{ ?Θ0 ⊢[ _ | _ | _ ] _ ∼ _ ⊣ ?Θ1 }}a |- _ =>
      lazymatch goal with
      | _ : lc_aenv Θ1 |- _ => fail
      | _ => let X := fresh "Hlo" in
             assert (X : lc_aenv Θ1)
               by (eapply (proj2 (proj2 a_assign_unify_consis_lc));
                   [ exact H | lc_mk ])
      end
  | H : {{ ?Θ0 ⊢[ _ | _ | _ ] _ ∼ _ ⊣ ?Θ1 }}a |- _ =>
      lazymatch goal with
      | _ : aenv_defs_lc Θ1 |- _ => fail
      | _ => let X := fresh "Hdo" in
             assert (X : aenv_defs_lc Θ1)
               by (eapply (proj2 (proj2 a_assign_unify_consis_defs_lc));
                   [ exact H | dl_mk ])
      end
  end.

(** Discharge by an induction hypothesis, supplying its side conditions. *)
Local Ltac le_ih :=
  match goal with
  | IH : a_suffix _ -> lc_aenv _ -> aenv_defs_lc _ -> ?A ⊴ ?B |- ?A ⊴ ?B =>
      apply IH; [ suf_mk | lc_mk | dl_mk ]
  | IH : lc_aenv _ -> aenv_defs_lc _ -> ?A ⊴ ?B |- ?A ⊴ ?B =>
      apply IH; [ lc_mk | dl_mk ]
  end.

(* ===================================================================== *)
(*  §4  RELATION TO [a_consis_sound]                                      *)
(*                                                                        *)
(*  ⚠️ OVERLAP, recorded deliberately.  [a_consis_sound]                   *)
(*  (consis/prop_soundness_consis.v) already carries [Θ0 ⊴ Θ1] as its     *)
(*  FIRST conjunct, for the CONSISTENCY component, under FULL             *)
(*  well-formedness of the context and both skeletons.  §3 is the         *)
(*  STRONGER form and is why the duplicate is kept — CLAUDE.md asks for  *)
(*  one fact, one name, in its STRONGEST form:                            *)
(*                                                                        *)
(*    · its hypotheses are weaker — [lc_aenv] + [aenv_defs_lc] rather     *)
(*      than [a_wf_aenv], and nothing at all about the skeletons;         *)
(*    · it covers the ASSIGN and UNIFY components too, which              *)
(*      [a_consis_sound] does not state.                                  *)
(*                                                                        *)
(*  ⚙ The corollary below discharges the comparison: it recovers          *)
(*  [a_consis_sound]'s conjunct from §3.  ⚠️ It is also the shape a        *)
(*  well-formed caller wants, so prefer it over §3 when [a_wf_aenv] is    *)
(*  already in hand.                                                      *)
(* ===================================================================== *)

