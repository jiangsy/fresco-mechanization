(** Problems, solutions, and OPTIMALITY for consistency
    — the notions [thm:complete-consistency] is stated against.
    (full-algo-spec.tex:1476-1519, "Problems and solutions of consistency").

    These are the notions [thm:complete-consistency] is stated against.  Note
    they are where the paper's EXTERNAL well-formedness conditions land: a
    problem REQUIRES its skeletons to be well-formed in Θ₀
    (docs/WF-SIDE-CONDITIONS.md).

    Optimality is the interesting one.  It says the algorithm's solution is the
    MOST GENERAL one: every other solution factors through it, via a further
    metasubstitution ζ — which is exactly why completeness needs COMPOSITION
    (`θ ≡ ζ ∘ θ₁`, see algo/prop_compose.v) and PRECISION (`ζP₁ ⊑ Q`, see
    algo/prop_precise.v).  Those two were the prerequisites; this file states
    what they are for. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_precise.

Set Implicit Arguments.

(* ===================================================================== *)
(*  1.  Consistency                                                       *)
(* ===================================================================== *)

(** A problem of consistency is a tuple (Θ₀; P₀; P) where P₀ and P are
    well-formed in Θ₀.  (The paper's external wf condition, made a premise.) *)
Definition a_consis_problem (Θ0 : aenv) (P0 P : pskl) : Prop :=
  a_wf_aenv Θ0 /\ a_wf_pskl Θ0 P0 /\ a_wf_pskl Θ0 P.

(** A solution is a tuple (Θ₀ ⊑[θ₁] Θ₁; P₁) such that the substituted input is
    consistent with P₁, and P₁ is a refinement of the substituted input
    skeleton. *)
Definition a_consis_solution
    (Θ0 : aenv) (P0 P : pskl) (θ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  empty ⨟ Θ1 ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θ1 P)) ≈ P1 /\
  Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl θ1 P0)) ⊳ P1.

(** The solution is OPTIMAL if every other solution factors through it: there is
    a ζ carrying Θ₁ to the other target, with θ ≡ ζ∘θ₁, and the algorithm's
    output is at least as PRECISE as the other one's. *)
Definition a_consis_optimal
    (Θ0 : aenv) (P0 P : pskl) (θ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  is_id_msubst θ1 ->
  forall θ Θ Q,
    a_consis_solution Θ0 P0 P θ Θ Q ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
      Θ ⨟ empty ⊢ᵣᵃ (msubst_bskl ζ P1) ⊳ Q.

(* ===================================================================== *)
(*  2.  Unification of flexible variables                                 *)
(* ===================================================================== *)

(** The paper's [α̂]/[β̂] are HATTED — flexible, defined or not.  [α `in` dom Θ0]
    would also admit RIGID and TERM variables, which [unifyvar] does not take.
    All four [a_unify] rules now carry [a_flex_tvar] explicitly (the hatted
    prose-completion, docs/PAPER-GAPS.md), so the problem must say so too. *)
Definition a_unify_problem (Θ0 : aenv) (α β : atom) : Prop :=
  a_wf_aenv Θ0 /\ a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β.

Definition a_unify_solution
    (Θ0 : aenv) (α β : atom) (θ1 : metasubst) (Θ1 : aenv) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  Θ1 ⊢ (msubst_lookup θ1 α) ≡ᵗ (msubst_lookup θ1 β).

Definition a_unify_optimal
    (Θ0 : aenv) (α β : atom) (θ1 : metasubst) (Θ1 : aenv) : Prop :=
  is_id_msubst θ1 ->
  forall θ Θ,
    a_unify_solution Θ0 α β θ Θ ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ.

(* ===================================================================== *)
(*  3.  Assignment of a flexible variable                                 *)
(* ===================================================================== *)

(** NB [P] is well-formed in [Ξ ++ Θ0], NOT in [Θ0].  [Assign-Depend] MOVES
    flexible variables out of [Θ0] into [Ξ] while [P] keeps mentioning them —
    its premise is literally [β ∈ ftv(P)] — so at a recursive assignment node
    [P]'s free variables are spread across both.  The soundness side already
    has this right ([assign_sound_concl] asks for [(Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P]).
    The two readings coincide only at the top-level call, where [Ξ = nil], which
    is why the bug was invisible.  Same for [a_non_flex].

    [dom Ξ ⊆ ftv(P)] is the paper's own invariant on [Ξ] — "Ξ only contains
    declarations of flexible variables APPEARING IN P" (full-algo-spec.tex:1508-1509)
    — which [a_decls Ξ] alone does not express ([a_decls] says only "every entry
    is an undefined flexible variable").  [Assign-Depend] maintains it.

    The subject is HATTED, as in [a_unify_problem] above. *)
Definition a_assign_problem (Θ0 : aenv) (Ξ : aenv) (α : atom) (P : pskl) : Prop :=
  a_wf_aenv (Ξ ++ Θ0) /\ a_flex_tvar Θ0 α /\
  a_wf_pskl (Ξ ++ Θ0) P /\ a_non_flex (Ξ ++ Θ0) P /\
  a_decls Ξ /\ dom Ξ [<=] ftvar_in_pskl P.

Definition a_assign_solution
    (Θ0 Ξ : aenv) (α : atom) (P : pskl) (θ1 : metasubst) (Θ1 : aenv) : Prop :=
  (Ξ ++ Θ0) ≤[ θ1 ] Θ1 /\
  empty ⨟ Θ1 ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θ1 P))
                ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup θ1 α))).

Definition a_assign_optimal
    (Θ0 Ξ : aenv) (α : atom) (P : pskl) (θ1 : metasubst) (Θ1 : aenv) : Prop :=
  is_id_msubst θ1 ->
  forall θ Θ,
    a_assign_solution Θ0 Ξ α P θ Θ ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv (Ξ ++ Θ0) θ (msubst_compose ζ θ1) Θ.

(* ===================================================================== *)
(*  4.  AUGMENTED optimality motives (for the mutual induction)           *)
(*                                                                        *)
(*  The three top-level [_optimal] definitions above are the UNAUGMENTED  *)
(*  statements of [thm:complete-consistency]'s optimality half.  The      *)
(*  induction, however, must run on the AUGMENTED problem                 *)
(*  (Δ₁;Δ₂;Ψ;Θ₀;P₀;S) of consistency-proofs.tex:2230-2242 — a Δ-indexed   *)
(*  pair of refinements plus the [no_flex_dep]/[flex_above_free] side      *)
(*  conditions that [consis_sound_post] (algo/prop_consis_sound.v:2501)    *)
(*  already carries.  So we keep the unaugmented definitions as the        *)
(*  top-level corollaries and state the induction against these AUGMENTED  *)
(*  [*_optimal_post] motives — mirroring exactly the shape of the green    *)
(*  soundness bundle [a_assign_unify_consis_sound].                        *)
(*                                                                         *)
(*  Design (docs/DESIGN-completeness-measure.md §6, §7.2): optimality is    *)
(*  proved by induction on the ALGORITHMIC derivation (which the theorem   *)
(*  is HANDED), so it needs no well-founded measure — that is confined to  *)
(*  the orthogonal EXISTENCE half.  Given the derivation Θ0 → Θ1 together  *)
(*  with the algorithm's own solution substitution [θ1] (Θ0 ≤[θ1] Θ1) and  *)
(*  ANY competing solution [θ] into [Θ], the motive produces the factoring *)
(*  [ζ]: Θ1 ≤[ζ] Θ, [θ ≡ ζ∘θ1], and — for consistency — a PRECISION        *)
(*  statement [ζQ ⊑ Qb] (⊑ = ad_precise, algo/prop_precise.v).  The         *)
(*  top-level corollary converts precision back to the refinement [⊳] via   *)
(*  [ad_precise_preserves_refine].                                         *)
(*                                                                         *)
(*  MOTIVE CORRECTION (validated 2026-07-15, [paper-gap]).  Each motive     *)
(*  and each top-level [_optimal] definition now REQUIRES [is_id_msubst θ1]. *)
(*  Without it the statements are FALSE — a concrete counterexample:         *)
(*                                                                          *)
(*    Θ0 = α̂,β̂,γ̂ (all flexible);  θ1 = [γ̂/α̂, γ̂/β̂, γ̂/γ̂]  (a valid, NON-    *)
(*    identity increment Θ0 ≤[θ1] Θ0);  competing θ = [Int/α̂, Bool/β̂, …].   *)
(*    An axiom node (e.g. Ghost/Unit) has Θ1 = Θ0, so it must exhibit ζ with *)
(*    a_inc_equiv Θ0 θ (ζ∘θ1) Θ.  But (ζ∘θ1)α̂ = ζγ̂ = (ζ∘θ1)β̂, forcing      *)
(*    Θ ⊢ Int ≡ᵗ ζγ̂ ≡ᵗ Bool, i.e. Int ≡ᵗ Bool — impossible.  So NO ζ works. *)
(*                                                                          *)
(*  The paper (consistency-proofs.tex:2246) produces θ1 EXISTENTIALLY as the *)
(*  algorithm's OWN solution, which is the identity metasubstitution ι       *)
(*  (a_isub / [DESIGN-completeness-measure.md §7.3 L10]): the algorithm only  *)
(*  ADDS definitions, never rewrites an existing flexible, so [Θ0 ⊴ Θ1] and  *)
(*  its witness θ1 satisfy [is_id_msubst θ1].  Requiring it here is exactly   *)
(*  the a_isub identity witness [prop_precise_recover.v] discharges, and it   *)
(*  is what makes [msubst_compose ζ θ1] collapse to [ζ] (see the helper       *)
(*  [msubst_compose_is_id_r] at the foot of this file).                      *)
(*                                                                          *)
(*  These are the INDUCTION targets only — pure [Prop]s, stated (not yet    *)
(*  proved) as the scaffolding the 28-case [a_assign_unify_consis_mutind]   *)
(*  bundle would discharge, exactly as [consis_sound_concl] et al. do for   *)
(*  soundness.  The competing-solution hypotheses mirror [consis_sound_post]*)
(*  verbatim (join [⊨ₛᵃ] + Δ₁-refinement [ad_refine_syn_f] + Δ₂-refinement  *)
(*  [ad_refine_pskl_f]) so that a sub-node's SOUNDNESS output feeds a        *)
(*  sub-node's OPTIMALITY input unchanged.                                  *)
(* ===================================================================== *)

Definition unify_optimal_post (F : atoms) (Θ0 : aenv) (α β : atom)
    (Θ1 : aenv) : Prop :=
  a_wf_aenv Θ0 -> a_flex_tvar Θ0 α -> a_flex_tvar Θ0 β ->
  forall θ1 θ Θ,
    is_id_msubst θ1 ->
    Θ0 ≤[ θ1 ] Θ1 ->
    Θ0 ≤[ θ ] Θ ->
    Θ ⊢ (msubst_lookup θ α) ≡ᵗ (msubst_lookup θ β) ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ.

Definition assign_optimal_post (F : atoms) (Θ0 Ξ : aenv) (α : atom)
    (P : pskl) (Θ1 : aenv) : Prop :=
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
  forall θ1 θ Θ,
    is_id_msubst θ1 ->
    (Ξ ++ Θ0) ≤[ θ1 ] Θ1 ->
    (Ξ ++ Θ0) ≤[ θ ] Θ ->
    empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θ P))
                 ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup θ α))) ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv (Ξ ++ Θ0) θ (msubst_compose ζ θ1) Θ.

Definition consis_optimal_post (F Δ1 Δ2 : atoms) (Θ0 : aenv)
    (P0 P Q : pskl) (Θ1 : aenv) : Prop :=
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (forall X, X `in` (Δ1 `union` Δ2) -> binds X abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 ->
  flex_above_free (Δ1 `union` Δ2) Θ0 ->
  forall θ1 θ Θ Qt Qb,
    is_id_msubst θ1 ->
    Θ0 ≤[ θ1 ] Θ1 ->
    bskl_to_pskl Qt = Q ->
    Θ0 ≤[ θ ] Θ ->
    empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θ P)) ≈ Qb ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl θ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl θ P) (bskl_to_pskl Qb) ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
      Θ ⨟ (Δ1 `union` Δ2) ⊢ₚᵣᵃ (msubst_bskl ζ Qt) ⊑ (bskl_to_pskl Qb).

(* ===================================================================== *)
(*  5.  REUSABLE FACTORING HELPERS (standalone, for the [OPT] bundle)      *)
(*                                                                        *)
(*  The (OPT) bundle's factoring conjunct is                              *)
(*    a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ.                           *)
(*  For the AXIOM/identity-output nodes (Ghost/GhostG/Unit/Rigid/GhostR)  *)
(*  the algorithm leaves the context unchanged (Θ1 = Θ0) and the natural  *)
(*  choice is ζ := θ, whereupon [msubst_compose θ θ1] must collapse to θ  *)
(*  — which needs [is_id_msubst θ1] (the corrected motive hypothesis).    *)
(*  These lemmas isolate that collapse.                                    *)
(* ===================================================================== *)

(** Reflexivity of metasubstitution equivalence: every increment is
    equivalent to itself (each flexible image is [≡ᵗ]-reflexive). *)
Lemma a_inc_equiv_refl : forall Θ0 θ Θ,
  Θ0 ≤[ θ ] Θ ->
  a_inc_equiv Θ0 θ θ Θ.
Proof.
  intros Θ0 θ Θ H; induction H.
  - apply a_inc_equiv__empty; auto.
  - apply a_inc_equiv__flex; auto.
    apply a_tyequiv__refl. apply mono_ptyp_lc; auto.
  - apply a_inc_equiv__flex_def; auto.
    apply a_tyequiv__refl. apply mono_ptyp_lc; auto.
  - apply a_inc_equiv__var; auto.
  - apply a_inc_equiv__var_skl; auto.
  - apply a_inc_equiv__tvar; auto.
Qed.

(** [dom θ ⊆ dom Θ0] for any increment [Θ0 ≤[θ] Θ]. *)
Lemma a_inc_dom_sub : forall Θ0 θ Θ,
  Θ0 ≤[ θ ] Θ ->
  dom θ [<=] dom Θ0.
Proof.
  intros Θ0 θ Θ H X HX.
  destruct (a_inc_dom_flex H HX) as [Hb | [τ Hb]]; apply binds_In in Hb; exact Hb.
Qed.

(** Prepending an entry outside the RIGHT (identity) multiplicand's domain
    does not change the composition. *)
Lemma msubst_compose_cons_l_id : forall α τ ζ θ1,
  is_id_msubst θ1 ->
  α `notin` dom θ1 ->
  msubst_compose ((α, τ) :: ζ) θ1 = msubst_compose ζ θ1.
Proof.
  induction θ1 as [ | [β b] θ1' IH ]; intros Hid Hni; simpl; auto.
  apply is_id_msubst_inv in Hid as [Heq Hid']; subst.
  simpl in Hni. simpl.
  rewrite IH by (first [ exact Hid' | clear - Hni; fsetdec ]).
  destruct (β == α) as [->|Hne]; [ exfalso; clear - Hni; fsetdec | reflexivity ].
Qed.

(** When [θ1] is an IDENTITY increment on the same source, composing any
    increment [θ] with it on the right is the identity: [θ ∘ θ1 = θ] as
    lists.  Both increments track [Θ0]'s flexibles in the same order. *)
Lemma msubst_compose_is_id_r : forall Θ0 θ1 Θ1 θ Θ,
  a_wf_aenv Θ0 ->
  is_id_msubst θ1 ->
  Θ0 ≤[ θ1 ] Θ1 ->
  Θ0 ≤[ θ ] Θ ->
  msubst_compose θ θ1 = θ.
Proof.
  intros Θ0 θ1 Θ1 θ Θ Hwf Hid Hinc1 Hinc; revert θ1 Θ1 Hid Hinc1.
  induction Hinc; intros θ1 Θ1 Hid Hinc1.
  - (* source nil : θ1 = nil *)
    inversion Hinc1; subst. reflexivity.
  - (* flex α *)
    inversion Hwf as [ | αh Θh Hnd Hwa | | | | ]; subst.
    inversion Hinc1 as [ | Θa θa Θb αa τa Hi1 Hw1 Hm1 | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    simpl. destruct (α == α) as [_ | Hne]; [ | contradiction ].
    assert (Hnid : α `notin` dom θa)
      by (pose proof (a_inc_dom_sub Hi1) as Hs; clear - Hs Hnd; fsetdec).
    rewrite (msubst_compose_cons_l_id _ _ Hid' Hnid).
    rewrite (IHHinc Hwa _ _ Hid' Hi1). reflexivity.
  - (* flex_def α := τ *)
    inversion Hwf as [ | | αh τh Θh Hnd Hwp Hm Hwa | | | ]; subst.
    inversion Hinc1 as [ | | Θa θa Θb αa τd τa He1 Hw1 Hm1 Heq1 | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    simpl. destruct (α == α) as [_ | Hne]; [ | contradiction ].
    assert (Hnid : α `notin` dom θa)
      by (pose proof (a_inc_dom_sub He1) as Hs; clear - Hs Hnd; fsetdec).
    rewrite (msubst_compose_cons_l_id _ _ Hid' Hnid).
    rewrite (IHHinc Hwa _ _ Hid' He1). reflexivity.
  - (* var typ *)
    inversion Hwf as [ | | | | xh Ah Θh Hnd Hwp Hwa | ]; subst.
    inversion Hinc1 as [ | | | Θa θa Θb Ξa xa Aa Hi1 Hs1 | | ]; subst.
    eapply IHHinc; eauto.
  - (* var skl *)
    inversion Hwf as [ | | | xh Ph Θh Hnd Hwp Hwa | | ]; subst.
    inversion Hinc1 as [ | | | | Θa θa Θb Ξa xa Pa Hi1 Hs1 | ]; subst.
    eapply IHHinc; eauto.
  - (* tvar *)
    inversion Hwf as [ | | | | | αh Θh Hnd Hwa ]; subst.
    inversion Hinc1 as [ | | | | | Θa θa Θb Ξa αa Hi1 Hs1 ]; subst.
    eapply IHHinc; eauto.
Qed.

(** The complete AXIOM-node factoring: at a node that leaves the context
    unchanged ([Θ1 = Θ0]) the competing solution's own substitution [θ]
    serves as the factoring [ζ]. *)
Lemma opt_axiom_factor : forall Θ0 θ1 θ Θ,
  a_wf_aenv Θ0 ->
  is_id_msubst θ1 ->
  Θ0 ≤[ θ1 ] Θ0 ->
  Θ0 ≤[ θ ] Θ ->
  Θ0 ≤[ θ ] Θ /\ a_inc_equiv Θ0 θ (msubst_compose θ θ1) Θ.
Proof.
  intros Θ0 θ1 θ Θ Hwf Hid Hinc1 Hinc.
  split; [ exact Hinc | ].
  rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
  apply a_inc_equiv_refl; exact Hinc.
Qed.
