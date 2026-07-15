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
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_precise_recover.

Set Implicit Arguments.

(* ===================================================================== *)
(*  1.  Consistency                                                       *)
(* ===================================================================== *)

(** A problem of consistency is a tuple (Θ₀; P₀; P) where P₀ and P are
    well-formed in Θ₀.  (The paper's external wf condition, made a premise.) *)
Definition a_consis_problem (Θ0 : aenv) (P0 P : pskl) : Prop :=
  a_wf_aenv Θ0 /\ a_wf_pskl Θ0 P0 /\ a_wf_pskl Θ0 P.

(* ---------------------------------------------------------------------- *)
(*  EXTERNAL-WF SIDE CONDITION on the solution target (validated 2026-07-15, *)
(*  [paper-gap]; docs/WF-SIDE-CONDITIONS.md, Solution target).               *)
(*                                                                          *)
(*  Each solution's target context Θ1 REQUIRES [a_wf_aenv Θ1].  This is the  *)
(*  paper's meaning of a solution: full-algo-spec.tex / algorithmic.tex:89  *)
(*  defines the increment as a finite map θ from flexible variables in Θ    *)
(*  to WELL-FORMED MONOTYPES IN Θ' — so the ambient target Θ' is a          *)
(*  well-formed context BY CONSTRUCTION.  The mechanized [a_inc] does not    *)
(*  enforce it ([a_inc__empty]/[a_suffix] base can rest on ill-formed defs), *)
(*  so it must be carried on the solution.  It is an external side          *)
(*  condition, NOT a weakening.                                             *)
(*                                                                          *)
(*  MACHINE-CHECKED NECESSITY (C-Unit counterexample).  Inverting the        *)
(*  competing join [empty ⨟ Θ ⊨ₛᵃ uskl_unit ≈ Qb] yields a [flex_r] branch  *)
(*  (Θ has a defined flex α ≔ τ, Qb = bskl_var_f α), residual goal          *)
(*  [pskl_unit ⊑ pskl_var_f α], dischargeable ONLY with [consis_mono_join]   *)
(*  — which needs [a_wf_aenv Θ].  And [a_wf_aenv Θ] is not otherwise         *)
(*  derivable from [a_inc].  So the wf of the (competing) solution target is  *)
(*  load-bearing; the corresponding motive hypotheses discharge it from      *)
(*  each competing solution's own new wf conjunct.                           *)
(* ---------------------------------------------------------------------- *)

(** A solution is a tuple (Θ₀ ⊑[θ₁] Θ₁; P₁) such that the substituted input is
    consistent with P₁, and P₁ is a refinement of the substituted input
    skeleton.  Its target Θ₁ is well-formed (external-wf side condition). *)
Definition a_consis_solution
    (Θ0 : aenv) (P0 P : pskl) (θ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  empty ⨟ Θ1 ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θ1 P)) ≈ P1 /\
  Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl θ1 P0)) ⊳ P1 /\
  a_wf_aenv Θ1.

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

(** External-wf side condition on the target Θ1 (see the block above). *)
Definition a_unify_solution
    (Θ0 : aenv) (α β : atom) (θ1 : metasubst) (Θ1 : aenv) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  Θ1 ⊢ (msubst_lookup θ1 α) ≡ᵗ (msubst_lookup θ1 β) /\
  a_wf_aenv Θ1.

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

(** External-wf side condition on the target Θ1 (see the block above). *)
Definition a_assign_solution
    (Θ0 Ξ : aenv) (α : atom) (P : pskl) (θ1 : metasubst) (Θ1 : aenv) : Prop :=
  (Ξ ++ Θ0) ≤[ θ1 ] Θ1 /\
  empty ⨟ Θ1 ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θ1 P))
                ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup θ1 α))) /\
  a_wf_aenv Θ1.

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
    a_wf_aenv Θ ->  (* external-wf side condition on the competing solution's target *)
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
    a_wf_aenv Θ ->  (* external-wf side condition on the competing solution's target *)
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
    a_wf_aenv Θ ->  (* external-wf side condition on the competing solution's target *)
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

(** An IDENTITY increment is determined by its SOURCE alone: two id-increments
    out of the same [Θ0] are equal as lists (the target is irrelevant — every
    image is the identity, and both track [Θ0]'s flexibles in the same order).
    This is what lets a sub-node's soundness [⊴]-witness stand in for the
    algorithm's own id-witness on the walk cases. *)
Lemma is_id_inc_unique : forall Θ0 θ1 Θ1,
  Θ0 ≤[ θ1 ] Θ1 -> is_id_msubst θ1 ->
  forall θ2 Θ2, Θ0 ≤[ θ2 ] Θ2 -> is_id_msubst θ2 -> θ1 = θ2.
Proof.
  intros Θ0 θ1 Θ1 Hinc1; induction Hinc1; intros Hid1 θ2 Θ2 Hinc2 Hid2.
  - inversion Hinc2; subst; reflexivity.
  - apply is_id_msubst_inv in Hid1 as [Heq1 Hid1']; subst.
    inversion Hinc2 as [ | Θa θa Θb αa τa Hinca Hwfa Hma [Heqα Heqθ2] Heqt
                       | | | | ]; subst.
    apply is_id_msubst_inv in Hid2 as [Heq2 Hid2']; subst.
    f_equal. eapply IHHinc1; eauto.
  - apply is_id_msubst_inv in Hid1 as [Heq1 Hid1']; subst.
    inversion Hinc2 as [ | | Θa θa Θb αa τd τa Hinca Hwfa Hma Heqda [Heqα Heqθ2] Heqt
                       | | | ]; subst.
    apply is_id_msubst_inv in Hid2 as [Heq2 Hid2']; subst.
    f_equal. eapply IHHinc1; eauto.
  - inversion Hinc2 as [ | | | Θa θa Θb Ξa xa Aa Hinca Hsa Heqsrc Heqt | | ]; subst.
    eapply IHHinc1; eauto.
  - inversion Hinc2 as [ | | | | Θa θa Θb Ξa xa Pa Hinca Hsa Heqsrc Heqt | ]; subst.
    eapply IHHinc1; eauto.
  - inversion Hinc2 as [ | | | | | Θa θa Θb Ξa αa Hinca Hsa Heqsrc Heqt ]; subst.
    eapply IHHinc1; eauto.
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

(* ===================================================================== *)
(*  6.  THE a_inc_equiv COMPOSITION GLUE  (the structural-case crux)        *)
(*                                                                        *)
(*  The structural consistency rules (Arrow, ForallInh/Syn, UnivGhost..)  *)
(*  each split a node into two (or a cofinite family of) sub-nodes and     *)
(*  must COMPOSE the two sub-node factorings into one.  With                *)
(*    sub1 :  a_inc_equiv Θ0   θ  (msubst_compose ζ1 θ1a) Θ                 *)
(*    sub2 :  a_inc_equiv Θmid ζ1 (msubst_compose ζ2 θ1b) Θ                 *)
(*  the composed factoring is  a_inc_equiv Θ0 θ (msubst_compose ζ2 θ1a) Θ   *)
(*  (using that the id-witnesses θ1a/θ1b compose away).  Built from a        *)
(*  CONGRUENCE (right-composition with an increment) and TRANSITIVITY of    *)
(*  a_inc_equiv — modelled on [a_inc_compose] (prop_compose.v:695).         *)
(* ===================================================================== *)

(** Two equivalent metasubstitutions act [≡ᵗ]-equivalently on a wf MONOtype.
    (Monotypes have no [∀], so no binder/opening obligation arises — this is
    why the congruence below can stay first-order.) *)
Lemma a_inc_equiv_msubst_mono : forall Θmid θ1 θ2 Θ τ,
  a_inc_equiv Θmid θ1 θ2 Θ ->
  a_wf_aenv Θmid ->
  a_wf_ptyp Θmid τ ->
  mono_ptyp τ ->
  Θ ⊢ (msubst_ptyp θ1 τ) ≡ᵗ (msubst_ptyp θ2 τ).
Proof.
  intros Θmid θ1 θ2 Θ τ Hie Hwf Hwt Hm; revert Hwt; induction Hm; intros Hwt.
  - (* unit *) simpl. apply a_tyequiv__refl. constructor.
  - (* var X *) simpl. inversion Hwt; subst.
    eapply prop_normal.a_inc_equiv_lookup; [ exact Hie | exact Hwf | assumption ].
  - (* arrow A1 A2 *) simpl. inversion Hwt; subst.
    apply a_tyequiv__arrow; [ apply IHHm1 | apply IHHm2 ]; assumption.
Qed.

(** A unique middle binding forces the two flanking decompositions to agree
    (Metalib [uniq_mid], spelled with explicit arguments). *)
Lemma aenv_mid_split : forall (E1 : aenv) x b1 F1 E2 b2 F2,
  uniq (E1 ++ (x ~ b1) ++ F1) ->
  E1 ++ (x ~ b1) ++ F1 = E2 ++ (x ~ b2) ++ F2 ->
  E1 = E2 /\ b1 = b2 /\ F1 = F2.
Proof.
  intros E1 x b1 F1 E2 b2 F2 Hu Heq.
  eapply uniq_mid; eauto.
Qed.

(** Head inversions for [a_inc_equiv] at the three binder entries: they carry
    [θ1]/[θ2] over unchanged and split the target at a suffix. *)
Lemma a_inc_equiv_tvar_inv : forall α Θ0 θ1 θ2 Θ,
  a_inc_equiv ((α ~ abind_tvar) ++ Θ0) θ1 θ2 Θ ->
  exists Ξ Θ', Θ = Ξ ++ (α ~ abind_tvar) ++ Θ'
             /\ a_suffix Ξ /\ a_inc_equiv Θ0 θ1 θ2 Θ'.
Proof. intros * H; inversion H; subst; eauto 8. Qed.

Lemma a_inc_equiv_var_typ_inv : forall x A Θ0 θ1 θ2 Θ,
  a_inc_equiv ((x ~ abind_var_typ A) ++ Θ0) θ1 θ2 Θ ->
  exists Ξ Θ', Θ = Ξ ++ (x ~ abind_var_typ (msubst_ptyp θ1 A)) ++ Θ'
             /\ a_suffix Ξ /\ a_inc_equiv Θ0 θ1 θ2 Θ'.
Proof. intros * H; inversion H; subst; eauto 8. Qed.

Lemma a_inc_equiv_var_skl_inv : forall x P Θ0 θ1 θ2 Θ,
  a_inc_equiv ((x ~ abind_var_skl P) ++ Θ0) θ1 θ2 Θ ->
  exists Ξ Θ', Θ = Ξ ++ (x ~ abind_var_skl (msubst_pskl θ1 P)) ++ Θ'
             /\ a_suffix Ξ /\ a_inc_equiv Θ0 θ1 θ2 Θ'.
Proof. intros * H; inversion H; subst; eauto 8. Qed.

(** An all-flexible source maps, under [a_inc_equiv], to an all-flexible target
    (mirror of [a_inc_suffix_target]). *)
Lemma a_inc_equiv_suffix_target : forall Θ ρ1 ρ2 Θ',
  a_inc_equiv Θ ρ1 ρ2 Θ' -> a_suffix Θ -> a_suffix Θ'.
Proof.
  intros Θ ρ1 ρ2 Θ' Hie; induction Hie; intros Hsuf; auto;
    inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst; auto; inversion Hb.
Qed.

(** Peel an all-flexible suffix [Ξ] off the source of an [a_inc_equiv] and its
    two witnessing increments simultaneously — the three list-heads coincide
    (one shared [ρ1]/[ρ2]), so the splits stay consistent for free.  Mirrors
    [a_inc_peel_suffix] (prop_compose.v:629) + [a_inc_strengthen_suffix_src]. *)
Lemma a_inc_equiv_inc_peel_suffix : forall Ξ Θ ρ1 ρ2 Θ',
  a_suffix Ξ ->
  a_inc_equiv (Ξ ++ Θ) ρ1 ρ2 Θ' ->
  (Ξ ++ Θ) ≤[ ρ1 ] Θ' ->
  (Ξ ++ Θ) ≤[ ρ2 ] Θ' ->
  exists ρ1b ρ2b,
    a_inc_equiv Θ ρ1b ρ2b Θ' /\ Θ ≤[ ρ1b ] Θ' /\ Θ ≤[ ρ2b ] Θ'
    /\ (exists p1, ρ1 = p1 ++ ρ1b /\ dom p1 [=] dom Ξ)
    /\ (exists p2, ρ2 = p2 ++ ρ2b /\ dom p2 [=] dom Ξ).
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ]; intros Θ ρ1 ρ2 Θ' Hsuf Hie Hi1 Hi2.
  - simpl in *. exists ρ1, ρ2.
    repeat split; auto;
      [ exists (@nil (atom * ptyp)) | exists (@nil (atom * ptyp)) ];
      simpl; split; solve [ reflexivity | clear; fsetdec ].
  - inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst.
    inversion Hb; subst; simpl in Hie, Hi1, Hi2.
    + (* flex_mono head *)
      inversion Hie as [ | S t1 t2 T aa u1 u2 Hie' Heq | | | | ]; subst.
      inversion Hi1; subst. inversion Hi2; subst.
      match goal with H : a_inc (Ξ' ++ Θ) t1 Θ' |- _ => rename H into Hi1' end.
      match goal with H : a_inc (Ξ' ++ Θ) t2 Θ' |- _ => rename H into Hi2' end.
      destruct (IH _ _ _ _ Hsuf' Hie' Hi1' Hi2')
        as [ρ1b [ρ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hd1]] [p2 [Hp2 Hd2]]]]]]]].
      exists ρ1b, ρ2b. repeat split; auto.
      * exists ((a, u1) :: p1). rewrite Hp1. simpl.
        split; [ reflexivity | rewrite Hd1; clear; fsetdec ].
      * exists ((a, u2) :: p2). rewrite Hp2. simpl.
        split; [ reflexivity | rewrite Hd2; clear; fsetdec ].
    + (* flex_mono_def head *)
      inversion Hie as [ | | S t1 t2 T aa td u1 u2 Hie' Heq Hdf | | | ]; subst.
      inversion Hi1; subst. inversion Hi2; subst.
      match goal with H : a_inc (Ξ' ++ Θ) t1 Θ' |- _ => rename H into Hi1' end.
      match goal with H : a_inc (Ξ' ++ Θ) t2 Θ' |- _ => rename H into Hi2' end.
      destruct (IH _ _ _ _ Hsuf' Hie' Hi1' Hi2')
        as [ρ1b [ρ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hd1]] [p2 [Hp2 Hd2]]]]]]]].
      exists ρ1b, ρ2b. repeat split; auto.
      * exists ((a, u1) :: p1). rewrite Hp1. simpl.
        split; [ reflexivity | rewrite Hd1; clear; fsetdec ].
      * exists ((a, u2) :: p2). rewrite Hp2. simpl.
        split; [ reflexivity | rewrite Hd2; clear; fsetdec ].
Qed.

(** TRANSITIVITY of metasubstitution equivalence (through a fixed target).
    The [var]/[var_skl] cases use [aenv_mid_split] to realign the two
    target decompositions at the unique term-variable position. *)
Lemma a_inc_equiv_trans : forall Θ0 θa θb Θ,
  a_inc_equiv Θ0 θa θb Θ ->
  forall θc,
  a_wf_aenv Θ ->
  a_inc_equiv Θ0 θb θc Θ ->
  a_inc_equiv Θ0 θa θc Θ.
Proof.
  intros Θ0 θa θb Θ Hab; induction Hab; intros θc Hwf Hbc.
  - (* empty *)
    inversion Hbc; subst. apply a_inc_equiv__empty; auto.
  - (* flex α *)
    match goal with He : _ ⊢ _ ≡ᵗ _ |- _ => rename He into Hab_eq end.
    inversion Hbc as [ | Sb tb tc Tb ac t2b t3 Hbc' Heqc | | | | ]; subst.
    apply a_inc_equiv__flex.
    + apply IHHab; auto.
    + eapply a_tyequiv__trans; [ exact Hab_eq | exact Heqc ].
  - (* flex_def α := τ *)
    match goal with Hd : _ ⊢ _ ≡ᵗ (msubst_ptyp _ _) |- _ => rename Hd into Hab_def end.
    match goal with He : _ ⊢ _ ≡ᵗ _ |- _ =>
      lazymatch type of He with
      | _ ⊢ _ ≡ᵗ (msubst_ptyp _ _) => fail
      | _ => rename He into Hab_eq
      end end.
    inversion Hbc as [ | | Sb tb tc Tb ac td t2b t3 Hbc' Heqc Hdefc | | | ]; subst.
    apply a_inc_equiv__flex_def.
    + apply IHHab; auto.
    + eapply a_tyequiv__trans; [ exact Hab_eq | exact Heqc ].
    + exact Hab_def.
  - (* var_typ x : realign, then rebuild *)
    destruct (a_inc_equiv_var_typ_inv Hbc) as [Xic [Tc [Heqt [Hsc Hrec]]]].
    pose proof (a_wf_aenv_uniq_local Hwf) as Hu.
    destruct (aenv_mid_split _ _ _ _ _ _ _ Hu Heqt) as [HeqΞ [Heqb HeqΘ]].
    subst.
    apply a_wf_aenv_strip_prefix_local in Hwf.
    inversion Hwf; subst.
    apply a_inc_equiv__var; [ apply IHHab; assumption | assumption ].
  - (* var_skl x *)
    destruct (a_inc_equiv_var_skl_inv Hbc) as [Xic [Tc [Heqt [Hsc Hrec]]]].
    pose proof (a_wf_aenv_uniq_local Hwf) as Hu.
    destruct (aenv_mid_split _ _ _ _ _ _ _ Hu Heqt) as [HeqΞ [Heqb HeqΘ]].
    subst.
    apply a_wf_aenv_strip_prefix_local in Hwf.
    inversion Hwf; subst.
    apply a_inc_equiv__var_skl; [ apply IHHab; assumption | assumption ].
  - (* tvar α *)
    destruct (a_inc_equiv_tvar_inv Hbc) as [Xic [Tc [Heqt [Hsc Hrec]]]].
    pose proof (a_wf_aenv_uniq_local Hwf) as Hu.
    destruct (aenv_mid_split _ _ _ _ _ _ _ Hu Heqt) as [HeqΞ [Heqb HeqΘ]].
    subst.
    apply a_wf_aenv_strip_prefix_local in Hwf.
    inversion Hwf; subst.
    apply a_inc_equiv__tvar; [ apply IHHab; assumption | assumption ].
Qed.

(** RIGHT-COMPOSITION CONGRUENCE: applying a fixed source-increment [σ] to two
    equivalent metasubstitutions preserves the equivalence.  Induction on [σ],
    mirroring [a_inc_compose] (prop_compose.v:695); the binder cases peel the
    suffix off the [a_inc_equiv] and its two witnessing increments together
    ([a_inc_equiv_inc_peel_suffix]) and realign the three target
    decompositions at the unique term-variable via [aenv_mid_split]. *)
Lemma a_inc_equiv_compose : forall Θ0 θ Θmid,
  Θ0 ≤[ θ ] Θmid ->
  a_wf_aenv Θ0 -> a_wf_aenv Θmid ->
  forall ρ1 ρ2 Θ,
  a_wf_aenv Θ ->
  a_inc_equiv Θmid ρ1 ρ2 Θ ->
  Θmid ≤[ ρ1 ] Θ -> Θmid ≤[ ρ2 ] Θ ->
  a_inc_equiv Θ0 (msubst_compose ρ1 θ) (msubst_compose ρ2 θ) Θ.
Proof.
  intros Θ0 θ Θmid Hθ; induction Hθ;
    intros Hwf0 Hwf1 ρ1 ρ2 Θt HwfT Hie Hi1 Hi2.
  - (* empty : source all-flexible, so target all-flexible *)
    simpl. apply a_inc_equiv__empty.
    eapply a_inc_equiv_suffix_target; [ exact Hie | assumption ].
  - (* flex α *)
    inversion Hwf0 as [ | αh Θh Hnd Hwa | | | | ]; subst.
    simpl. apply a_inc_equiv__flex.
    + apply IHHθ; auto.
    + eapply a_inc_equiv_msubst_mono;
        [ exact Hie | exact Hwf1 | eassumption | assumption ].
  - (* flex_def α := τ *)
    inversion Hwf0 as [ | | αh τh Θh Hnd Hwp Hm Hwa | | | ]; subst.
    simpl. apply a_inc_equiv__flex_def.
    + apply IHHθ; auto.
    + eapply a_inc_equiv_msubst_mono;
        [ exact Hie | exact Hwf1 | eassumption | assumption ].
    + rewrite msubst_ptyp_compose.
      * eapply a_tyequiv_msubst; [ eassumption | exact Hwf1 | exact Hi1 ].
      * intros X HX.
        eapply a_inc_compose_vis;
          [ exact Hθ | exact Hi1 | exact Hwa | exact Hwf1
          | eapply a_wf_ptyp_ftv_tvarish; eauto ].
  - (* var_typ x *)
    inversion Hwf0 as [ | | | | xh Ah Θh Hnd Hwp Hwa | ]; subst.
    assert (Hwf1t : a_wf_aenv Θ') by
      (apply a_wf_aenv_strip_prefix_local in Hwf1;
       inversion Hwf1; subst; assumption).
    assert (Hdisj : forall X, X `in` dom Ξ -> X `notin` dom Θ').
    { intros X HX. pose proof (a_wf_aenv_uniq_local Hwf1) as Hu1.
      clear - Hu1 HX. solve_uniq. }
    edestruct a_inc_equiv_inc_peel_suffix
      as [ρ1b [ρ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hdp1]] [p2 [Hp2 Hdp2]]]]]]]];
      [ exact H | exact Hie | exact Hi1 | exact Hi2 | ].
    destruct (a_inc_equiv_var_typ_inv Hie2) as [Ξe [Te [Heqe [Hse Hie3]]]].
    destruct (a_inc_var_inv Hib1) as [Ξ1 [T1 [Heq1 [Hs1 Hib1']]]].
    destruct (a_inc_var_inv Hib2) as [Ξ2 [T2 [Heq2 [Hs2 Hib2']]]].
    pose proof (a_wf_aenv_uniq_local HwfT) as HuT.
    rewrite Heqe in HuT.
    assert (HeqE1 : Ξe ++ (x ~ abind_var_typ (msubst_ptyp ρ1b (msubst_ptyp θ A))) ++ Te
                  = Ξ1 ++ (x ~ abind_var_typ (msubst_ptyp ρ1b (msubst_ptyp θ A))) ++ T1)
      by (rewrite <- Heqe; exact Heq1).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE1) as [HE1 [_ HT1]]; subst T1.
    assert (HeqE2 : Ξe ++ (x ~ abind_var_typ (msubst_ptyp ρ1b (msubst_ptyp θ A))) ++ Te
                  = Ξ2 ++ (x ~ abind_var_typ (msubst_ptyp ρ2b (msubst_ptyp θ A))) ++ T2)
      by (rewrite <- Heqe; exact Heq2).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE2) as [HE2 [_ HT2]]; subst T2.
    assert (Hc1 : msubst_compose ρ1 θ = msubst_compose ρ1b θ)
      by (rewrite Hp1; eapply msubst_compose_peel;
          [ exact Hθ | intros X HX; apply Hdisj; rewrite <- Hdp1; exact HX ]).
    assert (Hc2 : msubst_compose ρ2 θ = msubst_compose ρ2b θ)
      by (rewrite Hp2; eapply msubst_compose_peel;
          [ exact Hθ | intros X HX; apply Hdisj; rewrite <- Hdp2; exact HX ]).
    rewrite Hc1, Hc2, Heqe.
    assert (HA : msubst_ptyp (msubst_compose ρ1b θ) A
               = msubst_ptyp ρ1b (msubst_ptyp θ A)).
    { apply msubst_ptyp_compose. intros X HX.
      eapply a_inc_compose_vis;
        [ exact Hθ | exact Hib1' | exact Hwa | exact Hwf1t
        | eapply a_wf_ptyp_ftv_tvarish; eauto ]. }
    rewrite <- HA.
    apply a_inc_equiv__var; [ | exact Hse ].
    assert (HwfTe : a_wf_aenv Te).
    { rewrite Heqe in HwfT. apply a_wf_aenv_strip_prefix_local in HwfT.
      inversion HwfT; subst; assumption. }
    apply IHHθ; auto.
  - (* var_skl x *)
    inversion Hwf0 as [ | | | xh Ph Θh Hnd Hwp Hwa | | ]; subst.
    assert (Hwf1t : a_wf_aenv Θ') by
      (apply a_wf_aenv_strip_prefix_local in Hwf1;
       inversion Hwf1; subst; assumption).
    assert (Hdisj : forall X, X `in` dom Ξ -> X `notin` dom Θ').
    { intros X HX. pose proof (a_wf_aenv_uniq_local Hwf1) as Hu1.
      clear - Hu1 HX. solve_uniq. }
    edestruct a_inc_equiv_inc_peel_suffix
      as [ρ1b [ρ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hdp1]] [p2 [Hp2 Hdp2]]]]]]]];
      [ exact H | exact Hie | exact Hi1 | exact Hi2 | ].
    destruct (a_inc_equiv_var_skl_inv Hie2) as [Ξe [Te [Heqe [Hse Hie3]]]].
    destruct (a_inc_var_skl_inv Hib1) as [Ξ1 [T1 [Heq1 [Hs1 Hib1']]]].
    destruct (a_inc_var_skl_inv Hib2) as [Ξ2 [T2 [Heq2 [Hs2 Hib2']]]].
    pose proof (a_wf_aenv_uniq_local HwfT) as HuT.
    rewrite Heqe in HuT.
    assert (HeqE1 : Ξe ++ (x ~ abind_var_skl (msubst_pskl ρ1b (msubst_pskl θ P))) ++ Te
                  = Ξ1 ++ (x ~ abind_var_skl (msubst_pskl ρ1b (msubst_pskl θ P))) ++ T1)
      by (rewrite <- Heqe; exact Heq1).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE1) as [HE1 [_ HT1]]; subst T1.
    assert (HeqE2 : Ξe ++ (x ~ abind_var_skl (msubst_pskl ρ1b (msubst_pskl θ P))) ++ Te
                  = Ξ2 ++ (x ~ abind_var_skl (msubst_pskl ρ2b (msubst_pskl θ P))) ++ T2)
      by (rewrite <- Heqe; exact Heq2).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE2) as [HE2 [_ HT2]]; subst T2.
    assert (Hc1 : msubst_compose ρ1 θ = msubst_compose ρ1b θ)
      by (rewrite Hp1; eapply msubst_compose_peel;
          [ exact Hθ | intros X HX; apply Hdisj; rewrite <- Hdp1; exact HX ]).
    assert (Hc2 : msubst_compose ρ2 θ = msubst_compose ρ2b θ)
      by (rewrite Hp2; eapply msubst_compose_peel;
          [ exact Hθ | intros X HX; apply Hdisj; rewrite <- Hdp2; exact HX ]).
    rewrite Hc1, Hc2, Heqe.
    assert (HP : msubst_pskl (msubst_compose ρ1b θ) P
               = msubst_pskl ρ1b (msubst_pskl θ P)).
    { apply msubst_pskl_compose. intros X HX.
      eapply a_inc_compose_vis;
        [ exact Hθ | exact Hib1' | exact Hwa | exact Hwf1t
        | eapply a_wf_pskl_ftv_tvarish; eauto ]. }
    rewrite <- HP.
    apply a_inc_equiv__var_skl; [ | exact Hse ].
    assert (HwfTe : a_wf_aenv Te).
    { rewrite Heqe in HwfT. apply a_wf_aenv_strip_prefix_local in HwfT.
      inversion HwfT; subst; assumption. }
    apply IHHθ; auto.
  - (* tvar α *)
    inversion Hwf0 as [ | | | | | αh Θh Hnd Hwa ]; subst.
    assert (Hwf1t : a_wf_aenv Θ') by
      (apply a_wf_aenv_strip_prefix_local in Hwf1;
       inversion Hwf1; subst; assumption).
    edestruct a_inc_equiv_inc_peel_suffix
      as [ρ1b [ρ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hdp1]] [p2 [Hp2 Hdp2]]]]]]]];
      [ exact H | exact Hie | exact Hi1 | exact Hi2 | ].
    assert (Hdisj : forall X, X `in` dom Ξ -> X `notin` dom Θ').
    { intros X HX. pose proof (a_wf_aenv_uniq_local Hwf1) as Hu1.
      clear - Hu1 HX. solve_uniq. }
    destruct (a_inc_equiv_tvar_inv Hie2) as [Ξe [Te [Heqe [Hse Hie3]]]].
    destruct (a_inc_tvar_inv Hib1) as [Ξ1 [T1 [Heq1 [Hs1 Hib1']]]].
    destruct (a_inc_tvar_inv Hib2) as [Ξ2 [T2 [Heq2 [Hs2 Hib2']]]].
    pose proof (a_wf_aenv_uniq_local HwfT) as HuT.
    rewrite Heqe in HuT.
    assert (HeqE1 : Ξe ++ (α ~ abind_tvar) ++ Te = Ξ1 ++ (α ~ abind_tvar) ++ T1)
      by (rewrite <- Heqe; exact Heq1).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE1) as [HE1 [_ HT1]]; subst T1.
    assert (HeqE2 : Ξe ++ (α ~ abind_tvar) ++ Te = Ξ2 ++ (α ~ abind_tvar) ++ T2)
      by (rewrite <- Heqe; exact Heq2).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE2) as [HE2 [_ HT2]]; subst T2.
    assert (Hc1 : msubst_compose ρ1 θ = msubst_compose ρ1b θ)
      by (rewrite Hp1; eapply msubst_compose_peel;
          [ exact Hθ | intros X HX; apply Hdisj; rewrite <- Hdp1; exact HX ]).
    assert (Hc2 : msubst_compose ρ2 θ = msubst_compose ρ2b θ)
      by (rewrite Hp2; eapply msubst_compose_peel;
          [ exact Hθ | intros X HX; apply Hdisj; rewrite <- Hdp2; exact HX ]).
    rewrite Hc1, Hc2, Heqe.
    apply a_inc_equiv__tvar; [ | exact Hse ].
    assert (HwfTe : a_wf_aenv Te).
    { rewrite Heqe in HwfT. apply a_wf_aenv_strip_prefix_local in HwfT.
      inversion HwfT; subst; assumption. }
    apply IHHθ; auto.
Qed.

(* ===================================================================== *)
(*  The composed factoring, assembled from CONGRUENCE + TRANSITIVITY.      *)
(* ===================================================================== *)

(** With [θ1a], [θ1b] both identity metasubstitutions and every [θ1a]-flexible
    still [θ1b]-flexible, an inner id-composition on the right collapses:
    [(ζ∘θ1b)∘θ1a = ζ∘θ1a].  (The domain side condition rules out a [θ1a]-flex
    that was rigidified by [θ1b]'s source-extension; in the bundle it is the
    flex-preservation carried by [Θ0 ⊴ Θmid ⊴ Θfin].) *)
Lemma msubst_compose_id_compose : forall θ1a θ1b ζ,
  is_id_msubst θ1a -> is_id_msubst θ1b ->
  (forall α, α `in` dom θ1a -> α `in` dom θ1b) ->
  msubst_compose (msubst_compose ζ θ1b) θ1a = msubst_compose ζ θ1a.
Proof.
  intros θ1a θ1b ζ Hida Hidb Hdom.
  apply List.map_ext_in.
  intros [α τ] Hin. simpl. f_equal.
  assert (Hτ : τ = ptyp_var_f α).
  { unfold is_id_msubst in Hida. rewrite Forall_forall in Hida.
    specialize (Hida _ Hin). unfold is_id_entry in Hida. exact Hida. }
  subst τ. simpl.
  rewrite msubst_lookup_compose
    by (left; apply Hdom; eapply binds_In; exact Hin).
  rewrite msubst_lookup_id by exact Hidb. reflexivity.
Qed.

(** THE GLUE.  Two adjacent sub-node factorings (a consistency Arrow, a Forall,
    a UnivGhost split) compose into the whole node's factoring.  [θ1a]/[θ1b] are
    the two sub-nodes' identity solution-witnesses. *)
Lemma a_inc_equiv_glue : forall Θ0 Θmid Θfin Θ θ θ1a θ1b ζ1 ζ2,
  a_wf_aenv Θ0 -> a_wf_aenv Θmid -> a_wf_aenv Θfin -> a_wf_aenv Θ ->
  is_id_msubst θ1a -> is_id_msubst θ1b ->
  (forall α, α `in` dom θ1a -> α `in` dom θ1b) ->
  Θ0 ≤[ θ1a ] Θmid ->
  Θmid ≤[ θ1b ] Θfin ->
  Θmid ≤[ ζ1 ] Θ ->
  Θfin ≤[ ζ2 ] Θ ->
  a_inc_equiv Θ0 θ (msubst_compose ζ1 θ1a) Θ ->
  a_inc_equiv Θmid ζ1 (msubst_compose ζ2 θ1b) Θ ->
  a_inc_equiv Θ0 θ (msubst_compose ζ2 θ1a) Θ.
Proof.
  intros Θ0 Θmid Θfin Θ θ θ1a θ1b ζ1 ζ2
         Hwf0 Hwfm Hwff HwfT Hida Hidb Hdom Ha Hb Hζ1 Hζ2 Hsub1 Hsub2.
  (* the second increment through Θfin *)
  assert (Hζ2b : Θmid ≤[ msubst_compose ζ2 θ1b ] Θ)
    by (eapply a_inc_compose; [ exact Hb | exact Hwfm | exact Hwff | exact Hζ2 ]).
  (* congruence: push σ = θ1a onto sub2 *)
  pose proof (a_inc_equiv_compose Ha Hwf0 Hwfm HwfT Hsub2 Hζ1 Hζ2b) as Hcong.
  (* simplify the inner id-composition *)
  rewrite (msubst_compose_id_compose ζ2 Hida Hidb Hdom) in Hcong.
  (* transitivity with sub1 *)
  eapply a_inc_equiv_trans; [ exact Hsub1 | exact HwfT | exact Hcong ].
Qed.

(* ===================================================================== *)
(*  7.  THE 28-CASE MUTUAL OPTIMALITY BUNDLE                               *)
(*                                                                        *)
(*  Same shape as the green soundness bundle [a_assign_unify_consis_sound]  *)
(*  (prop_consis_sound.v:2562): mutual induction on the algorithmic         *)
(*  derivation via [a_assign_unify_consis_mutind].  The a_inc_equiv         *)
(*  factoring conjunct of every STRUCTURAL consistency case is discharged   *)
(*  by [a_inc_equiv_glue]; the FLEXIBLE cases' precision conjunct by         *)
(*  [consis_precise_via_join] / [consis_precise_via_refine]                 *)
(*  (prop_precise_recover.v); the AXIOM/identity-output cases by             *)
(*  [opt_axiom_factor].                                                     *)
(*                                                                          *)
(*  WORK-IN-PROGRESS.  Per the relaxed rule for this bundle, cases not yet   *)
(*  finished are [admit]-ed with an honest per-case marker (rule name +      *)
(*  what remains).  Every admitted goal is TRUE (it mirrors the             *)
(*  corresponding green soundness case plus the ζ-construction), just not    *)
(*  yet mechanized.  Print Assumptions therefore lists the admit axiom      *)
(*  until they are closed.  The GLUE and all factoring helpers above are     *)
(*  fully Qed'd and axiom-free.                                             *)
(* ===================================================================== *)

Theorem a_assign_unify_consis_optimal :
  (forall F Θ0 Ξ α P Θ1,
     a_assign F Θ0 Ξ α P Θ1 -> assign_optimal_post F Θ0 Ξ α P Θ1) /\
  (forall F Θ0 α β Θ1,
     a_unify F Θ0 α β Θ1 -> unify_optimal_post F Θ0 α β Θ1) /\
  (forall F Δ1 Δ2 Θ0 P0 P Q Θ1,
     a_consis F Δ1 Δ2 Θ0 P0 P Q Θ1 -> consis_optimal_post F Δ1 Δ2 Θ0 P0 P Q Θ1).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun F Θ0 Ξ α P Θ1 _ => assign_optimal_post F Θ0 Ξ α P Θ1)
           (fun F Θ0 α β Θ1 _ => unify_optimal_post F Θ0 α β Θ1)
           (fun F Δ1 Δ2 Θ0 P0 P Q Θ1 _ =>
              consis_optimal_post F Δ1 Δ2 Θ0 P0 P Q Θ1)).
  (* ================= a_assign (8) ================= *)
  - (* Assign-UnivGhost-Id : identity leaf, Ξ=nil, so Θ1 = source; ζ:=ρ. *)
    intros F Θ0 α. unfold assign_optimal_post.
    intros Hdecl Hwf HwfP ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Hjoin.
    simpl_env in *. exists ρ.
    apply (opt_axiom_factor Hwf Hid Hinc1 Hinc).
  - admit. (* TODO[optimality]: Assign-SolveM; the guessed β̄ extends Θ1; true;
              blocked on building ζ from guess^TY's monotype + occurs check. *)
  - admit. (* TODO[optimality]: Assign-Assign; consistency sub-IH (back-edge);
              true; blocked on threading the sub-node solution + glue. *)
  - admit. (* TODO[optimality]: Assign-Depend; walk, Ξ grows at tail; true;
              blocked on sub-IH context bookkeeping. *)
  - admit. (* TODO[optimality]: Assign-Skip; walk; true; blocked on sub-IH. *)
  - admit. (* TODO[optimality]: Assign-SkipRigid; walk; true; blocked on sub-IH. *)
  - admit. (* TODO[optimality]: Assign-SkipTmVar(typ); walk; true; sub-IH. *)
  - admit. (* TODO[optimality]: Assign-SkipTmVar(skl); walk; true; sub-IH. *)
  (* ================= a_unify (6) ================= *)
  - (* Flex-Flex-Id : Θ1 = Θ0, pure identity-node factoring *)
    intros F Θ0 α Hfa. unfold unify_optimal_post.
    intros Hwf _ _ θ1 θ Θ Hid Hinc1 Hinc Hwfth Heq.
    exists θ. apply (opt_axiom_factor Hwf Hid Hinc1 Hinc).
  - (* Flex-Flex-L : α̂ := β̂.  ζ := θ; the head flex-image [τ] plays the role of
       the definition's image, and the competing equality [θα̂ ≡ θβ̂] is exactly
       the [flex_def] side condition.  The factoring collapses (θ1 identity). *)
    intros F Θ0 α β Hne Hfβ.
    unfold unify_optimal_post.
    intros Hwf Hfα' Hfβ' θ1 θ Θ Hid Hinc1 Hinc Hwfth Heq.
    assert (Hβα : β <> α) by auto.
    inversion Hinc as [ | Θs θs Θt αs τ Hinc' Hwfτ Hmτ [Heqα Heqθ] Heqt | | | | ];
      subst.
    exists ((α, τ) :: θs). split.
    + apply a_inc__flex_def; auto.
      rewrite msubst_lookup_cons_eq in Heq.
      rewrite (msubst_lookup_cons_neq τ θs Hβα) in Heq.
      exact Heq.
    + rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
      apply a_inc_equiv_refl; exact Hinc.
  - (* Flex-Flex-R : β̂ := α̂.  Symmetric to L; the [flex_def] side condition is
       the competing equality read the other way, so it closes by [sym]. *)
    intros F Θ0 α β Hne Hfα.
    unfold unify_optimal_post.
    intros Hwf Hfα' Hfβ' θ1 θ Θ Hid Hinc1 Hinc Hwfth Heq.
    assert (Hαβ : α <> β) by auto.
    inversion Hinc as [ | Θs θs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqθ] Heqt | | | | ];
      subst.
    exists ((β, τ) :: θs). split.
    + apply a_inc__flex_def; auto.
      rewrite msubst_lookup_cons_eq in Heq.
      rewrite (msubst_lookup_cons_neq τ θs Hαβ) in Heq.
      apply a_tyequiv__sym; exact Heq.
    + rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
      apply a_inc_equiv_refl; exact Hinc.
  - admit. (* TODO[optimality]: Flex-Flex-Assign; consistency sub-IH (back-edge);
              true; blocked on the bridge + glue. *)
  - (* Flex-Flex-Skip : head flex γ̂ skipped (γ≠α,β).  Peel γ̂ off the competing
       θ = (γ,τγ)::θs, run the sub-IH with the soundness ⊴-witness (which the
       inverted conclusion-witness equals by id-uniqueness), then re-cons γ̂. *)
    intros F Θ0 Θ1 γ α β Hγα Hγβ Hu IHu.
    unfold unify_optimal_post.
    intros Hwf Hfα Hfβ θ1 θ Θ Hid Hinc1 Hinc Hwfth Heq.
    inversion Hwf as [ | γh Θh Hnd Hwf0 | | | | ]; subst.
    destruct (a_unify_subjects_flex Hwf0 Hu) as [Hfα0 Hfβ0].
    assert (Hαγ : α <> γ) by auto.
    assert (Hβγ : β <> γ) by auto.
    inversion Hinc as [ | Θs θs Θt γs τγ Hincs Hwfτ Hmτ [Heqγ Heqθ] Heqt
                      | | | | ]; subst.
    inversion Hinc1 as [ | Θp θp Θq γp τp Hincp Hwfp Hmp [Heqγ1 Heqθ1] Heqt1
                       | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτp Hid1s]; subst.
    destruct (a_unify_sound Hu Hwf0) as [[[w [Hidw Hincw]] _] [Hwf1 _]].
    assert (Hw : θp = w) by (eapply is_id_inc_unique; eauto). subst w.
    assert (Hγw : γ `notin` dom θp)
      by (pose proof (a_inc_dom_sub Hincp) as Hs; clear - Hs Hnd; fsetdec).
    rewrite (msubst_lookup_cons_neq τγ θs Hαγ) in Heq.
    rewrite (msubst_lookup_cons_neq τγ θs Hβγ) in Heq.
    destruct (IHu Hwf0 Hfα0 Hfβ0 θp θs Θ Hid1s Hincw Hincs Hwfth Heq)
      as [ζ' [Hζ' Hie']].
    exists ((γ, τγ) :: ζ'). split.
    + apply a_inc__flex; auto.
    + assert (Heqc : msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: θp)
                     = (γ, τγ) :: msubst_compose ζ' θp).
      { change (msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: θp))
          with ((γ, msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                :: msubst_compose ((γ, τγ) :: ζ') θp).
        rewrite (msubst_compose_cons_l_id τγ ζ' Hid1s Hγw).
        change (msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
          with (msubst_lookup ((γ, τγ) :: ζ') γ).
        rewrite msubst_lookup_cons_eq. reflexivity. }
      rewrite Heqc.
      apply a_inc_equiv__flex; [ exact Hie' | ].
      apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτ.
  - admit. (* TODO[optimality]: Flex-Flex-Skip'; walk; true; sub-IH. *)
  (* ================= a_consis (14) ================= *)
  - admit. (* TODO[optimality]: C-Ghost; axiom, Θ1=Θ0; opt_axiom_factor for the
              factoring + precision from the hole (Δ2∩ftv=∅); true. *)
  - admit. (* TODO[optimality]: C-Unit; axiom; opt_axiom_factor + refl precision. *)
  - admit. (* TODO[optimality]: C-Rigid; axiom; opt_axiom_factor + var precision. *)
  - admit. (* TODO[optimality]: C-Arrow; STRUCTURAL, two sub-nodes; true;
              a_inc_equiv_glue composes the two factorings; blocked on threading
              the sub-node solutions (soundness output -> optimality input) and
              discharging the glue's wf + flex-dom side conditions. *)
  - admit. (* TODO[optimality]: C-ForallInh; STRUCTURAL (rigid α added); glue with
              the cofinite α-extended ζ; true. *)
  - admit. (* TODO[optimality]: C-ForallSyn; STRUCTURAL; glue; true. *)
  - admit. (* TODO[optimality]: C-UnivGhost; STRUCTURAL (single sub-node); glue
              degenerates to congruence; true. *)
  - admit. (* TODO[optimality]: C-UnivGhost1; STRUCTURAL (rigid α); glue; true. *)
  - admit. (* TODO[optimality]: C-UnivGhost2; STRUCTURAL; glue; true. *)
  - admit. (* TODO[optimality]: C-Flex; MUTUAL (unify sub-IH) + precision via
              consis_precise_via_join; true; blocked on plumbing the sub-IH. *)
  - admit. (* TODO[optimality]: C-FlexL; MUTUAL (assign sub-IH) + precision via
              consis_precise_via_join; true. *)
  - admit. (* TODO[optimality]: C-FlexR; MUTUAL (assign sub-IH) + precision via
              consis_precise_via_refine; true. *)
  - admit. (* TODO[optimality]: C-GhostR; axiom, Θ1=Θ0; opt_axiom_factor +
              precision (Δ1∩ftv=∅); true. *)
  - admit. (* TODO[optimality]: C-UnivGhostR; STRUCTURAL (single sub-node,
              SAME derivation shrinks P0); glue/congruence; true. *)
Admitted.

(* ===================================================================== *)
(*  8.  TOP-LEVEL COROLLARIES (unaugmented [_optimal] statements)          *)
(*                                                                        *)
(*  These reduce the unaugmented optimality Props of §2/§3 to the bundle's  *)
(*  [*_optimal_post] motives.  For unification and assignment the two       *)
(*  coincide directly (no Δ/Ψ augmentation, no precision conjunct), so the  *)
(*  reduction is a thin wrapper.  (The consistency corollary additionally   *)
(*  needs [ad_precise_preserves_refine] to turn the motive's precision      *)
(*  conjunct back into the [⊳] refinement of [a_consis_optimal]; left as a  *)
(*  TODO alongside the augmentation reduction.)                            *)
(* ===================================================================== *)

Lemma a_unify_optimal_thm : forall F Θ0 α β Θ1,
  a_unify F Θ0 α β Θ1 ->
  a_wf_aenv Θ0 -> a_flex_tvar Θ0 α -> a_flex_tvar Θ0 β ->
  forall θ1, Θ0 ≤[ θ1 ] Θ1 ->
  a_unify_optimal Θ0 α β θ1 Θ1.
Proof.
  intros F Θ0 α β Θ1 Hu Hwf Hfa Hfb θ1 Hinc1.
  unfold a_unify_optimal. intros Hid θ Θ Hsol.
  destruct Hsol as [Hinc [Heq Hwfth]].
  destruct a_assign_unify_consis_optimal as [_ [Hunify _]].
  eapply (Hunify _ _ _ _ _ Hu); eauto.
Qed.

Lemma a_assign_optimal_thm : forall F Θ0 Ξ α P Θ1,
  a_assign F Θ0 Ξ α P Θ1 ->
  a_decls Ξ -> a_wf_aenv (Ξ ++ Θ0) -> (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
  forall θ1, (Ξ ++ Θ0) ≤[ θ1 ] Θ1 ->
  a_assign_optimal Θ0 Ξ α P θ1 Θ1.
Proof.
  intros F Θ0 Ξ α P Θ1 Ha Hdecl Hwf HwfP θ1 Hinc1.
  unfold a_assign_optimal. intros Hid θ Θ Hsol.
  destruct Hsol as [Hinc [Hjoin Hwfth]].
  destruct a_assign_unify_consis_optimal as [Hassign _].
  eapply (Hassign _ _ _ _ _ _ Ha); eauto.
Qed.
