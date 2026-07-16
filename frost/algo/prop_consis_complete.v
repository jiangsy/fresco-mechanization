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
    (`ρ ≡ ζ ∘ ρ₁`, see algo/prop_compose.v) and PRECISION (`ζP₁ ⊑ Q`, see
    algo/prop_precise.v).  Those two were the prerequisites; this file states
    what they are for. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
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
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_inc_strengthen.

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
(*  defines the increment as a finite map ρ from flexible variables in Θ    *)
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

(** A solution is a tuple (Θ₀ ⊑[ρ₁] Θ₁; P₁) such that the substituted input is
    consistent with P₁, and P₁ is a refinement of the substituted input
    skeleton.  Its target Θ₁ is well-formed (external-wf side condition). *)
Definition a_consis_solution
    (Θ0 : aenv) (P0 P : pskl) (ρ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  Θ0 ≤[ ρ1 ] Θ1 /\
  empty ⨟ Θ1 ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ1 P)) ≈ P1 /\
  Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl ρ1 P0)) ⊳ P1 /\
  a_wf_aenv Θ1.

(** The solution is OPTIMAL if every other solution factors through it: there is
    a ζ carrying Θ₁ to the other target, with ρ ≡ ζ∘ρ₁, and the algorithm's
    output is at least as PRECISE as the other one's. *)
Definition a_consis_optimal
    (Θ0 : aenv) (P0 P : pskl) (ρ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  is_id_msubst ρ1 ->
  forall ρ Θ Q,
    a_consis_solution Θ0 P0 P ρ Θ Q ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
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
    (Θ0 : aenv) (α β : atom) (ρ1 : metasubst) (Θ1 : aenv) : Prop :=
  Θ0 ≤[ ρ1 ] Θ1 /\
  Θ1 ⊢ (msubst_lookup ρ1 α) ≡ᵗ (msubst_lookup ρ1 β) /\
  a_wf_aenv Θ1.

Definition a_unify_optimal
    (Θ0 : aenv) (α β : atom) (ρ1 : metasubst) (Θ1 : aenv) : Prop :=
  is_id_msubst ρ1 ->
  forall ρ Θ,
    a_unify_solution Θ0 α β ρ Θ ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ.

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
    (Θ0 Ξ : aenv) (α : atom) (P : pskl) (ρ1 : metasubst) (Θ1 : aenv) : Prop :=
  (Ξ ++ Θ0) ≤[ ρ1 ] Θ1 /\
  empty ⨟ Θ1 ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ1 P))
                ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ1 α))) /\
  a_wf_aenv Θ1.

Definition a_assign_optimal
    (Θ0 Ξ : aenv) (α : atom) (P : pskl) (ρ1 : metasubst) (Θ1 : aenv) : Prop :=
  is_id_msubst ρ1 ->
  forall ρ Θ,
    a_assign_solution Θ0 Ξ α P ρ Θ ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv (Ξ ++ Θ0) ρ (msubst_compose ζ ρ1) Θ.

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
(*  with the algorithm's own solution substitution [ρ1] (Θ0 ≤[ρ1] Θ1) and  *)
(*  ANY competing solution [ρ] into [Θ], the motive produces the factoring *)
(*  [ζ]: Θ1 ≤[ζ] Θ, [ρ ≡ ζ∘ρ1], and — for consistency — a PRECISION        *)
(*  statement [ζQ ⊑ Qb] (⊑ = ad_precise, algo/prop_precise.v).  The         *)
(*  top-level corollary converts precision back to the refinement [⊳] via   *)
(*  [ad_precise_preserves_refine].                                         *)
(*                                                                         *)
(*  MOTIVE CORRECTION (validated 2026-07-15, [paper-gap]).  Each motive     *)
(*  and each top-level [_optimal] definition now REQUIRES [is_id_msubst ρ1]. *)
(*  Without it the statements are FALSE — a concrete counterexample:         *)
(*                                                                          *)
(*    Θ0 = α̂,β̂,γ̂ (all flexible);  ρ1 = [γ̂/α̂, γ̂/β̂, γ̂/γ̂]  (a valid, NON-    *)
(*    identity increment Θ0 ≤[ρ1] Θ0);  competing ρ = [Int/α̂, Bool/β̂, …].   *)
(*    An axiom node (e.g. Ghost/Unit) has Θ1 = Θ0, so it must exhibit ζ with *)
(*    a_inc_equiv Θ0 ρ (ζ∘ρ1) Θ.  But (ζ∘ρ1)α̂ = ζγ̂ = (ζ∘ρ1)β̂, forcing      *)
(*    Θ ⊢ Int ≡ᵗ ζγ̂ ≡ᵗ Bool, i.e. Int ≡ᵗ Bool — impossible.  So NO ζ works. *)
(*                                                                          *)
(*  The paper (consistency-proofs.tex:2246) produces ρ1 EXISTENTIALLY as the *)
(*  algorithm's OWN solution, which is the identity metasubstitution ι       *)
(*  (a_isub / [DESIGN-completeness-measure.md §7.3 L10]): the algorithm only  *)
(*  ADDS definitions, never rewrites an existing flexible, so [Θ0 ⊴ Θ1] and  *)
(*  its witness ρ1 satisfy [is_id_msubst ρ1].  Requiring it here is exactly   *)
(*  the a_isub identity witness [prop_precise_recover.v] discharges, and it   *)
(*  is what makes [msubst_compose ζ ρ1] collapse to [ζ] (see the helper       *)
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
  forall ρ1 ρ Θ,
    is_id_msubst ρ1 ->
    Θ0 ≤[ ρ1 ] Θ1 ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->  (* external-wf side condition on the competing solution's target *)
    Θ ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β) ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ.

Definition assign_optimal_post (F : atoms) (Θ0 Ξ : aenv) (α : atom)
    (P : pskl) (Θ1 : aenv) : Prop :=
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
  dom Ξ [<=] ftvar_in_pskl P ->  (* the pending decls are all used in P (Assign-Depend); threaded from Ξ=nil *)
  forall ρ1 ρ Θ,
    is_id_msubst ρ1 ->
    (Ξ ++ Θ0) ≤[ ρ1 ] Θ1 ->
    (Ξ ++ Θ0) ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->  (* external-wf side condition on the competing solution's target *)
    empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P))
                 ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α))) ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv (Ξ ++ Θ0) ρ (msubst_compose ζ ρ1) Θ.

Definition consis_optimal_post (F Δ1 Δ2 : atoms) (Θ0 : aenv)
    (P0 P Q : pskl) (Θ1 : aenv) : Prop :=
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (forall X, X `in` (Δ1 `union` Δ2) -> binds X abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 ->
  flex_above_free (Δ1 `union` Δ2) Θ0 ->
  forall ρ1 ρ Θ Qt Qb,
    is_id_msubst ρ1 ->
    Θ0 ≤[ ρ1 ] Θ1 ->
    bskl_to_pskl Qt = Q ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->  (* external-wf side condition on the competing solution's target *)
    (* The paper's AUGMENTED-SOLUTION side condition (consistency-proofs.tex
       :2239-2240): "no flexible variables in Θ depend on variables in Δ1 and
       Δ2" — on the COMPETING target Θ, in addition to the problem-side
       [no_flex_dep _ Θ0] above.  NOT derivable from the problem side (a
       competing increment may define a flexible with a Δ-mentioning image);
       load-bearing for the Δ-growing structural cases (C-ForallInh/Syn,
       C-UnivGhost1), whose outer precision reassembly strips the opened
       rigid α out of the sub-node's context. *)
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P)) ≈ Qb ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ P) (bskl_to_pskl Qb) ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
      Θ ⨟ (Δ1 `union` Δ2) ⊢ₚᵣᵃ (msubst_bskl ζ Qt) ⊑ (bskl_to_pskl Qb).

(* ===================================================================== *)
(*  5.  REUSABLE FACTORING HELPERS (standalone, for the [OPT] bundle)      *)
(*                                                                        *)
(*  The (OPT) bundle's factoring conjunct is                              *)
(*    a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ.                           *)
(*  For the AXIOM/identity-output nodes (Ghost/GhostG/Unit/Rigid/GhostR)  *)
(*  the algorithm leaves the context unchanged (Θ1 = Θ0) and the natural  *)
(*  choice is ζ := ρ, whereupon [msubst_compose ρ ρ1] must collapse to ρ  *)
(*  — which needs [is_id_msubst ρ1] (the corrected motive hypothesis).    *)
(*  These lemmas isolate that collapse.                                    *)
(* ===================================================================== *)

(** Reflexivity of metasubstitution equivalence: every increment is
    equivalent to itself (each flexible image is [≡ᵗ]-reflexive). *)
Lemma a_inc_equiv_refl : forall Θ0 ρ Θ,
  Θ0 ≤[ ρ ] Θ ->
  a_inc_equiv Θ0 ρ ρ Θ.
Proof.
  intros Θ0 ρ Θ H; induction H.
  - apply a_inc_equiv__empty; auto.
  - apply a_inc_equiv__flex; auto.
    apply a_tyequiv__refl. apply mono_ptyp_lc; auto.
  - apply a_inc_equiv__flex_def; auto.
    apply a_tyequiv__refl. apply mono_ptyp_lc; auto.
  - apply a_inc_equiv__var; auto.
  - apply a_inc_equiv__var_skl; auto.
  - apply a_inc_equiv__tvar; auto.
Qed.

(** [dom ρ ⊆ dom Θ0] for any increment [Θ0 ≤[ρ] Θ]. *)
Lemma a_inc_dom_sub : forall Θ0 ρ Θ,
  Θ0 ≤[ ρ ] Θ ->
  dom ρ [<=] dom Θ0.
Proof.
  intros Θ0 ρ Θ H X HX.
  destruct (a_inc_dom_flex H HX) as [Hb | [τ Hb]]; apply binds_In in Hb; exact Hb.
Qed.

(** Prepending an entry outside the RIGHT (identity) multiplicand's domain
    does not change the composition. *)
Lemma msubst_compose_cons_l_id : forall α τ ζ ρ1,
  is_id_msubst ρ1 ->
  α `notin` dom ρ1 ->
  msubst_compose ((α, τ) :: ζ) ρ1 = msubst_compose ζ ρ1.
Proof.
  induction ρ1 as [ | [β b] ρ1' IH ]; intros Hid Hni; simpl; auto.
  apply is_id_msubst_inv in Hid as [Heq Hid']; subst.
  simpl in Hni. simpl.
  rewrite IH by (first [ exact Hid' | clear - Hni; fsetdec ]).
  destruct (β == α) as [->|Hne]; [ exfalso; clear - Hni; fsetdec | reflexivity ].
Qed.

(** When [ρ1] is an IDENTITY increment on the same source, composing any
    increment [ρ] with it on the right is the identity: [ρ ∘ ρ1 = ρ] as
    lists.  Both increments track [Θ0]'s flexibles in the same order. *)
Lemma msubst_compose_is_id_r : forall Θ0 ρ1 Θ1 ρ Θ,
  a_wf_aenv Θ0 ->
  is_id_msubst ρ1 ->
  Θ0 ≤[ ρ1 ] Θ1 ->
  Θ0 ≤[ ρ ] Θ ->
  msubst_compose ρ ρ1 = ρ.
Proof.
  intros Θ0 ρ1 Θ1 ρ Θ Hwf Hid Hinc1 Hinc; revert ρ1 Θ1 Hid Hinc1.
  induction Hinc; intros ρ1 Θ1 Hid Hinc1.
  - (* source nil : ρ1 = nil *)
    inversion Hinc1; subst. reflexivity.
  - (* flex α *)
    inversion Hwf as [ | αh Θh Hnd Hwa | | | | ]; subst.
    inversion Hinc1 as [ | Θa ρa Θb αa τa Hi1 Hw1 Hm1 | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    simpl. destruct (α == α) as [_ | Hne]; [ | contradiction ].
    assert (Hnid : α `notin` dom ρa)
      by (pose proof (a_inc_dom_sub Hi1) as Hs; clear - Hs Hnd; fsetdec).
    rewrite (msubst_compose_cons_l_id _ _ Hid' Hnid).
    rewrite (IHHinc Hwa _ _ Hid' Hi1). reflexivity.
  - (* flex_def α := τ *)
    inversion Hwf as [ | | αh τh Θh Hnd Hwp Hm Hwa | | | ]; subst.
    inversion Hinc1 as [ | | Θa ρa Θb αa τd τa He1 Hw1 Hm1 Heq1 | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    simpl. destruct (α == α) as [_ | Hne]; [ | contradiction ].
    assert (Hnid : α `notin` dom ρa)
      by (pose proof (a_inc_dom_sub He1) as Hs; clear - Hs Hnd; fsetdec).
    rewrite (msubst_compose_cons_l_id _ _ Hid' Hnid).
    rewrite (IHHinc Hwa _ _ Hid' He1). reflexivity.
  - (* var typ *)
    inversion Hwf as [ | | | | xh Ah Θh Hnd Hwp Hwa | ]; subst.
    inversion Hinc1 as [ | | | Θa ρa Θb Ξa xa Aa Hi1 Hs1 | | ]; subst.
    eapply IHHinc; eauto.
  - (* var skl *)
    inversion Hwf as [ | | | xh Ph Θh Hnd Hwp Hwa | | ]; subst.
    inversion Hinc1 as [ | | | | Θa ρa Θb Ξa xa Pa Hi1 Hs1 | ]; subst.
    eapply IHHinc; eauto.
  - (* tvar *)
    inversion Hwf as [ | | | | | αh Θh Hnd Hwa ]; subst.
    inversion Hinc1 as [ | | | | | Θa ρa Θb Ξa αa Hi1 Hs1 ]; subst.
    eapply IHHinc; eauto.
Qed.

(** An IDENTITY increment is determined by its SOURCE alone: two id-increments
    out of the same [Θ0] are equal as lists (the target is irrelevant — every
    image is the identity, and both track [Θ0]'s flexibles in the same order).
    This is what lets a sub-node's soundness [⊴]-witness stand in for the
    algorithm's own id-witness on the walk cases. *)
Lemma is_id_inc_unique : forall Θ0 ρ1 Θ1,
  Θ0 ≤[ ρ1 ] Θ1 -> is_id_msubst ρ1 ->
  forall ρ2 Θ2, Θ0 ≤[ ρ2 ] Θ2 -> is_id_msubst ρ2 -> ρ1 = ρ2.
Proof.
  intros Θ0 ρ1 Θ1 Hinc1; induction Hinc1; intros Hid1 ρ2 Θ2 Hinc2 Hid2.
  - inversion Hinc2; subst; reflexivity.
  - apply is_id_msubst_inv in Hid1 as [Heq1 Hid1']; subst.
    inversion Hinc2 as [ | Θa ρa Θb αa τa Hinca Hwfa Hma [Heqα Heqρ2] Heqt
                       | | | | ]; subst.
    apply is_id_msubst_inv in Hid2 as [Heq2 Hid2']; subst.
    f_equal. eapply IHHinc1; eauto.
  - apply is_id_msubst_inv in Hid1 as [Heq1 Hid1']; subst.
    inversion Hinc2 as [ | | Θa ρa Θb αa τd τa Hinca Hwfa Hma Heqda [Heqα Heqρ2] Heqt
                       | | | ]; subst.
    apply is_id_msubst_inv in Hid2 as [Heq2 Hid2']; subst.
    f_equal. eapply IHHinc1; eauto.
  - inversion Hinc2 as [ | | | Θa ρa Θb Ξa xa Aa Hinca Hsa Heqsrc Heqt | | ]; subst.
    eapply IHHinc1; eauto.
  - inversion Hinc2 as [ | | | | Θa ρa Θb Ξa xa Pa Hinca Hsa Heqsrc Heqt | ]; subst.
    eapply IHHinc1; eauto.
  - inversion Hinc2 as [ | | | | | Θa ρa Θb Ξa αa Hinca Hsa Heqsrc Heqt ]; subst.
    eapply IHHinc1; eauto.
Qed.

(** The complete AXIOM-node factoring: at a node that leaves the context
    unchanged ([Θ1 = Θ0]) the competing solution's own substitution [ρ]
    serves as the factoring [ζ]. *)
Lemma opt_axiom_factor : forall Θ0 ρ1 ρ Θ,
  a_wf_aenv Θ0 ->
  is_id_msubst ρ1 ->
  Θ0 ≤[ ρ1 ] Θ0 ->
  Θ0 ≤[ ρ ] Θ ->
  Θ0 ≤[ ρ ] Θ /\ a_inc_equiv Θ0 ρ (msubst_compose ρ ρ1) Θ.
Proof.
  intros Θ0 ρ1 ρ Θ Hwf Hid Hinc1 Hinc.
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
(*    sub1 :  a_inc_equiv Θ0   ρ  (msubst_compose ζ1 ρ1a) Θ                 *)
(*    sub2 :  a_inc_equiv Θmid ζ1 (msubst_compose ζ2 ρ1b) Θ                 *)
(*  the composed factoring is  a_inc_equiv Θ0 ρ (msubst_compose ζ2 ρ1a) Θ   *)
(*  (using that the id-witnesses ρ1a/ρ1b compose away).  Built from a        *)
(*  CONGRUENCE (right-composition with an increment) and TRANSITIVITY of    *)
(*  a_inc_equiv — modelled on [a_inc_compose] (prop_compose.v:695).         *)
(* ===================================================================== *)

(** Two equivalent metasubstitutions act [≡ᵗ]-equivalently on a wf MONOtype.
    (Monotypes have no [∀], so no binder/opening obligation arises — this is
    why the congruence below can stay first-order.) *)
Lemma a_inc_equiv_msubst_mono : forall Θmid ρ1 ρ2 Θ τ,
  a_inc_equiv Θmid ρ1 ρ2 Θ ->
  a_wf_aenv Θmid ->
  a_wf_ptyp Θmid τ ->
  mono_ptyp τ ->
  Θ ⊢ (msubst_ptyp ρ1 τ) ≡ᵗ (msubst_ptyp ρ2 τ).
Proof.
  intros Θmid ρ1 ρ2 Θ τ Hie Hwf Hwt Hm; revert Hwt; induction Hm; intros Hwt.
  - (* unit *) simpl. apply a_tyequiv__refl. constructor.
  - (* var X *) simpl. inversion Hwt; subst.
    eapply prop_normal.a_inc_equiv_lookup; [ exact Hie | exact Hwf | assumption ].
  - (* arrow A1 A2 *) simpl. inversion Hwt; subst.
    apply a_tyequiv__arrow; [ apply IHHm1 | apply IHHm2 ]; assumption.
Qed.

(** ===================================================================
    SEMANTIC-MIDDLE TRANSPORT for [a_inc_equiv] (2026-07-15).

    [Flex-Flex-Skip'] and the structural consistency cases rebuild a
    [var]/[var_skl] binder entry across the competing increment.  Those
    entries carry a POLYMORPHIC payload, so the mono-only
    [a_inc_equiv_msubst_mono] does not apply; we lift the per-variable
    [a_inc_equiv_lookup] to arbitrary well-formed payloads.  The [∀]-case
    of that lift needs to move [≡ᵗ]/[≡ˢ] across a fresh rigid, hence the
    two strengthening lemmas below (only the [flex_def] rule reads the
    context, and a rigid is never a [flex_def]).
    =================================================================== *)

Lemma a_tyequiv_strengthen_tvar_cons : forall Θ0 A B,
  Θ0 ⊢ A ≡ᵗ B ->
  forall X Θ, Θ0 = (X ~ abind_tvar) ++ Θ ->
  Θ ⊢ A ≡ᵗ B.
Proof.
  intros Θ0 A B Heq; induction Heq; intros X0 Θ0' HΘ; subst.
  - apply a_tyequiv__refl; assumption.
  - apply a_tyequiv__sym; eauto.
  - eapply a_tyequiv__trans; eauto.
  - apply a_tyequiv__flex_def.
    destruct (binds_cons_1 _ _ _ _ _ _ H) as [[Heqx Heqb] | Hb'];
      [ discriminate | exact Hb' ].
  - apply a_tyequiv__arrow; eauto.
  - apply a_tyequiv__all with (L := L); intros X HX; eauto.
Qed.

Lemma a_pskl_tyequiv_strengthen_tvar_cons : forall Θ0 P Q,
  Θ0 ⊢ P ≡ˢ Q ->
  forall X Θ, Θ0 = (X ~ abind_tvar) ++ Θ ->
  Θ ⊢ P ≡ˢ Q.
Proof.
  intros Θ0 P Q Heq; induction Heq; intros X0 Θ0' HΘ; subst.
  - apply a_pskl_tyequiv__refl; assumption.
  - apply a_pskl_tyequiv__sym; eauto.
  - eapply a_pskl_tyequiv__trans; eauto.
  - apply a_pskl_tyequiv__flex_def.
    destruct (binds_cons_1 _ _ _ _ _ _ H) as [[Heqx Heqb] | Hb'];
      [ discriminate | exact Hb' ].
  - apply a_pskl_tyequiv__arrow; eauto.
  - apply a_pskl_tyequiv__all with (L := L); intros X HX; eauto.
  - apply a_pskl_tyequiv__tophole; eauto.
Qed.

(** An [a_inc]'s images are locally closed (they are monotypes). *)
Lemma a_inc_msubst_lc : forall Θ0 ρ Θ,
  Θ0 ≤[ ρ ] Θ -> msubst_lc ρ.
Proof.
  intros Θ0 ρ Θ Hinc X. apply mono_ptyp_lc.
  eapply a_inc_lookup_mono; exact Hinc.
Qed.

(** Identity metasubstitutions have locally-closed (variable) images. *)
Lemma is_id_msubst_values_lc : forall ρ,
  is_id_msubst ρ -> forall α τ, In (α, τ) ρ -> lc_ptyp τ.
Proof.
  induction ρ as [ | [β b] ρ' IH ]; intros Hid α τ Hin; [ inversion Hin | ].
  apply is_id_msubst_inv in Hid as [Heq Hid']; subst.
  destruct Hin as [Heqe | Hin'].
  - inversion Heqe; subst. apply lc_ptyp_var_f.
  - exact (IH Hid' α τ Hin').
Qed.

(** Composition under a locally-closed metasubst is locally closed. *)
Lemma msubst_lc_compose : forall ζ ρ,
  msubst_lc ζ ->
  (forall α τ, In (α, τ) ρ -> lc_ptyp τ) ->
  msubst_lc (msubst_compose ζ ρ).
Proof.
  intros ζ ρ Hζ. unfold msubst_compose.
  induction ρ as [ | [α τ] ρ' IH ]; intros Hlc X; simpl.
  - apply lc_ptyp_var_f.
  - destruct (X == α) as [-> | Hne].
    + apply msubst_ptyp_lc_lc; [ exact Hζ | apply (Hlc α τ); left; reflexivity ].
    + apply IH; [ intros a t Hin; apply (Hlc a t); right; exact Hin ].
Qed.

(** [msubst_pskl] commutes with opening under a locally-closed metasubst.
    (Local copies of [prop_consis_exist]'s lemmas, which cannot be imported
    here — that file imports this one.) *)
Lemma msubst_pskl_open_rec_lc_local : forall θ,
  msubst_lc θ ->
  forall P V k,
  msubst_pskl θ (open_pskl_wrt_pskl_rec k V P)
  = open_pskl_wrt_pskl_rec k (msubst_pskl θ V) (msubst_pskl θ P).
Proof.
  intros θ Hlc P;
    induction P as [ | n | X | P1 IH1 P2 IH2 | P0 IH0 | | P0 IH0 ];
    intros V k; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - symmetry.
    apply open_pskl_wrt_pskl_rec_degree_pskl_wrt_pskl.
    apply degree_pskl_wrt_pskl_O.
    apply degree_pskl_wrt_pskl_of_lc_pskl.
    apply lc_ptyp_to_pskl. apply Hlc.
Qed.

Lemma msubst_pskl_open_lc_local : forall θ P X,
  msubst_lc θ ->
  X `notin` dom θ ->
  msubst_pskl θ (open_pskl_wrt_pskl P (pskl_var_f X))
  = open_pskl_wrt_pskl (msubst_pskl θ P) (pskl_var_f X).
Proof.
  intros θ P X Hlc HX. unfold open_pskl_wrt_pskl.
  rewrite (msubst_pskl_open_rec_lc_local Hlc P (pskl_var_f X) 0).
  cbn [msubst_pskl]. rewrite msubst_lookup_notin by exact HX.
  reflexivity.
Qed.

(** The type lift of [a_inc_equiv_lookup] to arbitrary well-formed types. *)
Lemma a_inc_equiv_msubst_ptyp : forall A Θ0 ρ1 ρ2 Θ,
  a_wf_ptyp Θ0 A ->
  a_inc_equiv Θ0 ρ1 ρ2 Θ ->
  a_wf_aenv Θ0 ->
  msubst_lc ρ1 -> msubst_lc ρ2 ->
  Θ ⊢ (msubst_ptyp ρ1 A) ≡ᵗ (msubst_ptyp ρ2 A).
Proof.
  intros A Θ0 ρ1 ρ2 Θ Hwf; revert ρ1 ρ2 Θ.
  induction Hwf as [ Θ0 | Θ0 X Hbt | Θ0 A1 A2 Hwf1 IH1 Hwf2 IH2 | L Θ0 A0 Hwf0 IH0 ];
    intros ρ1 ρ2 Θ Hie Hwf Hlc1 Hlc2; simpl.
  - apply a_tyequiv__refl; apply lc_ptyp_unit.
  - eapply prop_normal.a_inc_equiv_lookup; eauto.
  - apply a_tyequiv__arrow; [ apply IH1 | apply IH2 ]; auto.
  - apply a_tyequiv__all
      with (L := L `union` dom ρ1 `union` dom ρ2 `union` dom Θ0).
    intros X HX.
    rewrite <- (msubst_ptyp_open_lc A0 Hlc1) by (clear - HX; fsetdec).
    rewrite <- (msubst_ptyp_open_lc A0 Hlc2) by (clear - HX; fsetdec).
    eapply a_tyequiv_strengthen_tvar_cons with (X := X) (Θ := Θ); [ | reflexivity ].
    apply IH0 with (X := X); [ clear - HX; fsetdec | | | exact Hlc1 | exact Hlc2 ].
    + apply a_inc_equiv__tvar with (Ξ := (@nil (atom * abind)));
        [ exact Hie | apply a_suffix__nil ].
    + apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf ].
Qed.

(** The skeleton mirror. *)
Lemma a_inc_equiv_msubst_pskl : forall P Θ0 ρ1 ρ2 Θ,
  a_wf_pskl Θ0 P ->
  a_inc_equiv Θ0 ρ1 ρ2 Θ ->
  a_wf_aenv Θ0 ->
  msubst_lc ρ1 -> msubst_lc ρ2 ->
  Θ ⊢ (msubst_pskl ρ1 P) ≡ˢ (msubst_pskl ρ2 P).
Proof.
  intros P Θ0 ρ1 ρ2 Θ Hwf; revert ρ1 ρ2 Θ.
  induction Hwf as [ Θ0 | Θ0 X Hbt | Θ0 P1 P2 Hwf1 IH1 Hwf2 IH2
                   | L Θ0 P0 Hwf0 IH0 | Θ0 | Θ0 P0 Hwf0 IH0 ];
    intros ρ1 ρ2 Θ Hie Hwf Hlc1 Hlc2; simpl.
  - apply a_pskl_tyequiv__refl; apply lc_pskl_unit.
  - apply a_tyequiv_pskl. eapply prop_normal.a_inc_equiv_lookup; eauto.
  - apply a_pskl_tyequiv__arrow; [ apply IH1 | apply IH2 ]; auto.
  - apply a_pskl_tyequiv__all
      with (L := L `union` dom ρ1 `union` dom ρ2 `union` dom Θ0).
    intros X HX.
    rewrite <- (msubst_pskl_open_lc_local P0 Hlc1) by (clear - HX; fsetdec).
    rewrite <- (msubst_pskl_open_lc_local P0 Hlc2) by (clear - HX; fsetdec).
    eapply a_pskl_tyequiv_strengthen_tvar_cons with (X := X) (Θ := Θ); [ | reflexivity ].
    apply IH0 with (X := X); [ clear - HX; fsetdec | | | exact Hlc1 | exact Hlc2 ].
    + apply a_inc_equiv__tvar with (Ξ := (@nil (atom * abind)));
        [ exact Hie | apply a_suffix__nil ].
    + apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf ].
  - apply a_pskl_tyequiv__refl; apply lc_pskl_hole.
  - apply a_pskl_tyequiv__tophole; apply IH0; auto.
Qed.

(** Composing with an IDENTITY increment on the right is invisible to
    [msubst] on a well-formed type/skeleton (every free variable is either
    a source flexible in [dom ρ1] or a rigid untouched by [ζ]). *)
Lemma msubst_compose_id_ptyp : forall Θ0 ρ1 Θ1 ζ Θ2 A,
  a_wf_aenv Θ0 -> a_wf_aenv Θ1 ->
  is_id_msubst ρ1 ->
  Θ0 ≤[ ρ1 ] Θ1 ->
  Θ1 ≤[ ζ ] Θ2 ->
  a_wf_ptyp Θ0 A ->
  msubst_ptyp (msubst_compose ζ ρ1) A = msubst_ptyp ζ A.
Proof.
  intros Θ0 ρ1 Θ1 ζ Θ2 A Hwf0 Hwf1 Hid Hinc1 Hζ HA.
  rewrite msubst_ptyp_compose;
    [ rewrite (msubst_ptyp_id (ρ:=ρ1) A Hid); reflexivity | ].
  intros X HX.
  destruct (a_wf_ptyp_ftv_tvarish HA HX) as [Hrig | [Hflex | [τ Hdef]]].
  - right. intros Hin.
    apply (a_inc_dom_flex Hζ) in Hin.
    assert (Hbt1 : binds X abind_tvar Θ1)
      by (eapply a_inc_binds_tvar; [ exact Hinc1 | exact Hrig ]).
    pose proof (a_wf_aenv_uniq Hwf1) as Hu.
    destruct Hin as [Hb | [τ Hb]];
      pose proof (binds_unique _ _ _ _ _ Hbt1 Hb Hu) as Hc; discriminate.
  - left. eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | left; exact Hflex ].
  - left. eapply a_inc_flex_dom;
      [ exact Hinc1 | exact Hwf0 | right; exists τ; exact Hdef ].
Qed.

Lemma msubst_compose_id_pskl : forall Θ0 ρ1 Θ1 ζ Θ2 P,
  a_wf_aenv Θ0 -> a_wf_aenv Θ1 ->
  is_id_msubst ρ1 ->
  Θ0 ≤[ ρ1 ] Θ1 ->
  Θ1 ≤[ ζ ] Θ2 ->
  a_wf_pskl Θ0 P ->
  msubst_pskl (msubst_compose ζ ρ1) P = msubst_pskl ζ P.
Proof.
  intros Θ0 ρ1 Θ1 ζ Θ2 P Hwf0 Hwf1 Hid Hinc1 Hζ HP.
  rewrite msubst_pskl_compose;
    [ rewrite (msubst_pskl_id (ρ:=ρ1) P Hid); reflexivity | ].
  intros X HX.
  destruct (a_wf_pskl_ftv_tvarish HP HX) as [Hrig | [Hflex | [τ Hdef]]].
  - right. intros Hin.
    apply (a_inc_dom_flex Hζ) in Hin.
    assert (Hbt1 : binds X abind_tvar Θ1)
      by (eapply a_inc_binds_tvar; [ exact Hinc1 | exact Hrig ]).
    pose proof (a_wf_aenv_uniq Hwf1) as Hu.
    destruct Hin as [Hb | [τ Hb]];
      pose proof (binds_unique _ _ _ _ _ Hbt1 Hb Hu) as Hc; discriminate.
  - left. eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | left; exact Hflex ].
  - left. eapply a_inc_flex_dom;
      [ exact Hinc1 | exact Hwf0 | right; exists τ; exact Hdef ].
Qed.

(** The identity-increment through a NON-flexible middle strengthens
    directly: the competing target's suffix is forced empty (a suffix is
    all-flexible, but the head [c ~ b] here is a rigid / term binding). *)
Lemma a_inc_id_mid_strip : forall c b Θ0 ρ1 Θ1,
  (b = abind_tvar \/
   (exists Q, b = abind_var_typ Q) \/ (exists Q, b = abind_var_skl Q)) ->
  ((c ~ b) ++ Θ0) ≤[ ρ1 ] ((c ~ b) ++ Θ1) ->
  Θ0 ≤[ ρ1 ] Θ1.
Proof.
  intros c b Θ0 ρ1 Θ1 Hb Hinc.
  destruct Hb as [-> | [[Q ->] | [Q ->]]].
  - apply a_inc_tvar_inv in Hinc as [Ξ [Θ2 [Heq [HΞ Hinc']]]].
    destruct Ξ as [ | [Z bz] Ξ' ]; simpl in Heq.
    + inversion Heq; subst. exact Hinc'.
    + inversion Heq; subst. inversion HΞ; subst.
      match goal with H : a_suffix_binding abind_tvar |- _ => inversion H end.
  - apply a_inc_var_inv in Hinc as [Ξ [A' [Θ2 [Heq [Heqv [HΞ Hinc']]]]]].
    destruct Ξ as [ | [Z bz] Ξ' ]; simpl in Heq.
    + inversion Heq; subst. exact Hinc'.
    + inversion Heq; subst. inversion HΞ; subst.
      match goal with H : a_suffix_binding (abind_var_typ _) |- _ => inversion H end.
  - apply a_inc_var_skl_inv in Hinc as [Ξ [P' [Θ2 [Heq [Heqv [HΞ Hinc']]]]]].
    destruct Ξ as [ | [Z bz] Ξ' ]; simpl in Heq.
    + inversion Heq; subst. exact Hinc'.
    + inversion Heq; subst. inversion HΞ; subst.
      match goal with H : a_suffix_binding (abind_var_skl _) |- _ => inversion H end.
Qed.

(** ===================================================================
    MID-INSERT for [a_inc_equiv] (the Assign-Skip FLEX-walk crux).

    Assign-Skip drops the walked flexible [β] from the target, so its
    factoring must SPLICE [β] back into both metasubstitutions of the
    sub-node's [a_inc_equiv], between the pending-declaration prefix [Ξ]
    and [Θ0].  Splicing a matching flexible pair preserves [a_inc_equiv];
    the [Ξ]-prefix is peeled off both metasubstitutions (its length is
    [dom Ξ], all-flexible), and its heads re-consed.  The peel needs the
    two metasubstitutions to have DISTINCT keys, which follows from
    source uniqueness. *)

(** An [a_inc_equiv]'s metasubstitutions inherit the source's key
    distinctness (each flexible entry is source-fresh; the term/rigid
    entries leave the metasubstitution untouched). *)
Lemma a_inc_equiv_uniq_l : forall E ρ σ Θ,
  a_inc_equiv E ρ σ Θ -> uniq E -> uniq ρ.
Proof.
  intros E ρ σ Θ Hie; induction Hie; intros Hu; simpl in *.
  - constructor.
  - destruct_uniq. constructor; [ apply IHHie; solve_uniq | ].
    destruct (prop_normal.a_inc_equiv_dom Hie) as [Hd _]. fsetdec.
  - destruct_uniq. constructor; [ apply IHHie; solve_uniq | ].
    destruct (prop_normal.a_inc_equiv_dom Hie) as [Hd _]. fsetdec.
  - apply IHHie. solve_uniq.
  - apply IHHie. solve_uniq.
  - apply IHHie. solve_uniq.
Qed.

Lemma a_inc_equiv_uniq_r : forall E ρ σ Θ,
  a_inc_equiv E ρ σ Θ -> uniq E -> uniq σ.
Proof.
  intros E ρ σ Θ Hie; induction Hie; intros Hu; simpl in *.
  - constructor.
  - destruct_uniq. constructor; [ apply IHHie; solve_uniq | ].
    destruct (prop_normal.a_inc_equiv_dom Hie) as [_ Hd]. fsetdec.
  - destruct_uniq. constructor; [ apply IHHie; solve_uniq | ].
    destruct (prop_normal.a_inc_equiv_dom Hie) as [_ Hd]. fsetdec.
  - apply IHHie. solve_uniq.
  - apply IHHie. solve_uniq.
  - apply IHHie. solve_uniq.
Qed.

(** A metasubstitution with empty domain is [nil] ([dom nil] on the RHS is
    cross-type-opaque to [fsetdec], hence the membership detour). *)
Lemma metasubst_dom_empty : forall (r : metasubst),
  dom r [=] empty -> r = nil.
Proof.
  destruct r as [ | [a t] r' ]; intros H; [ reflexivity | exfalso ].
  assert (Ha : a `in` dom ((a, t) :: r')) by (simpl; fsetdec).
  rewrite H in Ha. clear - Ha. fsetdec.
Qed.

Lemma a_inc_equiv_mid_insert_flex :
  forall Ξ β Θ0 Θ ρ1 ρ2 σ1 σ2 τ1 τ2,
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom ρ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  Θ ⊢ τ1 ≡ᵗ τ2 ->
  a_inc_equiv (Ξ ++ Θ0) (ρ1 ++ ρ2) (σ1 ++ σ2) Θ ->
  a_inc_equiv (Ξ ++ (β ~ abind_flex_mono) ++ Θ0)
              (ρ1 ++ (β, τ1) :: ρ2) (σ1 ++ (β, τ2) :: σ2) Θ.
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros β Θ0 Θ ρ1 ρ2 σ1 σ2 τ1 τ2 Hdec Huq Hdρ Hdσ Heqτ Hie.
  - rewrite dom_nil in Hdρ, Hdσ.
    apply metasubst_dom_empty in Hdρ; apply metasubst_dom_empty in Hdσ; subst.
    simpl in Hie |- *.
    apply a_inc_equiv__flex; [ exact Hie | exact Heqτ ].
  - inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Huρ : uniq (ρ1 ++ ρ2))
      by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
    assert (Huσ : uniq (σ1 ++ σ2))
      by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
    assert (HaΞ : a `notin` dom Ξ') by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ Θ0)) by (clear - Huq; simpl_env in Huq; solve_uniq).
    destruct ρ1 as [ | [ar tr] ρ1' ];
      [ exfalso; rewrite dom_nil in Hdρ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ')) by (simpl; fsetdec);
        rewrite <- Hdρ in Hin; clear - Hin; fsetdec | ].
    destruct σ1 as [ | [asg ts] σ1' ];
      [ exfalso; rewrite dom_nil in Hdσ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ')) by (simpl; fsetdec);
        rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
    assert (Harρ : ar `notin` dom ρ1') by (clear - Huρ; simpl_env in Huρ; solve_uniq).
    assert (Hasσ : asg `notin` dom σ1') by (clear - Huσ; simpl_env in Huσ; solve_uniq).
    simpl in Hie.
    inversion Hie as [ | S q1 q2 T aa u1 u2 Hie' Hequ | | | | ]; subst.
    simpl_env in Hdρ; simpl_env in Hdσ.
    simpl. apply a_inc_equiv__flex; [ | exact Hequ ].
    apply IH; auto.
    + clear - Hdρ Harρ HaΞ. simpl_env in *. fsetdec.
    + clear - Hdσ Hasσ HaΞ. simpl_env in *. fsetdec.
Qed.

(** Looking up a variable other than the mid-inserted key ignores that entry. *)
Lemma msubst_lookup_mid_drop : forall ρa β τ ρb X,
  X <> β ->
  msubst_lookup (ρa ++ (β, τ) :: ρb) X = msubst_lookup (ρa ++ ρb) X.
Proof.
  induction ρa as [ | [a t] ρa' IH ]; intros β τ ρb X Hne; simpl.
  - destruct (X == β) as [-> | _]; [ contradiction | reflexivity ].
  - destruct (X == a) as [-> | _]; [ reflexivity | apply IH; exact Hne ].
Qed.

(** Composition distributes over an append of the RIGHT multiplicand. *)
Lemma msubst_compose_app : forall ζ ρ1 ρ2,
  msubst_compose ζ (ρ1 ++ ρ2) = msubst_compose ζ ρ1 ++ msubst_compose ζ ρ2.
Proof.
  intros ζ ρ1 ρ2. unfold msubst_compose.
  induction ρ1 as [ | e ρ1' IH ]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

(** Peel a declaration-only (all-flexible) PREFIX off a competing increment:
    the [Ξ]-part of [ρ] has domain [dom Ξ] and the tail increment survives.
    (Mirror of [a_inc_mid_strip_flex] for a prefix rather than a mid.  This is
    the first step of the Assign-SkipRigid / SkipTmVar walk-case decomposition;
    the remaining wiring is blocked on the walked-past middle's competing
    suffix [Ξv] — see [remech-optimality-bundle-progress] memory.) *)
Lemma a_inc_strip_decls_prefix : forall Ξ E ρ Θ,
  a_decls Ξ ->
  (Ξ ++ E) ≤[ ρ ] Θ ->
  exists ρ1 ρ2, ρ = ρ1 ++ ρ2 /\ dom ρ1 [=] dom Ξ /\ E ≤[ ρ2 ] Θ.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros E ρ Θ Hdec Hinc.
  - exists (@nil (atom * ptyp)), ρ. simpl.
    split; [ reflexivity | split; [ clear; fsetdec | exact Hinc ] ].
  - inversion Hdec as [ | γ Ξ'' Hdec' [Heq HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs ρs Θt αs τ Hinc' Hwfτ Hmτ [Heqα Heqρ] Heqt | | | | ];
      subst.
    destruct (IH E ρs Θ Hdec' Hinc') as [ρ1 [ρ2 [Heqr [Hdom Hincr]]]].
    exists ((a, τ) :: ρ1), ρ2. simpl.
    split; [ rewrite Heqr; reflexivity
           | split; [ rewrite Hdom; clear; fsetdec | exact Hincr ] ].
Qed.

(* ===================================================================== *)
(*  DOWNARROW-NORMALIZATION FOUNDATIONS (GMM Lemma 2.6 factoring).          *)
(*  The optimality walk cases build the factoring by replacing each         *)
(*  competing (mono) image by its ⇓ᵗ[Θ] normal form (unfolds Θ flex_defs;   *)
(*  e.g. ⇓[Th]δ̂=() in algo/cex/cex_assign_optimal_syn_middle.v).  ⇓ᵗ[Θ]      *)
(*  preserves mono and wf-in-Θ on monotypes (the only images normalized).   *)
(* ===================================================================== *)

(* msubst preserves mono when every image is mono. *)
Lemma msubst_ptyp_mono_pointwise : forall ζ A,
  (forall Y, mono_ptyp (msubst_lookup ζ Y)) ->
  mono_ptyp A ->
  mono_ptyp (msubst_ptyp ζ A).
Proof.
  intros ζ A Himg Hm; induction Hm; simpl.
  - apply mono_ptyp__unit.
  - apply Himg.
  - apply mono_ptyp__arrow; auto.
Qed.

(* Every image of the downarrow metasubst is a monotype. *)
Lemma aenv_msubst_image_mono : forall Θ,
  a_wf_aenv Θ ->
  forall X, mono_ptyp (msubst_lookup (aenv_msubst Θ) X).
Proof.
  intros Θ Hwf; induction Hwf; intros X; simpl.
  - apply mono_ptyp__var.
  - (* flex_mono β *) destruct (X == α) as [-> | Hne];
      [ apply mono_ptyp__var | apply IHHwf ].
  - (* flex_mono_def β ≔ τ *) destruct (X == α) as [-> | Hne].
    + apply msubst_ptyp_mono_pointwise; [ apply IHHwf | exact H1 ].
    + apply IHHwf.
  - (* var_skl *) apply IHHwf.
  - (* var_typ *) apply IHHwf.
  - (* tvar *) apply IHHwf.
Qed.

(* wf-preservation of msubst on a MONOTYPE (no ∀-case). *)
Lemma a_wf_ptyp_msubst_mono : forall Θ ζ A,
  mono_ptyp A -> a_wf_ptyp Θ A ->
  (forall Y, a_binds_tvar Y Θ -> a_wf_ptyp Θ (msubst_lookup ζ Y)) ->
  a_wf_ptyp Θ (msubst_ptyp ζ A).
Proof.
  intros Θ ζ A Hm; induction Hm; intros Hwa Himg; simpl.
  - apply a_wf_ptyp__unit.
  - inversion Hwa; subst. apply Himg; assumption.
  - inversion Hwa; subst. apply a_wf_ptyp__arrow; auto.
Qed.

Ltac wk := eapply a_wf_ptyp_weaken;
  [ intros ? ? Hb; unfold binds; simpl; right; exact Hb | ].

(* Every downarrow image (of a type var of Θ) is wf in Θ. *)
Lemma aenv_msubst_image_wf : forall Θ,
  a_wf_aenv Θ ->
  forall Y, a_binds_tvar Y Θ ->
  a_wf_ptyp Θ (msubst_lookup (aenv_msubst Θ) Y).
Proof.
  intros Θ Hwf; induction Hwf; intros Y Hbt; simpl.
  - destruct Hbt as [Hb|[Hb|[t Hb]]]; inversion Hb.
  - (* flex_mono α *) destruct (Y == α) as [-> | Hne].
    + apply a_wf_ptyp__var. right; left. unfold binds; left; reflexivity.
    + wk. apply IHHwf.
      destruct Hbt as [Hb|[Hb|[t Hb]]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He ?]|Hb'];
        try (exfalso; apply Hne; exact He);
        [ left | right;left | right;right;exists t ]; exact Hb'.
  - (* flex_mono_def α ≔ τ *) destruct (Y == α) as [-> | Hne].
    + wk. apply a_wf_ptyp_msubst_mono; [ exact H1 | exact H0 | ].
      intros Z Hz. apply IHHwf; exact Hz.
    + wk. apply IHHwf.
      destruct Hbt as [Hb|[Hb|[t Hb]]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He ?]|Hb'];
        try (exfalso; apply Hne; exact He);
        [ left | right;left | right;right;exists t ]; exact Hb'.
  - (* var_skl *) wk. apply IHHwf.
    destruct Hbt as [Hb|[Hb|[t Hb]]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He Hc]|Hb'];
      try discriminate; [ left | right;left | right;right;exists t ]; exact Hb'.
  - (* var_typ *) wk. apply IHHwf.
    destruct Hbt as [Hb|[Hb|[t Hb]]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He Hc]|Hb'];
      try discriminate; [ left | right;left | right;right;exists t ]; exact Hb'.
  - (* tvar α *) destruct (Y == α) as [-> | Hne].
    + rewrite msubst_lookup_notin.
      * apply a_wf_ptyp__var. left. unfold binds; left; reflexivity.
      * pose proof (dom_aenv_msubst Θ). simpl.
        assert (α `notin` dom Θ) by exact H. clear - H0 H1. fsetdec.
    + wk. apply IHHwf.
      destruct Hbt as [Hb|[Hb|[t Hb]]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He ?]|Hb'];
        try (exfalso; apply Hne; exact He);
        [ left | right;left | right;right;exists t ]; exact Hb'.
Qed.

(* TOP-LEVEL downarrow preservation on a monotype. *)
Lemma mono_downarrow : forall Θ τ,
  a_wf_aenv Θ -> a_wf_ptyp Θ τ -> mono_ptyp τ ->
  mono_ptyp (⇓ᵗ[ Θ ] τ).
Proof.
  intros Θ τ Hwf Hwp Hm.
  apply msubst_ptyp_mono_pointwise; [ | exact Hm ].
  intros Y. apply aenv_msubst_image_mono; exact Hwf.
Qed.

Lemma a_wf_ptyp_downarrow_mono : forall Θ τ,
  a_wf_aenv Θ -> a_wf_ptyp Θ τ -> mono_ptyp τ ->
  a_wf_ptyp Θ (⇓ᵗ[ Θ ] τ).
Proof.
  intros Θ τ Hwf Hwp Hm.
  apply a_wf_ptyp_msubst_mono; [ exact Hm | exact Hwp | ].
  intros Y Hy. apply aenv_msubst_image_wf; assumption.
Qed.

(* ---- downarrow SCOPING + the join-grounding crux (GMM Lemma 2.6, step 2) ---- *)
(*  ⇓ᵗ[Θ] of a type stays inside any def-closed set containing its ftv; and    *)
(*  (THE CRUX) a mono-join uskl(S) ≈ syn(mono C) forces ⇓ˢ[Θ]S scoped to any    *)
(*  def-closed D that scopes C — so the walked payload downarrows into the      *)
(*  sub-target.  Holes contribute no ftv; the ∀/inh cases cannot fire (C mono). *)

Lemma msubst_ptyp_ftv : forall ζ A X,
  X `in` ftvar_in_ptyp (msubst_ptyp ζ A) ->
  exists Y, Y `in` ftvar_in_ptyp A /\ X `in` ftvar_in_ptyp (msubst_lookup ζ Y).
Proof.
  intros ζ A; induction A as [ | n | Z | A1 IHA1 A2 IHA2 | A0 IHA0 ];
    intros X HX; simpl in *.
  - clear - HX; fsetdec.
  - clear - HX; fsetdec.
  - exists Z. split; [ fsetdec | exact HX ].
  - apply AtomSetImpl.union_1 in HX. destruct HX as [H1 | H2].
    + destruct (IHA1 X H1) as [Y [HY1 HY2]]. exists Y; split; [ fsetdec | exact HY2 ].
    + destruct (IHA2 X H2) as [Y [HY1 HY2]]. exists Y; split; [ fsetdec | exact HY2 ].
  - destruct (IHA0 X HX) as [Y [HY1 HY2]]. exists Y; split; [ fsetdec | exact HY2 ].
Qed.

(* Every downarrow image of a var in a def-closed set D stays in D. *)
Lemma aenv_msubst_image_ftv_closed : forall Θ,
  a_wf_aenv Θ ->
  forall D,
  (forall α τ, binds α (abind_flex_mono_def τ) Θ -> α `in` D -> ftvar_in_ptyp τ [<=] D) ->
  forall X, X `in` D ->
  ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) X) [<=] D.
Proof.
  intros Θ Hwf; induction Hwf; intros D Hcl X HXD; simpl.
  - (* nil *) clear - HXD; fsetdec.
  - (* flex_mono α *) destruct (X == α) as [-> | Hne].
    + simpl. clear - HXD; fsetdec.
    + apply IHHwf; [ | exact HXD ].
      intros β σ Hb Hβ. eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ].
  - (* flex_mono_def α ≔ τ *) destruct (X == α) as [-> | Hne].
    + (* image = msubst (aenv_msubst Θ) τ ; ftv τ ⊆ D by closure *)
      assert (Hτ : ftvar_in_ptyp τ [<=] D)
        by (eapply Hcl; [ unfold binds; left; reflexivity | exact HXD ]).
      intros Z HZ.
      destruct (msubst_ptyp_ftv _ _ HZ) as [W [HW1 HW2]].
      assert (HWD : W `in` D) by (clear - Hτ HW1; fsetdec).
      assert (Hsub : ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) W) [<=] D).
      { apply IHHwf; [ | exact HWD ].
        intros β σ Hb Hβ. eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ]. }
      clear - HW2 Hsub. fsetdec.
    + apply IHHwf; [ | exact HXD ].
      intros β σ Hb Hβ. eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ].
  - (* var_skl *) apply IHHwf; [ | exact HXD ].
    intros β σ Hb Hβ.
    eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ].
  - (* var_typ *) apply IHHwf; [ | exact HXD ].
    intros β σ Hb Hβ.
    eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ].
  - (* tvar α *) destruct (X == α) as [-> | Hne].
    + rewrite msubst_lookup_notin.
      * simpl. clear - HXD; fsetdec.
      * pose proof (dom_aenv_msubst Θ). assert (α `notin` dom Θ) by exact H.
        clear - H0 H1; fsetdec.
    + apply IHHwf; [ | exact HXD ].
      intros β σ Hb Hβ.
      eapply Hcl; [ unfold binds; right; exact Hb | exact Hβ ].
Qed.

Lemma downarrow_ftv_closed : forall Θ A D,
  a_wf_aenv Θ ->
  ftvar_in_ptyp A [<=] D ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ -> α `in` D -> ftvar_in_ptyp τ [<=] D) ->
  ftvar_in_ptyp (⇓ᵗ[ Θ ] A) [<=] D.
Proof.
  intros Θ A D Hwf HA Hcl X HX.
  destruct (msubst_ptyp_ftv _ _ HX) as [Y [HY1 HY2]].
  assert (HYD : Y `in` D) by (clear - HA HY1; fsetdec).
  eapply (aenv_msubst_image_ftv_closed Hwf Hcl HYD); exact HY2.
Qed.

Lemma join_pskl_downarrow_mono_scoped : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  a_wf_aenv Θ ->
  forall S0 C D,
    S = pskl_to_uskl S0 ->
    Q = ptyp_to_bskl_syn C -> mono_ptyp C ->
    (forall α τ, binds α (abind_flex_mono_def τ) Θ -> α `in` D -> ftvar_in_ptyp τ [<=] D) ->
    ftvar_in_ptyp C [<=] D ->
    ftvar_in_pskl (⇓ˢ[ Θ ] S0) [<=] D.
Proof.
  intros Ψ Θ S Q Hc Hwf; induction Hc;
    intros S0 C0 D HeqS HeqC HmC0 Hcl HCD;
    unfold ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct S0; simpl in HeqS; try discriminate.
    simpl. clear; fsetdec.
  - (* var *)
    destruct S0; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    simpl. rewrite ftvar_in_ptyp_to_pskl.
    match goal with
    | |- context[msubst_lookup ?r ?X] =>
        replace (msubst_lookup r X) with (⇓ᵗ[ Θ ] (ptyp_var_f X)) by reflexivity
    end.
    apply downarrow_ftv_closed;
      [ exact Hwf | simpl; clear - HCD; simpl in HCD; fsetdec | exact Hcl ].
  - (* arrow *)
    destruct S0 as [ | n | X | S01 S02 | S0a | | S0b ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    inversion HmC0 as [ | | ? ? HmC1 HmC2 ]; subst.
    simpl. intros Z HZ.
    apply AtomSetImpl.union_1 in HZ. destruct HZ as [HZl | HZr].
    + apply (IHHc1 Hwf S01 C1 D eq_refl eq_refl HmC1 Hcl
               ltac:(clear - HCD; simpl in HCD; fsetdec) Z HZl).
    + apply (IHHc2 Hwf S02 C2 D eq_refl eq_refl HmC2 Hcl
               ltac:(clear - HCD; simpl in HCD; fsetdec) Z HZr).
  - (* forall_inh_tagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_inh_untagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_syn_tagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_syn *) destruct HmC0; simpl in HeqC; discriminate.
  - (* ghostg *) destruct HmC0; simpl in HeqC; discriminate.
  - (* topholeg *) destruct HmC0; simpl in HeqC; discriminate.
  - (* hole : subject is a ghost hole, ⇓ contributes no ftv *)
    destruct S0; simpl in HeqS; try discriminate.
    simpl. clear; fsetdec.
  - (* tophole *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_inh *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_drop *)
    destruct S0 as [ | | | | | | S0t ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl. apply (IHHc Hwf S0t C0 D eq_refl eq_refl HmC0 Hcl HCD).
  - (* flex_l : subject is a defined flexible *)
    destruct S0 as [ | | Xv | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) Xv = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk.
    rewrite <- msubst_pskl_ptyp_to_pskl.
    apply (IHHc Hwf (ptyp_to_pskl τ) C0 D
             (eq_sym (ptyp_to_uskl_syn_eq τ)) eq_refl HmC0 Hcl HCD).
  - (* flex_r : join is a defined flexible *)
    destruct C0; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hτcl : ftvar_in_ptyp τ [<=] D).
    { eapply Hcl; [ exact H | ].
      clear - HCD; simpl in HCD; fsetdec. }
    apply (IHHc Hwf S0 τ D eq_refl eq_refl Hmτ Hcl Hτcl).
Qed.



(* ===================================================================== *)
(*  CONTEXT-STRENGTHENING for the join (ad_pat_consis) and skeleton-wf     *)
(*  (ad_wf_pskl) judgments — the SkipRigid / SkipTmVar walk cases move    *)
(*  the competing join from the grown target down to the sub-target.       *)
(* ===================================================================== *)

Lemma a_binds_tvar_strengthen : forall X Θ Θ',
  a_binds_tvar X Θ -> uniq Θ ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  X `in` dom Θ' -> a_binds_tvar X Θ'.
Proof.
  intros X Θ Θ' Hbt Hu Hsub Hin.
  apply binds_In_inv in Hin as [b' Hb'].
  pose proof (Hsub _ _ Hb') as HbΘ.
  destruct Hbt as [Hb | [Hb | [τ Hb]]];
    pose proof (binds_unique _ _ _ _ _ HbΘ Hb Hu) as ->;
    [ left | right; left | right; right; exists τ ]; exact Hb'.
Qed.

Lemma ad_wf_pskl_strengthen : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall Θ', uniq Θ ->
  (forall x, x `in` Δ -> x `notin` dom Θ) ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall X, X `in` ftvar_in_pskl P -> X `in` Δ \/ X `in` dom Θ') ->
  Θ' ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H; induction H; intros Θ' Hu Hdisj Hsub Hsc.
  - apply ad_wf_pskl__unit.
  - apply ad_wf_pskl__var.
    assert (HXin : X `in` ftvar_in_pskl (pskl_var_f X)) by (simpl; fsetdec).
    destruct (Hsc X HXin) as [HΔ | Hd]; [ left; exact HΔ | ].
    destruct H as [HΔ | Htv]; [ left; exact HΔ | ].
    right. eapply a_binds_tvar_strengthen; eauto.
  - apply ad_wf_pskl__arrow.
    + apply IHad_wf_pskl1; auto. intros X HX. apply Hsc. simpl. fsetdec.
    + apply IHad_wf_pskl2; auto. intros X HX. apply Hsc. simpl. fsetdec.
  - apply ad_wf_pskl__all with (L := L `union` dom Θ `union` dom Θ' `union` Δ).
    intros X HX. apply H0.
    + clear - HX; fsetdec.
    + exact Hu.
    + assert (HxnΘ : X `notin` dom Θ) by (clear - HX; fsetdec).
      intros y Hy. destruct (y == X) as [-> | Hyne];
        [ exact HxnΘ | apply Hdisj; clear - Hy Hyne; fsetdec ].
    + exact Hsub.
    + intros Y HY.
      destruct (Y == X) as [-> | Hne]; [ left; clear; fsetdec | ].
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f X)) as Hup.
      assert (HYP : Y `in` ftvar_in_pskl P) by (simpl in Hup; clear - HY Hup Hne; fsetdec).
      destruct (Hsc Y HYP) as [HΔ | Hd]; [ left; clear - HΔ; fsetdec | right; exact Hd ].
  - apply ad_wf_pskl__hole.
  - apply ad_wf_pskl__tophole; [ exact H | ].
    apply IHad_wf_pskl; auto.
    + intros y Hy; clear - Hy; fsetdec.
    + intros X HX. right.
      pose proof (ad_wf_pskl_ftv_tvarish H0 HX) as Htv.
      assert (HxΘ : X `in` dom Θ).
      { destruct Htv as [He | Ht]; [ clear - He; fsetdec | ].
        destruct Ht as [Hb|[Hb|[τ Hb]]]; apply binds_In in Hb; exact Hb. }
      assert (HXtop : X `in` ftvar_in_pskl (pskl_tophole P)) by (simpl; exact HX).
      destruct (Hsc X HXtop) as [HΔ | Hd]; [ | exact Hd ].
      exfalso. apply (Hdisj X HΔ). exact HxΘ.
Qed.

Lemma binds_strengthen : forall (X:atom) (b:abind) (Θ Θ':aenv),
  binds X b Θ -> uniq Θ ->
  (forall x b0, binds x b0 Θ' -> binds x b0 Θ) ->
  X `in` dom Θ' -> binds X b Θ'.
Proof.
  intros X b Θ Θ' Hb Hu Hsub Hin.
  apply binds_In_inv in Hin as [b' Hb'].
  pose proof (Hsub _ _ Hb') as HbΘ.
  pose proof (binds_unique _ _ _ _ _ HbΘ Hb Hu) as ->. exact Hb'.
Qed.

Lemma binds_sub_cons : forall (e:aenv) Θ Θ',
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  forall x b, binds x b (e ++ Θ') -> binds x b (e ++ Θ).
Proof.
  intros e Θ Θ' Hsub x b Hb.
  apply binds_app_1 in Hb. destruct Hb as [H1 | H2];
    [ apply binds_app_2 | apply binds_app_3; apply Hsub ]; assumption.
Qed.

Ltac str_forall H0 Hu Hwf' Hsub HscS HscQ Rr Qq X HX openU openB :=
  apply H0;
  [ clear - HX; fsetdec
  | simpl_env; apply uniq_push; [ exact Hu | clear - HX; fsetdec ]
  | apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf' ]
  | apply binds_sub_cons with (e := (X ~ abind_tvar)); exact Hsub
  | intros Y HY;
    pose proof (openU Rr (uskl_var_f X)) as HupU; simpl in HupU;
    destruct (Y == X) as [-> | Hne]; [ simpl; clear; fsetdec | ];
    simpl; apply AtomSetImpl.add_2; apply HscS; clear - HY HupU Hne; fsetdec
  | intros Y HY;
    pose proof (openB Qq (bskl_var_f X)) as HupB; simpl in HupB;
    destruct (Y == X) as [-> | Hne]; [ simpl; clear; fsetdec | ];
    simpl; apply AtomSetImpl.add_2; apply HscQ; clear - HY HupB Hne; fsetdec ].

Lemma ad_pat_consis_strengthen : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  forall Θ', uniq Θ -> a_wf_aenv Θ' ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall X, X `in` ftvar_in_uskl S -> X `in` dom Θ') ->
  (forall X, X `in` ftvar_in_bskl Q -> X `in` dom Θ') ->
  Ψ ⨟ Θ' ⊨ₛᵃ S ≈ Q.
Proof.
  intros Ψ Θ S Q H; induction H;
    intros Θ' Hu Hwf' Hsub HscS HscQ; simpl in *.
  - apply ad_pat_consis__unit; auto.
  - apply ad_pat_consis__var; [ assumption | ].
    eapply a_binds_tvar_strengthen;
      [ eassumption | exact Hu | exact Hsub | apply HscS; fsetdec ].
  - eapply ad_pat_consis__arrow; [ | | exact H1 ].
    + apply IHad_pat_consis1; auto; intros X HX;
        solve [ apply HscS; fsetdec | apply HscQ; fsetdec ].
    + apply IHad_pat_consis2; auto; intros X HX;
        solve [ apply HscS; fsetdec | apply HscQ; fsetdec ].
  - eapply ad_pat_consis__forall_inh_tagged
      with (L := L `union` dom Θ `union` dom Θ'); [ | exact H1 ].
    intros X HX.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q X HX
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_inh_untagged
      with (L := L `union` dom Θ `union` dom Θ').
    intros X HX.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q X HX
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_syn_tagged
      with (L := L `union` dom Θ `union` dom Θ').
    intros X HX.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q X HX
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_syn
      with (L := L `union` dom Θ `union` dom Θ').
    intros X HX.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q X HX
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - apply ad_pat_consis__ghostg; auto.
  - apply ad_pat_consis__topholeg. apply IHad_pat_consis; auto.
  - apply ad_pat_consis__hole; auto.
    eapply ad_wf_pskl_strengthen; [ exact H0 | exact Hu | intros y Hy; clear - Hy; fsetdec | exact Hsub | ].
    intros X HX. right. apply HscQ.
    pose proof (ftvar_in_bskl_inh P) as Hb. clear - HX Hb. fsetdec.
  - apply ad_pat_consis__tophole. apply IHad_pat_consis; auto.
  - eapply ad_pat_consis__tophole_inh
      with (L := L `union` dom Θ `union` dom Θ').
    intros X HX.
    apply H0.
    + clear - HX; fsetdec.
    + simpl_env; apply uniq_push; [ exact Hu | clear - HX; fsetdec ].
    + apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf' ].
    + apply binds_sub_cons with (e := (X ~ abind_tvar)); exact Hsub.
    + intros Y HY. simpl in HY. simpl.
      apply AtomSetImpl.add_2. apply HscS; exact HY.
    + intros Y HY.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f X)) as HupB;
        simpl in HupB.
      destruct (Y == X) as [-> | Hne]; [ simpl; clear; fsetdec | ].
      simpl. apply AtomSetImpl.add_2. apply HscQ; clear - HY HupB Hne; fsetdec.
  - apply ad_pat_consis__tophole_drop. apply IHad_pat_consis; auto.
  - eapply ad_pat_consis__flex_l.
    + eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscS; fsetdec ].
    + apply IHad_pat_consis; auto.
      intros X HX.
      assert (Hbd' : binds α (abind_flex_mono_def τ) Θ')
        by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscS; fsetdec ]).
      assert (Hwfτ : a_wf_ptyp Θ' τ) by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hbd' ]).
      pose proof (a_wf_ptyp_ftv_dom' Hwfτ) as Hftv.
      pose proof (ftvar_in_uskl_ptyp_syn τ) as Hco.
      clear - HX Hftv Hco. fsetdec.
  - eapply ad_pat_consis__flex_r.
    + eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscQ; fsetdec ].
    + apply IHad_pat_consis; auto.
      intros X HX.
      assert (Hbd' : binds α (abind_flex_mono_def τ) Θ')
        by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscQ; fsetdec ]).
      assert (Hwfτ : a_wf_ptyp Θ' τ) by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hbd' ]).
      pose proof (a_wf_ptyp_ftv_dom' Hwfτ) as Hftv.
      pose proof (ftvar_in_bskl_ptyp_syn τ) as Hco.
      clear - HX Hftv Hco. fsetdec.
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
    [ρ1]/[ρ2] over unchanged and split the target at a suffix. *)
Lemma a_inc_equiv_tvar_inv : forall α Θ0 ρ1 ρ2 Θ,
  a_inc_equiv ((α ~ abind_tvar) ++ Θ0) ρ1 ρ2 Θ ->
  exists Ξ Θ', Θ = Ξ ++ (α ~ abind_tvar) ++ Θ'
             /\ a_suffix Ξ /\ a_inc_equiv Θ0 ρ1 ρ2 Θ'.
Proof. intros * H; inversion H; subst; eauto 8. Qed.

Lemma a_inc_equiv_var_typ_inv : forall x A Θ0 ρ1 ρ2 Θ,
  a_inc_equiv ((x ~ abind_var_typ A) ++ Θ0) ρ1 ρ2 Θ ->
  exists Ξ A' Θ', Θ = Ξ ++ (x ~ abind_var_typ A') ++ Θ'
             /\ (Θ' ⊢ A' ≡ᵗ (msubst_ptyp ρ1 A))
             /\ a_suffix Ξ /\ a_inc_equiv Θ0 ρ1 ρ2 Θ'.
Proof. intros * H; inversion H; subst; eauto 10. Qed.

Lemma a_inc_equiv_var_skl_inv : forall x P Θ0 ρ1 ρ2 Θ,
  a_inc_equiv ((x ~ abind_var_skl P) ++ Θ0) ρ1 ρ2 Θ ->
  exists Ξ P' Θ', Θ = Ξ ++ (x ~ abind_var_skl P') ++ Θ'
             /\ (Θ' ⊢ P' ≡ˢ (msubst_pskl ρ1 P))
             /\ a_suffix Ξ /\ a_inc_equiv Θ0 ρ1 ρ2 Θ'.
Proof. intros * H; inversion H; subst; eauto 10. Qed.

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
Lemma a_inc_equiv_trans : forall Θ0 ρa ρb Θ,
  a_inc_equiv Θ0 ρa ρb Θ ->
  forall ρc,
  a_wf_aenv Θ ->
  a_inc_equiv Θ0 ρb ρc Θ ->
  a_inc_equiv Θ0 ρa ρc Θ.
Proof.
  intros Θ0 ρa ρb Θ Hab; induction Hab; intros ρc Hwf Hbc.
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
  - (* var_typ x : realign, then rebuild (the first equivalence's semantic
       middle premise is reused verbatim) *)
    destruct (a_inc_equiv_var_typ_inv Hbc)
      as [Xic [Ac' [Tc [Heqt [Heqvc [Hsc Hrec]]]]]].
    pose proof (a_wf_aenv_uniq_local Hwf) as Hu.
    destruct (aenv_mid_split _ _ _ _ _ _ _ Hu Heqt) as [HeqΞ [Heqb HeqΘ]].
    injection Heqb as HeqA. subst.
    apply a_wf_aenv_strip_prefix_local in Hwf.
    inversion Hwf; subst.
    apply a_inc_equiv__var;
      [ apply IHHab; assumption | assumption | assumption ].
  - (* var_skl x *)
    destruct (a_inc_equiv_var_skl_inv Hbc)
      as [Xic [Pc' [Tc [Heqt [Heqvc [Hsc Hrec]]]]]].
    pose proof (a_wf_aenv_uniq_local Hwf) as Hu.
    destruct (aenv_mid_split _ _ _ _ _ _ _ Hu Heqt) as [HeqΞ [Heqb HeqΘ]].
    injection Heqb as HeqP. subst.
    apply a_wf_aenv_strip_prefix_local in Hwf.
    inversion Hwf; subst.
    apply a_inc_equiv__var_skl;
      [ apply IHHab; assumption | assumption | assumption ].
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
Lemma a_inc_equiv_compose : forall Θ0 ρ Θmid,
  Θ0 ≤[ ρ ] Θmid ->
  a_wf_aenv Θ0 -> a_wf_aenv Θmid ->
  forall ρ1 ρ2 Θ,
  a_wf_aenv Θ ->
  a_inc_equiv Θmid ρ1 ρ2 Θ ->
  Θmid ≤[ ρ1 ] Θ -> Θmid ≤[ ρ2 ] Θ ->
  a_inc_equiv Θ0 (msubst_compose ρ1 ρ) (msubst_compose ρ2 ρ) Θ.
Proof.
  intros Θ0 ρ Θmid Hρ; induction Hρ;
    intros Hwf0 Hwf1 ρ1 ρ2 Θt HwfT Hie Hi1 Hi2.
  - (* empty : source all-flexible, so target all-flexible *)
    simpl. apply a_inc_equiv__empty.
    eapply a_inc_equiv_suffix_target; [ exact Hie | assumption ].
  - (* flex α *)
    inversion Hwf0 as [ | αh Θh Hnd Hwa | | | | ]; subst.
    simpl. apply a_inc_equiv__flex.
    + apply IHHρ; auto.
    + eapply a_inc_equiv_msubst_mono;
        [ exact Hie | exact Hwf1 | eassumption | assumption ].
  - (* flex_def α := τ *)
    inversion Hwf0 as [ | | αh τh Θh Hnd Hwp Hm Hwa | | | ]; subst.
    simpl. apply a_inc_equiv__flex_def.
    + apply IHHρ; auto.
    + eapply a_inc_equiv_msubst_mono;
        [ exact Hie | exact Hwf1 | eassumption | assumption ].
    + rewrite msubst_ptyp_compose.
      * eapply a_tyequiv_msubst; [ eassumption | exact Hwf1 | exact Hi1 ].
      * intros X HX.
        eapply a_inc_compose_vis;
          [ exact Hρ | exact Hi1 | exact Hwa | exact Hwf1
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
      [ exact H0 | exact Hie | exact Hi1 | exact Hi2 | ].
    destruct (a_inc_equiv_var_typ_inv Hie2)
      as [Ξe [Ae' [Te [Heqe [Heqve [Hse Hie3]]]]]].
    destruct (a_inc_var_inv Hib1) as [Ξ1 [A1' [T1 [Heq1 [Heqv1 [Hs1 Hib1']]]]]].
    destruct (a_inc_var_inv Hib2) as [Ξ2 [A2' [T2 [Heq2 [Heqv2 [Hs2 Hib2']]]]]].
    pose proof (a_wf_aenv_uniq_local HwfT) as HuT.
    rewrite Heqe in HuT.
    assert (HeqE1 : Ξe ++ (x ~ abind_var_typ Ae') ++ Te
                  = Ξ1 ++ (x ~ abind_var_typ A1') ++ T1)
      by (rewrite <- Heqe; exact Heq1).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE1) as [HE1 [HB1 HT1]].
    injection HB1 as HB1. subst A1' T1.
    assert (HeqE2 : Ξe ++ (x ~ abind_var_typ Ae') ++ Te
                  = Ξ2 ++ (x ~ abind_var_typ A2') ++ T2)
      by (rewrite <- Heqe; exact Heq2).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE2) as [HE2 [HB2 HT2]].
    injection HB2 as HB2. subst A2' T2.
    assert (Hc1 : msubst_compose ρ1 ρ = msubst_compose ρ1b ρ)
      by (rewrite Hp1; eapply msubst_compose_peel;
          [ exact Hρ | intros X HX; apply Hdisj; rewrite <- Hdp1; exact HX ]).
    assert (Hc2 : msubst_compose ρ2 ρ = msubst_compose ρ2b ρ)
      by (rewrite Hp2; eapply msubst_compose_peel;
          [ exact Hρ | intros X HX; apply Hdisj; rewrite <- Hdp2; exact HX ]).
    rewrite Hc1, Hc2, Heqe.
    assert (HwfTe : a_wf_aenv Te).
    { rewrite Heqe in HwfT. apply a_wf_aenv_strip_prefix_local in HwfT.
      inversion HwfT; subst; assumption. }
    apply a_inc_equiv__var; [ | | exact Hse ].
    { apply IHHρ; auto. }
    (* the composed semantic middle *)
    assert (HA : msubst_ptyp (msubst_compose ρ1b ρ) A
               = msubst_ptyp ρ1b (msubst_ptyp ρ A)).
    { apply msubst_ptyp_compose. intros X HX.
      eapply a_inc_compose_vis;
        [ exact Hρ | exact Hib1' | exact Hwa | exact Hwf1t
        | eapply a_wf_ptyp_ftv_tvarish; eauto ]. }
    rewrite HA.
    eapply a_tyequiv__trans; [ exact Heqve | ].
    eapply a_tyequiv_msubst; [ exact H | exact Hwf1t | exact Hib1' ].
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
      [ exact H0 | exact Hie | exact Hi1 | exact Hi2 | ].
    destruct (a_inc_equiv_var_skl_inv Hie2)
      as [Ξe [Pe' [Te [Heqe [Heqve [Hse Hie3]]]]]].
    destruct (a_inc_var_skl_inv Hib1) as [Ξ1 [P1' [T1 [Heq1 [Heqv1 [Hs1 Hib1']]]]]].
    destruct (a_inc_var_skl_inv Hib2) as [Ξ2 [P2' [T2 [Heq2 [Heqv2 [Hs2 Hib2']]]]]].
    pose proof (a_wf_aenv_uniq_local HwfT) as HuT.
    rewrite Heqe in HuT.
    assert (HeqE1 : Ξe ++ (x ~ abind_var_skl Pe') ++ Te
                  = Ξ1 ++ (x ~ abind_var_skl P1') ++ T1)
      by (rewrite <- Heqe; exact Heq1).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE1) as [HE1 [HB1 HT1]].
    injection HB1 as HB1. subst P1' T1.
    assert (HeqE2 : Ξe ++ (x ~ abind_var_skl Pe') ++ Te
                  = Ξ2 ++ (x ~ abind_var_skl P2') ++ T2)
      by (rewrite <- Heqe; exact Heq2).
    destruct (aenv_mid_split _ _ _ _ _ _ _ HuT HeqE2) as [HE2 [HB2 HT2]].
    injection HB2 as HB2. subst P2' T2.
    assert (Hc1 : msubst_compose ρ1 ρ = msubst_compose ρ1b ρ)
      by (rewrite Hp1; eapply msubst_compose_peel;
          [ exact Hρ | intros X HX; apply Hdisj; rewrite <- Hdp1; exact HX ]).
    assert (Hc2 : msubst_compose ρ2 ρ = msubst_compose ρ2b ρ)
      by (rewrite Hp2; eapply msubst_compose_peel;
          [ exact Hρ | intros X HX; apply Hdisj; rewrite <- Hdp2; exact HX ]).
    rewrite Hc1, Hc2, Heqe.
    assert (HwfTe : a_wf_aenv Te).
    { rewrite Heqe in HwfT. apply a_wf_aenv_strip_prefix_local in HwfT.
      inversion HwfT; subst; assumption. }
    apply a_inc_equiv__var_skl; [ | | exact Hse ].
    { apply IHHρ; auto. }
    assert (HP : msubst_pskl (msubst_compose ρ1b ρ) P
               = msubst_pskl ρ1b (msubst_pskl ρ P)).
    { apply msubst_pskl_compose. intros X HX.
      eapply a_inc_compose_vis;
        [ exact Hρ | exact Hib1' | exact Hwa | exact Hwf1t
        | eapply a_wf_pskl_ftv_tvarish; eauto ]. }
    rewrite HP.
    eapply a_pskl_tyequiv__trans; [ exact Heqve | ].
    eapply a_pskl_tyequiv_msubst; [ exact H | exact Hwf1t | exact Hib1' ].
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
    assert (Hc1 : msubst_compose ρ1 ρ = msubst_compose ρ1b ρ)
      by (rewrite Hp1; eapply msubst_compose_peel;
          [ exact Hρ | intros X HX; apply Hdisj; rewrite <- Hdp1; exact HX ]).
    assert (Hc2 : msubst_compose ρ2 ρ = msubst_compose ρ2b ρ)
      by (rewrite Hp2; eapply msubst_compose_peel;
          [ exact Hρ | intros X HX; apply Hdisj; rewrite <- Hdp2; exact HX ]).
    rewrite Hc1, Hc2, Heqe.
    apply a_inc_equiv__tvar; [ | exact Hse ].
    assert (HwfTe : a_wf_aenv Te).
    { rewrite Heqe in HwfT. apply a_wf_aenv_strip_prefix_local in HwfT.
      inversion HwfT; subst; assumption. }
    apply IHHρ; auto.
Qed.

(* ===================================================================== *)
(*  The composed factoring, assembled from CONGRUENCE + TRANSITIVITY.      *)
(* ===================================================================== *)

(** With [ρ1a], [ρ1b] both identity metasubstitutions and every [ρ1a]-flexible
    still [ρ1b]-flexible, an inner id-composition on the right collapses:
    [(ζ∘ρ1b)∘ρ1a = ζ∘ρ1a].  (The domain side condition rules out a [ρ1a]-flex
    that was rigidified by [ρ1b]'s source-extension; in the bundle it is the
    flex-preservation carried by [Θ0 ⊴ Θmid ⊴ Θfin].) *)
Lemma msubst_compose_id_compose : forall ρ1a ρ1b ζ,
  is_id_msubst ρ1a -> is_id_msubst ρ1b ->
  (forall α, α `in` dom ρ1a -> α `in` dom ρ1b) ->
  msubst_compose (msubst_compose ζ ρ1b) ρ1a = msubst_compose ζ ρ1a.
Proof.
  intros ρ1a ρ1b ζ Hida Hidb Hdom.
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
    a UnivGhost split) compose into the whole node's factoring.  [ρ1a]/[ρ1b] are
    the two sub-nodes' identity solution-witnesses. *)
Lemma a_inc_equiv_glue : forall Θ0 Θmid Θfin Θ ρ ρ1a ρ1b ζ1 ζ2,
  a_wf_aenv Θ0 -> a_wf_aenv Θmid -> a_wf_aenv Θfin -> a_wf_aenv Θ ->
  is_id_msubst ρ1a -> is_id_msubst ρ1b ->
  (forall α, α `in` dom ρ1a -> α `in` dom ρ1b) ->
  Θ0 ≤[ ρ1a ] Θmid ->
  Θmid ≤[ ρ1b ] Θfin ->
  Θmid ≤[ ζ1 ] Θ ->
  Θfin ≤[ ζ2 ] Θ ->
  a_inc_equiv Θ0 ρ (msubst_compose ζ1 ρ1a) Θ ->
  a_inc_equiv Θmid ζ1 (msubst_compose ζ2 ρ1b) Θ ->
  a_inc_equiv Θ0 ρ (msubst_compose ζ2 ρ1a) Θ.
Proof.
  intros Θ0 Θmid Θfin Θ ρ ρ1a ρ1b ζ1 ζ2
         Hwf0 Hwfm Hwff HwfT Hida Hidb Hdom Ha Hb Hζ1 Hζ2 Hsub1 Hsub2.
  (* the second increment through Θfin *)
  assert (Hζ2b : Θmid ≤[ msubst_compose ζ2 ρ1b ] Θ)
    by (eapply a_inc_compose; [ exact Hb | exact Hwfm | exact Hwff | exact Hζ2 ]).
  (* congruence: push σ = ρ1a onto sub2 *)
  pose proof (a_inc_equiv_compose Ha Hwf0 Hwfm HwfT Hsub2 Hζ1 Hζ2b) as Hcong.
  (* simplify the inner id-composition *)
  rewrite (msubst_compose_id_compose ζ2 Hida Hidb Hdom) in Hcong.
  (* transitivity with sub1 *)
  eapply a_inc_equiv_trans; [ exact Hsub1 | exact HwfT | exact Hcong ].
Qed.

(* ===================================================================== *)
(*  6b.  ≡ᵗ CONTEXT-STRENGTHENING (for Flex-Flex-Skip')                     *)
(*                                                                        *)
(*  When a competing solution's target GROWS across a rigid/term binding   *)
(*  (Flex-Flex-Skip'), the [≡ᵗ] equality [Θ ⊢ A ≡ᵗ B] must be strengthened *)
(*  to the sub-target [Θt] over which both endpoints are wf.  This is NOT  *)
(*  a bare structural strip (≡ᵗ's trans can route through intermediates    *)
(*  mentioning the dropped binding); it goes through the normal form       *)
(*  [⇓ᵗ] (prop_normal.v): [⇓] is [≡ᵗ]-invariant [a_tyequiv_downarrow],     *)
(*  [⇓] ignores entries above a suffix [downarrow_app_agree_ptyp], and     *)
(*  every wf MONOtype is [≡ᵗ] to its own normal form                       *)
(*  [a_tyequiv_to_downarrow_mono].  The endpoints here are the increment   *)
(*  images [msubst_lookup ρ α/β] — MONOtypes — so no [∀]-binder case ever  *)
(*  arises.                                                                *)
(* ===================================================================== *)

(** Entries ABOVE a suffix do not change the normal form of a type whose free
    variables all live in the suffix. *)
Lemma downarrow_app_agree_ptyp : forall Θp Θs A,
  uniq (Θp ++ Θs) ->
  ftvar_in_ptyp A [<=] dom Θs ->
  ⇓ᵗ[ Θp ++ Θs ] A = ⇓ᵗ[ Θs ] A.
Proof.
  intros Θp Θs A Hu; induction A; intros Hsub; simpl in *.
  - reflexivity.
  - reflexivity.
  - apply aenv_msubst_lookup_app; [ exact Hu | clear - Hsub; fsetdec ].
  - f_equal; [ apply IHA1 | apply IHA2 ]; clear - Hsub; fsetdec.
  - f_equal; apply IHA; clear - Hsub; fsetdec.
Qed.

(** A wf type's free variables live in the context's domain. *)
Lemma a_wf_ptyp_ftv_dom : forall Θ A,
  a_wf_ptyp Θ A -> ftvar_in_ptyp A [<=] dom Θ.
Proof.
  intros Θ A H X HX.
  apply (a_wf_ptyp_ftv_tvarish H) in HX.
  destruct HX as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

(** [aenv_msubst] on a flex / flex-def head (reflexivity, exposing the cons so
    that [msubst_lookup_cons_eq]/[_neq] can fire). *)
Lemma aenv_msubst_flex_head : forall α Θ,
  aenv_msubst ((α ~ abind_flex_mono) ++ Θ) = (α, ptyp_var_f α) :: aenv_msubst Θ.
Proof. reflexivity. Qed.

Lemma aenv_msubst_flex_def_head : forall α τ Θ,
  aenv_msubst ((α ~ abind_flex_mono_def τ) ++ Θ)
    = (α, ⇓ᵗ[ Θ ] τ) :: aenv_msubst Θ.
Proof. reflexivity. Qed.

(** Given the var-leaf equivalence, every wf MONOtype is [≡ᵗ] its normal form. *)
Lemma mono_downarrow_from_var : forall Θ,
  (forall X, a_binds_tvar X Θ -> Θ ⊢ (ptyp_var_f X) ≡ᵗ ⇓ᵗ[Θ] (ptyp_var_f X)) ->
  forall τ, a_wf_ptyp Θ τ -> mono_ptyp τ -> Θ ⊢ τ ≡ᵗ ⇓ᵗ[Θ] τ.
Proof.
  intros Θ Hvar τ Hwfτ Hmono; revert Hwfτ; induction Hmono; intros Hwfτ.
  - simpl. apply a_tyequiv__refl. constructor.
  - apply Hvar. inversion Hwfτ; subst. auto.
  - inversion Hwfτ; subst. simpl.
    apply a_tyequiv__arrow; [ apply IHHmono1 | apply IHHmono2 ]; auto.
Qed.

(** Every wf MONOtype is [≡ᵗ]-equivalent to its own normal form. *)
Lemma a_tyequiv_to_downarrow_mono : forall Θ,
  a_wf_aenv Θ ->
  forall τ, a_wf_ptyp Θ τ -> mono_ptyp τ -> Θ ⊢ τ ≡ᵗ ⇓ᵗ[Θ] τ.
Proof.
  intros Θ Hwf; induction Hwf as
    [ | α Θ' Hnd Hwf IH
      | α σ Θ' Hnd Hwpσ Hmσ Hwf IH
      | x P Θ' Hnd Hwp Hwf IH
      | x A0 Θ' Hnd Hwp Hwf IH
      | α Θ' Hnd Hwf IH ];
    apply mono_downarrow_from_var; intros X HX.
  - (* nil: no tvar binding *)
    exfalso. destruct HX as [Hb | [Hb | [t Hb]]]; inversion Hb.
  - (* head = undefined flex α *)
    cbn [msubst_ptyp]. rewrite aenv_msubst_flex_head.
    destruct (X == α) as [Heq | Hne].
    + subst X. rewrite msubst_lookup_cons_eq. apply a_tyequiv__refl. constructor.
    + rewrite msubst_lookup_cons_neq by auto.
      assert (HbΘ' : a_binds_tvar X Θ').
      { destruct HX as [Hb | [Hb | [t Hb]]];
          [ left | right; left | right; right; exists t ];
          (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
           [ congruence | exact Hb' ]). }
      apply a_tyequiv_weaken_cons.
      apply (IH (ptyp_var_f X)); [ apply a_wf_ptyp__var; exact HbΘ' | constructor ].
  - (* head = definition α := σ *)
    cbn [msubst_ptyp]. rewrite aenv_msubst_flex_def_head.
    destruct (X == α) as [Heq | Hne].
    + subst X. rewrite msubst_lookup_cons_eq.
      eapply a_tyequiv__trans.
      * apply a_tyequiv__flex_def. unfold binds; simpl; left; reflexivity.
      * apply a_tyequiv_weaken_cons. apply (IH σ Hwpσ Hmσ).
    + rewrite msubst_lookup_cons_neq by auto.
      assert (HbΘ' : a_binds_tvar X Θ').
      { destruct HX as [Hb | [Hb | [t Hb]]];
          [ left | right; left | right; right; exists t ];
          (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
           [ congruence | exact Hb' ]). }
      apply a_tyequiv_weaken_cons.
      apply (IH (ptyp_var_f X)); [ apply a_wf_ptyp__var; exact HbΘ' | constructor ].
  - (* head = term skeleton x : P (⇓ drops it) *)
    assert (HbΘ' : a_binds_tvar X Θ').
    { destruct HX as [Hb | [Hb | [t Hb]]];
        [ left | right; left | right; right; exists t ];
        (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
         [ discriminate | exact Hb' ]). }
    change (⇓ᵗ[ (x ~ abind_var_skl P) ++ Θ' ] (ptyp_var_f X))
      with (⇓ᵗ[ Θ' ] (ptyp_var_f X)).
    apply a_tyequiv_weaken_cons.
    apply (IH (ptyp_var_f X)); [ apply a_wf_ptyp__var; exact HbΘ' | constructor ].
  - (* head = term type x : A0 (⇓ drops it) *)
    assert (HbΘ' : a_binds_tvar X Θ').
    { destruct HX as [Hb | [Hb | [t Hb]]];
        [ left | right; left | right; right; exists t ];
        (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
         [ discriminate | exact Hb' ]). }
    change (⇓ᵗ[ (x ~ abind_var_typ A0) ++ Θ' ] (ptyp_var_f X))
      with (⇓ᵗ[ Θ' ] (ptyp_var_f X)).
    apply a_tyequiv_weaken_cons.
    apply (IH (ptyp_var_f X)); [ apply a_wf_ptyp__var; exact HbΘ' | constructor ].
  - (* head = rigid α (⇓ drops it) *)
    change (⇓ᵗ[ (α ~ abind_tvar) ++ Θ' ] (ptyp_var_f X))
      with (⇓ᵗ[ Θ' ] (ptyp_var_f X)).
    destruct (X == α) as [Heq | Hne].
    + subst X. cbn [msubst_ptyp]. rewrite aenv_msubst_notin by auto.
      apply a_tyequiv__refl. constructor.
    + assert (HbΘ' : a_binds_tvar X Θ').
      { destruct HX as [Hb | [Hb | [t Hb]]];
          [ left | right; left | right; right; exists t ];
          (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
           [ congruence | exact Hb' ]). }
      apply a_tyequiv_weaken_cons.
      apply (IH (ptyp_var_f X)); [ apply a_wf_ptyp__var; exact HbΘ' | constructor ].
Qed.

(* Poly generalization of a_tyequiv_to_downarrow_mono: any wf type (incl. ∀) is
   ≡ᵗ its downarrow.  Needed for a_inc_self_downarrow's var/flex_def middle
   re-proof, where the middle type may be a polytype. *)
Lemma a_tyequiv_to_downarrow : forall Θ A,
  a_wf_ptyp Θ A -> a_wf_aenv Θ -> Θ ⊢ A ≡ᵗ (⇓ᵗ[ Θ ] A).
Proof.
  intros Θ A Hwp; induction Hwp; intros Hwf.
  - simpl. apply a_tyequiv__refl. constructor.
  - apply a_tyequiv_to_downarrow_mono;
      [ exact Hwf | apply a_wf_ptyp__var; assumption | constructor ].
  - simpl. apply a_tyequiv__arrow; [ apply IHHwp1 | apply IHHwp2 ]; exact Hwf.
  - simpl. apply a_tyequiv__all with (L := L `union` dom Θ). intros X HX.
    assert (HxΘ : X `notin` dom Θ) by (clear - HX; fsetdec).
    assert (Hwfx : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ exact HxΘ | exact Hwf ]).
    specialize (H0 X ltac:(clear - HX; fsetdec) Hwfx).
    assert (Hcomm : ⇓ᵗ[ (X ~ abind_tvar) ++ Θ ] (open_ptyp_wrt_ptyp A (ptyp_var_f X))
                    = open_ptyp_wrt_ptyp (⇓ᵗ[ Θ ] A) (ptyp_var_f X)).
    { replace (aenv_msubst ((X ~ abind_tvar) ++ Θ)) with (aenv_msubst Θ)
        by (symmetry; apply aenv_msubst_tvar).
      apply msubst_ptyp_open_lc;
        [ apply aenv_msubst_lc; exact Hwf
        | rewrite dom_aenv_msubst; exact HxΘ ]. }
    rewrite Hcomm in H0.
    eapply a_tyequiv_strengthen_tvar_cons; [ exact H0 | reflexivity ].
Qed.

(* The middle-≡ adjustment for a_inc_self_downarrow: msubst ρ A ≡ its ⇓-composed
   form, when msubst ρ A is wf in the (suffix) sub-target Θt of Θ. *)
Lemma msubst_downarrow_tyequiv : forall Θ Θpre Θt B,
  Θ = Θpre ++ Θt -> uniq Θ -> a_wf_aenv Θt ->
  a_wf_ptyp Θt B ->
  Θt ⊢ B ≡ᵗ (⇓ᵗ[ Θ ] B).
Proof.
  intros Θ Θpre Θt B HeqΘ Huq Hwfaenv HwfB. subst Θ.
  rewrite (downarrow_app_agree_ptyp Θpre Θt B Huq (a_wf_ptyp_ftv_dom HwfB)).
  apply a_tyequiv_to_downarrow; [ exact HwfB | exact Hwfaenv ].
Qed.

Lemma a_wf_aenv_app_r : forall Θp Θs,
  a_wf_aenv (Θp ++ Θs) -> a_wf_aenv Θs.
Proof.
  induction Θp as [ | [a b] Θp' IH ]; intros Θs Hwf; simpl in Hwf.
  - exact Hwf.
  - inversion Hwf; subst; apply IH; assumption.
Qed.

Lemma msubst_compose_downarrow_tyequiv : forall Θ Θpre Θt ρ A,
  Θ = Θpre ++ Θt -> uniq Θ -> a_wf_aenv Θ -> a_wf_aenv Θt ->
  msubst_lc ρ ->
  (forall X, X `in` dom ρ -> a_wf_ptyp Θt (msubst_lookup ρ X)) ->
  lc_ptyp A ->
  Θt ⊢ (msubst_ptyp (msubst_compose (aenv_msubst Θ) ρ) A) ≡ᵗ (msubst_ptyp ρ A).
Proof.
  intros Θ Θpre Θt ρ A HeqΘ Huq HwfΘ Hwft Hlcρ Himg Hlc;
    revert Θpre Θt HeqΘ Huq Hwft Himg.
  induction Hlc; intros Θpre Θt HeqΘ Huq Hwft Himg; simpl.
  - apply a_tyequiv__refl. constructor.
  - (* var X *)
    destruct (AtomSetProperties.In_dec Xpt (dom ρ)) as [Hin | Hni].
    + rewrite msubst_lookup_compose by (left; exact Hin).
      apply a_tyequiv__sym.
      eapply msubst_downarrow_tyequiv;
        [ exact HeqΘ | exact Huq | exact Hwft | apply Himg; exact Hin ].
    + rewrite (msubst_lookup_notin ρ Hni).
      assert (Hnic : Xpt `notin` dom (msubst_compose (aenv_msubst Θ) ρ)).
      { rewrite dom_msubst_compose. exact Hni. }
      rewrite (msubst_lookup_notin _ Hnic).
      apply a_tyequiv__refl. constructor.
  - apply a_tyequiv__arrow;
      [ apply (IHHlc1 Θpre Θt HeqΘ Huq Hwft Himg)
      | apply (IHHlc2 Θpre Θt HeqΘ Huq Hwft Himg) ].
  - apply a_tyequiv__all
      with (L := dom ρ `union` dom Θt `union` dom Θpre
                 `union` dom (msubst_compose (aenv_msubst Θ) ρ)).
    intros X HX.
    rewrite <- (@msubst_ptyp_open_lc (msubst_compose (aenv_msubst Θ) ρ) A X);
      [ | intros Y; destruct (AtomSetProperties.In_dec Y (dom ρ)) as [Hyi | Hyn];
          [ rewrite msubst_lookup_compose by (left; exact Hyi);
            apply msubst_ptyp_lc_lc; [ apply aenv_msubst_lc; exact HwfΘ | apply Hlcρ ]
          | assert (Hync : Y `notin` dom (msubst_compose (aenv_msubst Θ) ρ))
              by (rewrite dom_msubst_compose; exact Hyn);
            rewrite (msubst_lookup_notin _ Hync); apply lc_ptyp_var_f ]
        | clear - HX; fsetdec ].
    rewrite <- (@msubst_ptyp_open_lc ρ A X); [ | exact Hlcρ | clear - HX; fsetdec ].
    apply (H0 X Θpre Θt HeqΘ Huq Hwft Himg).
Qed.

(* pskl mirror of msubst_compose_downarrow_tyequiv (var_skl middle adjustment). *)
Lemma msubst_pskl_compose_downarrow_tyequiv : forall Θ Θpre Θt ρ P,
  Θ = Θpre ++ Θt -> uniq Θ -> a_wf_aenv Θ -> a_wf_aenv Θt ->
  msubst_lc ρ ->
  (forall X, X `in` dom ρ -> a_wf_ptyp Θt (msubst_lookup ρ X)) ->
  lc_pskl P ->
  Θt ⊢ (msubst_pskl (msubst_compose (aenv_msubst Θ) ρ) P) ≡ˢ (msubst_pskl ρ P).
Proof.
  intros Θ Θpre Θt ρ P HeqΘ Huq HwfΘ Hwft Hlcρ Himg Hlc;
    revert Θpre Θt HeqΘ Huq Hwft Himg.
  induction Hlc; intros Θpre Θt HeqΘ Huq Hwft Himg; simpl.
  - apply a_pskl_tyequiv__refl. constructor.
  - destruct (AtomSetProperties.In_dec Xps (dom ρ)) as [Hin | Hni].
    + rewrite msubst_lookup_compose by (left; exact Hin).
      apply a_tyequiv_pskl. apply a_tyequiv__sym.
      eapply msubst_downarrow_tyequiv;
        [ exact HeqΘ | exact Huq | exact Hwft | apply Himg; exact Hin ].
    + rewrite (msubst_lookup_notin ρ Hni).
      assert (Hnic : Xps `notin` dom (msubst_compose (aenv_msubst Θ) ρ))
        by (rewrite dom_msubst_compose; exact Hni).
      rewrite (msubst_lookup_notin _ Hnic).
      apply a_pskl_tyequiv__refl. constructor.
  - apply a_pskl_tyequiv__arrow;
      [ apply (IHHlc1 Θpre Θt HeqΘ Huq Hwft Himg)
      | apply (IHHlc2 Θpre Θt HeqΘ Huq Hwft Himg) ].
  - apply a_pskl_tyequiv__all
      with (L := dom ρ `union` dom Θt `union` dom Θpre
                 `union` dom (msubst_compose (aenv_msubst Θ) ρ)).
    intros X HX.
    rewrite <- (@msubst_pskl_open_lc_local (msubst_compose (aenv_msubst Θ) ρ) P1 X);
      [ | intros Y; destruct (AtomSetProperties.In_dec Y (dom ρ)) as [Hyi | Hyn];
          [ rewrite msubst_lookup_compose by (left; exact Hyi);
            apply msubst_ptyp_lc_lc; [ apply aenv_msubst_lc; exact HwfΘ | apply Hlcρ ]
          | assert (Hync : Y `notin` dom (msubst_compose (aenv_msubst Θ) ρ))
              by (rewrite dom_msubst_compose; exact Hyn);
            rewrite (msubst_lookup_notin _ Hync); apply lc_ptyp_var_f ]
        | clear - HX; fsetdec ].
    rewrite <- (@msubst_pskl_open_lc_local ρ P1 X); [ | exact Hlcρ | clear - HX; fsetdec ].
    apply (H0 X Θpre Θt HeqΘ Huq Hwft Himg).
  - apply a_pskl_tyequiv__refl. constructor.
  - apply a_pskl_tyequiv__tophole. apply (IHHlc Θpre Θt HeqΘ Huq Hwft Himg).
Qed.

(* Normalize an a_inc by its own (suffix-of-Θ) target's flex_defs: the metasubst
   images are ⇓ᵗ[Θ]-collapsed while the target Θt is kept.  Makes the metasubst
   equal ⇓ρ = compose(aenv_msubst Θ)ρ, matching the ⇓-normalized join subject
   (consis_downarrow_subject).  The ρb′-vs-⇓ρb′ reconciliation. *)
Lemma a_inc_self_downarrow : forall Θ0 ρ Θt,
  Θ0 ≤[ ρ ] Θt ->
  forall Θpre,
  a_wf_aenv (Θpre ++ Θt) -> uniq (Θpre ++ Θt) -> a_wf_aenv Θ0 ->
  Θ0 ≤[ msubst_compose (aenv_msubst (Θpre ++ Θt)) ρ ] Θt.
Proof.
  intros Θ0 ρ Θt Hinc; induction Hinc; intros Θpre HwfW Huq Hwf0.
  - (* empty *) simpl. apply a_inc__empty; assumption.
  - (* flex α τ : target Θ' unchanged, Θpre unchanged *)
    simpl.
    inversion Hwf0 as [ | α0 Θ0x Hnd0 Hwf0' | | | | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ') by (eapply a_wf_aenv_app_r; exact HwfW).
    assert (Hdd : ⇓ᵗ[ Θpre ++ Θ' ] τ = ⇓ᵗ[ Θ' ] τ)
      by (apply downarrow_app_agree_ptyp; [ exact Huq | apply a_wf_ptyp_ftv_dom; exact H ]).
    apply a_inc__flex.
    + eapply IHHinc; [ exact HwfW | exact Huq | exact Hwf0' ].
    + rewrite Hdd. apply a_wf_ptyp_downarrow_mono; [ exact HwfΘ' | exact H | exact H0 ].
    + rewrite Hdd. apply mono_downarrow; [ exact HwfΘ' | exact H | exact H0 ].
  - (* flex_def α ≔ τ : image τ', premise τ'≡msubst ρ τ *)
    simpl.
    inversion Hwf0 as [ | | α0 τ0 Θ0x Hnd0 Hwpτ0 Hmτ0 Hwf0' | | | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ') by (eapply a_wf_aenv_app_r; exact HwfW).
    assert (Hdd : ⇓ᵗ[ Θpre ++ Θ' ] τ' = ⇓ᵗ[ Θ' ] τ')
      by (apply downarrow_app_agree_ptyp; [ exact Huq | apply a_wf_ptyp_ftv_dom; exact H ]).
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    apply a_inc__flex_def.
    + eapply IHHinc; [ exact HwfW | exact Huq | exact Hwf0' ].
    + rewrite Hdd. apply a_wf_ptyp_downarrow_mono; [ exact HwfΘ' | exact H | exact H0 ].
    + rewrite Hdd. apply mono_downarrow; [ exact HwfΘ' | exact H | exact H0 ].
    + eapply a_tyequiv__trans.
      * apply a_tyequiv__sym.
        eapply msubst_downarrow_tyequiv;
          [ reflexivity | exact Huq | exact HwfΘ' | exact H ].
      * eapply a_tyequiv__trans; [ exact H1 | ].
        apply a_tyequiv__sym.
        eapply msubst_compose_downarrow_tyequiv;
          [ reflexivity | exact Huq | exact HwfW | exact HwfΘ' | exact Hlcρ | | ].
        -- intros X HX. eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf0' | ].
           destruct (a_inc_dom_flex Hinc HX) as [Hb | [t0 Hb]];
             [ right; left | right; right; exists t0 ]; exact Hb.
        -- eapply a_wf_ptyp_lc; exact Hwpτ0.
  - (* var A : ρ unchanged, target Ξ++(x~var A')++Θ' *)
    inversion Hwf0 as [ | | | | x0 A0 Θ0x Hnd0 HwpA Hwf0' | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ').
    { eapply a_wf_aenv_app_r with (Θp := Θpre ++ Ξ ++ (x ~ abind_var_typ A')).
      simpl_env. simpl_env in HwfW. exact HwfW. }
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    apply a_inc__var; [ | | exact H0 ].
    + replace (Θpre ++ Ξ ++ x ~ abind_var_typ A' ++ Θ')
         with ((Θpre ++ Ξ ++ x ~ abind_var_typ A') ++ Θ') by (simpl_env; reflexivity).
      eapply IHHinc with (Θpre := Θpre ++ Ξ ++ (x ~ abind_var_typ A'));
        [ simpl_env; simpl_env in HwfW; exact HwfW
        | simpl_env; simpl_env in Huq; exact Huq | exact Hwf0' ].
    + eapply a_tyequiv__trans; [ exact H | ].
      apply a_tyequiv__sym.
      eapply msubst_compose_downarrow_tyequiv with
        (Θpre := Θpre ++ Ξ ++ (x ~ abind_var_typ A'));
        [ simpl_env; reflexivity | simpl_env; simpl_env in Huq; exact Huq
        | simpl_env; simpl_env in HwfW; exact HwfW | exact HwfΘ' | exact Hlcρ | | ].
      * intros X HX. eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf0' | ].
        destruct (a_inc_dom_flex Hinc HX) as [Hb | [t0 Hb]];
          [ right; left | right; right; exists t0 ]; exact Hb.
      * eapply a_wf_ptyp_lc; exact HwpA.
  - (* var_skl P : ρ unchanged, target Ξ++(x~var_skl P')++Θ' *)
    inversion Hwf0 as [ | | | x0 P0 Θ0x Hnd0 HwpP Hwf0' | | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ').
    { eapply a_wf_aenv_app_r with (Θp := Θpre ++ Ξ ++ (x ~ abind_var_skl P')).
      simpl_env. simpl_env in HwfW. exact HwfW. }
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    apply a_inc__var_skl; [ | | exact H0 ].
    + replace (Θpre ++ Ξ ++ x ~ abind_var_skl P' ++ Θ')
         with ((Θpre ++ Ξ ++ x ~ abind_var_skl P') ++ Θ') by (simpl_env; reflexivity).
      eapply IHHinc with (Θpre := Θpre ++ Ξ ++ (x ~ abind_var_skl P'));
        [ simpl_env; simpl_env in HwfW; exact HwfW
        | simpl_env; simpl_env in Huq; exact Huq | exact Hwf0' ].
    + eapply a_pskl_tyequiv__trans; [ exact H | ].
      apply a_pskl_tyequiv__sym.
      eapply msubst_pskl_compose_downarrow_tyequiv with
        (Θpre := Θpre ++ Ξ ++ (x ~ abind_var_skl P'));
        [ simpl_env; reflexivity | simpl_env; simpl_env in Huq; exact Huq
        | simpl_env; simpl_env in HwfW; exact HwfW | exact HwfΘ' | exact Hlcρ | | ].
      * intros X HX. eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf0' | ].
        destruct (a_inc_dom_flex Hinc HX) as [Hb | [t0 Hb]];
          [ right; left | right; right; exists t0 ]; exact Hb.
      * eapply a_wf_pskl_lc; exact HwpP.
  - (* tvar α : target Ξ++(α~tvar)++Θ' *)
    inversion Hwf0 as [ | | | | | α0 Θ0x Hnd0 Hwf0' ]; subst.
    apply a_inc__tvar; [ | exact H ].
    replace (Θpre ++ Ξ ++ α ~ abind_tvar ++ Θ')
       with ((Θpre ++ Ξ ++ α ~ abind_tvar) ++ Θ') by (simpl_env; reflexivity).
    eapply IHHinc with (Θpre := Θpre ++ Ξ ++ (α ~ abind_tvar));
      [ simpl_env; simpl_env in HwfW; exact HwfW
      | simpl_env; simpl_env in Huq; exact Huq | exact Hwf0' ].
Qed.

(* a_inc_equiv twin of a_inc_self_downarrow: an increment is ≡-equivalent to its
   own downarrow.  Used to adjust the factoring's competing metasubst ⇓ρ→ρ. *)
Lemma a_inc_equiv_self_downarrow : forall Θ0 ρ Θt,
  Θ0 ≤[ ρ ] Θt ->
  forall Θpre,
  a_wf_aenv (Θpre ++ Θt) -> uniq (Θpre ++ Θt) -> a_wf_aenv Θ0 ->
  a_inc_equiv Θ0 ρ (msubst_compose (aenv_msubst (Θpre ++ Θt)) ρ) Θt.
Proof.
  intros Θ0 ρ Θt Hinc; induction Hinc; intros Θpre HwfW Huq Hwf0.
  - simpl. apply a_inc_equiv__empty; assumption.
  - simpl.
    inversion Hwf0 as [ | α0 Θ0x Hnd0 Hwf0' | | | | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ') by (eapply a_wf_aenv_app_r; exact HwfW).
    assert (Hdd : ⇓ᵗ[ Θpre ++ Θ' ] τ = ⇓ᵗ[ Θ' ] τ)
      by (apply downarrow_app_agree_ptyp; [ exact Huq | apply a_wf_ptyp_ftv_dom; exact H ]).
    apply a_inc_equiv__flex.
    + eapply IHHinc; [ exact HwfW | exact Huq | exact Hwf0' ].
    + rewrite Hdd. apply a_tyequiv_to_downarrow_mono; [ exact HwfΘ' | exact H | exact H0 ].
  - simpl.
    inversion Hwf0 as [ | | α0 τ0 Θ0x Hnd0 Hwpτ0 Hmτ0 Hwf0' | | | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ') by (eapply a_wf_aenv_app_r; exact HwfW).
    assert (Hdd : ⇓ᵗ[ Θpre ++ Θ' ] τ' = ⇓ᵗ[ Θ' ] τ')
      by (apply downarrow_app_agree_ptyp; [ exact Huq | apply a_wf_ptyp_ftv_dom; exact H ]).
    apply a_inc_equiv__flex_def.
    + eapply IHHinc; [ exact HwfW | exact Huq | exact Hwf0' ].
    + rewrite Hdd. apply a_tyequiv_to_downarrow_mono; [ exact HwfΘ' | exact H | exact H0 ].
    + exact H1.
  - inversion Hwf0 as [ | | | | x0 A0 Θ0x Hnd0 HwpA Hwf0' | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ').
    { eapply a_wf_aenv_app_r with (Θp := Θpre ++ Ξ ++ (x ~ abind_var_typ A')).
      simpl_env. simpl_env in HwfW. exact HwfW. }
    apply a_inc_equiv__var; [ | exact H | exact H0 ].
    replace (Θpre ++ Ξ ++ x ~ abind_var_typ A' ++ Θ')
       with ((Θpre ++ Ξ ++ x ~ abind_var_typ A') ++ Θ') by (simpl_env; reflexivity).
    eapply IHHinc with (Θpre := Θpre ++ Ξ ++ (x ~ abind_var_typ A'));
      [ simpl_env; simpl_env in HwfW; exact HwfW
      | simpl_env; simpl_env in Huq; exact Huq | exact Hwf0' ].
  - inversion Hwf0 as [ | | | x0 P0 Θ0x Hnd0 HwpP Hwf0' | | ]; subst.
    assert (HwfΘ' : a_wf_aenv Θ').
    { eapply a_wf_aenv_app_r with (Θp := Θpre ++ Ξ ++ (x ~ abind_var_skl P')).
      simpl_env. simpl_env in HwfW. exact HwfW. }
    apply a_inc_equiv__var_skl; [ | exact H | exact H0 ].
    replace (Θpre ++ Ξ ++ x ~ abind_var_skl P' ++ Θ')
       with ((Θpre ++ Ξ ++ x ~ abind_var_skl P') ++ Θ') by (simpl_env; reflexivity).
    eapply IHHinc with (Θpre := Θpre ++ Ξ ++ (x ~ abind_var_skl P'));
      [ simpl_env; simpl_env in HwfW; exact HwfW
      | simpl_env; simpl_env in Huq; exact Huq | exact Hwf0' ].
  - inversion Hwf0 as [ | | | | | α0 Θ0x Hnd0 Hwf0' ]; subst.
    apply a_inc_equiv__tvar; [ | exact H ].
    replace (Θpre ++ Ξ ++ α ~ abind_tvar ++ Θ')
       with ((Θpre ++ Ξ ++ α ~ abind_tvar) ++ Θ') by (simpl_env; reflexivity).
    eapply IHHinc with (Θpre := Θpre ++ Ξ ++ (α ~ abind_tvar));
      [ simpl_env; simpl_env in HwfW; exact HwfW
      | simpl_env; simpl_env in Huq; exact Huq | exact Hwf0' ].
Qed.

(* Strip a term-var middle (x:Q) from an ID increment, dropping it from both
   source and target (id ⟹ no suffix added, so Ξv=nil, A'=Q).  The id-side
   plumbing of the SkipTmVar walk case: recovers the (Ξ++Θ0) id-increment. *)
Lemma a_inc_var_mid_strip_id : forall Ξ x Q Θ0 ρ Θ1,
  a_decls Ξ ->
  is_id_msubst ρ ->
  (Ξ ++ (x ~ abind_var_typ Q) ++ Θ0) ≤[ ρ ] ((x ~ abind_var_typ Q) ++ Θ1) ->
  (Ξ ++ Θ0) ≤[ ρ ] Θ1.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros x Q Θ0 ρ Θ1 Hdec Hid Hinc.
  - simpl in Hinc.
    destruct (a_inc_var_inv Hinc) as [Ξv [A' [Θ2 [Heqt [Heqv [Hsuf Hinc']]]]]].
    destruct Ξv as [ | [z bz] Ξv' ].
    + simpl in Heqt. inversion Heqt; subst. exact Hinc'.
    + exfalso. simpl in Heqt. inversion Heqt; subst.
      inversion Hsuf as [ | z0 b0 Ξ0 Hsuf0 Hsb ]; subst.
      inversion Hsb.
  - inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs ρs Θts aa τ Hinc' Hwfτ Hmτ | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    apply a_inc__flex; [ | | apply mono_ptyp__var ].
    2:{ apply a_wf_ptyp__var.
        inversion Hwfτ as [ | Θw Xw Hbt | | ]; subst.
        eapply a_binds_tvar_strip_mid with
          (c := x) (b := abind_var_typ Q) (Ξ := (@nil (atom * abind)));
          [ simpl; exact Hbt
          | intro Hc; inversion Hc
          | intro Hc; inversion Hc
          | intros ? Hc; inversion Hc ]. }
    eapply IH; [ exact Hdec' | exact Hid' | exact Hinc' ].
Qed.

Lemma aenv_msubst_dom_inv : forall Θ X,
  X `in` dom (aenv_msubst Θ) -> a_flex_tvar Θ X.
Proof.
  induction Θ as [ | [a b] Θ' IH ]; intros X HX; simpl in HX.
  - clear - HX; fsetdec.
  - assert (Hstep : forall Y, a_flex_tvar Θ' Y -> a_flex_tvar ((a, b) :: Θ') Y).
    { intros Y [Hb | [τ Hb]]; [ left | right; exists τ ];
        unfold binds; simpl; right; exact Hb. }
    destruct b; simpl in HX.
    + apply Hstep. apply IH. exact HX.
    + apply Hstep. apply IH. exact HX.
    + apply Hstep. apply IH. exact HX.
    + destruct (X == a) as [-> | Hne].
      * left. unfold binds; simpl; left; reflexivity.
      * apply Hstep. apply IH. clear - HX Hne; fsetdec.
    + destruct (X == a) as [-> | Hne].
      * right. eexists. unfold binds; simpl; left; reflexivity.
      * apply Hstep. apply IH. clear - HX Hne; fsetdec.
Qed.

Lemma msubst_pskl_ftv_lower : forall ρ P X,
  X `in` ftvar_in_pskl P ->
  ftvar_in_ptyp (msubst_lookup ρ X) [<=] ftvar_in_pskl (msubst_pskl ρ P).
Proof.
  induction P as [ | n | Y | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros X HX; simpl in HX |- *.
  - clear - HX; fsetdec.
  - clear - HX; fsetdec.
  - assert (X = Y) by (clear - HX; fsetdec); subst.
    rewrite ftvar_in_ptyp_to_pskl. clear; fsetdec.
  - apply AtomSetImpl.union_1 in HX; destruct HX as [HXa | HXb];
      [ pose proof (IHa X HXa) | pose proof (IHb X HXb) ]; clear - H; fsetdec.
  - pose proof (IHall X HX). clear - H; fsetdec.
  - clear - HX; fsetdec.
  - pose proof (IHt X HX). clear - H; fsetdec.
Qed.

Lemma a_assign_subject_flex_local : forall F Θ0 Ξ α P Θ1,
  Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
  a_flex_tvar Θ0 α.
Proof.
  intros F Θ0 Ξ α P Θ1 H; induction H.
  - left. unfold binds; simpl; left; reflexivity.
  - left. unfold binds; simpl; left; reflexivity.
  - exact H.
  - apply a_flex_tvar_weaken_prefix. exact IHa_assign.
  - apply a_flex_tvar_weaken_prefix. exact IHa_assign.
  - apply a_flex_tvar_weaken_prefix. exact IHa_assign.
  - apply a_flex_tvar_weaken_prefix. exact IHa_assign.
  - apply a_flex_tvar_weaken_prefix. exact IHa_assign.
Qed.

Lemma msubst_lookup_app_in : forall ζ1 ζ2 X,
  X `in` dom ζ1 -> msubst_lookup (ζ1 ++ ζ2) X = msubst_lookup ζ1 X.
Proof.
  induction ζ1 as [ | [a t] ζ1' IH ]; intros ζ2 X HX; simpl in *.
  - clear - HX; fsetdec.
  - destruct (X == a) as [-> | Hne];
      [ reflexivity | apply IH; clear - HX Hne; fsetdec ].
Qed.

(** THE ≡ᵗ STRENGTHENING.  Strip a middle binding [c~b] and an [a_decls]-free
    prefix [Ξ] off both sides of a MONOtype equivalence whose endpoints are wf
    in the tail [Θt]. *)
Lemma a_tyequiv_strengthen_mono_mid : forall Ξ c b Θt A B,
  a_wf_aenv (Ξ ++ (c ~ b) ++ Θt) ->
  a_wf_ptyp Θt A -> mono_ptyp A ->
  a_wf_ptyp Θt B -> mono_ptyp B ->
  (Ξ ++ (c ~ b) ++ Θt) ⊢ A ≡ᵗ B ->
  Θt ⊢ A ≡ᵗ B.
Proof.
  intros Ξ c b Θt A B Hwf HwfA HmA HwfB HmB Heq.
  rewrite <- app_assoc in Hwf, Heq.
  assert (Hwft : a_wf_aenv Θt) by (apply a_wf_aenv_strip_prefix_local in Hwf; exact Hwf).
  assert (Huniq : uniq ((Ξ ++ (c ~ b)) ++ Θt)) by (apply a_wf_aenv_uniq; exact Hwf).
  pose proof (a_tyequiv_downarrow Hwf Heq) as Hd.
  assert (HdA : ⇓ᵗ[ (Ξ ++ (c ~ b)) ++ Θt ] A = ⇓ᵗ[ Θt ] A)
    by (apply downarrow_app_agree_ptyp;
        [ exact Huniq | apply a_wf_ptyp_ftv_dom; exact HwfA ]).
  assert (HdB : ⇓ᵗ[ (Ξ ++ (c ~ b)) ++ Θt ] B = ⇓ᵗ[ Θt ] B)
    by (apply downarrow_app_agree_ptyp;
        [ exact Huniq | apply a_wf_ptyp_ftv_dom; exact HwfB ]).
  rewrite HdA, HdB in Hd.
  eapply a_tyequiv__trans;
    [ apply (a_tyequiv_to_downarrow_mono Hwft HwfA HmA) | ].
  rewrite Hd. apply a_tyequiv__sym.
  apply (a_tyequiv_to_downarrow_mono Hwft HwfB HmB).
Qed.

(** The BRIDGE, generalised over the refinement's ghost context [Δ].  The
    packaged [consis_refine_mono_tyequiv] (prop_mono_bridge.v) fixes [Δ] to
    [empty]; the consistency optimality nodes present the competing
    Δ₁-refinement over a NON-empty [Δ], but [refine_mono_join] (the only place
    [Δ] is touched) is already [Δ]-agnostic, so the generalisation is free. *)
Lemma consis_refine_mono_tyequiv_gen : forall Θ Δ A B Qt,
  a_wf_aenv Θ ->
  mono_ptyp A -> mono_ptyp B ->
  empty ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl_syn A) ≈ Qt ->
  Θ ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_inh (ptyp_to_pskl B)) ⊳ Qt ->
  Θ ⊢ A ≡ᵗ B.
Proof.
  intros Θ Δ A B Qt Hwf HmA HmB Hc Hr.
  rewrite (ptyp_to_bskl_inh_syn_eq HmB) in Hr.
  destruct (consis_mono_join Hc Hwf (A := A) eq_refl HmA) as [C [HmC [HeqC HeA]]].
  destruct (refine_mono_join Hr Hwf (B := B) eq_refl HmB) as [C' [HmC' [HeqC' HeB]]].
  assert (HCC : C = C')
    by (apply ptyp_to_bskl_syn_inj; auto; rewrite <- HeqC, <- HeqC'; reflexivity).
  subst C'.
  eapply a_tyequiv__trans; [ exact HeA | apply a_tyequiv__sym; exact HeB ].
Qed.

(** Monotype precision recovery, for the AXIOM nodes (Unit/Rigid) whose
    algorithmic output is a CONCRETE monotype painting rather than a flexible
    [α̂].  Same [consis_mono_join] core as [consis_precise_core], but the subject
    is the raw painting [ptyp_to_pskl A] instead of [msubst_bskl ζ α̂]. *)
Lemma consis_precise_mono_join : forall Θ Δ A Qb,
  a_wf_aenv Θ ->
  mono_ptyp A ->
  (forall X, X `in` ftvar_in_ptyp A -> a_binds_tvar X Θ) ->
  empty ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl_syn A) ≈ Qb ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (ptyp_to_pskl A) ⊑ (bskl_to_pskl Qb).
Proof.
  intros Θ Δ A Qb Hwf HmA Hvis Hjoin.
  destruct (consis_mono_join Hjoin Hwf (A := A) eq_refl HmA) as [C [HmC [HQb Heq]]].
  unfold ad_precise.
  rewrite (ptyp_to_bskl_inh_syn_eq HmA).
  subst Qb.
  replace (bskl_to_pskl (ptyp_to_bskl_syn C)) with (ptyp_to_pskl C).
  2:{ unfold ptyp_to_bskl_syn. rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity. }
  rewrite (ptyp_to_bskl_inh_syn_eq HmC).
  apply tyequiv_mono_refine_syn; auto.
Qed.

(** Colour erasure commutes with metasubstitution. *)
Lemma bskl_to_pskl_msubst_bskl : forall ρ Q,
  bskl_to_pskl (msubst_bskl ρ Q) = msubst_pskl ρ (bskl_to_pskl Q).
Proof.
  intros ρ Q; induction Q; simpl; try reflexivity.
  - rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity.
  - rewrite IHQ1, IHQ2. reflexivity.
  - rewrite IHQ. reflexivity.
  - rewrite IHQ. reflexivity.
  - rewrite IHQ. reflexivity.
Qed.

(** A join whose SUBJECT is the ghost hole forces the target painting to be
    fully INHERITED: it is invariant under erase-then-reinherit.  (The only
    two rules that can conclude [uskl_hole ≈ Qb] are [__hole], whose target is
    an [inh] painting, and [__flex_r], whose target is a defined-flex variable
    — both fixed points of [inh ∘ erase].) *)
Lemma consis_hole_target_inh : forall Ψ Θ Qb,
  Ψ ⨟ Θ ⊨ₛᵃ uskl_hole ≈ Qb ->
  pskl_to_bskl_inh (bskl_to_pskl Qb) = Qb.
Proof.
  intros Ψ Θ Qb H.
  remember uskl_hole as S eqn:HS.
  induction H; try discriminate HS.
  - rewrite bskl_to_pskl_pskl_to_bskl_inh. reflexivity.
  - reflexivity.
Qed.

(** Metasubstitution preserves guarded skeleton shape.  The only interesting
    leaf is a flexible variable: every image of an information increase is a
    monotype, hence guarded. *)
Lemma guarded_pskl_msubst_inc : forall Θ0 ρ Θ P,
  Θ0 ≤[ ρ ] Θ ->
  guarded_pskl P ->
  guarded_pskl (msubst_pskl ρ P).
Proof.
  intros Θ0 ρ Θ P Hinc Hg. inversion Hg; subst; simpl.
  - apply guarded_pskl__unit.
  - apply mono_ptyp_to_pskl_guarded. eapply a_inc_lookup_mono; eauto.
  - apply guarded_pskl__arrow;
      eapply msubst_pskl_lc; eauto.
Qed.

(** A guarded consistency subject has a guarded target.  Stated with an
    explicit local-closure premise on the target so the Arrow case needs no
    separate regularity development.  A left-side defined-flex lookup recurs
    on its definition; a right-side lookup lands at a guarded variable. *)
Lemma ad_pat_consis_guarded_r : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  a_wf_aenv Θ ->
  forall P,
    S = pskl_to_uskl P ->
    guarded_pskl P ->
    lc_bskl Q ->
    guarded_bskl Q.
Proof.
  intros Ψ Θ S Q Hc Hwf; induction Hc; intros P0 HeqS Hg Hlc;
    try solve [ destruct P0; simpl in HeqS; try discriminate;
                inversion Hg ].
  - destruct P0; simpl in HeqS; try discriminate.
    apply guarded_bskl__unit.
  - destruct P0; simpl in HeqS; try discriminate.
    apply guarded_bskl__var.
  - destruct P0; simpl in HeqS; try discriminate.
    inversion Hlc; subst. apply guarded_bskl__arrow; assumption.
  - (* flex_l *)
    destruct P0; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    apply IHHc with (P := ptyp_to_pskl τ); auto.
    + symmetry. apply ptyp_to_uskl_syn_eq.
    + apply mono_ptyp_to_pskl_guarded.
      eapply a_wf_aenv_binds_def_mono; eauto.
  - (* flex_r *) apply guarded_bskl__var.
Qed.

(** If a tophole subject is refined to a guarded target, the tophole must have
    been removed.  Target-side flexible aliases are peeled recursively and
    folded back after the removal. *)
Lemma ad_refine_syn_f_tophole_guarded_inv : forall F Θ Δ Q R,
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ (bskl_tophole Q) R ->
  guarded_bskl R ->
  ad_refine_syn_f F Θ Δ Q R.
Proof.
  intros F Θ Δ Q R Hwf Hr.
  remember (bskl_tophole Q) as Qt eqn:HeqQt.
  induction Hr; intros Hg; try discriminate HeqQt.
  - inversion HeqQt; subst. exact Hr.
  - inversion Hg.
  - inversion Hg.
  - inversion HeqQt; subst.
    eapply ad_refine_syn_f__flex_r; [ exact H | ].
    apply IHHr; [ exact Hwf | reflexivity | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_refine_pskl_f_tophole_guarded_inv : forall F Θ Δ P Q,
  a_wf_aenv Θ ->
  ad_refine_pskl_f F Θ Δ (pskl_tophole P) Q ->
  guarded_pskl Q ->
  ad_refine_pskl_f F Θ Δ P Q.
Proof.
  intros F Θ Δ P Q Hwf Hr.
  remember (pskl_tophole P) as Pt eqn:HeqPt.
  induction Hr; intros Hg; try discriminate HeqPt.
  - inversion HeqPt; subst. exact Hr.
  - inversion Hg.
  - inversion Hg.
  - inversion HeqPt; subst.
    eapply ad_refine_pskl_f__flex_r; [ exact H | ].
    apply IHHr; [ exact Hwf | reflexivity | ].
    apply mono_ptyp_to_pskl_guarded.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** A consistency derivation from a tophole to a guarded target must use the
    tophole-dropping path.  As above, a target-side defined-flex alias is
    unfolded recursively and folded back afterwards. *)
Lemma ad_pat_consis_tophole_guarded_inv : forall Ψ Θ P Q,
  a_wf_aenv Θ ->
  Ψ ⨟ Θ ⊨ₛᵃ (uskl_tophole (pskl_to_uskl P)) ≈ Q ->
  guarded_pskl P ->
  guarded_bskl Q ->
  Ψ ⨟ Θ ⊨ₛᵃ (pskl_to_uskl P) ≈ Q.
Proof.
  intros Ψ Θ P Q Hwf Hc.
  remember (uskl_tophole (pskl_to_uskl P)) as S eqn:HeqS.
  induction Hc; intros HgP HgQ; try discriminate HeqS.
  - inversion HgQ.
  - inversion HgQ.
  - inversion HeqS; subst. exact Hc.
  - inversion HeqS; subst.
    eapply ad_pat_consis__flex_r; [ exact H | ].
    apply IHHc; [ exact Hwf | reflexivity | exact HgP | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_refine_syn_f_tophole_keep_inv : forall F Θ Δ P Q,
  a_wf_aenv Θ ->
  guarded_bskl P ->
  ad_refine_syn_f F Θ Δ (bskl_tophole P) (bskl_tophole Q) ->
  ad_refine_syn_f F Θ Δ P Q.
Proof.
  intros F Θ Δ P Q Hwf Hg Hr.
  inversion Hr; subst; try discriminate.
  - match goal with
    | Hsub : ad_refine_syn_f _ _ _ P (bskl_tophole Q) |- _ =>
        pose proof (ad_refine_syn_f_guarded_r Hwf Hsub Hg) as Hbad;
        inversion Hbad
    end.
  - assumption.
Qed.

Lemma ad_refine_pskl_f_tophole_keep_inv : forall F Θ Δ P Q,
  a_wf_aenv Θ ->
  guarded_pskl P ->
  ad_refine_pskl_f F Θ Δ (pskl_tophole P) (pskl_tophole Q) ->
  ad_refine_pskl_f F Θ Δ P Q.
Proof.
  intros F Θ Δ P Q Hwf Hg Hr.
  inversion Hr; subst; try discriminate.
  - match goal with
    | Hsub : ad_refine_pskl_f _ _ _ P (pskl_tophole Q) |- _ =>
        pose proof (ad_refine_pskl_f_guarded_r Hwf Hsub Hg) as Hbad;
        inversion Hbad
    end.
  - assumption.
Qed.

(** Joint inversion of the three competing-solution judgments at a universal
    ghost.  Looking only at the join leaves [tophole_inh], whose premise keeps
    the wrapper.  The inherited refinement rules that case out: a guarded
    body cannot refine to an inherited quantifier.  The surviving cases are
    exactly keeping the tophole on all three judgments or dropping it on all
    three judgments. *)
Lemma consis_tophole_solution_inv : forall F1 F2 Δ1 Δ2 Θ P0 P Qb,
  a_wf_aenv Θ ->
  guarded_pskl P0 -> guarded_pskl P ->
  empty ⨟ Θ ⊨ₛᵃ (uskl_tophole (pskl_to_uskl P)) ≈ Qb ->
  ad_refine_syn_f F1 Θ Δ1 (bskl_tophole (pskl_to_bskl_inh P0)) Qb ->
  ad_refine_pskl_f F2 Θ Δ2 (pskl_tophole P) (bskl_to_pskl Qb) ->
  (exists Q,
      Qb = bskl_tophole Q /\
      empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl P) ≈ Q /\
      ad_refine_syn_f F1 Θ Δ1 (pskl_to_bskl_inh P0) Q /\
      ad_refine_pskl_f F2 Θ Δ2 P (bskl_to_pskl Q))
  \/
  (empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl P) ≈ Qb /\
   ad_refine_syn_f F1 Θ Δ1 (pskl_to_bskl_inh P0) Qb /\
   ad_refine_pskl_f F2 Θ Δ2 P (bskl_to_pskl Qb)).
Proof.
  intros F1 F2 Δ1 Δ2 Θ P0 P Qb Hwf Hg0 Hg Hc Hrs Hrp.
  remember (uskl_tophole (pskl_to_uskl P)) as S eqn:HeqS.
  induction Hc; try discriminate HeqS.
  - (* tophole kept *)
    inversion HeqS; subst. left. exists Q. repeat split; auto.
    + eapply ad_refine_syn_f_tophole_keep_inv; eauto using guarded_pskl_to_bskl_inh.
    + simpl in Hrp. eapply ad_refine_pskl_f_tophole_keep_inv; eauto.
  - (* tophole_inh: incompatible with the inherited refinement from a
       guarded body *)
    inversion Hrs; subst; try discriminate.
    pose proof (ad_refine_syn_f_guarded_r Hwf H4
                  (guarded_pskl_to_bskl_inh Hg0)) as Hbad.
    inversion Hbad.
  - (* tophole dropped *)
    inversion HeqS; subst. right.
    assert (HlcQ : lc_bskl Q) by (eapply ad_refine_syn_f_lc_r; eauto).
    assert (HgQ : guarded_bskl Q)
      by (eapply ad_pat_consis_guarded_r; eauto; reflexivity).
    repeat split; auto.
    + eapply ad_refine_syn_f_tophole_guarded_inv; eauto.
    + eapply ad_refine_pskl_f_tophole_guarded_inv; eauto.
      apply guarded_bskl_to_pskl; exact HgQ.
  - (* target-side defined flexible: its variable target is guarded, so all
       three derivations take their dropping paths *)
    inversion HeqS; subst. right.
    assert (HgQ : guarded_bskl (bskl_var_f α)) by constructor.
    repeat split.
    + eapply ad_pat_consis_tophole_guarded_inv;
        [ exact Hwf | | exact Hg | exact HgQ ].
      eapply ad_pat_consis__flex_r; [ exact H | exact Hc ].
    + eapply ad_refine_syn_f_tophole_guarded_inv;
        [ exact Hwf | exact Hrs | exact HgQ ].
    + eapply ad_refine_pskl_f_tophole_guarded_inv;
        [ exact Hwf | exact Hrp | constructor ].
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
(*  what remains).  Print Assumptions lists the admit axiom until they are   *)
(*  closed.  The GLUE and all factoring helpers above are fully Qed'd and    *)
(*  axiom-free.                                                              *)
(*                                                                           *)
(*  *** RESOLVED FALSITY (2026-07-15) ***                                    *)
(*  The a_assign conjunct WAS false under the ORIGINAL syntactic-middle      *)
(*  information increase (machine-checked:                                   *)
(*  algo/cex/cex_assign_optimal_syn_middle.v, kept against a local copy of   *)
(*  the old rules).  The mechanization has since ADOPTED GMM-style SEMANTIC  *)
(*  ENTRIES in [a_inc]/[a_inc_equiv]'s var/var_skl rules (def_meta.v):       *)
(*  binder middles are preserved up to ≡ᵗ/≡ˢ, exactly GundryMM10 §3.1.       *)
(*  Under the adopted rules the formerly-false walk cases are TRUE again     *)
(*  (the cex file's [cex_zeta_semantic] factors the very instance), and the  *)
(*  "syntactic middle obstacle" of Assign-SkipTmVar / Flex-Flex-Skip'        *)
(*  DISSOLVES: ζ := ζ' works, the inverted middle's ≡-premise transports.    *)
(*  The PAPER still states the syntactic rules — flagged in                  *)
(*  docs/PAPER-GAPS.md + sections/appendices/optimality-cex.tex.             *)
(* ===================================================================== *)

(* --- Assembly infrastructure for the SkipTmVar/SkipRigid walk cases --- *)
(* A monotype whose free type variables are all tvar-ish in Θ is well-formed
   there — used to place a ⇓-normalized image in a sub-target. *)
Lemma mono_ftv_wf : forall Θ τ,
  mono_ptyp τ ->
  (forall X, X `in` ftvar_in_ptyp τ -> a_binds_tvar X Θ) ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ τ Hm; induction Hm; intros Hftv; simpl in *.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply Hftv. fsetdec.
  - apply a_wf_ptyp__arrow;
      [ apply IHHm1 | apply IHHm2 ]; intros X HX; apply Hftv; fsetdec.
Qed.

(* Normalize the decls-prefix images of a competing a_inc into a sub-target Θ'
   (below the walked binder): the Θ0-part increment is already into Θ' and the
   Ξ-prefix flex images ⇓-collapse into Θ' once they are join-grounded. *)
Lemma a_inc_downarrow_prefix : forall Ξ ρa T Θ0 ρb σb Θ Θ',
  a_decls Ξ ->
  (Ξ ++ T) ≤[ ρa ++ ρb ] Θ ->
  uniq (Ξ ++ T) ->
  dom ρa [=] dom Ξ ->
  Θ0 ≤[ σb ] Θ' ->
  a_wf_aenv Θ -> uniq Θ ->
  (forall x c, binds x c Θ' -> binds x c Θ) ->
  (forall X, X `in` dom ρa ->
     ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup ρa X)) [<=] dom Θ') ->
  (Ξ ++ Θ0) ≤[ (msubst_compose (aenv_msubst Θ) ρa) ++ σb ] Θ'.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ];
    intros ρa T Θ0 ρb σb Θ Θ' Hdec Hinc Huq Hdom Hincb Hwf Huqt Hsub Hgr.
  - rewrite dom_nil in Hdom.
    destruct ρa as [ | [c t] ρa' ];
      [ simpl; exact Hincb
      | exfalso; simpl in Hdom;
        assert (c `in` dom ((c,t)::ρa')) by (simpl; fsetdec);
        rewrite Hdom in H; clear - H; fsetdec ].
  - inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    destruct ρa as [ | [c t] ρa' ];
      [ exfalso; simpl in Hdom;
        assert (a `in` dom ((a~abind_flex_mono)++Ξ')) by (simpl; fsetdec);
        rewrite <- Hdom in H; clear - H; fsetdec | ].
    simpl in Hinc.
    inversion Hinc as [ | S ρs Tt aa τ0 Hinc' Hwfτ Hmτ | | | | ]; subst.
    simpl.
    assert (Huq' : uniq (Ξ' ++ T)) by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (HanΞΘ : c `notin` dom (Ξ' ++ T))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Hanρa : c `notin` dom ρa').
    { pose proof (a_inc_dom_sub Hinc') as Hs.
      clear - Hs HanΞΘ. repeat rewrite dom_app in *. fsetdec. }
    assert (Hlkc : msubst_lookup ((c, t) :: ρa') c = t)
      by (simpl; destruct (c == c); [ reflexivity | contradiction ]).
    assert (Hgrc : ftvar_in_ptyp (⇓ᵗ[ Θ ] t) [<=] dom Θ').
    { pose proof (Hgr c ltac:(simpl; clear; fsetdec)) as Hg.
      rewrite Hlkc in Hg. exact Hg. }
    assert (Hwfd : a_wf_ptyp Θ' (⇓ᵗ[ Θ ] t)).
    { apply mono_ftv_wf; [ apply mono_downarrow; auto | ].
      intros X HX.
      assert (HXd : X `in` dom Θ') by (clear - Hgrc HX; fsetdec).
      eapply a_binds_tvar_strengthen;
        [ | exact Huqt | exact Hsub | exact HXd ].
      eapply a_wf_ptyp_ftv_tvarish;
        [ apply a_wf_ptyp_downarrow_mono; eauto | exact HX ]. }
    apply a_inc__flex; [ | exact Hwfd | apply mono_downarrow; auto ].
    eapply IH; [ exact Hdec' | exact Hinc' | exact Huq' | | exact Hincb
               | exact Hwf | exact Huqt | exact Hsub | ].
    + clear - Hdom Hanρa HanΞΘ. simpl in Hdom.
      repeat rewrite dom_app in *. fsetdec.
    + intros X HX. destruct (X == c) as [-> | Hne].
      * exfalso. clear - HX Hanρa. fsetdec.
      * assert (HXin : X `in` dom ((c, t) :: ρa'))
          by (simpl; clear - HX; fsetdec).
        pose proof (Hgr X HXin) as Hg.
        rewrite (msubst_lookup_cons_neq t ρa' Hne) in Hg.
        exact Hg.
Qed.

Lemma a_inc_equiv_mid_insert_var :
  forall Ξ x Θ0 Θ' Ξv ρ1 ρ2 σ1 σ2 A A',
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom ρ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  Θ' ⊢ A' ≡ᵗ (msubst_ptyp ρ2 A) ->
  a_suffix Ξv ->
  a_inc_equiv (Ξ ++ Θ0) (ρ1 ++ ρ2) (σ1 ++ σ2) Θ' ->
  a_inc_equiv (Ξ ++ (x ~ abind_var_typ A) ++ Θ0)
              (ρ1 ++ ρ2) (σ1 ++ σ2)
              (Ξv ++ (x ~ abind_var_typ A') ++ Θ').
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros x Θ0 Θ' Ξv ρ1 ρ2 σ1 σ2 A A' Hdec Huq Hdρ Hdσ Heqm Hsuf Hie.
  - rewrite dom_nil in Hdρ, Hdσ.
    apply metasubst_dom_empty in Hdρ; apply metasubst_dom_empty in Hdσ; subst.
    simpl in Hie |- *.
    apply a_inc_equiv__var; [ exact Hie | exact Heqm | exact Hsuf ].
  - inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Huρ : uniq (ρ1 ++ ρ2))
      by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
    assert (Huσ : uniq (σ1 ++ σ2))
      by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
    assert (HaΞ : a `notin` dom Ξ') by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ Θ0)) by (clear - Huq; simpl_env in Huq; solve_uniq).
    destruct ρ1 as [ | [ar tr] ρ1' ];
      [ exfalso; rewrite dom_nil in Hdρ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ')) by (simpl; fsetdec);
        rewrite <- Hdρ in Hin; clear - Hin; fsetdec | ].
    destruct σ1 as [ | [asg ts] σ1' ];
      [ exfalso; rewrite dom_nil in Hdσ;
        assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ')) by (simpl; fsetdec);
        rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
    assert (Harρ : ar `notin` dom ρ1') by (clear - Huρ; simpl_env in Huρ; solve_uniq).
    assert (Hasσ : asg `notin` dom σ1') by (clear - Huσ; simpl_env in Huσ; solve_uniq).
    simpl in Hie.
    inversion Hie as [ | S q1 q2 T aa u1 u2 Hie' Hequ | | | | ]; subst.
    simpl_env in Hdρ; simpl_env in Hdσ.
    simpl. apply a_inc_equiv__flex.
    2:{ apply a_tyequiv_weaken with (Θ := Θ');
        [ intros y b Hb; simpl_env; auto | exact Hequ ]. }
    apply IH; auto.
    + clear - Hdρ Harρ HaΞ. simpl_env in *. fsetdec.
    + clear - Hdσ Hasσ HaΞ. simpl_env in *. fsetdec.
Qed.


(* The join is invariant under ⇓-normalizing the SUBJECT, when the RHS is a
   monotype (mono C prunes every ∀/tophole_inh case, exactly as in
   join_pskl_downarrow_mono_scoped).  This transfers the assign-node join
   (subject msubst ρ P, RHS syn(mono ρα)) onto the ⇓-normalized subject, which
   O2 shows is scoped to the sub-target Θ'. *)
Lemma consis_downarrow_subject : forall Ψ Θ S Q,
  ad_pat_consis Ψ Θ S Q ->
  a_wf_aenv Θ ->
  forall S0 C,
    S = pskl_to_uskl S0 ->
    Q = ptyp_to_bskl_syn C -> mono_ptyp C ->
    ad_pat_consis Ψ Θ (pskl_to_uskl (⇓ˢ[ Θ ] S0)) Q.
Proof.
  intros Ψ Θ S Q Hc Hwf; induction Hc;
    intros S0 C0 HeqS HeqC HmC0;
    unfold ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct S0; simpl in HeqS; try discriminate.
    simpl. apply ad_pat_consis__unit; assumption.
  - (* var X : uniform ⇓(var X) ≡ var X route (covers tvar/flex_mono/flex_def) *)
    destruct S0 as [ | | Xp | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | Xc | | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    simpl.
    replace (ptyp_to_pskl (msubst_lookup (aenv_msubst Θ) Xc))
       with (ptyp_to_pskl (⇓ᵗ[ Θ ] (ptyp_var_f Xc))) by reflexivity.
    assert (Hwfx : a_wf_ptyp Θ (ptyp_var_f Xc)) by (apply a_wf_ptyp__var; exact H0).
    assert (Hmono_x : mono_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f Xc)))
      by (apply mono_downarrow; [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]).
    assert (Hwf_x : a_wf_ptyp Θ (⇓ᵗ[ Θ ] (ptyp_var_f Xc)))
      by (apply a_wf_ptyp_downarrow_mono; [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]).
    assert (Hvis : forall Y, Y `in` ftvar_in_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f Xc)) ->
                   a_binds_tvar Y Θ)
      by (intros Y HY; eapply a_wf_ptyp_ftv_tvarish; [ exact Hwf_x | exact HY ]).
    assert (Heqd : Θ ⊢ (⇓ᵗ[ Θ ] (ptyp_var_f Xc)) ≡ᵗ (ptyp_var_f Xc)).
    { apply a_tyequiv__sym.
      apply a_tyequiv_to_downarrow_mono;
        [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]. }
    destruct (tyequiv_mono_consis_transport_q Heqd Hwf Hmono_x Hvis) as [_ Hfwd].
    rewrite ptyp_to_uskl_syn_eq.
    change (bskl_var_f Xc) with (ptyp_to_bskl_syn (ptyp_var_f Xc)).
    apply Hfwd.
    eapply ad_pat_consis_psi_cong;
      [ apply consis_mono_refl; [ exact Hmono_x | exact Hvis ]
      | fsetdec ].
  - (* arrow *)
    destruct S0 as [ | | | S01 S02 | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    inversion HmC0 as [ | | ? ? HmC1 HmC2 ]; subst.
    simpl.
    apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ apply (IHHc1 Hwf S01 C1 eq_refl eq_refl HmC1)
      | apply (IHHc2 Hwf S02 C2 eq_refl eq_refl HmC2)
      | exact H ].
  - (* forall_inh_tagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_inh_untagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_syn_tagged *) destruct HmC0; simpl in HeqC; discriminate.
  - (* forall_syn *) destruct HmC0; simpl in HeqC; discriminate.
  - (* ghostg *) destruct HmC0; simpl in HeqC; discriminate.
  - (* topholeg *) destruct HmC0; simpl in HeqC; discriminate.
  - (* hole *)
    destruct S0; simpl in HeqS; try discriminate.
    simpl. apply ad_pat_consis__hole; [ exact H | exact H0 ].
  - (* tophole *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_inh *) destruct HmC0; simpl in HeqC; discriminate.
  - (* tophole_drop *)
    destruct S0 as [ | | | | | | S0t ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl. apply ad_pat_consis__tophole_drop.
    apply (IHHc Hwf S0t C0 eq_refl eq_refl HmC0).
  - (* flex_l : subject is a defined flexible *)
    destruct S0 as [ | | Xv | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) Xv = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk.
    rewrite <- msubst_pskl_ptyp_to_pskl.
    apply (IHHc Hwf (ptyp_to_pskl τ) C0
             (eq_sym (ptyp_to_uskl_syn_eq τ)) eq_refl HmC0).
  - (* flex_r : join is a defined flexible *)
    destruct C0; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_pat_consis__flex_r with (τ := τ); [ exact H | ].
    apply (IHHc Hwf S0 τ eq_refl eq_refl Hmτ).
Qed.

Lemma skip_tm_var_case : forall F Θ0 Θ1 Ξ α x Q P,
  a_assign (add x F) Θ0 Ξ α P Θ1 ->
  assign_optimal_post (add x F) Θ0 Ξ α P Θ1 ->
  assign_optimal_post F ((x ~ abind_var_typ Q) ++ Θ0) Ξ α P ((x ~ abind_var_typ Q) ++ Θ1).
Proof.
  intros F Θ0 Θ1 Ξ α x Q P Ha IHa.
  unfold assign_optimal_post in *.
  intros Hdecl Hwf HwfP Hdomξ ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Hjoin.
  assert (Huqf : uniq (Ξ ++ (x ~ abind_var_typ Q) ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Hwf' : a_wf_aenv (Ξ ++ Θ0)) by (eapply a_wf_aenv_strip_mid; eauto).
  assert (Huq' : uniq (Ξ ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf').
  assert (Hwf0 : a_wf_aenv Θ0) by (eapply a_wf_aenv_app_r; exact Hwf').
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
  assert (Hxfr : x `notin` ftvar_in_pskl P).
  { intro Hx. destruct (ad_wf_pskl_ftv_tvarish HwfP Hx) as [Hemp | Hbt].
    - clear - Hemp. fsetdec.
    - assert (Hbx : binds x (abind_var_typ Q)
                (Ξ ++ (x ~ abind_var_typ Q) ++ Θ0))
        by (apply binds_app_3; left; reflexivity).
      destruct Hbt as [Hb | [Hb | [τ Hb]]];
        (pose proof (binds_unique _ _ _ _ _ Hb Hbx (a_wf_aenv_uniq Hwf)) as Heq;
         discriminate Heq). }
  assert (HwfP' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P)
    by (eapply ad_wf_pskl_strip_mid; [ exact HwfP | exact Hxfr ]).
  (* competing: strip Ξ, invert x-var *)
  destruct (@a_inc_strip_decls_prefix Ξ ((x ~ abind_var_typ Q) ++ Θ0) ρ Θ Hdecl Hinc) as [ρa [ρb' [Heqρ [Hdρa Hincxb]]]].
  destruct (a_inc_var_inv Hincxb) as [Ξv [A' [Θ' [HeqΘ [HeqA' [HsufΞv Hincb]]]]]].
  assert (HwfΘ' : a_wf_aenv Θ').
  { rewrite HeqΘ in Hwfth.
    eapply a_wf_aenv_app_r with (Θp := Ξv ++ (x ~ abind_var_typ A')).
    simpl_env. simpl_env in Hwfth. exact Hwfth. }
  assert (HeqW : (Ξv ++ (x ~ abind_var_typ A')) ++ Θ' = Θ)
    by (rewrite HeqΘ; simpl_env; reflexivity).
  (* normalize the Θ0-part base by ⇓[Θ] *)
  assert (Hincb_n : Θ0 ≤[ msubst_compose (aenv_msubst Θ) ρb' ] Θ').
  { pose proof (a_inc_self_downarrow Hincb (Ξv ++ (x ~ abind_var_typ A'))) as Hs.
    rewrite HeqW in Hs. apply Hs; [ exact Hwfth | exact HuqΘ | exact Hwf0 ]. }
  (* competing over Θ' at ⇓ρ *)
  assert (Hside : forall Y, Y `in` ftvar_in_pskl P ->
            Y `in` dom ρ \/ Y `notin` dom (aenv_msubst Θ)).
  { intros Y HY.
    destruct (AtomSetProperties.In_dec Y (dom ρ)) as [Hin | Hni]; [ left; exact Hin | right ].
    intro Hin2. apply aenv_msubst_dom_inv in Hin2.
    destruct (ad_wf_pskl_ftv_tvarish HwfP HY) as [Hemp | Hbt]; [ clear - Hemp; fsetdec | ].
    destruct Hbt as [Htv | [Hfm | [τ0 Hfd]]].
    - assert (HtvΘ : binds Y abind_tvar Θ)
        by (eapply a_inc_binds_tvar; [ exact Hinc | exact Htv ]).
      destruct Hin2 as [Hb | [τ1 Hb]];
        (pose proof (binds_unique _ _ _ _ _ HtvΘ Hb (a_wf_aenv_uniq Hwfth)) as Heqb;
         discriminate Heqb).
    - assert (Hyd : Y `in` dom ρ)
        by (eapply a_inc_flex_dom; [ exact Hinc | exact Hwf | left; exact Hfm ]).
      contradiction.
    - assert (Hyd : Y `in` dom ρ)
        by (eapply a_inc_flex_dom; [ exact Hinc | exact Hwf | right; exists τ0; exact Hfd ]).
      contradiction. }
  assert (HO2 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)) [<=] dom Θ').
  { assert (Hmona : mono_ptyp (msubst_lookup ρ α)) by (eapply a_inc_lookup_mono; exact Hinc).
    eapply join_pskl_downarrow_mono_scoped;
      [ exact Hjoin | exact Hwfth | reflexivity | reflexivity | exact Hmona | | ].
    - intros β τ Hbβ Hβd.
      assert (Hβpre : β `notin` dom (Ξv ++ (x ~ abind_var_typ A'))).
      { pose proof HuqΘ as Hu2. rewrite HeqΘ in Hu2. rewrite <- app_assoc in Hu2.
        apply uniq_app_iff in Hu2. destruct Hu2 as [_ [_ Hdisj]].
        clear - Hdisj Hβd. unfold disjoint in Hdisj. fsetdec. }
      assert (Hbβ' : binds β (abind_flex_mono_def τ) Θ').
      { rewrite HeqΘ in Hbβ. rewrite <- app_assoc in Hbβ.
        apply binds_app_iff in Hbβ. destruct Hbβ as [Hb | Hb]; [ | exact Hb ].
        exfalso. apply binds_In in Hb. clear - Hb Hβpre. fsetdec. }
      apply a_wf_ptyp_ftv_dom.
      eapply a_wf_aenv_binds_def_wf_local; [ exact HwfΘ' | exact Hbβ' ].
    - assert (Hflexα : a_flex_tvar Θ0 α)
        by (eapply a_assign_subject_flex_local; exact Ha).
      assert (HαΘ0 : α `in` dom Θ0)
        by (destruct Hflexα as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
      assert (Hαρa : α `notin` dom ρa).
      { rewrite Hdρa. clear - Huqf HαΘ0. simpl_env in Huqf. solve_uniq. }
      assert (Hwfα : a_wf_ptyp Θ' (msubst_lookup ρ α)).
      { rewrite Heqρ. rewrite (msubst_lookup_app_notin ρa ρb' Hαρa).
        eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ].
        destruct Hflexα as [Hb | [τ0 Hb]];
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]. }
      apply a_wf_ptyp_ftv_dom. exact Hwfα. }
  assert (Hgr : forall X, X `in` dom ρa ->
             ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup ρa X)) [<=] dom Θ').
  { intros X HX.
    assert (HXP : X `in` ftvar_in_pskl P) by (apply Hdomξ; rewrite <- Hdρa; exact HX).
    assert (HXρ : X `in` dom ρ)
      by (rewrite Heqρ; rewrite dom_app; clear - HX; fsetdec).
    assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup ρa X)
                   = msubst_lookup (msubst_compose (aenv_msubst Θ) ρ) X).
    { rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ (or_introl HXρ)).
      f_equal. rewrite Heqρ. symmetry. apply msubst_lookup_app_in; exact HX. }
    rewrite Heqlk.
    eapply AtomSetProperties.subset_trans;
      [ apply (msubst_pskl_ftv_lower (msubst_compose (aenv_msubst Θ) ρ) P HXP) | ].
    rewrite msubst_pskl_compose; [ exact HO2 | exact Hside ]. }
  assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
  { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3. exact Hb. }
  assert (Hinc_sub0 : (Ξ ++ Θ0) ≤[ (msubst_compose (aenv_msubst Θ) ρa)
                          ++ (msubst_compose (aenv_msubst Θ) ρb') ] Θ').
  { assert (HincR : (Ξ ++ (x ~ abind_var_typ Q) ++ Θ0) ≤[ ρa ++ ρb' ] Θ)
      by (rewrite <- Heqρ; exact Hinc).
    eapply a_inc_downarrow_prefix;
      [ exact Hdecl | exact HincR | exact Huqf | exact Hdρa
      | exact Hincb_n | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
  assert (Hinc_sub : (Ξ ++ Θ0) ≤[ msubst_compose (aenv_msubst Θ) ρ ] Θ').
  { rewrite Heqρ. rewrite msubst_compose_app. exact Hinc_sub0. }
  (* the join over Θ' at ⇓ρ *)
  assert (Hmona : mono_ptyp (msubst_lookup ρ α)) by (eapply a_inc_lookup_mono; exact Hinc).
  assert (Hf0 : a_flex_tvar Θ0 α) by (eapply a_assign_subject_flex_local; exact Ha).
  assert (HαΘ0 : α `in` dom Θ0)
    by (destruct Hf0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
  assert (Hαρa : α `notin` dom ρa)
    by (rewrite Hdρa; clear - Huqf HαΘ0; simpl_env in Huqf; solve_uniq).
  assert (Hbtα0 : a_binds_tvar α Θ0)
    by (destruct Hf0 as [Hb | [τ0 Hb]];
        [ right; left; exact Hb | right; right; exists τ0; exact Hb ]).
  assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup ρ α)).
  { rewrite Heqρ. rewrite (msubst_lookup_app_notin ρa ρb' Hαρa).
    eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | exact Hbtα0 ]. }
  assert (Hftvα : ftvar_in_ptyp (msubst_lookup ρ α) [<=] dom Θ')
    by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
  assert (Hvisα : forall Y, Y `in` ftvar_in_ptyp (msubst_lookup ρ α) -> a_binds_tvar Y Θ).
  { intros Y HY.
    assert (HbtY' : a_binds_tvar Y Θ')
      by (eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfα' | exact HY ]).
    destruct HbtY' as [Hb | [Hb | [τ0 Hb]]];
      [ left | right; left | right; right; exists τ0 ]; apply Hsub'; exact Hb. }
  assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup ρ α) = ⇓ᵗ[ Θ' ] (msubst_lookup ρ α)).
  { rewrite <- HeqW.
    apply downarrow_app_agree_ptyp; [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
  assert (Hj1 : ad_pat_consis empty Θ
            (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)))
            (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α)))).
  { eapply consis_downarrow_subject;
      [ exact Hjoin | exact Hwfth | reflexivity | reflexivity | exact Hmona ]. }
  assert (Heqρα : Θ ⊢ (msubst_lookup ρ α) ≡ᵗ (⇓ᵗ[ Θ ] (msubst_lookup ρ α))).
  { apply a_tyequiv_to_downarrow_mono;
      [ exact Hwfth | eapply a_wf_ptyp_weaken; [ exact Hsub' | exact Hwfα' ] | exact Hmona ]. }
  destruct (tyequiv_mono_consis_transport_q Heqρα Hwfth Hmona Hvisα) as [_ Hfwd].
  pose proof (Hfwd empty _ Hj1) as Hj2.
  assert (Hjstr : ad_pat_consis empty Θ'
            (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl ρ P)))
            (pskl_to_bskl_syn (ptyp_to_pskl (⇓ᵗ[ Θ ] (msubst_lookup ρ α))))).
  { eapply ad_pat_consis_strengthen;
      [ exact Hj2 | exact HuqΘ | exact HwfΘ' | exact Hsub' | | ].
    - intros Z HZ. rewrite ftvar_in_uskl_pskl in HZ. clear - HO2 HZ. fsetdec.
    - intros Z HZ. rewrite ftvar_in_bskl_syn in HZ.
      rewrite ftvar_in_ptyp_to_pskl in HZ.
      rewrite Hddα in HZ.
      assert (a_wf_ptyp Θ' (⇓ᵗ[ Θ' ] (msubst_lookup ρ α)))
        by (apply a_wf_ptyp_downarrow_mono; [ exact HwfΘ' | exact Hwfα' | exact Hmona ]).
      apply a_wf_ptyp_ftv_dom in H. clear - H HZ. fsetdec. }
  assert (Hjoin_sub : empty ⨟ Θ' ⊨ₛᵃ
            (pskl_to_uskl (msubst_pskl (msubst_compose (aenv_msubst Θ) ρ) P))
          ≈ (pskl_to_bskl_syn (ptyp_to_pskl
              (msubst_lookup (msubst_compose (aenv_msubst Θ) ρ) α)))).
  { assert (Hαρ : α `in` dom ρ).
    { rewrite Heqρ. rewrite dom_app.
      assert (Hαb : α `in` dom ρb')
        by (eapply a_inc_flex_dom; [ exact Hincb | exact Hwf0 | exact Hf0 ]).
      clear - Hαb. fsetdec. }
    rewrite (msubst_pskl_compose (aenv_msubst Θ) ρ P Hside).
    rewrite (msubst_lookup_compose (aenv_msubst Θ) ρ (or_introl Hαρ)).
    exact Hjstr. }
  (* id-witness for the sub *)
  assert (Hinc1_s : (Ξ ++ Θ0) ≤[ ρ1 ] Θ1)
    by (eapply a_inc_var_mid_strip_id; [ exact Hdecl | exact Hid | exact Hinc1 ]).
  destruct (IHa Hdecl Hwf' HwfP' Hdomξ ρ1 (msubst_compose (aenv_msubst Θ) ρ) Θ'
                Hid Hinc1_s Hinc_sub HwfΘ' Hjoin_sub) as [ζ' [Hζ' Hie']].
  exists ζ'. split.
  - (* ((x:Q)++Θ1) ≤[ζ'] Θ  via a_inc__var *)
    rewrite HeqΘ. apply a_inc__var; [ exact Hζ' | | exact HsufΞv ].
    (* Θ'⊢A'≡msubst ζ' Q : chain A'≡msubst ρb' Q ≡ msubst ζ' Q *)
    assert (HwfaΘ0x : a_wf_aenv ((x ~ abind_var_typ Q) ++ Θ0))
      by (eapply a_wf_aenv_app_r; exact Hwf).
    destruct (a_wf_aenv_var_typ_inv HwfaΘ0x) as [_ [HwfQ0 _]].
    assert (HwfQ : a_wf_ptyp (Ξ ++ Θ0) Q)
      by (eapply a_wf_ptyp_weaken; [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
    assert (HlcQ : lc_ptyp Q) by (eapply a_wf_ptyp_lc; exact HwfQ0).
    assert (HwfΘ1 : a_wf_aenv Θ1)
      by (eapply a_assign_preserves_wf; [ exact Ha | exact Hdecl | exact Hwf' | exact HwfP' ]).
    assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) ρ))
      by (eapply a_inc_msubst_lc; exact Hinc_sub).
    assert (Hlc2 : msubst_lc (msubst_compose ζ' ρ1)).
    { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ' | ].
      intros a t Hin. eapply is_id_msubst_values_lc; [ exact Hid | exact Hin ]. }
    pose proof (a_inc_equiv_msubst_ptyp HwfQ Hie' Hwf' Hlc1 Hlc2) as Hmid.
    rewrite (msubst_compose_id_ptyp Hwf' HwfΘ1 Hid Hinc1_s Hζ' HwfQ) in Hmid.
    assert (Hag : msubst_ptyp (msubst_compose (aenv_msubst Θ) ρ) Q
                = msubst_ptyp (msubst_compose (aenv_msubst Θ) ρb') Q).
    { apply msubst_ptyp_agree. intros X HXQ.
      rewrite Heqρ. rewrite msubst_compose_app.
      apply msubst_lookup_app_notin.
      rewrite dom_msubst_compose. rewrite Hdρa.
      assert (HXΘ0 : X `in` dom Θ0)
        by (apply a_wf_ptyp_ftv_dom in HwfQ0; clear - HwfQ0 HXQ; fsetdec).
      clear - Huqf HXΘ0. simpl_env in Huqf. solve_uniq. }
    rewrite Hag in Hmid.
    eapply a_tyequiv__trans; [ exact HeqA' | ].
    eapply a_tyequiv__trans; [ | exact Hmid ].
    apply a_tyequiv__sym.
    eapply msubst_compose_downarrow_tyequiv with (Θpre := Ξv ++ (x ~ abind_var_typ A'));
      [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth
      | exact HwfΘ' | eapply a_inc_msubst_lc; exact Hincb
      | intros X HXd;
        destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
        (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
        [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
      | exact HlcQ ].
  - (* factoring: mid_insert_var over ⇓ρ, then ⇓ρ→ρ via self_downarrow + trans *)
    assert (HwfaΘ0x : a_wf_aenv ((x ~ abind_var_typ Q) ++ Θ0))
      by (eapply a_wf_aenv_app_r; exact Hwf).
    destruct (a_wf_aenv_var_typ_inv HwfaΘ0x) as [_ [HwfQ0 _]].
    assert (HlcQ : lc_ptyp Q) by (eapply a_wf_ptyp_lc; exact HwfQ0).
    destruct (@a_inc_strip_decls_prefix Ξ ((x ~ abind_var_typ Q) ++ Θ0) ρ1
                ((x ~ abind_var_typ Q) ++ Θ1) Hdecl Hinc1)
      as [ρ1a [ρ1b' [Heqρ1' [Hdρ1a Hinc1x]]]].
    assert (Hmiddle : Θ' ⊢ A' ≡ᵗ msubst_ptyp (msubst_compose (aenv_msubst Θ) ρb') Q).
    { eapply a_tyequiv__trans; [ exact HeqA' | ].
      apply a_tyequiv__sym.
      eapply msubst_compose_downarrow_tyequiv with (Θpre := Ξv ++ (x ~ abind_var_typ A'));
        [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
        | eapply a_inc_msubst_lc; exact Hincb
        | intros X HXd;
          destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
          (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
        | exact HlcQ ]. }
    assert (Hmi : a_inc_equiv (Ξ ++ (x ~ abind_var_typ Q) ++ Θ0)
                    (msubst_compose (aenv_msubst Θ) ρ) (msubst_compose ζ' ρ1)
                    (Ξv ++ (x ~ abind_var_typ A') ++ Θ')).
    { rewrite Heqρ. rewrite (msubst_compose_app (aenv_msubst Θ) ρa ρb').
      rewrite Heqρ1'. rewrite (msubst_compose_app ζ' ρ1a ρ1b').
      apply a_inc_equiv_mid_insert_var;
        [ exact Hdecl | exact Huq' | rewrite dom_msubst_compose; exact Hdρa
        | rewrite dom_msubst_compose; exact Hdρ1a | exact Hmiddle | exact HsufΞv | ].
      rewrite Heqρ in Hie'. rewrite (msubst_compose_app (aenv_msubst Θ) ρa ρb') in Hie'.
      rewrite Heqρ1' in Hie'. rewrite (msubst_compose_app ζ' ρ1a ρ1b') in Hie'.
      exact Hie'. }
    rewrite <- HeqΘ in Hmi.
    eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
    pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind))) as Hself.
    simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ].
Qed.

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
    intros Hdecl Hwf HwfP Hdomξ ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Hjoin.
    simpl_env in *. exists ρ.
    apply (opt_axiom_factor Hwf Hid Hinc1 Hinc).
  - admit. (* TODO[optimality]: Assign-SolveM; the guessed β̄ extends Θ1; true;
              blocked on building ζ from guess^TY's monotype + occurs check. *)
  - admit. (* TODO[optimality]: Assign-Assign; consistency sub-IH (back-edge);
              true; blocked on threading the sub-node solution + glue. *)
  - (* Assign-Depend : the pending suffix grows at the TAIL, so the merged
       context [Ξ ++ (β~flex) ++ Θ0] and the target Θ1 are LITERALLY the
       IH's, re-associated.  Direct from the IH; no mid-insert needed. *)
    intros F Θ0 Θ1 Ξ α β P Hne Hβin Ha IHa.
    unfold assign_optimal_post in *.
    intros Hdecl Hwf HwfP Hdomξ ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Hjoin.
    assert (Hdecl' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app;
          [ exact Hdecl | apply (a_decls__cons β); apply a_decls__nil ]).
    assert (Hdomξ' : dom (Ξ ++ (β ~ abind_flex_mono)) [<=] ftvar_in_pskl P)
      by (repeat rewrite dom_app; simpl; clear - Hdomξ Hβin; fsetdec).
    rewrite <- app_assoc in Hwf, HwfP, Hinc1, Hinc.
    destruct (IHa Hdecl' Hwf HwfP Hdomξ' ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Hjoin)
      as [ζ [Hζ Hie]].
    exists ζ. split; [ exact Hζ | ].
    rewrite app_assoc in Hie. exact Hie.
  - (* Assign-Skip : β sandwiched Ξ ++ [β] ++ Θ0; target Θ1 SHRINKS (β dropped),
       the genuine mid-insert case (closed 2026-07-15 via
       [a_inc_equiv_mid_insert_flex]). *)
    intros F Θ0 Θ1 Ξ α β P Hne Hβin Ha IHa.
    unfold assign_optimal_post in *.
    intros Hdecl Hwf HwfP Hdomξ ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Hjoin.
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0)) by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P)
      by (eapply ad_wf_pskl_strip_mid; [ exact HwfP | exact Hβin ]).
    assert (Huqf : uniq (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq' : uniq (Ξ ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf').
    assert (HβΞ : β `notin` dom Ξ) by (clear - Huqf; simpl_env in Huqf; solve_uniq).
    (* peel the competing ρ and the identity ρ1 at β *)
    destruct (a_inc_mid_strip_flex β Θ0 Hdecl Hinc)
      as [ρa [τ [ρb [Heqρ [Hdρa [Hincb Hincab]]]]]].
    destruct (a_inc_mid_strip_flex β Θ0 Hdecl Hinc1)
      as [ρ1a [τβ [ρ1b [Heqρ1 [Hdρ1a [Hinc1b Hinc1ab]]]]]].
    (* ρ1a, ρ1b are identity; τβ = β̂ *)
    rewrite Heqρ1 in Hid.
    apply Forall_app in Hid as [Hida Hidtail].
    pose proof (Forall_inv Hidtail) as Heβ.
    pose proof (Forall_inv_tail Hidtail) as Hidb.
    unfold is_id_entry in Heβ; simpl in Heβ; subst τβ.
    assert (Hidab : is_id_msubst (ρ1a ++ ρ1b))
      by (apply Forall_app; split; assumption).
    (* τ = lookup ρ β, well-formed monotype *)
    assert (Hβρa : β `notin` dom ρa) by (rewrite Hdρa; exact HβΞ).
    assert (Hlkβ : msubst_lookup ρ β = τ)
      by (rewrite Heqρ; rewrite msubst_lookup_app_notin by exact Hβρa;
          apply msubst_lookup_cons_eq).
    assert (Hmτ : mono_ptyp τ)
      by (rewrite <- Hlkβ; eapply a_inc_lookup_mono; exact Hinc).
    assert (Hbtβ : a_binds_tvar β (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (right; left; unfold binds; apply in_or_app; right; left; reflexivity).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (rewrite <- Hlkβ;
          eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact Hbtβ ]).
    (* sub id-witness w = ρ1a ++ ρ1b *)
    destruct (a_assign_sound Ha Hdecl Hwf' HwfP') as [[[w [Hidw Hincw]] _] _].
    assert (Hweq : w = ρ1a ++ ρ1b)
      by (eapply is_id_inc_unique;
          [ exact Hincw | exact Hidw | exact Hinc1ab | exact Hidab ]).
    (* transfer the competing join to the β-dropped increment ρa ++ ρb *)
    assert (Hlkα : msubst_lookup (ρa ++ ρb) α = msubst_lookup ρ α)
      by (rewrite Heqρ; symmetry; apply msubst_lookup_mid_drop; exact Hne).
    assert (HeqP : msubst_pskl (ρa ++ ρb) P = msubst_pskl ρ P).
    { rewrite Heqρ. apply msubst_pskl_agree. intros X HX.
      symmetry. apply msubst_lookup_mid_drop.
      clear - HX Hβin. intro; subst X; contradiction. }
    assert (HjoinSub : empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl (ρa ++ ρb) P))
              ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup (ρa ++ ρb) α))))
      by (rewrite HeqP, Hlkα; exact Hjoin).
    destruct (IHa Hdecl Hwf' HwfP' Hdomξ w (ρa ++ ρb) Θ
                  Hidw Hincw Hincab Hwfth HjoinSub)
      as [ζ' [Hζ' Hie']].
    (* rebuild ζ := (β, τ) :: ζ' *)
    exists ((β, τ) :: ζ'). split.
    + apply a_inc__flex; [ exact Hζ' | exact Hwfτ | exact Hmτ ].
    + (* factoring, via the mid-insert lemma *)
      assert (HβΘ0 : β `notin` dom Θ0)
        by (clear - Huqf; simpl_env in Huqf; solve_uniq).
      assert (Hβρ1a : β `notin` dom ρ1a) by (rewrite Hdρ1a; exact HβΞ).
      assert (Hβρ1b : β `notin` dom ρ1b).
      { assert (Hd1b : dom (ρ1a ++ ρ1b) [<=] dom (Ξ ++ Θ0))
          by (eapply a_inc_dom_sub; exact Hinc1ab).
        clear - Hd1b HβΞ HβΘ0 Hdρ1a. simpl_env in *. fsetdec. }
      (* compose ((β,τ)::ζ') ρ1 = compose ζ' ρ1a ++ (β,τ) :: compose ζ' ρ1b *)
      assert (Hcz : msubst_compose ((β, τ) :: ζ') ρ1
                    = msubst_compose ζ' ρ1a ++ (β, τ) :: msubst_compose ζ' ρ1b).
      { rewrite Heqρ1. rewrite msubst_compose_app.
        change (msubst_compose ((β, τ) :: ζ')
                  ((β, ptyp_var_f β) :: ρ1b))
          with ((β, msubst_ptyp ((β, τ) :: ζ') (ptyp_var_f β))
                :: msubst_compose ((β, τ) :: ζ') ρ1b).
        change (msubst_ptyp ((β, τ) :: ζ') (ptyp_var_f β))
          with (msubst_lookup ((β, τ) :: ζ') β).
        rewrite msubst_lookup_cons_eq.
        rewrite (msubst_compose_cons_l_id τ ζ' Hida Hβρ1a).
        rewrite (msubst_compose_cons_l_id τ ζ' Hidb Hβρ1b).
        reflexivity. }
      rewrite Hcz.
      (* compose ζ' w = compose ζ' ρ1a ++ compose ζ' ρ1b *)
      rewrite Hweq in Hie'. rewrite msubst_compose_app in Hie'.
      rewrite Heqρ.
      apply a_inc_equiv_mid_insert_flex;
        [ exact Hdecl | exact Huq' | exact Hdρa
        | rewrite dom_msubst_compose; exact Hdρ1a
        | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτ
        | exact Hie' ].
  - admit. (* TODO[optimality]: Assign-SkipRigid; RIGID walk. Here the competing
              target GROWS: (β~tvar ++ Θ0) ≤[ρ] Θ inverts (a_inc_tvar_inv) to
              Θ = Ξ ++ (β~tvar) ++ Θ' with Θ0 ≤[ρ] Θ'. The join is over Θ but the
              sub-node needs it over Θ' => NEEDS a ⊨ₛᵃ (join) CONTEXT-STRENGTHENING
              lemma (SECOND infrastructure need, not the ≡ᵗ one). *)
  - (* Assign-SkipTmVar(typ) : CLOSED 2026-07-16 via [skip_tm_var_case] (the GMM
       ⇓-normalizing factoring: a_inc_self_downarrow + a_inc_downarrow_prefix land
       the competing at ⇓ρ over the sub-target Θ', consis_downarrow_subject +
       O2 grounding transfer the join, a_inc_equiv_mid_insert_var +
       a_inc_equiv_self_downarrow rebuild the factoring). *)
    intros F Θ0 Θ1 Ξ α x Q P Ha IHa.
    apply (skip_tm_var_case Ha IHa).
  - admit. (* TODO[optimality]: Assign-SkipTmVar(skl); as SkipTmVar(typ), with
              ≡ˢ/a_pskl_tyequiv_msubst on the skeleton binding. *)
  (* ================= a_unify (6) ================= *)
  - (* Flex-Flex-Id : Θ1 = Θ0, pure identity-node factoring *)
    intros F Θ0 α Hfa. unfold unify_optimal_post.
    intros Hwf _ _ ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Heq.
    exists ρ. apply (opt_axiom_factor Hwf Hid Hinc1 Hinc).
  - (* Flex-Flex-L : α̂ := β̂.  ζ := ρ; the head flex-image [τ] plays the role of
       the definition's image, and the competing equality [ρα̂ ≡ ρβ̂] is exactly
       the [flex_def] side condition.  The factoring collapses (ρ1 identity). *)
    intros F Θ0 α β Hne Hfβ.
    unfold unify_optimal_post.
    intros Hwf Hfα' Hfβ' ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Heq.
    assert (Hβα : β <> α) by auto.
    inversion Hinc as [ | Θs ρs Θt αs τ Hinc' Hwfτ Hmτ [Heqα Heqρ] Heqt | | | | ];
      subst.
    exists ((α, τ) :: ρs). split.
    + apply a_inc__flex_def; auto.
      rewrite msubst_lookup_cons_eq in Heq.
      rewrite (msubst_lookup_cons_neq τ ρs Hβα) in Heq.
      exact Heq.
    + rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
      apply a_inc_equiv_refl; exact Hinc.
  - (* Flex-Flex-R : β̂ := α̂.  Symmetric to L; the [flex_def] side condition is
       the competing equality read the other way, so it closes by [sym]. *)
    intros F Θ0 α β Hne Hfα.
    unfold unify_optimal_post.
    intros Hwf Hfα' Hfβ' ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Heq.
    assert (Hαβ : α <> β) by auto.
    inversion Hinc as [ | Θs ρs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqρ] Heqt | | | | ];
      subst.
    exists ((β, τ) :: ρs). split.
    + apply a_inc__flex_def; auto.
      rewrite msubst_lookup_cons_eq in Heq.
      rewrite (msubst_lookup_cons_neq τ ρs Hαβ) in Heq.
      apply a_tyequiv__sym; exact Heq.
    + rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
      apply a_inc_equiv_refl; exact Hinc.
  - admit. (* TODO[optimality]: Flex-Flex-Assign; consistency sub-IH (back-edge);
              true; blocked on the bridge + glue. *)
  - (* Flex-Flex-Skip : head flex γ̂ skipped (γ≠α,β).  Peel γ̂ off the competing
       ρ = (γ,τγ)::ρs, run the sub-IH with the soundness ⊴-witness (which the
       inverted conclusion-witness equals by id-uniqueness), then re-cons γ̂. *)
    intros F Θ0 Θ1 γ α β Hγα Hγβ Hu IHu.
    unfold unify_optimal_post.
    intros Hwf Hfα Hfβ ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Heq.
    inversion Hwf as [ | γh Θh Hnd Hwf0 | | | | ]; subst.
    destruct (a_unify_subjects_flex Hwf0 Hu) as [Hfα0 Hfβ0].
    assert (Hαγ : α <> γ) by auto.
    assert (Hβγ : β <> γ) by auto.
    inversion Hinc as [ | Θs ρs Θt γs τγ Hincs Hwfτ Hmτ [Heqγ Heqρ] Heqt
                      | | | | ]; subst.
    inversion Hinc1 as [ | Θp ρp Θq γp τp Hincp Hwfp Hmp [Heqγ1 Heqρ1] Heqt1
                       | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτp Hid1s]; subst.
    destruct (a_unify_sound Hu Hwf0) as [[[w [Hidw Hincw]] _] [Hwf1 _]].
    assert (Hw : ρp = w) by (eapply is_id_inc_unique; eauto). subst w.
    assert (Hγw : γ `notin` dom ρp)
      by (pose proof (a_inc_dom_sub Hincp) as Hs; clear - Hs Hnd; fsetdec).
    rewrite (msubst_lookup_cons_neq τγ ρs Hαγ) in Heq.
    rewrite (msubst_lookup_cons_neq τγ ρs Hβγ) in Heq.
    destruct (IHu Hwf0 Hfα0 Hfβ0 ρp ρs Θ Hid1s Hincw Hincs Hwfth Heq)
      as [ζ' [Hζ' Hie']].
    exists ((γ, τγ) :: ζ'). split.
    + apply a_inc__flex; auto.
    + assert (Heqc : msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: ρp)
                     = (γ, τγ) :: msubst_compose ζ' ρp).
      { change (msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: ρp))
          with ((γ, msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                :: msubst_compose ((γ, τγ) :: ζ') ρp).
        rewrite (msubst_compose_cons_l_id τγ ζ' Hid1s Hγw).
        change (msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
          with (msubst_lookup ((γ, τγ) :: ζ') γ).
        rewrite msubst_lookup_cons_eq. reflexivity. }
      rewrite Heqc.
      apply a_inc_equiv__flex; [ exact Hie' | ].
      apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτ.
  - (* Flex-Flex-Skip' (a_unify__skip_other).  ALL THREE b-shapes CLOSED under
       the adopted GMM-semantic middles (2026-07-15).  Peel the non-flex middle
       [c ~ b] off the competing increment (a_inc_tvar/var/var_skl_inv); the
       identity increment strengthens directly (a_inc_id_mid_strip, suffix
       forced nil); strengthen the [≡ᵗ] join to the sub-target via
       [a_tyequiv_strengthen_mono_mid]; run the sub-IH; rebuild with ζ := ζ'.
       The var/var_skl middles' [≡]-premise transports across the increment via
       [a_inc_equiv_msubst_ptyp]/[_pskl] + [msubst_compose_id_ptyp]/[_pskl]. *)
    intros F Θ0 Θ1 c b α β Hbcase Hu IHu.
    unfold unify_optimal_post in *.
    intros Hwf Hfα Hfβ ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Heq.
    assert (Hwf0 : a_wf_aenv Θ0)
      by (apply (a_wf_aenv_strip_prefix_local (c ~ b)); exact Hwf).
    destruct (a_unify_subjects_flex Hwf0 Hu) as [Hfα0 Hfβ0].
    assert (Hbtα : a_binds_tvar α Θ0) by (right; exact Hfα0).
    assert (Hbtβ : a_binds_tvar β Θ0) by (right; exact Hfβ0).
    assert (Hinc1' : Θ0 ≤[ ρ1 ] Θ1)
      by (eapply a_inc_id_mid_strip; [ exact Hbcase | exact Hinc1 ]).
    destruct Hbcase as [-> | [[Q ->] | [Q ->]]].
    + (* b = abind_tvar : no middle payload, no bridge needed *)
      apply a_inc_tvar_inv in Hinc as [Ξ [Θ2 [-> [HΞ Hinc']]]].
      assert (Hwfth2 : a_wf_aenv Θ2)
        by (rewrite <- app_assoc in Hwfth;
            apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
      assert (Heq2 : Θ2 ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β)).
      { eapply a_tyequiv_strengthen_mono_mid;
          [ exact Hwfth
          | eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]
          | eapply a_inc_lookup_mono; exact Hinc'
          | eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]
          | eapply a_inc_lookup_mono; exact Hinc'
          | exact Heq ]. }
      destruct (IHu Hwf0 Hfα0 Hfβ0 ρ1 ρ Θ2 Hid Hinc1' Hinc' Hwfth2 Heq2)
        as [ζ' [Hζ' Hie']].
      exists ζ'. split.
      * apply a_inc__tvar; [ exact Hζ' | exact HΞ ].
      * apply a_inc_equiv__tvar; [ exact Hie' | exact HΞ ].
    + (* b = abind_var_typ Q : semantic type middle *)
      apply a_inc_var_inv in Hinc as [Ξ [A' [Θ2 [-> [HA'eq [HΞ Hinc']]]]]].
      assert (Hwfth2 : a_wf_aenv Θ2)
        by (rewrite <- app_assoc in Hwfth;
            apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
      assert (Heq2 : Θ2 ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β)).
      { eapply a_tyequiv_strengthen_mono_mid;
          [ exact Hwfth
          | eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]
          | eapply a_inc_lookup_mono; exact Hinc'
          | eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]
          | eapply a_inc_lookup_mono; exact Hinc'
          | exact Heq ]. }
      destruct (IHu Hwf0 Hfα0 Hfβ0 ρ1 ρ Θ2 Hid Hinc1' Hinc' Hwfth2 Heq2)
        as [ζ' [Hζ' Hie']].
      destruct (a_wf_aenv_var_typ_inv Hwf) as [_ [HwfQ _]].
      destruct (a_unify_sound Hu Hwf0) as [_ [Hwf1 _]].
      assert (Hbridge : Θ2 ⊢ A' ≡ᵗ (msubst_ptyp ζ' Q)).
      { eapply a_tyequiv__trans; [ exact HA'eq | ].
        rewrite <- (msubst_compose_id_ptyp Hwf0 Hwf1 Hid Hinc1' Hζ' HwfQ).
        eapply a_inc_equiv_msubst_ptyp;
          [ exact HwfQ | exact Hie' | exact Hwf0
          | eapply a_inc_msubst_lc; exact Hinc'
          | eapply msubst_lc_compose;
              [ eapply a_inc_msubst_lc; exact Hζ'
              | eapply is_id_msubst_values_lc; exact Hid ] ]. }
      exists ζ'. split.
      * apply a_inc__var; [ exact Hζ' | exact Hbridge | exact HΞ ].
      * apply a_inc_equiv__var; [ exact Hie' | exact HA'eq | exact HΞ ].
    + (* b = abind_var_skl Q : semantic skeleton middle *)
      apply a_inc_var_skl_inv in Hinc as [Ξ [P' [Θ2 [-> [HP'eq [HΞ Hinc']]]]]].
      assert (Hwfth2 : a_wf_aenv Θ2)
        by (rewrite <- app_assoc in Hwfth;
            apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
      assert (Heq2 : Θ2 ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β)).
      { eapply a_tyequiv_strengthen_mono_mid;
          [ exact Hwfth
          | eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]
          | eapply a_inc_lookup_mono; exact Hinc'
          | eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]
          | eapply a_inc_lookup_mono; exact Hinc'
          | exact Heq ]. }
      destruct (IHu Hwf0 Hfα0 Hfβ0 ρ1 ρ Θ2 Hid Hinc1' Hinc' Hwfth2 Heq2)
        as [ζ' [Hζ' Hie']].
      destruct (a_wf_aenv_var_skl_inv Hwf) as [_ [HwfQ _]].
      destruct (a_unify_sound Hu Hwf0) as [_ [Hwf1 _]].
      assert (Hbridge : Θ2 ⊢ P' ≡ˢ (msubst_pskl ζ' Q)).
      { eapply a_pskl_tyequiv__trans; [ exact HP'eq | ].
        rewrite <- (msubst_compose_id_pskl Hwf0 Hwf1 Hid Hinc1' Hζ' HwfQ).
        eapply a_inc_equiv_msubst_pskl;
          [ exact HwfQ | exact Hie' | exact Hwf0
          | eapply a_inc_msubst_lc; exact Hinc'
          | eapply msubst_lc_compose;
              [ eapply a_inc_msubst_lc; exact Hζ'
              | eapply is_id_msubst_values_lc; exact Hid ] ]. }
      exists ζ'. split.
      * apply a_inc__var_skl; [ exact Hζ' | exact Hbridge | exact HΞ ].
      * apply a_inc_equiv__var_skl; [ exact Hie' | exact HP'eq | exact HΞ ].
  (* ================= a_consis (14) ================= *)
  - (* C-Ghost : axiom, Θ1=Θ0.  ζ:=ρ (opt_axiom_factor).  The SUBJECT is the
       ghost hole, so the competing join forces the target Qb to be inherited
       (consis_hole_target_inh); the precision goal then collapses to the
       competing Δ₁-refinement of the INPUT P0 (Hrs), Δ-weakened. *)
    intros F Δ1 Δ2 Θ0 P0 Hint. unfold consis_optimal_post.
    intros Hwf HwfP0 HwfP Hrig Hnfd Hfaf ρ1 ρ Θ Qt Qb
           Hid Hinc1 HeqQt Hinc Hwfth Hnfdc Hjoin Hrs Hrp.
    exists ρ.
    destruct (opt_axiom_factor Hwf Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    replace (pskl_to_uskl (msubst_pskl ρ pskl_hole)) with uskl_hole in Hjoin
      by reflexivity.
    pose proof (consis_hole_target_inh Hjoin) as Hqinh.
    unfold ad_precise. rewrite Hqinh.
    rewrite bskl_to_pskl_msubst_bskl, HeqQt.
    apply ad_refine_syn_delta_mono with (Δ0 := Δ1); [ | clear; fsetdec ].
    apply ad_refine_syn_f_forget in Hrs. exact Hrs.
  - (* C-Unit : axiom, Θ1=Θ0.  ζ:=ρ (opt_axiom_factor); precision from the unit
       join via consis_precise_mono_join. *)
    intros F Δ1 Δ2 Θ0. unfold consis_optimal_post.
    intros Hwf HwfP0 HwfP Hrig Hnfd Hfaf ρ1 ρ Θ Qt Qb
           Hid Hinc1 HeqQt Hinc Hwfth Hnfdc Hjoin Hrs Hrp.
    exists ρ.
    destruct (opt_axiom_factor Hwf Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    destruct Qt; simpl in HeqQt; try discriminate. clear HeqQt.
    cbn [msubst_bskl bskl_to_pskl].
    apply consis_precise_mono_join with (A := ptyp_unit);
      [ exact Hwfth | apply mono_ptyp__unit
      | intros X HX; simpl in HX; clear - HX; fsetdec
      | exact Hjoin ].
  - (* C-Rigid : axiom, Θ1=Θ0.  Subject α is a RIGID tvar, so ρ fixes it
       (α∉dom ρ); ζ:=ρ; precision by consis_precise_mono_join at A:=`α. *)
    intros F Δ1 Δ2 Θ0 α Hbind. unfold consis_optimal_post.
    intros Hwf HwfP0 HwfP Hrig Hnfd Hfaf ρ1 ρ Θ Qt Qb
           Hid Hinc1 HeqQt Hinc Hwfth Hnfdc Hjoin Hrs Hrp.
    exists ρ.
    destruct (opt_axiom_factor Hwf Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    assert (Hαnρ : α `notin` dom ρ).
    { intros Hin. pose proof (a_wf_aenv_uniq Hwf) as Hu.
      destruct (a_inc_dom_flex Hinc Hin) as [Hb | [τ Hb]];
        pose proof (binds_unique _ _ _ _ _ Hbind Hb Hu) as Hcon; discriminate. }
    assert (Hbtα : binds α abind_tvar Θ) by (eapply a_inc_binds_tvar; eauto).
    destruct Qt; simpl in HeqQt; try discriminate.
    inversion HeqQt; subst. clear HeqQt.
    cbn [msubst_bskl]. rewrite bskl_to_pskl_pskl_to_bskl_syn.
    rewrite (msubst_lookup_notin ρ Hαnρ).
    apply consis_precise_mono_join with (A := ptyp_var_f α);
      [ exact Hwfth | apply mono_ptyp__var
      | intros X HX; simpl in HX;
        assert (HXα : X = α) by (clear - HX; fsetdec); subst X; left; exact Hbtα
      | ].
    replace (msubst_pskl ρ (pskl_var_f α))
      with (ptyp_to_pskl (msubst_lookup ρ α)) in Hjoin by reflexivity.
    rewrite (msubst_lookup_notin ρ Hαnρ) in Hjoin.
    rewrite pskl_to_uskl_ptyp in Hjoin. exact Hjoin.
  - admit. (* TODO[optimality]: C-Arrow; STRUCTURAL, two sub-nodes; true;
              a_inc_equiv_glue composes the two factorings; blocked on threading
              the sub-node solutions (soundness output -> optimality input) and
              discharging the glue's wf + flex-dom side conditions. *)
  - admit. (* TODO[optimality]: C-ForallInh; STRUCTURAL, Δ GROWS by the opened α.
              glue with the cofinite α-extended ζ.  The paper's no_flex_dep-on-Θ
              side condition (consistency-proofs.tex:2239-2240) is NOW IN THE
              MOTIVE ([no_flex_dep (Δ1∪Δ2) Θ], 2026-07-15); the sub-node's
              [no_flex_dep (add α _) ((α~tvar)++Θ)] is derivable from it + α
              fresh + wf.  Remaining work: cofinite inversion of the competing
              join/refinements, sub-solution assembly, and the outer precision
              reassembly (context-strip of the opened rigid α + rename). *)
  - admit. (* TODO[optimality]: C-ForallSyn; STRUCTURAL, Δ2 GROWS; glue; as
              C-ForallInh (no_flex_dep-on-Θ now in the motive). *)
  - (* C-UnivGhost.  Jointly invert the competing join and its two refinement
       witnesses.  The apparent [tophole_inh] branch is impossible; the two
       surviving branches either keep or drop the wrapper uniformly. *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P Q Hc IHc.
    unfold consis_optimal_post in *.
    intros Hwf HwfP0 HwfP Hrig Hnfd Hfaf ρ1 ρ Θ Qt Qb
           Hid Hinc1 HeqQt Hinc Hwfth Hnfdc Hjoin Hrs Hrp.
    assert (Hg0 : guarded_pskl P0) by (inversion HwfP0; assumption).
    assert (Hg : guarded_pskl P) by (inversion HwfP; assumption).
    assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0) by (inversion HwfP0; assumption).
    assert (HwfP' : Θ0 ⨟ empty ⊢ₚₛᵃ P) by (inversion HwfP; assumption).
    assert (Hg0ρ : guarded_pskl (msubst_pskl ρ P0))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (Hgρ : guarded_pskl (msubst_pskl ρ P))
      by (eapply guarded_pskl_msubst_inc; eauto).
    change (empty ⨟ Θ ⊨ₛᵃ
              (uskl_tophole (pskl_to_uskl (msubst_pskl ρ P))) ≈ Qb) in Hjoin.
    change (ad_refine_syn_f Δ1 Θ Δ1
              (bskl_tophole (pskl_to_bskl_inh (msubst_pskl ρ P0))) Qb) in Hrs.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl ρ P)) (bskl_to_pskl Qb)) in Hrp.
    destruct Qt as [|n|X|Qt1 Qt2|Qt|Qt| |Qt];
      simpl in HeqQt; try discriminate.
    inversion HeqQt; subst Q.
    destruct (consis_tophole_solution_inv Hwfth Hg0ρ Hgρ Hjoin Hrs Hrp)
      as [[Qb' [-> [Hjoin' [Hrs' Hrp']]]] | [Hjoin' [Hrs' Hrp']]].
    + destruct (IHc Hwf HwfP0' HwfP' Hrig Hnfd Hfaf
                   ρ1 ρ Θ Qt Qb' Hid Hinc1 eq_refl Hinc Hwfth Hnfdc
                   Hjoin' Hrs' Hrp')
        as [ζ [Hζ [Hie Hprec]]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      unfold ad_precise in *. simpl.
      apply ad_refine_syn__tophole_keep; [ | exact Hprec ].
      apply guarded_pskl_to_bskl_inh, guarded_bskl_to_pskl.
      eapply ad_pat_consis_guarded_r;
        [ exact Hjoin' | exact Hwfth | reflexivity | exact Hgρ | ].
      eapply ad_refine_syn_f_lc_r; exact Hrs'.
    + destruct (IHc Hwf HwfP0' HwfP' Hrig Hnfd Hfaf
                   ρ1 ρ Θ Qt Qb Hid Hinc1 eq_refl Hinc Hwfth Hnfdc
                   Hjoin' Hrs' Hrp')
        as [ζ [Hζ [Hie Hprec]]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      unfold ad_precise in *. simpl.
      apply ad_refine_syn__tophole_remove. exact Hprec.
  - admit. (* TODO[optimality]: C-UnivGhost1; STRUCTURAL, Δ1 GROWS by α; glue; as
              C-ForallInh (no_flex_dep-on-Θ now in the motive). *)
  - (* C-UnivGhost2.  The guarded input refinement makes the competing target
       guarded, so both the join and the subject refinement must drop the
       universal-ghost wrapper before applying the sub-IH. *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P Q Hg0 Hnf Hc IHc.
    unfold consis_optimal_post in *.
    intros Hwf HwfP0 HwfP Hrig Hnfd Hfaf ρ1 ρ Θ Qt Qb
           Hid Hinc1 HeqQt Hinc Hwfth Hnfdc Hjoin Hrs Hrp.
    assert (Hg : guarded_pskl P) by (inversion HwfP; assumption).
    assert (HwfP' : Θ0 ⨟ empty ⊢ₚₛᵃ P) by (inversion HwfP; assumption).
    assert (Hg0ρ : guarded_pskl (msubst_pskl ρ P0))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (Hgρ : guarded_pskl (msubst_pskl ρ P))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (HgQb : guarded_bskl Qb).
    { eapply ad_refine_syn_f_guarded_r;
        [ exact Hwfth | exact Hrs | ].
      apply guarded_pskl_to_bskl_inh. exact Hg0ρ. }
    change (empty ⨟ Θ ⊨ₛᵃ
              (uskl_tophole (pskl_to_uskl (msubst_pskl ρ P))) ≈ Qb) in Hjoin.
    assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρ P)) ≈ Qb)
      by (eapply ad_pat_consis_tophole_guarded_inv; eauto).
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl ρ P)) (bskl_to_pskl Qb)) in Hrp.
    assert (Hrp' : ad_refine_pskl_f Δ2 Θ Δ2
              (msubst_pskl ρ P) (bskl_to_pskl Qb)).
    { eapply ad_refine_pskl_f_tophole_guarded_inv; eauto.
      apply guarded_bskl_to_pskl. exact HgQb. }
    destruct (IHc Hwf HwfP0 HwfP' Hrig Hnfd Hfaf
                 ρ1 ρ Θ Qt Qb Hid Hinc1 HeqQt Hinc Hwfth Hnfdc
                 Hjoin' Hrs Hrp')
      as [ζ [Hζ [Hie Hprec]]].
    exists ζ. repeat split; assumption.
  - (* C-Flex : subjects α̂, β̂ equated by unification.  The competing join +
       Δ₁-refinement force [ρα̂ ≡ ρβ̂] (the bridge), feeding the unify sub-IH for
       the increment + factoring; the precision conjunct is [via_join]. *)
    intros F Δ1 Δ2 Θ0 Θ1 α β Hu IHu.
    unfold unify_optimal_post in IHu. unfold consis_optimal_post.
    intros Hwf HwfP0 HwfP Hrig Hnfd Hfaf ρ1 ρ Θ Qt Qb
           Hid Hinc1 HeqQt Hinc Hwfth Hnfdc Hjoin Hrs Hrp.
    destruct (a_unify_subjects_flex Hwf Hu) as [Hfα Hfβ].
    destruct a_assign_unify_consis_sound as [_ [Hsnd_u _]].
    destruct (Hsnd_u _ _ _ _ _ Hu Hwf) as [Hle [Hwf1 _]].
    assert (Hmα : mono_ptyp (msubst_lookup ρ α)) by (eapply a_inc_lookup_mono; exact Hinc).
    assert (Hmβ : mono_ptyp (msubst_lookup ρ β)) by (eapply a_inc_lookup_mono; exact Hinc).
    assert (Heqαβ : Θ ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β)).
    { eapply consis_refine_mono_tyequiv_gen with (Qt := Qb);
        [ exact Hwfth | exact Hmα | exact Hmβ | | ].
      - replace (msubst_pskl ρ (pskl_var_f α))
          with (ptyp_to_pskl (msubst_lookup ρ α)) in Hjoin by reflexivity.
        rewrite pskl_to_uskl_ptyp in Hjoin. exact Hjoin.
      - apply ad_refine_syn_f_forget in Hrs. exact Hrs. }
    destruct (IHu Hwf Hfα Hfβ ρ1 ρ Θ Hid Hinc1 Hinc Hwfth Heqαβ) as [ζ [Hζ Hie]].
    assert (Hbα1 : a_binds_tvar α Θ1).
    { eapply a_isub_binds_tvarish; [ exact Hle | ].
      destruct Hfα as [Hb | [τ Hb]];
        [ right; left | right; right; exists τ ]; exact Hb. }
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
    destruct Qt; simpl in HeqQt; try discriminate.
    inversion HeqQt; subst. clear HeqQt.
    eapply consis_precise_via_join;
      [ exact Hwfth | exact Hfα | exact Hinc | exact Hbα1 | exact Hζ
      | exact Hwf1 | exact Hie
      | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf | exact Hfα ]
      | apply msubst_lookup_id; exact Hid
      | exact Hjoin ].
  - admit. (* TODO[optimality]: C-FlexL; precision conjunct closes via
              consis_precise_via_join (subject α̂, as C-Flex) + a_binds_tvar α Θ1
              from the soundness bundle.  BLOCKED on the increment+factoring: the
              assign sub-IH (assign_optimal_post) demands its competing-join
              hypothesis  [uskl(ρP0) ≈ syn(ρα̂)]  which must be RECONSTRUCTED from
              this node's consis hyps (Hjoin: uskl(ρα̂)≈Qb ; Hrs: inh{ρP0}⊳Qb).
              That reconstruction needs a refine→consis bridge (only the mono
              direction [ad_pat_consis_refine_syn_f_mono] exists — it goes
              consis→refine) PLUS extraction of a monotype view of the assigned
              skeleton P0 (ρP0 mono because α̂ is flex_mono).  Real missing infra,
              not assembly. (2026-07-15) *)
  - admit. (* TODO[optimality]: C-FlexR; precision conjunct closes via
              consis_precise_via_refine (input α̂, off the competing Δ₁-refine).
              BLOCKED, same wall as C-FlexL: the assign sub-IH needs its
              competing-join  [uskl(ρP) ≈ syn(ρα̂)]  rebuilt from Hjoin/Hrs, which
              additionally requires TARGET transport of consistency along ρα̂ ≡ C
              (only SUBJECT transport [tyequiv_mono_consis_transport] exists).
              Real missing infra. (2026-07-15) *)
  - admit. (* TODO[optimality]: C-GhostR; axiom, Θ1=Θ0; opt_axiom_factor gives
              the increment+factoring (ζ:=ρ).  BLOCKED on precision
              [inh{ρP} ⊳ inh{bskl_to_pskl Qb}].  Unlike C-Ghost the SUBJECT P
              (not the input) drives it, and P may be POLYMORPHIC, so:
              (a) the mono join/refine recovery does not apply; and
              (b) the natural bridge [ad_refine_pskl → ad_precise] on Hrp FAILS —
                  ad_refine_pskl's hole rule [pskl_hole ⊳ Q] would need
                  [bskl_hole ⊳ inh{Q}] but ad_refine_syn's hole rule only yields
                  [bskl_hole ⊳ SYN{Q}]; the ∀-rule conversely forces inh on the
                  right.  Needs the full refine machinery (trans + a re-inherit
                  lemma), or a non-mono consis→refine bridge.  (2026-07-15) *)
  - (* C-UnivGhostR.  Here the subject is already guarded, so its competing
       join has a guarded target.  The tophole on the input refinement can
       therefore only be removed; the sub-IH then has exactly the outer goal. *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IHc.
    unfold consis_optimal_post in *.
    intros Hwf HwfP0 HwfP Hrig Hnfd Hfaf ρ1 ρ Θ Qt Qb
           Hid Hinc1 HeqQt Hinc Hwfth Hnfdc Hjoin Hrs Hrp.
    assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0) by (inversion HwfP0; assumption).
    assert (Hgρ : guarded_pskl (msubst_pskl ρ P))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (HlcQb : lc_bskl Qb) by (eapply ad_refine_syn_f_lc_r; eauto).
    assert (HgQb : guarded_bskl Qb)
      by (eapply ad_pat_consis_guarded_r; eauto; reflexivity).
    change (ad_refine_syn_f Δ1 Θ Δ1
              (bskl_tophole (pskl_to_bskl_inh (msubst_pskl ρ P0))) Qb) in Hrs.
    assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
              (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb)
      by (eapply ad_refine_syn_f_tophole_guarded_inv; eauto).
    destruct (IHc Hwf HwfP0' HwfP Hrig Hnfd Hfaf
                 ρ1 ρ Θ Qt Qb Hid Hinc1 HeqQt Hinc Hwfth Hnfdc
                 Hjoin Hrs' Hrp)
      as [ζ [Hζ [Hie Hprec]]].
    exists ζ. repeat split; assumption.
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
  forall ρ1, Θ0 ≤[ ρ1 ] Θ1 ->
  a_unify_optimal Θ0 α β ρ1 Θ1.
Proof.
  intros F Θ0 α β Θ1 Hu Hwf Hfa Hfb ρ1 Hinc1.
  unfold a_unify_optimal. intros Hid ρ Θ Hsol.
  destruct Hsol as [Hinc [Heq Hwfth]].
  destruct a_assign_unify_consis_optimal as [_ [Hunify _]].
  eapply (Hunify _ _ _ _ _ Hu); eauto.
Qed.

Lemma a_assign_optimal_thm : forall F Θ0 Ξ α P Θ1,
  a_assign F Θ0 Ξ α P Θ1 ->
  a_decls Ξ -> a_wf_aenv (Ξ ++ Θ0) -> (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
  dom Ξ [<=] ftvar_in_pskl P ->  (* pending decls all used in P; vacuous at the top-level Ξ=nil *)
  forall ρ1, (Ξ ++ Θ0) ≤[ ρ1 ] Θ1 ->
  a_assign_optimal Θ0 Ξ α P ρ1 Θ1.
Proof.
  intros F Θ0 Ξ α P Θ1 Ha Hdecl Hwf HwfP Hdomξ ρ1 Hinc1.
  unfold a_assign_optimal. intros Hid ρ Θ Hsol.
  destruct Hsol as [Hinc [Hjoin Hwfth]].
  destruct a_assign_unify_consis_optimal as [Hassign _].
  eapply (Hassign _ _ _ _ _ _ Ha); eauto.
Qed.
