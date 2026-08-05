(** RESOLUTION of the flexible-counterpart counterexample
    ([cex_p6_flex_counterpart.v], 2026-07-25).

    The counterexample machine-checks that the -var completeness lemmas
    ([lemma:complete-consistency-constraint-collection-solving-var] and its
    subtyping twin) are FALSE **as isolated statements**: with
      Θ0 = c~tvar, β̂~flex   κ = [β̂ ↦ unit→unit]   ψa = c → unit
      ρ = [c ↦ unit]         P_i = c → unit         P_0 = β̂   Q = unit → unit
    every premise holds, yet the conclusion precision fails.

    THIS FILE records why that isolated falsity is NOT a completeness problem
    — the bad configuration is not producible by a real algorithm run — and
    proves the load-bearing fact.

    ── Why the isolated lemma is false only for an unreachable κ ──

    The only solve rule that fires on [P_i = c→unit ∼ P_0 = β̂] is
    [SolE-FlexR] ([a_solve_eq__flex_r]): [nonflex{P} ⊢ P ∼ α̂ ⤳ α̂].  There is
    NO flex-SPLIT rule in constraint solving (fig:selected-look): [SolE-Arrow]
    needs both sides to be arrows, and [SolE-FlexR] solves the flexible
    counterpart directly to [β̂], kept whole.  (The [split[α̂][β̂→α1̂]] rule
    lives only in the inference/[⤳ᵐ] layer, which can introduce fresh
    flexibles via a context move; constraint solving cannot and need not.)

    So [P_a = β̂] and the conclusion needs [κβ̂ ⊑ᵖ ψa].  The cex forces
    [κβ̂ = unit→unit] while [ψa = c→unit].  But that κ is FORCED BY ρ, not
    free: the consistency premise is [ρ(ψa) = unit→unit ∼ Q] and the
    refinement is [inh{κβ̂} ⊳ Q] against the SAME Q; since a rigid [c] is not
    consistent with [unit], Q must be [unit→…] on the left, pinning
    [κβ̂ = unit→unit].  ρ having substituted [c ↦ unit] is exactly what strips
    the rigid [c] out of everything κ can see, while [ψa] (used only for the
    final precision) still carries [c].

    ── Why the decoupled configuration is unreachable ──

    A flexible counterpart opposite a rigid variable that ρ has substituted
    away requires the constraint collection to have emitted a RAW Θ0-flex
    payload opposite a compound (arrow) subject.  It never does: when the
    counterpart of a compound comparison is a flexible variable,
    [a_lookeq__flex_r] (LE-FlexR) FRESHENS it to a new [α1 ∈ Ξ].  The -var
    lemma therefore never sees the raw [β̂] at an arrow node — it sees the
    fresh [α1], which is the NON-var lemma's job (κ extends over Ξ and can
    assign [α1] the rigid [c], so precision holds).

    ── Why only the arrow case matters ──

    κ maps flexibles to MONOTYPES, whose only shapes are [unit], a
    (mono/rigid) variable, or an ARROW.  Refinement [inh{κP0} ⊳ Q] into a ∀
    or a ghost/∀◇ requires a ∀/∀◇/defined-flex source, which a monotype never
    is.  Hence P0 = flexible is IMPOSSIBLE in the ForallInh / ForallSyn /
    ghost cases; and at leaves ([unit] / rigid var) a flexible P0 is handled
    correctly ([SolE-Flex] / the [SolE-Var] special case).  The Arrow case is
    the only one whose flexible-P0 subcase is even reachable, and the
    freshening below is what keeps it off the reachable inputs.

    The two lemmas are Qed and axiom-free. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decorated.

Set Implicit Arguments.

(** THE ESTABLISHMENT.  A flexible-variable counterpart opposite a COMPOUND
    (arrow) subject is always FRESHENED by [LE-FlexR] to a new [α1 ∈ Ξ]: the
    constraint collection never emits a raw Θ0-flex payload at an arrow node.
    (Inversion leaves only [LE-Absent], excluded by [α ∈ ftv], and
    [LE-FlexR].) *)
Lemma a_lookeq_arrow_subject_flex_target_freshened :
  forall Θ α P1 P2 β Ξ 𝒞,
  a_lookeq Θ α (pskl_arrow P1 P2) (pskl_var_f β) Ξ 𝒞 ->
  α `in` ftvar_in_pskl (pskl_arrow P1 P2) ->
  exists α1, Ξ = (α1 ~ abind_flex_mono) ++ nil
         /\ 𝒞 = a_cstr_eq (pskl_var_f α1) :: nil.
Proof.
  intros Θ α P1 P2 β Ξ 𝒞 H Hin; inversion H; subst.
  - (* LE-Absent: α ∉ ftv, contradicts Hin *)
    simpl in *. fsetdec.
  - (* LE-FlexR: the freshened payload *)
    eexists; split; reflexivity.
Qed.

(** THE GENERAL DICHOTOMY.  For a flexible TARGET, either the payload is
    FRESHENED ([α1 ∈ Ξ]) or it is RAW — and a raw payload's subject is NEVER
    an arrow (it is a variable or a ∀◇-wrapped variable).  So a raw Θ0-flex
    payload can only sit opposite a LEAF, never a compound bearing a rigid
    ρ-substituted variable. *)
Lemma a_lookeq_flex_target_raw_subject_not_arrow :
  forall Θ α P β Ξ 𝒞,
  a_lookeq Θ α P (pskl_var_f β) Ξ 𝒞 ->
  α `in` ftvar_in_pskl P ->
  (exists α1, α1 `in` dom Ξ /\ 𝒞 = a_cstr_eq (pskl_var_f α1) :: nil)
  \/
  (Ξ = nil /\ 𝒞 = a_cstr_eq (pskl_var_f β) :: nil
   /\ forall Q1 Q2, P <> pskl_arrow Q1 Q2).
Proof.
  intros Θ α P β Ξ 𝒞 H.
  remember (pskl_var_f β) as tgt eqn:Htgt.
  induction H; intros Hin; try discriminate Htgt.
  - (* LE-Var: subject = var α, raw payload P = var β *)
    right. inversion Htgt; subst. repeat split; try reflexivity.
    intros Q1 Q2; discriminate.
  - (* LE-Absent: α ∉ ftv, contradiction *)
    simpl in Hin. exfalso. fsetdec.
  - (* LE-FlexR: freshened *)
    left. inversion Htgt; subst. eexists; split; [ | reflexivity ].
    simpl. fsetdec.
  - (* LE-UnivGhost2: subject = ∀◇, recurse — stays non-arrow *)
    simpl in Hin. specialize (IHa_lookeq Htgt Hin).
    destruct IHa_lookeq as [Hfresh | Hraw].
    + left; assumption.
    + right. destruct Hraw as [HΞ [HC _]].
      repeat split; try assumption.
      intros Q1 Q2; discriminate.
Qed.
