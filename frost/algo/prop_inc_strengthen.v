(** Increment strengthening / mid-strip infrastructure for the OPTIMALITY
    walk cases (algo/prop_consis_complete.v, Blocker-2).

    The assign walk sandwiches the skipped binding as [Ξ ++ [β] ++ Θ0]
    (unlike Flex-Flex-Skip's clean head-flex).  [a_inc_peel_suffix] only peels
    an all-flex suffix; here we need to peel the suffix AND the mid flex binding
    together, then RE-INSERT the suffix over the smaller tail — producing the
    sub-node's competing increment [(Ξ ++ Θ0) ≤[ρ1 ++ ρ2] Θ].

    The suffix here is [a_decls Ξ] (every entry an UNDEFINED flexible), the
    algorithm's own invariant on the pending suffix (full-algo-spec.tex:1508).
    That is what keeps the re-insertion clean: with no [flex_mono_def] entry in
    Ξ there is no definition whose image depends on the dropped [β], so the
    reconstructed increment's premises transport unchanged.  (With a general
    [a_suffix] Ξ a def entry [a ≔ τd] could have [β ∈ ftv τd], and dropping
    β's metasubst entry would change [msubst τd] — the flex_def premise
    [τa' ≡ᵗ msubst (ρ1++ρ2) τd] would then be false.) *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_compose.

Set Implicit Arguments.

(** MID-STRIP of a flexible binding sandwiched under an [a_decls] suffix.
    Peels the suffix Ξ and the mid flex [β] off a competing increment
    [(Ξ ++ β̂ ++ Θ0) ≤[ρ] Θ], returning
      - the split [ρ = ρ1 ++ (β,τ) :: ρ2] (ρ1 = the Ξ-part, dom ρ1 = dom Ξ),
      - the tail increment [Θ0 ≤[ρ2] Θ], and
      - the RE-INSERTED increment [(Ξ ++ Θ0) ≤[ρ1 ++ ρ2] Θ] with β dropped.
    The target [Θ] is UNCHANGED (flex/suffix entries do not extend it). *)
Lemma a_inc_mid_strip_flex : forall Ξ β Θ0 ρ Θ,
  a_decls Ξ ->
  (Ξ ++ (β ~ abind_flex_mono) ++ Θ0) ≤[ ρ ] Θ ->
  exists ρ1 τ ρ2,
    ρ = ρ1 ++ (β, τ) :: ρ2 /\
    dom ρ1 [=] dom Ξ /\
    Θ0 ≤[ ρ2 ] Θ /\
    (Ξ ++ Θ0) ≤[ ρ1 ++ ρ2 ] Θ.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros β Θ0 ρ Θ Hdec Hinc.
  - (* Ξ = nil : head is the mid flex β itself *)
    simpl in Hinc.
    inversion Hinc as [ | Θs ρs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqρ] Heqt
                      | | | | ]; subst.
    exists (@nil (atom * ptyp)), τ, ρs. simpl.
    split; [ reflexivity | ].
    split; [ clear; fsetdec | ].
    split; [ exact Hinc' | exact Hinc' ].
  - (* Ξ = (a ~ flex) ++ Ξ' : peel the head flex a, recurse *)
    inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs ρs Θt as' τ Hinc' Hwfτ Hmτ [Heqa Heqρ] Heqt
                      | | | | ]; subst.
    destruct (IH _ _ _ _ Hdec' Hinc')
      as [ρ1 [τ2 [ρ2 [Heqρ [Hdom [Hinc2 Hrec]]]]]].
    exists ((a, τ) :: ρ1), τ2, ρ2. simpl.
    split; [ rewrite Heqρ; reflexivity | ].
    split; [ clear - Hdom; simpl_env; fsetdec | ].
    split; [ exact Hinc2 | ].
    apply a_inc__flex; auto.
Qed.
