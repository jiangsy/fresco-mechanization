(** PROBE (2026-08-16): the §8c.9 b-CORE, stated over TWO ARBITRARY
    supply-threaded look derivations, is FALSE — the pair induction's
    side 2 must be THE RUNNER's computation, not an arbitrary
    [e_lookeq]/[e_looksub] derivation.
    (docs/HANDOFF-extractable-algo-encoding.md §8c.9, fourth pass.)

    THE MISSED OVERLAP.  [guarded_pskl] includes VARIABLES
    (frost/def_shapes.v), so at a node

        ⫯(α)  ∼[α]  β                (subject ⫯(var α), target var β)

    BOTH [LE-FlexR] (subject ≠ α, α occurs, var target) and
    [LE-UnivGhost2] (⫯ subject, guarded target) fire.  §8c.9's crossing
    inventory checked FlexR×Var ("excluded by P ≠ α") but not
    FlexR×UnivGhost2.  The two roots' collections DISAGREE in kind:

        FlexR         Ξ = (α̂1 ~ flex)   𝒞 = [eq α̂1]     (fresh FLEXIBLE)
        UG2 ∘ Var     Ξ = nil           𝒞 = [eq β]      (the RAW target)

    and the divergence is fatal for the fused fold-transport: with the
    accumulated pattern [1] and β RIGID, the FlexR-side fold SUCCEEDS
    (SE-FlexR guesses the pattern into the fresh flexible) while the
    UG2-side fold is STUCK ([1 ∼ β] with β rigid matches no solve rule).
    All of the b-core's designed side conditions (rel-related inputs,
    flex-agreement, binds/supply-interval invariants, scopings,
    coverage) are satisfiable around this pair — [probe_bcore_fold1_ok]
    + [probe_bcore_fold2_stuck] below exhibit the fold halves — so no
    motive over two ARBITRARY e-derivations can conclude "the second
    fold exists".

    WHAT IS MACHINE-CHECKED HERE:
      (1) [probe_bcore_flexr_route]   — the FlexR derivation;
      (2) [probe_bcore_ug2_route]     — the UG2∘Var derivation of the
                                        SAME instance (same supply);
      (3) [probe_bcore_fold1_ok]      — the FlexR-side fold succeeds at
                                        pattern [1], β rigid;
      (4) [probe_bcore_fold2_stuck]   — the UG2-side fold has NO
                                        derivation there.

    CONSEQUENCE (the design pivot, argued in the handoff): the b-core's
    side 2 is stated as the RUNNER's computation
    ([e_lookeq_impl]/[e_looksub_impl] returning [Some]).  The runner
    always takes FlexR at a (⫯, var) node (def_look_impl.v, the
    ⫯-subject/var-target clause), so the fatal orientation
    (FlexR on side 1, UG2∘Var on side 2) cannot arise — and the
    surviving orientation (UG2∘Var on side 1, FlexR on side 2) is
    transportable: side 2's target is a FRESH UNDEFINED FLEXIBLE, so
    the head solve always exists, at worst diverging to a VAR yield on
    both sides (the "hatch" of the eq-level motive; a var pattern is a
    fixed point of the whole fold, so the divergence is harmless). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_look.

Open Scope frost_a_scope.
Open Scope frost_e_scope.

(** The subject: ⫯(α).  Both routes look for α in it. *)
Definition probe_subj (α : atom) : pskl := pskl_tophole (pskl_var_f α).

(** (1) The FlexR route: the raw target is replaced by a fresh flexible. *)
Lemma probe_bcore_flexr_route : forall (S : supply) Θ α β α1,
  α1 `notin` S ->
  {{ S ↝ (add α1 S) ⊨ Θ ⊢ (probe_subj α) ∼[ α ] (pskl_var_f β)
     ⤳ ((α1 ~ abind_flex_mono) ++ nil)
     ⨾ (a_cstr_eq (pskl_var_f α1) :: nil) }}e.
Proof.
  intros * Hα1. unfold probe_subj.
  apply e_lookeq__flex_r.
  - exact Hα1.
  - discriminate.
  - simpl. fsetdec.
Qed.

(** (2) The UG2∘Var route of the SAME instance: the raw target is KEPT
    (a variable is [guarded_pskl], so LE-UnivGhost2 fires). *)
Lemma probe_bcore_ug2_route : forall (S : supply) Θ α β,
  {{ S ↝ S ⊨ Θ ⊢ (probe_subj α) ∼[ α ] (pskl_var_f β)
     ⤳ nil ⨾ (a_cstr_eq (pskl_var_f β) :: nil) }}e.
Proof.
  intros. unfold probe_subj.
  apply e_lookeq__univ_ghost2.
  - apply guarded_pskl__var.
  - apply e_lookeq__var.
Qed.

(** The two fold contexts: side 1 sees its fresh flexible; on BOTH sides
    β is RIGID. *)
Definition probe_ctx1 (α1 β : atom) : aenv :=
  (α1 ~ abind_flex_mono) ++ (β ~ abind_tvar) ++ nil.
Definition probe_ctx2 (β : atom) : aenv :=
  (β ~ abind_tvar) ++ nil.

(** (3) The FlexR-side fold succeeds at the pattern [1]: SE-FlexR hands
    the pattern through [guess^TY]. *)
Lemma probe_bcore_fold1_ok : forall α1 β,
  {{ (probe_ctx1 α1 β) ⊩ (a_cstr_eq (pskl_var_f α1) :: nil)
     ⨾ pskl_unit ⤳ (nil ++ nil) ⨾ pskl_unit }}a.
Proof.
  intros. unfold probe_ctx1.
  apply a_solve_cstr__eq with (P'' := pskl_unit).
  - replace pskl_unit with (ptyp_to_pskl ptyp_unit) at 2 by reflexivity.
    apply a_solve_eq__flex_r.
    + left. auto.
    + split; [ apply lc_pskl_unit | ].
      intros Hf; inversion Hf.
    + apply nonghost_pskl__unit.
    + apply a_guess_mono__unit.
  - apply a_solve_cstr__empty.
Qed.

(** (4) The UG2-side fold is STUCK: [1 ∼ β] with β rigid matches no
    solve rule (SE-Unit needs a unit target, SE-FlexR a FLEXIBLE one). *)
Lemma probe_bcore_fold2_stuck : forall β Ξ Q,
  ~ {{ (probe_ctx2 β) ⊩ (a_cstr_eq (pskl_var_f β) :: nil)
       ⨾ pskl_unit ⤳ Ξ ⨾ Q }}a.
Proof.
  intros * Hd. inversion Hd; subst.
  match goal with
  | He : a_solve_eq _ pskl_unit (pskl_var_f β) _ _ |- _ =>
      inversion He; subst
  end.
  (* only SE-FlexR shape-matches, and it demands β flexible *)
  match goal with
  | Hf : a_flex_tvar (probe_ctx2 β) β |- _ =>
      destruct Hf as [Hb | [τ Hb]]; unfold probe_ctx2, binds in Hb;
      simpl in Hb;
      (destruct Hb as [Hb | Hb]; [ inversion Hb | exact Hb ])
  end.
Qed.
