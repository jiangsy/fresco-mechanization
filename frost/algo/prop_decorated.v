(** Soundness of the DECORATED algorithmic judgements w.r.t. the declarative
    skeleton judgements — the paper's [\wenhao{TODO}] step
    ([subtyping-proofs.tex:1047], "Now we prove soundness of subtyping").

    GOAL HERE: mechanise the soundness STATEMENTS and check the paper's
    reasoning by attempting the structural proof.  Local admits are expected.

    A decorated derivation [a_consistag P0 Ψ Θ0 S Q Θ1] should map to the
    declarative skeleton consistency [Δ ⨟ Γ ⊨ₛ R ≈ Q'] with: the decorated
    source [S : uskl] as the declarative LHS [R]; the solved-tag set [Ψ] as the
    declarative tag context [Δ]; the projected context [⌊Θ1⌋] as [Γ]; and the
    syn-painted output [pskl_to_bskl_syn Q] as the declarative RHS [Q']
    (matching the existing [a_consis_solution] reading in [def_question.v]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.def_ott.
Require Import src.frost.prop_ln.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.

Set Implicit Arguments.

(* Tag context conversion (FINDING F16): the decorated judgements carry the
   tag context as a SET [Ψ : atoms], but [d_pat_consis]/[d_pat_sub] carry it as
   a [list atom].  We convert with [AtomSetImpl.elements]; a faithful treatment
   would unify the two representations (the declarative type-level [d_consis]
   already uses [atoms]; the skeleton-level [d_pat_*] still uses [list atom]). *)
Definition Ψ_to_Δ (Ψ : atoms) : list atom := AtomSetImpl.elements Ψ.

(* ===================================================================== *)
(*  Soundness of decorated consistency  (paper soundness, \wenhao{TODO}). *)
(* ===================================================================== *)
Theorem a_consistag_sound : forall P0 Ψ Θ0 S Q Θ1,
    a_consistag P0 Ψ Θ0 S Q Θ1 ->
    d_pat_consis (Ψ_to_Δ Ψ) (aenv_to_denv Θ1) S (pskl_to_bskl_syn Q).
Proof.
  intros P0 Ψ Θ0 S Q Θ1 H. induction H.
  - (* GhostG → d_pat_consis__ghostg.  Δ = ∅ ↦ elements ∅ = nil. *)
    admit.
  - (* Arrow → d_pat_consis__arrow.  FINDING F16': decl splits Δ1,Δ2 (list
       append, disjoint), algo unions Ψ1∪Ψ2 (set).  Soundness needs
       elements(Ψ1∪Ψ2) to relate to (elements Ψ1 ++ elements Ψ2) up to the
       disjointness the decl arrow rule demands. *)
    admit.
  - (* ForallInh → d_pat_consis__forall_inh_tagged.  Tag δ collected
       (Ψ∪{δ}) ↔ decl's ε-tagged ∀.  Plausibly aligned. *)
    admit.
  - (* ForallSyn → d_pat_consis__forall_syn. *)
    admit.
  - (* UnivGhost → d_pat_consis__tophole. *)
    admit.
  - (* UnivGhostG → d_pat_consis__topholeg. *)
    admit.
  - (* UnivGhost1 → d_pat_consis__tophole_inh. *)
    admit.
  - (* UnivGhost2 → d_pat_consis__tophole_drop. *)
    admit.
  - (* GhostR → ??? FINDING F15: the algo GhostR rule ([□] expected, output
       ⌊S⌋) has NO declarative counterpart — the paper itself comments
       "WT: Decl does not have this case" (algorithmic.tex:1662).  Its
       soundness cannot be a 1-1 rule map; needs either a derived declarative
       argument or a new declarative rule.  GENUINE PAPER-REASONING GAP. *)
    admit.
  - (* UnivGhostR → ??? FINDING F15 (cont.): likewise no declarative
       counterpart (algorithmic.tex:1671 "Decl does not have this case"). *)
    admit.
Admitted.

(* ===================================================================== *)
(*  Soundness of decorated subtyping  (paper soundness, \wenhao{TODO}).    *)
(* ===================================================================== *)
Theorem a_subtag_sound : forall NM M P0 Ψ Θ0 S Q Θ1,
    a_subtag NM M P0 Ψ Θ0 S Q Θ1 ->
    d_pat_sub M (Ψ_to_Δ Ψ) (aenv_to_denv Θ1) S (pskl_to_bskl_syn Q).
Proof.
  intros NM M P0 Ψ Θ0 S Q Θ1 H. induction H.
  - (* Check → d_pat_sub__infer/check via a_consistag_sound. *)
    admit.
  - (* ForallR → d_pat_sub forall-on-right; output suffix Ξ dropped. *)
    admit.
  - (* UnivGhostR → d_pat_sub__univ_ghost_r (fills the universal ghost). *)
    admit.
  - (* Arrow → d_pat_sub__arg: consistency on the domain (a_consistag_sound)
       + IH on the codomain.  Same set-vs-list tag-context concern (F16). *)
    admit.
  - (* ForallL → d_pat_sub__forall_l_{tagged,untagged}: instantiation via the
       extracted P1.  Depends on the a_tag_support PLACEHOLDER and the extract
       (a_extract) — the hardest case; the tag bookkeeping Ψ∪Ψg ↔ the decl
       ε-tag must line up.  Cannot be checked until a_tag_support is real. *)
    admit.
  - (* GhostG → d_pat_sub__ghostg. *)
    admit.
  - (* UnivGhostL → d_pat_sub__univ_ghost_l. *)
    admit.
  - (* UnivGhostLG → d_pat_sub__univ_ghost_lg. *)
    admit.
Admitted.
