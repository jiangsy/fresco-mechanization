(** Soundness of the DECORATED algorithmic judgements w.r.t. the declarative
    skeleton judgements — the paper's [\wenhao{TODO}] step
    ([subtyping-proofs.tex:1047]).

    Mechanise the soundness STATEMENTS and check the paper's reasoning by
    attempting the structural proof.  The decorated source [S : uskl] is the
    declarative LHS; the solved-tag list [Ψ] is the declarative tag context
    [Δ] (F16 resolved: [Ψ : list atom]); [⌊Θ1⌋] is [Γ].

    Reasoning-check findings surfaced while discharging cases:

    - F15: algo consistency [GhostR]/[UnivGhostR] have NO declarative rule
      (paper: "Decl does not have this case", alg.tex:1662/1671).
    - F17 (RHS COLOUR): the declarative RHS is a COLOURED [bskl] whose ∀-colour
      is derivation-dependent — the SAME source [uskl_all_etag] maps to
      [bskl_all_inh] (via [forall_inh_tagged]) or [bskl_all_syn] (via
      [forall_syn_tagged]).  The algo output [Q : pskl] is uncoloured, so the
      RHS CANNOT be a uniform [pskl_to_bskl_syn Q]; the [bskl] must be
      synthesised by the derivation.  The statement below uses
      [pskl_to_bskl_syn Q] as a PLACEHOLDER — correct only for the colour-free
      / syn cases; the inherited-∀ cases ([ForallInh], [tophole_inh]) are
      provably off and admitted with this note.
    - F18 (CONTEXT THREADING): the algo threads an evolving output context
      ([Θ0 → Θ1 → Θ2] in [Arrow]) whereas [d_pat_consis] uses a single fixed
      [Γ]; soundness of the binary rules needs a stability/projection argument
      ([⌊Θ1⌋] and [⌊Θ2⌋] agree on the relevant part) — the admitted
      [a_stable_*] lemmas. *)

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

(* ===================================================================== *)
(*  Soundness of decorated consistency  (paper soundness, \wenhao{TODO}). *)
(* ===================================================================== *)
Theorem a_consistag_sound : forall P0 Ψ Θ0 S Q Θ1,
    a_consistag P0 Ψ Θ0 S Q Θ1 ->
    d_pat_consis Ψ (aenv_to_denv Θ1) S (pskl_to_bskl_syn Q).
Proof.
  intros P0 Ψ Θ0 S Q Θ1 H. induction H.
  - (* GhostG → d_pat_consis__ghostg.  Colour-free, no threading: closes. *)
    simpl. apply d_pat_consis__ghostg.
  - (* Arrow → d_pat_consis__arrow.  F18: IH1 is under ⌊Θ1⌋, IH2 under ⌊Θ2⌋,
       but d_pat_consis__arrow needs ONE Γ — needs stability ⌊Θ1⌋↦⌊Θ2⌋. *)
    admit.
  - (* ForallInh → d_pat_consis__forall_inh_tagged.  F17: decl RHS is
       [bskl_all_inh], but the statement paints [pskl_all_syn Q] to
       [bskl_all_syn].  Provably off — needs colour-aware RHS. *)
    admit.
  - (* ForallSyn → d_pat_consis__forall_syn_tagged.  RHS [bskl_all_syn] —
       colour matches; binder + cofinite to discharge. *)
    admit.
  - (* UnivGhost → d_pat_consis__tophole. *)
    admit.
  - (* UnivGhostG → d_pat_consis__topholeg. *)
    admit.
  - (* UnivGhost1 → d_pat_consis__tophole_inh.  F17: RHS [bskl_all_inh]. *)
    admit.
  - (* UnivGhost2 → d_pat_consis__tophole_drop. *)
    admit.
  - (* GhostR → ??? F15: no declarative rule. *)
    admit.
  - (* UnivGhostR → ??? F15: no declarative rule. *)
    admit.
Admitted.

(* ===================================================================== *)
(*  Soundness of decorated subtyping  (paper soundness, \wenhao{TODO}).    *)
(* ===================================================================== *)
Theorem a_subtag_sound : forall NM M P0 Ψ Θ0 S Q Θ1,
    a_subtag NM M P0 Ψ Θ0 S Q Θ1 ->
    d_pat_sub M Ψ (aenv_to_denv Θ1) S (pskl_to_bskl_syn Q).
Proof.
  intros NM M P0 Ψ Θ0 S Q Θ1 H. induction H.
  - (* Check → via a_consistag_sound. *)
    admit.
  - (* ForallR → forall-on-right; output suffix Ξ dropped (F18-like). *)
    admit.
  - (* UnivGhostR → d_pat_sub__univ_ghost_r. *)
    admit.
  - (* Arrow → d_pat_sub__arg + a_consistag_sound on the domain (F18). *)
    admit.
  - (* ForallL → d_pat_sub__forall_l_*; blocked on a_tag_support placeholder
       and the Ψ++Ψg ↔ decl ε-tag bookkeeping. *)
    admit.
  - (* GhostG → d_pat_sub__ghostg. *)
    admit.
  - (* UnivGhostL → d_pat_sub__univ_ghost_l. *)
    admit.
  - (* UnivGhostLG → d_pat_sub__univ_ghost_lg. *)
    admit.
Admitted.
