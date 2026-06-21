(** Soundness of the DECORATED algorithmic judgements w.r.t. the declarative
    skeleton judgements — the paper's [\wenhao{TODO}] step
    ([subtyping-proofs.tex:1047]).

    Mechanise the soundness STATEMENTS (using the algo notations) and check the
    paper's reasoning by attempting the structural proof.  The decorated source
    [S : uskl] is the declarative LHS; the solved-tag SET [Ψ : atoms] is the
    declarative tag context [Δ] (converted via [AtomSetImpl.elements] until the
    [d_pat→atoms] refactor, F16); [⌊Θ1⌋] is [Γ].

    Reasoning-check findings (admitted cases, documented inline):
    - F15: algo [GhostR]/[UnivGhostR] have NO declarative rule
      (paper: "Decl does not have this case", alg.tex:1662/1671).
    - F17 (RHS colour): the declarative RHS [bskl] has a derivation-dependent
      ∀-colour — same source [uskl_all_etag] ↦ [bskl_all_inh] OR [bskl_all_syn].
      The algo output [Q : pskl] is uncoloured, so the RHS cannot be a uniform
      [pskl_to_bskl_syn Q]; the [bskl] must be synthesised by the derivation.
      Affects the inherited-∀ cases.
    - F18 (context threading): the algo threads [Θ0→Θ1→Θ2] (Arrow) whereas
      [d_pat_consis] uses one fixed [Γ]; binary-rule soundness needs a
      stability argument (the admitted [a_stable_*]). *)

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

(* Tag context bridge (F16): decorated [Ψ : atoms] ↦ declarative [Δ : list]. *)
Definition Ψtoδ (Ψ : atoms) : list atom := AtomSetImpl.elements Ψ.

(* ===================================================================== *)
(*  Soundness of decorated consistency  (paper soundness, \wenhao{TODO}). *)
(* ===================================================================== *)
Theorem a_consistag_sound : forall P0 Ψ Θ0 S Q Θ1,
    Θ0 ⊢ᶜ[ P0 | Ψ ] S ⤳ Q ⊣ Θ1 ->
    (Ψtoδ Ψ) ⨟ ⌊ Θ1 ⌋ ⊨ₛ S ≈ (pskl_to_bskl_syn Q).
Proof.
  intros P0 Ψ Θ0 S Q Θ1 H. induction H.
  - (* GhostG → d_pat_consis__ghostg.  Needs elements ∅ = nil. *)
    admit.
  - (* Arrow → d_pat_consis__arrow.  F18 (Γ threading) + F16 (elements of a
       union vs append). *)
    admit.
  - (* ForallInh → d_pat_consis__forall_inh_tagged.  F17: RHS bskl_all_inh. *)
    admit.
  - (* ForallSyn → d_pat_consis__forall_syn_tagged. *)
    admit.
  - (* UnivGhost → d_pat_consis__tophole.  Unary, colour-free: closes. *)
    simpl. apply d_pat_consis__tophole. assumption.
  - (* UnivGhostG → d_pat_consis__topholeg.  Closes. *)
    simpl. apply d_pat_consis__topholeg. assumption.
  - (* UnivGhost1 → d_pat_consis__tophole_inh.  F17: RHS bskl_all_inh. *)
    admit.
  - (* UnivGhost2 → d_pat_consis__tophole_drop.  Closes. *)
    apply d_pat_consis__tophole_drop. assumption.
  - (* GhostR → ??? F15: no declarative rule. *)
    admit.
  - (* UnivGhostR → ??? F15: no declarative rule. *)
    admit.
Admitted.

(* ===================================================================== *)
(*  Soundness of decorated subtyping  (paper soundness, \wenhao{TODO}).    *)
(* ===================================================================== *)
Theorem a_subtag_sound : forall NM M P0 Ψ Θ0 S Q Θ1,
    Θ0 ⊢ˢ[ NM | M | P0 | Ψ ] S ⤳ Q ⊣ Θ1 ->
    (Ψtoδ Ψ) ⨟ ⌊ Θ1 ⌋ ⊢ₛ[ M ] S ⊑ (pskl_to_bskl_syn Q).
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
  - (* ForallL → d_pat_sub__forall_l_*; blocked on a_tag_support placeholder. *)
    admit.
  - (* GhostG → d_pat_sub__ghostg. *)
    admit.
  - (* UnivGhostL → d_pat_sub__univ_ghost_l. *)
    admit.
  - (* UnivGhostLG → d_pat_sub__univ_ghost_lg. *)
    admit.
Admitted.
