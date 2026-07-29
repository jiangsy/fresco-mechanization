(** P6-L — COMPLETENESS OF LOOK  [a_extract_complete]
    (paper [lemma:complete-look], subtyping-proofs.tex:2730).

    [a_extract] has ONE rule, so P6-L's shape is fixed:

      P ≼[α,m] P' ⤳ Ξ ⨾ 𝒞  →  (Ξ ++ Θ0) ⊩ 𝒞 ⨾ □ ⤳ Q  →  guess^N(Q) = (Ξ';Q')
        →  Θ0 ⊢ P ⊳[N,α,m] P' ⤳ (Ξ ++ Ξ') ↪ Q'

    Premises 1-2 are P6-Ss ([a_looksub_solve_complete]) instantiated at
    [Pi := pskl_hole] and [Ψi := empty], so [Ψ' = Ψa]; then
    [ad_partial_precise_complete] (P5b-i) upgrades the ⊑ᵖ[Ψa] output to plain
    ⊑ against [⌊ψa⌋ˢ], exactly as the paper does at tex:2764.

    THE WORK IS THE THIRD PREMISE — the paper's one-line "by induction on the
    definition of guess^N(P_s)", which must produce a metasubstitution
    EXTENSION κ' over the guessed flexibles Ξ' with four conclusions at once
    (wf, [a_inc], [a_inc_equiv], precision).  Two observations shape it:

    - **We CHOOSE the guess.**  P6-L's conclusion is existential in Ξ and the
      extract's output, so the induction may build [a_guess_mono] and κ'
      SIMULTANEOUSLY rather than consuming a given guess.
    - **[guess_join_witness] (prop_consis_complete.v:4624) does NOT serve
      here**, though DESIGN §7's table said so: it is CONSISTENCY-driven and
      demands a MONOTYPE counterpart, whereas guess^TY passes ∀ through
      ([a_guess_mono__forall] returns a [ptyp_all]) and P6-L's counterpart
      [⌊ψa⌋ˢ] is a general ghost-free skeleton.  See DESIGN §7.3.

    At [N = SK] the guess is the identity ([a_guess__sk]: Ξ' = ·, Q' = Q), so
    κ' = · and every conclusion is P6-Ss's verbatim.  This file builds the
    TY side. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  WHERE A HOLE FACES THE COUNTERPART, THE COUNTERPART IS A MONOTYPE  *)
(*                                                                        *)
(*  guess^TY replaces each ◇ of the solve output by a FRESH flexible, and  *)
(*  the θ-extension must send that flexible to the counterpart's skeleton  *)
(*  AT THAT POSITION — so the position had better hold a monotype, since   *)
(*  a metasubstitution's images are monotypes.  It does, and the reason is *)
(*  purely the PAINTING: [ad_refine_syn__hole] demands a SYNTHESISED       *)
(*  target, precision hands it an INHERITED one, and the two paintings     *)
(*  agree exactly on ∀-free skeletons ([pskl_all_syn] is the ONE           *)
(*  constructor where they differ — [bskl_all_inh] vs [bskl_all_syn]).     *)
(*                                                                        *)
(*  This is the mechanical content of the paper's side remark at tex:2812 — *)
(*  for each quantifier in the erased ψa, premise (f) ensures it does not   *)
(*  correspond to a universal ghost in P_s.                                *)
(* ===================================================================== *)

(** ∀-freeness, the exact condition under which the two paintings agree. *)
Inductive pskl_all_free : pskl -> Prop :=
| paf_unit   : pskl_all_free pskl_unit
| paf_var_b  : forall n, pskl_all_free (pskl_var_b n)
| paf_var_f  : forall α, pskl_all_free (pskl_var_f α)
| paf_arrow  : forall P1 P2,
    pskl_all_free P1 -> pskl_all_free P2 -> pskl_all_free (pskl_arrow P1 P2)
| paf_hole   : pskl_all_free pskl_hole
| paf_tophole : forall P, pskl_all_free P -> pskl_all_free (pskl_tophole P).

#[export] Hint Constructors pskl_all_free : frost.

(** The two paintings agree EXACTLY on the ∀-free skeletons, and where they
    agree they agree on the same skeleton. *)
Lemma pskl_inh_eq_syn_inv : forall P Q,
  pskl_to_bskl_inh P = pskl_to_bskl_syn Q ->
  P = Q /\ pskl_all_free P.
Proof.
  induction P; intros Q Heq; destruct Q; cbn in Heq; try discriminate Heq.
  - split; [ reflexivity | apply paf_unit ].
  - injection Heq as ->. split; [ reflexivity | apply paf_var_b ].
  - injection Heq as ->. split; [ reflexivity | apply paf_var_f ].
  - injection Heq as Heq1 Heq2.
    destruct (IHP1 _ Heq1) as [-> Hf1]. destruct (IHP2 _ Heq2) as [-> Hf2].
    split; [ reflexivity | apply paf_arrow; assumption ].
  (* NB no ∀ bullet: [bskl_all_inh] vs [bskl_all_syn] IS discriminable, so
     [try discriminate Heq] above already closed that diagonal case — that
     disagreement is exactly what this lemma is about *)
  - split; [ reflexivity | apply paf_hole ].
  - injection Heq as Heq0. destruct (IHP _ Heq0) as [-> Hf].
    split; [ reflexivity | apply paf_tophole; assumption ].
Qed.

(** …and a ∀-free, GHOST-free skeleton IS a monotype painting.  Ghost-freeness
    is what [a_tags_sort] at TY supplies for ψa ([uskl_ghost_free]), so
    [⌊ψa⌋ˢ] has no ◇ / ∀◇ to obstruct this. *)
Inductive pskl_ghost_free : pskl -> Prop :=
| pgf_unit  : pskl_ghost_free pskl_unit
| pgf_var_b : forall n, pskl_ghost_free (pskl_var_b n)
| pgf_var_f : forall α, pskl_ghost_free (pskl_var_f α)
| pgf_arrow : forall P1 P2,
    pskl_ghost_free P1 -> pskl_ghost_free P2 ->
    pskl_ghost_free (pskl_arrow P1 P2)
| pgf_all   : forall P, pskl_ghost_free P -> pskl_ghost_free (pskl_all_syn P).

#[export] Hint Constructors pskl_ghost_free : frost.

Lemma pskl_all_ghost_free_mono : forall P,
  pskl_all_free P -> pskl_ghost_free P -> lc_pskl P ->
  exists τ, ptyp_to_pskl τ = P /\ mono_ptyp τ.
Proof.
  intros P Ha; induction Ha; intros Hg Hlc; try solve [ inversion Hg ].
  - exists ptyp_unit; split; [ reflexivity | apply mono_ptyp__unit ].
  - (* a BOUND variable is ruled out by local closure, not by ghost-freeness *)
    inversion Hlc.
  - exists (ptyp_var_f α); split; [ reflexivity | apply mono_ptyp__var ].
  - inversion Hg; subst. inversion Hlc; subst.
    destruct (IHHa1 ltac:(assumption) ltac:(assumption)) as [τ1 [Heq1 Hm1]].
    destruct (IHHa2 ltac:(assumption) ltac:(assumption)) as [τ2 [Heq2 Hm2]].
    exists (ptyp_arrow τ1 τ2); cbn; rewrite Heq1, Heq2.
    split; [ reflexivity | apply mono_ptyp__arrow; assumption ].
Qed.
