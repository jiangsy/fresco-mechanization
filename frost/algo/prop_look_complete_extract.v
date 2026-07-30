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
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.

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

(* ===================================================================== *)
(*  §2  RENAMING THE GUESS                                                *)
(*                                                                        *)
(*  [a_guess_mono__forall] is COFINITE in the opener with a FIXED (Ξ; A):  *)
(*                                                                        *)
(*    (forall α ∉ L, guess (P^α) = (Ξ; A^α))  ⟹  guess (∀P) = (Ξ; ∀A)     *)
(*                                                                        *)
(*  so building a guess under a ∀ means building it at ONE fresh opener    *)
(*  and renaming into the family.  The guessed flexibles Ξ do NOT move —   *)
(*  they are fresh names invented by the hole rule, independent of the     *)
(*  binder — which is why the renaming must avoid [dom Ξ] on both sides.   *)
(* ===================================================================== *)

Lemma a_guess_mono_rename_tvar : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A ->
  forall β γ, β `notin` dom Ξ -> γ `notin` dom Ξ ->
  a_guess_mono Θ (subst_pskl_in_pskl (pskl_var_f γ) β P) Ξ
                 (subst_ptyp_in_ptyp (ptyp_var_f γ) β A).
Proof.
  intros Θ P Ξ A H; induction H; intros β γ Hβ Hγ; cbn.
  - (* □ ↦ a FRESH flexible: the invented name is not β (β ∉ dom Ξ), so the
       image is untouched and the same rule re-applies *)
    simpl_env in Hβ.
    destruct (α == β) as [-> | Hne];
      [ exfalso; clear - Hβ; fsetdec | ].
    destruct_if; [ exfalso; congruence | apply a_guess_mono__hole ].
  - (* ∀◇ is dropped *) apply a_guess_mono__tophole; apply IHa_guess_mono; auto.
  - (* a variable is renamed on BOTH sides, in lockstep *)
    destruct_if; apply a_guess_mono__var.
  - apply a_guess_mono__unit.
  - (* the two branches split [Ξ1 ++ Ξ2]; freshness is inherited *)
    rewrite dom_app in Hβ, Hγ.
    apply a_guess_mono__arrow;
      [ apply IHa_guess_mono1 | apply IHa_guess_mono2 ];
      clear - Hβ Hγ; fsetdec.
  - (* ∀ : commute the substitution past the opener on both sides *)
    apply a_guess_mono__forall
      with (L := L `union` singleton β `union` singleton γ).
    intros α Hα.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var;
      [ | clear - Hα; fsetdec | apply lc_ptyp_var_f ].
    apply H0; [ clear - Hα; solve_notin | exact Hβ | exact Hγ ].
Qed.

(** …and the form the ∀ case actually consumes: ONE instance at a β fresh for
    everything becomes the cofinite family, because β occurs in neither the
    guessed flexibles nor (after the substitution is undone) the payload. *)
Lemma a_guess_mono_all_of_one : forall Θ P Ξ A β,
  a_guess_mono Θ (open_pskl_wrt_pskl P (pskl_var_f β)) Ξ
                 (open_ptyp_wrt_ptyp A (ptyp_var_f β)) ->
  β `notin` dom Ξ ->
  β `notin` ftvar_in_pskl P -> β `notin` ftvar_in_ptyp A ->
  a_guess_mono Θ (pskl_all_syn P) Ξ (ptyp_all A).
Proof.
  intros Θ P Ξ A β Hg Hβ HβP HβA.
  apply a_guess_mono__forall
    with (L := add β (dom Ξ `union` ftvar_in_pskl P `union` ftvar_in_ptyp A)).
  intros α Hα.
  (* β ∉ ftv P / ftv A, so opening at α IS the β-instance with β renamed *)
  rewrite (subst_pskl_in_pskl_intro β P (pskl_var_f α)) by exact HβP.
  rewrite (subst_ptyp_in_ptyp_intro β A (ptyp_var_f α)) by exact HβA.
  apply a_guess_mono_rename_tvar;
    [ exact Hg | exact Hβ | clear - Hα; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §3  THE HOLE CASE, WHICH IS WHAT MAKES THE θ-EXTENSION WELL-DEFINED   *)
(*                                                                        *)
(*  guess^TY sends a ◇ to a fresh flexible α̂, so κ' must send α̂ to the     *)
(*  counterpart's skeleton at that position — and a metasubstitution's     *)
(*  images are Θ-scoped MONOTYPES.  Both are delivered by inverting        *)
(*  precision at a hole, and there are only two ways to derive it:         *)
(*                                                                        *)
(*   · [ad_refine_syn__hole] — its target is a SYNTHESISED painting while  *)
(*     precision supplies an INHERITED one, so §1 forces ∀-freeness, and   *)
(*     ghost-freeness (from [a_tags_sort] at TY) then forces a monotype.   *)
(*     Its fill premise is [Θ ⨟ empty ⊢ₚₛᵃ P] — CLOSED, which is also why  *)
(*     a hole under a ∀ can never be filled with the bound variable and    *)
(*     the images stay Θ-well-formed.                                     *)
(*   · [ad_refine_syn__flex_r] — the target IS a defined flexible, so the  *)
(*     monotype is that variable itself.                                  *)
(* ===================================================================== *)

(** Inverting the refinement with the source pinned to ◇ and the TARGET still
    a variable — [inversion] then produces clean equations we control.  Only
    two rules have a ◇ source: [__hole] and [__flex_r]. *)
Lemma ad_refine_syn_hole_l_inv : forall Θ Δ Y,
  Θ ⨟ Δ ⊢ᵣᵃ bskl_hole ⊳ Y ->
  (exists P, Θ ⨟ empty ⊢ₚₛᵃ P /\ Y = pskl_to_bskl_syn P)
  \/ (exists α τ, binds α (abind_flex_mono_def τ) Θ /\ Y = bskl_var_f α).
Proof.
  intros Θ Δ Y H; inversion H; subst;
    [ left; eexists; split; [ eassumption | reflexivity ]
    | right; do 2 eexists; split; [ eassumption | reflexivity ] ].
Qed.

Lemma ad_precise_hole_inv_mono : forall Θ Δ X,
  Θ ⨟ Δ ⊢ₚᵣᵃ pskl_hole ⊑ X ->
  pskl_ghost_free X -> lc_pskl X ->
  exists τ, ptyp_to_pskl τ = X /\ mono_ptyp τ /\ Θ ⨟ empty ⊢ₚₛᵃ X.
Proof.
  intros Θ Δ X Hp Hgf Hlc. unfold ad_precise in Hp. cbn in Hp.
  destruct (ad_refine_syn_hole_l_inv Hp) as [[P [Hwf Heq]] | [α [τ0 [Hb Heq]]]].
  - (* __hole : the SYN/INH painting clash pins X ∀-free, hence a monotype *)
    destruct (@pskl_inh_eq_syn_inv _ _ Heq) as [-> Haf].
    destruct (@pskl_all_ghost_free_mono _ Haf Hgf Hlc) as [τ [Heqτ Hmτ]].
    exists τ; repeat split; [ exact Heqτ | exact Hmτ | exact Hwf ].
  - (* __flex_r : the target is a defined flexible — the monotype is IT *)
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in Heq;
      try discriminate Heq.
    (* X = α0, and the equation pins α0 = α *)
    assert (Hαe : α0 = α) by congruence; subst α0.
    exists (ptyp_var_f α); split; [ reflexivity | split ];
      [ apply mono_ptyp__var
      | (* Δ-membership, then the three [a_binds_tvar] disjuncts *)
        apply a_wf_pskl__var; right; right; right; exists τ0; exact Hb ].
Qed.

(* ===================================================================== *)
(*  §4  A ∀-HEADED SOURCE NEVER REFINES TO A MONOTYPE                     *)
(*                                                                        *)
(*  The ∀ case of the witness induction must refute the [__flex_r] reading *)
(*  of its precision premise: if the counterpart were a defined flexible   *)
(*  α̂, precision would demand [∀… ⊳ syn τ] for α̂'s MONOTYPE definition τ,  *)
(*  and no rule can do that — [__all] needs an inherited-∀ target, which a *)
(*  monotype painting never is, and [__flex_r] only chains to another      *)
(*  monotype definition.  The chain terminates because every definition in *)
(*  a well-formed context is a monotype.                                  *)
(* ===================================================================== *)

Lemma ad_refine_syn_all_l_not_mono : forall Θ Δ Y τ,
  Θ ⨟ Δ ⊢ᵣᵃ (bskl_all_inh Y) ⊳ (ptyp_to_bskl_syn τ) ->
  a_wf_aenv Θ -> mono_ptyp τ -> False.
Proof.
  intros Θ Δ Y τ H. remember (bskl_all_inh Y) as Src eqn:HeqS.
  remember (ptyp_to_bskl_syn τ) as Tgt eqn:HeqT.
  revert Y τ HeqS HeqT.
  induction H; intros Y0 τ0 HeqS HeqT HwfΘ Hmτ; subst;
    try discriminate HeqS.
  - (* __all : NO monotype painting is an inherited ∀ — and note [ptyp_all]
       is discriminated too, since its painting is [bskl_all_SYN].  So every
       shape of τ0 dies on [HeqT] and there is nothing left to do. *)
    destruct τ0; cbn in HeqT; discriminate HeqT.
  - (* __flex_r : only a VARIABLE painting survives [HeqT]; chain to its
       definition, which a well-formed context keeps a monotype *)
    destruct τ0; cbn in HeqT; try discriminate HeqT.
    assert (Hαe : α = α0) by congruence; subst α0.
    eapply IHad_refine_syn;
      [ reflexivity | reflexivity | exact HwfΘ
      | eapply a_wf_aenv_binds_def_mono; eassumption ].
Qed.
