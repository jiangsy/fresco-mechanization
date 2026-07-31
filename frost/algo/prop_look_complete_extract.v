(** P6-L — COMPLETENESS OF LOOK  [a_extract_complete_gen]
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
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.def_tags.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_sub_complete.
Require Import src.frost.algo.prop_look_complete.
Require Import src.frost.algo.prop_look_complete_cstr.
Require Import src.frost.algo.prop_look_complete_sub_cstr.

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
    is [pskl_ghost_free] (the FIXPOINT of prop_pat_sub.v — [◇]/[∀◇] map to
    [False]); what [a_tags_sort] at TY supplies for ψa is its uskl twin
    [uskl_ghost_free], and §5's [uskl_ghost_free_to_pskl] bridges them, so
    [⌊ψa⌋ˢ] has no ◇ / ∀◇ to obstruct this. *)
Lemma pskl_all_ghost_free_mono : forall P,
  pskl_all_free P -> pskl_ghost_free P -> lc_pskl P ->
  exists τ, ptyp_to_pskl τ = P /\ mono_ptyp τ.
Proof.
  intros P Ha; induction Ha; intros Hg Hlc; cbn in Hg;
    try solve [ contradiction ].
  - exists ptyp_unit; split; [ reflexivity | apply mono_ptyp__unit ].
  - (* a BOUND variable is ruled out by local closure, not by ghost-freeness *)
    inversion Hlc.
  - exists (ptyp_var_f α); split; [ reflexivity | apply mono_ptyp__var ].
  - destruct Hg as [Hg1 Hg2]. inversion Hlc; subst.
    destruct (IHHa1 Hg1 ltac:(assumption)) as [τ1 [Heq1 Hm1]].
    destruct (IHHa2 Hg2 ltac:(assumption)) as [τ2 [Heq2 Hm2]].
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

(* ===================================================================== *)
(*  §5  BRIDGES AND TRANSPORTS THE WITNESS INDUCTION CONSUMES             *)
(*                                                                        *)
(*  Four small facts, each of which the paper uses silently:               *)
(*                                                                        *)
(*   · ghost-freeness is invariant under opening (both ways), so the ∀     *)
(*     case may descend into [⌊ψa⌋ˢ]'s body and come back out;             *)
(*   · [a_tags_sort] at TY hands ghost-freeness on the DECORATED ψa, and   *)
(*     the witness needs it on the ERASURE [⌊ψa⌋ˢ];                        *)
(*   · a metasubstitution's image must be [a_wf_ptyp], while §3 delivers   *)
(*     [a_wf_pskl] of its painting — the two agree on monotypes;           *)
(*   · a Δ-BOUND variable of a precision derivation can be renamed.  This  *)
(*     is the "removing β as necessary" move: the ∀ case runs the IH at    *)
(*     ONE fresh β and must hand [ad_refine_syn__all] a COFINITE family.   *)
(* ===================================================================== *)

(** Ghost-freeness is a purely structural property of the constructor
    skeleton, so opening by a variable neither creates nor destroys it. *)
Lemma pskl_ghost_free_open_rec_iff : forall P Q k,
  pskl_ghost_free Q ->
  (pskl_ghost_free (open_pskl_wrt_pskl_rec k Q P) <-> pskl_ghost_free P).
Proof.
  intros P; induction P as [ | n | α | P1 IH1 P2 IH2 | P0 IH0 | | P0 IH0 ];
    intros Q k HQ; cbn.
  - tauto.
  - (* a bound index either stays one or becomes [Q]; [pskl_var_b n] is
       ghost-free and so, by hypothesis, is [Q] — the iff is trivial both ways *)
    destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; cbn; tauto.
  - tauto.
  - specialize (IH1 Q k HQ); specialize (IH2 Q k HQ). tauto.
  - specialize (IH0 Q (S k) HQ). tauto.
  - (* ◇ is ghost-free on NEITHER side *) tauto.
  - (* ∀◇ likewise *) tauto.
Qed.

Lemma pskl_ghost_free_open_inv : forall P α,
  pskl_ghost_free (open_pskl_wrt_pskl P (pskl_var_f α)) ->
  pskl_ghost_free P.
Proof.
  intros P α H. unfold open_pskl_wrt_pskl in H.
  eapply (@pskl_ghost_free_open_rec_iff P (pskl_var_f α) 0);
    [ cbn; exact I | exact H ].
Qed.

(** [a_tags_sort a_sub_mode_ty] gives ghost-freeness of the DECORATED ψa;
    the witness induction runs against the erasure.  The ε-tagged ∀ erases
    to a plain [pskl_all_syn], which is exactly [pgf_all]. *)
Lemma uskl_ghost_free_to_pskl : forall ψ,
  uskl_ghost_free ψ -> pskl_ghost_free ⌊ ψ ⌋ˢ.
Proof.
  intros ψ H; induction H; cbn.
  - exact I.
  - exact I.
  - split; assumption.
  - (* ∀ε : erases to a plain ∀; one instance suffices, by the open-invariance *)
    pick fresh α for L.
    eapply pskl_ghost_free_open_inv with (α := α).
    rewrite <- uskl_to_pskl_open. apply H0. clear - Fr; fsetdec.
  - pick fresh α for L.
    eapply pskl_ghost_free_open_inv with (α := α).
    rewrite <- uskl_to_pskl_open. apply H0. clear - Fr; fsetdec.
Qed.

(** The converse of [a_wf_ptyp_to_wf_pskl] on a MONOTYPE: a monotype has no
    binder, so its painting's well-formedness is its own — and the Δ slot is
    irrelevant because §3 always delivers the CLOSED reading. *)
Lemma a_wf_ptyp_of_wf_pskl_mono : forall Θ τ,
  mono_ptyp τ ->
  Θ ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl τ) ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ τ Hm; induction Hm; intros Hwf; cbn in Hwf.
  - apply a_wf_ptyp__unit.
  - inversion Hwf; subst.
    apply a_wf_ptyp__var.
    match goal with H : _ \/ _ |- _ =>
      destruct H as [Hc | Hbt]; [ exfalso; clear - Hc; fsetdec | exact Hbt ] end.
  - inversion Hwf; subst. apply a_wf_ptyp__arrow; auto.
Qed.

(** Every definition of a well-formed context is scoped by its domain, so a
    name outside the domain is fresh for all of them — the side condition
    [ad_refine_syn_f_rename] asks for, discharged by freshness alone. *)
Lemma a_wf_aenv_def_ftv_fresh : forall Θ β,
  a_wf_aenv Θ -> β `notin` dom Θ ->
  forall α τ, binds α (abind_flex_mono_def τ) Θ -> β `notin` ftvar_in_ptyp τ.
Proof.
  intros Θ β Hwf Hβ α τ Hb.
  assert (Hwfτ : a_wf_ptyp Θ τ)
    by (eapply a_wf_aenv_binds_def_wf; eassumption).
  assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
    by (eapply a_wf_ptyp_ftv_dom'; exact Hwfτ).
  clear - Hβ Hsc; fsetdec.
Qed.

(** Renaming a Δ-BOUND variable of a refinement derivation.  Routed through
    the fill-hygiene variant: [ad_refine_syn_f_rename] needs the renamed name
    in [F], and [ad_refine_syn_f_fextend_dom] puts it there for free because
    it is outside [dom Θ] — every hole fill is wf at its own context, hence
    can never BE it.  (The ftv-keyed [ad_refine_syn_f_fextend_ftv] would NOT
    do: β occurs in the target [X0^β], which is the whole point.) *)
Lemma ad_refine_syn_rename_delta : forall Θ Δ Q Q' β α0,
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ Q' ->
  a_wf_aenv Θ ->
  β `notin` dom Θ ->
  Θ ⨟ (add α0 (remove β Δ)) ⊢ᵣᵃ
    (subst_bskl_in_bskl (bskl_var_f α0) β Q) ⊳
    (subst_bskl_in_bskl (bskl_var_f α0) β Q').
Proof.
  intros Θ Δ Q Q' β α0 H HwfΘ Hβ.
  apply ad_refine_syn_f_forget with (F := singleton β).
  apply ad_refine_syn_f_rename;
    [ apply ad_refine_syn_f_fextend_dom with (F := empty);
        [ apply ad_refine_syn_f_of_plain; exact H
        | intros α1 Hα1; right; assert (α1 = β) by (clear - Hα1; fsetdec);
          subst; exact Hβ ]
    | clear; fsetdec
    | exact Hβ
    | eapply a_wf_aenv_def_ftv_fresh; eassumption ].
Qed.

(** …and its precision reading, which is what the ∀ case applies. *)
Lemma ad_precise_rename_delta : forall Θ Δ P X β α0,
  Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ X ->
  a_wf_aenv Θ ->
  β `notin` dom Θ ->
  Θ ⨟ (add α0 (remove β Δ)) ⊢ₚᵣᵃ
    (subst_pskl_in_pskl (pskl_var_f α0) β P) ⊑
    (subst_pskl_in_pskl (pskl_var_f α0) β X).
Proof.
  intros Θ Δ P X β α0 H HwfΘ Hβ. unfold ad_precise in *.
  rewrite <- ! subst_var_bskl_inh.
  apply ad_refine_syn_rename_delta; assumption.
Qed.

(* ===================================================================== *)
(*  §6  INVERTING PRECISION AT A COMPOSITE SOURCE — WITH A REPLAY          *)
(*                                                                        *)
(*  The witness induction descends the SOURCE [P_s], so at an arrow / ∀◇ / *)
(*  ∀ it must read the counterpart's matching piece off the precision      *)
(*  premise.  Three rules can conclude precision at a non-atomic source,   *)
(*  and only ONE of them is the structural one: [__flex_r] fires whenever  *)
(*  the counterpart is a DEFINED FLEXIBLE, replacing the target by that    *)
(*  definition's monotype painting and leaving the source untouched.       *)
(*                                                                        *)
(*  ⚠️ At the ∀ that chain REFUTES (§4).  At the ARROW and the ∀◇ IT DOES  *)
(*  NOT: κs can turn a flexible into an arrow, so the source's shape does  *)
(*  not clash with a monotype painting, and the chain must be CHASED.  So  *)
(*  those two lemmas each return, besides the counterpart's pieces, a      *)
(*  REPLAY function rebuilding precision against the ORIGINAL X — the      *)
(*  chased [__flex_r] steps re-applied.  (This is one-step re-application, *)
(*  not transitivity of refinement, which is FALSE —                       *)
(*  cex/cex_refine_not_transitive.v.)  The chase terminates on the         *)
(*  DERIVATION, which is why these are inductions on it, not on a size.    *)
(* ===================================================================== *)

Lemma ad_precise_arrow_l_inv : forall Θ Δ Src Tgt,
  Θ ⨟ Δ ⊢ᵣᵃ Src ⊳ Tgt ->
  forall S1 S2 X,
  Src = bskl_arrow (pskl_to_bskl_inh S1) (pskl_to_bskl_inh S2) ->
  Tgt = pskl_to_bskl_inh X ->
  a_wf_aenv Θ -> pskl_ghost_free X -> lc_pskl X ->
  exists X1 X2,
    pskl_ghost_free X1 /\ pskl_ghost_free X2 /\ lc_pskl X1 /\ lc_pskl X2 /\
    Θ ⨟ Δ ⊢ₚᵣᵃ S1 ⊑ X1 /\ Θ ⨟ Δ ⊢ₚᵣᵃ S2 ⊑ X2 /\
    (forall Y1 Y2,
       Θ ⨟ Δ ⊢ₚᵣᵃ Y1 ⊑ X1 -> Θ ⨟ Δ ⊢ₚᵣᵃ Y2 ⊑ X2 ->
       Θ ⨟ Δ ⊢ₚᵣᵃ (pskl_arrow Y1 Y2) ⊑ X).
Proof.
  intros Θ Δ Src Tgt H; induction H;
    intros S1 S2 X HeqS HeqT HwfΘ Hgf Hlc;
    try discriminate HeqS.
  - (* __arrow : the structural case *)
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    inversion HeqS; inversion HeqT; subst.
    cbn in Hgf; destruct Hgf as [Hgf1 Hgf2]. inversion Hlc; subst.
    exists X1, X2. unfold ad_precise.
    split; [ assumption | ]. split; [ assumption | ].
    split; [ assumption | ]. split; [ assumption | ].
    split; [ assumption | ]. split; [ assumption | ].
    intros Y1 Y2 HY1 HY2. cbn.
    apply ad_refine_syn__arrow; assumption.
  - (* __flex_r : chase the definition, then re-apply the rule *)
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    assert (Hαe : α0 = α) by congruence; subst α0.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eassumption).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eassumption).
    assert (Hpaint : ptyp_to_bskl_syn τ = pskl_to_bskl_inh (ptyp_to_pskl τ))
      by (symmetry; apply ptyp_to_bskl_inh_syn_eq; exact Hmτ).
    destruct (IHad_refine_syn S1 S2 (ptyp_to_pskl τ) HeqS Hpaint HwfΘ
                ltac:(apply ptyp_to_pskl_ghost_free)
                ltac:(apply lc_ptyp_to_pskl; eapply a_wf_ptyp_lc; exact Hwfτ))
      as (X1 & X2 & Hg1 & Hg2 & Hl1 & Hl2 & Hp1 & Hp2 & Hreplay).
    exists X1, X2.
    split; [ exact Hg1 | ]. split; [ exact Hg2 | ].
    split; [ exact Hl1 | ]. split; [ exact Hl2 | ].
    split; [ exact Hp1 | ]. split; [ exact Hp2 | ].
    intros Y1 Y2 HY1 HY2. unfold ad_precise; cbn.
    apply ad_refine_syn__flex_r with (τ := τ); [ assumption | ].
    rewrite Hpaint. exact (Hreplay Y1 Y2 HY1 HY2).
Qed.

Lemma ad_precise_tophole_l_inv : forall Θ Δ Src Tgt,
  Θ ⨟ Δ ⊢ᵣᵃ Src ⊳ Tgt ->
  forall S0 X,
  Src = bskl_tophole (pskl_to_bskl_inh S0) ->
  Tgt = pskl_to_bskl_inh X ->
  a_wf_aenv Θ -> pskl_ghost_free X -> lc_pskl X ->
  exists X',
    pskl_ghost_free X' /\ lc_pskl X' /\
    Θ ⨟ Δ ⊢ₚᵣᵃ S0 ⊑ X' /\
    (forall Y, Θ ⨟ Δ ⊢ₚᵣᵃ Y ⊑ X' -> Θ ⨟ Δ ⊢ₚᵣᵃ Y ⊑ X).
Proof.
  intros Θ Δ Src Tgt H; induction H;
    intros S0 X HeqS HeqT HwfΘ Hgf Hlc;
    try discriminate HeqS.
  - (* __tophole_remove : the ghost is dropped, X is unchanged *)
    inversion HeqS; subst.
    exists X.
    split; [ exact Hgf | ]. split; [ exact Hlc | ].
    (* [subst] has already rewritten the rule's target to [inh X] and, in
       doing so, consumed HeqT — hence the guarded rewrite *)
    split; [ unfold ad_precise; try rewrite <- HeqT; assumption | ].
    intros Y HY; exact HY.
  - (* __tophole_fill : the target is a SYNTHESISED ∀, which no inherited
       painting is — [pskl_all_syn] paints to [bskl_all_INH] *)
    exfalso.
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      discriminate HeqT.
  - (* __tophole_keep : the target keeps the ghost, so X would carry a ∀◇ —
       excluded by ghost-freeness *)
    exfalso.
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    cbn in Hgf; contradiction.
  - (* __flex_r : chase *)
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    assert (Hαe : α0 = α) by congruence; subst α0.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eassumption).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eassumption).
    assert (Hpaint : ptyp_to_bskl_syn τ = pskl_to_bskl_inh (ptyp_to_pskl τ))
      by (symmetry; apply ptyp_to_bskl_inh_syn_eq; exact Hmτ).
    destruct (IHad_refine_syn S0 (ptyp_to_pskl τ) HeqS Hpaint HwfΘ
                ltac:(apply ptyp_to_pskl_ghost_free)
                ltac:(apply lc_ptyp_to_pskl; eapply a_wf_ptyp_lc; exact Hwfτ))
      as (X' & Hg' & Hl' & Hp' & Hreplay).
    exists X'.
    split; [ exact Hg' | ]. split; [ exact Hl' | ]. split; [ exact Hp' | ].
    intros Y HY. unfold ad_precise; cbn.
    apply ad_refine_syn__flex_r with (τ := τ); [ assumption | ].
    rewrite Hpaint. exact (Hreplay Y HY).
Qed.

(** At a ∀ source there is NO chase: §4 refutes the [__flex_r] reading, so the
    counterpart is a ∀ too and the inversion is exact — no replay needed, the
    caller rebuilds with [ad_refine_syn__all]. *)
Lemma ad_precise_all_l_inv : forall Θ Δ Src Tgt,
  Θ ⨟ Δ ⊢ᵣᵃ Src ⊳ Tgt ->
  forall S0 X,
  Src = bskl_all_inh (pskl_to_bskl_inh S0) ->
  Tgt = pskl_to_bskl_inh X ->
  a_wf_aenv Θ -> pskl_ghost_free X -> lc_pskl X ->
  exists X0 L,
    X = pskl_all_syn X0 /\
    (forall β, β `notin` L ->
       Θ ⨟ (add β Δ) ⊢ₚᵣᵃ (open_pskl_wrt_pskl S0 (pskl_var_f β))
                       ⊑ (open_pskl_wrt_pskl X0 (pskl_var_f β))).
Proof.
  intros Θ Δ Src Tgt H; induction H;
    intros S0 X HeqS HeqT HwfΘ Hgf Hlc;
    try discriminate HeqS.
  - (* __all *)
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    inversion HeqS; inversion HeqT; subst.
    exists X0, L. split; [ reflexivity | ].
    intros β Hβ. unfold ad_precise.
    rewrite ! pskl_to_bskl_inh_open. apply H; exact Hβ.
  - (* __flex_r : REFUTED — a ∀-headed source never refines to a monotype *)
    exfalso.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eassumption).
    subst.
    eapply ad_refine_syn_all_l_not_mono; eassumption.
Qed.

(* ===================================================================== *)
(*  §7  FOUR SMALL TOOLS THE WITNESS INDUCTION ASSEMBLES WITH             *)
(* ===================================================================== *)

(** [msubst_pskl] only reads its argument's FREE variables, so entries keyed
    outside them are invisible.  The arrow case needs exactly this: the two
    branches' extensions are appended in one order but each branch's IH was
    proved against its own extension alone. *)
Lemma msubst_pskl_lookup_congr_ftv : forall κ σ P,
  (forall α, α `in` ftvar_in_pskl P ->
     msubst_lookup κ α = msubst_lookup σ α) ->
  msubst_pskl κ P = msubst_pskl σ P.
Proof.
  intros κ σ P; revert κ σ;
    induction P as [ | n | α | P1 IHP1 P2 IHP2 | P0 IHP0 | | P0 IHP0 ];
    intros κ σ Heq; cbn in *; try reflexivity.
  - rewrite Heq by (clear; fsetdec); reflexivity.
  - rewrite (IHP1 κ σ), (IHP2 κ σ);
      [ reflexivity | intros α Hα; apply Heq; clear - Hα; fsetdec
      | intros α Hα; apply Heq; clear - Hα; fsetdec ].
  - rewrite (IHP0 κ σ); [ reflexivity | exact Heq ].
  - rewrite (IHP0 κ σ); [ reflexivity | exact Heq ].
Qed.

Lemma msubst_lookup_mid_skip : forall κa κm κb α,
  α `notin` dom κm ->
  msubst_lookup (κa ++ κm ++ κb) α = msubst_lookup (κa ++ κb) α.
Proof.
  intros κa κm κb α Hα.
  destruct (AtomSetProperties.In_dec α (dom κa)) as [Hin | Hnin].
  - rewrite (@msubst_lookup_app_in κa (κm ++ κb) α Hin).
    rewrite (@msubst_lookup_app_in κa κb α Hin). reflexivity.
  - rewrite (@msubst_lookup_app_notin κa (κm ++ κb) α Hnin).
    rewrite (@msubst_lookup_app_notin κa κb α Hnin).
    rewrite (@msubst_lookup_app_notin κm κb α Hα). reflexivity.
Qed.

Lemma msubst_pskl_mid_skip : forall κa κm κb P,
  (forall α, α `in` dom κm -> α `notin` ftvar_in_pskl P) ->
  msubst_pskl (κa ++ κm ++ κb) P = msubst_pskl (κa ++ κb) P.
Proof.
  intros κa κm κb P Hdisj.
  apply msubst_pskl_lookup_congr_ftv; intros α Hα.
  apply msubst_lookup_mid_skip.
  intro Hc. apply (Hdisj α Hc). exact Hα.
Qed.

(** Precision is monotone in Δ (the [_f]-kit transport, at [F = ∅]). *)
Lemma ad_precise_delta_mono : forall Θ Δ0 Δ P X,
  Θ ⨟ Δ0 ⊢ₚᵣᵃ P ⊑ X -> Δ0 [<=] Δ ->
  Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ X.
Proof.
  intros Θ Δ0 Δ P X H Hsub. unfold ad_precise in *.
  apply ad_refine_syn_f_forget with (F := empty).
  eapply ad_refine_syn_f_delta_mono;
    [ apply ad_refine_syn_f_of_plain; exact H | exact Hsub ].
Qed.

(** Renaming a Δ-BOUND variable of skeleton well-formedness — the wf twin of
    §5's [ad_precise_rename_delta], and needed for the same reason.  The ∀◇
    case is where freshness earns its keep: its premise is CLOSED
    ([Θ ⨟ empty ⊢ₚₛᵃ P]), so β ∉ dom Θ makes β fresh for the body and the
    substitution is a no-op there. *)
Lemma a_wf_pskl_rename_delta : forall Θ Δ P β α0,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  β `notin` dom Θ ->
  Θ ⨟ (add α0 (remove β Δ)) ⊢ₚₛᵃ (subst_pskl_in_pskl (pskl_var_f α0) β P).
Proof.
  intros Θ Δ P β α0 H; revert α0; induction H; intros α1 Hβ; cbn.
  - apply a_wf_pskl__unit.
  - destruct_if as [-> | Hne].
    + apply a_wf_pskl__var. left. clear; fsetdec.
    + apply a_wf_pskl__var.
      destruct H as [HΔ | Hbt];
        [ left; clear - HΔ Hne; fsetdec | right; exact Hbt ].
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L `union` singleton β `union` singleton α1).
    intros α2 Hα2.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα2; fsetdec | apply lc_pskl_var_f ].
    eapply a_wf_pskl_delta_mono;
      [ apply H0; [ clear - Hα2; fsetdec | exact Hβ ]
      | clear - Hα2; fsetdec ].
  - apply a_wf_pskl__hole.
  - (* ∀◇ : the body is wf at the CLOSED Δ, so β ∉ ftv it and subst is a no-op *)
    assert (Hfr : β `notin` ftvar_in_pskl P).
    { assert (Hsc : ftvar_in_pskl P [<=] (empty `union` dom Θ))
        by (eapply a_wf_pskl_ftv_dom; exact H0).
      clear - Hβ Hsc; fsetdec. }
    rewrite (subst_pskl_in_pskl_fresh_eq P (pskl_var_f α1) β Hfr).
    apply a_wf_pskl__tophole; [ exact H | exact H0 ].
Qed.

(* ===================================================================== *)
(*  §8  THE TWO PROPERTIES OF THE INCOMING κ THE INDUCTION NEEDS           *)
(*                                                                        *)
(*  The ∀ case opens at a fresh β and must (a) push κ through the opener   *)
(*  and (b) know β does not appear in the κ-IMAGE of the body — otherwise  *)
(*  the renaming that builds the cofinite family would move it.  Both are  *)
(*  properties of the incoming κ, and an [a_inc] supplies both: images are *)
(*  locally closed ([a_inc_lookup_lc]) and SCOPED BY THE TARGET.           *)
(* ===================================================================== *)

(** A metasubstitution's images are scoped by the target context (an
    unbound variable maps to itself, hence the [add α]). *)
Lemma a_inc_lookup_ftv : forall Θ0 κ Θ α,
  κ ∷ Θ0 ⊑ Θ ->
  ftvar_in_ptyp (msubst_lookup κ α) [<=] add α (dom Θ).
Proof.
  intros Θ0 κ Θ α H; revert α; induction H; intros α0; cbn.
  - clear; fsetdec.
  - destruct (α0 == α) as [-> | Hne].
    + assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ')
        by (eapply a_wf_ptyp_ftv_dom'; eassumption).
      clear - Hsc; fsetdec.
    + apply IHa_inc.
  - destruct (α0 == α) as [-> | Hne].
    + assert (Hsc : ftvar_in_ptyp τ' [<=] dom Θ')
        by (eapply a_wf_ptyp_ftv_dom'; eassumption).
      clear - Hsc; fsetdec.
    + apply IHa_inc.
  - specialize (IHa_inc α0); simpl_env; clear - IHa_inc; fsetdec.
  - specialize (IHa_inc α0); simpl_env; clear - IHa_inc; fsetdec.
  - specialize (IHa_inc α0); simpl_env; clear - IHa_inc; fsetdec.
Qed.

(** Both properties survive prefixing a block of wf monotype images — which
    is what the ∀ / arrow cases hand back up. *)
Lemma msubst_lc_app_wf : forall Θ κa κb,
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa ->
  msubst_lc κb ->
  msubst_lc (κa ++ κb).
Proof.
  intros Θ κa κb Hall Hlc; unfold msubst_lc in *; intros α.
  induction κa as [ | [α1 τ1] κa' IH ]; cbn; [ apply Hlc | ].
  inversion Hall as [ | ph pt [Hwf1 Hm1] Hall' ]; subst; cbn in Hwf1.
  destruct (α == α1) as [-> | Hne];
    [ eapply a_wf_ptyp_lc; exact Hwf1 | apply IH; exact Hall' ].
Qed.

Lemma msubst_ftv_app_wf : forall Θ κa κb,
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa ->
  (forall α, ftvar_in_ptyp (msubst_lookup κb α) [<=] add α (dom Θ)) ->
  forall α, ftvar_in_ptyp (msubst_lookup (κa ++ κb) α) [<=] add α (dom Θ).
Proof.
  intros Θ κa κb Hall Hsc α.
  induction κa as [ | [α1 τ1] κa' IH ]; cbn; [ apply Hsc | ].
  inversion Hall as [ | ph pt [Hwf1 Hm1] Hall' ]; subst; cbn in Hwf1.
  destruct (α == α1) as [-> | Hne].
  - assert (Hs1 : ftvar_in_ptyp τ1 [<=] dom Θ)
      by (eapply a_wf_ptyp_ftv_dom'; exact Hwf1).
    clear - Hs1; fsetdec.
  - apply IH; exact Hall'.
Qed.

(** A name fresh for the skeleton and for the target context is fresh for the
    κ-image too — the fact that keeps the ∀ case's renaming honest. *)
Lemma msubst_pskl_ftv_fresh : forall (Θ : aenv) κ P β,
  (forall α, ftvar_in_ptyp (msubst_lookup κ α) [<=] add α (dom Θ)) ->
  β `notin` ftvar_in_pskl P ->
  β `notin` dom Θ ->
  β `notin` ftvar_in_pskl (msubst_pskl κ P).
Proof.
  intros Θ κ P β Hsc; revert P;
    induction P as [ | n | α | P1 IH1 P2 IH2 | P0 IH0 | | P0 IH0 ];
    intros HβP HβΘ; cbn in *; try solve [ clear; fsetdec ].
  - assert (Hb : ftvar_in_pskl (ptyp_to_pskl (msubst_lookup κ α))
                 [<=] ftvar_in_ptyp (msubst_lookup κ α))
      by (apply ptyp_to_pskl_ftv).
    specialize (Hsc α). clear - Hb Hsc HβP HβΘ; fsetdec.
  - specialize (IH1 ltac:(clear - HβP; fsetdec) HβΘ).
    specialize (IH2 ltac:(clear - HβP; fsetdec) HβΘ).
    clear - IH1 IH2; fsetdec.
  - apply IH0; assumption.
  - apply IH0; assumption.
Qed.

(** One instance at a fresh β becomes the cofinite family — for skeleton
    well-formedness and for precision.  Both bodies are the same three moves:
    re-express the α-instance as a β-renaming of the β-instance
    ([subst_*_intro]), rename ([*_rename_delta]), then relax Δ. *)
Lemma a_wf_pskl_all_of_one : forall Θ Δ P β,
  Θ ⨟ (add β Δ) ⊢ₚₛᵃ (open_pskl_wrt_pskl P (pskl_var_f β)) ->
  β `notin` dom Θ -> β `notin` Δ -> β `notin` ftvar_in_pskl P ->
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_all_syn P).
Proof.
  intros Θ Δ P β Hwf HβΘ HβΔ HβP.
  apply a_wf_pskl__all
    with (L := add β (Δ `union` dom Θ `union` ftvar_in_pskl P)).
  intros α0 Hα0.
  assert (Hsub : add α0 (remove β (add β Δ)) [<=] add α0 Δ)
    by (clear - HβΔ; fsetdec).
  eapply a_wf_pskl_delta_mono; [ | exact Hsub ].
  rewrite (subst_pskl_in_pskl_intro β P (pskl_var_f α0)) by exact HβP.
  apply a_wf_pskl_rename_delta; [ exact Hwf | exact HβΘ ].
Qed.

Lemma ad_precise_all_of_one : forall Θ Δ S0 X0 β,
  Θ ⨟ (add β Δ) ⊢ₚᵣᵃ (open_pskl_wrt_pskl S0 (pskl_var_f β))
                  ⊑ (open_pskl_wrt_pskl X0 (pskl_var_f β)) ->
  a_wf_aenv Θ ->
  β `notin` dom Θ -> β `notin` Δ ->
  β `notin` ftvar_in_pskl S0 -> β `notin` ftvar_in_pskl X0 ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (pskl_all_syn S0) ⊑ (pskl_all_syn X0).
Proof.
  intros Θ Δ S0 X0 β Hpre HwfΘ HβΘ HβΔ HβS HβX.
  unfold ad_precise; cbn [pskl_to_bskl_inh].
  apply ad_refine_syn__all
    with (L := add β (Δ `union` dom Θ `union` ftvar_in_pskl S0
                        `union` ftvar_in_pskl X0)).
  intros α0 Hα0.
  rewrite <- ! pskl_to_bskl_inh_open.
  assert (Hsub : add α0 (remove β (add β Δ)) [<=] add α0 Δ)
    by (clear - HβΔ; fsetdec).
  eapply ad_precise_delta_mono; [ | exact Hsub ].
  rewrite (subst_pskl_in_pskl_intro β S0 (pskl_var_f α0)) by exact HβS.
  rewrite (subst_pskl_in_pskl_intro β X0 (pskl_var_f α0)) by exact HβX.
  apply ad_precise_rename_delta; [ exact Hpre | exact HwfΘ | exact HβΘ ].
Qed.

(* ===================================================================== *)
(*  §9  THE WITNESS INDUCTION                                             *)
(*                                                                        *)
(*  The paper's "by induction on the definition of guess^N(P_s)" — but     *)
(*  read the other way round.  P6-L's conclusion is EXISTENTIAL in Ξ and   *)
(*  in the extract's output, so we do not consume a given guess: we BUILD  *)
(*  [a_guess_mono] and the metasubstitution extension κ' SIMULTANEOUSLY,   *)
(*  descending [P_s] and reading the counterpart's matching piece off the  *)
(*  precision premise (§6) at each step.  The extension is POSITIONAL, as  *)
(*  the paper says: at a ◇ the guess invents a fresh flexible and κ' sends *)
(*  it to the monotype §3 finds at that position in [⌊ψa⌋ˢ].               *)
(*                                                                        *)
(*  The measure is [size_pskl P_s] — the ∀ case opens at a fresh β, and    *)
(*  opening by a variable preserves size.                                 *)
(*                                                                        *)
(*  BOTH Δ's move.  [Δ0] carries [P_s]'s own binders (wf) and [Δ] the      *)
(*  counterpart's (precision); [a_wf_pskl__all] and [ad_refine_syn__all]   *)
(*  each grow their own, and the ∀◇ case RESETS Δ0 to ∅ (the ghost's body  *)
(*  is wf CLOSED).  They are therefore independent parameters of the       *)
(*  induction, not tied to one another.                                    *)
(*                                                                        *)
(*  κ''s images are Θ-well-formed no matter how deep the ∀-nesting goes,   *)
(*  which is what makes the extension legal: [ad_refine_syn__hole]'s fill  *)
(*  premise is [Θ ⨟ ∅ ⊢ₚₛᵃ P] — CLOSED — so a hole under a binder is never *)
(*  filled with the bound variable (§3).                                   *)
(* ===================================================================== *)

Lemma a_guess_ty_witness : forall n Θ0 Θ κs Δ Δ0 Ps X,
  size_pskl Ps <= n ->
  a_wf_aenv Θ ->
  Θ0 ⨟ Δ0 ⊢ₚₛᵃ Ps ->
  msubst_lc κs ->
  (forall α, ftvar_in_ptyp (msubst_lookup κs α) [<=] add α (dom Θ)) ->
  pskl_ghost_free X -> lc_pskl X ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_pskl κs Ps) ⊑ X ->
  forall L, exists Ξ' A κ',
    a_guess_mono nil Ps Ξ' A /\
    all_flex_mono Ξ' /\
    uniq Ξ' /\
    keys κ' = keys Ξ' /\
    (forall α, α `in` dom Ξ' -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    (Ξ' ++ Θ0) ⨟ Δ0 ⊢ₚₛᵃ (ptyp_to_pskl A) /\
    Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_pskl (κ' ++ κs) (ptyp_to_pskl A)) ⊑ X.
Proof.
  intros n; induction n as [ | n IH ];
    intros Θ0 Θ κs Δ Δ0 Ps X Hsz HwfΘ HwfPs Hκlc Hκsc Hgf Hlc Hprec L.
  - (* no skeleton has size 0 *)
    exfalso. pose proof (size_pskl_min Ps) as Hm.
    clear - Hsz Hm. inversion Hsz; lia.
  - assert (HlcPs : lc_pskl Ps) by (eapply a_wf_pskl_lc; exact HwfPs).
    destruct Ps as [ | m | α | Ps1 Ps2 | Ps0 | | Ps0 ].
    + (* ------------------------------ unit ------------------------------ *)
      exists nil, ptyp_unit, nil.
      split; [ apply a_guess_mono__unit | ].
      split; [ apply Forall_nil | ].
      split; [ apply uniq_nil | ].
      split; [ reflexivity | ].
      split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
      split; [ apply Forall_nil | ].
      split; [ cbn; apply a_wf_pskl__unit | ].
      cbn [app ptyp_to_pskl]. exact Hprec.
    + (* var_b : excluded by local closure, not by ghost-freeness *)
      exfalso. inversion HlcPs.
    + (* ------------------------------ var ------------------------------- *)
      (* guess^TY returns the variable itself, so BOTH remaining goals are
         the corresponding hypotheses verbatim *)
      exists nil, (ptyp_var_f α), nil.
      split; [ apply a_guess_mono__var | ].
      split; [ apply Forall_nil | ].
      split; [ apply uniq_nil | ].
      split; [ reflexivity | ].
      split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
      split; [ apply Forall_nil | ].
      split; [ cbn [app ptyp_to_pskl]; exact HwfPs | ].
      cbn [app ptyp_to_pskl]. exact Hprec.
    + (* ----------------------------- arrow ------------------------------ *)
      cbn in Hsz.
      assert (HwfPs1 : Θ0 ⨟ Δ0 ⊢ₚₛᵃ Ps1) by (inversion HwfPs; subst; assumption).
      assert (HwfPs2 : Θ0 ⨟ Δ0 ⊢ₚₛᵃ Ps2) by (inversion HwfPs; subst; assumption).
      assert (Hpre' : Θ ⨟ Δ ⊢ᵣᵃ
                (bskl_arrow (pskl_to_bskl_inh (msubst_pskl κs Ps1))
                            (pskl_to_bskl_inh (msubst_pskl κs Ps2)))
                ⊳ (pskl_to_bskl_inh X))
        by (unfold ad_precise in Hprec; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_arrow_l_inv Θ Δ _ _ Hpre'
                  (msubst_pskl κs Ps1) (msubst_pskl κs Ps2) X
                  eq_refl eq_refl HwfΘ Hgf Hlc)
        as (X1 & X2 & Hg1 & Hg2 & Hl1 & Hl2 & Hp1 & Hp2 & Hreplay).
      destruct (IH Θ0 Θ κs Δ Δ0 Ps1 X1 ltac:(clear - Hsz; lia)
                   HwfΘ HwfPs1 Hκlc Hκsc Hg1 Hl1 Hp1
                   (L `union` ftvar_in_pskl Ps1 `union` ftvar_in_pskl Ps2))
        as (Ξ1 & A1 & κa & Hgu1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hwf1 & Hpr1).
      destruct (IH Θ0 Θ κs Δ Δ0 Ps2 X2 ltac:(clear - Hsz; lia)
                   HwfΘ HwfPs2 Hκlc Hκsc Hg2 Hl2 Hp2
                   (L `union` ftvar_in_pskl Ps1 `union` ftvar_in_pskl Ps2
                      `union` dom Ξ1))
        as (Ξ2 & A2 & κb & Hgu2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hwf2 & Hpr2).
      (* the two guessed blocks are apart, and each misses the OTHER branch's
         source variables — which is what makes each branch's own κ invisible
         to the other's payload *)
      assert (Hdκa : dom κa [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
      assert (Hdκb : dom κb [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
      assert (HA1 : ftvar_in_pskl (ptyp_to_pskl A1)
                    [<=] ftvar_in_pskl Ps1 `union` dom Ξ1).
      { assert (Hb : ftvar_in_ptyp A1 [<=] ftvar_in_pskl Ps1 `union` dom Ξ1)
          by (eapply a_guess_mono_ftv; exact Hgu1).
        assert (Hc : ftvar_in_pskl (ptyp_to_pskl A1) [<=] ftvar_in_ptyp A1)
          by (apply ptyp_to_pskl_ftv).
        clear - Hb Hc; fsetdec. }
      assert (HA2 : ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] ftvar_in_pskl Ps2 `union` dom Ξ2).
      { assert (Hb : ftvar_in_ptyp A2 [<=] ftvar_in_pskl Ps2 `union` dom Ξ2)
          by (eapply a_guess_mono_ftv; exact Hgu2).
        assert (Hc : ftvar_in_pskl (ptyp_to_pskl A2) [<=] ftvar_in_ptyp A2)
          by (apply ptyp_to_pskl_ftv).
        clear - Hb Hc; fsetdec. }
      assert (Hdisj : disjoint Ξ1 Ξ2).
      { unfold disjoint. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hα0 Hfr2; fsetdec. }
      assert (Heq1 : msubst_pskl (κa ++ κb ++ κs) (ptyp_to_pskl A1)
                     = msubst_pskl (κa ++ κs) (ptyp_to_pskl A1)).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0 Hdκb; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hfr2 HA1; fsetdec. }
      assert (Heq2 : msubst_pskl (nil ++ κa ++ (κb ++ κs)) (ptyp_to_pskl A2)
                     = msubst_pskl (nil ++ (κb ++ κs)) (ptyp_to_pskl A2)).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin1 : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
        specialize (Hfr1 α0 Hin1).
        assert (Hne : α0 `notin` dom Ξ2)
          by (clear - Hin1 Hdisj; unfold disjoint in Hdisj; fsetdec).
        clear - Hfr1 Hne HA2; fsetdec. }
      cbn [app] in Heq2.
      exists (Ξ1 ++ Ξ2), (ptyp_arrow A1 A2), (κa ++ κb).
      split; [ apply a_guess_mono__arrow; assumption | ].
      split; [ apply all_flex_mono_app; assumption | ].
      split; [ clear - Hu1 Hu2 Hdisj; solve_uniq | ].
      split; [ rewrite ! keys_app; rewrite Hk1, Hk2; reflexivity | ].
      split; [ intros α0 Hα0; rewrite dom_app in Hα0;
               destruct (union_1 Hα0) as [Hin1 | Hin2];
                 [ specialize (Hfr1 α0 Hin1); clear - Hfr1; fsetdec
                 | specialize (Hfr2 α0 Hin2); clear - Hfr2; fsetdec ] | ].
      split; [ apply Forall_app; split; assumption | ].
      split.
      { rewrite app_assoc. cbn [ptyp_to_pskl]. apply a_wf_pskl__arrow.
        - eapply a_wf_pskl_weaken; [ | exact Hwf1 ].
          intros x b Hb. apply binds_weaken_mid. exact Hb.
        - eapply a_wf_pskl_weaken; [ | exact Hwf2 ].
          intros x b Hb. apply binds_app_3. exact Hb. }
      rewrite app_assoc. cbn [ptyp_to_pskl msubst_pskl].
      rewrite Heq1, Heq2.
      apply Hreplay; assumption.
    + (* ------------------------------- ∀ -------------------------------- *)
      cbn in Hsz.
      assert (HwfF : exists Lw, forall β, β `notin` Lw ->
                Θ0 ⨟ (add β Δ0) ⊢ₚₛᵃ (open_pskl_wrt_pskl Ps0 (pskl_var_f β)))
        by (inversion HwfPs; subst; eexists; eassumption).
      destruct HwfF as [Lw HwfF].
      assert (Hpre' : Θ ⨟ Δ ⊢ᵣᵃ
                (bskl_all_inh (pskl_to_bskl_inh (msubst_pskl κs Ps0)))
                ⊳ (pskl_to_bskl_inh X))
        by (unfold ad_precise in Hprec; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_all_l_inv Θ Δ _ _ Hpre' (msubst_pskl κs Ps0) X
                  eq_refl eq_refl HwfΘ Hgf Hlc)
        as (X0 & Lp & HeqX & HprF).
      subst X.
      assert (HgfX0 : pskl_ghost_free X0) by (cbn in Hgf; exact Hgf).
      assert (HlcX0 : forall α0,
                lc_pskl (open_pskl_wrt_pskl X0 (pskl_var_f α0)))
        by (inversion Hlc; subst; assumption).
      pick fresh β for (L `union` Lw `union` Lp `union` Δ `union` Δ0
                          `union` ftvar_in_pskl Ps0 `union` ftvar_in_pskl X0
                          `union` dom Θ `union` dom Θ0 `union` dom κs).
      assert (HwfβPs : Θ0 ⨟ (add β Δ0) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl Ps0 (pskl_var_f β)))
        by (apply HwfF; clear - Fr; fsetdec).
      assert (HprβX : Θ ⨟ (add β Δ) ⊢ₚᵣᵃ
                (msubst_pskl κs (open_pskl_wrt_pskl Ps0 (pskl_var_f β)))
                ⊑ (open_pskl_wrt_pskl X0 (pskl_var_f β))).
      { rewrite (@msubst_pskl_open_lc_local κs Ps0 β Hκlc
                   ltac:(clear - Fr; fsetdec)).
        apply HprF; clear - Fr; fsetdec. }
      destruct (IH Θ0 Θ κs (add β Δ) (add β Δ0)
                   (open_pskl_wrt_pskl Ps0 (pskl_var_f β))
                   (open_pskl_wrt_pskl X0 (pskl_var_f β))
                   ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                         clear - Hsz; lia)
                   HwfΘ HwfβPs Hκlc Hκsc
                   ltac:(unfold open_pskl_wrt_pskl;
                         apply pskl_ghost_free_open_rec; exact HgfX0)
                   ltac:(apply HlcX0)
                   HprβX
                   (add β (L `union` dom Θ `union` dom Θ0
                             `union` ftvar_in_pskl Ps0
                             `union` ftvar_in_pskl X0)))
        as (Ξ' & A' & κ' & Hgu & Hfm & Hu & Hk & Hfr & HF & Hwf' & Hpr).
      (* CLOSE the guessed payload over β: [a_guess_mono__forall] is cofinite
         in the opener with a FIXED (Ξ;A), so the body must not mention β *)
      assert (HβΞ : β `notin` dom Ξ')
        by (intro Hc; specialize (Hfr β Hc); clear - Hfr; fsetdec).
      assert (HopenA : open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp β A')
                         (ptyp_var_f β) = A')
        by (apply open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp).
      assert (HβA : β `notin` ftvar_in_ptyp (close_ptyp_wrt_ptyp β A'))
        by (rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp; clear; fsetdec).
      assert (HβPA : β `notin` ftvar_in_pskl
                       (ptyp_to_pskl (close_ptyp_wrt_ptyp β A'))).
      { assert (Hc : ftvar_in_pskl (ptyp_to_pskl (close_ptyp_wrt_ptyp β A'))
                     [<=] ftvar_in_ptyp (close_ptyp_wrt_ptyp β A'))
          by (apply ptyp_to_pskl_ftv).
        clear - Hc HβA; fsetdec. }
      assert (HopenPA : ptyp_to_pskl A'
                = open_pskl_wrt_pskl
                    (ptyp_to_pskl (close_ptyp_wrt_ptyp β A')) (pskl_var_f β))
        by (rewrite <- ptyp_to_pskl_open; rewrite HopenA; reflexivity).
      exists Ξ', (ptyp_all (close_ptyp_wrt_ptyp β A')), κ'.
      split.
      { eapply a_guess_mono_all_of_one with (β := β);
          [ rewrite HopenA; exact Hgu
          | exact HβΞ
          | clear - Fr; fsetdec
          | exact HβA ]. }
      split; [ exact Hfm | ].
      split; [ exact Hu | ].
      split; [ exact Hk | ].
      split; [ intros α0 Hα0; specialize (Hfr α0 Hα0);
               clear - Hfr; fsetdec | ].
      split; [ exact HF | ].
      split.
      { cbn [ptyp_to_pskl].
        eapply a_wf_pskl_all_of_one with (β := β);
          [ rewrite <- HopenPA; exact Hwf'
          | rewrite dom_app; clear - HβΞ Fr; fsetdec
          | clear - Fr; fsetdec
          | exact HβPA ]. }
      (* precision: the β-instance, closed back into the cofinite family *)
      assert (Hβκ : β `notin` ftvar_in_pskl
                (msubst_pskl (κ' ++ κs)
                   (ptyp_to_pskl (close_ptyp_wrt_ptyp β A')))).
      { eapply msubst_pskl_ftv_fresh;
          [ eapply msubst_ftv_app_wf; [ exact HF | exact Hκsc ]
          | exact HβPA
          | clear - Fr; fsetdec ]. }
      cbn [ptyp_to_pskl msubst_pskl].
      eapply ad_precise_all_of_one with (β := β);
        [ | exact HwfΘ | clear - Fr; fsetdec | clear - Fr; fsetdec
        | exact Hβκ | clear - Fr; fsetdec ].
      rewrite <- (@msubst_pskl_open_lc_local (κ' ++ κs)
                    (ptyp_to_pskl (close_ptyp_wrt_ptyp β A')) β
                    (msubst_lc_app_wf HF Hκlc)
                    ltac:(rewrite dom_app;
                          assert (Hd : dom κ' [=] dom Ξ')
                            by (apply keys_eq_dom; exact Hk);
                          clear - Hd HβΞ Fr; fsetdec)).
      rewrite <- HopenPA. exact Hpr.
    + (* ------------------------------- ◇ -------------------------------- *)
      assert (Hpre' : Θ ⨟ Δ ⊢ₚᵣᵃ pskl_hole ⊑ X)
        by (unfold ad_precise in Hprec |- *; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_hole_inv_mono Θ Δ X Hpre' Hgf Hlc)
        as (τ & Heqτ & Hmτ & HwfX).
      assert (Hwfτ : a_wf_ptyp Θ τ)
        by (apply a_wf_ptyp_of_wf_pskl_mono;
            [ exact Hmτ | rewrite Heqτ; exact HwfX ]).
      pick fresh α1 for (L `union` dom Θ `union` dom Θ0 `union` dom κs).
      exists ((α1 ~ abind_flex_mono) ++ nil), (ptyp_var_f α1),
             ((α1, τ) :: nil).
      split; [ apply a_guess_mono__hole | ].
      split; [ unfold all_flex_mono; repeat constructor | ].
      split; [ solve_uniq | ].
      split; [ reflexivity | ].
      split; [ intros α0 Hα0; simpl_env in Hα0;
               assert (Hα1 : α0 = α1) by (clear - Hα0; fsetdec);
               subst α0; clear - Fr; fsetdec | ].
      split; [ constructor; [ split; assumption | apply Forall_nil ] | ].
      split.
      { cbn [app ptyp_to_pskl]. apply a_wf_pskl__var. right. right. left.
        unfold binds. left. reflexivity. }
      (* κ' sends the guessed flexible to exactly the monotype §3 found *)
      cbn [app ptyp_to_pskl msubst_pskl].
      rewrite msubst_lookup_cons_eq. rewrite Heqτ.
      apply ad_precise_refl. eapply a_wf_pskl_delta_mono;
        [ exact HwfX | clear; fsetdec ].
    + (* ------------------------------ ∀◇ -------------------------------- *)
      cbn in Hsz.
      assert (Hguard : guarded_pskl Ps0) by (inversion HwfPs; subst; assumption).
      assert (HwfPs0 : Θ0 ⨟ empty ⊢ₚₛᵃ Ps0)
        by (inversion HwfPs; subst; assumption).
      assert (Hpre' : Θ ⨟ Δ ⊢ᵣᵃ
                (bskl_tophole (pskl_to_bskl_inh (msubst_pskl κs Ps0)))
                ⊳ (pskl_to_bskl_inh X))
        by (unfold ad_precise in Hprec; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_tophole_l_inv Θ Δ _ _ Hpre' (msubst_pskl κs Ps0) X
                  eq_refl eq_refl HwfΘ Hgf Hlc)
        as (X' & Hg' & Hl' & Hp' & Hreplay).
      destruct (IH Θ0 Θ κs Δ empty Ps0 X' ltac:(clear - Hsz; lia)
                   HwfΘ HwfPs0 Hκlc Hκsc Hg' Hl' Hp' L)
        as (Ξ' & A & κ' & Hgu & Hfm & Hu & Hk & Hfr & HF & Hwf' & Hpr).
      exists Ξ', A, κ'.
      split; [ apply a_guess_mono__tophole; exact Hgu | ].
      split; [ exact Hfm | ].
      split; [ exact Hu | ].
      split; [ exact Hk | ].
      split; [ exact Hfr | ].
      split; [ exact HF | ].
      split; [ eapply a_wf_pskl_delta_mono; [ exact Hwf' | clear; fsetdec ] | ].
      apply Hreplay; exact Hpr.
Qed.

(* ===================================================================== *)
(*  §10  P6-L — [a_extract_complete_gen]  (paper [lemma:complete-look])        *)
(*                                                                        *)
(*  The assembly the paper describes at tex:2755-2833, in its order:       *)
(*                                                                        *)
(*   (a)-(f)  P6-Ss ([a_looksub_solve_complete]) at [Pi := □], [Ψi := ∅],  *)
(*            so [Ψ' = Ψa]; its precision premise                          *)
(*            [Θ ⨟ Δ ⊢ κ□ ⊑ᵖ[∅] ψa] IS the precision hole rule.            *)
(*   (g)      [ad_partial_precise_complete] (P5b-i) upgrades ⊑ᵖ[Ψa] to     *)
(*            plain ⊑ against [⌊ψa⌋ˢ] — the paper's step at tex:2764.      *)
(*   (h),(i)-(12)  the guess.  At SK it is the identity, so κ' = · and     *)
(*            every conclusion is P6-Ss's verbatim; at TY it is §9.        *)
(*   (13)     [a_extract__solve] on (a), (b) and the guess.                *)
(*                                                                        *)
(*  The [a_inc] and wf conclusions are assembled with the HOMOGENEOUS-FLEX *)
(*  REORDER KIT of prop_look_complete_cstr.v: [a_extract] emits [Ξc,Ξ']    *)
(*  where the natural build order is [Ξ',Ξc] (both blocks are undefined    *)
(*  flexibles, so the order is immaterial — but not syntactically so).     *)
(*                                                                        *)
(*  As in P6-Ss, the paper's [inc[θ≡θa]{Θ0}{Θ}] appears as the REFLEXIVE   *)
(*  [a_inc_equiv Θ0 κ κ Θ]: the mech's [a_inc_equiv] is POSITIONAL, so the *)
(*  content "θa agrees with θ on Θ0" is carried instead by the a_inc       *)
(*  conclusion exhibiting θa as the EXTENSION [κa ++ κ].                   *)
(* ===================================================================== *)

(** P6-L, GENERALIZED in Δ.  The paper-facing statement is the Δ = ∅ corollary
    [a_extract_complete] at the end of the file — same convention as
    P6-Cs / P6-Ss ([a_lookeq_solve_complete_gen] / [a_lookeq_solve_complete],
    [a_looksub_solve_complete_gen] / [a_looksub_solve_complete]). *)
Theorem a_extract_complete_gen :
  forall n NM M Θ0 Θ κ Δ Ψa Ψsub ψa Q P P0 R' α,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->                            (* erase R' = P (R' is κ-FREE) *)
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψa ψa ->
  (ftag_in_uskl R') ∩ Ψa [=] empty ->       (* the paper's "Ψ disjoint from Ψa" *)
  Δ ∩ ftvar_in_uskl ψa [=] empty ->         (* ⌐ the precision HOLE rule's side condition *)
  Θ ⨟ Δ ⊢ₚₛᵃ ⌊ ψa ⌋ˢ ->                     (* the paper's wf premise for ψa *)
  delta_def_fresh Δ Θ ->
  sub_shield Θ0 Ψa empty P0 ψa ->
  (* the join's AMBIENT tag context: the paper's [Ψ,Ψa] — P6-Ss's range
     parameter, surfaced (2026-07-31) for P7b's Sub-ForallL, whose row
     premise runs at [Ψ ∪ Ψa] with the ambient [Ψ ⊆ ftag R'] *)
  Ψsub [<=] ftag_in_uskl R' `union` Ψa ->
  Ψa [<=] Ψsub ->
  (* subject = (κR')[ψa/α], EXACTLY the paper's form *)
  ad_pat_sub_g n NM M Ψsub Θ
    (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R')) Q ->
  Θ ⨟ empty ⊢ₚₛᵃ
    (uskl_to_pskl (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R'))) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  exists Ξ Pa κa,
    (Θ0 ⊢ P ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ Pa) /\      (* look succeeds *)
    (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa /\                 (* Θ0,Ξ ⊢ Pa *)
    a_wf_aenv (Ξ ++ Θ0) /\
    keys κa = keys Ξ /\
    (κa ++ κ) ∷ (Ξ ++ Θ0) ⊑ Θ /\                 (* inc[θa]{Θ0,Ξ}{Θ} *)
    a_inc_equiv Θ0 κ κ Θ /\                      (* inc[θ≡θa]{Θ0}{Θ} *)
    Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_pskl (κa ++ κ) Pa) ⊑ ⌊ ψa ⌋ˢ.
Proof.
  intros n NM M Θ0 Θ κ Δ Ψa Ψsub ψa Q P P0 R' α.
  intros HwfΘ HwfΘ0 HwfP0 HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR HscopeR HlcR
         Htags Hdisj HΔψ Hwfψ Hdfresh Hshield HΨsubU HΨsubL Hsubty
         HwfSubj Hrefine.
  (* ---- (a)-(f) : P6-Ss at [Pi := □], [Ψi := ∅] ---- *)
  destruct (@a_looksub_solve_complete n NM M Θ0 Θ κ Δ Ψa empty Ψa Ψsub ψa Q
              P P0 pskl_hole R' α
              HwfΘ HwfΘ0 HwfP0 ltac:(apply a_wf_pskl__hole)
              HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR HscopeR HlcR Htags Hdisj
              ltac:(clear; fsetdec) Hdfresh Hshield
              ltac:(cbn [msubst_pskl];
                    apply ad_ppre__hole; [ clear; fsetdec | exact HΔψ ])
              HΨsubU HΨsubL
              Hsubty HwfSubj Hrefine)
    as (𝒞 & Ξc & Pa & κc & Hlook & Hsolve & HwfPa & HwfΞc & HαΞc & Hkeysc
        & HForc & Hincc & Heqv & Hκcfresh & Hprec & _).
  (* ---- (g) : P5b-i upgrades ⊑ᵖ[Ψa] to plain ⊑ ⌊ψa⌋ˢ ---- *)
  assert (Hpre : Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_pskl (κc ++ κ) Pa) ⊑ ⌊ ψa ⌋ˢ).
  { eapply ad_partial_precise_complete;
      [ exact HwfΘ | exact Htags | exact Hwfψ | ].
    eapply ad_partial_precise_psi_cong; [ exact Hprec | clear; fsetdec ]. }
  (* ---- the reorder kit's prerequisites on the COLLECTED block ---- *)
  assert (HfmΞc : all_flex_mono Ξc)
    by (eapply a_looksub_all_flex_mono; exact Hlook).
  assert (HwmΞc : Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κc)
    by (destruct (@a_inc_flex_prefix_split Ξc κc Θ0 κ Θ HfmΞc Hkeysc Hincc)
          as [Hw _]; exact Hw).
  assert (HuqΞc : uniq (Ξc ++ Θ0)) by (apply a_wf_aenv_uniq; exact HwfΞc).
  (* ---- (h) : the guess.  SK is the identity; TY is §9 ---- *)
  destruct NM.
  - (* ================================ TY ============================== *)
    assert (Hgfψ : pskl_ghost_free ⌊ ψa ⌋ˢ)
      by (inversion Htags; subst; apply uskl_ghost_free_to_pskl; assumption).
    assert (Hlcψ : lc_pskl ⌊ ψa ⌋ˢ) by (eapply a_wf_pskl_lc; exact Hwfψ).
    destruct (@a_guess_ty_witness (size_pskl Pa) (Ξc ++ Θ0) Θ (κc ++ κ)
                Δ empty Pa ⌊ ψa ⌋ˢ
                (le_n _) HwfΘ HwfPa
                ltac:(unfold msubst_lc; intros α0;
                      eapply a_inc_lookup_lc; exact Hincc)
                ltac:(intros α0; eapply a_inc_lookup_ftv; exact Hincc)
                Hgfψ Hlcψ Hpre
                (add α (dom Θ `union` dom Θ0 `union` dom Ξc `union` dom κ)))
      as (Ξ' & A & κ' & Hgu & HfmΞ' & HuqΞ' & Hkeys' & Hfr' & HF' & Hwf'
          & Hpr').
    assert (HdomΞ' : dom κ' [=] dom Ξ') by (apply keys_eq_dom; exact Hkeys').
    assert (HuqAll : uniq (Ξc ++ Ξ' ++ Θ0)).
    { assert (Hd1 : disjoint Ξ' Ξc)
        by (unfold disjoint; intros α0 Hα0;
            assert (Hin : α0 `in` dom Ξ') by (clear - Hα0; fsetdec);
            specialize (Hfr' α0 Hin); clear - Hα0 Hfr'; fsetdec).
      assert (Hd2 : disjoint Ξ' Θ0)
        by (unfold disjoint; intros α0 Hα0;
            assert (Hin : α0 `in` dom Ξ') by (clear - Hα0; fsetdec);
            specialize (Hfr' α0 Hin); clear - Hα0 Hfr'; fsetdec).
      clear - HuqΞc HuqΞ' Hd1 Hd2; solve_uniq. }
    exists (Ξc ++ Ξ'), (ptyp_to_pskl A), (κc ++ κ').
    split.
    { eapply a_extract__solve;
        [ exact Hlook | exact Hsolve | apply a_guess__ty; exact Hgu ]. }
    split.
    { rewrite app_assoc. apply a_wf_pskl_swap_app. exact Hwf'. }
    split.
    { rewrite app_assoc.
      apply (@a_wf_aenv_flex_prefix Ξc (Ξ' ++ Θ0));
        [ exact HfmΞc | exact HuqAll | ].
      apply (@a_wf_aenv_flex_prefix Ξ' Θ0);
        [ exact HfmΞ' | clear - HuqAll; solve_uniq | exact HwfΘ0 ]. }
    split; [ rewrite ! keys_app; rewrite Hkeysc, Hkeys'; reflexivity | ].
    split.
    { (* the goal IS [(κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ] on the nose — do NOT
         reassociate, or the split becomes ambiguous *)
      apply (@a_inc_flex_prefix_build (Ξc ++ Ξ') (κc ++ κ') Θ0 κ Θ);
        [ apply all_flex_mono_app; assumption
        | rewrite ! keys_app; rewrite Hkeysc, Hkeys'; reflexivity
        | apply Forall_app; split; assumption
        | exact Hκ ]. }
    split; [ exact Heqv | ].
    (* the ONE reorder on the metasubstitution side: §9 built [κ',κc,κ],
       [a_extract] wants [κc,κ',κ]; the two blocks are apart *)
    rewrite app_assoc.
    rewrite <- (@msubst_pskl_app_swap κ' κc κ (ptyp_to_pskl A));
      [ exact Hpr' | ].
    intros α0 Hα0.
    assert (Hin : α0 `in` dom Ξ') by (clear - Hα0 HdomΞ'; fsetdec).
    specialize (Hfr' α0 Hin).
    assert (Hdc : dom κc [=] dom Ξc) by (apply keys_eq_dom; exact Hkeysc).
    clear - Hfr' Hdc; fsetdec.
  - (* ================================ SK ============================== *)
    (* [a_guess__sk] : Ξ' = ·, Q' = Q, so κ' = · and every conclusion is
       P6-Ss's verbatim *)
    exists (Ξc ++ nil), Pa, (κc ++ nil).
    split.
    { eapply a_extract__solve;
        [ exact Hlook | exact Hsolve | apply a_guess__sk ]. }
    (* only NOW may the empty guess block be absorbed — [a_extract__solve]'s
       conclusion is [Ξ ++ Ξ'], which no longer unifies once it is gone *)
    rewrite ! app_nil_r.
    split; [ exact HwfPa | ].
    split; [ exact HwfΞc | ].
    split; [ exact Hkeysc | ].
    split; [ exact Hincc | ].
    split; [ exact Heqv | ].
    exact Hpre.
Qed.

Print Assumptions a_extract_complete_gen.

(* ===================================================================== *)
(*  §11  THE Δ-HYGIENE PREMISES ABSORB AT Δ = ∅                            *)
(*                                                                        *)
(*  Two of P6-L's premises are pure Δ-hygiene — [delta_def_fresh Δ Θ] (Δ's *)
(*  members are fresh for Θ's flexible DEFINITIONS, inherited from P6-Ss)  *)
(*  and [Δ ∩ ftv ψa = ∅] (the precision HOLE rule's own side condition).   *)
(*  Both are VACUOUS at Δ = ∅, which is where every consumer enters: Δ     *)
(*  tracks the counterpart's ∀-binders, so it is empty at the top of a run *)
(*  and grows only inside the precision derivation.                       *)
(*                                                                        *)
(*  ⚠️ What does NOT absorb is [sub_shield] — that is P6-Sv's REPAIR, and  *)
(*  the paper's statement WITHOUT it is machine-checked FALSE              *)
(*  (cex/cex_p6sv_forall_flex.v).  It can only ever be DISCHARGED at a     *)
(*  call site where it is derivable, never dropped.  The remaining         *)
(*  premises are the paper's own EXTERNAL well-formedness side conditions  *)
(*  (docs/WF-SIDE-CONDITIONS.md), and α's freshness is Barendregt.         *)
(* ===================================================================== *)

(** P6-L — THE PAPER'S STATEMENT ([lemma:complete-look]).  Use THIS one unless
    you are threading a non-empty Δ down from an enclosing precision
    derivation. *)
Corollary a_extract_complete :
  forall n NM M Θ0 Θ κ Ψa ψa Q P P0 R' α,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψa ψa ->
  (ftag_in_uskl R') ∩ Ψa [=] empty ->
  Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψa ⌋ˢ ->
  sub_shield Θ0 Ψa empty P0 ψa ->
  ad_pat_sub_g n NM M Ψa Θ
    (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R')) Q ->
  Θ ⨟ empty ⊢ₚₛᵃ
    (uskl_to_pskl (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R'))) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  exists Ξ Pa κa,
    (Θ0 ⊢ P ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ Pa) /\
    (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa /\
    a_wf_aenv (Ξ ++ Θ0) /\
    keys κa = keys Ξ /\
    (κa ++ κ) ∷ (Ξ ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    Θ ⨟ empty ⊢ₚᵣᵃ (msubst_pskl (κa ++ κ) Pa) ⊑ ⌊ ψa ⌋ˢ.
Proof.
  intros n NM M Θ0 Θ κ Ψa ψa Q P P0 R' α.
  intros HwfΘ HwfΘ0 HwfP0 HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR HscopeR HlcR
         Htags Hdisj Hwfψ Hshield Hsubty HwfSubj Hrefine.
  eapply a_extract_complete_gen with (Ψsub := Ψa);
    [ exact HwfΘ | exact HwfΘ0 | exact HwfP0 | exact HmodSK | exact HmodTY
    | exact Hκ | exact HαΘ | exact HαΘ0 | exact HeraseR | exact HscopeR
    | exact HlcR | exact Htags | exact Hdisj
    | clear; fsetdec                                 (* ∅ ∩ ftv ψa = ∅ *)
    | exact Hwfψ
    | intros β α0 τ Hβ; exfalso; clear - Hβ; fsetdec (* delta_def_fresh ∅ Θ *)
    | exact Hshield
    | clear; fsetdec | clear; fsetdec                (* Ψsub := Ψa *)
    | exact Hsubty | exact HwfSubj | exact Hrefine ].
Qed.

Print Assumptions a_extract_complete.

(* ===================================================================== *)
(*  Sub-ForallL item 4 — [a_sub__forall_l]'s COFINITE extract family from *)
(*  the ONE instance P6-L produces.  The look's outputs (Ξ ⨾ 𝒞) never     *)
(*  mention the looked variable and the solve/guess components do not     *)
(*  see it at all, so the family is the renamed look                      *)
(*  ([a_looksub_rename_var]) + the SAME solve + the SAME guess.           *)
(* ===================================================================== *)

Lemma a_extract_family_of_instance : forall Θ0 NM M α P P0 Ξ P1,
  Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α)) ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 ->
  α `notin` ftvar_in_pskl P ->
  forall α',
  α' `notin` (singleton α `union` ftvar_in_pskl P) ->
  Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α')) ⊳[ NM , α' , M ] P0 ⤳ Ξ ↪ P1.
Proof.
  intros Θ0 NM M α P P0 Ξ P1 Hex Hfr α' Hα'.
  inversion Hex; subst.
  eapply a_extract__solve; [ | eassumption | eassumption ].
  assert (Hα'P : α' `notin`
                   ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                  P (pskl_var_f α)) as Hup.
    simpl in Hup. clear - Hα' Hup; fsetdec. }
  match goal with
    Hlk : _ ≼[ α , _ ] _ ⤳ _ ⨾ _ |- _ =>
    pose proof (a_looksub_rename_var Hlk Hα'P) as Hlk'
  end.
  rewrite <- (subst_pskl_in_pskl_intro α P (pskl_var_f α') Hfr) in Hlk'.
  exact Hlk'.
Qed.
