(** THE CAPTURE CONFIGURATION: refinement's rules alone do not preserve
    well-formedness, so the paper's presupposition (both sides well-formed,
    declarative.tex "Skeleton refinement") is load-bearing.

    ⚠️ RETRACTED 2026-10-08: this file used to prove that [ad_refine_syn] is
    NOT TRANSITIVE.  That rested on the mechanised Ghost rule demanding a
    WELL-FORMED fill.  The paper's Ghost rule only asks that the fill avoid
    Δ, and since the refinement rules were made faithful to the paper the
    composite below is derivable ([hole_to_Bres]), so the refutation is gone.

    ROOT CAUSE of the capture (paper, declarative.tex, refinement).  The
    GhostForall rule

        Δ ⨟ Γ,α ⊢ ∀◇inh{P} ⊳ Q
        ----------------------------------
        Δ ⨟ Γ   ⊢ ∀◇inh{P} ⊳ syn{∀α.} Q

    binds α in Γ but deliberately KEEPS Δ (the paper's own comment there
    reads "It's fine to keep Δ since we already required well-formedness
    separately").  But Δ is exactly what the Ghost rule tests:

        Δ ∩ ftv(syn{Q}) = ∅
        -----------------------
        Δ ⨟ Γ ⊢ □ ⊳ syn{Q}

    So a ghost NESTED under a GhostForall may be filled with the very α that
    the GhostForall binds.  The result captures α:

        ∀◇(□→□)  ⊳  ∀α. ∀◇(α→α)

    and the right-hand side is NOT a well-formed skeleton: skeleton
    well-formedness binds a quantifier's variable in Δ, and a ∀◇-ghost's
    body is checked under Γ∖Δ, where that variable is no longer bound
    ([ad_refine_syn_output_not_wf]).  The paper excludes it by presupposing
    well-formedness of both sides; nothing in the rules does.

    Everything below is Qed and axiom-free. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.

(* The fill: ∀◇(□ → □).  Well-formed at the empty Δ: the tophole's body
   is an arrow (hence guarded), and the arrow's components are holes. *)
Definition Pfill : pskl := pskl_tophole (pskl_arrow pskl_hole pskl_hole).

Lemma Pfill_wf : forall Θ, {{ Θ ⨟ empty ⊢ₚₛ Pfill }}a.
Proof.
  intros. apply a_wf_pskl__tophole.
  - apply guarded_pskl__arrow; constructor.
  - apply a_wf_pskl__arrow; apply a_wf_pskl__hole.
Qed.

(* Step 1: □ ⊳ syn(∀◇(□→□))   by the ghost rule (the fill is closed). *)
Lemma step1 : forall Θ Δ,
  {{ Θ ⨟ Δ ⊢ᵣ bskl_hole ⊳ (pskl_to_bskl_syn Pfill) }}ad.
Proof. intros. apply ad_refine_syn__hole. simpl. clear. fsetdec. Qed.

(* Step 2: syn(∀◇(□→□)) ⊳ ∀α. ∀◇(α→α)   by tophole_fill, filling both
   ghosts with the fresh CONTEXT rigid α introduced by the rule. *)
Definition Bres : bskl :=
  bskl_all_syn (bskl_tophole (bskl_arrow (bskl_var_b 0) (bskl_var_b 0))).

Lemma step2 : forall Θ Δ,
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_syn Pfill) ⊳ Bres }}ad.
Proof.
  intros. simpl. apply ad_refine_syn__tophole_fill with (L := dom Θ `union` Δ).
  intros α Hα. simpl.
  apply ad_refine_syn__tophole_keep.
  apply ad_refine_syn__arrow;
    (replace (bskl_var_f α) with (pskl_to_bskl_syn (pskl_var_f α)) by reflexivity;
     apply ad_refine_syn__hole; simpl; clear - Hα; fsetdec).
Qed.

(* Bres IS a syn painting -- of Pres. *)
Definition Pres : pskl :=
  pskl_all_syn (pskl_tophole (pskl_arrow (pskl_var_b 0) (pskl_var_b 0))).

Lemma Bres_is_syn : Bres = pskl_to_bskl_syn Pres.
Proof. reflexivity. Qed.

(* ...but Pres is NOT well-formed: the all-rule puts the bound variable in
   Δ, and the tophole-rule checks its body under [Θ∖Δ], where the variable
   is no longer bound. *)
Lemma Pres_not_wf : forall Θ Δ, ~ ({{ Θ ⨟ Δ ⊢ₚₛ Pres }}a).
Proof.
  intros Θ Δ Hwf. unfold Pres in Hwf.
  inversion Hwf as [ | | | L Θa Δa Pa Hbody | | ]; subst.
  pick fresh α for (L `union` dom Θ).
  specialize (Hbody α ltac:(auto)). simpl in Hbody.
  inversion Hbody as [ | | | | | Θb Δb Pb Hg Hwfb ]; subst.
  inversion Hwfb as [ | | Θc Δc P1 P2 Hw1 Hw2 | | | ]; subst.
  inversion Hw1 as [ | Θd Δd Xd Htv | | | | ]; subst.
  apply a_binds_tvar_aenv_minus in Htv. destruct Htv as [_ Hn].
  clear - Hn. fsetdec.
Qed.

(* ⚠️ RETRACTED 2026-10-08: the NON-TRANSITIVITY this file was named for.
   It rested on the mechanised ghost rule demanding a WELL-FORMED fill, which
   the paper's rule never did: the paper's ghost rule only asks that the fill
   avoid [Δ].  Now that [ad_refine_syn__hole] follows the paper, □ refines to
   the very output of [step2] in one step — [Bres] is closed — so the
   composite of [step1] and [step2] is derivable after all.  What survives is
   the point the paper's presupposition rests on: [step2] derives an output
   that is NOT well-formed ([Pres_not_wf]), so "refinement preserves
   well-formedness" needs the presupposition, and cannot be read off the
   rules. *)
Lemma hole_to_Bres : forall Θ Δ, {{ Θ ⨟ Δ ⊢ᵣ bskl_hole ⊳ Bres }}ad.
Proof.
  intros. rewrite Bres_is_syn. apply ad_refine_syn__hole.
  simpl. clear. fsetdec.
Qed.

(** The refinement rules alone derive an ill-formed output from a
    well-formed input: [Pfill] is well-formed, [step2] refines it to [Bres],
    and [Bres] paints [Pres], which is well-formed in no context. *)
Theorem ad_refine_syn_output_not_wf :
  ({{ nil ⨟ empty ⊢ₚₛ Pfill }}a) /\
  ({{ nil ⨟ empty ⊢ᵣ (pskl_to_bskl_syn Pfill) ⊳ (pskl_to_bskl_syn Pres) }}ad) /\
  ~ ({{ nil ⨟ empty ⊢ₚₛ Pres }}a).
Proof.
  split; [ apply Pfill_wf | split ].
  - rewrite <- Bres_is_syn. apply step2.
  - apply Pres_not_wf.
Qed.
