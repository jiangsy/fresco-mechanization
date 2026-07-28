(** COUNTEREXAMPLE: algorithmic refinement [ad_refine_syn] is NOT transitive.

    Consequence: [lemma:precision-preserves-refinement]
    (full-algo-spec.tex:716) — "if Θ ⊢ P ⊑ Q and Θ ⊢ inh{Q} ⊳ A then
    Θ ⊢ inh{P} ⊳ A" — is not provable as stated, and with it the
    completeness/optimality development that rests on it.

    ROOT CAUSE (paper, declarative.tex:1505-1510).  The GhostForall rule

        Δ ⨟ Γ,α ⊢ ⊤.inh{P} ⊳ Q
        ----------------------------------
        Δ ⨟ Γ   ⊢ ⊤.inh{P} ⊳ syn{∀α.} Q

    binds α in Γ but deliberately KEEPS Δ (the paper's own comment there
    reads "It's fine to keep Δ since we already required well-formedness
    separately").  But Δ is exactly what the Ghost rule tests:

        Δ ∩ ftv(syn{Q}) = ∅
        -----------------------
        Δ ⨟ Γ ⊢ □ ⊳ syn{Q}

    So a ghost NESTED under a GhostForall may be filled with the very α that
    the GhostForall binds — α is in Γ, not in Δ, so the side condition does
    not forbid it.  The result captures α:

        ⊤.(□→□)  ⊳  ∀α. ⊤.(α→α)

    and the right-hand side is NOT a well-formed skeleton: skeleton
    well-formedness binds a quantifier's variable in Δ, while a ⊤-ghost's
    body must be well-formed at the EMPTY Δ.  Since the Ghost rule can only
    produce WELL-FORMED fills, □ cannot refine to it — transitivity fails.

    LIKELY FIX (for the authors): GhostForall should extend Δ as well as Γ
    (i.e. [Δ,α ⨟ Γ,α]), exactly as the ∀-rule does.  Then the Ghost rule's
    side condition forbids the capture and [step2] below is underivable.

    NB the mechanised [ad_refine_syn__tophole_fill] is FAITHFUL to the paper
    here (α into the context, Δ untouched), so this is a paper-level issue,
    not an encoding slip.  (Separately, the mech's [ad_refine_syn__all] adds
    the variable only to Δ where the paper adds it to both Δ and Γ; that
    discrepancy is unrelated to this counterexample.)

    Everything below is Qed and axiom-free. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.

(* The fill: ⊤.(□ → □).  Well-formed at the empty Δ: the tophole's body
   is an arrow (hence guarded), and the arrow's components are holes. *)
Definition Pfill : pskl := pskl_tophole (pskl_arrow pskl_hole pskl_hole).

Lemma Pfill_wf : forall Θ, Θ ⨟ empty ⊢ₚₛᵃ Pfill.
Proof.
  intros. apply a_wf_pskl__tophole.
  - apply guarded_pskl__arrow; constructor.
  - apply a_wf_pskl__arrow; apply a_wf_pskl__hole.
Qed.

(* Step 1: □ ⊳ syn(⊤.(□→□))   by the ghost rule. *)
Lemma step1 : forall Θ Δ,
  Θ ⨟ Δ ⊢ᵣᵃ bskl_hole ⊳ (pskl_to_bskl_syn Pfill).
Proof. intros. apply ad_refine_syn__hole. apply Pfill_wf. Qed.

(* Step 2: syn(⊤.(□→□)) ⊳ ∀X. ⊤.(X→X)   by tophole_fill, filling both
   ghosts with the fresh CONTEXT rigid X introduced by the rule. *)
Definition Bres : bskl :=
  bskl_all_syn (bskl_tophole (bskl_arrow (bskl_var_b 0) (bskl_var_b 0))).

Lemma step2 : forall Θ Δ,
  Θ ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_syn Pfill) ⊳ Bres.
Proof.
  intros. simpl. apply ad_refine_syn__tophole_fill with (L := dom Θ).
  intros X HX. simpl.
  apply ad_refine_syn__tophole_keep.
  - apply guarded_bskl__arrow; constructor.
  - apply ad_refine_syn__arrow;
      (replace (bskl_var_f X) with (pskl_to_bskl_syn (pskl_var_f X)) by reflexivity;
       apply ad_refine_syn__hole;
       apply a_wf_pskl__var; right; left; unfold binds; left; reflexivity).
Qed.

(* Bres IS a syn painting -- of Pres. *)
Definition Pres : pskl :=
  pskl_all_syn (pskl_tophole (pskl_arrow (pskl_var_b 0) (pskl_var_b 0))).

Lemma Bres_is_syn : Bres = pskl_to_bskl_syn Pres.
Proof. reflexivity. Qed.

(* ...but Pres is NOT well-formed: the all-rule puts the bound variable in
   Δ, while the tophole-rule demands its body be well-formed at EMPTY Δ. *)
Lemma Pres_not_wf : forall Θ Δ, ~ (Θ ⨟ Δ ⊢ₚₛᵃ Pres).
Proof.
  intros Θ Δ Hwf. unfold Pres in Hwf.
  inversion Hwf as [ | | | L Θa Δa Pa Hbody | | ]; subst.
  pick fresh X for (L `union` dom Θ).
  specialize (Hbody X ltac:(auto)). simpl in Hbody.
  inversion Hbody as [ | | | | | Θb Δb Pb Hg Hwfb ]; subst.
  inversion Hwfb as [ | | Θc Δc P1 P2 Hw1 Hw2 | | | ]; subst.
  inversion Hw1 as [ | Θd Δd Xd Hin | | | | ]; subst.
  destruct Hin as [Hemp | Htv].
  - clear - Hemp. fsetdec.
  - clear - Htv Fr.
    destruct Htv as [Hb | [Hb | [t Hb]]];
      apply binds_In in Hb; clear - Hb Fr; fsetdec.
Qed.

(* The ghost rule is the ONLY rule that can put □ on the left (flex_r only
   fires with a variable on the right, and a variable is itself a syn
   painting).  So anything □ refines to is a syn painting of a WELL-FORMED
   skeleton. *)
Lemma hole_inv : forall Θ Δ Q',
  Θ ⨟ Δ ⊢ᵣᵃ bskl_hole ⊳ Q' ->
  exists P, Q' = pskl_to_bskl_syn P /\ Θ ⨟ empty ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ Q' H. remember bskl_hole as Q eqn:HQ.
  induction H; try discriminate.
  - exists P. split; [ reflexivity | assumption ].
  - exists (pskl_var_f α). split; [ reflexivity | ].
    apply a_wf_pskl__var. right. right. right. exists τ. exact H.
Qed.

Lemma no_hole_to_Bres : forall Θ Δ, ~ (Θ ⨟ Δ ⊢ᵣᵃ bskl_hole ⊳ Bres).
Proof.
  intros Θ Δ H.
  destruct (hole_inv _ _ _ H) as [P [Heq HwfP]].
  (* Bres = pskl_to_bskl_syn P forces P = Pres, which is not well-formed *)
  destruct P as [ | | | | Pb | | ]; simpl in Heq; try discriminate.
  destruct Pb as [ | | | | | | Pt ]; simpl in Heq; try discriminate.
  destruct Pt as [ | | | Pt1 Pt2 | | | ]; simpl in Heq; try discriminate.
  destruct Pt1 as [ | n1 | | | | | ]; simpl in Heq; try discriminate.
  destruct Pt2 as [ | n2 | | | | | ]; simpl in Heq; try discriminate.
  inversion Heq; subst.
  eapply Pres_not_wf. exact HwfP.
Qed.

(* CONSEQUENCE: [ad_refine_syn] is NOT transitive.
     □ ⊳ syn(⊤.(□→□))            (step1, the ghost rule)
     syn(⊤.(□→□)) ⊳ ∀X.⊤.(X→X)   (step2, tophole_fill + two ghost fills
                                   with the CONTEXT rigid X the rule binds)
   but NOT
     □ ⊳ ∀X.⊤.(X→X)              (no_hole_to_Bres)
   because the ghost rule can only produce a WELL-FORMED skeleton, and
   ∀X.⊤.(X→X) is not one: [a_wf_pskl__all] binds X in Δ, whereas
   [a_wf_pskl__tophole] requires its body to be well-formed at the EMPTY Δ.
   Refinement's [tophole_fill], by contrast, binds X in the CONTEXT. *)
Theorem ad_refine_syn_not_transitive :
  ~ (forall Θ Δ Q1 Q2 Q3,
       Θ ⨟ Δ ⊢ᵣᵃ Q1 ⊳ Q2 -> Θ ⨟ Δ ⊢ᵣᵃ Q2 ⊳ Q3 -> Θ ⨟ Δ ⊢ᵣᵃ Q1 ⊳ Q3).
Proof.
  intros Htrans.
  eapply (no_hole_to_Bres nil empty).
  eapply Htrans; [ apply step1 | apply step2 ].
Qed.
