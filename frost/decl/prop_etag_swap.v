(** ε-TAG EQUIVARIANCE of the declarative judgments, and the ForallL
    FRESHENING it buys.

    ⭐ WHAT THIS IS FOR.  The paper's ForallL side condition is the single word
    *fresh* on the instantiation's tags Ψ', and it means GLOBAL freshness —
    fresh from the SUBJECT's own tags too, not just from the tag context, which
    is what [lemma:precision-substitution] needs and what the context-local
    reading does not give (Arrow splits the tag context but not the subject).
    All four subtyping judgments — [d_sub], [d_pat_sub], [ad_pat_sub] and the
    fuel mirrors [ad_pat_sub_g] / [_gv] — now render it that way, and THIS FILE
    is what pays for it: the one place the strong reading is not free is
    [d_consis_sub_trans_mid] (CST, prop_general_subsumption.v), whose ForallL
    case transports along [utyp_tag_refines], where the subject GAINS tags.
    See docs/PAPER-GAPS.md and docs/HANDOFF-closed-corollaries-declarative.md.

    ⭐ THE PRIMITIVE IS A SWAP, NOT A ONE-WAY RENAME.  A rename [ε1 ↦ ε2] is
    sound only when ε2 is fresh for the WHOLE derivation, and "the tags of a
    derivation" is not something a [Prop] lets us collect.  A transposition is
    a bijection, so it is an automorphism of every judgment with NO freshness
    side condition — the same reason algo/prop_swap.v takes equivariance as the
    renaming primitive for TYPE variables.  §1-§2 prove it for tag counting,
    well-scopedness, both consistencies and both subtypings; frost/prop_etag.v
    has the syntactic layer.  §3 turns it into the freshening: a ForallL node's
    instantiation can be moved out of any finite set, one transposition per bad
    tag, measured by the cardinality of the tags still in the way.

    ⚠️⚠️ WHY §3 IS NOT ENOUGH, and what §4-§5 do about it.  §3 freshens ONE
    node, from that node's own data.  Rewriting a whole derivation that way
    would need the freshened premise fed back to an induction hypothesis — and
    a STRUCTURAL induction cannot: at a ForallL node the IH is tied to the
    ORIGINAL instantiation [ph], while freshening produces a derivation of a
    DIFFERENT statement ([C[ph''] ⩽ B], not [C[ph] ⩽ B]).  ⚠️ Nor can the swap
    be applied to the IH's OUTPUT: there the instantiation's tags and the
    refined subject's tags sit in the SAME term ([T0[ph]]), so a transposition
    moves both.

    ⭐ SO STOP FRESHENING NODE BY NODE.  §4 introduces the tags-BOUND twin
    [d_sub_tagsin U] ("every ForallL's Ψ' ⊆ U"), whose [d_sub_to_tagsin]
    COLLECTS the bound by a plain induction — no freshening anywhere — and §5
    then moves [U] WHOLESALE with a single chain of transpositions, which is
    legitimate whenever the CONCLUSION is tag-free (then no swap touches it).
    CST consumes exactly that: it runs on [d_sub_tagsin U] against a
    tag-bounded refinement [utyp_tag_refines_in V], with ONE global
    [U ∩ V [=] ∅] discharging every node's hygiene at once, and its two call
    sites establish that from §5 because the transported derivation runs at the
    empty tag context with a PAINTED (hence tag-free) subject.

    ⚙ Each equivariance statement threads its tag context as [Ψs [=] swap Ψ]
    rather than substituting, because the rules state their contexts up to
    [ [=] ]; the four re-derivations that needs are in frost/prop_etag.v §3.

    ⚙ NO [Set Implicit Arguments], for the same reason as
    algo/typing/prop_conserv.v: the statements thread equations, and under the
    flag their set arguments would become strictly implicit. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.prop_etag.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_weakening.
Require Import src.frost.decl.prop_renaming.

(* ===================================================================== *)
(*  §1  THE LEAF JUDGMENTS: tag counting, and well-scopedness             *)
(* ===================================================================== *)

Lemma d_tags_swap_etag : forall Ψ C,
  d_tags Ψ C ->
  forall ε1 ε2 Ψs, Ψs [=] swap_atoms ε1 ε2 Ψ ->
  d_tags Ψs (swap_etag_in_utyp ε1 ε2 C).
Proof.
  intros Ψ C H; induction H; intros ε1 ε2 Ψs Heq; simpl.
  - apply d_tags__unit. eapply swap_atoms_empty_of; eassumption.
  - apply d_tags__var. eapply swap_atoms_empty_of; eassumption.
  - apply d_tags__arrow with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
                             (Ψ2 := swap_atoms ε1 ε2 Ψ2);
      [ apply IHd_tags1; reflexivity | apply IHd_tags2; reflexivity
      | apply swap_atoms_disjoint_of; assumption
      | eapply swap_atoms_union_of; eassumption ].
  - apply d_tags__all_etag with (L := L) (Ψ0 := swap_atoms ε1 ε2 Ψ0).
    + intros α Hα. rewrite <- swap_etag_in_utyp_open_var.
      apply H0; [ exact Hα | reflexivity ].
    + apply swap_atoms_notin_of; assumption.
    + eapply swap_atoms_add_of; eassumption.
Qed.

Lemma d_tags_skl_swap_etag : forall Ψ R,
  d_tags_skl Ψ R ->
  forall ε1 ε2 Ψs, Ψs [=] swap_atoms ε1 ε2 Ψ ->
  d_tags_skl Ψs (swap_etag_in_uskl ε1 ε2 R).
Proof.
  intros Ψ R H; induction H; intros ε1 ε2 Ψs Heq; simpl.
  - apply d_tags_skl__unit. eapply swap_atoms_empty_of; eassumption.
  - apply d_tags_skl__var. eapply swap_atoms_empty_of; eassumption.
  - apply d_tags_skl__arrow with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
                                 (Ψ2 := swap_atoms ε1 ε2 Ψ2);
      [ apply IHd_tags_skl1; reflexivity | apply IHd_tags_skl2; reflexivity
      | apply swap_atoms_disjoint_of; assumption
      | eapply swap_atoms_union_of; eassumption ].
  - apply d_tags_skl__all_etag with (L := L) (Ψ0 := swap_atoms ε1 ε2 Ψ0).
    + intros α Hα. rewrite <- swap_etag_in_uskl_open_var.
      apply H0; [ exact Hα | reflexivity ].
    + apply swap_atoms_notin_of; assumption.
    + eapply swap_atoms_add_of; eassumption.
  - apply d_tags_skl__holeg. eapply swap_atoms_empty_of; eassumption.
  - apply d_tags_skl__topholeg. apply IHd_tags_skl; assumption.
Qed.

(** Well-scopedness cannot see a tag at all. *)
Lemma d_wf_utyp_swap_etag : forall Γ C,
  d_wf_utyp Γ C -> forall ε1 ε2, d_wf_utyp Γ (swap_etag_in_utyp ε1 ε2 C).
Proof.
  intros Γ C H; induction H; intros ε1 ε2; simpl;
    try solve [ constructor; auto ].
  - apply d_wf_utyp__all_syn with (L := L). intros α Hα.
    rewrite <- swap_etag_in_utyp_open_var. auto.
  - apply d_wf_utyp__all_etag with (L := L) (ε := swap_atom ε1 ε2 ε).
    intros α Hα. rewrite <- swap_etag_in_utyp_open_var. auto.
Qed.

Lemma d_wf_uskl_swap_etag : forall Γ Δ R,
  d_wf_uskl Γ Δ R -> forall ε1 ε2, d_wf_uskl Γ Δ (swap_etag_in_uskl ε1 ε2 R).
Proof.
  intros Γ Δ R H; induction H; intros ε1 ε2; simpl;
    try solve [ constructor; auto ].
  - apply d_wf_uskl__all_syn with (L := L). intros α Hα.
    rewrite <- swap_etag_in_uskl_open_var. auto.
  - apply d_wf_uskl__all_etag with (L := L) (ε := swap_atom ε1 ε2 ε).
    intros α Hα. rewrite <- swap_etag_in_uskl_open_var. auto.
  - apply d_wf_uskl__tophole;
      [ apply guarded_uskl_swap_etag; assumption | auto ].
  - apply d_wf_uskl__topholeg;
      [ apply guarded_uskl_swap_etag; assumption | auto ].
Qed.

(* ===================================================================== *)
(*  §2  CONSISTENCY AND SUBTYPING, both sorts                             *)
(* ===================================================================== *)

Lemma d_consis_swap_etag : forall Ψ Γ C B,
  d_consis Ψ Γ C B ->
  forall ε1 ε2 Ψs, Ψs [=] swap_atoms ε1 ε2 Ψ ->
  d_consis Ψs Γ (swap_etag_in_utyp ε1 ε2 C) B.
Proof.
  intros Ψ Γ C B H; induction H; intros ε1 ε2 Ψs Heq; simpl.
  - apply d_consis__unit. eapply swap_atoms_empty_of; eassumption.
  - apply d_consis__var;
      [ assumption | eapply swap_atoms_empty_of; eassumption ].
  - apply d_consis__arrow with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
                               (Ψ2 := swap_atoms ε1 ε2 Ψ2);
      [ apply IHd_consis1; reflexivity | apply IHd_consis2; reflexivity
      | eapply swap_atoms_union_of; eassumption ].
  - apply d_consis__forall_inh_tagged
      with (L := L) (Ψ0 := swap_atoms ε1 ε2 Ψ0);
      [ | eapply swap_atoms_add_of; eassumption ].
    intros α Hα. rewrite <- swap_etag_in_utyp_open_var.
    apply H0; [ exact Hα | reflexivity ].
  - apply d_consis__forall_inh_untagged with (L := L). intros α Hα.
    rewrite <- swap_etag_in_utyp_open_var. apply H0; [ exact Hα | exact Heq ].
  - apply d_consis__forall_syn_tagged with (L := L). intros α Hα.
    rewrite <- swap_etag_in_utyp_open_var. apply H0; [ exact Hα | exact Heq ].
  - apply d_consis__forall_syn with (L := L). intros α Hα.
    rewrite <- swap_etag_in_utyp_open_var. apply H0; [ exact Hα | exact Heq ].
Qed.

Lemma d_pat_consis_swap_etag : forall Ψ Γ R Q,
  d_pat_consis Ψ Γ R Q ->
  forall ε1 ε2 Ψs, Ψs [=] swap_atoms ε1 ε2 Ψ ->
  d_pat_consis Ψs Γ (swap_etag_in_uskl ε1 ε2 R) Q.
Proof.
  intros Ψ Γ R Q H; induction H; intros ε1 ε2 Ψs Heq; simpl.
  - apply d_pat_consis__unit. eapply swap_atoms_empty_of; eassumption.
  - apply d_pat_consis__var;
      [ eapply swap_atoms_empty_of; eassumption | assumption ].
  - apply d_pat_consis__arrow with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
                                   (Ψ2 := swap_atoms ε1 ε2 Ψ2);
      [ apply IHd_pat_consis1; reflexivity
      | apply IHd_pat_consis2; reflexivity
      | eapply swap_atoms_union_of; eassumption ].
  - apply d_pat_consis__forall_inh_tagged
      with (L := L) (Ψ0 := swap_atoms ε1 ε2 Ψ0);
      [ | eapply swap_atoms_add_of; eassumption ].
    intros α Hα. rewrite <- swap_etag_in_uskl_open_var.
    apply H0; [ exact Hα | reflexivity ].
  - apply d_pat_consis__forall_inh_untagged with (L := L). intros α Hα.
    rewrite <- swap_etag_in_uskl_open_var. apply H0; [ exact Hα | exact Heq ].
  - apply d_pat_consis__forall_syn_tagged with (L := L). intros α Hα.
    rewrite <- swap_etag_in_uskl_open_var. apply H0; [ exact Hα | exact Heq ].
  - apply d_pat_consis__forall_syn with (L := L). intros α Hα.
    rewrite <- swap_etag_in_uskl_open_var. apply H0; [ exact Hα | exact Heq ].
  - apply d_pat_consis__ghostg. eapply swap_atoms_empty_of; eassumption.
  - apply d_pat_consis__topholeg. apply IHd_pat_consis; exact Heq.
  - apply d_pat_consis__hole;
      [ eapply swap_atoms_empty_of; eassumption | assumption ].
  - apply d_pat_consis__tophole. apply IHd_pat_consis; exact Heq.
  - apply d_pat_consis__tophole_inh with (L := L). intros α Hα.
    change (uskl_tophole (swap_etag_in_uskl ε1 ε2 R))
      with (swap_etag_in_uskl ε1 ε2 (uskl_tophole R)).
    apply H0; [ exact Hα | exact Heq ].
  - apply d_pat_consis__tophole_drop. apply IHd_pat_consis; exact Heq.
Qed.

Lemma d_sub_swap_etag : forall M Ψ Γ C B,
  d_sub M Ψ Γ C B ->
  forall ε1 ε2 Ψs, Ψs [=] swap_atoms ε1 ε2 Ψ ->
  d_sub M Ψs Γ (swap_etag_in_utyp ε1 ε2 C) B.
Proof.
  intros M Ψ Γ C B H; induction H; intros ε1 ε2 Ψs Heq; simpl.
  - apply d_sub__infer;
      [ eapply d_consis_swap_etag;
          [ eassumption | symmetry; apply swap_atoms_empty ]
      | assumption | eapply swap_atoms_empty_of; eassumption ].
  - apply d_sub__check;
      [ apply guarded_utyp_swap_etag; assumption | assumption
      | eapply d_consis_swap_etag; [ eassumption | exact Heq ]
      | assumption ].
  - apply d_sub__forall_r with (L := L);
      [ assumption | intros α Hα; apply H1; [ exact Hα | exact Heq ] ].
  - apply d_sub__arg with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
                          (Ψ2 := swap_atoms ε1 ε2 Ψ2);
      [ eapply d_consis_swap_etag; [ eassumption | reflexivity ]
      | apply IHd_sub; reflexivity
      | eapply swap_atoms_union_of; eassumption ].
  - apply d_sub__forall_l_tagged
      with (Ψ' := swap_atoms ε1 ε2 Ψ') (ph := swap_etag_in_utyp ε1 ε2 ph).
    + assumption.
    + rewrite Heq. apply swap_atoms_disjoint_of; assumption.
    + rewrite (ftag_swap_etag_in_utyp ε1 ε2 (utyp_all_etag ε C)).
      apply swap_atoms_disjoint_of; assumption.
    + eapply d_tags_swap_etag; [ eassumption | reflexivity ].
    + apply d_wf_utyp_swap_etag; assumption.
    + apply is_ttyp_swap_etag; assumption.
    + rewrite <- swap_etag_in_utyp_open. apply IHd_sub.
      rewrite Heq. symmetry. apply swap_atoms_union.
  - apply d_sub__forall_l_untagged
      with (Ψ' := swap_atoms ε1 ε2 Ψ') (ph := swap_etag_in_utyp ε1 ε2 ph).
    + assumption.
    + rewrite Heq. apply swap_atoms_disjoint_of; assumption.
    + rewrite (ftag_swap_etag_in_utyp ε1 ε2 (utyp_all_syn C)).
      apply swap_atoms_disjoint_of; assumption.
    + eapply d_tags_swap_etag; [ eassumption | reflexivity ].
    + apply d_wf_utyp_swap_etag; assumption.
    + apply is_ttyp_swap_etag; assumption.
    + rewrite <- swap_etag_in_utyp_open. apply IHd_sub.
      rewrite Heq. symmetry. apply swap_atoms_union.
Qed.

Lemma d_pat_sub_swap_etag : forall M Ψ Γ R Q,
  d_pat_sub M Ψ Γ R Q ->
  forall ε1 ε2 Ψs, Ψs [=] swap_atoms ε1 ε2 Ψ ->
  d_pat_sub M Ψs Γ (swap_etag_in_uskl ε1 ε2 R) Q.
Proof.
  intros M Ψ Γ R Q H; induction H; intros ε1 ε2 Ψs Heq; simpl.
  - apply d_pat_sub__infer;
      [ eapply swap_atoms_empty_of; eassumption
      | eapply d_pat_consis_swap_etag;
          [ eassumption | symmetry; apply swap_atoms_empty ]
      | assumption ].
  - apply d_pat_sub__univ_ghost_r;
      [ eapply swap_atoms_empty_of; eassumption
      | apply guarded_uskl_swap_etag; assumption | assumption | assumption
      | eapply d_pat_consis_swap_etag;
          [ eassumption | symmetry; apply swap_atoms_empty ] ].
  - apply d_pat_sub__arg with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
                              (Ψ2 := swap_atoms ε1 ε2 Ψ2);
      [ eapply d_pat_consis_swap_etag; [ eassumption | reflexivity ]
      | apply IHd_pat_sub; reflexivity
      | eapply swap_atoms_union_of; eassumption ].
  - apply d_pat_sub__forall_l_tagged
      with (Ψ' := swap_atoms ε1 ε2 Ψ') (psi := swap_etag_in_uskl ε1 ε2 psi).
    + assumption.
    + rewrite Heq. apply swap_atoms_disjoint_of; assumption.
    + rewrite (ftag_swap_etag_in_uskl ε1 ε2 (uskl_all_etag ε R)).
      apply swap_atoms_disjoint_of; assumption.
    + eapply d_tags_skl_swap_etag; [ eassumption | reflexivity ].
    + apply d_wf_uskl_swap_etag; assumption.
    + apply is_tskl_swap_etag; assumption.
    + rewrite <- swap_etag_in_uskl_open. apply IHd_pat_sub.
      rewrite Heq. symmetry. apply swap_atoms_union.
  - apply d_pat_sub__forall_l_untagged
      with (Ψ' := swap_atoms ε1 ε2 Ψ') (psi := swap_etag_in_uskl ε1 ε2 psi).
    + assumption.
    + rewrite Heq. apply swap_atoms_disjoint_of; assumption.
    + rewrite (ftag_swap_etag_in_uskl ε1 ε2 (uskl_all_syn R)).
      apply swap_atoms_disjoint_of; assumption.
    + eapply d_tags_skl_swap_etag; [ eassumption | reflexivity ].
    + apply d_wf_uskl_swap_etag; assumption.
    + apply is_tskl_swap_etag; assumption.
    + rewrite <- swap_etag_in_uskl_open. apply IHd_pat_sub.
      rewrite Heq. symmetry. apply swap_atoms_union.
  - apply d_pat_sub__ghost;
      [ eapply swap_atoms_empty_of; eassumption | assumption | assumption ].
  - apply d_pat_sub__univ_ghost_l; [ assumption | apply IHd_pat_sub; exact Heq ].
  - apply d_pat_sub__ghostg;
      [ eapply swap_atoms_empty_of; eassumption | assumption ].
  - apply d_pat_sub__univ_ghost_lg;
      [ assumption | apply IHd_pat_sub; exact Heq ].
Qed.

(* ===================================================================== *)
(*  §3  FRESHENING — what the strong reading of [Ψ' fresh] costs, which    *)
(*  is nothing.                                                           *)
(*                                                                        *)
(*  ⭐ The point of the whole file.  A ForallL node's instantiation tags    *)
(*  can be moved out of ANY finite set, one transposition at a time, and   *)
(*  the measure that decreases is the cardinality of the tags still in the *)
(*  way.  The conclusion is untouched: the swaps only ever exchange a tag  *)
(*  of the instantiation (which lives in the SUBSTITUTED subject, not in   *)
(*  the rule's conclusion) with a globally fresh one.                      *)
(* ===================================================================== *)

Lemma d_sub_freshen_forall_l_aux : forall k Ψ Ψ' Γ m C ph B S,
  cardinal (Ψ' ∩ S) <= k ->
  (Ψ `union` Ψ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⩽ B ->
  d_tags Ψ' ph -> Γ ⊢ᵤ ph -> is_ttyp ph ->
  Ψ' ∩ Ψ [=] empty ->
  Ψ' ∩ (ftag_in_utyp C) [=] empty ->
  exists Ψ'' ph'',
    Ψ'' ∩ Ψ [=] empty /\ Ψ'' ∩ (ftag_in_utyp C) [=] empty /\
    Ψ'' ∩ S [=] empty /\
    d_tags Ψ'' ph'' /\ Γ ⊢ᵤ ph'' /\ is_ttyp ph'' /\
    (Ψ `union` Ψ'') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph'') ⩽ B.
Proof.
  induction k; intros Ψ Ψ' Γ m C ph B S Hk Hsub Ht Hwf Htt Hd1 Hd2;
    destruct (choose (Ψ' ∩ S)) as [ ε1 | ] eqn:Hch.
  - (* no fuel left, but a tag still in the way: impossible *)
    exfalso. apply choose_1 in Hch.
    assert (HE : Empty (Ψ' ∩ S)) by (apply cardinal_Empty; lia).
    exact (HE ε1 Hch).
  - apply choose_2 in Hch. exists Ψ', ph.
    split; [ exact Hd1 | ]. split; [ exact Hd2 | ].
    split; [ apply AtomSetProperties.empty_is_empty_1; exact Hch | ].
    split; [ exact Ht | ]. split; [ exact Hwf | ]. split; [ exact Htt | ].
    exact Hsub.
  - (* ⭐ THE STEP: ε1 is a tag of the instantiation that S also owns.
       Exchange it with a globally fresh ε2 and recurse. *)
    apply choose_1, AtomSetFacts.inter_iff in Hch as [ Hin1 HinS ].
    pick fresh ε2 for (Ψ `union` Ψ' `union` S `union` ftag_in_utyp C).
    assert (Hε1Ψ : ε1 `notin` Ψ) by (clear - Hin1 Hd1; fsetdec).
    assert (Hε1C : ε1 `notin` ftag_in_utyp C) by (clear - Hin1 Hd2; fsetdec).
    (* the subject's OWN tags are untouched, so only the instantiation moves *)
    assert (HC : swap_etag_in_utyp ε1 ε2 C = C)
      by (apply swap_etag_in_utyp_fresh_eq;
            [ exact Hε1C | clear - Fr; fsetdec ]).
    assert (Hsub' : (Ψ `union` (swap_atoms ε1 ε2 Ψ')) ⨟ Γ
                      ⊢[ m ] (open_utyp_wrt_utyp C (swap_etag_in_utyp ε1 ε2 ph))
                      ⩽ B).
    { pose proof (d_sub_swap_etag m (Ψ `union` Ψ') Γ
                    (open_utyp_wrt_utyp C ph) B Hsub ε1 ε2
                    (Ψ `union` (swap_atoms ε1 ε2 Ψ'))
                    ltac:(rewrite swap_atoms_union,
                            (swap_atoms_notin ε1 ε2 Ψ Hε1Ψ
                               ltac:(clear - Fr; fsetdec));
                          reflexivity)) as Hx.
      rewrite swap_etag_in_utyp_open, HC in Hx. exact Hx. }
    apply (IHk Ψ (swap_atoms ε1 ε2 Ψ') Γ m C
             (swap_etag_in_utyp ε1 ε2 ph) B S).
    + assert (Hlt : cardinal ((swap_atoms ε1 ε2 Ψ') ∩ S)
                    < cardinal (Ψ' ∩ S))
        by (apply swap_atoms_shrink;
              [ exact Hin1 | exact HinS | clear - Fr; fsetdec
              | clear - Fr; fsetdec ]).
      lia.
    + exact Hsub'.
    + eapply d_tags_swap_etag; [ exact Ht | reflexivity ].
    + apply d_wf_utyp_swap_etag; exact Hwf.
    + apply is_ttyp_swap_etag; exact Htt.
    + apply swap_atoms_disjoint_keep;
        [ exact Hd1 | exact Hε1Ψ | clear - Fr; fsetdec ].
    + apply swap_atoms_disjoint_keep;
        [ exact Hd2 | exact Hε1C | clear - Fr; fsetdec ].
  - apply choose_2 in Hch. exists Ψ', ph.
    split; [ exact Hd1 | ]. split; [ exact Hd2 | ].
    split; [ apply AtomSetProperties.empty_is_empty_1; exact Hch | ].
    split; [ exact Ht | ]. split; [ exact Hwf | ]. split; [ exact Htt | ].
    exact Hsub.
Qed.

(** ⭐ THE PER-NODE FRESHENING.  A ForallL node's instantiation can always be
    re-tagged away from any finite set — so the GLOBAL reading of the paper's
    `Ψ' fresh` (the two premises the rules carry) costs no derivations.

    ⚙ NO CONSUMER TODAY, and kept deliberately: it is the statement §4-§5 had
    to be invented to get around (see the header), and it is INCOMPARABLE with
    §5's wholesale version, which reaches a whole derivation but only when the
    CONCLUSION is tag-free.  This one asks nothing of the conclusion. *)
Lemma d_sub_freshen_forall_l : forall Ψ Ψ' Γ m C ph B S,
  (Ψ `union` Ψ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⩽ B ->
  d_tags Ψ' ph -> Γ ⊢ᵤ ph -> is_ttyp ph ->
  Ψ' ∩ Ψ [=] empty ->
  Ψ' ∩ (ftag_in_utyp C) [=] empty ->
  exists Ψ'' ph'',
    Ψ'' ∩ Ψ [=] empty /\ Ψ'' ∩ (ftag_in_utyp C) [=] empty /\
    Ψ'' ∩ S [=] empty /\
    d_tags Ψ'' ph'' /\ Γ ⊢ᵤ ph'' /\ is_ttyp ph'' /\
    (Ψ `union` Ψ'') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph'') ⩽ B.
Proof.
  intros Ψ Ψ' Γ m C ph B S.
  apply (d_sub_freshen_forall_l_aux (cardinal (Ψ' ∩ S))). lia.
Qed.

(* ===================================================================== *)
(*  §4  THE TAGS-BOUND TWIN [d_sub_tagsin U] — what lets an INDUCTION     *)
(*  apply §2's equivariance.                                              *)
(*                                                                        *)
(*  ⭐ §3 freshens ONE node from that node's own data, and no structural   *)
(*  induction chains those steps: at a ForallL node the IH is tied to the  *)
(*  ORIGINAL instantiation, while freshening yields a derivation of a      *)
(*  DIFFERENT statement.  The way out is to stop freshening node by node.  *)
(*  COLLECT every ForallL's Ψ' into one bound [U] first — a plain          *)
(*  induction, no renaming — and then move [U] wholesale with a single     *)
(*  chain of transpositions.  §5 does the moving; it is legitimate exactly *)
(*  when the CONCLUSION is tag-free, because then no swap touches it.      *)
(*                                                                        *)
(*  ⚙ [__forall_r] is EXISTS-FRESH here where [d_sub]'s is cofinite.  The  *)
(*  collection has to produce ONE [U] for the whole rule, and a cofinite   *)
(*  premise would demand a bound uniform in infinitely many α — so naming  *)
(*  the atom makes [d_sub_to_tagsin] a one-liner, and the forgetful        *)
(*  direction pays for it with the renaming lemma the tree already has     *)
(*  ([d_sub_rename_tvar], decl/prop_renaming.v).                           *)
(* ===================================================================== *)

Inductive d_sub_tagsin :
  atoms -> mode -> atoms -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_sub_tagsin__infer : forall U Ψ Γ C B,
    empty ⨟ Γ ⊢ C ∼ B ->
    is_styp B ->
    Ψ [=] empty ->
    d_sub_tagsin U mode_ti Ψ Γ C B
| d_sub_tagsin__check : forall U Ψ Γ C B,
    guarded_utyp C ->
    guarded_btyp B ->
    Ψ ⨟ Γ ⊢ C ∼ B ->
    is_ityp B ->
    d_sub_tagsin U mode_tc Ψ Γ C B
| d_sub_tagsin__forall_r : forall U α Ψ Γ C B,
    is_ityp (btyp_all_inh B) ->
    α `notin` (dom Γ `union` ftvar_in_utyp C `union` ftvar_in_btyp B) ->
    d_sub_tagsin U mode_tc Ψ ((α ~ dbind_tvar) ++ Γ) C
      (open_btyp_wrt_btyp B (btyp_var_f α)) ->
    d_sub_tagsin U mode_tc Ψ Γ C (btyp_all_inh B)
| d_sub_tagsin__arg : forall U Ψ Ψ1 Ψ2 Γ m C1 C2 B1 B2,
    Ψ1 ⨟ Γ ⊢ C1 ∼ B1 ->
    d_sub_tagsin U m Ψ2 Γ C2 B2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    d_sub_tagsin U (mode_fn m) Ψ Γ (utyp_arrow C1 C2) (btyp_arrow B1 B2)
| d_sub_tagsin__forall_l_tagged : forall U Ψ Ψ' Γ m ε C ph B,
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_utyp (utyp_all_etag ε C)) [=] empty ->
    Ψ' [<=] U ->                     (* ⭐ the ONE premise [d_sub] does not have *)
    d_tags Ψ' ph ->
    Γ ⊢ᵤ ph ->
    is_ttyp ph ->
    d_sub_tagsin U m (Ψ `union` Ψ') Γ (open_utyp_wrt_utyp C ph) B ->
    d_sub_tagsin U m Ψ Γ (utyp_all_etag ε C) B
| d_sub_tagsin__forall_l_untagged : forall U Ψ Ψ' Γ m C ph B,
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_utyp (utyp_all_syn C)) [=] empty ->
    Ψ' [<=] U ->
    d_tags Ψ' ph ->
    Γ ⊢ᵤ ph ->
    is_ttyp ph ->
    d_sub_tagsin U m (Ψ `union` Ψ') Γ (open_utyp_wrt_utyp C ph) B ->
    d_sub_tagsin U m Ψ Γ (utyp_all_syn C) B.

(** The bound only ever needs to grow. *)
Lemma d_sub_tagsin_weaken : forall U m Ψ Γ C B,
  d_sub_tagsin U m Ψ Γ C B -> forall U', U [<=] U' -> d_sub_tagsin U' m Ψ Γ C B.
Proof.
  intros U m Ψ Γ C B H; induction H; intros U' Hle.
  - apply d_sub_tagsin__infer; assumption.
  - apply d_sub_tagsin__check; assumption.
  - apply d_sub_tagsin__forall_r with (α := α);
      [ assumption | assumption | apply IHd_sub_tagsin; exact Hle ].
  - apply d_sub_tagsin__arg with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ assumption | apply IHd_sub_tagsin; exact Hle | assumption ].
  - apply d_sub_tagsin__forall_l_tagged with (Ψ' := Ψ') (ph := ph);
      [ assumption | assumption | assumption | clear - H2 Hle; fsetdec
      | assumption | assumption | assumption | apply IHd_sub_tagsin; exact Hle ].
  - apply d_sub_tagsin__forall_l_untagged with (Ψ' := Ψ') (ph := ph);
      [ assumption | assumption | assumption | clear - H2 Hle; fsetdec
      | assumption | assumption | assumption | apply IHd_sub_tagsin; exact Hle ].
Qed.

(** FORGET the bound.  The one step that is not a constructor application is
    [__forall_r], where the exists-fresh premise has to be regenerated into
    [d_sub]'s cofinite family — exactly what [d_sub_rename_tvar] is for.

    ⚙ No consumer: CST goes the other way ([d_sub_to_tagsin]).  It is here as
    the ROUND-TRIP CERTIFICATE — with it, [d_sub_tagsin U] provably describes
    exactly the [d_sub] derivations whose ForallL tags fit in [U], so the
    exists-fresh [__forall_r] above is a presentation choice and not a
    strengthening. *)
Lemma d_sub_tagsin_of : forall U m Ψ Γ C B,
  d_sub_tagsin U m Ψ Γ C B -> Ψ ⨟ Γ ⊢[ m ] C ⩽ B.
Proof.
  intros U m Ψ Γ C B H; induction H.
  - apply d_sub__infer; assumption.
  - apply d_sub__check; assumption.
  - apply d_sub__forall_r with
      (L := dom Γ `union` ftvar_in_utyp C `union` ftvar_in_btyp B
            `union` singleton α);
      [ assumption | ].
    intros β Hβ.
    rewrite (subst_btyp_in_btyp_intro α) by (clear - H0; fsetdec).
    rewrite <- (subst_utyp_in_utyp_fresh_eq C (utyp_var_f β) α)
      by (clear - H0; fsetdec).
    apply (@d_sub_rename_tvar _ _ _ _ _ IHd_sub_tagsin nil Γ α β);
      [ reflexivity | simpl; clear - H0 Hβ; fsetdec ].
  - apply d_sub__arg with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
  - apply d_sub__forall_l_tagged with (Ψ' := Ψ') (ph := ph); assumption.
  - apply d_sub__forall_l_untagged with (Ψ' := Ψ') (ph := ph); assumption.
Qed.

(** ⭐ COLLECT the bound.  A plain induction — the union of the sub-derivation's
    bound with this node's own [Ψ'] — with NO freshening anywhere; that is the
    whole point of separating collection from moving. *)
Lemma d_sub_to_tagsin : forall m Ψ Γ C B,
  Ψ ⨟ Γ ⊢[ m ] C ⩽ B -> exists U, d_sub_tagsin U m Ψ Γ C B.
Proof.
  intros m Ψ Γ C B H; induction H.
  - exists empty. apply d_sub_tagsin__infer; assumption.
  - exists empty. apply d_sub_tagsin__check; assumption.
  - pick fresh α0 for
      (L `union` dom Γ `union` ftvar_in_utyp C `union` ftvar_in_btyp B).
    destruct (H1 α0 ltac:(solve_notin_auto)) as [ U HU ].
    exists U. apply d_sub_tagsin__forall_r with (α := α0);
      [ assumption | clear - Fr; solve_notin_auto | exact HU ].
  - destruct IHd_sub as [ U HU ]. exists U.
    apply d_sub_tagsin__arg with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
  - destruct IHd_sub as [ U HU ]. exists (U `union` Ψ').
    apply d_sub_tagsin__forall_l_tagged with (Ψ' := Ψ') (ph := ph);
      [ assumption | assumption | assumption | clear; fsetdec
      | assumption | assumption | assumption
      | eapply d_sub_tagsin_weaken; [ exact HU | clear; fsetdec ] ].
  - destruct IHd_sub as [ U HU ]. exists (U `union` Ψ').
    apply d_sub_tagsin__forall_l_untagged with (Ψ' := Ψ') (ph := ph);
      [ assumption | assumption | assumption | clear; fsetdec
      | assumption | assumption | assumption
      | eapply d_sub_tagsin_weaken; [ exact HU | clear; fsetdec ] ].
Qed.

(** Equivariance of the twin — §2's [d_sub_swap_etag] with the bound carried
    along.  [__forall_r]'s side condition is about TYPE variables, which a
    tag swap cannot see ([ftvar_swap_etag_in_utyp]). *)
Lemma d_sub_tagsin_swap_etag : forall U m Ψ Γ C B,
  d_sub_tagsin U m Ψ Γ C B ->
  forall ε1 ε2 Us Ψs,
    Us [=] swap_atoms ε1 ε2 U -> Ψs [=] swap_atoms ε1 ε2 Ψ ->
    d_sub_tagsin Us m Ψs Γ (swap_etag_in_utyp ε1 ε2 C) B.
Proof.
  intros U m Ψ Γ C B H; induction H; intros ε1 ε2 Us Ψs HU Heq; simpl.
  - apply d_sub_tagsin__infer;
      [ eapply d_consis_swap_etag;
          [ eassumption | symmetry; apply swap_atoms_empty ]
      | assumption | eapply swap_atoms_empty_of; eassumption ].
  - apply d_sub_tagsin__check;
      [ apply guarded_utyp_swap_etag; assumption | assumption
      | eapply d_consis_swap_etag; [ eassumption | exact Heq ]
      | assumption ].
  - apply d_sub_tagsin__forall_r with (α := α);
      [ assumption
      | rewrite ftvar_swap_etag_in_utyp; assumption
      | apply IHd_sub_tagsin; assumption ].
  - apply d_sub_tagsin__arg with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
                                 (Ψ2 := swap_atoms ε1 ε2 Ψ2);
      [ eapply d_consis_swap_etag; [ eassumption | reflexivity ]
      | apply IHd_sub_tagsin; [ exact HU | reflexivity ]
      | eapply swap_atoms_union_of; eassumption ].
  - apply d_sub_tagsin__forall_l_tagged
      with (Ψ' := swap_atoms ε1 ε2 Ψ') (ph := swap_etag_in_utyp ε1 ε2 ph).
    + assumption.
    + rewrite Heq. apply swap_atoms_disjoint_of; assumption.
    + rewrite (ftag_swap_etag_in_utyp ε1 ε2 (utyp_all_etag ε C)).
      apply swap_atoms_disjoint_of; assumption.
    + rewrite HU. apply swap_atoms_subset_of; assumption.
    + eapply d_tags_swap_etag; [ eassumption | reflexivity ].
    + apply d_wf_utyp_swap_etag; assumption.
    + apply is_ttyp_swap_etag; assumption.
    + rewrite <- swap_etag_in_utyp_open. apply IHd_sub_tagsin;
        [ exact HU | rewrite Heq; symmetry; apply swap_atoms_union ].
  - apply d_sub_tagsin__forall_l_untagged
      with (Ψ' := swap_atoms ε1 ε2 Ψ') (ph := swap_etag_in_utyp ε1 ε2 ph).
    + assumption.
    + rewrite Heq. apply swap_atoms_disjoint_of; assumption.
    + rewrite (ftag_swap_etag_in_utyp ε1 ε2 (utyp_all_syn C)).
      apply swap_atoms_disjoint_of; assumption.
    + rewrite HU. apply swap_atoms_subset_of; assumption.
    + eapply d_tags_swap_etag; [ eassumption | reflexivity ].
    + apply d_wf_utyp_swap_etag; assumption.
    + apply is_ttyp_swap_etag; assumption.
    + rewrite <- swap_etag_in_utyp_open. apply IHd_sub_tagsin;
        [ exact HU | rewrite Heq; symmetry; apply swap_atoms_union ].
Qed.

(* ===================================================================== *)
(*  §5  WHOLESALE FRESHENING.                                             *)
(*                                                                        *)
(*  ⭐ The payoff.  Once the derivation's instantiation tags are bounded   *)
(*  by one set [U], moving them off a chosen [S] is §3's iteration again — *)
(*  but now ONE transposition rewrites the WHOLE derivation at once, so    *)
(*  there is no induction hypothesis to feed a changed statement back to.  *)
(*  The side condition is on the CONCLUSION only: the swap must fix its    *)
(*  tag context and its subject, which it does as soon as [S] avoids both. *)
(* ===================================================================== *)

Lemma d_sub_tagsin_freshen_aux : forall k U m Ψ Γ C B S,
  cardinal (U ∩ S) <= k ->
  d_sub_tagsin U m Ψ Γ C B ->
  S ∩ Ψ [=] empty ->
  S ∩ (ftag_in_utyp C) [=] empty ->
  exists U', U' ∩ S [=] empty /\ d_sub_tagsin U' m Ψ Γ C B.
Proof.
  induction k; intros U m Ψ Γ C B S Hk Hsub HΨ HC;
    destruct (choose (U ∩ S)) as [ ε1 | ] eqn:Hch.
  - (* no fuel left, but a tag still in the way: impossible *)
    exfalso. apply choose_1 in Hch.
    assert (HE : Empty (U ∩ S)) by (apply cardinal_Empty; lia).
    exact (HE ε1 Hch).
  - apply choose_2 in Hch. exists U.
    split; [ apply AtomSetProperties.empty_is_empty_1; exact Hch | exact Hsub ].
  - (* ⭐ THE STEP: ε1 is bounded by U and in the way; exchange it for a
       globally fresh ε2.  The conclusion is fixed because S avoids both Ψ
       and the subject's tags, and ε1 ∈ S. *)
    apply choose_1, AtomSetFacts.inter_iff in Hch as [ Hin1U Hin1S ].
    pick fresh ε2 for (U `union` S `union` Ψ `union` ftag_in_utyp C).
    assert (Hε1Ψ : ε1 `notin` Ψ) by (clear - Hin1S HΨ; fsetdec).
    assert (Hε1C : ε1 `notin` ftag_in_utyp C) by (clear - Hin1S HC; fsetdec).
    assert (HCeq : swap_etag_in_utyp ε1 ε2 C = C)
      by (apply swap_etag_in_utyp_fresh_eq;
            [ exact Hε1C | clear - Fr; fsetdec ]).
    pose proof (d_sub_tagsin_swap_etag U m Ψ Γ C B Hsub ε1 ε2
                  (swap_atoms ε1 ε2 U) Ψ ltac:(reflexivity)
                  ltac:(symmetry; apply swap_atoms_notin;
                          [ exact Hε1Ψ | clear - Fr; fsetdec ])) as Hx.
    rewrite HCeq in Hx.
    apply (IHk (swap_atoms ε1 ε2 U) m Ψ Γ C B S);
      [ | exact Hx | exact HΨ | exact HC ].
    assert (Hlt : cardinal ((swap_atoms ε1 ε2 U) ∩ S) < cardinal (U ∩ S))
      by (apply swap_atoms_shrink;
            [ exact Hin1U | exact Hin1S | clear - Fr; fsetdec
            | clear - Fr; fsetdec ]).
    lia.
  - apply choose_2 in Hch. exists U.
    split; [ apply AtomSetProperties.empty_is_empty_1; exact Hch | exact Hsub ].
Qed.

(** ⭐ THE LEMMA THE BRIDGE CONSUMES.  Every ForallL instantiation of a
    subtyping derivation can be re-tagged away from any finite [S], provided
    [S] is disjoint from what the CONCLUSION mentions.  Compare §3, which
    moves ONE node and cannot be iterated through an induction. *)
Lemma d_sub_freshen : forall m Ψ Γ C B S,
  Ψ ⨟ Γ ⊢[ m ] C ⩽ B ->
  S ∩ Ψ [=] empty ->
  S ∩ (ftag_in_utyp C) [=] empty ->
  exists U, U ∩ S [=] empty /\ d_sub_tagsin U m Ψ Γ C B.
Proof.
  intros m Ψ Γ C B S H HΨ HC.
  destruct (d_sub_to_tagsin m Ψ Γ C B H) as [ U HU ].
  apply (d_sub_tagsin_freshen_aux (cardinal (U ∩ S)) U m Ψ Γ C B S);
    [ lia | exact HU | exact HΨ | exact HC ].
Qed.
