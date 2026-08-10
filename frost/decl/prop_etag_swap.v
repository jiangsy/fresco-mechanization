(** ε-TAG EQUIVARIANCE of the declarative judgments, and the ForallL
    FRESHENING it buys.

    ⭐ WHAT THIS IS FOR.  The paper's ForallL side condition is the single word
    *fresh* on the instantiation's tags Ψ', and the tree reads it TWO ways:
    [d_sub] / [d_pat_sub] / [ad_pat_sub] render it as freshness from the TAG
    CONTEXT ([Ψ' ∩ Ψ [=] ∅]), while the fuel mirrors [ad_pat_sub_g] / [_gv]
    additionally demand freshness from the SUBJECT's own tags — the GLOBAL
    reading, which is what [lemma:precision-substitution] needs and which the
    weak one does not give (Arrow splits the tag context but not the subject).
    Making all four agree is what a completeness corollary over the
    declarative system needs; see docs/PAPER-GAPS.md and
    docs/HANDOFF-closed-corollaries-declarative.md.

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

    ⚠️⚠️ WHAT IS STILL OWED, and why it is not more of the same.  §3 freshens
    ONE node, from that node's own data.  Rewriting a whole derivation into the
    global reading needs the freshened premise to be fed back to an induction
    hypothesis — and a STRUCTURAL induction cannot: at a ForallL node the IH is
    tied to the ORIGINAL instantiation [ph], while freshening produces a
    derivation of a DIFFERENT statement ([C[ph''] ⩽ B], not [C[ph] ⩽ B]).  The
    same wall appears in [d_consis_sub_trans_mid] (CST, prop_general_
    subsumption.v), whose ForallL case transports along [utyp_tag_refines],
    where the subject GAINS tags.  ⚠️ And the swap cannot be applied to the
    IH's OUTPUT either: there the instantiation's tags and the refined
    subject's tags sit in the SAME term ([T0[ph]]), so a transposition moves
    both.

    ⭐ THE MISSING PIECE, worked out but not built: a tags-BOUND twin
    [d_sub_tagsin U] ("every ForallL's Ψ' ⊆ U"), whose [d_sub_to_tagsin] is a
    plain collection induction (no freshening), plus its equivariance.  Then
    (i) CST takes [d_sub_tagsin U] and [ftag(C') ∩ U [=] ∅], and its ForallL
    case closes from [Ψ' ⊆ U] plus the node's own hygiene, under the invariant
    [ftag(C'_node) ⊆ ftag(C_node) ∪ ftag(C'_root)]; and (ii) the call sites
    discharge [ftag(C') ∩ U [=] ∅] by freshening the transported derivation
    wholesale — legitimate exactly there, because its conclusion
    ([∅ ⨟ Γ ⊢[M] ⌈B'⌉ˢ ⩽ B]) is TAG-FREE, so a transposition of two inner tags
    leaves it fixed.  §2's equivariance is what that step consumes.

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
    + eapply d_tags_swap_etag; [ eassumption | reflexivity ].
    + apply d_wf_utyp_swap_etag; assumption.
    + apply is_ttyp_swap_etag; assumption.
    + rewrite <- swap_etag_in_utyp_open. apply IHd_sub.
      rewrite Heq. symmetry. apply swap_atoms_union.
  - apply d_sub__forall_l_untagged
      with (Ψ' := swap_atoms ε1 ε2 Ψ') (ph := swap_etag_in_utyp ε1 ε2 ph).
    + assumption.
    + rewrite Heq. apply swap_atoms_disjoint_of; assumption.
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
    + eapply d_tags_skl_swap_etag; [ eassumption | reflexivity ].
    + apply d_wf_uskl_swap_etag; assumption.
    + apply is_tskl_swap_etag; assumption.
    + rewrite <- swap_etag_in_uskl_open. apply IHd_pat_sub.
      rewrite Heq. symmetry. apply swap_atoms_union.
  - apply d_pat_sub__forall_l_untagged
      with (Ψ' := swap_atoms ε1 ε2 Ψ') (psi := swap_etag_in_uskl ε1 ε2 psi).
    + assumption.
    + rewrite Heq. apply swap_atoms_disjoint_of; assumption.
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

(** ⭐ THE FRESHENING.  A ForallL node's instantiation can always be re-tagged
    away from any finite set — so the GLOBAL reading of the paper's
    `Ψ' fresh` (the two premises the rules carry) costs no derivations, and
    a transport whose subject gains tags can re-establish it. *)
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
