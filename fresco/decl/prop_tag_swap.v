(** ε-TAG EQUIVARIANCE of the declarative judgments, and the ForallL
    FRESHENING it buys.

    ⭐ WHAT THIS IS FOR.  The paper's ForallL side condition is the single word
    *fresh* on the instantiation's tags Ψ', and it means GLOBAL freshness —
    fresh from the SUBJECT's own tags too, not just from the tag context, which
    is what [lemma:precision-substitution] needs and what the context-local
    reading does not give (Arrow splits the tag context but not the subject).
    All four subtyping judgments — [d_sub], [d_pat_sub], [ad_pat_sub] and the
    fuel mirror [ad_pat_sub_fuel] — now render it that way, and THIS FILE
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
    well-scopedness and consistency; fresco/prop_tag.v has the syntactic layer.

    ⚠️⚠️ WHY EQUIVARIANCE ALONE IS NOT ENOUGH.  A ForallL node's instantiation
    can be moved out of any finite set one transposition at a time — but that
    step cannot be CHAINED through a structural induction: at a ForallL node
    the IH is tied to the ORIGINAL instantiation [ph], while freshening
    produces a derivation of a DIFFERENT statement ([C[ph''] ⩽ B], not
    [C[ph] ⩽ B]).  ⚠️ Nor can the swap be applied to the IH's OUTPUT: there the
    instantiation's tags and the refined subject's tags sit in the SAME term
    ([T0[ph]]), so a transposition moves both.

    ⭐ SO DO NOT FRESHEN NODE BY NODE.  §3 introduces the tags-BOUND twin
    [d_sub_tagsin U] ("every ForallL's Ψ' ⊆ U"), whose [d_sub_to_tagsin]
    COLLECTS the bound by a plain induction — no freshening anywhere — and §4
    then moves [U] WHOLESALE with a single chain of transpositions, which is
    legitimate whenever the CONCLUSION is tag-free (then no swap touches it).
    One swap now rewrites the whole derivation, so there is no changed
    statement to feed back.  CST consumes exactly that: it runs on
    [d_sub_tagsin U] against a tag-bounded refinement [utyp_tag_refines_in V],
    with ONE global [U ∩ V [=] ∅] discharging every node's hygiene at once, and
    its two call sites establish that from §4 because the transported
    derivation runs at the empty tag context with a PAINTED (hence tag-free)
    subject.

    ⚙ RESTART NOTE (2026-08-11) — three statements were DELETED as
    consumer-less once §3-§4 landed, and each is cheap to re-derive:
    [d_sub_swap_tag] and [d_pat_sub_swap_tag] (§3's [d_sub_tagsin_swap_tag]
    is the same proof with the [Ψ' ⊆ U] row carried, and [d_sub_to_tagsin]
    recovers the plain statement from it), together with [d_pat_consis_swap_tag]
    / [d_tags_skl_swap_tag] / [d_wf_uskl_swap_tag], which served only the
    skeleton one; [d_sub_freshen_forall_l], the per-node freshening the
    paragraph above explains cannot be chained; and [d_sub_tagsin_of], the
    twin's forgetful direction — CST goes the other way, and it was here only
    as the round-trip certificate (its one non-trivial step is regenerating
    [d_sub]'s cofinite [ForallR] from the twin's exists-fresh one, which is
    [d_sub_rename_tvar]).

    ⚙ Each equivariance statement threads its tag context as [Ψs [=] swap Ψ]
    rather than substituting, because the rules state their contexts up to
    [ [=] ]; the four re-derivations that needs are in fresco/prop_tag.v §3.

    ⚙ NO [Set Implicit Arguments], for the same reason as
    algo_decl/prop_conserv.v: the statements thread equations, and under the
    flag their set arguments would become strictly implicit. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_tag.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_weakening.
Require Import src.fresco.decl.prop_renaming.

(* ===================================================================== *)
(*  §1  THE LEAF JUDGMENTS: tag counting, and well-scopedness             *)
(* ===================================================================== *)

Lemma d_tags_swap_tag : forall Ψ C,
  d_tags Ψ C ->
  forall ε1 ε2 Ψs, Ψs [=] swap_atoms ε1 ε2 Ψ ->
  d_tags Ψs (swap_tag_in_utyp ε1 ε2 C).
Proof.
  intros Ψ C H; induction H; intros ε1 ε2 Ψs Heq; simpl.
  - apply d_tags__unit. eapply swap_atoms_empty_of; eassumption.
  - apply d_tags__var. eapply swap_atoms_empty_of; eassumption.
  - apply d_tags__arrow with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
                             (Ψ2 := swap_atoms ε1 ε2 Ψ2);
      [ apply IHd_tags1; reflexivity | apply IHd_tags2; reflexivity
      | apply swap_atoms_disjoint_of; assumption
      | eapply swap_atoms_union_of; eassumption ].
  - apply d_tags__all_tag with (L := L) (Ψ0 := swap_atoms ε1 ε2 Ψ0).
    + intros α Hα. rewrite <- swap_tag_in_utyp_open_var.
      apply H0; [ exact Hα | reflexivity ].
    + apply swap_atoms_notin_of; assumption.
    + eapply swap_atoms_add_of; eassumption.
Qed.

(** Well-scopedness cannot see a tag at all. *)
Lemma d_wf_utyp_swap_tag : forall Γ C,
  d_wf_utyp Γ C -> forall ε1 ε2, d_wf_utyp Γ (swap_tag_in_utyp ε1 ε2 C).
Proof.
  intros Γ C H; induction H; intros ε1 ε2; simpl;
    try solve [ constructor; auto ].
  - apply d_wf_utyp__all_syn with (L := L). intros α Hα.
    rewrite <- swap_tag_in_utyp_open_var. auto.
  - apply d_wf_utyp__all_tag with (L := L) (ε := swap_atom ε1 ε2 ε).
    intros α Hα. rewrite <- swap_tag_in_utyp_open_var. auto.
Qed.

(* ===================================================================== *)
(*  §2  CONSISTENCY                                                       *)
(* ===================================================================== *)

Lemma d_consis_swap_tag : forall Ψ Γ C B,
  d_consis Ψ Γ C B ->
  forall ε1 ε2 Ψs, Ψs [=] swap_atoms ε1 ε2 Ψ ->
  d_consis Ψs Γ (swap_tag_in_utyp ε1 ε2 C) B.
Proof.
  intros Ψ Γ C B H; induction H; intros ε1 ε2 Ψs Heq; simpl.
  - apply d_consis__unit. eapply swap_atoms_empty_of; eassumption.
  - apply d_consis__var;
      [ assumption | eapply swap_atoms_empty_of; eassumption ].
  - apply d_consis__forall_inh_tagged
      with (L := L) (Ψ0 := swap_atoms ε1 ε2 Ψ0);
      [ | eapply swap_atoms_add_of; eassumption ].
    intros α Hα. rewrite <- swap_tag_in_utyp_open_var.
    apply H0; [ exact Hα | reflexivity ].
  - apply d_consis__forall_inh_untagged with (L := L). intros α Hα.
    rewrite <- swap_tag_in_utyp_open_var. apply H0; [ exact Hα | exact Heq ].
  - apply d_consis__forall_syn_tagged with (L := L). intros α Hα.
    rewrite <- swap_tag_in_utyp_open_var. apply H0; [ exact Hα | exact Heq ].
  - apply d_consis__forall_syn with (L := L). intros α Hα.
    rewrite <- swap_tag_in_utyp_open_var. apply H0; [ exact Hα | exact Heq ].
  - apply d_consis__arrow with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
                               (Ψ2 := swap_atoms ε1 ε2 Ψ2);
      [ apply IHd_consis1; reflexivity | apply IHd_consis2; reflexivity
      | eapply swap_atoms_union_of; eassumption ].
Qed.

(* ===================================================================== *)
(*  §3  THE TAGS-BOUND TWIN [d_sub_tagsin U] — what lets an INDUCTION     *)
(*  apply §1-§2's equivariance to a WHOLE derivation.                      *)
(*                                                                        *)
(*  ⭐ Freshening a ForallL node from that node's own data cannot be        *)
(*  chained: at a ForallL node the IH is tied to the ORIGINAL              *)
(*  instantiation, while freshening yields a derivation of a DIFFERENT     *)
(*  statement.  So COLLECT every ForallL's Ψ' into one bound [U] first —   *)
(*  a plain induction, no renaming — and then move [U] wholesale with a    *)
(*  single chain of transpositions.  §4 does the moving; it is legitimate  *)
(*  exactly when the CONCLUSION is tag-free, because then no swap touches  *)
(*  it.                                                                    *)
(*                                                                        *)
(*  ⚙ [__forall_r] is EXISTS-FRESH here where [d_sub]'s is cofinite.  The  *)
(*  collection has to produce ONE [U] for the whole rule, and a cofinite   *)
(*  premise would demand a bound uniform in infinitely many α — so naming  *)
(*  the atom makes [d_sub_to_tagsin] a one-liner.  ⚠️ The price is paid by  *)
(*  the forgetful direction, which has to regenerate the cofinite family   *)
(*  ([d_sub_rename_tvar], decl/prop_renaming.v); see the header's RESTART  *)
(*  NOTE, where that direction is recorded rather than kept.               *)
(* ===================================================================== *)

Inductive d_sub_tagsin :
  atoms -> mode -> atoms -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_sub_tagsin__infer : forall U Ψ Γ C B,
    {{ empty ⨟ Γ ⊢ C ∼ B }}d ->
    is_styp B ->
    Ψ [=] empty ->
    d_sub_tagsin U mode_ti Ψ Γ C B
| d_sub_tagsin__check : forall U Ψ Γ C B,
    guarded_utyp C ->
    guarded_btyp B ->
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
    is_ityp B ->
    d_sub_tagsin U mode_tc Ψ Γ C B
| d_sub_tagsin__forall_r : forall U α Ψ Γ C B,
    is_ityp (btyp_all_inh B) ->
    α `notin` (dom Γ `union` ftvar_in_utyp C `union` ftvar_in_btyp B) ->
    d_sub_tagsin U mode_tc Ψ ((α ~ dbind_tvar) ++ Γ) C
      (open_btyp_wrt_btyp B (btyp_var_f α)) ->
    d_sub_tagsin U mode_tc Ψ Γ C (btyp_all_inh B)
| d_sub_tagsin__arg : forall U Ψ Ψ1 Ψ2 Γ m C1 C2 B1 B2,
    {{ Ψ1 ⨟ Γ ⊢ C1 ∼ B1 }}d ->
    d_sub_tagsin U m Ψ2 Γ C2 B2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    d_sub_tagsin U (mode_fn m) Ψ Γ (utyp_arrow C1 C2) (btyp_arrow B1 B2)
| d_sub_tagsin__forall_l_tagged : forall U Ψ Ψ' Γ m ε C ph B,
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_utyp (utyp_all_tag ε C)) [=] empty ->
    Ψ' [<=] U ->                     (* ⭐ the ONE premise [d_sub] does not have *)
    d_tags Ψ' ph ->
    {{ Γ ⊢ᵤ ph }}d ->
    is_dtyp ph ->
    d_sub_tagsin U m (Ψ `union` Ψ') Γ (open_utyp_wrt_utyp C ph) B ->
    d_sub_tagsin U m Ψ Γ (utyp_all_tag ε C) B
| d_sub_tagsin__forall_l_untagged : forall U Ψ Ψ' Γ m C ph B,
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_utyp (utyp_all_syn C)) [=] empty ->
    Ψ' [<=] U ->
    d_tags Ψ' ph ->
    {{ Γ ⊢ᵤ ph }}d ->
    is_dtyp ph ->
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

(** ⭐ COLLECT the bound.  A plain induction — the union of the sub-derivation's
    bound with this node's own [Ψ'] — with NO freshening anywhere; that is the
    whole point of separating collection from moving. *)
Lemma d_sub_to_tagsin : forall m Ψ Γ C B,
  {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d -> exists U, d_sub_tagsin U m Ψ Γ C B.
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

(** ⭐ EQUIVARIANCE OF THE TWIN — §1-§2 lifted to [d_sub] itself, with the
    bound carried along.  [__forall_r]'s side condition is about TYPE variables, which a
    tag swap cannot see ([ftvar_swap_tag_in_utyp]). *)
Lemma d_sub_tagsin_swap_tag : forall U m Ψ Γ C B,
  d_sub_tagsin U m Ψ Γ C B ->
  forall ε1 ε2 Us Ψs,
    Us [=] swap_atoms ε1 ε2 U -> Ψs [=] swap_atoms ε1 ε2 Ψ ->
    d_sub_tagsin Us m Ψs Γ (swap_tag_in_utyp ε1 ε2 C) B.
Proof.
  intros U m Ψ Γ C B H; induction H; intros ε1 ε2 Us Ψs HU Heq; simpl.
  - apply d_sub_tagsin__infer;
      [ eapply d_consis_swap_tag;
          [ eassumption | symmetry; apply swap_atoms_empty ]
      | assumption | eapply swap_atoms_empty_of; eassumption ].
  - apply d_sub_tagsin__check;
      [ apply guarded_utyp_swap_tag; assumption | assumption
      | eapply d_consis_swap_tag; [ eassumption | exact Heq ]
      | assumption ].
  - apply d_sub_tagsin__forall_r with (α := α);
      [ assumption
      | rewrite ftvar_swap_tag_in_utyp; assumption
      | apply IHd_sub_tagsin; assumption ].
  - apply d_sub_tagsin__arg with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
                                 (Ψ2 := swap_atoms ε1 ε2 Ψ2);
      [ eapply d_consis_swap_tag; [ eassumption | reflexivity ]
      | apply IHd_sub_tagsin; [ exact HU | reflexivity ]
      | eapply swap_atoms_union_of; eassumption ].
  - apply d_sub_tagsin__forall_l_tagged
      with (Ψ' := swap_atoms ε1 ε2 Ψ') (ph := swap_tag_in_utyp ε1 ε2 ph).
    + assumption.
    + rewrite Heq. apply swap_atoms_disjoint_of; assumption.
    + rewrite (ftag_swap_tag_in_utyp ε1 ε2 (utyp_all_tag ε C)).
      apply swap_atoms_disjoint_of; assumption.
    + rewrite HU. apply swap_atoms_subset_of; assumption.
    + eapply d_tags_swap_tag; [ eassumption | reflexivity ].
    + apply d_wf_utyp_swap_tag; assumption.
    + apply is_dtyp_swap_tag; assumption.
    + rewrite <- swap_tag_in_utyp_open. apply IHd_sub_tagsin;
        [ exact HU | rewrite Heq; symmetry; apply swap_atoms_union ].
  - apply d_sub_tagsin__forall_l_untagged
      with (Ψ' := swap_atoms ε1 ε2 Ψ') (ph := swap_tag_in_utyp ε1 ε2 ph).
    + assumption.
    + rewrite Heq. apply swap_atoms_disjoint_of; assumption.
    + rewrite (ftag_swap_tag_in_utyp ε1 ε2 (utyp_all_syn C)).
      apply swap_atoms_disjoint_of; assumption.
    + rewrite HU. apply swap_atoms_subset_of; assumption.
    + eapply d_tags_swap_tag; [ eassumption | reflexivity ].
    + apply d_wf_utyp_swap_tag; assumption.
    + apply is_dtyp_swap_tag; assumption.
    + rewrite <- swap_tag_in_utyp_open. apply IHd_sub_tagsin;
        [ exact HU | rewrite Heq; symmetry; apply swap_atoms_union ].
Qed.

(* ===================================================================== *)
(*  §4  WHOLESALE FRESHENING.                                             *)
(*                                                                        *)
(*  ⭐ The payoff.  Once the derivation's instantiation tags are bounded   *)
(*  by one set [U], moving them off a chosen [S] is one transposition at a *)
(*  time again —                                                          *)
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
    assert (HCeq : swap_tag_in_utyp ε1 ε2 C = C)
      by (apply swap_tag_in_utyp_fresh_eq;
            [ exact Hε1C | clear - Fr; fsetdec ]).
    pose proof (d_sub_tagsin_swap_tag U m Ψ Γ C B Hsub ε1 ε2
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
    [S] is disjoint from what the CONCLUSION mentions.  ⭐ Note that ONE swap
    rewrites the WHOLE derivation here — which is exactly why this can be
    iterated where a per-node freshening cannot (see the header). *)
Lemma d_sub_freshen : forall m Ψ Γ C B S,
  {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d ->
  S ∩ Ψ [=] empty ->
  S ∩ (ftag_in_utyp C) [=] empty ->
  exists U, U ∩ S [=] empty /\ d_sub_tagsin U m Ψ Γ C B.
Proof.
  intros m Ψ Γ C B S H HΨ HC.
  destruct (d_sub_to_tagsin m Ψ Γ C B H) as [ U HU ].
  apply (d_sub_tagsin_freshen_aux (cardinal (U ∩ S)) U m Ψ Γ C B S);
    [ lia | exact HU | exact HΨ | exact HC ].
Qed.
