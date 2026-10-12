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
Require Import src.fresco.decl.prop_ctx_mono.
Require Import src.fresco.decl.prop_renaming.

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
    α `notin` (dom Γ `union` ftvar_in_utyp C `union` ftvar_in_btyp B) ->
    d_sub_tagsin U mode_tc Ψ ((α ~ dbind_tvar) ++ Γ) C
      (open_btyp_wrt_btyp B (btyp_var_f α)) ->
    d_sub_tagsin U mode_tc Ψ Γ C (btyp_all_inh B)
| d_sub_tagsin__arrow : forall U Ψ Ψ1 Ψ2 Γ m C1 C2 B1 B2,
    {{ Ψ1 ⨟ Γ ⊢ C1 ∼ B1 }}d ->
    d_sub_tagsin U m Ψ2 Γ C2 B2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    d_sub_tagsin U (mode_fn m) Ψ Γ (utyp_arrow C1 C2) (btyp_arrow B1 B2)
| d_sub_tagsin__forall_l_tagged : forall U Ψ Ψ' Γ m ε C ph B,
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_utyp (utyp_all_tag ε C)) [=] empty ->
    Ψ' [<=] U ->
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

Lemma d_sub_tagsin_weaken : forall U m Ψ Γ C B,
  d_sub_tagsin U m Ψ Γ C B -> forall U', U [<=] U' -> d_sub_tagsin U' m Ψ Γ C B.
Proof.
  intros U m Ψ Γ C B H; induction H; intros U' Hle.
  - apply d_sub_tagsin__infer; assumption.
  - apply d_sub_tagsin__check; assumption.
  - apply d_sub_tagsin__forall_r with (α := α);
      [ assumption | apply IHd_sub_tagsin; exact Hle ].
  - apply d_sub_tagsin__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ assumption | apply IHd_sub_tagsin; exact Hle | assumption ].
  - apply d_sub_tagsin__forall_l_tagged with (Ψ' := Ψ') (ph := ph);
      [ assumption | assumption | assumption | clear - H2 Hle; fsetdec
      | assumption | assumption | assumption | apply IHd_sub_tagsin; exact Hle ].
  - apply d_sub_tagsin__forall_l_untagged with (Ψ' := Ψ') (ph := ph);
      [ assumption | assumption | assumption | clear - H2 Hle; fsetdec
      | assumption | assumption | assumption | apply IHd_sub_tagsin; exact Hle ].
Qed.

Lemma d_sub_to_tagsin : forall m Ψ Γ C B,
  {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d -> exists U, d_sub_tagsin U m Ψ Γ C B.
Proof.
  intros m Ψ Γ C B H; induction H.
  - exists empty. apply d_sub_tagsin__infer; assumption.
  - exists empty. apply d_sub_tagsin__check; assumption.
  - pick fresh α0 for
      (L `union` dom Γ `union` ftvar_in_utyp C `union` ftvar_in_btyp B).
    destruct (H0 α0 ltac:(solve_notin_auto)) as [ U HU ].
    exists U. apply d_sub_tagsin__forall_r with (α := α0);
      [ clear - Fr; solve_notin_auto | exact HU ].
  - destruct IHd_sub as [ U HU ]. exists U.
    apply d_sub_tagsin__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
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
      [ rewrite ftvar_swap_tag_in_utyp; assumption
      | apply IHd_sub_tagsin; assumption ].
  - apply d_sub_tagsin__arrow with (Ψ1 := swap_atoms ε1 ε2 Ψ1)
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

Lemma d_sub_tagsin_freshen_aux : forall k U m Ψ Γ C B S,
  cardinal (U ∩ S) <= k ->
  d_sub_tagsin U m Ψ Γ C B ->
  S ∩ Ψ [=] empty ->
  S ∩ (ftag_in_utyp C) [=] empty ->
  exists U', U' ∩ S [=] empty /\ d_sub_tagsin U' m Ψ Γ C B.
Proof.
  induction k; intros U m Ψ Γ C B S Hk Hsub HΨ HC;
    destruct (choose (U ∩ S)) as [ ε1 | ] eqn:Hch.
  -
    exfalso. apply choose_1 in Hch.
    assert (HE : Empty (U ∩ S)) by (apply cardinal_Empty; lia).
    exact (HE ε1 Hch).
  - apply choose_2 in Hch. exists U.
    split; [ apply AtomSetProperties.empty_is_empty_1; exact Hch | exact Hsub ].
  -
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
