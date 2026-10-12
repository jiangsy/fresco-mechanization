Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.consistency.prop_soundness_consis.

Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.typing.def_pat_impl.
Require Import src.fresco.ext_algo.typing.def_typing_impl.

Lemma notin_mem_false : forall α S, α `notin` S -> mem α S = false.
Proof.
  intros * H. destruct (mem α S) eqn:Hm; [ | reflexivity ].
  exfalso. apply H. apply mem_true_in. exact Hm.
Qed.

Lemma inter_is_empty_complete : forall S1 S2,
  S1 ∩ S2 [=] empty -> is_empty (inter S1 S2) = true.
Proof.
  intros * H. apply AtomSetFacts.is_empty_iff.
  intros a Hin. apply (AtomSetFacts.empty_iff a). apply H. exact Hin.
Qed.

Lemma tvarish_ck_complete : forall Θ α,
  a_binds_tvar α Θ -> tvarish_ck Θ α = true.
Proof.
  intros Θ α Hb. unfold tvarish_ck. apply orb_true_intro.
  destruct Hb as [Hr | [Hf | [τ Hf]]];
    [ left; apply rigid_bound_ck_complete; exact Hr
    | right; apply flex_tvar_flex_bound_ck; left; exact Hf
    | right; apply flex_tvar_flex_bound_ck; right; exists τ; exact Hf ].
Qed.

Lemma guarded_shape_ck_complete : forall P,
  guarded_pskl P -> guarded_shape_ck P = true.
Proof. intros P H; inversion H; subst; reflexivity. Qed.

Lemma uniq_ck_complete : forall Θ, uniq Θ -> uniq_ck Θ = true.
Proof.
  induction Θ as [ | [x b] Θ' IH ]; simpl; intros Hu; [ reflexivity | ].
  inversion Hu; subst.
  apply andb_true_intro; split;
    [ apply negb_true_iff; apply notin_mem_false; assumption
    | apply IH; assumption ].
Qed.

Lemma suffix_ck_complete : forall Ξ, a_suffix Ξ -> suffix_ck Ξ = true.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros Hs; [ reflexivity | ].
  inversion Hs as [ | ? ? ? Htl Hbd ]; subst.
  inversion Hbd; subst; simpl; apply IH; exact Htl.
Qed.

Lemma ghost_ck_complete : forall P, P = pskl_ghost -> ghost_ck P = true.
Proof. intros P ->; reflexivity. Qed.

Lemma pskl_eqb_complete : forall P Q, P = Q -> pskl_eqb P Q = true.
Proof.
  intros P Q <-. induction P; simpl;
    try reflexivity; try solve [ assumption ].
  - apply Nat.eqb_refl.
  - destruct (α == α); congruence.
  - apply andb_true_intro; split; assumption.
Qed.

Lemma ptyp_eqb_complete : forall A B, A = B -> ptyp_eqb A B = true.
Proof.
  intros A B <-. induction A; simpl;
    try reflexivity; try solve [ assumption ].
  - apply Nat.eqb_refl.
  - destruct (α == α); congruence.
  - apply andb_true_intro; split; assumption.
Qed.

Lemma degree_ptyp_ck_complete : forall A k,
  degree_ptyp_wrt_ptyp k A -> degree_ptyp_ck k A = true.
Proof.
  induction A; simpl; intros k Hd; inversion Hd; subst;
    try reflexivity; try solve [ apply IHA; assumption ].
  - apply Nat.ltb_lt; assumption.
  - apply andb_true_intro; split; [ apply IHA1 | apply IHA2 ]; assumption.
Qed.

Corollary lc_ptyp_ck_complete : forall A,
  lc_ptyp A -> degree_ptyp_ck 0 A = true.
Proof.
  intros; apply degree_ptyp_ck_complete;
    apply degree_ptyp_wrt_ptyp_of_lc_ptyp; assumption.
Qed.

Lemma degree_pskl_ck_complete : forall P k,
  degree_pskl_wrt_pskl k P -> degree_pskl_ck k P = true.
Proof.
  induction P; simpl; intros k Hd; inversion Hd; subst;
    try reflexivity; try solve [ apply IHP; assumption ].
  - apply Nat.ltb_lt; assumption.
  - apply andb_true_intro; split; [ apply IHP1 | apply IHP2 ]; assumption.
Qed.

Corollary lc_pskl_ck_complete : forall P,
  lc_pskl P -> degree_pskl_ck 0 P = true.
Proof.
  intros; apply degree_pskl_ck_complete;
    apply degree_pskl_wrt_pskl_of_lc_pskl; assumption.
Qed.

Lemma defs_mono_ck_complete : forall Θ,
  aenv_defs_mono Θ -> defs_mono_ck Θ = true.
Proof.
  induction Θ as [ | [x b] Θ' IH ]; simpl; intros Hm; [ reflexivity | ].
  inversion Hm as [ | ? ? He Htl ]; subst.
  apply andb_true_intro; split; [ | apply IH; exact Htl ].
  destruct b; simpl in *; try reflexivity.
  apply mono_ck_complete; exact He.
Qed.

Lemma wf_pskl_ck_complete : forall n Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> size_pskl P <= n -> wf_pskl_ck n Θ Δ P = true.
Proof.
  induction n as [ | n IH ]; intros Θ Δ P Hwf Hsz.
  { exfalso. pose proof (size_pskl_min P). lia. }
  destruct P; simpl; simpl in Hsz.

  -  reflexivity.

  -
    inversion Hwf.

  -
    inversion Hwf as [ | ? ? ? Hin | | | | ]; subst.
    apply tvarish_ck_complete; exact Hin.

  -
    inversion Hwf as [ | | ? ? ? ? H1 H2 | | | ]; subst.
    apply andb_true_intro; split; apply IH; solve [ assumption | lia ].

  -
    remember (supply_fresh (dom Θ `union` Δ `union` ftvar_in_pskl P)) as β
      eqn:Hβ.
    assert (Hfr : β `notin` (dom Θ `union` Δ `union` ftvar_in_pskl P))
      by (subst β; apply supply_fresh_notin).
    apply IH.
    + apply a_wf_pskl_all_inv_at; [ exact Hwf | clear - Hfr; fsetdec ].
    + rewrite size_pskl_open_pskl_wrt_pskl_var. lia.

  -  reflexivity.

  -
    inversion Hwf as [ | | | | | ? ? ? Hg Hp ]; subst.
    apply andb_true_intro; split;
      [ apply guarded_shape_ck_complete; exact Hg
      | apply IH; solve [ exact Hp | lia ] ].
Qed.

Corollary wf_pskl_ck_complete_at_size : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> wf_pskl_ck (size_pskl P) Θ Δ P = true.
Proof. intros; apply wf_pskl_ck_complete; [ assumption | lia ]. Qed.

Lemma arrow_split_complete : forall P1 P2,
  exists r, arrow_split (pskl_arrow P1 P2) = Some r
            /\ proj1_sig r = (P1, P2).
Proof. intros. eexists. split; reflexivity. Qed.

Lemma ptyp_arrow_split_complete : forall A1 A2,
  exists r, ptyp_arrow_split (ptyp_arrow A1 A2) = Some r
            /\ proj1_sig r = (A1, A2).
Proof. intros. eexists. split; reflexivity. Qed.

Lemma abind_var_skl_get_complete : forall P,
  exists r, abind_var_skl_get (abind_var_skl P) = Some r /\ proj1_sig r = P.
Proof. intros. eexists. split; reflexivity. Qed.

Lemma abind_var_typ_get_complete : forall A,
  exists r, abind_var_typ_get (abind_var_typ A) = Some r /\ proj1_sig r = A.
Proof. intros. eexists. split; reflexivity. Qed.

Lemma lookup_binding_complete : forall x Θ b,
  uniq Θ -> binds x b Θ ->
  exists r, lookup_binding x Θ = Some r /\ proj1_sig r = b.
Proof.
  intros x Θ. induction Θ as [ | [y b'] Θ' IH ]; intros b Hu Hb;
    [ inversion Hb | ].
  inversion Hu; subst. simpl.
  destruct (x == y) as [-> | Hne].
  -
    destruct Hb as [Heq | Hin].
    + inversion Heq; subst. eexists. split; reflexivity.
    + exfalso. assert (y `in` dom Θ') by (eapply binds_In; exact Hin).
      fsetdec.
  - destruct Hb as [Heq | Hin]; [ inversion Heq; congruence | ].
    destruct (IH b ltac:(assumption) Hin) as [[b0 Hb0] [Hr Hpr]].
    simpl in Hpr; subst b0.
    rewrite Hr. eexists. split; reflexivity.
Qed.

Lemma split_at_key_skl_complete : forall x Ξ P Θ',
  uniq (Ξ ++ (x ~ abind_var_skl P) ++ Θ') ->
  exists r, split_at_key_skl x (Ξ ++ (x ~ abind_var_skl P) ++ Θ') = Some r
            /\ proj1_sig r = (Ξ, P, Θ').
Proof.
  intros x Ξ. induction Ξ as [ | [y b] Ξ' IH ]; intros P Θ' Hu.
  -
    simpl. destruct (x == x) as [Heq | Hne]; [ | congruence ].
    eexists. split; reflexivity.
  - simpl in Hu |- *. inversion Hu; subst.
    destruct (x == y) as [Heq | Hne].
    +
      exfalso. subst y. simpl_env in *. fsetdec.
    + destruct (IH P Θ' ltac:(assumption)) as [[t Ht] [Hr Hpr]].
      simpl in Hpr; subst t.
      change (x ~ abind_var_skl P ++ Θ')
        with ((x, abind_var_skl P) :: Θ') in Hr.
      rewrite Hr. eexists. split; reflexivity.
Qed.

Lemma split_at_key_typ_complete : forall x Ξ A Θ',
  uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ') ->
  exists r, split_at_key_typ x (Ξ ++ (x ~ abind_var_typ A) ++ Θ') = Some r
            /\ proj1_sig r = (Ξ, A, Θ').
Proof.
  intros x Ξ. induction Ξ as [ | [y b] Ξ' IH ]; intros A Θ' Hu.
  -
    simpl. destruct (x == x) as [Heq | Hne]; [ | congruence ].
    eexists. split; reflexivity.
  - simpl in Hu |- *. inversion Hu; subst.
    destruct (x == y) as [Heq | Hne].
    +
      exfalso. subst y. simpl_env in *. fsetdec.
    + destruct (IH A Θ' ltac:(assumption)) as [[t Ht] [Hr Hpr]].
      simpl in Hpr; subst t.
      change (x ~ abind_var_typ A ++ Θ')
        with ((x, abind_var_typ A) :: Θ') in Hr.
      rewrite Hr. eexists. split; reflexivity.
Qed.

Lemma pskl_readback_complete : forall A,
  exists r, pskl_readback (ptyp_to_pskl A) = Some r /\ proj1_sig r = A.
Proof.
  induction A; simpl;
    try solve [ eexists; split; reflexivity ].
  - destruct IHA1 as [r1 [Hr1 Hp1]]. destruct IHA2 as [r2 [Hr2 Hp2]].
    rewrite Hr1. destruct r1 as [A1' H1']. simpl in Hp1; subst A1'.
    rewrite Hr2. destruct r2 as [A2' H2']. simpl in Hp2; subst A2'.
    eexists. split; reflexivity.
  - destruct IHA as [r [Hr Hp]].
    rewrite Hr. destruct r as [A' H']. simpl in Hp; subst A'.
    eexists. split; reflexivity.
Qed.

Lemma pskl_readback_all_complete : forall A0,
  exists r, pskl_readback_all (ptyp_to_pskl (ptyp_all A0)) = Some r
            /\ proj1_sig r = A0.
Proof.
  intros A0. unfold pskl_readback_all. simpl.
  destruct (pskl_readback_complete A0) as [r [Hr Hp]].
  rewrite Hr. destruct r as [A' H']. simpl in Hp; subst A'.
  eexists. split; reflexivity.
Qed.
