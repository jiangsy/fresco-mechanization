Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.

Set Implicit Arguments.

Lemma a_wf_pskl_ftv_binds : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ.
Proof.
  intros Θ Δ P H; induction H; intros β Hβ; simpl in Hβ.
  - fsetdec.
  - assert (β = α) by fsetdec. subst. auto.
  - destruct (union_1 Hβ); auto.
  - pick fresh α2 for (L `union` ftvar_in_pskl P `union` {{β}}).
    assert (HZL : α2 `notin` L) by fsetdec.
    assert (HY' : β `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α2))).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α2)).
      fsetdec. }
    assert (Hne : β <> α2) by fsetdec.
    destruct (H0 α2 HZL β HY') as [Hb | [Hb | [τ Hb]]];
      apply binds_cons_1 in Hb; destruct Hb as [[? ?] | Hb];
      try (subst; contradiction);
      [ left | right; left | right; right; exists τ ]; exact Hb.
  - fsetdec.
  - pose proof (IHa_wf_pskl β Hβ) as Htv.
    apply a_binds_tvar_aenv_minus in Htv. apply Htv.
Qed.

Lemma a_wf_pskl_lc : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> lc_pskl P.
Proof.
  intros Θ Δ P H; induction H; eauto using lc_pskl.
Qed.

Lemma a_scope_pskl_of_wf : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  a_scope_pskl Θ P.
Proof.
  intros Θ Δ P H. split;
    [ eapply a_wf_pskl_lc; exact H | exact (a_wf_pskl_ftv_binds H) ].
Qed.

Lemma a_scope_pskl_lc : forall Θ P, a_scope_pskl Θ P -> lc_pskl P.
Proof. intros Θ P H; exact (proj1 H). Qed.

Lemma a_scope_pskl_ftv_binds : forall Θ P γ,
  a_scope_pskl Θ P -> γ `in` ftvar_in_pskl P -> a_binds_tvar γ Θ.
Proof. intros Θ P γ H; exact (proj2 H γ). Qed.

Lemma a_scope_pskl_var : forall Θ α,
  a_binds_tvar α Θ -> a_scope_pskl Θ (pskl_var_f α).
Proof.
  intros Θ α H. split; [ apply lc_pskl_var_f | ].
  intros β Hβ. simpl in Hβ. apply singleton_1 in Hβ. subst. exact H.
Qed.

Lemma a_scope_pskl_all_of_open : forall L Θ P,
  (forall α, α `notin` L ->
     a_scope_pskl ((α ~ abind_tvar) ++ Θ) (open_pskl_wrt_pskl P (pskl_var_f α))) ->
  a_scope_pskl Θ (pskl_all_syn P).
Proof.
  intros L Θ P H. split.
  - destruct (atom_fresh (L `union` ftvar_in_pskl P)) as [α Hα].
    apply lc_pskl_all_syn_exists with (α1 := α).
    apply (proj1 (H α ltac:(clear - Hα; fsetdec))).
  - intros γ Hγ. simpl in Hγ.
    destruct (atom_fresh (L `union` singleton γ)) as [α Hα].
    assert (Hγo : γ `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α)).
      clear - H0 Hγ; fsetdec. }
    destruct (a_binds_tvar_cons_tvar_inv
                (proj2 (H α ltac:(clear - Hα; fsetdec)) γ Hγo)) as [-> | Hb];
      [ exfalso; clear - Hα; fsetdec | exact Hb ].
Qed.

Lemma a_scope_pskl_all_close : forall α Θ Q,
  a_scope_pskl ((α ~ abind_tvar) ++ Θ) Q ->
  a_scope_pskl Θ (pskl_all_syn (close_pskl_wrt_pskl α Q)).
Proof.
  intros α Θ Q [Hlc Hb]. split.
  - apply lc_pskl_all_syn_exists with (α1 := α).
    rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl. exact Hlc.
  - intros γ Hγ. simpl in Hγ. rewrite ftvar_in_pskl_close_pskl_wrt_pskl in Hγ.
    destruct (a_binds_tvar_cons_tvar_inv (Hb γ ltac:(clear - Hγ; fsetdec)))
      as [-> | Hb']; [ exfalso; clear - Hγ; fsetdec | exact Hb' ].
Qed.

#[export] Hint Extern 1 (a_scope_pskl _ _) =>
  eapply a_scope_pskl_of_wf; eassumption : core.

Unset Implicit Arguments.

Lemma swap_atom_l : forall a b, swap_atom a b a = b.
Proof.
  intros. unfold swap_atom.
  destruct (a == a); [reflexivity | exfalso; apply n; reflexivity].
Qed.

Lemma swap_atom_r : forall a b, swap_atom a b b = a.
Proof.
  intros. unfold swap_atom.
  destruct (b == a); [congruence |].
  destruct (b == b); [reflexivity | exfalso; apply n0; reflexivity].
Qed.

Lemma swap_atom_inj : forall a b x y,
  swap_atom a b x = swap_atom a b y -> x = y.
Proof.
  intros * H.
  rewrite <- (swap_atom_invol a b x), <- (swap_atom_invol a b y), H.
  reflexivity.
Qed.

Definition rename_abind (γ β : atom) (bd : abind) : abind :=
  match bd with
  | abind_tvar            => abind_tvar
  | abind_var_typ A       => abind_var_typ (subst_ptyp_in_ptyp (ptyp_var_f γ) β A)
  | abind_var_skl P       => abind_var_skl (subst_pskl_in_pskl (pskl_var_f γ) β P)
  | abind_flex_mono       => abind_flex_mono
  | abind_flex_mono_def A => abind_flex_mono_def (subst_ptyp_in_ptyp (ptyp_var_f γ) β A)
  end.

Fixpoint rename_aenv (γ β : atom) (Θ : aenv) : aenv :=
  match Θ with
  | nil           => nil
  | (x, bd) :: Θ' => ((if x == β then γ else x), rename_abind γ β bd)
                       :: rename_aenv γ β Θ'
  end.

Local Lemma notin_union_split : forall (x : atom) (s t : atoms),
  x `notin` (s `union` t) -> x `notin` s /\ x `notin` t.
Proof. intros; split; fsetdec. Qed.

Local Lemma notin_union_join : forall (x : atom) (s t : atoms),
  x `notin` s -> x `notin` t -> x `notin` (s `union` t).
Proof. intros; fsetdec. Qed.

Fixpoint swap_ptyp (a b : atom) (A : ptyp) : ptyp :=
  match A with
  | ptyp_unit => ptyp_unit
  | ptyp_var_b n => ptyp_var_b n
  | ptyp_var_f α => ptyp_var_f (swap_atom a b α)
  | ptyp_arrow A1 A2 => ptyp_arrow (swap_ptyp a b A1) (swap_ptyp a b A2)
  | ptyp_all A0 => ptyp_all (swap_ptyp a b A0)
  end.

Fixpoint swap_pskl (a b : atom) (P : pskl) : pskl :=
  match P with
  | pskl_unit => pskl_unit
  | pskl_var_b n => pskl_var_b n
  | pskl_var_f α => pskl_var_f (swap_atom a b α)
  | pskl_arrow P1 P2 => pskl_arrow (swap_pskl a b P1) (swap_pskl a b P2)
  | pskl_all_syn P0 => pskl_all_syn (swap_pskl a b P0)
  | pskl_ghost => pskl_ghost
  | pskl_univ_ghost P0 => pskl_univ_ghost (swap_pskl a b P0)
  end.

Definition swap_abind (a b : atom) (bd : abind) : abind :=
  match bd with
  | abind_tvar => abind_tvar
  | abind_var_typ A => abind_var_typ (swap_ptyp a b A)
  | abind_var_skl P => abind_var_skl (swap_pskl a b P)
  | abind_flex_mono => abind_flex_mono
  | abind_flex_mono_def τ => abind_flex_mono_def (swap_ptyp a b τ)
  end.

Definition swap_aenv (a b : atom) (Θ : aenv) : aenv :=
  List.map (fun e => (swap_atom a b (fst e), swap_abind a b (snd e))) Θ.

Lemma swap_ptyp_invol : forall a b A, swap_ptyp a b (swap_ptyp a b A) = A.
Proof.
  induction A; simpl; f_equal; auto using swap_atom_invol.
Qed.

Lemma swap_pskl_invol : forall a b P, swap_pskl a b (swap_pskl a b P) = P.
Proof.
  induction P; simpl; f_equal; auto using swap_atom_invol.
Qed.

Lemma swap_abind_invol : forall a b bd, swap_abind a b (swap_abind a b bd) = bd.
Proof.
  destruct bd; simpl; f_equal; auto using swap_ptyp_invol, swap_pskl_invol.
Qed.

Lemma swap_aenv_cons : forall a b x bd (Θ : aenv),
  swap_aenv a b ((x, bd) :: Θ)
  = (swap_atom a b x, swap_abind a b bd) :: swap_aenv a b Θ.
Proof. reflexivity. Qed.

Lemma swap_aenv_one_tvar : forall a b,
  swap_aenv a b (a ~ abind_tvar) = b ~ abind_tvar.
Proof.
  intros a b. unfold swap_aenv, one. simpl.
  rewrite swap_atom_l. reflexivity.
Qed.

Lemma swap_aenv_invol : forall a b Θ, swap_aenv a b (swap_aenv a b Θ) = Θ.
Proof.
  induction Θ as [| [x bd] Θ']; [reflexivity |].
  rewrite !swap_aenv_cons, swap_atom_invol, swap_abind_invol, IHΘ'.
  reflexivity.
Qed.

Lemma swap_aenv_app : forall a b (Θ1 Θ2 : aenv),
  swap_aenv a b (Θ1 ++ Θ2) = swap_aenv a b Θ1 ++ swap_aenv a b Θ2.
Proof. intros. unfold swap_aenv. apply List.map_app. Qed.

Lemma swap_ptyp_ftv_in : forall a b A x,
  x `in` ftvar_in_ptyp A ->
  swap_atom a b x `in` ftvar_in_ptyp (swap_ptyp a b A).
Proof.
  intros a b A; induction A; simpl; intros x Hx; try solve [fsetdec | auto].
  -  assert (x = α) by fsetdec. subst. fsetdec.
  -
    assert (x `in` ftvar_in_ptyp A1 \/ x `in` ftvar_in_ptyp A2) as [h | h]
      by fsetdec;
      [ pose proof (IHA1 x h) | pose proof (IHA2 x h) ]; fsetdec.
Qed.

Lemma swap_pskl_ftv_in : forall a b P x,
  x `in` ftvar_in_pskl P ->
  swap_atom a b x `in` ftvar_in_pskl (swap_pskl a b P).
Proof.
  intros a b P; induction P; simpl; intros x Hx; try solve [fsetdec | auto].
  -  assert (x = α) by fsetdec. subst. fsetdec.
  -
    assert (x `in` ftvar_in_pskl P1 \/ x `in` ftvar_in_pskl P2) as [h | h]
      by fsetdec;
      [ pose proof (IHP1 x h) | pose proof (IHP2 x h) ]; fsetdec.
Qed.

Lemma swap_ptyp_ftv_notin : forall a b A x,
  x `notin` ftvar_in_ptyp A ->
  swap_atom a b x `notin` ftvar_in_ptyp (swap_ptyp a b A).
Proof.
  intros * Hn Hin. apply Hn.
  pose proof (swap_ptyp_ftv_in a b (swap_ptyp a b A) (swap_atom a b x) Hin)
    as h.
  rewrite swap_ptyp_invol, swap_atom_invol in h. exact h.
Qed.

Lemma swap_pskl_ftv_notin : forall a b P x,
  x `notin` ftvar_in_pskl P ->
  swap_atom a b x `notin` ftvar_in_pskl (swap_pskl a b P).
Proof.
  intros * Hn Hin. apply Hn.
  pose proof (swap_pskl_ftv_in a b (swap_pskl a b P) (swap_atom a b x) Hin)
    as h.
  rewrite swap_pskl_invol, swap_atom_invol in h. exact h.
Qed.

Lemma swap_ptyp_fresh_id : forall a b A,
  a `notin` ftvar_in_ptyp A -> b `notin` ftvar_in_ptyp A ->
  swap_ptyp a b A = A.
Proof.
  induction A; simpl; intros Ha Hb; f_equal;
    try solve
      [ reflexivity
      | apply swap_atom_other; intro; subst; fsetdec
      | apply IHA; fsetdec
      | apply IHA1; fsetdec
      | apply IHA2; fsetdec ].
Qed.

Lemma swap_pskl_fresh_id : forall a b P,
  a `notin` ftvar_in_pskl P -> b `notin` ftvar_in_pskl P ->
  swap_pskl a b P = P.
Proof.
  induction P; simpl; intros Ha Hb; f_equal;
    try solve
      [ reflexivity
      | apply swap_atom_other; intro; subst; fsetdec
      | apply IHP; fsetdec
      | apply IHP1; fsetdec
      | apply IHP2; fsetdec ].
Qed.

Lemma swap_aenv_dom_in : forall a b (Θ : aenv) x,
  x `in` dom Θ -> swap_atom a b x `in` dom (swap_aenv a b Θ).
Proof.
  intros a b Θ; induction Θ as [| [y bd] Θ']; simpl; intros x Hx.
  - fsetdec.
  - assert (x = y \/ x `in` dom Θ') as [h | h] by fsetdec.
    + subst. fsetdec.
    + pose proof (IHΘ' x h). fsetdec.
Qed.

Lemma swap_aenv_dom_notin : forall a b (Θ : aenv) x,
  x `notin` dom Θ -> swap_atom a b x `notin` dom (swap_aenv a b Θ).
Proof.
  intros * Hn Hin. apply Hn.
  pose proof (swap_aenv_dom_in a b (swap_aenv a b Θ) (swap_atom a b x) Hin)
    as h.
  rewrite swap_aenv_invol, swap_atom_invol in h. exact h.
Qed.

Lemma swap_abind_ftv_in : forall a b bd x,
  x `in` ftvar_in_abind bd ->
  swap_atom a b x `in` ftvar_in_abind (swap_abind a b bd).
Proof.
  intros; destruct bd; simpl in *;
    auto using swap_ptyp_ftv_in, swap_pskl_ftv_in; fsetdec.
Qed.

Lemma swap_aenv_ftvar_in : forall a b (Θ : aenv) x,
  x `in` ftvar_in_aenv Θ ->
  swap_atom a b x `in` ftvar_in_aenv (swap_aenv a b Θ).
Proof.
  intros a b Θ; induction Θ as [| [y bd] Θ']; simpl; intros x Hx.
  - fsetdec.
  - assert (x = y \/ x `in` ftvar_in_abind bd \/ x `in` ftvar_in_aenv Θ')
      as [h | [h | h]] by fsetdec.
    + subst. fsetdec.
    + pose proof (swap_abind_ftv_in a b bd x h). fsetdec.
    + pose proof (IHΘ' x h). fsetdec.
Qed.

Lemma swap_aenv_ftvar_notin : forall a b (Θ : aenv) x,
  x `notin` ftvar_in_aenv Θ ->
  swap_atom a b x `notin` ftvar_in_aenv (swap_aenv a b Θ).
Proof.
  intros * Hn Hin. apply Hn.
  pose proof (swap_aenv_ftvar_in a b (swap_aenv a b Θ) (swap_atom a b x) Hin)
    as h.
  rewrite swap_aenv_invol, swap_atom_invol in h. exact h.
Qed.

Lemma swap_aenv_binds : forall a b x bd (Θ : aenv),
  binds x bd Θ ->
  binds (swap_atom a b x) (swap_abind a b bd) (swap_aenv a b Θ).
Proof.
  intros a b x bd Θ; unfold binds;
    induction Θ as [| [y byd] Θ']; simpl; intros H.
  - contradiction.
  - destruct H as [Heq | Hin].
    + inversion Heq; subst. left; reflexivity.
    + right; auto.
Qed.

Lemma swap_aenv_uniq : forall a b (Θ : aenv),
  uniq Θ -> uniq (swap_aenv a b Θ).
Proof.
  intros a b Θ H; induction H; simpl.
  - constructor.
  - constructor; auto using swap_aenv_dom_notin.
Qed.

Lemma swap_ptyp_open_rec : forall a b A2 A1 k,
  swap_ptyp a b (open_ptyp_wrt_ptyp_rec k A2 A1)
  = open_ptyp_wrt_ptyp_rec k (swap_ptyp a b A2) (swap_ptyp a b A1).
Proof.
  intros a b A2; induction A1; intros k; simpl;
    try solve [f_equal; auto].

  destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; simpl; auto.
Qed.

Lemma swap_pskl_open_rec : forall a b P2 P1 k,
  swap_pskl a b (open_pskl_wrt_pskl_rec k P2 P1)
  = open_pskl_wrt_pskl_rec k (swap_pskl a b P2) (swap_pskl a b P1).
Proof.
  intros a b P2; induction P1; intros k; simpl;
    try solve [f_equal; auto].

  destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; simpl; auto.
Qed.

Lemma swap_ptyp_open : forall a b A1 A2,
  swap_ptyp a b (open_ptyp_wrt_ptyp A1 A2)
  = open_ptyp_wrt_ptyp (swap_ptyp a b A1) (swap_ptyp a b A2).
Proof. intros. unfold open_ptyp_wrt_ptyp. apply swap_ptyp_open_rec. Qed.

Lemma swap_pskl_open : forall a b P1 P2,
  swap_pskl a b (open_pskl_wrt_pskl P1 P2)
  = open_pskl_wrt_pskl (swap_pskl a b P1) (swap_pskl a b P2).
Proof. intros. unfold open_pskl_wrt_pskl. apply swap_pskl_open_rec. Qed.

Lemma swap_pskl_open_var : forall a b P β,
  swap_pskl a b (open_pskl_wrt_pskl P (pskl_var_f β))
  = open_pskl_wrt_pskl (swap_pskl a b P) (pskl_var_f (swap_atom a b β)).
Proof. intros. apply swap_pskl_open. Qed.

Lemma swap_ptyp_close_rec : forall a b x A k,
  swap_ptyp a b (close_ptyp_wrt_ptyp_rec k x A)
  = close_ptyp_wrt_ptyp_rec k (swap_atom a b x) (swap_ptyp a b A).
Proof.
  intros a b x; induction A; intros k; simpl.
  - reflexivity.
  -  destruct (lt_ge_dec n k); reflexivity.
  -
    destruct (x == α) as [e | n0].
    + rewrite e. simpl.
      match goal with
      | |- context [if ?t then _ else _] => destruct t as [_ | n1]
      end; [reflexivity | exfalso; apply n1; reflexivity].
    + simpl.
      match goal with
      | |- context [if ?t then _ else _] => destruct t as [e1 | ?]
      end; [exfalso; apply n0; exact (swap_atom_inj a b x α e1) | reflexivity].
  -  f_equal; auto.
  -  f_equal; auto.
Qed.

Lemma swap_ptyp_close : forall a b x A,
  swap_ptyp a b (close_ptyp_wrt_ptyp x A)
  = close_ptyp_wrt_ptyp (swap_atom a b x) (swap_ptyp a b A).
Proof. intros. unfold close_ptyp_wrt_ptyp. apply swap_ptyp_close_rec. Qed.

Lemma swap_pskl_close_rec : forall a b x P k,
  swap_pskl a b (close_pskl_wrt_pskl_rec k x P)
  = close_pskl_wrt_pskl_rec k (swap_atom a b x) (swap_pskl a b P).
Proof.
  intros a b x; induction P; intros k; simpl.
  - reflexivity.
  -  destruct (lt_ge_dec n k); reflexivity.
  -
    destruct (x == α) as [e | n0].
    + rewrite e. simpl.
      match goal with
      | |- context [if ?t then _ else _] => destruct t as [_ | n1]
      end; [reflexivity | exfalso; apply n1; reflexivity].
    + simpl.
      match goal with
      | |- context [if ?t then _ else _] => destruct t as [e1 | ?]
      end; [exfalso; apply n0; exact (swap_atom_inj a b x α e1) | reflexivity].
  -  f_equal; auto.
  -  f_equal; auto.
  -  reflexivity.
  -  f_equal; auto.
Qed.

Lemma swap_pskl_close : forall a b x P,
  swap_pskl a b (close_pskl_wrt_pskl x P)
  = close_pskl_wrt_pskl (swap_atom a b x) (swap_pskl a b P).
Proof. intros. unfold close_pskl_wrt_pskl. apply swap_pskl_close_rec. Qed.

Lemma swap_pskl_ptyp_to_pskl : forall a b A,
  swap_pskl a b (ptyp_to_pskl A) = ptyp_to_pskl (swap_ptyp a b A).
Proof. induction A; simpl; f_equal; auto. Qed.

Lemma a_guess_mono_swap : forall a b Θ P Ξ τ,
  a_guess_mono Θ P Ξ τ ->
  a_guess_mono (swap_aenv a b Θ) (swap_pskl a b P)
               (swap_aenv a b Ξ) (swap_ptyp a b τ).
Proof.
  intros * H; induction H; simpl.
  -
    apply a_guess_mono__ghost. auto using swap_aenv_ftvar_notin.
  -  apply a_guess_mono__univ_ghost; auto.
  -  apply a_guess_mono__var.
  -  apply a_guess_mono__unit.
  -
    rewrite swap_aenv_app. apply a_guess_mono__arrow; auto.
  -
    rewrite swap_ptyp_close.
    apply a_guess_mono__forall.
    + apply notin_union_split in H as [h1 h2].
      apply notin_union_join;
        auto using swap_aenv_ftvar_notin, swap_pskl_ftv_notin.
    + rewrite swap_pskl_open_var in IHa_guess_mono. exact IHa_guess_mono.
Qed.

Lemma a_guess_swap : forall a b Θ NM Q Ξ Q',
  a_guess Θ NM Q Ξ Q' ->
  a_guess (swap_aenv a b Θ) NM (swap_pskl a b Q)
          (swap_aenv a b Ξ) (swap_pskl a b Q').
Proof.
  intros * H; destruct H; simpl.
  - apply a_guess__sk.
  - rewrite swap_pskl_ptyp_to_pskl. apply a_guess__ty.
    apply a_guess_mono_swap; auto.
Qed.

Lemma empty_eq_swap_atoms_empty : forall a b,
  empty [=] swap_atoms a b empty.
Proof. intros. symmetry. apply swap_atoms_empty. Qed.

Lemma eq_swap_atoms_add : forall a b x (S S' : atoms),
  S' [=] swap_atoms a b S ->
  add (swap_atom a b x) S' [=] swap_atoms a b (add x S).
Proof.
  intros * HS y. split; intros Hy.
  - apply swap_atoms_spec.
    assert (y = swap_atom a b x \/ y `in` S') as [h | h] by fsetdec.
    + subst. rewrite swap_atom_invol. fsetdec.
    + assert (y `in` swap_atoms a b S) by fsetdec.
      apply swap_atoms_spec in H. fsetdec.
  - apply swap_atoms_spec in Hy.
    assert (swap_atom a b y = x \/ swap_atom a b y `in` S) as [h | h]
      by fsetdec.
    + assert (y = swap_atom a b x)
        by (rewrite <- h, swap_atom_invol; reflexivity).
      fsetdec.
    + assert (y `in` swap_atoms a b S) by (apply swap_atoms_spec; exact h).
      fsetdec.
Qed.

Lemma swap_notin_eq : forall a b x (S S' : atoms),
  S' [=] swap_atoms a b S ->
  x `notin` S ->
  swap_atom a b x `notin` S'.
Proof.
  intros * HS Hn Hin.
  assert (h0 : swap_atom a b x `in` swap_atoms a b S) by fsetdec.
  pose proof (proj1 (swap_atoms_spec a b S (swap_atom a b x)) h0) as h.
  rewrite swap_atom_invol in h. contradiction.
Qed.

Definition swap_cstr (a b : atom) (c : a_cstr) : a_cstr :=
  match c with
  | a_cstr_sub m P => a_cstr_sub m (swap_pskl a b P)
  | a_cstr_eq P => a_cstr_eq (swap_pskl a b P)
  end.

Definition swap_cstrs (a b : atom) (C : a_cstrs) : a_cstrs :=
  List.map (swap_cstr a b) C.

Lemma swap_cstrs_cons : forall a b c (C : a_cstrs),
  swap_cstrs a b (c :: C) = swap_cstr a b c :: swap_cstrs a b C.
Proof. reflexivity. Qed.

Lemma swap_cstrs_ftv_notin : forall a b (C : a_cstrs) x,
  x `notin` ftvar_in_a_cstrs C ->
  swap_atom a b x `notin` ftvar_in_a_cstrs (swap_cstrs a b C).
Proof.
  induction C as [ | c C IH ]; intros x Hx; simpl in *; [ fsetdec | ].
  pose proof (IH x ltac:(clear - Hx; fsetdec)) as Hc.
  destruct c as [m P | P]; simpl in *;
    pose proof (swap_pskl_ftv_notin a b P x ltac:(clear - Hx; fsetdec)) as Hp;
    clear - Hc Hp; fsetdec.
Qed.

Lemma swap_look_guard : forall a b (C : a_cstrs) (Ξ : aenv),
  ftvar_in_a_cstrs C ∩ dom Ξ [=] empty ->
  ftvar_in_a_cstrs (swap_cstrs a b C) ∩ dom (swap_aenv a b Ξ) [=] empty.
Proof.
  intros a b C Ξ H.
  assert (Hkey : forall x, x `in` ftvar_in_a_cstrs (swap_cstrs a b C) ->
                           x `in` dom (swap_aenv a b Ξ) -> False).
  { intros x Hc Hd.
    assert (Hc' : swap_atom a b x `in` ftvar_in_a_cstrs C).
    { destruct (AtomSetProperties.In_dec (swap_atom a b x)
                  (ftvar_in_a_cstrs C)) as [Hy | Hn]; [ exact Hy | ].
      pose proof (swap_cstrs_ftv_notin a b C (swap_atom a b x) Hn) as Hno.
      rewrite swap_atom_invol in Hno. contradiction. }
    assert (Hd' : swap_atom a b x `in` dom Ξ).
    { destruct (AtomSetProperties.In_dec (swap_atom a b x) (dom Ξ))
        as [Hy | Hn]; [ exact Hy | ].
      pose proof (swap_aenv_dom_notin a b Ξ (swap_atom a b x) Hn) as Hno.
      rewrite swap_atom_invol in Hno. contradiction. }
    clear - H Hc' Hd'. fsetdec. }
  intros x; split; intros Hin;
    [ exfalso; apply (Hkey x); clear - Hin; fsetdec
    | clear - Hin; fsetdec ].
Qed.

Lemma swap_guess_guard : forall a b (C : a_cstrs) (Q : pskl) (Ξ : aenv),
  (ftvar_in_a_cstrs C ∪ ftvar_in_pskl Q) ∩ dom Ξ [=] empty ->
  (ftvar_in_a_cstrs (swap_cstrs a b C) ∪ ftvar_in_pskl (swap_pskl a b Q))
    ∩ dom (swap_aenv a b Ξ) [=] empty.
Proof.
  intros a b C Q Ξ H.
  assert (Hkey : forall x,
            x `in` (ftvar_in_a_cstrs (swap_cstrs a b C)
                    ∪ ftvar_in_pskl (swap_pskl a b Q)) ->
            x `in` dom (swap_aenv a b Ξ) -> False).
  { intros x Hc Hd.
    assert (Hc' : swap_atom a b x
                  `in` (ftvar_in_a_cstrs C ∪ ftvar_in_pskl Q)).
    { destruct (AtomSetProperties.In_dec (swap_atom a b x)
                  (ftvar_in_a_cstrs C ∪ ftvar_in_pskl Q)) as [Hy | Hn];
        [ exact Hy | exfalso ].
      pose proof (swap_cstrs_ftv_notin a b C (swap_atom a b x)
                    ltac:(clear - Hn; fsetdec)) as Hno1.
      pose proof (swap_pskl_ftv_notin a b Q (swap_atom a b x)
                    ltac:(clear - Hn; fsetdec)) as Hno2.
      rewrite swap_atom_invol in Hno1. rewrite swap_atom_invol in Hno2.
      clear - Hc Hno1 Hno2. fsetdec. }
    assert (Hd' : swap_atom a b x `in` dom Ξ).
    { destruct (AtomSetProperties.In_dec (swap_atom a b x) (dom Ξ))
        as [Hy | Hn]; [ exact Hy | ].
      pose proof (swap_aenv_dom_notin a b Ξ (swap_atom a b x) Hn) as Hno.
      rewrite swap_atom_invol in Hno. contradiction. }
    clear - H Hc' Hd'. fsetdec. }
  intros x; split; intros Hin;
    [ exfalso; apply (Hkey x); clear - Hin; fsetdec
    | clear - Hin; fsetdec ].
Qed.

Lemma swap_cstrs_app : forall a b (C1 C2 : a_cstrs),
  swap_cstrs a b (C1 ++ C2) = swap_cstrs a b C1 ++ swap_cstrs a b C2.
Proof. intros. unfold swap_cstrs. apply List.map_app. Qed.

Lemma swap_ptyp_subst : forall a b A x B,
  swap_ptyp a b (subst_ptyp_in_ptyp A x B)
  = subst_ptyp_in_ptyp (swap_ptyp a b A) (swap_atom a b x) (swap_ptyp a b B).
Proof.
  intros a b A x; induction B; simpl; try solve [reflexivity | f_equal; auto].

  match goal with
  | |- context [if ?t then _ else _] => destruct t as [e | n0]
  end.
  - rewrite e. simpl.
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [_ | n1]
    end; [reflexivity | exfalso; apply n1; reflexivity].
  - simpl.
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [e1 | ?]
    end; [exfalso; apply n0; exact (swap_atom_inj a b _ _ e1) | reflexivity].
Qed.

Lemma swap_pskl_as_subst : forall a b P,
  b `notin` ftvar_in_pskl P ->
  swap_pskl a b P = subst_pskl_in_pskl (pskl_var_f b) a P.
Proof.
  induction P; simpl; intros Hb; f_equal;
    try solve [ reflexivity | apply IHP; fsetdec
              | apply IHP1; fsetdec | apply IHP2; fsetdec ].
  destruct (α == a) as [-> | Hne].
  - rewrite swap_atom_l. reflexivity.
  - rewrite swap_atom_other; [ reflexivity | assumption | ].
    intros ->. clear - Hb; fsetdec.
Qed.

Lemma swap_ptyp_as_subst : forall a b A,
  b `notin` ftvar_in_ptyp A ->
  swap_ptyp a b A = subst_ptyp_in_ptyp (ptyp_var_f b) a A.
Proof.
  induction A; simpl; intros Hb; f_equal;
    try solve [ reflexivity | apply IHA; fsetdec
              | apply IHA1; fsetdec | apply IHA2; fsetdec ].
  destruct (α == a) as [-> | Hne].
  - rewrite swap_atom_l. reflexivity.
  - rewrite swap_atom_other; [ reflexivity | assumption | ].
    intros ->. clear - Hb; fsetdec.
Qed.

Lemma swap_aenv_as_rename : forall β γ (Θ : aenv),
  γ `notin` ftvar_in_aenv Θ ->
  swap_aenv β γ Θ = rename_aenv γ β Θ.
Proof.
  induction Θ as [| [x bd] Θ' IH]; intros Hγ; [reflexivity |].
  simpl in Hγ. rewrite swap_aenv_cons. cbn [rename_aenv].
  f_equal; [ f_equal | apply IH; clear - Hγ; fsetdec ].
  -
    unfold swap_atom. destruct (x == β) as [-> | Hne].
    + destruct (β == β) as [_ | Hc]; [ reflexivity | contradiction ].
    + destruct (x == γ) as [-> | _]; [ exfalso; clear - Hγ; fsetdec | ].
      destruct (x == β) as [Hc | _]; [ contradiction | reflexivity ].
  -
    destruct bd; simpl in Hγ |- *.
    + reflexivity.
    + f_equal. apply swap_ptyp_as_subst. fsetdec.
    + f_equal. apply swap_pskl_as_subst. fsetdec.
    + reflexivity.
    + f_equal. apply swap_ptyp_as_subst. fsetdec.
Qed.

Lemma swap_pskl_subst : forall a b P x Q,
  swap_pskl a b (subst_pskl_in_pskl P x Q)
  = subst_pskl_in_pskl (swap_pskl a b P) (swap_atom a b x) (swap_pskl a b Q).
Proof.
  intros a b P x; induction Q; simpl; try solve [reflexivity | f_equal; auto].

  match goal with
  | |- context [if ?t then _ else _] => destruct t as [e | n0]
  end.
  - rewrite e. simpl.
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [_ | n1]
    end; [reflexivity | exfalso; apply n1; reflexivity].
  - simpl.
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [e1 | ?]
    end; [exfalso; apply n0; exact (swap_atom_inj a b _ _ e1) | reflexivity].
Qed.

Lemma lc_ptyp_swap : forall a b A, lc_ptyp A -> lc_ptyp (swap_ptyp a b A).
Proof.
  intros * H; induction H; simpl; try solve [constructor; auto].

  constructor. intros α0.
  specialize (H0 (swap_atom a b α0)).
  rewrite swap_ptyp_open in H0. simpl in H0.
  rewrite swap_atom_invol in H0. exact H0.
Qed.

Lemma lc_pskl_swap : forall a b P, lc_pskl P -> lc_pskl (swap_pskl a b P).
Proof.
  intros * H; induction H; simpl; try solve [constructor; auto].

  constructor. intros α0.
  specialize (H0 (swap_atom a b α0)).
  rewrite swap_pskl_open in H0. simpl in H0.
  rewrite swap_atom_invol in H0. exact H0.
Qed.

Lemma mono_ptyp_swap : forall a b A, mono_ptyp A -> mono_ptyp (swap_ptyp a b A).
Proof. intros * H; induction H; simpl; constructor; auto. Qed.

Lemma guarded_pskl_swap : forall a b P,
  guarded_pskl P -> guarded_pskl (swap_pskl a b P).
Proof.
  intros * H; destruct H; simpl; constructor; auto using lc_pskl_swap.
Qed.

Lemma nonghost_pskl_swap : forall a b P,
  nonghost_pskl P -> nonghost_pskl (swap_pskl a b P).
Proof. intros * H; destruct H; simpl; constructor. Qed.

Lemma swap_pskl_not_ghost : forall a b P,
  P <> pskl_ghost -> swap_pskl a b P <> pskl_ghost.
Proof.
  intros * H. destruct P; simpl; try discriminate. congruence.
Qed.

Lemma pskl_ghost_free_swap : forall a b P,
  pskl_ghost_free P -> pskl_ghost_free (swap_pskl a b P).
Proof.
  induction P; intros H; simpl in *; try contradiction; auto.
  destruct H; split; auto.
Qed.

Lemma a_binds_tvar_swap : forall a b α (Θ : aenv),
  a_binds_tvar α Θ -> a_binds_tvar (swap_atom a b α) (swap_aenv a b Θ).
Proof.
  intros * [h | [h | [τ h]]];
    [ left | right; left | right; right; exists (swap_ptyp a b τ) ];
    apply (swap_aenv_binds a b) in h; exact h.
Qed.

Lemma a_flex_tvar_swap : forall a b (Θ : aenv) α,
  a_flex_tvar Θ α -> a_flex_tvar (swap_aenv a b Θ) (swap_atom a b α).
Proof.
  intros * [h | [τ h]];
    [ left | right; exists (swap_ptyp a b τ) ];
    apply (swap_aenv_binds a b) in h; exact h.
Qed.

Lemma a_flex_swap : forall a b (Θ : aenv) P,
  a_flex Θ P -> a_flex (swap_aenv a b Θ) (swap_pskl a b P).
Proof.
  intros * H; destruct H; simpl.
  - apply a_flex__var. apply (swap_aenv_binds a b) in H. exact H.
  - apply a_flex__var_def with (τ := swap_ptyp a b τ).
    apply (swap_aenv_binds a b) in H. exact H.
Qed.

Lemma a_non_flex_swap : forall a b (Θ : aenv) P,
  a_non_flex Θ P -> a_non_flex (swap_aenv a b Θ) (swap_pskl a b P).
Proof.
  intros * [Hlc Hnf]. split; [auto using lc_pskl_swap |].
  intros Hf. apply Hnf.
  apply (a_flex_swap a b) in Hf.
  rewrite swap_aenv_invol, swap_pskl_invol in Hf. exact Hf.
Qed.

Lemma a_suffix_swap : forall a b (Ξ : aenv),
  a_suffix Ξ -> a_suffix (swap_aenv a b Ξ).
Proof.
  intros * H; induction H; simpl; [constructor |].
  constructor; [exact IHa_suffix |].
  destruct H0; simpl; constructor.
Qed.

Lemma swap_aenv_minus : forall a b (Θ : aenv) Δ,
  swap_aenv a b (aenv_minus Θ Δ) = aenv_minus (swap_aenv a b Θ) (swap_atoms a b Δ).
Proof.
  intros a b Θ Δ. induction Θ as [| [x bd] Θ IH]; [ reflexivity | ].
  rewrite swap_aenv_cons. unfold aenv_minus in *. simpl.
  destruct (AtomSetImpl.mem x Δ) eqn:Hm;
    destruct (AtomSetImpl.mem (swap_atom a b x) (swap_atoms a b Δ)) eqn:Hm';
    simpl; try exact IH; try (f_equal; exact IH).
  all: exfalso.
  - apply AtomSetFacts.mem_iff in Hm. apply AtomSetFacts.not_mem_iff in Hm'.
    apply Hm'. apply swap_atoms_in. exact Hm.
  - apply AtomSetFacts.not_mem_iff in Hm. apply AtomSetFacts.mem_iff in Hm'.
    apply (proj1 (swap_atoms_spec a b Δ _)) in Hm'. rewrite swap_atom_invol in Hm'.
    contradiction.
Qed.

Lemma a_wf_pskl_swap : forall a b (Θ : aenv) (Δ : atoms) P,
  a_wf_pskl Θ Δ P ->
  forall Δ', Δ' [=] swap_atoms a b Δ ->
  a_wf_pskl (swap_aenv a b Θ) Δ' (swap_pskl a b P).
Proof.
  intros a b Θ Δ P H; induction H; intros Δ' HΔ; simpl.
  - constructor.
  - constructor. auto using a_binds_tvar_swap.
  - constructor; auto.
  - apply a_wf_pskl__all with (L := swap_atoms a b L).
    intros α0 Hα0.
    assert (hin : swap_atom a b α0 `notin` L)
      by (intro hc; apply Hα0; apply swap_atoms_spec; exact hc).
    pose proof (eq_swap_atoms_add a b (swap_atom a b α0) _ _ HΔ) as Hadd.
    rewrite swap_atom_invol in Hadd.
    specialize (H0 _ hin _ Hadd).
    rewrite swap_pskl_open in H0. simpl in H0.
    rewrite swap_atom_invol in H0. exact H0.
  - constructor.
  - constructor; [auto using guarded_pskl_swap |].
    rewrite (aenv_minus_eq _ HΔ), <- swap_aenv_minus.
    apply IHa_wf_pskl. rewrite swap_atoms_empty. fsetdec.
Qed.

Lemma swap_atom_neq : forall a b x y,
  x <> y -> swap_atom a b x <> swap_atom a b y.
Proof. intros * Hne He. apply Hne. exact (swap_atom_inj a b _ _ He). Qed.

Lemma swap_pskl_neq_var : forall a b P α,
  P <> pskl_var_f α ->
  swap_pskl a b P <> pskl_var_f (swap_atom a b α).
Proof.
  intros * Hne He. apply Hne.
  rewrite <- (swap_pskl_invol a b P), He. simpl.
  rewrite swap_atom_invol. reflexivity.
Qed.

Lemma flex_r_off_swap : forall a b Θ P',
  flex_r_off Θ P' -> flex_r_off (swap_aenv a b Θ) (swap_pskl a b P').
Proof.
  intros a b Θ P' H β Heq Hf.
  destruct P' as [ | | γ | | | | ]; simpl in Heq; try discriminate Heq.
  injection Heq as <-.
  apply (H γ eq_refl).
  apply (a_flex_tvar_swap a b) in Hf.
  rewrite swap_aenv_invol, swap_atom_invol in Hf. exact Hf.
Qed.

Lemma forall_r_off_swap : forall a b m P',
  forall_r_off m P' -> forall_r_off m (swap_pskl a b P').
Proof.
  intros a b m P' H B Heq Hm.
  destruct P' as [ | | | | P0 | | ]; simpl in Heq; try discriminate.
  injection Heq as Heq0; subst B.
  intro Hgf. apply (H P0 eq_refl Hm).
  simpl in Hgf |- *.
  apply (pskl_ghost_free_swap a b) in Hgf.
  rewrite swap_pskl_invol in Hgf. exact Hgf.
Qed.

Lemma peel_l_off_swap : forall a b P,
  peel_l_off P -> peel_l_off (swap_pskl a b P).
Proof.
  intros a b P [H1 H2]; destruct P; simpl;
    try solve [ split; intros; discriminate ];
    [ exfalso; exact (H1 _ eq_refl) | exfalso; exact (H2 _ eq_refl) ].
Qed.

Lemma solve_l_off_swap : forall a b P,
  solve_l_off P -> solve_l_off (swap_pskl a b P).
Proof.
  intros a b P [H0 [H1 H2]]; destruct P; simpl;
    try solve [ split;
                [ intros; discriminate | split; intros; discriminate ] ];
    [ exfalso; exact (H0 _ eq_refl)
    | exfalso; exact (H1 _ eq_refl)
    | exfalso; exact (H2 _ eq_refl) ].
Qed.

Local Lemma notin_add_split : forall (x y : atom) (S : atoms),
  x `notin` add y S -> x <> y /\ x `notin` S.
Proof. intros; split; fsetdec. Qed.

Local Lemma notin_add_join : forall (x y : atom) (S : atoms),
  x <> y -> x `notin` S -> x `notin` add y S.
Proof. intros; fsetdec. Qed.

Ltac swap_freshness :=
  repeat match goal with
         | H : _ `notin` add _ _ |- _ =>
             apply notin_add_split in H; destruct H
         | H : _ `notin` (_ `union` _) |- _ =>
             apply notin_union_split in H; destruct H
         end;
  repeat match goal with
         | |- _ `notin` add _ _ => apply notin_add_join
         | |- _ `notin` (_ `union` _) => apply notin_union_join
         end;
  auto using swap_aenv_ftvar_notin, swap_pskl_ftv_notin,
             swap_ptyp_ftv_notin, swap_aenv_dom_notin, swap_atom_neq.

Scheme a_looksub_sind := Induction for a_looksub Sort Prop
  with a_lookeq_sind := Induction for a_lookeq Sort Prop.
Combined Scheme a_looksub_lookeq_sind from a_looksub_sind, a_lookeq_sind.

Lemma a_looksub_lookeq_swap : forall a b,
  (forall Θ α m P P' Ξ C,
     a_looksub Θ α m P P' Ξ C ->
     a_looksub (swap_aenv a b Θ) (swap_atom a b α) m
       (swap_pskl a b P) (swap_pskl a b P')
       (swap_aenv a b Ξ) (swap_cstrs a b C)) /\
  (forall Θ α P P' Ξ C,
     a_lookeq Θ α P P' Ξ C ->
     a_lookeq (swap_aenv a b Θ) (swap_atom a b α)
       (swap_pskl a b P) (swap_pskl a b P')
       (swap_aenv a b Ξ) (swap_cstrs a b C)).
Proof.
  intros a b.
  apply (a_looksub_lookeq_sind
           (fun Θ α m P P' Ξ C _ =>
              a_looksub (swap_aenv a b Θ) (swap_atom a b α) m
                (swap_pskl a b P) (swap_pskl a b P')
                (swap_aenv a b Ξ) (swap_cstrs a b C))
           (fun Θ α P P' Ξ C _ =>
              a_lookeq (swap_aenv a b Θ) (swap_atom a b α)
                (swap_pskl a b P) (swap_pskl a b P')
                (swap_aenv a b Ξ) (swap_cstrs a b C)));
    intros; simpl;
    rewrite ?swap_aenv_app, ?swap_cstrs_app, ?swap_pskl_open_var in *;
    try solve [eauto 5 using a_looksub, a_lookeq, swap_pskl_ftv_notin,
      swap_pskl_neq_var, guarded_pskl_swap, pskl_ghost_free_swap,
      swap_look_guard, swap_pskl_not_ghost, forall_r_off_swap, flex_r_off_swap];
    try solve [apply a_looksub__check; auto 3 using swap_pskl_neq_var,
      guarded_pskl_swap, pskl_ghost_free_swap];
    try solve [apply a_looksub__arrow; auto 3 using swap_look_guard |
               apply a_lookeq__arrow; auto 3 using swap_look_guard].
  - apply a_looksub__forall_r with (β := swap_atom a b β);
      auto 3 using swap_pskl_ftv_in, swap_pskl_neq_var;
      try solve [apply pskl_ghost_free_swap; auto 2]; swap_freshness.
  - apply a_looksub__forall_l with (β := swap_atom a b β);
      auto 3 using swap_pskl_not_ghost, forall_r_off_swap;
      try solve [apply swap_pskl_ftv_in; auto 2]; swap_freshness.
  - apply a_lookeq__flex_r;
      auto 3 using a_flex_tvar_swap, swap_pskl_neq_var, swap_pskl_ftv_in;
      swap_freshness.
  - apply a_lookeq__forall_inh with (β := swap_atom a b β); auto 2;
      try solve [apply swap_pskl_ftv_in; auto 2]; swap_freshness.
  - apply a_lookeq__forall_syn with (β := swap_atom a b β); auto 2;
      try solve [apply swap_pskl_ftv_in; auto 2]; swap_freshness.
  - apply a_lookeq__univ_ghost1 with (β := swap_atom a b β); auto 2;
      try solve [apply swap_pskl_ftv_in; auto 2]; swap_freshness.
Qed.

Scheme a_solve_sub_sind := Induction for a_solve_sub Sort Prop
  with a_solve_eq_sind := Induction for a_solve_eq Sort Prop.
Combined Scheme a_solve_sub_eq_sind from a_solve_sub_sind, a_solve_eq_sind.

Lemma a_solve_sub_eq_swap : forall a b,
  (forall Θ m P Q Ξ P',
     a_solve_sub Θ m P Q Ξ P' ->
     a_solve_sub (swap_aenv a b Θ) m (swap_pskl a b P) (swap_pskl a b Q)
       (swap_aenv a b Ξ) (swap_pskl a b P')) /\
  (forall Θ P Q Ξ P',
     a_solve_eq Θ P Q Ξ P' ->
     a_solve_eq (swap_aenv a b Θ) (swap_pskl a b P) (swap_pskl a b Q)
       (swap_aenv a b Ξ) (swap_pskl a b P')).
Proof.
  intros a b.
  apply (a_solve_sub_eq_sind
           (fun Θ m P Q Ξ P' _ =>
              a_solve_sub (swap_aenv a b Θ) m (swap_pskl a b P)
                (swap_pskl a b Q) (swap_aenv a b Ξ) (swap_pskl a b P'))
           (fun Θ P Q Ξ P' _ =>
              a_solve_eq (swap_aenv a b Θ) (swap_pskl a b P)
                (swap_pskl a b Q) (swap_aenv a b Ξ) (swap_pskl a b P')));
    intros; simpl;

    rewrite ? swap_aenv_app in *; rewrite ? swap_aenv_cons in *; simpl in *;
    rewrite ?swap_pskl_close, ?swap_pskl_open_var, ?swap_pskl_ptyp_to_pskl in *;
    try solve [eauto 4 using a_solve_sub, a_solve_eq, peel_l_off_swap,
      guarded_pskl_swap, pskl_ghost_free_swap, a_flex_tvar_swap,
      a_non_flex_swap, nonghost_pskl_swap, a_guess_mono_swap];
    try solve [apply a_solve_sub__check;
      auto 3 using guarded_pskl_swap, pskl_ghost_free_swap];
    try solve [apply a_solve_eq__flex_r;
      auto 3 using a_flex_tvar_swap, a_non_flex_swap, nonghost_pskl_swap, a_guess_mono_swap];
    try solve [econstructor; auto 2; swap_freshness].
  - apply a_solve_sub__forall_r with (β := swap_atom a b β);
      auto 3 using solve_l_off_swap;
      try solve [apply pskl_ghost_free_swap; auto 2]; swap_freshness.
Qed.

Lemma a_solve_cstr_swap : forall a b Θ C P Ξ Q,
  a_solve_cstr Θ C P Ξ Q ->
  a_solve_cstr (swap_aenv a b Θ) (swap_cstrs a b C)
    (swap_pskl a b P) (swap_aenv a b Ξ) (swap_pskl a b Q).
Proof.
  intros * H; induction H; simpl.
  - apply a_solve_cstr__empty.
  - apply a_solve_cstr__sub. apply (proj1 (a_solve_sub_eq_swap a b)); auto.
  - rewrite swap_aenv_app.
    apply a_solve_cstr__eq with (P'' := swap_pskl a b P'');
      [ apply (proj2 (a_solve_sub_eq_swap a b)); auto
      | rewrite <- swap_aenv_app; exact IHa_solve_cstr ].
Qed.

Lemma a_extract_swap : forall a b Θ NM α m P P' Ξ Q,
  a_extract Θ NM α m P P' Ξ Q ->
  a_extract (swap_aenv a b Θ) NM (swap_atom a b α) m
    (swap_pskl a b P) (swap_pskl a b P')
    (swap_aenv a b Ξ) (swap_pskl a b Q).
Proof.
  intros * H; destruct H.
  rewrite ! swap_aenv_app.
  apply a_extract__solve with (C := swap_cstrs a b C) (Q := swap_pskl a b Q).
  - apply (proj1 (a_looksub_lookeq_swap a b)); auto.
  - rewrite <- swap_aenv_app.
    pose proof (a_solve_cstr_swap a b _ _ _ _ _ H0) as h. exact h.
  - rewrite <- ! swap_aenv_app. apply a_guess_swap; auto.
  -
    apply swap_look_guard; assumption.
  -
    apply swap_guess_guard; assumption.
Qed.

Lemma swap_aenv_dom_in_rev : forall a b (Θ : aenv) x,
  x `in` dom (swap_aenv a b Θ) -> swap_atom a b x `in` dom Θ.
Proof.
  intros * Hx.
  pose proof (swap_aenv_dom_in a b (swap_aenv a b Θ) x Hx) as h.
  rewrite swap_aenv_invol in h. exact h.
Qed.

Lemma swap_pskl_ftv_in_rev : forall a b P x,
  x `in` ftvar_in_pskl (swap_pskl a b P) -> swap_atom a b x `in` ftvar_in_pskl P.
Proof.
  intros * Hx.
  pose proof (swap_pskl_ftv_in a b (swap_pskl a b P) x Hx) as h.
  rewrite swap_pskl_invol in h. exact h.
Qed.

Lemma swap_inter_ftv_empty : forall a b (Δ Δ' : atoms) P,
  Δ' [=] swap_atoms a b Δ ->
  Δ ∩ ftvar_in_pskl P [=] empty ->
  Δ' ∩ ftvar_in_pskl (swap_pskl a b P) [=] empty.
Proof.
  intros * HΔ Hemp y. split; intros Hy; [| fsetdec].
  exfalso.
  assert (h1 : y `in` Δ') by fsetdec.
  assert (h2 : y `in` ftvar_in_pskl (swap_pskl a b P)) by fsetdec.
  assert (h1' : y `in` swap_atoms a b Δ) by fsetdec.
  pose proof (proj1 (swap_atoms_spec a b Δ y) h1') as h1''.
  pose proof (swap_pskl_ftv_in_rev a b P y h2) as h2'.
  assert (swap_atom a b y `in` (Δ ∩ ftvar_in_pskl P)) by (apply inter_3; auto).
  fsetdec.
Qed.

Lemma a_assign_unify_consis_swap : forall a b,
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
     {{ (swap_aenv a b Θ0) ⊲[ swap_aenv a b Ξ ]
       (swap_atom a b α) ≔ (swap_pskl a b P) ⊣ (swap_aenv a b Θ1) }}a) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
     {{ (swap_aenv a b Θ0) ⊲
       (swap_atom a b α) ≈ᵘ (swap_atom a b β) ⊣ (swap_aenv a b Θ1) }}a) /\
  (forall Δ1 Δ2 Θ0 P0 P Q Θ1,
     a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 ->
     forall Δ1' Δ2',
       Δ1' [=] swap_atoms a b Δ1 ->
       Δ2' [=] swap_atoms a b Δ2 ->
     a_consis Δ1' Δ2' (swap_aenv a b Θ0) (swap_pskl a b P0)
       (swap_pskl a b P) (swap_pskl a b Q) (swap_aenv a b Θ1)).
Proof.
  intros a b.
  apply a_assign_unify_consis_mutind;
    try solve [intros; simpl;
      rewrite ?swap_aenv_app in *;
      econstructor; eauto 3 using swap_atom_neq,
        swap_pskl_ftv_in, swap_pskl_ftv_notin, swap_aenv_dom_notin,
        a_flex_tvar_swap, guarded_pskl_swap, a_non_flex_swap,
        swap_pskl_not_ghost, swap_inter_ftv_empty].
  -
    intros Θ0 Ξ α P βs τ Hnα Hg Hmono Huniq Hfr. simpl.
    rewrite !swap_aenv_app.
    apply a_assign__solve_m;
      auto using swap_pskl_ftv_notin, a_guess_mono_swap, mono_ptyp_swap,
                 swap_aenv_uniq.
    intros α1 Hα1.
    pose proof (swap_aenv_dom_in_rev a b βs α1 Hα1) as hdom.
    specialize (Hfr _ hdom).
    apply notin_add_split in Hfr; destruct Hfr as [hne hdom0].
    apply notin_add_join.
    +
      intros he. apply hne.
      rewrite he, swap_atom_invol. reflexivity.
    +
      rewrite <- swap_aenv_app.
      intros hc.
      pose proof (swap_aenv_dom_in_rev a b (Ξ ++ Θ0) α1 hc). contradiction.
  -
    intros Θ0 Θ1 Ξ α β τ P Q Hflex Hnd Hd IH. simpl.
    eapply a_assign__assign.
    + exact (a_flex_tvar_swap a b _ _ Hflex).
    + apply swap_aenv_dom_notin; exact Hnd.
    + specialize (IH empty empty
                     (empty_eq_swap_atoms_empty a b)
                     (empty_eq_swap_atoms_empty a b)).
      rewrite swap_aenv_app in IH.
      rewrite !swap_pskl_subst in IH.
      rewrite !swap_pskl_ptyp_to_pskl in IH.
      change (swap_pskl a b (pskl_var_f α)) with
        (pskl_var_f (swap_atom a b α)) in IH.
      exact IH.
  -
    intros Θ0 Θ1 α1 τ α β Q Hfα Hfβ Hnd Hd IH. simpl.
    eapply a_unify__flex_assign.
    + exact (a_flex_tvar_swap a b _ _ Hfα).
    + exact (a_flex_tvar_swap a b _ _ Hfβ).
    + apply swap_aenv_dom_notin; exact Hnd.
    + specialize (IH empty empty
                     (empty_eq_swap_atoms_empty a b)
                     (empty_eq_swap_atoms_empty a b)).
      rewrite !swap_pskl_ptyp_to_pskl in IH.
      rewrite !swap_ptyp_subst in IH.
      change (swap_ptyp a b (ptyp_var_f α)) with
        (ptyp_var_f (swap_atom a b α)) in IH.
      change (swap_ptyp a b (ptyp_var_f β)) with
        (ptyp_var_f (swap_atom a b β)) in IH.
      exact IH.
  -
    intros Θ0 Θ1 c bd α β Hb Hnd Hd IH. simpl.
    apply a_unify__skip_other.
    + destruct Hb as [-> | [[Q ->] | [Q ->]]]; simpl.
      * left; reflexivity.
      * right; left; eexists; reflexivity.
      * right; right; eexists; reflexivity.
    + apply swap_aenv_dom_notin; exact Hnd.
    + exact IH.
  -
    intros Δ1 Δ2 Θ0 α Hb Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__rigid.
    pose proof (swap_aenv_binds a b _ _ _ Hb) as h. exact h.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    rewrite swap_pskl_close.
    apply a_consis__forall_inh.
    + swap_freshness; eauto using swap_notin_eq.
    + specialize (IH (add (swap_atom a b α) Δ1') (add (swap_atom a b α) Δ2')
                     (eq_swap_atoms_add a b α _ _ HΔ1)
                        (eq_swap_atoms_add a b α _ _ HΔ2)).
      rewrite !swap_pskl_open_var in IH; auto 2.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    rewrite swap_pskl_close.
    apply a_consis__forall_syn.
    + swap_freshness; eauto using swap_notin_eq.
    + specialize (IH Δ1' (add (swap_atom a b α) Δ2')
                     HΔ1 (eq_swap_atoms_add a b α _ _ HΔ2)).
      rewrite !swap_pskl_open_var in IH; auto 2.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    rewrite swap_pskl_close.
    apply a_consis__univ_ghost1.
    + swap_freshness; eauto using swap_notin_eq.
    + specialize (IH (add (swap_atom a b α) Δ1') Δ2'
                     (eq_swap_atoms_add a b α _ _ HΔ1) HΔ2).
      rewrite !swap_pskl_open_var in IH; auto 2.
Qed.

Lemma a_consis_empty_swap : forall a b Θ0 P0 P Q Θ1,
  {{ Θ0 ⊢[ P0 ] P ∼ Q ⊣ Θ1 }}a ->
  {{ (swap_aenv a b Θ0) ⊢[ swap_pskl a b P0 ]
    (swap_pskl a b P) ∼ (swap_pskl a b Q) ⊣ (swap_aenv a b Θ1) }}a.
Proof.
  intros * H.
  apply (proj2 (proj2 (a_assign_unify_consis_swap a b)) _ _ _ _ _ _ _ H);
    apply empty_eq_swap_atoms_empty.
Qed.

Lemma a_consis_chk_swap : forall a b Θ0 A B Θ1,
  a_consis_chk Θ0 A B Θ1 ->
  a_consis_chk (swap_aenv a b Θ0) (swap_pskl a b A) (swap_pskl a b B)
    (swap_aenv a b Θ1).
Proof.
  intros * [Q H]. exists (swap_pskl a b Q). apply a_consis_empty_swap; auto.
Qed.

Scheme a_sub_sind := Induction for a_sub Sort Prop
  with a_sub_flex_sind := Induction for a_sub_flex Sort Prop.
Combined Scheme a_sub_sub_flex_sind from a_sub_sind, a_sub_flex_sind.

Lemma a_sub_sub_flex_swap : forall a b,
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 ->
     a_sub NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
       (swap_pskl a b P) (swap_pskl a b Q) (swap_aenv a b Θ1)) /\
  (forall NM M P0 Θ0 Ξ α A Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
     a_sub_flex NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
       (swap_aenv a b Ξ) (swap_atom a b α) (swap_pskl a b A)
       (swap_aenv a b Θ1)).
Proof.
  intros a b.
  apply (a_sub_sub_flex_sind
           (fun NM M P0 Θ0 P Q Θ1 _ =>
              a_sub NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
                (swap_pskl a b P) (swap_pskl a b Q) (swap_aenv a b Θ1))
           (fun NM M P0 Θ0 Ξ α A Θ1 _ =>
              a_sub_flex NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
                (swap_aenv a b Ξ) (swap_atom a b α) (swap_pskl a b A)
                (swap_aenv a b Θ1))).

  -
    intros NM P Θ0. simpl. apply a_sub__infer.
  -
    intros Θ0 Θ1 A B Hgfa Hgfb Hga Hgb Hchk. simpl.
    apply a_sub__check;
      auto using guarded_pskl_swap, pskl_ghost_free_swap, a_consis_chk_swap.
  -
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huniq Hfr Hd IH. simpl.
    apply a_sub__forall_r with (α := swap_atom a b α) (Ξ := swap_aenv a b Ξ).
    + apply pskl_ghost_free_swap; exact Hgf.
    + auto using a_suffix_swap.
    + rewrite <- swap_aenv_app. auto using swap_aenv_uniq.
    + swap_freshness.
    + rewrite !swap_pskl_open_var in IH.
      rewrite !swap_aenv_app in IH. exact IH.
  -
    intros Θ0 P Hg. simpl.
    apply a_sub__univ_ghost_r; auto using guarded_pskl_swap.
  -
    intros NM M P0 Θ0 Θ1 α A Hd IH. simpl.
    apply a_sub__flex_mono. exact IH.
  -
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hd IH. simpl.
    eapply a_sub__arrow;
      [ exact (a_consis_empty_swap a b _ _ _ _ _ Hc) | exact IH ].
  -
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hm Hg Hfr Hex Huniq Hwf Hd IH. simpl.
    apply a_sub__forall_l with (α := swap_atom a b α)
      (Ξ := swap_aenv a b Ξ) (P1 := swap_pskl a b P1); auto.
    + destruct Hg as [hg | ->];
        [ left; auto using guarded_pskl_swap | right; reflexivity ].
    + swap_freshness.
    + pose proof (a_extract_swap a b _ _ _ _ _ _ _ _ Hex) as h.
      rewrite swap_pskl_open_var in h. exact h.
    + rewrite <- swap_aenv_app. auto using swap_aenv_uniq.
    + rewrite <- swap_aenv_app.
      apply (a_wf_pskl_swap a b _ _ _ Hwf).
      apply empty_eq_swap_atoms_empty.
    + rewrite swap_pskl_open in IH.
      rewrite swap_aenv_app in IH. exact IH.
  -
    intros M Θ0 P0 Hm. simpl. apply a_sub__ghost; exact Hm.
  -
    intros M Θ0 Θ1 P0 P Q Hm Hd IH. simpl.
    apply a_sub__univ_ghost_l; auto.

  -
    intros NM M P0 Θ0 Θ1 Ξ α0 α β A Hne Hfα Hfβ Hd IH. simpl.
    apply a_sub_flex__solve
      with (α := swap_atom a b α) (β := swap_atom a b β);
      [ auto using swap_atom_neq | | |].
    + rewrite <- swap_aenv_app. swap_freshness.
    + rewrite <- swap_aenv_app. swap_freshness.
    + rewrite !swap_aenv_app in IH. exact IH.
  -
    intros NM M P0 Θ0 Θ1 Ξ α β τ A Hout Hd IH. simpl.
    apply a_sub_flex__assign; auto using swap_aenv_dom_notin.
    rewrite !swap_pskl_subst in IH.
    rewrite !swap_pskl_ptyp_to_pskl in IH.
    change (swap_pskl a b (pskl_var_f α)) with
      (pskl_var_f (swap_atom a b α)) in IH.
    rewrite swap_aenv_app in IH. exact IH.
  -
    intros NM M P0 Θ0 Θ1 Ξ α β A Hne Hin Hd IH. simpl.
    apply a_sub_flex__depend;
      auto using swap_atom_neq, swap_pskl_ftv_in.
    rewrite swap_aenv_app in IH. exact IH.
  -
    intros NM M P0 Θ0 Θ1 Ξ α β A Hne Hnf Hout Hd IH. simpl.
    apply a_sub_flex__skip;
      auto using swap_atom_neq, swap_pskl_ftv_notin, swap_aenv_dom_notin.
  -
    intros NM M P0 Θ0 Θ1 Ξ α β A Hne Hnf Hout Hd IH. simpl.
    apply a_sub_flex__skip_rigid;
      auto using swap_atom_neq, swap_pskl_ftv_notin, swap_aenv_dom_notin.
  -
    intros NM M P0 Θ0 Θ1 Ξ α x Q A Hout Hd IH. simpl.
    apply a_sub_flex__skip_tm_var;
      [ apply swap_aenv_dom_notin; exact Hout | exact IH ].
  -
    intros NM M P0 Θ0 Θ1 Ξ α x Q A Hout Hd IH. simpl.
    apply a_sub_flex__skip_tm_skl;
      [ apply swap_aenv_dom_notin; exact Hout | exact IH ].
Qed.

Lemma swap_abind_fresh_id : forall a b bd,
  a `notin` ftvar_in_abind bd -> b `notin` ftvar_in_abind bd ->
  swap_abind a b bd = bd.
Proof.
  intros; destruct bd; simpl in *; f_equal;
    auto using swap_ptyp_fresh_id, swap_pskl_fresh_id.
Qed.

Lemma swap_aenv_fresh_id : forall a b (Θ : aenv),
  a `notin` ftvar_in_aenv Θ -> b `notin` ftvar_in_aenv Θ ->
  swap_aenv a b Θ = Θ.
Proof.
  intros a b Θ; induction Θ as [| [x bd] Θ']; intros Ha Hb; [reflexivity |].
  simpl in Ha, Hb. rewrite swap_aenv_cons.
  rewrite swap_atom_other; [| fsetdec | fsetdec].
  rewrite swap_abind_fresh_id; [| fsetdec | fsetdec].
  rewrite IHΘ'; [reflexivity | fsetdec | fsetdec].
Qed.

Lemma a_sub_swap_junk : forall β0 β1 NM M P0 Θ0 P Q Θ1,
  a_sub NM M P0 Θ0 P Q Θ1 ->
  β0 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
     `union` ftvar_in_pskl P ->
  β1 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
     `union` ftvar_in_pskl P ->
  a_sub NM M P0 Θ0 P (swap_pskl β0 β1 Q) (swap_aenv β0 β1 Θ1).
Proof.
  intros * Hd H0 H1.
  apply notin_union_split in H0; destruct H0 as [h0 H0].
  apply notin_union_split in H0; destruct H0 as [h0' h0''].
  apply notin_union_split in H1; destruct H1 as [h1 H1].
  apply notin_union_split in H1; destruct H1 as [h1' h1''].
  pose proof (proj1 (a_sub_sub_flex_swap β0 β1) _ _ _ _ _ _ _ Hd) as h.
  rewrite (swap_aenv_fresh_id β0 β1 Θ0) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P0) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P) in h; auto.
Qed.

Lemma a_sub_flex_swap_junk : forall β0 β1 NM M P0 Θ0 Ξ α A Θ1,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  β0 <> α -> β1 <> α ->
  β0 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P0 ->
  β1 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P0 ->
  a_sub_flex NM M P0 Θ0 Ξ α (swap_pskl β0 β1 A) (swap_aenv β0 β1 Θ1).
Proof.
  intros * Hd Hne0 Hne1 H0 H1.
  apply notin_union_split in H0; destruct H0 as [h0 H0].
  apply notin_union_split in H0; destruct H0 as [h0' h0''].
  apply notin_union_split in H1; destruct H1 as [h1 H1].
  apply notin_union_split in H1; destruct H1 as [h1' h1''].
  pose proof (proj2 (a_sub_sub_flex_swap β0 β1) _ _ _ _ _ _ _ _ Hd) as h.
  rewrite (swap_aenv_fresh_id β0 β1 Θ0) in h; auto.
  rewrite (swap_aenv_fresh_id β0 β1 Ξ) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P0) in h; auto.
  rewrite (swap_atom_other β0 β1 α) in h; auto.
Qed.

Lemma swap_junk_dom_out : forall β0 β1 (Θ1 : aenv),
  β1 `notin` dom Θ1 ->
  β0 `notin` dom (swap_aenv β0 β1 Θ1).
Proof.
  intros * Hn Hc.
  pose proof (swap_aenv_dom_in_rev β0 β1 Θ1 β0 Hc) as h.
  rewrite swap_atom_l in h. contradiction.
Qed.

Lemma eq_swap_atoms_fresh : forall a b (S : atoms),
  a `notin` S -> b `notin` S -> S [=] swap_atoms a b S.
Proof.
  intros * Ha Hb y. split; intros Hy.
  - apply swap_atoms_spec.
    destruct (y == a); [ subst; contradiction | ].
    destruct (y == b); [ subst; contradiction | ].
    rewrite swap_atom_other; auto.
  - apply swap_atoms_spec in Hy.
    destruct (y == a); [ subst; rewrite swap_atom_l in Hy; contradiction | ].
    destruct (y == b); [ subst; rewrite swap_atom_r in Hy; contradiction | ].
    rewrite swap_atom_other in Hy; auto.
Qed.

Lemma a_assign_swap_junk : forall β0 β1 Θ0 Ξ α P Θ1,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  β0 <> α -> β1 <> α ->
  β0 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  β1 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ (swap_aenv β0 β1 Θ1) }}a.
Proof.
  intros * Hd Hne0 Hne1 H0 H1.
  apply notin_union_split in H0; destruct H0 as [h0 H0].
  apply notin_union_split in H0; destruct H0 as [h0' h0''].
  apply notin_union_split in H1; destruct H1 as [h1 H1].
  apply notin_union_split in H1; destruct H1 as [h1' h1''].
  pose proof (proj1 (a_assign_unify_consis_swap β0 β1) _ _ _ _ _ Hd) as h.
  rewrite (swap_aenv_fresh_id β0 β1 Θ0) in h; auto.
  rewrite (swap_aenv_fresh_id β0 β1 Ξ) in h; auto.
  rewrite (swap_atom_other β0 β1 α) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P) in h; auto.
Qed.

Lemma a_unify_swap_junk : forall β0 β1 Θ0 α β Θ1,
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  β0 <> α -> β1 <> α -> β0 <> β -> β1 <> β ->
  β0 `notin` ftvar_in_aenv Θ0 -> β1 `notin` ftvar_in_aenv Θ0 ->
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ (swap_aenv β0 β1 Θ1) }}a.
Proof.
  intros * Hd Hnα0 Hnα1 Hnβ0 Hnβ1 H0 H1.
  pose proof (proj1 (proj2 (a_assign_unify_consis_swap β0 β1))
                _ _ _ _ Hd) as h.
  rewrite (swap_aenv_fresh_id β0 β1 Θ0) in h; auto.
  rewrite (swap_atom_other β0 β1 α) in h; auto.
  rewrite (swap_atom_other β0 β1 β) in h; auto.
Qed.

Lemma a_consis_swap_junk : forall β0 β1 Δ1 Δ2 Θ0 P0 P Q Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
  β0 `notin` Δ1 `union` Δ2 ->
  β1 `notin` Δ1 `union` Δ2 ->
  β0 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
     `union` ftvar_in_pskl P ->
  β1 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
     `union` ftvar_in_pskl P ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ (swap_pskl β0 β1 Q)
    ⊣ (swap_aenv β0 β1 Θ1) }}a.
Proof.
  intros * Hd HS0 HS1 H0 H1.
  apply notin_union_split in H0; destruct H0 as [h0 H0].
  apply notin_union_split in H0; destruct H0 as [h0' h0''].
  apply notin_union_split in H1; destruct H1 as [h1 H1].
  apply notin_union_split in H1; destruct H1 as [h1' h1''].
  pose proof (proj2 (proj2 (a_assign_unify_consis_swap β0 β1))
                _ _ _ _ _ _ _ Hd Δ1 Δ2
                (eq_swap_atoms_fresh β0 β1 Δ1 ltac:(solve_notin_auto) ltac:(solve_notin_auto))
                (eq_swap_atoms_fresh β0 β1 Δ2 ltac:(solve_notin_auto) ltac:(solve_notin_auto)))
    as h.
  rewrite (swap_aenv_fresh_id β0 β1 Θ0) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P0) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P) in h; auto.
Qed.

Lemma a_sub_flex_skip_no_loss : forall NM M P0 Θ0 Θ1 Ξ α β A,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  α <> β ->
  β `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P0 ->
  exists γ, γ `notin` dom Θ1 /\
    a_sub_flex NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α
      (swap_pskl β γ A) ((β ~ abind_flex_mono) ++ swap_aenv β γ Θ1).
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P0 `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_sub_flex__skip.
  - exact Hne.
  - clear - Hfr; fsetdec.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_sub_flex_swap_junk;
      [ exact Hd | auto | clear - Fr; fsetdec | exact Hfr
      | clear - Fr; fsetdec ].
Qed.

Lemma a_sub_flex_skip_rigid_no_loss : forall NM M P0 Θ0 Θ1 Ξ α β A,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  α <> β ->
  β `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P0 ->
  exists γ, γ `notin` dom Θ1 /\
    a_sub_flex NM M P0 ((β ~ abind_tvar) ++ Θ0) Ξ α
      (swap_pskl β γ A) ((β ~ abind_tvar) ++ swap_aenv β γ Θ1).
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P0 `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_sub_flex__skip_rigid.
  - exact Hne.
  - clear - Hfr; fsetdec.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_sub_flex_swap_junk;
      [ exact Hd | auto | clear - Fr; fsetdec | exact Hfr
      | clear - Fr; fsetdec ].
Qed.

Lemma a_sub_flex_assign_no_loss : forall NM M P0 Θ0 Θ1 Ξ α β τ A,
  a_sub NM (mode_fn M) (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
    (Ξ ++ Θ0) (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) A Θ1 ->
  β `notin` ftvar_in_aenv (Ξ ++ Θ0)
     `union` ftvar_in_pskl (ptyp_to_pskl τ) ->
  exists γ, γ `notin` dom Θ1 /\
    a_sub_flex NM M P0 ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α
      (swap_pskl β γ A) ((β ~ abind_flex_mono_def τ) ++ swap_aenv β γ Θ1).
Proof.
  intros * Hd Hfr.
  assert (Hsub0 : β `notin` ftvar_in_pskl
                    (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  P0 (ptyp_to_pskl τ) β) as Hup.
    clear - Hup Hfr. fsetdec. }
  assert (Hsubs : β `notin` ftvar_in_pskl
                    (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  (pskl_var_f α) (ptyp_to_pskl τ) β) as Hup.
    clear - Hup Hfr. simpl in Hup. fsetdec. }
  assert (HΞΘ : β `notin` ftvar_in_aenv (Ξ ++ Θ0)) by (clear - Hfr; fsetdec).
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv (Ξ ++ Θ0)
                    `union` ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
                    `union` ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                           (pskl_var_f α))).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_sub_flex__assign.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_sub_swap_junk;
      [ exact Hd
      | clear - HΞΘ Hsub0 Hsubs; fsetdec
      | clear - Fr; fsetdec ].
Qed.

Lemma a_assign_skip_no_loss : forall Θ0 Θ1 Ξ α β P,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  α <> β ->
  β `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((β ~ abind_flex_mono) ++ swap_aenv β γ Θ1) }}a.
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_assign__skip.
  - exact Hne.
  - clear - Hfr; fsetdec.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_assign_swap_junk;
      [ exact Hd | clear - Hne; auto | clear - Fr; fsetdec
      | exact Hfr | clear - Fr; fsetdec ].
Qed.

Lemma a_assign_skip_rigid_no_loss : forall Θ0 Θ1 Ξ α β P,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  α <> β ->
  β `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((β ~ abind_tvar) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((β ~ abind_tvar) ++ swap_aenv β γ Θ1) }}a.
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_assign__skip_rigid.
  - clear - Hfr; fsetdec.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_assign_swap_junk;
      [ exact Hd | clear - Hne; auto | clear - Fr; fsetdec
      | exact Hfr | clear - Fr; fsetdec ].
Qed.

Lemma a_assign_skip_tm_var_no_loss : forall Θ0 Θ1 Ξ α x Q P,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  α <> x ->
  x `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((x ~ abind_var_typ Q) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((x ~ abind_var_typ Q) ++ swap_aenv x γ Θ1) }}a.
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_assign__skip_tm_var.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_assign_swap_junk;
      [ exact Hd | clear - Hne; auto | clear - Fr; fsetdec
      | exact Hfr | clear - Fr; fsetdec ].
Qed.

Lemma a_assign_skip_tm_skl_no_loss : forall Θ0 Θ1 Ξ α x Q P,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  α <> x ->
  x `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((x ~ abind_var_skl Q) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((x ~ abind_var_skl Q) ++ swap_aenv x γ Θ1) }}a.
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_assign__skip_tm_skl.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_assign_swap_junk;
      [ exact Hd | clear - Hne; auto | clear - Fr; fsetdec
      | exact Hfr | clear - Fr; fsetdec ].
Qed.

Lemma a_assign_assign_no_loss : forall Θ0 Θ1 Ξ α β τ P Q,
  {{ (Ξ ++ Θ0) ⊢[ empty | empty
       | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) ]
    (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ∼ Q ⊣ Θ1 }}a ->
  a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α ->
  β `notin` ftvar_in_aenv (Ξ ++ Θ0)
     `union` ftvar_in_pskl (ptyp_to_pskl τ) ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((β ~ abind_flex_mono_def τ) ++ swap_aenv β γ Θ1) }}a.
Proof.
  intros * Hd Hfl Hfr.
  assert (Hsub0 : β `notin` ftvar_in_pskl
                    (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  P (ptyp_to_pskl τ) β) as Hup.
    clear - Hup Hfr. fsetdec. }
  assert (Hsubs : β `notin` ftvar_in_pskl
                    (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  (pskl_var_f α) (ptyp_to_pskl τ) β) as Hup.
    clear - Hup Hfr. simpl in Hup. fsetdec. }
  assert (HΞΘ : β `notin` ftvar_in_aenv (Ξ ++ Θ0)) by (clear - Hfr; fsetdec).
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv (Ξ ++ Θ0)
                    `union` ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
                    `union` ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                           (pskl_var_f α))).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_assign__assign with (τ := τ) (Q := swap_pskl β γ Q).
  - exact Hfl.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_consis_swap_junk;
      [ exact Hd | clear; fsetdec | clear; fsetdec
      | clear - HΞΘ Hsub0 Hsubs; fsetdec
      | clear - Fr; fsetdec ].
Qed.

Lemma a_unify_flex_skip_no_loss : forall Θ0 Θ1 α1 α β,
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  α1 <> α -> α1 <> β ->
  α1 `notin` ftvar_in_aenv Θ0 ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((α1 ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
      ⊣ ((α1 ~ abind_flex_mono) ++ swap_aenv α1 γ Θ1) }}a.
Proof.
  intros * Hd Hnα Hnβ Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0
                    `union` singleton α `union` singleton β).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_unify__flex_skip.
  - exact Hnα.
  - exact Hnβ.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_unify_swap_junk;
      [ exact Hd | exact Hnα | clear - Fr; fsetdec | exact Hnβ
      | clear - Fr; fsetdec | exact Hfr | clear - Fr; fsetdec ].
Qed.

Lemma a_unify_skip_other_no_loss : forall Θ0 Θ1 c b α β,
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  (b = abind_tvar \/
   (exists Q, b = abind_var_typ Q) \/
   (exists Q, b = abind_var_skl Q)) ->
  c <> α -> c <> β ->
  c `notin` ftvar_in_aenv Θ0 ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((c ~ b) ++ Θ0) ⊲ α ≈ᵘ β ⊣ ((c ~ b) ++ swap_aenv c γ Θ1) }}a.
Proof.
  intros * Hd Hb Hnα Hnβ Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0
                    `union` singleton α `union` singleton β).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_unify__skip_other.
  - exact Hb.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_unify_swap_junk;
      [ exact Hd | exact Hnα | clear - Fr; fsetdec | exact Hnβ
      | clear - Fr; fsetdec | exact Hfr | clear - Fr; fsetdec ].
Qed.

Lemma a_unify_flex_assign_no_loss : forall Θ0 Θ1 α1 τ α β Q,
  {{ Θ0 ⊢[ empty | empty
       | (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β))) ]
    (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))) ∼ Q ⊣ Θ1 }}a ->
  a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) α ->
  a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β ->
  α1 <> α -> α1 <> β ->
  α1 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_ptyp τ ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((α1 ~ abind_flex_mono_def τ) ++ Θ0) ⊲ α ≈ᵘ β
      ⊣ ((α1 ~ abind_flex_mono_def τ) ++ swap_aenv α1 γ Θ1) }}a.
Proof.
  intros * Hd Hflα Hflβ Hnα Hnβ Hfr.
  assert (Hs : forall x, α1 <> x ->
            α1 `notin` ftvar_in_pskl
              (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f x)))).
  { intros x Hx. rewrite ftvar_ptyp_to_pskl.
    pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                  (ptyp_var_f x) τ α1) as Hup.
    clear - Hup Hx Hfr. simpl in Hup. fsetdec. }
  pose proof (Hs α Hnα) as Hsα. pose proof (Hs β Hnβ) as Hsβ.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0
                    `union` ftvar_in_pskl
                        (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
                    `union` ftvar_in_pskl
                        (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1
                                         (ptyp_var_f α)))).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_unify__flex_assign with (τ := τ) (Q := swap_pskl α1 γ Q).
  - exact Hflα.
  - exact Hflβ.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_consis_swap_junk;
      [ exact Hd | clear; fsetdec | clear; fsetdec
      | clear - Hfr Hsα Hsβ; fsetdec
      | clear - Fr; fsetdec ].
Qed.

Lemma a_tyequiv_swap : forall a b Θ A B,
  {{ Θ ⊢ A ≡ᵗ B }}a ->
  {{ (swap_aenv a b Θ) ⊢ (swap_ptyp a b A) ≡ᵗ (swap_ptyp a b B) }}a.
Proof.
  intros * H; induction H; simpl.
  - apply a_tyequiv__refl. auto using lc_ptyp_swap.
  - apply a_tyequiv__sym; auto.
  - eapply a_tyequiv__trans; eauto.
  - apply a_tyequiv__flex_def.
    exact (swap_aenv_binds a b _ _ _ H).
  - apply a_tyequiv__arrow; auto.
  - apply a_tyequiv__all with (L := swap_atoms a b L).
    intros α0 Hα0.
    assert (hin : swap_atom a b α0 `notin` L)
      by (intro hc; apply Hα0; apply swap_atoms_spec; exact hc).
    specialize (H0 _ hin).
    rewrite !swap_ptyp_open in H0. simpl in H0.
    rewrite swap_atom_invol in H0. exact H0.
Qed.

Definition kswap_msubst (a b : atom) (ζ : metasubst) : metasubst :=
  List.map (fun e => (swap_atom a b (fst e), snd e)) ζ.

Lemma msubst_lookup_kswap_other : forall a b (ζ : metasubst) γ,
  γ <> a -> γ <> b ->
  msubst_lookup (kswap_msubst a b ζ) γ = msubst_lookup ζ γ.
Proof.
  intros a b ζ γ Ha Hb; induction ζ as [| [y τ] ζ']; simpl; [reflexivity |].
  destruct (γ == y) as [e | n0].
  - rewrite <- e. rewrite (swap_atom_other a b γ Ha Hb).
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [_ | n1]
    end; [reflexivity | exfalso; apply n1; reflexivity].
  - match goal with
    | |- (if ?t then _ else _) = _ => destruct t as [e1 | n1]
    end.
    + exfalso. apply n0.
      rewrite <- (swap_atom_invol a b y), <- e1.
      symmetry. apply swap_atom_other; auto.
    + exact IHζ'.
Qed.

Lemma msubst_lookup_kswap_keyed : forall a b (ζ : metasubst),
  a <> b ->
  ~ List.In b (List.map fst ζ) ->
  List.In a (List.map fst ζ) ->
  msubst_lookup (kswap_msubst a b ζ) b = msubst_lookup ζ a.
Proof.
  intros a b ζ Hne; induction ζ as [| [y τ] ζ']; intros Hnb Hin;
    simpl in *.
  - contradiction.
  - destruct (a == y) as [e | n0].
    + rewrite <- e. rewrite swap_atom_l.
      match goal with
      | |- context [if ?t then _ else _] => destruct t as [_ | n1]
      end; [reflexivity | exfalso; apply n1; reflexivity].
    + destruct Hin as [e | Hin']; [exfalso; congruence |].
      assert (hyb : y <> b) by (intro; apply Hnb; left; auto).
      assert (hya : y <> a) by congruence.
      match goal with
      | |- (if ?t then _ else _) = _ => destruct t as [e1 | n1]
      end.
      * exfalso. rewrite (swap_atom_other a b y) in e1 by auto. congruence.
      * apply IHζ'; auto.
Qed.

Lemma msubst_ptyp_kswap : forall a b (ζ : metasubst) A,
  a <> b ->
  ~ List.In b (List.map fst ζ) ->
  b `notin` ftvar_in_ptyp A ->
  (a `notin` ftvar_in_ptyp A \/ List.In a (List.map fst ζ)) ->
  msubst_ptyp (kswap_msubst a b ζ) (swap_ptyp a b A) = msubst_ptyp ζ A.
Proof.
  intros a b ζ A Hne Hnb; induction A; simpl; intros HbA HaA;
    try solve [reflexivity].
  -
    destruct (α == a) as [e | n0].
    + subst α. rewrite swap_atom_l.
      apply msubst_lookup_kswap_keyed; auto.
      destruct HaA as [h | h]; [exfalso; fsetdec | exact h].
    + assert (α <> b) by fsetdec.
      rewrite (swap_atom_other a b α) by auto.
      apply msubst_lookup_kswap_other; auto.
  -
    f_equal; [apply IHA1 | apply IHA2]; try fsetdec;
      destruct HaA as [h | h]; auto; left; fsetdec.
  -
    f_equal. apply IHA; [fsetdec |].
    destruct HaA as [h | h]; [left; fsetdec | right; exact h].
Qed.

Lemma msubst_pskl_kswap : forall a b (ζ : metasubst) P,
  a <> b ->
  ~ List.In b (List.map fst ζ) ->
  b `notin` ftvar_in_pskl P ->
  (a `notin` ftvar_in_pskl P \/ List.In a (List.map fst ζ)) ->
  msubst_pskl (kswap_msubst a b ζ) (swap_pskl a b P) = msubst_pskl ζ P.
Proof.
  intros a b ζ P Hne Hnb; induction P; simpl; intros HbP HaP;
    try solve [reflexivity].
  -
    destruct (α == a) as [e | n0].
    + subst α. rewrite swap_atom_l. f_equal.
      apply msubst_lookup_kswap_keyed; auto.
      destruct HaP as [h | h]; [exfalso; fsetdec | exact h].
    + assert (α <> b) by fsetdec.
      rewrite (swap_atom_other a b α) by auto.
      f_equal. apply msubst_lookup_kswap_other; auto.
  -
    f_equal; [apply IHP1 | apply IHP2]; try fsetdec;
      destruct HaP as [h | h]; auto; left; fsetdec.
  -
    f_equal. apply IHP; [fsetdec |].
    destruct HaP as [h | h]; [left; fsetdec | right; exact h].
  -
    f_equal. apply IHP; [fsetdec |].
    destruct HaP as [h | h]; [left; fsetdec | right; exact h].
Qed.

Lemma a_inc_keys_dom : forall (κ : metasubst) (Θs Θt : aenv) γ,
  κ ∷ Θs ⊑ Θt -> List.In γ (List.map fst κ) -> γ `in` dom Θs.
Proof.
  intros * H; induction H; simpl; intros Hin; try contradiction;
    try solve [ destruct Hin as [e | Hin]; [subst; fsetdec |
                pose proof (IHa_inc Hin); fsetdec ]
              | pose proof (IHa_inc Hin); fsetdec ].
Qed.

Lemma a_inc_flex_in_keys : forall (κ : metasubst) (Θs Θt : aenv) γ,
  κ ∷ Θs ⊑ Θt -> a_flex_tvar Θs γ -> List.In γ (List.map fst κ).
Proof.
  intros * H; induction H; simpl; intros Hf;
    destruct Hf as [Hf | [τ0 Hf]];
    try solve [ inversion Hf ];
    destruct Hf as [Heq | Hf];
    try solve [ inversion Heq; subst; left; reflexivity
              | inversion Heq
              | right; apply IHa_inc; left; assumption
              | right; apply IHa_inc; right; eexists; eassumption
              | apply IHa_inc; left; assumption
              | apply IHa_inc; right; eexists; eassumption ].
Qed.

Lemma a_wf_ptyp_ftv_tvarish : forall (Θ : aenv) A γ,
  a_wf_ptyp Θ A -> γ `in` ftvar_in_ptyp A -> a_binds_tvar γ Θ.
Proof.
  intros * H; induction H; simpl; intros Hγ; try solve [fsetdec].
  -  assert (γ = α) by fsetdec. subst. exact H.
  -
    assert (γ `in` ftvar_in_ptyp A1 \/ γ `in` ftvar_in_ptyp A2) as [h | h]
      by fsetdec; auto.
  -
    destruct (atom_fresh (L `union` singleton γ)) as [α Hα].
    assert (hγ : γ `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A (ptyp_var_f α))).
    { pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A (ptyp_var_f α)).
      fsetdec. }
    assert (hb : a_binds_tvar γ ((α ~ abind_tvar) ++ Θ))
      by (apply H0; auto).
    destruct hb as [hb | [hb | [τ hb]]];
      (destruct hb as [heq | hb];
       [ inversion heq; subst; exfalso; fsetdec
       | unfold a_binds_tvar; auto; right; right; exists τ; exact hb ]).
Qed.
Arguments a_wf_ptyp_ftv_tvarish [Θ A γ] _ _.

Lemma msubst_bskl_kswap_paint : forall a b (ζ : metasubst) P,
  a <> b ->
  ~ List.In b (List.map fst ζ) ->
  b `notin` ftvar_in_pskl P ->
  (a `notin` ftvar_in_pskl P \/ List.In a (List.map fst ζ)) ->
  msubst_bskl (kswap_msubst a b ζ) (pskl_to_bskl_syn (swap_pskl a b P))
  = msubst_bskl ζ (pskl_to_bskl_syn P).
Proof.
  intros a b ζ P Hne Hnb; induction P; simpl; intros HbP HaP;
    try solve [reflexivity].
  -
    destruct (α == a) as [e | n0].
    + subst α. rewrite swap_atom_l. f_equal. f_equal.
      apply msubst_lookup_kswap_keyed; auto.
      destruct HaP as [h | h]; [exfalso; fsetdec | exact h].
    + assert (α <> b) by fsetdec.
      rewrite (swap_atom_other a b α) by auto.
      f_equal. f_equal. apply msubst_lookup_kswap_other; auto.
  -
    f_equal; [apply IHP1 | apply IHP2]; try fsetdec;
      destruct HaP as [h | h]; auto; left; fsetdec.
  -
    f_equal. apply IHP; [fsetdec |].
    destruct HaP as [h | h]; [left; fsetdec | right; exact h].
  -
    f_equal. apply IHP; [fsetdec |].
    destruct HaP as [h | h]; [left; fsetdec | right; exact h].
Qed.

Lemma msubst_bskl_head_notin : forall β τβ (ζ : metasubst) Q,
  β `notin` ftvar_in_bskl Q ->
  msubst_bskl ((β, τβ) :: ζ) Q = msubst_bskl ζ Q.
Proof.
  intros β τβ ζ Q; induction Q; simpl; intros Hn; f_equal;
    try solve [reflexivity | apply IHQ; fsetdec
              | apply IHQ1; fsetdec | apply IHQ2; fsetdec].

  match goal with
  | |- context [if ?t then _ else _] => destruct t as [e | ?]
  end; [exfalso; fsetdec | reflexivity].
Qed.

Lemma msubst_compose_kswap_id : forall a b (ζ κ1 : metasubst),
  is_id_msubst κ1 ->
  (forall α, List.In α (List.map fst κ1) -> α <> a /\ α <> b) ->
  msubst_compose (kswap_msubst a b ζ) κ1 = msubst_compose ζ κ1.
Proof.
  intros a b ζ κ1; induction κ1 as [| [α τ] κ1']; intros Hid Hk;
    [reflexivity |].
  inversion Hid as [| e κl he hl]; subst.
  unfold is_id_entry in he; simpl in he. subst τ.
  unfold msubst_compose; simpl.
  destruct (Hk α (or_introl eq_refl)) as [ha hb].
  f_equal.
  - f_equal. apply msubst_lookup_kswap_other; auto.
  - apply IHκ1'; auto.
    intros α0 h0. apply Hk. right. exact h0.
Qed.

Local Lemma dom_ftvar_aenv : forall Θ : aenv, dom Θ [<=] ftvar_in_aenv Θ.
Proof. induction Θ as [| [x bd] Θ']; simpl; fsetdec. Qed.

Lemma a_inc_kswap : forall a b (ζ : metasubst) (Θ1 Θ : aenv),
  ζ ∷ Θ1 ⊑ Θ ->
  a <> b ->
  {{ ⊢ Θ1 }}a ->
  b `notin` ftvar_in_aenv Θ1 ->
  (forall bd, binds a bd Θ1 ->
     bd = abind_flex_mono \/ exists τ, bd = abind_flex_mono_def τ) ->
  (kswap_msubst a b ζ) ∷ (swap_aenv a b Θ1) ⊑ Θ.
Proof.
  intros a b ζ Θ1 Θ Hinc; induction Hinc; intros Hne Hwf Hb Ha; simpl.
  -  apply a_inc__empty; auto.
  -
    apply a_inc__flex; auto.
    apply IHHinc;
      [ exact Hne
      | inversion Hwf; auto
      | simpl in Hb; fsetdec
      | intros bd hbd; apply Ha; right; exact hbd ].
  -
    inversion Hwf; subst.
    assert (hkeys : ~ List.In b (List.map fst κ)).
    { intro hc. pose proof (a_inc_keys_dom _ _ _ _ Hinc hc) as hd.
      simpl in Hb. pose proof (dom_ftvar_aenv Θ). fsetdec. }
    apply a_inc__flex_def; auto.
    + apply IHHinc;
        [ exact Hne
        | assumption
        | simpl in Hb; fsetdec
        | intros bd hbd; apply Ha; right; exact hbd ].
    + rewrite msubst_ptyp_kswap; auto.
      * simpl in Hb. fsetdec.
      * destruct (AtomSetProperties.In_dec a (ftvar_in_ptyp τ)) as [hin | hout];
          [right | left; exact hout].
        match goal with
        | h : a_wf_ptyp _ τ |- _ =>
            pose proof (a_wf_ptyp_ftv_tvarish h hin) as hbt
        end.
        destruct hbt as [hbt | [hbt | [τ0 hbt]]].
        -- exfalso.
           destruct (Ha abind_tvar) as [hc | [τ1 hc]];
             [right; exact hbt | discriminate | discriminate].
        -- eapply a_inc_flex_in_keys; eauto. left; exact hbt.
        -- eapply a_inc_flex_in_keys; eauto. right; eexists; exact hbt.
  -
    inversion Hwf; subst.
    assert (hxa : x <> a).
    { intro; subst x.
      destruct (Ha (abind_var_typ A)) as [hc | [τ1 hc]];
        [left; reflexivity | discriminate | discriminate]. }
    assert (hxb : x <> b) by (simpl in Hb; fsetdec).
    assert (hkeys : ~ List.In b (List.map fst κ)).
    { intro hc. pose proof (a_inc_keys_dom _ _ _ _ Hinc hc) as hd.
      simpl in Hb. pose proof (dom_ftvar_aenv Θ). fsetdec. }
    rewrite (swap_atom_other a b x) by auto.
    apply a_inc__var; auto.
    + apply IHHinc;
        [ exact Hne
        | assumption
        | simpl in Hb; fsetdec
        | intros bd hbd; apply Ha; right; exact hbd ].
    + rewrite msubst_ptyp_kswap; auto.
      * simpl in Hb. fsetdec.
      * destruct (AtomSetProperties.In_dec a (ftvar_in_ptyp A)) as [hin | hout];
          [right | left; exact hout].
        match goal with
        | h : a_wf_ptyp _ A |- _ =>
            pose proof (a_wf_ptyp_ftv_tvarish h hin) as hbt
        end.
        destruct hbt as [hbt | [hbt | [τ0 hbt]]].
        -- exfalso.
           destruct (Ha abind_tvar) as [hc | [τ1 hc]];
             [right; exact hbt | discriminate | discriminate].
        -- eapply a_inc_flex_in_keys; eauto. left; exact hbt.
        -- eapply a_inc_flex_in_keys; eauto. right; eexists; exact hbt.
  -
    inversion Hwf; subst.
    assert (hxa : x <> a).
    { intro; subst x.
      destruct (Ha (abind_var_skl P)) as [hc | [τ1 hc]];
        [left; reflexivity | discriminate | discriminate]. }
    assert (hxb : x <> b) by (simpl in Hb; fsetdec).
    assert (hkeys : ~ List.In b (List.map fst κ)).
    { intro hc. pose proof (a_inc_keys_dom _ _ _ _ Hinc hc) as hd.
      simpl in Hb. pose proof (dom_ftvar_aenv Θ). fsetdec. }
    rewrite (swap_atom_other a b x) by auto.
    apply a_inc__var_skl; auto.
    + apply IHHinc;
        [ exact Hne
        | assumption
        | simpl in Hb; fsetdec
        | intros bd hbd; apply Ha; right; exact hbd ].
    + rewrite msubst_pskl_kswap; auto.
      * simpl in Hb. fsetdec.
      * destruct (AtomSetProperties.In_dec a (ftvar_in_pskl P)) as [hin | hout];
          [right | left; exact hout].
        match goal with
        | h : {{ _ ⨟ empty ⊢ₚₛ P }}a |- _ =>
            pose proof (a_wf_pskl_ftv_binds h hin)
              as hbt
        end.
        destruct hbt as [hbt | [hbt | [τ0 hbt]]].
        -- exfalso.
           destruct (Ha abind_tvar) as [hc | [τ1 hc]];
             [right; exact hbt | discriminate | discriminate].
        -- eapply a_inc_flex_in_keys; eauto. left; exact hbt.
        -- eapply a_inc_flex_in_keys; eauto. right; eexists; exact hbt.
  -
    inversion Hwf; subst.
    assert (hxa : α <> a).
    { intro; subst α.
      destruct (Ha abind_tvar) as [hc | [τ1 hc]];
        [left; reflexivity | discriminate | discriminate]. }
    assert (hxb : α <> b) by (simpl in Hb; fsetdec).
    rewrite (swap_atom_other a b α) by auto.
    apply a_inc__tvar; auto.
    apply IHHinc;
      [ exact Hne
      | assumption
      | simpl in Hb; fsetdec
      | intros bd hbd; apply Ha; right; exact hbd ].
Qed.

Lemma swap_aenv_fresh_eq : forall x y Θ,
  x `notin` (dom Θ `union` ftvar_in_aenv Θ) ->
  y `notin` (dom Θ `union` ftvar_in_aenv Θ) ->
  swap_aenv x y Θ = Θ.
Proof. intros; apply swap_aenv_fresh_id; fsetdec. Qed.

Set Implicit Arguments.

Fixpoint swap_exp (a b : atom) (e : exp) : exp :=
  match e with
  | exp_unit          => exp_unit
  | exp_var_b n       => exp_var_b n
  | exp_var_f x       => exp_var_f (swap_atom a b x)
  | exp_abs e1        => exp_abs (swap_exp a b e1)
  | exp_abs_anno A e1 => exp_abs_anno (swap_ptyp a b A) (swap_exp a b e1)
  | exp_app e1 e2     => exp_app (swap_exp a b e1) (swap_exp a b e2)
  | exp_anno e1 A     => exp_anno (swap_exp a b e1) (swap_ptyp a b A)
  | exp_freeze e1     => exp_freeze (swap_exp a b e1)
  end.

Lemma swap_exp_open_rec : forall a b e u k,
  swap_exp a b (open_exp_wrt_exp_rec k u e)
  = open_exp_wrt_exp_rec k (swap_exp a b u) (swap_exp a b e).
Proof.
  intros a b e; induction e; intros u k; simpl; f_equal; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma swap_exp_open_var : forall a b e x,
  swap_exp a b (open_exp_wrt_exp e (exp_var_f x))
  = open_exp_wrt_exp (swap_exp a b e) (exp_var_f (swap_atom a b x)).
Proof. intros. apply swap_exp_open_rec. Qed.

Lemma swap_exp_fresh_id : forall a b e,
  a `notin` fvar_in_exp e `union` ftvar_in_exp e ->
  b `notin` fvar_in_exp e `union` ftvar_in_exp e ->
  swap_exp a b e = e.
Proof.
  intros a b e; induction e; simpl; intros Ha Hb; f_equal;
    solve [ reflexivity
          | apply IHe; clear - Ha Hb; fsetdec
          | apply IHe1; clear - Ha Hb; fsetdec
          | apply IHe2; clear - Ha Hb; fsetdec
          | apply swap_ptyp_fresh_id; clear - Ha Hb; fsetdec
          | apply swap_atom_other; clear - Ha Hb; fsetdec ].
Qed.

Lemma swap_block_ftv_filter : forall a b (Ξ : aenv) A,
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
  forall γ, γ `in` dom (swap_aenv a b Ξ) ->
            γ `notin` ftvar_in_ptyp (swap_ptyp a b A).
Proof.
  intros a b Ξ A Hf γ Hγ.
  pose proof (swap_ptyp_ftv_notin a b A (swap_atom a b γ)
                (Hf _ (swap_aenv_dom_in_rev a b Ξ γ Hγ))) as h.
  rewrite swap_atom_invol in h. exact h.
Qed.

Unset Implicit Arguments.

Lemma swap_atom_same : forall a x, swap_atom a a x = x.
Proof. intros a x; unfold swap_atom; destruct (x == a); subst; reflexivity. Qed.

Lemma swap_atoms_same : forall a S, swap_atoms a a S [=] S.
Proof. intros a S x; rewrite swap_atoms_spec, swap_atom_same; reflexivity. Qed.

Lemma swap_ptyp_same : forall a A, swap_ptyp a a A = A.
Proof. intros a A; induction A; simpl; f_equal; auto using swap_atom_same. Qed.

Lemma swap_pskl_same : forall a P, swap_pskl a a P = P.
Proof. intros a P; induction P; simpl; f_equal; auto using swap_atom_same. Qed.

Lemma swap_abind_same : forall a bd, swap_abind a a bd = bd.
Proof. intros a bd; destruct bd; simpl; f_equal; auto using swap_ptyp_same, swap_pskl_same. Qed.

Lemma swap_aenv_same : forall a Θ, swap_aenv a a Θ = Θ.
Proof.
  intros a Θ; induction Θ as [|[x bd] Θ IH]; [reflexivity |].
  rewrite swap_aenv_cons, swap_atom_same, swap_abind_same, IH. reflexivity.
Qed.

Lemma swap_cstrs_same : forall a C, swap_cstrs a a C = C.
Proof.
  intros a C; induction C as [|c C IH]; [reflexivity |].
  rewrite swap_cstrs_cons, IH. destruct c; simpl; rewrite swap_pskl_same; reflexivity.
Qed.

Lemma swap_exp_same : forall a e, swap_exp a a e = e.
Proof.
  intros a e; induction e; simpl; f_equal;
    auto using swap_atom_same, swap_ptyp_same.
Qed.
