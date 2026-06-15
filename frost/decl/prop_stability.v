(** Frost — structural declarative-typing properties (order irrelevance,
    stability). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_general_subsumption.

Set Implicit Arguments.

(** * Well-formedness consequences used by variable head-factoring.

    The [d_wf_denv] context invariant carries [x ∉ dom Γ] at every
    extension and [d_wf_ptyp Γ A] at every term binding, so it yields
    both [uniq Γ] (needed to identify a variable's binding under the
    [d_typing__var] inversion) and the binding's well-formedness
    (needed by the consistency-transitivity steps). *)
Lemma d_wf_denv_uniq : forall Γ, d_wf_denv Γ -> uniq Γ.
Proof. intros Γ H; induction H; auto. Qed.

(** A term binding's type is well-formed in the full context (the
    invariant records it over the tail; weaken back up). *)
Lemma d_wf_denv_binds_ptyp : forall Γ x A,
    d_wf_denv Γ ->
    binds x (dbind_typ A) Γ ->
    d_wf_ptyp Γ A.
Proof.
  intros Γ x A Hwf. induction Hwf; intros Hb.
  - inversion Hb.
  - analyze_binds Hb.
    rewrite_env (nil ++ (X ~ dbind_tvar) ++ Γ).
    apply d_wf_ptyp_weakening. simpl. apply IHHwf; assumption.
  - analyze_binds Hb.
    + assert (A = A0) by congruence. subst A0.
      rewrite_env (nil ++ (x0 ~ dbind_typ A) ++ Γ).
      apply d_wf_ptyp_weakening. simpl. exact H0.
    + rewrite_env (nil ++ (x0 ~ dbind_typ A0) ++ Γ).
      apply d_wf_ptyp_weakening. simpl. apply IHHwf; assumption.
  - analyze_binds Hb.
    rewrite_env (nil ++ (x0 ~ dbind_skl P) ++ Γ).
    apply d_wf_ptyp_weakening. simpl. apply IHHwf; assumption.
Qed.

(** Consistency is reflexive on the synthesised painting: a
    well-formed [A] synthesises a [btyp] consistent with the
    [utyp] painting of the same [A] (empty tag context). *)
Lemma d_consis_syn_refl : forall Γ A,
    d_wf_ptyp Γ A ->
    empty ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ ptyp_to_btyp_syn A.
Proof.
  intros Γ A Hwf. induction Hwf; simpl.
  - apply d_consis__unit; reflexivity.
  - apply d_consis__var; [ exact H | reflexivity ].
  - apply d_consis__arrow with (Δ1 := empty) (Δ2 := empty);
      [ exact IHHwf1 | exact IHHwf2 | fsetdec ].
  - apply d_consis__forall_syn with (L := L). intros X HX.
    specialize (H0 X HX).
    rewrite ptyp_to_utyp_syn_open in H0.
    rewrite ptyp_to_btyp_syn_open in H0.
    simpl in H0. exact H0.
Qed.

(** Structural converse of [d_consis_syn_refl]: a synthesised painting is
    consistent ONLY with its own [btyp] synthesis.  Holds because the
    target is forced [is_styp] (synthesised) — that excludes the
    [d_consis__forall_inh_*] rules (whose RHS is inherited) and the tagged
    rules (whose LHS is [utyp_all_etag], never produced by a painting), so
    consistency collapses to structural congruence.  This is what makes a
    variable's [mode_ti] type EXACTLY its binding painting, hence the
    extracted [d_sub] lands at the empty tag context demanded by
    [d_typing__sub]. *)
Lemma d_consis_paint_syn_eq : forall B,
    is_styp B ->
    forall Δ Γ A, Δ ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B -> B = ptyp_to_btyp_syn A.
Proof.
  intros B Hstyp. induction Hstyp; intros Δ Γ A Hc.
  - (* unit *) destruct A; simpl in Hc; inversion Hc; subst; reflexivity.
  - (* var *) destruct A; simpl in Hc; inversion Hc; subst; reflexivity.
  - (* arrow *)
    destruct A; simpl in Hc; inversion Hc; subst.
    simpl. f_equal; [ eapply IHHstyp1 | eapply IHHstyp2 ]; eassumption.
  - (* all_syn *)
    destruct A; simpl in Hc; inversion Hc; subst.
    simpl. f_equal.
    pick fresh X for (L `union` L0 `union` ftvar_in_btyp B `union` ftvar_in_ptyp A).
    specialize (H5 X ltac:(auto)).
    replace (utyp_var_f X) with (ptyp_to_utyp_syn (ptyp_var_f X)) in H5 by reflexivity.
    rewrite <- ptyp_to_utyp_syn_open in H5.
    specialize (H0 X ltac:(auto) Δ ((X ~ dbind_tvar) ++ Γ)
                  (open_ptyp_wrt_ptyp A (ptyp_var_f X)) H5).
    rewrite ptyp_to_btyp_syn_open in H0. simpl in H0.
    apply open_btyp_wrt_btyp_inj with (Xbt1 := X).
    + fsetdec.
    + pose proof (ftvar_ptyp_to_btyp_syn A). fsetdec.
    + exact H0.
Qed.

(** Well-formed plain types are locally closed. *)
Lemma d_wf_ptyp_lc : forall Γ A, d_wf_ptyp Γ A -> lc_ptyp A.
Proof.
  intros Γ A H. induction H.
  - apply lc_ptyp_unit.
  - apply lc_ptyp_var_f.
  - apply lc_ptyp_arrow; assumption.
  - pick fresh X. apply (lc_ptyp_all_exists X). auto.
Qed.

(** A [mode_ti] typing of a variable [x : A] synthesises a synthesised
    type [B1] that is consistent with the painting of [x]'s binding.
    [is_styp B1] holds because [__var] paints a [ptyp] and [__sub] at
    [mode_ti] (only [d_sub__infer]) records [is_styp] directly.  The tag
    context of the consistency may grow under composition, so it is
    existential. *)
Lemma d_typing_var_ti_consis : forall Γ x A B1,
    d_wf_denv Γ ->
    binds x (dbind_typ A) Γ ->
    Γ ⊢[ mode_ti ] (exp_var_f x) ⦂ B1 ->
    is_styp B1 /\ exists Δt, Δt ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B1.
Proof.
  intros Γ x A B1 Hwf Hb Htyp.
  assert (Huniq : uniq Γ) by (apply d_wf_denv_uniq; exact Hwf).
  remember (exp_var_f x) as e. remember mode_ti as m.
  induction Htyp; subst; try discriminate.
  - (* __var: B1 = ptyp_to_btyp_syn A0, binds x A0; uniq pins A0 = A. *)
    inversion Heqe; subst x0.
    assert (A0 = A) by
      (assert (dbind_typ A0 = dbind_typ A) by (eapply binds_unique; eauto);
       congruence). subst A0.
    assert (Hwfa : d_wf_ptyp Γ A) by (eapply d_wf_denv_binds_ptyp; eauto).
    split.
    + apply is_styp_ptyp_to_btyp_syn; eapply d_wf_ptyp_lc; eauto.
    + exists empty. apply d_consis_syn_refl; exact Hwfa.
  - (* __sub at mode_ti: only d_sub__infer; compose the inner consistency. *)
    match goal with H : empty ⨟ _ ⊢[ mode_ti ] _ ⊑ B2 |- _ =>
      rename H into Hsub end.
    inversion Hsub as [ Δ0 Γ0 C0 B0 Hcons0 Hstyp0 HΔ0 | | | | | ]; subst;
      try congruence.
    edestruct IHHtyp as [Hstyp1 [Δt Hcons1]]; auto.
    split; [ exact Hstyp0 | ].
    (* Hcons1 : Δt ⊨ ptyp_to_utyp_syn A ≈ B1   (B1 the inner type)
       Hcons0 : empty ⊨ btyp_to_utyp_syn B1 ≈ B2  (coerced from ptyp_to_utyp_syn) *)
    rewrite ptyp_to_utyp_syn_btyp_to_ptyp in Hcons0.
    assert (HB1 : B1 = ptyp_to_btyp_syn (btyp_to_ptyp B1)) by
      (symmetry; apply ptyp_to_btyp_syn_btyp_to_ptyp; apply is_styp_is_syn; exact Hstyp1).
    rewrite HB1 in Hcons1.
    edestruct d_consis_compose as [Δc [_ Hc]].
    + exact Hcons1.
    + rewrite ptyp_to_utyp_syn_btyp_to_ptyp. exact Hcons0.
    + exists Δc. exact Hc.
Qed.

(** Variable head-factoring: typing [x] at a function mode reduces to a
    subtyping out of [x]'s (painted) binding into the demanded type.
    Only [d_typing__sub] can fire at [mode_fn _] (the [__var] / [__forall]
    rules require [mode_ti] / [mode_tc]); the inner [mode_ti] typing is
    absorbed by consistency transitivity. *)
Lemma d_typing_var_fn_factor : forall Γ x A B m,
    d_wf_denv Γ ->
    binds x (dbind_typ A) Γ ->
    Γ ⊢[ mode_fn m ] (exp_var_f x) ⦂ B ->
    exists Δ, Δ ⨟ Γ ⊢[ mode_fn m ] ptyp_to_utyp_syn A ⊑ B.
Proof.
  intros Γ x A B m Hwf Hb Htyp.
  remember (exp_var_f x) as e. remember (mode_fn m) as mf.
  induction Htyp; subst; try discriminate; try congruence.
  - (* __sub: inner [Γ ⊢[ti] x ⦂ B1] (= Htyp), outer
       [empty ⊢[fn m] paint B1 ⊑ B2] (= H0). *)
    destruct (@d_typing_var_ti_consis Γ x A B1 Hwf Hb Htyp)
      as [Hstyp1 [Δt Hcons1]].
    rewrite ptyp_to_utyp_syn_btyp_to_ptyp in H0.
    edestruct (@d_consis_sub_trans (mode_fn m) empty Γ (btyp_to_utyp_syn B1) B2
                 H0 B1 (ptyp_to_utyp_syn A) Δt) as [Δ [_ Hgoal]].
    + reflexivity.
    + apply is_styp_is_syn; exact Hstyp1.
    + exact Hcons1.
    + exists Δ. exact Hgoal.
Qed.

(** A curried function type [A1 → … → An → R] built from a list of
    (argument-type, argument-term) pairs (a spine). *)
Definition curry_ptyp (args : list (ptyp * exp)) (R : ptyp) : ptyp :=
  fold_right (fun ae acc => ptyp_arrow (fst ae) acc) R args.

(** The curried application [f e1 … en]. *)
Definition curry_exp (f : exp) (args : list (ptyp * exp)) : exp :=
  fold_left (fun g ae => exp_app g (snd ae)) args f.

(** A prefix of [n] universal quantifiers [∀…∀. A]. *)
Fixpoint ptyp_forall_prefix (n : nat) (A : ptyp) : ptyp :=
  match n with
  | O => A
  | S n' => ptyp_all (ptyp_forall_prefix n' A)
  end.

(** A curried [btyp] arrow [Barg1 → … → Bargk → B] from the head's
    arrow-argument [btyp]s. *)
Definition curry_btyp (Bargs : list btyp) (B : btyp) : btyp :=
  fold_right btyp_arrow B Bargs.

(** The [k]-fold function mode [mode_fn (… (mode_fn m))]. *)
Fixpoint mode_fn_n (k : nat) (m : mode) : mode :=
  match k with
  | O => m
  | S k' => mode_fn (mode_fn_n k' m)
  end.

Lemma mode_fn_n_fn : forall k m, mode_fn_n k (mode_fn m) = mode_fn (mode_fn_n k m).
Proof. induction k; intros m; simpl; [ reflexivity | rewrite IHk; reflexivity ]. Qed.

Lemma curry_exp_snoc : forall f args a,
    curry_exp f (args ++ a :: nil) = exp_app (curry_exp f args) (snd a).
Proof. intros. unfold curry_exp. rewrite fold_left_app. reflexivity. Qed.

Lemma curry_btyp_snoc : forall Bargs Barg B,
    curry_btyp (Bargs ++ Barg :: nil) B = curry_btyp Bargs (btyp_arrow Barg B).
Proof. intros. unfold curry_btyp. rewrite fold_right_app. reflexivity. Qed.

(** The per-argument premises of [d_typing__app], packaged so as to be
    independent of the argument's position in the spine: an argument [e]
    fits an arrow-argument [btyp] [Barg] iff it pattern-synthesises a
    skeleton that refines [Barg]'s erasure and checks against [Barg]'s
    inherited painting.  ([A = btyp_to_ptyp Barg] is folded in.) *)
Definition arg_ok (Γ : list (atom * dbind)) (Barg : btyp) (e : exp) : Prop :=
  exists P,
    (Γ ⊢[ mode_tc ] e ⇨ (pskl_to_bskl_syn P)) /\
    (nil ⨟ Γ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl (btyp_to_ptyp Barg)))) /\
    (Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh (btyp_to_ptyp Barg))).

(** A single application step from a head arrow type plus argument
    evidence (the [d_typing__app] introduction, repackaged). *)
Lemma d_typing_app_step : forall Γ m e1 e2 Barg B,
    Γ ⊢[ mode_fn m ] e1 ⦂ (btyp_arrow Barg B) ->
    arg_ok Γ Barg e2 ->
    Γ ⊢[ m ] (exp_app e1 e2) ⦂ B.
Proof.
  intros Γ m e1 e2 Barg B Hhead [P [Hpat [Href Hchk]]].
  eapply d_typing__app with (P := P) (A := btyp_to_ptyp Barg) (Barg := Barg);
    [ reflexivity | exact Hpat | exact Href | exact Hhead | exact Hchk ].
Qed.

(** Head-generic spine INVERSION: a curried application factors into a
    head typed at the [k]-fold function mode against the curried arrow,
    plus per-argument evidence.  Works for an arbitrary head [f] because
    [exp_app _ _] is neither [is_base_term] nor [is_value], so only
    [d_typing__app] can fire. *)
Lemma d_typing_app_spine_inv : forall args Γ f m R',
    Γ ⊢[ m ] curry_exp f args ⦂ R' ->
    exists Bargs,
      length Bargs = length args /\
      (Γ ⊢[ mode_fn_n (length args) m ] f ⦂ curry_btyp Bargs R') /\
      Forall2 (arg_ok Γ) Bargs (List.map snd args).
Proof.
  intro args. induction args as [ | a init IHinit ] using rev_ind;
    intros Γ f m R' Htyp.
  - (* empty spine: [curry_exp f [] = f] *)
    exists nil. simpl. repeat split; [ exact Htyp | constructor ].
  - (* snoc: [exp_app (curry_exp f init) (snd a)] *)
    rewrite curry_exp_snoc in Htyp.
    inversion Htyp; subst;
      try (exfalso;
           match goal with
           | Hv : is_value (exp_app _ _) |- _ => inversion Hv
           | Hb : is_base_term (exp_app _ _) |- _ => inversion Hb
           end).
    (* surviving [__app] case: head [H6], arg evidence [P], [Barg]. *)
    edestruct (IHinit Γ f (mode_fn m) (btyp_arrow Barg R')) as [Bi [Hlen [Hhd Hfa]]];
      [ eassumption | ].
    exists (Bi ++ Barg :: nil). repeat split.
    + rewrite !app_length. simpl. rewrite Hlen. reflexivity.
    + rewrite curry_btyp_snoc.
      rewrite mode_fn_n_fn in Hhd.
      rewrite app_length, Nat.add_1_r. simpl. exact Hhd.
    + rewrite List.map_app. simpl. apply Forall2_app; [ exact Hfa | ].
      constructor; [ | constructor ].
      eexists; repeat split; eassumption.
Qed.

(** Head-generic spine REASSEMBLY (the converse). *)
Lemma d_typing_app_spine_build : forall args Γ f m R' Bargs,
    length Bargs = length args ->
    Γ ⊢[ mode_fn_n (length args) m ] f ⦂ curry_btyp Bargs R' ->
    Forall2 (arg_ok Γ) Bargs (List.map snd args) ->
    Γ ⊢[ m ] curry_exp f args ⦂ R'.
Proof.
  intro args. induction args as [ | a init IHinit ] using rev_ind;
    intros Γ f m R' Bargs Hlen Hhead Hall.
  - (* [] *) destruct Bargs; [ simpl in Hhead; exact Hhead | inversion Hlen ].
  - (* snoc *)
    rewrite curry_exp_snoc.
    rewrite List.map_app in Hall. simpl in Hall.
    apply Forall2_app_inv_r in Hall as [Bi [Blast [Hfa [Hlast HBeq]]]].
    inversion Hlast as [ | Barg e0 Btl etl Haok Htail HBl Hel ]; subst.
    inversion Htail; subst.
    apply d_typing_app_step with (Barg := Barg); [ | exact Haok ].
    apply (IHinit Γ f (mode_fn m) (btyp_arrow Barg R') Bi).
    + apply Forall2_length in Hfa. rewrite List.map_length in Hfa. exact Hfa.
    + rewrite curry_btyp_snoc in Hhead.
      rewrite app_length, Nat.add_1_r in Hhead. simpl in Hhead.
      rewrite <- mode_fn_n_fn in Hhead. exact Hhead.
    + exact Hfa.
Qed.

(** * The subsumption-permutation engine.

    A "spine" pairs each binding argument type [A : ptyp] (whose
    synthesised painting is the subtyping LHS) with the head's
    arrow-argument [Barg : btyp] (the RHS).  [spine_utyp] / [spine_btyp]
    assemble the two curried arrows over a shared tail. *)
Definition spine_utyp (Rt : utyp) (sp : list (utyp * btyp)) : utyp :=
  fold_right (fun p acc => utyp_arrow (fst p) acc) Rt sp.
Definition spine_btyp (Rb : btyp) (sp : list (utyp * btyp)) : btyp :=
  fold_right (fun p acc => btyp_arrow (snd p) acc) Rb sp.

(** ENGINE (no [∀]-prefix): a curried-arrow subtyping is stable under
    permutation of its argument spine.  The crux is the [perm_swap] case:
    two adjacent [d_sub__arg] steps contribute argument consistencies with
    tag sets [Δp], [Δq] and a result with [Δr]; swapping them only reorders
    the set union [Δp ∪ (Δq ∪ Δr)] ⟶ [Δq ∪ (Δp ∪ Δr)], equal as SETS —
    which is exactly why the [Δ]-as-[atoms] refactor makes order
    irrelevance clean (the old [list]-disjoint-append encoding could not
    commute the two without reproving disjointness). *)
Lemma d_sub_arrow_spine_perm : forall sp sp',
    Permutation sp sp' ->
    forall Δ Γ Rt Rb m,
      Δ ⨟ Γ ⊢[ mode_fn_n (length sp) m ] spine_utyp Rt sp ⊑ spine_btyp Rb sp ->
      Δ ⨟ Γ ⊢[ mode_fn_n (length sp') m ] spine_utyp Rt sp' ⊑ spine_btyp Rb sp'.
Proof.
  intros sp sp' Hperm. induction Hperm; intros Δ Γ Rt Rb m Hsub.
  - (* nil *) exact Hsub.
  - (* skip x : sp = x::l, sp' = x::l' *)
    simpl in Hsub |- *.
    inversion Hsub as [ | | | Δ0 Δ1 Δ2 Γ0 m0 C1 C2 B1 B2 Hcons Hrest HΔ | | ]; subst.
    apply d_sub__arg with (Δ1 := Δ1) (Δ2 := Δ2);
      [ exact Hcons | apply IHHperm; exact Hrest | exact HΔ ].
  - (* swap x y : sp = y::x::l, sp' = x::y::l *)
    simpl in Hsub |- *.
    inversion Hsub as [ | | | Δ0 Δy Δyr Γ0 m0 Cy C2 By B2 Hcy Hyr HΔyr | | ]; subst.
    inversion Hyr as [ | | | Δ0' Δx Δl Γ0' m0' Cx C2' Bx B2' Hcx Hl HΔl | | ]; subst.
    apply d_sub__arg with (Δ1 := Δx) (Δ2 := (Δy `union` Δl));
      [ exact Hcx
      | apply d_sub__arg with (Δ1 := Δy) (Δ2 := Δl);
          [ exact Hcy | exact Hl | reflexivity ]
      | fsetdec ].
  - (* trans *)
    apply IHHperm2. apply IHHperm1. exact Hsub.
Qed.

(** ** Support for stripping the [∀]-prefix and bridging the [paint]/[curry]
    forms to the [spine] forms used by the engine. *)

Lemma spine_utyp_cons : forall Rt p sp,
    spine_utyp Rt (p :: sp) = utyp_arrow (fst p) (spine_utyp Rt sp).
Proof. reflexivity. Qed.

Lemma spine_btyp_cons : forall Rb p sp,
    spine_btyp Rb (p :: sp) = btyp_arrow (snd p) (spine_btyp Rb sp).
Proof. reflexivity. Qed.

Lemma curry_ptyp_cons : forall a args R,
    curry_ptyp (a :: args) R = ptyp_arrow (fst a) (curry_ptyp args R).
Proof. reflexivity. Qed.

Lemma curry_btyp_cons : forall b Bargs R',
    curry_btyp (b :: Bargs) R' = btyp_arrow b (curry_btyp Bargs R').
Proof. reflexivity. Qed.

Fixpoint utyp_all_syn_n (j : nat) (C : utyp) : utyp :=
  match j with O => C | S j' => utyp_all_syn (utyp_all_syn_n j' C) end.

Lemma paint_forall_prefix : forall n X,
    ptyp_to_utyp_syn (ptyp_forall_prefix n X) = utyp_all_syn_n n (ptyp_to_utyp_syn X).
Proof. induction n; intros X; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

Lemma map_fst_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> List.map fst (combine l1 l2) = l1.
Proof.
  induction l1 as [ | a l1 IH ]; destruct l2 as [ | b l2 ]; simpl; intros H;
    try reflexivity; try discriminate.
  rewrite IH; [ reflexivity | congruence ].
Qed.

Lemma map_snd_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> List.map snd (combine l1 l2) = l2.
Proof.
  induction l1 as [ | a l1 IH ]; destruct l2 as [ | b l2 ]; simpl; intros H;
    try reflexivity; try discriminate.
  rewrite IH; [ reflexivity | congruence ].
Qed.

Lemma paint_curry_spine : forall args Bargs R,
    length args = length Bargs ->
    ptyp_to_utyp_syn (curry_ptyp args R)
    = spine_utyp (ptyp_to_utyp_syn R)
        (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args) Bargs).
Proof.
  induction args as [ | a args IH ]; destruct Bargs as [ | b Bargs ]; intros R Hlen;
    try discriminate; [ reflexivity | ].
  cbn [List.map combine] in *. rewrite spine_utyp_cons, curry_ptyp_cons.
  cbn [fst snd ptyp_to_utyp_syn]. f_equal. apply IH. cbn [length] in Hlen. congruence.
Qed.

Lemma spine_btyp_curry : forall (args : list (ptyp * exp)) Bargs R',
    length args = length Bargs ->
    spine_btyp R' (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args) Bargs)
    = curry_btyp Bargs R'.
Proof.
  induction args as [ | a args IH ]; destruct Bargs as [ | b Bargs ]; intros R' Hlen;
    try discriminate; [ reflexivity | ].
  cbn [List.map combine] in *. rewrite spine_btyp_cons, curry_btyp_cons.
  cbn [fst snd]. f_equal. apply IH. cbn [length] in Hlen. congruence.
Qed.

Lemma open_spine_utyp_rec : forall sp k ph Rt,
    open_utyp_wrt_utyp_rec k ph (spine_utyp Rt sp)
    = spine_utyp (open_utyp_wrt_utyp_rec k ph Rt)
        (List.map (fun p => (open_utyp_wrt_utyp_rec k ph (fst p), snd p)) sp).
Proof.
  induction sp as [ | p sp IH ]; intros k ph Rt; [ reflexivity | ].
  rewrite spine_utyp_cons. cbn [List.map]. rewrite spine_utyp_cons.
  cbn [fst snd open_utyp_wrt_utyp_rec]. f_equal. apply IH.
Qed.

Lemma open_utyp_all_syn_n_rec : forall j k ph W,
    open_utyp_wrt_utyp_rec k ph (utyp_all_syn_n j W)
    = utyp_all_syn_n j (open_utyp_wrt_utyp_rec (k + j) ph W).
Proof.
  induction j as [ | j IH ]; intros k ph W; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. replace (k + S j) with (S k + j) by lia. reflexivity.
Qed.

Lemma mode_fn_n_ge1_fn : forall n m,
    1 <= n -> exists m', mode_fn_n n m = mode_fn m'.
Proof. destruct n; intros m H; [ lia | exists (mode_fn_n n m); reflexivity ]. Qed.

(** At a function mode, a [utyp_all_syn] LHS can only be subtyped via the
    untagged [∀]-left rule. *)
Lemma d_sub_fn_all_syn_inv : forall Δ Γ m C B,
    Δ ⨟ Γ ⊢[ mode_fn m ] (utyp_all_syn C) ⊑ B ->
    exists Δ' ph,
      AtomSetImpl.inter Δ' Δ [=] empty /\ d_tags Δ' ph /\ Γ ⊢ᵤ ph /\ is_ttyp ph /\
      (Δ `union` Δ') ⨟ Γ ⊢[ mode_fn m ] (open_utyp_wrt_utyp C ph) ⊑ B.
Proof.
  intros Δ Γ m C B Hsub.
  inversion Hsub as [ | | | | | Δ0 Δ' Γ0 m0 C0 ph B0 Hm Hfresh Htags Hwfph Httyp Hpre ];
    subst.
  exists Δ', ph.
  split; [ exact Hfresh | ]. split; [ exact Htags | ].
  split; [ exact Hwfph | ]. split; [ exact Httyp | exact Hpre ].
Qed.

(** Same, at the [k]-fold function mode. *)
Lemma d_sub_fnn_all_syn_inv : forall n m Δ Γ C B,
    1 <= n ->
    Δ ⨟ Γ ⊢[ mode_fn_n n m ] (utyp_all_syn C) ⊑ B ->
    exists Δ' ph,
      AtomSetImpl.inter Δ' Δ [=] empty /\ d_tags Δ' ph /\ Γ ⊢ᵤ ph /\ is_ttyp ph /\
      (Δ `union` Δ') ⨟ Γ ⊢[ mode_fn_n n m ] (open_utyp_wrt_utyp C ph) ⊑ B.
Proof.
  intros n m Δ Γ C B Hpos Hsub.
  destruct (mode_fn_n_ge1_fn m Hpos) as [m' Hm']. rewrite Hm' in Hsub.
  apply d_sub_fn_all_syn_inv in Hsub as [Δ' [ph [Hf [Ht [Hw [Hi Hp]]]]]].
  exists Δ', ph. rewrite Hm'.
  split; [ exact Hf | ]. split; [ exact Ht | ].
  split; [ exact Hw | ]. split; [ exact Hi | exact Hp ].
Qed.

(** [spine_btyp] only sees the [snd] components, so it is invariant under a
    map that rewrites the [utyp] [fst]s (e.g. [∀]-instantiation). *)
Lemma spine_btyp_map_fst : forall (h : utyp -> utyp) Rb sp,
    spine_btyp Rb (List.map (fun p => (h (fst p), snd p)) sp) = spine_btyp Rb sp.
Proof.
  induction sp as [ | p sp IH ]; [ reflexivity | ].
  cbn [List.map]. rewrite spine_btyp_cons, spine_btyp_cons. cbn [fst snd].
  rewrite IH. reflexivity.
Qed.

(** ENGINE WITH [∀]-PREFIX: strip the [j] outer [∀]s (reusing the
    instantiation witnesses on the permuted side), then permute the argument
    spine via [d_sub_arrow_spine_perm].  The instantiation witnesses are
    arbitrary [utyp]s, which is why the spine engine is stated over arbitrary
    [utyp] arguments rather than paintings. *)
Lemma d_sub_prefix_spine_perm : forall j sp sp',
    Permutation sp sp' ->
    1 <= length sp ->
    forall Δ Γ Rt Rb m,
      Δ ⨟ Γ ⊢[ mode_fn_n (length sp) m ] (utyp_all_syn_n j (spine_utyp Rt sp)) ⊑ spine_btyp Rb sp ->
      Δ ⨟ Γ ⊢[ mode_fn_n (length sp') m ] (utyp_all_syn_n j (spine_utyp Rt sp')) ⊑ spine_btyp Rb sp'.
Proof.
  induction j as [ | j IHj ]; intros sp sp' Hperm Hpos Δ Γ Rt Rb m Hsub.
  - simpl in Hsub |- *. eapply d_sub_arrow_spine_perm; eassumption.
  - assert (Hle : length sp = length sp') by (apply Permutation_length; assumption).
    assert (Hpos' : 1 <= length sp') by (rewrite <- Hle; exact Hpos).
    simpl in Hsub.
    apply d_sub_fnn_all_syn_inv in Hsub as [Δ' [ph [Hf [Ht [Hw [Hi Hp]]]]]];
      [ | exact Hpos ].
    unfold open_utyp_wrt_utyp in Hp.
    rewrite open_utyp_all_syn_n_rec in Hp. simpl in Hp.
    rewrite open_spine_utyp_rec in Hp.
    (* Hp LHS in [map g] form, RHS still [spine_btyp Rb sp]; convert RHS to
       [map g] form so [IHj] (with spine [map g sp]) matches. *)
    rewrite <- (spine_btyp_map_fst (open_utyp_wrt_utyp_rec j ph) Rb sp) in Hp.
    rewrite <- (List.map_length
                  (fun p : utyp * btyp => (open_utyp_wrt_utyp_rec j ph (fst p), snd p)) sp)
      in Hp.
    apply IHj with
      (sp' := List.map (fun p => (open_utyp_wrt_utyp_rec j ph (fst p), snd p)) sp') in Hp;
      [ | apply Permutation_map; exact Hperm
        | rewrite List.map_length; exact Hpos ].
    rewrite List.map_length in Hp.
    rewrite spine_btyp_map_fst in Hp.
    (* reconstruct y's outer forall_l *)
    simpl. apply d_sub__forall_l_untagged with (Δ' := Δ') (ph := ph).
    + destruct (mode_fn_n_ge1_fn m Hpos') as [m'' Hm'']. rewrite Hm''. discriminate.
    + exact Hf.
    + exact Ht.
    + exact Hw.
    + exact Hi.
    + unfold open_utyp_wrt_utyp.
      rewrite open_utyp_all_syn_n_rec. simpl.
      rewrite open_spine_utyp_rec.
      exact Hp.
Qed.

(** ** Glue: transport the argument evidence and the spine pairing along the
    permutation, and rename a variable head with an identical binding. *)

Lemma map_combine_proj :
  forall (X Y Z W : Type) (h : X -> W) (l1 : list (X * Y)) (l2 : list Z),
    List.map (fun p => (h (fst (fst p)), snd p)) (combine l1 l2)
    = combine (List.map (fun q => h (fst q)) l1) l2.
Proof.
  induction l1 as [ | a l1 IH ]; destruct l2 as [ | b l2 ]; simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma Forall2_argok_to : forall Γ (args : list (ptyp * exp)) Bargs,
    Forall2 (arg_ok Γ) Bargs (List.map snd args) ->
    Forall2 (fun (ae : ptyp * exp) B => arg_ok Γ B (snd ae)) args Bargs.
Proof.
  induction args as [ | a args IH ]; intros Bargs H; simpl in H;
    inversion H; subst; constructor; auto.
Qed.

Lemma Forall2_argok_from : forall Γ (args : list (ptyp * exp)) Bargs,
    Forall2 (fun (ae : ptyp * exp) B => arg_ok Γ B (snd ae)) args Bargs ->
    Forall2 (arg_ok Γ) Bargs (List.map snd args).
Proof.
  induction args as [ | a args IH ]; intros Bargs H;
    inversion H; subst; simpl; constructor; auto.
Qed.

(** Permute two lists in lockstep, transporting a [Forall2] relation and
    yielding the combined permutation. *)
Lemma Permutation_zip_transport :
  forall (A B : Type) (R : A -> B -> Prop) (l1 l1' : list A),
    Permutation l1 l1' ->
    forall l2, Forall2 R l1 l2 ->
    exists l2', Forall2 R l1' l2' /\ Permutation (combine l1 l2) (combine l1' l2').
Proof.
  intros A B R l1 l1' Hperm. induction Hperm; intros l2 Hf.
  - inversion Hf; subst. exists nil. split; constructor.
  - inversion Hf as [ | a0 b l0 lb HR Hf' ]; subst.
    destruct (IHHperm lb Hf') as [lb' [Hf2 Hp2]].
    exists (b :: lb'). split; [ constructor; assumption | ].
    simpl. constructor. exact Hp2.
  - inversion Hf as [ | a0 b1 l0 lrest HR1 Hf1 ]; subst.
    inversion Hf1 as [ | a1 b2 l1 lrest2 HR2 Hf2 ]; subst.
    exists (b2 :: b1 :: lrest2). split.
    + constructor; [ assumption | constructor; assumption ].
    + simpl. apply perm_swap.
  - destruct (IHHperm1 l2 Hf) as [l2' [Hf' Hp']].
    destruct (IHHperm2 l2' Hf') as [l2'' [Hf'' Hp'']].
    exists l2''. split; [ assumption | eapply Permutation_trans; eassumption ].
Qed.

(** A variable head can be renamed to any other variable with an identical
    binding (only [d_typing__var] consults the binding; [uniq] pins it). *)
Lemma d_typing_var_rename : forall Γ m e B,
    Γ ⊢[ m ] e ⦂ B ->
    forall x y T, e = exp_var_f x -> uniq Γ ->
    binds x (dbind_typ T) Γ -> binds y (dbind_typ T) Γ ->
    Γ ⊢[ m ] (exp_var_f y) ⦂ B.
Proof.
  intros Γ m e B Htyp. induction Htyp; intros x0 y T Heq Huniq Hbx Hby;
    subst; try discriminate.
  - (* __var *)
    inversion Heq; subst.
    assert (dbind_typ A = dbind_typ T) by (eapply binds_unique; eauto).
    assert (A = T) by congruence. subst T.
    apply d_typing__var; exact Hby.
  - (* __sub *)
    eapply d_typing__sub;
      [ apply is_base_term__var | eapply IHHtyp; eauto | eassumption ].
  - (* __forall (var is a value) *)
    apply d_typing__forall with (L := L `union` dom Γ);
      [ apply is_value__var | ].
    intros X HX. eapply H1 with (x := x0) (y := y) (T := T); try reflexivity.
    + fsetdec.
    + apply uniq_push; [ exact Huniq | fsetdec ].
    + apply binds_cons_3; auto.
    + apply binds_cons_3; auto.
Qed.

(** * Head-subsumption permutation (the core).

    From a variable [x] typed (at the [k]-fold function mode) against a
    curried arrow [curry_btyp Bargs R'], with [x : ∀ⁿ.(curry args R)] and
    [y : ∀ⁿ.(curry args' R)] for a permutation [args ~ args'], produce a
    typing of [y] against the correspondingly-permuted arrow, together with
    the transported per-argument evidence.

    PROOF ([k = length args]):
    - [k = 0]: [args = args' = []], the two bindings coincide, so [y]'s
      typing is [x]'s with the variable renamed ([d_typing_var_rename]).
    - [k ≥ 1]: invert [x]'s head typing — at [mode_fn_n k m] only
      [d_typing__sub] fires, giving an EMPTY-[Δ] subtyping out of [x]'s
      [mode_ti] type.  That type is EXACTLY the binding painting
      ([d_consis_paint_syn_eq] applied to [d_typing_var_ti_consis]), so the
      subtyping is [∅ ⊢ ptyp_to_utyp_syn (∀ⁿ.curry args R) ⊑ curry_btyp Bargs R'].
      Re-express it in [spine]/[utyp_all_syn_n] form ([paint_forall_prefix],
      [paint_curry_spine], [spine_btyp_curry]) and permute via
      [d_sub_prefix_spine_perm] — which strips the [∀]-prefix reusing the
      instantiation witnesses and reorders the argument spine, the
      tag context being preserved as a SET (the empty top-level [Δ] is
      preserved, which is what [d_typing__sub] demands for the rebuild).
      Convert back to [y]'s binding painting and rebuild [y]'s typing with
      [d_typing__var] + [d_typing__sub].
    - [arg_ok] is per-argument, hence transported along the permutation by
      [Permutation_zip_transport].

    The conceptual content — set-union commutativity ⟹ argument order is
    irrelevant — lives in [d_sub_arrow_spine_perm]. *)
Lemma d_typing_var_head_perm : forall Γ m n x y args args' Bargs R R',
    d_wf_denv Γ ->
    Permutation args args' ->
    binds x (dbind_typ (ptyp_forall_prefix n (curry_ptyp args R))) Γ ->
    binds y (dbind_typ (ptyp_forall_prefix n (curry_ptyp args' R))) Γ ->
    Γ ⊢[ mode_fn_n (length args) m ] (exp_var_f x) ⦂ curry_btyp Bargs R' ->
    Forall2 (arg_ok Γ) Bargs (List.map snd args) ->
    exists Bargs',
      (Γ ⊢[ mode_fn_n (length args') m ] (exp_var_f y) ⦂ curry_btyp Bargs' R') /\
      Forall2 (arg_ok Γ) Bargs' (List.map snd args').
Proof.
  intros Γ m n x y args args' Bargs R R' Hwf Hperm Hbx Hby Hheadx Hallx.
  assert (Huniq : uniq Γ) by (apply d_wf_denv_uniq; exact Hwf).
  assert (HlenB : length Bargs = length args)
    by (apply Forall2_length in Hallx; rewrite List.map_length in Hallx; exact Hallx).
  destruct (Permutation_zip_transport Hperm (@Forall2_argok_to Γ args Bargs Hallx))
    as [Bargs' [Hall' Hcomb]].
  pose proof (@Forall2_argok_from Γ args' Bargs' Hall') as Hall'2.
  assert (HlenB' : length Bargs' = length args')
    by (apply Forall2_length in Hall'2; rewrite List.map_length in Hall'2; exact Hall'2).
  exists Bargs'. split; [ | exact Hall'2 ].
  destruct (Nat.eq_dec (length args) 0) as [ Hz | Hnz ].
  - (* k = 0: args = [] hence args' = [], Bargs = Bargs' = [] *)
    assert (Hae : args = nil) by (destruct args; [ reflexivity | simpl in Hz; discriminate ]).
    subst args. apply Permutation_nil in Hperm. subst args'.
    simpl in Hheadx, Hallx |- *.
    inversion Hallx; subst Bargs. inversion Hall'2; subst Bargs'.
    eapply d_typing_var_rename;
      [ exact Hheadx | reflexivity | exact Huniq | exact Hbx | exact Hby ].
  - (* k ≥ 1 *)
    assert (Hpos : 1 <= length args) by lia.
    assert (Hpos' : 1 <= length args') by (rewrite <- (Permutation_length Hperm); exact Hpos).
    (* x's head: extract the empty-[Δ] subtyping from the binding painting *)
    destruct (mode_fn_n_ge1_fn m Hpos) as [mfx Hmfx]. rewrite Hmfx in Hheadx.
    inversion Hheadx as [ | | | Γ0 m0 e0 B1 B2 Hbt Hti Hsub | | | | | | | ]; subst;
      try discriminate.
    destruct (@d_typing_var_ti_consis Γ x (ptyp_forall_prefix n (curry_ptyp args R)) B1
                Hwf Hbx Hti) as [Hstyp1 [Δt Hcons1]].
    pose proof (@d_consis_paint_syn_eq B1 Hstyp1 Δt Γ
                  (ptyp_forall_prefix n (curry_ptyp args R)) Hcons1) as HB1. subst B1.
    rewrite ptyp_to_utyp_syn_btyp_to_ptyp, btyp_to_utyp_syn_ptyp_to_btyp_syn in Hsub.
    rewrite paint_forall_prefix, (paint_curry_spine args Bargs R ltac:(lia)) in Hsub.
    rewrite <- (spine_btyp_curry args Bargs R' ltac:(lia)) in Hsub.
    rewrite <- Hmfx in Hsub.
    assert (Hlensp : length (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args) Bargs)
                     = length args)
      by (rewrite combine_length, List.map_length, HlenB; apply Nat.min_id).
    rewrite <- Hlensp in Hsub.
    (* permute the spine via the engine (forward, to fix the [sp'] evar) *)
    assert (Hpermsp : Permutation
              (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args) Bargs)
              (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args') Bargs')).
    { rewrite <- (map_combine_proj ptyp_to_utyp_syn args Bargs),
              <- (map_combine_proj ptyp_to_utyp_syn args' Bargs').
      apply Permutation_map. exact Hcomb. }
    assert (Hpossp : 1 <= length
              (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args) Bargs))
      by (rewrite Hlensp; exact Hpos).
    pose proof (@d_sub_prefix_spine_perm n
                  (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args) Bargs)
                  (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args') Bargs')
                  Hpermsp Hpossp empty Γ (ptyp_to_utyp_syn R) R' m Hsub) as Hsub'.
    (* convert back into [y]'s binding painting / curried arrow *)
    assert (Hlensp' : length
              (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args') Bargs') = length args')
      by (rewrite combine_length, List.map_length, HlenB'; apply Nat.min_id).
    rewrite Hlensp' in Hsub'.
    rewrite <- (paint_curry_spine args' Bargs' R ltac:(lia)) in Hsub'.
    rewrite <- paint_forall_prefix in Hsub'.
    rewrite (spine_btyp_curry args' Bargs' R' ltac:(lia)) in Hsub'.
    eapply d_typing__sub with
      (B1 := ptyp_to_btyp_syn (ptyp_forall_prefix n (curry_ptyp args' R))).
    + apply is_base_term__var.
    + apply d_typing__var. exact Hby.
    + rewrite ptyp_to_utyp_syn_btyp_to_ptyp, btyp_to_utyp_syn_ptyp_to_btyp_syn.
      exact Hsub'.
Qed.

(** * Order irrelevance of argument permutation.

    Permuting the arguments of a function-typed variable — and its argument
    types accordingly — does not affect typability.  Each entry of [args]
    pairs an argument type with its term, so one [Permutation] permutes both
    together; the function type carries an arbitrary [n]-quantifier prefix
    ([ptyp_forall_prefix]) and an arbitrary codomain [R]; the result [R'] at
    mode [m] is arbitrary.  The n-ary, polymorphic, full-permutation
    strengthening of the old [d_typing_order_irrel_adj].

    STATEMENT FIX (vs. the original stub): the [d_wf_denv Γ] premise is
    REQUIRED, not cosmetic — without it the lemma is unprovable.  The proof
    must invert [Γ ⊢[mode_ti] (exp_var_f x) ⦂ B1], which by [d_typing__var]
    only yields [B1 = ptyp_to_btyp_syn A₀] for *some* [binds x (dbind_typ A₀)];
    [uniq Γ] (from [d_wf_denv]) is what identifies [A₀] with the lemma's
    binding, and the consistency-transitivity steps need the binding's
    well-formedness.  This mirrors the old [d_typing_order_irrel_adj], which
    carried [d_wf_denv Γ] for exactly these reasons.

    STRENGTHENING NOTES.
    - HEAD GENERALITY (discharges the old TODO): the spine reassembly used
      here ([d_typing_var_fn_factor] + repeated [d_typing__app]) treats the
      head generically — only [d_typing__app] can fire on [exp_app _ _] since
      it is neither [is_base_term] nor [is_value].  The variable-specificity
      is confined to head-factoring; an arbitrary head with a supplied
      curried-arrow subsumption would slot in unchanged.
    - IFF FOR FREE: [Permutation] is symmetric, so this lemma also gives the
      converse by instantiating with the reverse permutation.
    - INDEPENDENT OF [d_refine_preserves_wf]: the per-argument refinement
      premise [nil ⊢ᵣ … ⊳ …] inside [d_typing__app] is transported verbatim
      from [x]'s derivation to [y]'s; order-irrelevance never rebuilds it. *)
Lemma d_typing_order_irrel : forall Γ m n x y args args' R R',
    d_wf_denv Γ ->
    Permutation args args' ->
    binds x (dbind_typ (ptyp_forall_prefix n (curry_ptyp args R))) Γ ->
    binds y (dbind_typ (ptyp_forall_prefix n (curry_ptyp args' R))) Γ ->
    Γ ⊢[ m ] curry_exp (exp_var_f x) args ⦂ R' ->
    Γ ⊢[ m ] curry_exp (exp_var_f y) args' ⦂ R'.
Proof.
  intros Γ m n x y args args' R R' Hwf Hperm Hbx Hby Htyp.
  (* Factor [x]'s curried application into head typing + per-arg evidence. *)
  apply d_typing_app_spine_inv in Htyp as [Bargs [Hlen [Hheadx Hallx]]].
  (* Permute the head subsumption and transport the argument evidence. *)
  destruct (@d_typing_var_head_perm Γ m n x y args args' Bargs R R'
              Hwf Hperm Hbx Hby Hheadx Hallx)
    as [Bargs' [Hheady Hally']].
  (* Reassemble [y]'s curried application. *)
  pose proof (Forall2_length Hally') as Hlen'. rewrite List.map_length in Hlen'.
  eapply d_typing_app_spine_build with (Bargs := Bargs');
    [ exact Hlen' | exact Hheady | exact Hally' ].
Qed.

(* Sanity: no axioms or admits — "Closed under the global context". *)
Print Assumptions d_typing_order_irrel.

(** * Worked example (sanity check).

    [x : ∀a. a → (a→a) → int],  [y : ∀a. (a→a) → a → int].
    Then [x 1 (λz.z)] typeable implies [y (λz.z) 1] typeable.

    The bound [a] is [ptyp_var_b 0] under the single [∀]; [int] is an
    arbitrary codomain [Rint]; [1] and [λz.z] are arbitrary argument terms
    [one], [zid] (their per-argument well-typing is carried inside the
    application-typing hypothesis and transported verbatim).  The two
    binding types and the two application terms are *definitionally* the
    [ptyp_forall_prefix]/[curry_ptyp]/[curry_exp] instances, so the lemma
    applies up to computation; the argument lists are swaps, so
    [Permutation] is [perm_swap]. *)
Example order_irrel_x_y :
  forall Γ m x y (one zid : exp) (Rint : ptyp) (R' : btyp),
    d_wf_denv Γ ->
    binds x (dbind_typ
      (ptyp_all (ptyp_arrow (ptyp_var_b 0)
        (ptyp_arrow (ptyp_arrow (ptyp_var_b 0) (ptyp_var_b 0)) Rint)))) Γ ->
    binds y (dbind_typ
      (ptyp_all (ptyp_arrow (ptyp_arrow (ptyp_var_b 0) (ptyp_var_b 0))
        (ptyp_arrow (ptyp_var_b 0) Rint)))) Γ ->
    Γ ⊢[ m ] (exp_app (exp_app (exp_var_f x) one) zid) ⦂ R' ->
    Γ ⊢[ m ] (exp_app (exp_app (exp_var_f y) zid) one) ⦂ R'.
Proof.
  intros Γ m x y one zid Rint R' Hwf Hbx Hby Htyp.
  apply (@d_typing_order_irrel Γ m 1 x y
           ((ptyp_var_b 0, one)
            :: (ptyp_arrow (ptyp_var_b 0) (ptyp_var_b 0), zid) :: nil)
           ((ptyp_arrow (ptyp_var_b 0) (ptyp_var_b 0), zid)
            :: (ptyp_var_b 0, one) :: nil)
           Rint R');
    [ exact Hwf | apply perm_swap | exact Hbx | exact Hby | exact Htyp ].
Qed.
