Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_general_subsumption.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.decl.prop_syntax_directed.

Set Implicit Arguments.

Lemma d_typing_var_ti_consis : forall Γ x A B1,
    d_wf_denv Γ ->
    binds x (dbind_typ A) Γ ->
    {{ Γ ⊢[ mode_ti ] (exp_var_f x) ⦂ B1 }}d ->
    is_styp B1 /\ exists Ψt, {{ Ψt ⨟ Γ ⊢ ptyp_to_utyp_syn A ∼ B1 }}d.
Proof.
  intros Γ x A B1 Hwf Hb Htyp.
  assert (Huniq : uniq Γ) by (apply d_wf_denv_uniq; exact Hwf).
  remember (exp_var_f x) as e. remember mode_ti as m.
  induction Htyp; subst; try discriminate.
  -
    inversion Heqe; subst x0.
    assert (A0 = A) by
      (assert (dbind_typ A0 = dbind_typ A) by (eapply binds_unique; eauto);
       congruence). subst A0.
    assert (Hwfa : d_wf_ptyp Γ A) by (eapply d_wf_denv_binds_ptyp; eauto).
    split.
    + apply is_styp_ptyp_to_btyp_syn; eapply d_wf_ptyp_lc; eauto.
    + exists empty. apply d_consis_syn_refl; exact Hwfa.
  -
    match goal with H : {{ empty ⨟ _ ⊢[ mode_ti ] _ ⩽ B }}d |- _ =>
      rename H into Hsub end.
    inversion Hsub as [ Ψ0 Γ0 C0 B0 Hcons0 Hstyp0 HΨ0 | | | | | ]; subst;
      try congruence.
    edestruct IHHtyp as [Hstyp1 [Ψt Hcons1]]; auto.
    split; [ exact Hstyp0 | ].
    edestruct d_consis_compose as [Ψc [_ Hc]].
    + exact Hcons1.
    + exact Hcons0.
    + exists Ψc. exact Hc.
Qed.

Definition curry_ptyp (args : list (ptyp * exp)) (R : ptyp) : ptyp :=
  fold_right (fun ae acc => ptyp_arrow (fst ae) acc) R args.

Definition curry_exp (f : exp) (args : list (ptyp * exp)) : exp :=
  fold_left (fun g ae => exp_app g (snd ae)) args f.

Fixpoint ptyp_forall_prefix (n : nat) (A : ptyp) : ptyp :=
  match n with
  | O => A
  | S n' => ptyp_all (ptyp_forall_prefix n' A)
  end.

Definition curry_btyp (Bargs : list btyp) (B : btyp) : btyp :=
  fold_right btyp_arrow B Bargs.

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

Definition arg_ok (Γ : list (atom * dbind)) (Barg : btyp) (e : exp) : Prop :=
  exists P,
    ({{ Γ ⊢ˢ[ mode_tc ] e ⦂ (pskl_to_bskl_syn P) }}d) /\
    ({{ Γ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl Barg) }}d) /\
    ({{ Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh (btyp_to_ptyp Barg)) }}d).

Lemma d_typing_app_step : forall Γ m e1 e2 Barg B,
    {{ Γ ⊢[ mode_fn m ] e1 ⦂ (btyp_arrow Barg B) }}d ->
    arg_ok Γ Barg e2 ->
    {{ Γ ⊢[ m ] (exp_app e1 e2) ⦂ B }}d.
Proof.
  intros Γ m e1 e2 Barg B Hhead [P [Hpat [Href Hchk]]].
  eapply d_typing__app with (P := P) (B1 := Barg);
    [ exact Hpat | exact Href | exact Hhead | exact Hchk ].
Qed.

Lemma btyp_spine_curry : forall Bargs Bt Bnew,
    is_styp Bt ->
    btyp_spine (length Bargs) (curry_btyp Bargs Bt) Bt Bnew (curry_btyp Bargs Bnew).
Proof.
  induction Bargs; intros; simpl;
    [ apply btyp_spine__tail; assumption | apply btyp_spine__arrow; auto ].
Qed.

Lemma is_fn_n_mode_fn_n : forall k, is_fn_n k (mode_fn_n k mode_ti).
Proof. induction k; simpl; [ apply is_fn_n__ti | apply is_fn_n__fn; assumption ]. Qed.

Lemma mode_fn_n_subst_fn_n : forall k m,
    mode_fn_n_subst (mode_fn_n k mode_ti) m = mode_fn_n k m.
Proof. induction k; intros m; simpl; [ reflexivity | rewrite IHk; reflexivity ]. Qed.

Lemma d_typing_app_spine_inv : forall args Γ f m B',
    d_wf_denv Γ ->
    {{ Γ ⊢[ m ] curry_exp f args ⦂ B' }}d ->
    exists Bargs,
      length Bargs = length args /\
      ({{ Γ ⊢[ mode_fn_n (length args) m ] f ⦂ curry_btyp Bargs B' }}d) /\
      Forall2 (arg_ok Γ) Bargs (List.map snd args).
Proof.
  intro args. induction args as [ | a init IHinit ] using rev_ind;
    intros Γ f m B' Hwf Htyp.
  -
    exists nil. simpl. repeat split; [ exact Htyp | constructor ].
  -
    rewrite curry_exp_snoc in Htyp.
    remember (exp_app (curry_exp f init) (snd a)) as ea eqn:Hea.
    revert Hwf Hea. induction Htyp; intros Hwf Hea;
      try discriminate Hea;
      try (exfalso; subst;
           match goal with Hv : is_value (exp_app _ _) |- _ => inversion Hv end).
    +
      subst e.
      destruct (IHHtyp Hwf eq_refl) as [Bargs [Hlen [Hhead Hall]]].
      assert (Hst : is_styp (ptyp_to_btyp_syn A)).
      { apply is_styp_ptyp_to_btyp_syn, lc_ptyp_of_lc_utyp_syn.
        eapply d_sub_lc_l. eassumption. }
      exists Bargs. split; [ exact Hlen | split; [ | exact Hall ] ].
      rewrite <- Hlen. rewrite <- Hlen in Hhead.
      rewrite <- (mode_fn_n_subst_fn_n (length Bargs) m).
      eapply d_typing_general_subsumption_spine;
        [ exact Hwf
        | exact Hhead
        | apply is_fn_n_mode_fn_n
        | apply btyp_spine_curry; exact Hst
        | rewrite btyp_to_utyp_syn_ptyp_to_btyp_syn; eassumption ].
    +
      injection Hea; intros; subst.
      edestruct (IHinit Γ f (mode_fn m) (btyp_arrow B1 B2)) as [Bi [Hlen [Hhd Hfa]]];
        [ exact Hwf | eassumption | ].
      exists (Bi ++ B1 :: nil). repeat split.
      * rewrite !app_length. simpl. rewrite Hlen. reflexivity.
      * rewrite curry_btyp_snoc.
        rewrite mode_fn_n_fn in Hhd.
        rewrite app_length, Nat.add_1_r. simpl. exact Hhd.
      * rewrite List.map_app. simpl. apply Forall2_app; [ exact Hfa | ].
        constructor; [ | constructor ].
        eexists; repeat split; eassumption.
Qed.

Lemma d_typing_app_spine_build : forall args Γ f m B' Bargs,
    length Bargs = length args ->
    {{ Γ ⊢[ mode_fn_n (length args) m ] f ⦂ curry_btyp Bargs B' }}d ->
    Forall2 (arg_ok Γ) Bargs (List.map snd args) ->
    {{ Γ ⊢[ m ] curry_exp f args ⦂ B' }}d.
Proof.
  intro args. induction args as [ | a init IHinit ] using rev_ind;
    intros Γ f m B' Bargs Hlen Hhead Hall.
  -  destruct Bargs; [ simpl in Hhead; exact Hhead | inversion Hlen ].
  -
    rewrite curry_exp_snoc.
    rewrite List.map_app in Hall. simpl in Hall.
    apply Forall2_app_inv_r in Hall as [Bi [Blast [Hfa [Hlast HBeq]]]].
    inversion Hlast as [ | Barg e0 Btl etl Haok Htail HBl Hel ]; subst.
    inversion Htail; subst.
    apply d_typing_app_step with (Barg := Barg); [ | exact Haok ].
    apply (IHinit Γ f (mode_fn m) (btyp_arrow Barg B') Bi).
    + apply Forall2_length in Hfa. rewrite List.map_length in Hfa. exact Hfa.
    + rewrite curry_btyp_snoc in Hhead.
      rewrite app_length, Nat.add_1_r in Hhead. simpl in Hhead.
      rewrite <- mode_fn_n_fn in Hhead. exact Hhead.
    + exact Hfa.
Qed.

Definition spine_utyp (Rt : utyp) (sp : list (utyp * btyp)) : utyp :=
  fold_right (fun p acc => utyp_arrow (fst p) acc) Rt sp.
Definition spine_btyp (Rb : btyp) (sp : list (utyp * btyp)) : btyp :=
  fold_right (fun p acc => btyp_arrow (snd p) acc) Rb sp.

Lemma d_sub_arrow_spine_perm : forall sp sp',
    Permutation sp sp' ->
    forall Ψ Γ Ct Bb m,
      {{ Ψ ⨟ Γ ⊢[ mode_fn_n (length sp) m ] spine_utyp Ct sp ⩽ spine_btyp Bb sp }}d ->
      {{ Ψ ⨟ Γ ⊢[ mode_fn_n (length sp') m ] spine_utyp Ct sp' ⩽ spine_btyp Bb sp' }}d.
Proof.
  intros sp sp' Hperm. induction Hperm; intros Ψ Γ Ct Bb m Hsub.
  -  exact Hsub.
  -
    simpl in Hsub |- *.
    inversion Hsub as [ | | | Ψ0 Ψ1 Ψ2 Γ0 m0 C1 C2 B1 B2 Hcons Hrest HΔ | | ]; subst.
    apply d_sub__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ exact Hcons | apply IHHperm; exact Hrest | exact HΔ ].
  -
    simpl in Hsub |- *.
    inversion Hsub as [ | | | Ψ0 Ψy Ψyr Γ0 m0 Cy C2 By B2 Hcy Hyr HΔyr | | ]; subst.
    inversion Hyr as [ | | | Ψ0' Ψx Ψl Γ0' m0' Cx C2' Bx B2' Hcx Hl HΔl | | ]; subst.
    apply d_sub__arrow with (Ψ1 := Ψx) (Ψ2 := (Ψy `union` Ψl));
      [ exact Hcx
      | apply d_sub__arrow with (Ψ1 := Ψy) (Ψ2 := Ψl);
          [ exact Hcy | exact Hl | reflexivity ]
      | fsetdec ].
  -
    apply IHHperm2. apply IHHperm1. exact Hsub.
Qed.

Lemma spine_utyp_cons : forall Ct p sp,
    spine_utyp Ct (p :: sp) = utyp_arrow (fst p) (spine_utyp Ct sp).
Proof. reflexivity. Qed.

Lemma spine_btyp_cons : forall Bb p sp,
    spine_btyp Bb (p :: sp) = btyp_arrow (snd p) (spine_btyp Bb sp).
Proof. reflexivity. Qed.

Lemma curry_ptyp_cons : forall a args A,
    curry_ptyp (a :: args) A = ptyp_arrow (fst a) (curry_ptyp args A).
Proof. reflexivity. Qed.

Lemma curry_btyp_cons : forall B Bargs B',
    curry_btyp (B :: Bargs) B' = btyp_arrow B (curry_btyp Bargs B').
Proof. reflexivity. Qed.

Fixpoint utyp_all_syn_n (j : nat) (C : utyp) : utyp :=
  match j with O => C | S j' => utyp_all_syn (utyp_all_syn_n j' C) end.

Lemma paint_forall_prefix : forall n A,
    ptyp_to_utyp_syn (ptyp_forall_prefix n A) = utyp_all_syn_n n (ptyp_to_utyp_syn A).
Proof. induction n; intros A; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

Lemma paint_curry_spine : forall args Bargs A,
    length args = length Bargs ->
    ptyp_to_utyp_syn (curry_ptyp args A)
    = spine_utyp (ptyp_to_utyp_syn A)
        (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args) Bargs).
Proof.
  induction args as [ | a args IH ]; destruct Bargs as [ | b Bargs ]; intros A Hlen;
    try discriminate; [ reflexivity | ].
  cbn [List.map combine] in *. rewrite spine_utyp_cons, curry_ptyp_cons.
  cbn [fst snd ptyp_to_utyp_syn]. f_equal. apply IH. cbn [length] in Hlen. congruence.
Qed.

Lemma spine_btyp_curry : forall (args : list (ptyp * exp)) Bargs B',
    length args = length Bargs ->
    spine_btyp B' (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args) Bargs)
    = curry_btyp Bargs B'.
Proof.
  induction args as [ | a args IH ]; destruct Bargs as [ | b Bargs ]; intros B' Hlen;
    try discriminate; [ reflexivity | ].
  cbn [List.map combine] in *. rewrite spine_btyp_cons, curry_btyp_cons.
  cbn [fst snd]. f_equal. apply IH. cbn [length] in Hlen. congruence.
Qed.

Lemma open_spine_utyp_rec : forall sp k C Ct,
    open_utyp_wrt_utyp_rec k C (spine_utyp Ct sp)
    = spine_utyp (open_utyp_wrt_utyp_rec k C Ct)
        (List.map (fun p => (open_utyp_wrt_utyp_rec k C (fst p), snd p)) sp).
Proof.
  induction sp as [ | p sp IH ]; intros k C Ct; [ reflexivity | ].
  rewrite spine_utyp_cons. cbn [List.map]. rewrite spine_utyp_cons.
  cbn [fst snd open_utyp_wrt_utyp_rec]. f_equal. apply IH.
Qed.

Lemma open_utyp_all_syn_n_rec : forall j k C C',
    open_utyp_wrt_utyp_rec k C (utyp_all_syn_n j C')
    = utyp_all_syn_n j (open_utyp_wrt_utyp_rec (k + j) C C').
Proof.
  induction j as [ | j IH ]; intros k C C'; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. replace (k + S j) with (S k + j) by lia. reflexivity.
Qed.

Lemma mode_fn_n_ge1_fn : forall n m,
    1 <= n -> exists m', mode_fn_n n m = mode_fn m'.
Proof. destruct n; intros m H; [ lia | exists (mode_fn_n n m); reflexivity ]. Qed.

Lemma d_sub_fn_all_syn_inv : forall Ψ Γ m C B,
    {{ Ψ ⨟ Γ ⊢[ mode_fn m ] (utyp_all_syn C) ⩽ B }}d ->
    exists Ψ' C',
      Ψ' ∩ Ψ [=] empty /\
      Ψ' ∩ (ftag_in_utyp (utyp_all_syn C)) [=] empty /\
      d_tags Ψ' C' /\ {{ Γ ⊢ᵤ C' }}d /\ is_dtyp C' /\
      {{ (Ψ `union` Ψ') ⨟ Γ ⊢[ mode_fn m ] (open_utyp_wrt_utyp C C') ⩽ B }}d.
Proof.
  intros Ψ Γ m C B Hsub.
  inversion Hsub as [ | | | | | Ψ0 Ψ' Γ0 m0 C0 C' B0 Hm Hfresh Hhyg Htags Hwfph Httyp Hpre ];
    subst.
  exists Ψ', C'.
  split; [ exact Hfresh | ]. split; [ exact Hhyg | ]. split; [ exact Htags | ].
  split; [ exact Hwfph | ]. split; [ exact Httyp | exact Hpre ].
Qed.

Lemma d_sub_fnn_all_syn_inv : forall n m Ψ Γ C B,
    1 <= n ->
    {{ Ψ ⨟ Γ ⊢[ mode_fn_n n m ] (utyp_all_syn C) ⩽ B }}d ->
    exists Ψ' C',
      Ψ' ∩ Ψ [=] empty /\
      Ψ' ∩ (ftag_in_utyp (utyp_all_syn C)) [=] empty /\
      d_tags Ψ' C' /\ {{ Γ ⊢ᵤ C' }}d /\ is_dtyp C' /\
      {{ (Ψ `union` Ψ') ⨟ Γ ⊢[ mode_fn_n n m ] (open_utyp_wrt_utyp C C') ⩽ B }}d.
Proof.
  intros n m Ψ Γ C B Hpos Hsub.
  destruct (mode_fn_n_ge1_fn m Hpos) as [m' Hm']. rewrite Hm' in Hsub.
  apply d_sub_fn_all_syn_inv in Hsub as [Ψ' [C' [Hf [Hh [Ht [Hw [Hi Hp]]]]]]].
  exists Ψ', C'. rewrite Hm'.
  split; [ exact Hf | ]. split; [ exact Hh | ]. split; [ exact Ht | ].
  split; [ exact Hw | ]. split; [ exact Hi | exact Hp ].
Qed.

Lemma spine_btyp_map_fst : forall (h : utyp -> utyp) Bb sp,
    spine_btyp Bb (List.map (fun p => (h (fst p), snd p)) sp) = spine_btyp Bb sp.
Proof.
  induction sp as [ | p sp IH ]; [ reflexivity | ].
  cbn [List.map]. rewrite spine_btyp_cons, spine_btyp_cons. cbn [fst snd].
  rewrite IH. reflexivity.
Qed.

Lemma ftag_utyp_all_syn_n : forall j C,
    ftag_in_utyp (utyp_all_syn_n j C) [=] ftag_in_utyp C.
Proof. induction j; intros C; simpl; [ reflexivity | apply IHj ]. Qed.

Lemma ftag_spine_utyp_perm : forall Ct sp sp',
    Permutation sp sp' ->
    ftag_in_utyp (spine_utyp Ct sp) [=] ftag_in_utyp (spine_utyp Ct sp').
Proof.
  intros Ct sp sp' H. induction H.
  - reflexivity.
  - rewrite !spine_utyp_cons. cbn [ftag_in_utyp]. rewrite IHPermutation.
    reflexivity.
  - rewrite !spine_utyp_cons. cbn [ftag_in_utyp]. fsetdec.
  - rewrite IHPermutation1. exact IHPermutation2.
Qed.

Lemma d_sub_prefix_spine_perm : forall j sp sp',
    Permutation sp sp' ->
    1 <= length sp ->
    forall Ψ Γ Ct Bb m,
      {{ Ψ ⨟ Γ ⊢[ mode_fn_n (length sp) m ] (utyp_all_syn_n j (spine_utyp Ct sp)) ⩽ spine_btyp Bb sp }}d ->
      {{ Ψ ⨟ Γ ⊢[ mode_fn_n (length sp') m ] (utyp_all_syn_n j (spine_utyp Ct sp')) ⩽ spine_btyp Bb sp' }}d.
Proof.
  induction j as [ | j IHj ]; intros sp sp' Hperm Hpos Ψ Γ Ct Bb m Hsub.
  - simpl in Hsub |- *. eapply d_sub_arrow_spine_perm; eassumption.
  - assert (Hle : length sp = length sp') by (apply Permutation_length; assumption).
    assert (Hpos' : 1 <= length sp') by (rewrite <- Hle; exact Hpos).
    simpl in Hsub.
    apply d_sub_fnn_all_syn_inv in Hsub as [Ψ' [ph [Hf [Hh [Ht [Hw [Hi Hp]]]]]]];
      [ | exact Hpos ].
    unfold open_utyp_wrt_utyp in Hp.
    rewrite open_utyp_all_syn_n_rec in Hp. simpl in Hp.
    rewrite open_spine_utyp_rec in Hp.
    rewrite <- (spine_btyp_map_fst (open_utyp_wrt_utyp_rec j ph) Bb sp) in Hp.
    rewrite <- (List.map_length
                  (fun p : utyp * btyp => (open_utyp_wrt_utyp_rec j ph (fst p), snd p)) sp)
      in Hp.
    apply IHj with
      (sp' := List.map (fun p => (open_utyp_wrt_utyp_rec j ph (fst p), snd p)) sp') in Hp;
      [ | apply Permutation_map; exact Hperm
        | rewrite List.map_length; exact Hpos ].
    rewrite List.map_length in Hp.
    rewrite spine_btyp_map_fst in Hp.

    simpl. apply d_sub__forall_l_untagged with (Ψ' := Ψ') (ph := ph).
    + destruct (mode_fn_n_ge1_fn m Hpos') as [m'' Hm'']. rewrite Hm''. discriminate.
    + exact Hf.
    +
      cbn [ftag_in_utyp] in Hh |- *.
      rewrite !ftag_utyp_all_syn_n in Hh |- *.
      rewrite <- (ftag_spine_utyp_perm Ct Hperm). exact Hh.
    + exact Ht.
    + exact Hw.
    + exact Hi.
    + unfold open_utyp_wrt_utyp.
      rewrite open_utyp_all_syn_n_rec. simpl.
      rewrite open_spine_utyp_rec.
      exact Hp.
Qed.

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

Lemma d_typing_var_head_perm : forall Γ m n x y args args' Bargs A' B',
    d_wf_denv Γ ->
    Permutation args args' ->
    binds x (dbind_typ (ptyp_forall_prefix n (curry_ptyp args A'))) Γ ->
    binds y (dbind_typ (ptyp_forall_prefix n (curry_ptyp args' A'))) Γ ->
    {{ Γ ⊢[ mode_fn_n (length args) m ] (exp_var_f x) ⦂ curry_btyp Bargs B' }}d ->
    Forall2 (arg_ok Γ) Bargs (List.map snd args) ->
    exists Bargs',
      ({{ Γ ⊢[ mode_fn_n (length args') m ] (exp_var_f y) ⦂ curry_btyp Bargs' B' }}d) /\
      Forall2 (arg_ok Γ) Bargs' (List.map snd args').
Proof.
  intros Γ m n x y args args' Bargs A' B' Hwf Hperm Hbx Hby Hheadx Hallx.
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
  -
    assert (Hae : args = nil) by (destruct args; [ reflexivity | simpl in Hz; discriminate ]).
    subst args. apply Permutation_nil in Hperm. subst args'.
    simpl in Hheadx, Hallx |- *.
    inversion Hallx; subst Bargs. inversion Hall'2; subst Bargs'.
    assert (Hsub := d_typing_subst_var Hheadx x y _ Huniq Hbx Hby).
    assert (Heqv : subst_exp_in_exp (exp_var_f y) x (exp_var_f x) = exp_var_f y)
      by default_simp.
    rewrite Heqv in Hsub. exact Hsub.
  -
    assert (Hpos : 1 <= length args) by lia.
    assert (Hpos' : 1 <= length args') by (rewrite <- (Permutation_length Hperm); exact Hpos).

    destruct (mode_fn_n_ge1_fn m Hpos) as [mfx Hmfx]. rewrite Hmfx in Hheadx.
    inversion Hheadx as [ | | | Γ0 m0 e0 B1 B2 Hti Hsub | | | | | ]; subst;
      try discriminate.
    destruct (@d_typing_var_ti_consis Γ x (ptyp_forall_prefix n (curry_ptyp args A'))
                (ptyp_to_btyp_syn B1) Hwf Hbx Hti) as [Hstyp1 [Δt Hcons1]].
    pose proof (@d_consis_paint_syn_eq (ptyp_to_btyp_syn B1) Hstyp1 Δt Γ
                  (ptyp_forall_prefix n (curry_ptyp args A')) Hcons1) as HB1.
    apply (f_equal btyp_to_ptyp) in HB1.
    rewrite !btyp_to_ptyp_ptyp_to_btyp_syn in HB1. subst B1.
    rewrite paint_forall_prefix, (paint_curry_spine args Bargs A' ltac:(lia)) in Hsub.
    rewrite <- (spine_btyp_curry args Bargs B' ltac:(lia)) in Hsub.
    rewrite <- Hmfx in Hsub.
    assert (Hlensp : length (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args) Bargs)
                     = length args)
      by (rewrite combine_length, List.map_length, HlenB; apply Nat.min_id).
    rewrite <- Hlensp in Hsub.

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
                  Hpermsp Hpossp empty Γ (ptyp_to_utyp_syn A') B' m Hsub) as Hsub'.

    assert (Hlensp' : length
              (combine (List.map (fun ae => ptyp_to_utyp_syn (fst ae)) args') Bargs') = length args')
      by (rewrite combine_length, List.map_length, HlenB'; apply Nat.min_id).
    rewrite Hlensp' in Hsub'.
    rewrite <- (paint_curry_spine args' Bargs' A' ltac:(lia)) in Hsub'.
    rewrite <- paint_forall_prefix in Hsub'.
    rewrite (spine_btyp_curry args' Bargs' B' ltac:(lia)) in Hsub'.
    eapply d_typing__sub with
      (A := ptyp_forall_prefix n (curry_ptyp args' A')).
    + apply d_typing__var. exact Hby.
    + exact Hsub'.
Qed.

Lemma d_typing_order_irrel : forall Γ m n x y args args' A B',
    d_wf_denv Γ ->
    Permutation args args' ->
    binds x (dbind_typ (ptyp_forall_prefix n (curry_ptyp args A))) Γ ->
    binds y (dbind_typ (ptyp_forall_prefix n (curry_ptyp args' A))) Γ ->
    {{ Γ ⊢[ m ] curry_exp (exp_var_f x) args ⦂ B' }}d ->
    {{ Γ ⊢[ m ] curry_exp (exp_var_f y) args' ⦂ B' }}d.
Proof.
  intros Γ m n x y args args' A B' Hwf Hperm Hbx Hby Htyp.

  destruct (@d_typing_app_spine_inv args Γ (exp_var_f x) m B' Hwf Htyp)
    as [Bargs [Hlen [Hheadx Hallx]]].

  destruct (@d_typing_var_head_perm Γ m n x y args args' Bargs A B'
              Hwf Hperm Hbx Hby Hheadx Hallx)
    as [Bargs' [Hheady Hally']].

  pose proof (Forall2_length Hally') as Hlen'. rewrite List.map_length in Hlen'.
  eapply d_typing_app_spine_build with (Bargs := Bargs');
    [ exact Hlen' | exact Hheady | exact Hally' ].
Qed.
