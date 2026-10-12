Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Wf_nat.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.basic.def_order.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Fixpoint nall_ptyp (A : ptyp) : nat :=
  match A with
  | ptyp_arrow A1 A2 => nall_ptyp A1 + nall_ptyp A2
  | ptyp_all A1      => 1 + nall_ptyp A1
  | _                => 0
  end.

Fixpoint nall_pskl (P : pskl) : nat :=
  match P with
  | pskl_arrow P1 P2 => nall_pskl P1 + nall_pskl P2
  | pskl_all_syn P1  => 1 + nall_pskl P1
  | pskl_univ_ghost P1  => nall_pskl P1
  | _                => 0
  end.

Lemma nall_pskl_open_rec : forall P β k,
  nall_pskl (open_pskl_wrt_pskl_rec k (pskl_var_f β) P) = nall_pskl P.
Proof.
  induction P; intros β k; simpl;
    try reflexivity;
    try (match goal with
         | |- context [ lt_eq_lt_dec ?a ?b ] =>
             destruct (lt_eq_lt_dec a b) as [[?|?]|?]
         end; reflexivity);
    first [ solve [ auto ] | f_equal; auto ].
Qed.

Corollary nall_pskl_open : forall P β,
  nall_pskl (open_pskl_wrt_pskl P (pskl_var_f β)) = nall_pskl P.
Proof. intros. apply nall_pskl_open_rec. Qed.

Lemma nall_ptyp_to_pskl : forall A,
  nall_pskl (ptyp_to_pskl A) = nall_ptyp A.
Proof. induction A; simpl; lia. Qed.

Fixpoint hnall_ptyp (A : ptyp) : nat :=
  match A with
  | ptyp_all A1 => 1 + hnall_ptyp A1
  | _           => 0
  end.

Fixpoint hnall_pskl (P : pskl) : nat :=
  match P with
  | pskl_all_syn P1 => 1 + hnall_pskl P1
  | pskl_univ_ghost P1 => hnall_pskl P1
  | _               => 0
  end.

Lemma guarded_pskl_hnall : forall P, guarded_pskl P -> hnall_pskl P = 0.
Proof. intros * H; destruct H; reflexivity. Qed.

Lemma hnall_ptyp_to_pskl : forall A,
  hnall_pskl (ptyp_to_pskl A) = hnall_ptyp A.
Proof. induction A; simpl; lia. Qed.

Lemma hnall_ptyp_close_rec : forall A β k,
  hnall_ptyp (close_ptyp_wrt_ptyp_rec k β A) = hnall_ptyp A.
Proof.
  induction A; intros β k; simpl;
    try reflexivity;
    try (match goal with |- context [ if ?c then _ else _ ] => destruct c end;
         reflexivity);
    auto.
Qed.

Corollary hnall_ptyp_close : forall A β,
  hnall_ptyp (close_ptyp_wrt_ptyp β A) = hnall_ptyp A.
Proof. intros. apply hnall_ptyp_close_rec. Qed.

Fixpoint chain_hits_pskl (k : nat) (P : pskl) : bool :=
  match P with
  | pskl_var_b j    => Nat.eqb j k
  | pskl_all_syn P1 => chain_hits_pskl (S k) P1
  | pskl_univ_ghost P1 => chain_hits_pskl k P1
  | _               => false
  end.

Lemma hnall_pskl_open_rec_graft : forall P Q k,
  hnall_pskl (open_pskl_wrt_pskl_rec k Q P)
  = hnall_pskl P + (if chain_hits_pskl k P then hnall_pskl Q else 0).
Proof.
  induction P; intros Q k; simpl;
    try lia;

    try (rewrite IHP; destruct (chain_hits_pskl _ P); lia);
    match goal with
    | |- context [ lt_eq_lt_dec ?j ?k0 ] =>
        destruct (lt_eq_lt_dec j k0) as [[?|?]|?];
        destruct (Nat.eqb_spec j k0); simpl; subst; lia
    end.
Qed.

Corollary hnall_pskl_open_graft : forall P Q,
  hnall_pskl (open_pskl_wrt_pskl P Q)
  = hnall_pskl P + (if chain_hits_pskl 0 P then hnall_pskl Q else 0).
Proof. intros. apply hnall_pskl_open_rec_graft. Qed.

Corollary hnall_pskl_open : forall P β,
  hnall_pskl (open_pskl_wrt_pskl P (pskl_var_f β)) = hnall_pskl P.
Proof.
  intros. rewrite hnall_pskl_open_graft. simpl.
  destruct (chain_hits_pskl 0 P); lia.
Qed.

Fixpoint pure_chain_to (α : atom) (P : pskl) : Prop :=
  match P with
  | pskl_var_f β    => β = α
  | pskl_all_syn P1 => pure_chain_to α P1
  | pskl_univ_ghost P1 => pure_chain_to α P1
  | _               => False
  end.

Lemma pure_chain_to_open_rec : forall P α β k,
  pure_chain_to α P ->
  pure_chain_to α (open_pskl_wrt_pskl_rec k (pskl_var_f β) P).
Proof.

  induction P; intros α0 β0 k Hc; simpl in *; try contradiction; auto.
Qed.

Lemma chain_hits_open_pure_chain : forall P α k,
  chain_hits_pskl k P = true ->
  pure_chain_to α (open_pskl_wrt_pskl_rec k (pskl_var_f α) P).
Proof.

  induction P; intros α0 k Hc; simpl in *; try discriminate; auto.
  match goal with
  | Hc : Nat.eqb ?j ?k0 = true |- _ =>
      destruct (Nat.eqb_spec j k0); [ subst | discriminate ];
      destruct (lt_eq_lt_dec k0 k0) as [[?|?]|?]; simpl; auto; lia
  end.
Qed.

Lemma e_looksub_pure_chain_cstrs : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  pure_chain_to α P ->
  (guarded_pskl P' \/ P' = pskl_ghost) ->
  C = (a_cstr_sub m P' :: nil) \/ C = nil.
Proof.
  intros * H; induction H; intros Hchain Hg; simpl in *;
    try contradiction;
    eauto using pure_chain_to_open_rec.
  -
    exfalso.
    match goal with
    | HgA : guarded_pskl ?A, Hne : ?A <> pskl_var_f _ |- _ =>
        destruct HgA; simpl in *; [ contradiction | congruence | contradiction ]
    end.
  -
    exfalso. destruct Hg as [ Hg | Hg ]; [ inversion Hg | discriminate ].
Qed.

Lemma e_solve_sub_ghost_hnall : forall S0 Θ m Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ pskl_ghost ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
  (guarded_pskl Q \/ Q = pskl_ghost) ->
  hnall_pskl P' = 0.
Proof.
  intros * H Hg; inversion H; subst; simpl in *; try reflexivity;

    try solve [ match goal with
                | Hga : guarded_pskl pskl_ghost |- _ => inversion Hga
                end ];

    try solve [ exfalso; destruct Hg as [ Hg | Hg ];
                [ inversion Hg | discriminate ] ].

  apply guarded_pskl_hnall; assumption.
Qed.

Lemma e_guess_mono_hnall : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> hnall_ptyp A <= hnall_pskl P.
Proof.
  intros * H; induction H; simpl in *; try lia.
  rewrite hnall_ptyp_close. rewrite hnall_pskl_open in IHe_guess_mono. lia.
Qed.

Lemma e_guess_hnall : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> hnall_pskl Q' <= hnall_pskl Q.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ]; [ lia | ].
  rewrite hnall_ptyp_to_pskl. apply (e_guess_mono_hnall Hg).
Qed.

Theorem e_extract_pure_chain_hnall : forall S0 Θ0 NM α m P P' S1 Ξ Q',
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q' }}e ->
  pure_chain_to α P ->
  (guarded_pskl P' \/ P' = pskl_ghost) ->
  hnall_pskl Q' = 0.
Proof.
  intros * H Hchain Hg; destruct H.
  match goal with
  | Hl : e_looksub _ _ _ _ _ _ _ _ ?C |- _ =>
      destruct (e_looksub_pure_chain_cstrs Hl Hchain Hg); subst C
  end;
  match goal with
  | Hc : e_solve_cstr _ _ _ _ _ _ _ |- _ => inversion Hc; subst
  end;
  match goal with
  | Hgs : e_guess _ _ ?Q _ _ _ |- _ =>
      pose proof (e_guess_hnall Hgs);
      assert (hnall_pskl Q = 0)
        by (solve [ eapply e_solve_sub_ghost_hnall; eassumption
                  | reflexivity ]);
      lia
  end.
Qed.

Theorem e_extract_forall_l_hnall : forall S0 Θ0 NM α M P P0 S1 Ξ P1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α))
     ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}e ->
  (guarded_pskl P0 \/ P0 = pskl_ghost) ->
  hnall_pskl (open_pskl_wrt_pskl P P1) < hnall_pskl (pskl_all_syn P).
Proof.
  intros * Hx Hg. simpl.
  rewrite hnall_pskl_open_graft.
  destruct (chain_hits_pskl 0 P) eqn:Hhit; [ | lia ].
  pose proof (@chain_hits_open_pure_chain P α 0 Hhit) as Hpure.
  rewrite (e_extract_pure_chain_hnall Hx Hpure Hg).
  lia.
Qed.

Lemma e_guess_mono_lc : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> lc_ptyp A.
Proof.
  intros * H; induction H;
    try solve [ assumption | constructor; auto ].

  match goal with
  | |- lc_ptyp (ptyp_all (close_ptyp_wrt_ptyp ?b _)) =>
      apply (lc_ptyp_all_exists b);
      rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp; assumption
  end.
Qed.

Corollary e_guess_mono_lc_pskl : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> lc_pskl (ptyp_to_pskl A).
Proof. intros. apply ptyp_to_pskl_lc. eauto using e_guess_mono_lc. Qed.

Definition lc_a_cstr (c : a_cstr) : Prop :=
  match c with
  | a_cstr_sub _ P => lc_pskl P
  | a_cstr_eq P    => lc_pskl P
  end.

Lemma e_looksub_lookeq_cstrs_lc :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     lc_pskl P -> lc_pskl P' -> Forall lc_a_cstr C) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     lc_pskl P -> lc_pskl P' -> Forall lc_a_cstr C).
Proof.
  apply e_looksub_lookeq_mutind;
    intros;
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_univ_ghost _) |- _ => apply lc_pskl_univ_ghost_inv in H
    end;

    try solve [ repeat (constructor; simpl; auto) ];

    try solve [ rewrite Forall_app; split;
                eauto using lc_pskl_all_syn_inv, lc_pskl_univ_ghost ];

    try solve [ eauto using lc_pskl_all_syn_inv, lc_pskl_univ_ghost ].
Qed.

Corollary e_looksub_cstrs_lc : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  lc_pskl P -> lc_pskl P' -> Forall lc_a_cstr C.
Proof. intros. eapply (proj1 e_looksub_lookeq_cstrs_lc); eassumption. Qed.

Lemma e_solve_sub_eq_lc :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     lc_pskl P -> lc_pskl Q -> lc_pskl P') /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     lc_pskl P -> lc_pskl Q -> lc_pskl P').
Proof.
  apply e_solve_sub_eq_mutind;
    intros;

    try solve [ eapply e_guess_mono_lc_pskl; eassumption ];
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_univ_ghost _) |- _ => apply lc_pskl_univ_ghost_inv in H
    | H : guarded_pskl _           |- _ => apply guarded_pskl_lc in H
    end;
    try solve
      [ assumption
      | eauto
      | constructor; eauto
      | apply lc_pskl_univ_ghost; eauto
      | apply lc_pskl_univ_ghost; constructor; eauto ];
    try match goal with
    | |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl
    end;
    match goal with
    | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
        apply IH;
        eauto using lc_pskl_all_syn_inv, lc_pskl_univ_ghost
    end.
Qed.

Corollary e_solve_sub_lc : forall S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
  lc_pskl P -> lc_pskl Q -> lc_pskl P'.
Proof. intros. eapply (proj1 e_solve_sub_eq_lc); eassumption. Qed.

Corollary e_solve_eq_lc : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
  lc_pskl P -> lc_pskl Q -> lc_pskl P'.
Proof. intros. eapply (proj2 e_solve_sub_eq_lc); eassumption. Qed.

Lemma e_solve_cstr_lc : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  lc_pskl P -> Forall lc_a_cstr C -> lc_pskl Q.
Proof.
  intros * H; induction H; intros Hlc HC;
    try match goal with
        | HC0 : Forall lc_a_cstr (_ :: _) |- _ =>
            inversion HC0; subst; simpl in *
        end;
    eauto using e_solve_sub_lc, e_solve_eq_lc.
Qed.

Lemma e_lookeq_order_total_n : forall n S0 Θ α P P',
  size_pskl P + size_pskl P' <= n ->
  e_lookeq_order S0 Θ α P P'.
Proof.
  induction n; intros * Hsz;
    [ pose proof (size_pskl_min P); pose proof (size_pskl_min P'); lia | ].
  constructor; intros; subst; simpl in Hsz;
    repeat match goal with |- _ /\ _ => split end; intros;
    apply IHn; repeat rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia.
Qed.

Theorem e_lookeq_order_total : forall S0 Θ α P P',
  e_lookeq_order S0 Θ α P P'.
Proof. intros. eapply e_lookeq_order_total_n. apply le_n. Qed.

Lemma e_looksub_order_total_n : forall n S0 Θ α m P P',
  size_pskl P + size_pskl P' <= n ->
  e_looksub_order S0 Θ α m P P'.
Proof.
  induction n; intros * Hsz;
    [ pose proof (size_pskl_min P); pose proof (size_pskl_min P'); lia | ].
  constructor; intros; subst; simpl in Hsz;
    repeat match goal with |- _ /\ _ => split end; intros;
    try apply e_lookeq_order_total;
    apply IHn; repeat rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia.
Qed.

Theorem e_looksub_order_total : forall S0 Θ α m P P',
  e_looksub_order S0 Θ α m P P'.
Proof. intros. eapply e_looksub_order_total_n. apply le_n. Qed.

Lemma e_solve_eq_order_total_n : forall n S0 Θ P Q,
  size_pskl P + size_pskl Q <= n ->
  lc_pskl P ->
  e_solve_eq_order S0 Θ P Q.
Proof.
  induction n; intros * Hsz Hlc;
    [ pose proof (size_pskl_min P); pose proof (size_pskl_min Q); lia | ].
  constructor; intros; subst; simpl in Hsz;
    try solve [ apply e_guess_mono_order_total; assumption ];
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_univ_ghost _) |- _ => apply lc_pskl_univ_ghost_inv in H
    end;
    repeat match goal with |- _ /\ _ => split end; intros;
    (apply IHn;
     [ repeat rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia
     | eauto using lc_pskl_all_syn_inv, lc_pskl_univ_ghost ]).
Qed.

Theorem e_solve_eq_order_total : forall S0 Θ P Q,
  lc_pskl P -> e_solve_eq_order S0 Θ P Q.
Proof. intros. eapply e_solve_eq_order_total_n; [ apply le_n | assumption ]. Qed.

Lemma e_solve_sub_order_total_n : forall n S0 Θ m P Q,
  size_pskl P + size_pskl Q <= n ->
  lc_pskl P ->
  e_solve_sub_order S0 Θ m P Q.
Proof.
  induction n; intros * Hsz Hlc;
    [ pose proof (size_pskl_min P); pose proof (size_pskl_min Q); lia | ].
  constructor; intros; subst; simpl in Hsz;

    try solve [ apply e_solve_eq_order_total; assumption ];
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_univ_ghost _) |- _ => apply lc_pskl_univ_ghost_inv in H
    end;
    repeat match goal with |- _ /\ _ => split end; intros;

    try solve [ apply e_solve_eq_order_total;
                solve [ assumption | constructor ] ];
    (apply IHn;
     [ repeat rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia
     | eauto using lc_pskl_all_syn_inv, lc_pskl_univ_ghost;
       try solve [ constructor ] ]).
Qed.

Theorem e_solve_sub_order_total : forall S0 Θ m P Q,
  lc_pskl P -> e_solve_sub_order S0 Θ m P Q.
Proof. intros. eapply e_solve_sub_order_total_n; [ apply le_n | assumption ]. Qed.

Theorem e_solve_cstr_order_total : forall C S0 Θ P,
  lc_pskl P -> Forall lc_a_cstr C -> e_solve_cstr_order S0 Θ C P.
Proof.
  induction C as [ | c C' IH ]; intros * Hlc HC; constructor; intros;
    match goal with
    | Heq : nil = _ :: _ |- _ => discriminate Heq
    | Heq : _ :: _ = _ :: _ |- _ =>
        inversion Heq; subst; inversion HC; subst; simpl in *
    end.
  -
    apply e_solve_sub_order_total; assumption.
  -
    split; [ apply e_solve_eq_order_total; assumption | intros ].
    apply IH; [ eapply e_solve_eq_lc; eauto | assumption ].
Qed.

Theorem e_guess_order_total : forall S0 NM Q,
  lc_pskl Q -> e_guess_order S0 NM Q.
Proof.
  intros; constructor; intros _; apply e_guess_mono_order_total; assumption.
Qed.

Theorem e_extract_order_total : forall S0 Θ0 NM α m P P',
  lc_pskl P -> lc_pskl P' -> e_extract_order S0 Θ0 NM α m P P'.
Proof.
  intros; constructor.
  - apply e_looksub_order_total.
  - intros. apply e_solve_cstr_order_total;
      [ constructor | eapply e_looksub_cstrs_lc; eassumption ].
  - intros. apply e_guess_order_total.
    eapply e_solve_cstr_lc;
      [ eassumption | constructor | eapply e_looksub_cstrs_lc; eassumption ].
Qed.

Fixpoint fnd_mode (M : mode) : nat :=
  match M with
  | mode_fn M' => 1 + fnd_mode M'
  | _          => 0
  end.

Fixpoint ndef_aenv (Θ : aenv) : nat :=
  match Θ with
  | nil                                => 0
  | (_, abind_flex_mono_def _) :: Θ'   => 1 + ndef_aenv Θ'
  | _ :: Θ'                            => ndef_aenv Θ'
  end.

Lemma ndef_aenv_app : forall Θ1 Θ2,
  ndef_aenv (Θ1 ++ Θ2) = ndef_aenv Θ1 + ndef_aenv Θ2.
Proof.
  induction Θ1 as [ | [x b] Θ1' IH ]; intros; simpl; [ auto | ].
  destruct b; rewrite IH; lia.
Qed.

Definition entry_def_mono (xb : atom * abind) : Prop :=
  match snd xb with
  | abind_flex_mono_def τ => mono_ptyp τ
  | _                     => True
  end.

Notation aenv_defs_mono := (Forall entry_def_mono).

Lemma entry_def_mono_flex : forall α, entry_def_mono (α, abind_flex_mono).
Proof. intros; exact I. Qed.

Lemma entry_def_mono_tvar : forall α, entry_def_mono (α, abind_tvar).
Proof. intros; exact I. Qed.

Lemma entry_def_mono_var_typ : forall x A, entry_def_mono (x, abind_var_typ A).
Proof. intros; exact I. Qed.

Lemma entry_def_mono_var_skl : forall x Q, entry_def_mono (x, abind_var_skl Q).
Proof. intros; exact I. Qed.

Lemma entry_def_mono_def : forall α τ,
  mono_ptyp τ -> entry_def_mono (α, abind_flex_mono_def τ).
Proof. intros; exact H. Qed.

Lemma aenv_defs_mono_cons_inv : forall x b (Θ : aenv),
  aenv_defs_mono ((x ~ b) ++ Θ) ->
  entry_def_mono (x, b) /\ aenv_defs_mono Θ.
Proof. intros * HF. inversion HF; subst. split; assumption. Qed.

Lemma Forall_app_intro : forall (X : Type) (Pr : X -> Prop) l1 l2,
  Forall Pr l1 -> Forall Pr l2 -> Forall Pr (l1 ++ l2).
Proof. intros; apply Forall_app; split; assumption. Qed.

Lemma all_flex_mono_ndef : forall Ξ, all_flex_mono Ξ -> ndef_aenv Ξ = 0.
Proof.
  unfold all_flex_mono; induction 1 as [ | [x b] Ξ' Hb _ IH ];
    simpl in *; subst; auto.
Qed.

Lemma all_flex_mono_defs_mono : forall Ξ, all_flex_mono Ξ -> aenv_defs_mono Ξ.
Proof.
  unfold all_flex_mono; induction 1 as [ | [x b] Ξ' Hb _ IH ];
    constructor; simpl in *; subst; auto using entry_def_mono_flex.
Qed.

Lemma e_guess_mono_block_flex : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> all_flex_mono Ξ.
Proof.
  intros * H; induction H;
    try solve [ repeat constructor ];
    try solve [ apply all_flex_mono_app; assumption ];
    assumption.
Qed.

Lemma e_guess_block_flex : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> all_flex_mono Ξ.
Proof.
  intros * H; destruct H; [ constructor | ].
  eauto using e_guess_mono_block_flex.
Qed.

Lemma e_looksub_lookeq_block_flex :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> all_flex_mono Ξ) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> all_flex_mono Ξ).
Proof.
  apply e_looksub_lookeq_mutind;
    intros;
    try solve [ repeat constructor ];
    try solve [ apply all_flex_mono_app; assumption ];
    assumption.
Qed.

Lemma e_solve_sub_eq_block_flex :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e -> all_flex_mono Ξ) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> all_flex_mono Ξ).
Proof.
  apply e_solve_sub_eq_mutind;
    intros;
    try solve [ repeat constructor ];
    try solve [ apply all_flex_mono_app; assumption ];
    eauto using e_guess_mono_block_flex.
Qed.

Lemma e_solve_cstr_block_flex : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e -> all_flex_mono Ξ.
Proof.
  intros * H; induction H;
    eauto using all_flex_mono_app, (proj1 e_solve_sub_eq_block_flex),
      (proj2 e_solve_sub_eq_block_flex).
  constructor.
Qed.

Lemma e_extract_block_flex : forall S0 Θ0 NM α m P P' S1 Ξ Q',
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q' }}e ->
  all_flex_mono Ξ.
Proof.
  intros * H; destruct H.
  repeat apply all_flex_mono_app;
    eauto using (proj1 e_looksub_lookeq_block_flex),
      e_solve_cstr_block_flex, e_guess_block_flex.
Qed.

Lemma mono_ptyp_nall : forall τ, mono_ptyp τ -> nall_ptyp τ = 0.
Proof. induction 1; simpl; lia. Qed.

Lemma mono_pskl_nall : forall τ,
  mono_ptyp τ -> nall_pskl (ptyp_to_pskl τ) = 0.
Proof. intros. rewrite nall_ptyp_to_pskl. auto using mono_ptyp_nall. Qed.

Lemma nall_pskl_subst_nallfree : forall P Q β,
  nall_pskl Q = 0 ->
  nall_pskl (subst_pskl_in_pskl Q β P) = nall_pskl P.
Proof.
  induction P; intros * Hz; simpl;
    try (match goal with |- context [ if ?c then _ else _ ] => destruct c end);
    repeat match goal with
    | IH : context [ subst_pskl_in_pskl ] |- _ => rewrite IH by assumption
    end;
    simpl; lia.
Qed.

Lemma e_assign_unify_consis_defs_mono :
  (forall S0 Θ Ξ α P S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e ->
     aenv_defs_mono Θ -> aenv_defs_mono Ξ -> aenv_defs_mono Θ') /\
  (forall S0 Θ α β S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e ->
     aenv_defs_mono Θ -> aenv_defs_mono Θ') /\
  (forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
     aenv_defs_mono Θ -> aenv_defs_mono Θ').
Proof.
  apply e_assign_unify_consis_mutind;
    intros;
    simpl in *;

    repeat match goal with
    | H : Forall entry_def_mono (_ ++ _) |- _ =>
        apply Forall_app in H; destruct H
    | H : Forall entry_def_mono (_ :: _) |- _ =>
        inversion H; subst; clear H
    end;
    repeat match goal with
    | IH : Forall entry_def_mono ?Θin -> Forall entry_def_mono (_ :: _)
      |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(eauto using Forall_app_intro,
                                 entry_def_mono_tvar));
        inversion HH; subst; clear IH HH
    end;
    eauto 8 using Forall_app_intro, Forall_cons, Forall_nil,
      entry_def_mono_flex, entry_def_mono_tvar, entry_def_mono_def,
      entry_def_mono_var_typ, entry_def_mono_var_skl,
      all_flex_mono_defs_mono, e_guess_mono_block_flex,
      mono_ptyp__var.
Qed.

Corollary e_consis_defs_mono : forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
  {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
  aenv_defs_mono Θ -> aenv_defs_mono Θ'.
Proof.
  intros. eapply (proj2 (proj2 e_assign_unify_consis_defs_mono)); eassumption.
Qed.

Lemma e_guess_lc : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> lc_pskl Q -> lc_pskl Q'.
Proof.
  intros * H Hlc; destruct H; eauto using e_guess_mono_lc_pskl.
Qed.

Lemma e_extract_lc : forall S0 Θ0 NM α m P P' S1 Ξ Q',
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q' }}e ->
  lc_pskl P -> lc_pskl P' -> lc_pskl Q'.
Proof.
  intros * H HP HP'; destruct H.
  eapply e_guess_lc; [ eassumption | ].
  eapply e_solve_cstr_lc;
    [ eassumption | constructor | eapply e_looksub_cstrs_lc; eassumption ].
Qed.

Fixpoint nholes_pskl (P : pskl) : nat :=
  match P with
  | pskl_ghost        => 1
  | pskl_arrow P1 P2 => nholes_pskl P1 + nholes_pskl P2
  | pskl_all_syn P1  => nholes_pskl P1
  | pskl_univ_ghost P1  => nholes_pskl P1
  | _                => 0
  end.

Fixpoint nundef_aenv (Θ : aenv) : nat :=
  match Θ with
  | nil                            => 0
  | (_, abind_flex_mono) :: Θ'     => 1 + nundef_aenv Θ'
  | _ :: Θ'                        => nundef_aenv Θ'
  end.

Lemma nundef_aenv_app : forall Θ1 Θ2,
  nundef_aenv (Θ1 ++ Θ2) = nundef_aenv Θ1 + nundef_aenv Θ2.
Proof.
  induction Θ1 as [ | [x b] Θ1' IH ]; intros; simpl; [ auto | ].
  destruct b; rewrite IH; lia.
Qed.

Lemma nholes_ptyp_to_pskl : forall A, nholes_pskl (ptyp_to_pskl A) = 0.
Proof. induction A; simpl; lia. Qed.

Lemma nholes_pskl_open_rec_var : forall P β k,
  nholes_pskl (open_pskl_wrt_pskl_rec k (pskl_var_f β) P) = nholes_pskl P.
Proof.
  induction P; intros β k; simpl;
    try reflexivity;
    try (match goal with
         | |- context [ lt_eq_lt_dec ?a ?b ] =>
             destruct (lt_eq_lt_dec a b) as [[?|?]|?]
         end; reflexivity);
    first [ solve [ auto ] | f_equal; auto ].
Qed.

Corollary nholes_pskl_open : forall P β,
  nholes_pskl (open_pskl_wrt_pskl P (pskl_var_f β)) = nholes_pskl P.
Proof. intros. apply nholes_pskl_open_rec_var. Qed.

Lemma nholes_pskl_subst_ghostfree : forall P Q β,
  nholes_pskl Q = 0 ->
  nholes_pskl (subst_pskl_in_pskl Q β P) = nholes_pskl P.
Proof.
  induction P; intros * Hz; simpl;
    try (match goal with |- context [ if ?c then _ else _ ] => destruct c end);
    repeat match goal with
    | IH : context [ subst_pskl_in_pskl ] |- _ => rewrite IH by assumption
    end;
    simpl; lia.
Qed.

Lemma e_guess_mono_block_nundef : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> nundef_aenv Ξ = nholes_pskl P.
Proof.
  intros * H; induction H; simpl;
    repeat rewrite nundef_aenv_app;
    repeat rewrite nholes_pskl_open in *;
    lia.
Qed.

Lemma e_assign_unify_consis_ndef_mono :
  (forall S0 Θ Ξ α P S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e ->
     ndef_aenv Ξ + ndef_aenv Θ <= ndef_aenv Θ') /\
  (forall S0 Θ α β S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e ->
     ndef_aenv Θ <= ndef_aenv Θ') /\
  (forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
     ndef_aenv Θ <= ndef_aenv Θ').
Proof.
  apply e_assign_unify_consis_mutind;
    intros; simpl in *;
    repeat rewrite ndef_aenv_app in *; simpl in *;

    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    end; subst; simpl in *;
    lia.
Qed.

Corollary e_consis_ndef_mono : forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
  {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
  ndef_aenv Θ <= ndef_aenv Θ'.
Proof.
  intros. eapply (proj2 (proj2 e_assign_unify_consis_ndef_mono)); eassumption.
Qed.

Lemma e_assign_unify_consis_wpres :
  (forall S0 Θ Ξ α P S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e ->
     nundef_aenv Θ' + ndef_aenv Θ'
     <= nundef_aenv (Ξ ++ Θ) + ndef_aenv (Ξ ++ Θ) + nholes_pskl P) /\
  (forall S0 Θ α β S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e ->
     nundef_aenv Θ' + ndef_aenv Θ' <= nundef_aenv Θ + ndef_aenv Θ) /\
  (forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
     nundef_aenv Θ' + ndef_aenv Θ'
     <= nundef_aenv Θ + ndef_aenv Θ + nholes_pskl P0 + nholes_pskl P).
Proof.
  apply e_assign_unify_consis_mutind;
    intros; simpl in *;

    repeat match goal with
    | Hg : e_guess_mono _ _ _ _ _ |- _ =>
        pose proof (e_guess_mono_block_nundef Hg);
        pose proof (all_flex_mono_ndef (e_guess_mono_block_flex Hg));
        clear Hg
    end;
    repeat match goal with
    | H : context [ nholes_pskl (if ?c then _ else _) ] |- _ => destruct c
    | |- context [ nholes_pskl (if ?c then _ else _) ] => destruct c
    end;

    repeat rewrite nholes_pskl_subst_ghostfree in *
      by (auto using nholes_ptyp_to_pskl);
    repeat rewrite nholes_ptyp_to_pskl in *;
    repeat rewrite nholes_pskl_open in *;
    repeat rewrite nundef_aenv_app in *;
    repeat rewrite ndef_aenv_app in *;
    simpl in *;

    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    end; subst; simpl in *;
    lia.
Qed.

Corollary e_consis_wpres : forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
  {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
  nundef_aenv Θ' + ndef_aenv Θ'
  <= nundef_aenv Θ + ndef_aenv Θ + nholes_pskl P0 + nholes_pskl P.
Proof.
  intros. eapply (proj2 (proj2 e_assign_unify_consis_wpres)); eassumption.
Qed.

Lemma e_consis_block_order_total_n :
  forall n1 n2,
  (forall n4 S Θ α β,
     nundef_aenv Θ <= n1 ->
     ndef_aenv Θ <= n2 ->
     length Θ <= n4 ->
     aenv_defs_mono Θ ->
     e_unify_order S Θ α β) /\
  (forall n4 S Θ Ξ α P,
     nholes_pskl P + nundef_aenv (Ξ ++ Θ) <= n1 ->
     ndef_aenv (Ξ ++ Θ) <= n2 ->
     length Θ <= n4 ->
     lc_pskl P -> aenv_defs_mono (Ξ ++ Θ) ->
     e_assign_order S Θ Ξ α P) /\
  (forall n3 Δ1 Δ2 S Θ P0 P,
     nholes_pskl P0 + nholes_pskl P + nundef_aenv Θ <= n1 ->
     ndef_aenv Θ <= n2 ->
     size_pskl P0 + size_pskl P <= n3 ->
     lc_pskl P0 -> lc_pskl P -> aenv_defs_mono Θ ->
     e_consis_order Δ1 Δ2 S Θ P0 P).
Proof.
  intros n1; induction n1 as [n1 IH1] using lt_wf_ind;
    intros n2; induction n2 as [n2 IH2] using lt_wf_ind.

  assert (Huni : forall n4 S Θ α β,
             nundef_aenv Θ <= n1 -> ndef_aenv Θ <= n2 -> length Θ <= n4 ->
             aenv_defs_mono Θ ->
             e_unify_order S Θ α β).
  { intros n4; induction n4 as [n4 IH4] using lt_wf_ind;
      intros * Hw Hnd Hlen Hdm.
    constructor; intros; subst; simpl in *;
      repeat match goal with
      | H : Forall entry_def_mono (_ :: _) |- _ =>
          inversion H; subst; clear H
      end.
    -
      match goal with
      | He : entry_def_mono (_, abind_flex_mono_def _) |- _ =>
          unfold entry_def_mono in He; simpl in He
      end.
      unshelve eapply (proj2 (proj2 (IH2 (ndef_aenv Θ0) ltac:(lia)))
                         (size_pskl _ + size_pskl _));
        try apply le_n;
        try assumption;
        try solve [ repeat rewrite nholes_ptyp_to_pskl; simpl; lia ];
        try solve [ apply ptyp_to_pskl_lc;
                    match goal with
                    | |- context [ if ?c then _ else _ ] => destruct c
                    end;
                    auto using mono_ptyp_lc; constructor ].
    -
      apply (IH4 (length Θ0)); try assumption; try lia.
    -
      apply (IH4 (length Θ0)); try assumption; try lia.
    -
      apply (IH4 (length Θ0)); try assumption; try lia.
    -
      apply (IH4 (length Θ0)); try assumption; try lia. }

  assert (Hass : forall n4 S Θ Ξ α P,
             nholes_pskl P + nundef_aenv (Ξ ++ Θ) <= n1 ->
             ndef_aenv (Ξ ++ Θ) <= n2 ->
             length Θ <= n4 ->
             lc_pskl P -> aenv_defs_mono (Ξ ++ Θ) ->
             e_assign_order S Θ Ξ α P).
  { intros n4; induction n4 as [n4 IH4] using lt_wf_ind;
      intros * Hw Hnd Hlen Hlc Hdm.
    constructor; intros; subst; simpl in *;
      repeat rewrite nundef_aenv_app in Hw; simpl in Hw;
      repeat rewrite ndef_aenv_app in Hnd; simpl in Hnd;
      repeat match goal with
      | H : Forall entry_def_mono (_ ++ _) |- _ =>
          apply Forall_app in H; destruct H
      | H : Forall entry_def_mono (_ :: _) |- _ =>
          inversion H; subst; clear H
      end.
    -
      apply e_guess_mono_order_total; assumption.
    -
      match goal with
      | He : entry_def_mono (_, abind_flex_mono_def _) |- _ =>
          unfold entry_def_mono in He; simpl in He
      end.
      unshelve eapply (proj2 (proj2 (IH2 (ndef_aenv (Ξ ++ Θ0))
                                       ltac:(rewrite ndef_aenv_app; lia)))
                         (size_pskl _ + size_pskl _));
        try apply le_n;
        try assumption;

        try solve [ rewrite nholes_pskl_subst_ghostfree
                      by auto using nholes_ptyp_to_pskl;
                    repeat match goal with
                    | |- context [ nholes_pskl (if ?c then _ else _) ] =>
                        destruct c
                    end;
                    repeat rewrite nholes_ptyp_to_pskl;
                    rewrite nundef_aenv_app; simpl; lia ];

        try solve [ rewrite ndef_aenv_app; apply le_n ];

        try solve [ match goal with
                    | |- lc_pskl (if ?c then _ else _) => destruct c
                    end;
                    auto using ptyp_to_pskl_lc, mono_ptyp_lc;
                    constructor ];
        try solve [ apply subst_pskl_in_pskl_lc_pskl;
                    auto using ptyp_to_pskl_lc, mono_ptyp_lc ];
        auto using Forall_app_intro.
    -
      split;
        (apply (IH4 (length Θ0)); [ lia | .. ];
         try assumption;
         repeat rewrite nundef_aenv_app; repeat rewrite ndef_aenv_app;
         simpl; try lia;
         repeat apply Forall_app_intro;
         eauto using Forall_cons, Forall_nil, entry_def_mono_flex).
    -
      apply (IH4 (length Θ0)); [ lia | .. ];
        try assumption;
        repeat rewrite nundef_aenv_app; repeat rewrite ndef_aenv_app;
        simpl; try lia;
        auto using Forall_app_intro.
    -
      apply (IH4 (length Θ0)); [ lia | .. ];
        try assumption;
        repeat rewrite nundef_aenv_app; repeat rewrite ndef_aenv_app;
        simpl; try lia;
        auto using Forall_app_intro.
    -
      apply (IH4 (length Θ0)); [ lia | .. ];
        try assumption;
        repeat rewrite nundef_aenv_app; repeat rewrite ndef_aenv_app;
        simpl; try lia;
        auto using Forall_app_intro. }
  split; [ exact Huni | split; [ exact Hass | ] ].

  intros n3; induction n3 as [n3 IH3] using lt_wf_ind;
    intros * Hw Hnd Hsz Hlc0 Hlc Hdm.
  constructor; intros; subst; simpl in Hw, Hsz.
  -
    repeat match goal with
    | Hl : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in Hl; destruct Hl
    end.
    split.
    + unshelve eapply (IH3 (size_pskl P0a + size_pskl P1) ltac:(lia));
        try apply le_n; try assumption; lia.
    + intros * Hc1.
      pose proof (e_consis_wpres Hc1) as Hwp.
      pose proof (e_consis_ndef_mono Hc1) as Hmono.
      pose proof (e_consis_defs_mono Hc1 Hdm) as Hdm1.
      destruct (lt_eq_lt_dec (ndef_aenv Θ) (ndef_aenv Θ1)) as [[Hlt|Heq]|Hgt];
        [ | | lia ].
      *
        unshelve eapply (proj2 (proj2 (IH1 (nholes_pskl P0b + nholes_pskl P2
                                            + nundef_aenv Θ1)
                                         ltac:(lia)
                                         (ndef_aenv Θ1)))
                           (size_pskl P0b + size_pskl P2));
          try apply le_n; try assumption.
      *
        unshelve eapply (IH3 (size_pskl P0b + size_pskl P2) ltac:(lia));
          try apply le_n; try assumption; lia.
  -
    unshelve eapply (IH3 (size_pskl (open_pskl_wrt_pskl P0'
                                       (pskl_var_f (supply_fresh S)))
                          + size_pskl (open_pskl_wrt_pskl P1
                                         (pskl_var_f (supply_fresh S))))
                       ltac:(repeat rewrite size_pskl_open_pskl_wrt_pskl_var;
                             lia));
      try apply le_n; try assumption;
      try solve [ repeat rewrite nholes_pskl_open; simpl; lia ];
      try solve [ simpl; lia ];
      try solve [ eauto using lc_pskl_all_syn_inv ];
      try solve [ constructor; [ apply entry_def_mono_tvar | assumption ] ].
  -
    unshelve eapply (IH3 (size_pskl (pskl_univ_ghost P0')
                          + size_pskl (open_pskl_wrt_pskl P1
                                         (pskl_var_f (supply_fresh S))))
                       ltac:(simpl;
                             repeat rewrite size_pskl_open_pskl_wrt_pskl_var;
                             lia));
      try apply le_n; try assumption;
      try solve [ simpl; repeat rewrite nholes_pskl_open; simpl; lia ];
      try solve [ simpl; lia ];
      try solve [ eauto using lc_pskl_all_syn_inv ];
      try solve [ constructor; [ apply entry_def_mono_tvar | assumption ] ].
  -
    unshelve eapply (IH3 (size_pskl P0' + size_pskl P1) ltac:(simpl in *; lia));
      try apply le_n; try assumption;
      try solve [ simpl in *; lia ];
      eauto using lc_pskl_univ_ghost_inv.
  -
    unshelve eapply (IH3 (size_pskl (open_pskl_wrt_pskl P0'
                                       (pskl_var_f (supply_fresh S)))
                          + size_pskl (pskl_univ_ghost P1))
                       ltac:(simpl;
                             repeat rewrite size_pskl_open_pskl_wrt_pskl_var;
                             lia));
      try apply le_n; try assumption;
      try solve [ simpl; repeat rewrite nholes_pskl_open; simpl; lia ];
      try solve [ simpl; lia ];
      try solve [ eauto using lc_pskl_all_syn_inv ];
      try solve [ constructor; [ apply entry_def_mono_tvar | assumption ] ].
  -
    unshelve eapply (IH3 (size_pskl P0 + size_pskl P1) ltac:(simpl in *; lia));
      try apply le_n; try assumption;
      try solve [ simpl in *; lia ];
      eauto using lc_pskl_univ_ghost_inv.
  -
    unshelve eapply (IH3 (size_pskl P0' + size_pskl P) ltac:(simpl in *; lia));
      try apply le_n; try assumption;
      try solve [ simpl in *; lia ];
      eauto using lc_pskl_univ_ghost_inv.
  -
    apply (Huni (length Θ)); try apply le_n; try assumption; simpl in *; lia.
  -
    apply (Hass (length Θ)); simpl; try apply le_n; try assumption; lia.
  -
    apply (Hass (length Θ)); simpl; try apply le_n; try assumption; lia.
Qed.

Theorem e_consis_order_total : forall Δ1 Δ2 S Θ P0 P,
  lc_pskl P0 -> lc_pskl P -> aenv_defs_mono Θ ->
  e_consis_order Δ1 Δ2 S Θ P0 P.
Proof.
  intros.
  unshelve eapply (proj2 (proj2 (e_consis_block_order_total_n
                                   (nholes_pskl P0 + nholes_pskl P
                                    + nundef_aenv Θ)
                                   (ndef_aenv Θ)))
                     (size_pskl P0 + size_pskl P));
    try apply le_n; assumption.
Qed.

Lemma e_sub_order_total_n :
  (forall Δ1 Δ2 S Θ P0 P,
     lc_pskl P0 -> lc_pskl P -> aenv_defs_mono Θ ->
     e_consis_order Δ1 Δ2 S Θ P0 P) ->
  forall n1 n2 n4,
  (forall n3 n5 S0 NM M P0 Θ0 P,
     fnd_mode M <= n1 ->
     nall_pskl P0 <= n2 ->
     ndef_aenv Θ0 <= n4 ->
     hnall_pskl P <= n3 ->
     size_pskl P <= n5 ->
     lc_pskl P -> lc_pskl P0 -> aenv_defs_mono Θ0 ->
     e_sub_order S0 NM M P0 Θ0 P)
  /\
  (forall n6 S0 NM M P0 Θ0 Ξ α,
     fnd_mode (mode_fn M) <= n1 ->
     nall_pskl P0 <= n2 ->
     ndef_aenv (Ξ ++ Θ0) <= n4 ->
     length Θ0 <= n6 ->
     lc_pskl P0 -> aenv_defs_mono (Ξ ++ Θ0) ->
     e_sub_flex_order S0 NM M P0 Θ0 Ξ α).
Proof.
  intros Hco n1; induction n1 as [n1 IH1] using lt_wf_ind;
    intros n2; induction n2 as [n2 IH2] using lt_wf_ind;
    intros n4; induction n4 as [n4 IH4] using lt_wf_ind.

  assert (Hpsi : forall n6 S0 NM M P0 Θ0 Ξ α,
             fnd_mode (mode_fn M) <= n1 ->
             nall_pskl P0 <= n2 ->
             ndef_aenv (Ξ ++ Θ0) <= n4 ->
             length Θ0 <= n6 ->
             lc_pskl P0 -> aenv_defs_mono (Ξ ++ Θ0) ->
             e_sub_flex_order S0 NM M P0 Θ0 Ξ α).
  { intros n6; induction n6 as [n6 IH6] using lt_wf_ind;
      intros * Hfnd Hnall Hndef Hlen Hlc0 Hdm.
    constructor; intros; subst;
      simpl in *;
      repeat rewrite ndef_aenv_app in Hndef; simpl in Hndef;
      repeat match goal with
      | H : Forall entry_def_mono (_ ++ _) |- _ =>
          apply Forall_app in H; destruct H
      | H : Forall entry_def_mono (_ :: _) |- _ =>
          inversion H; subst; clear H
      end.
    -
      constructor; intros; subst; try congruence.

      match goal with
      | Heq : mode_fn _ = mode_fn _ |- _ =>
          inversion Heq; subst; clear Heq
      end;
      match goal with
      | Heq : pskl_arrow _ _ = pskl_arrow _ _ |- _ =>
          inversion Heq; subst; clear Heq
      end.
      split.
      { apply Hco.
        - match goal with
          | Hl : lc_pskl (pskl_arrow _ _) |- _ =>
              apply lc_pskl_arrow_inv in Hl; destruct Hl; assumption
          end.
        - constructor.
        - repeat apply Forall_app_intro;
            eauto 10 using Forall_cons, Forall_nil, entry_def_mono_flex,
              entry_def_mono_def, mono_ptyp__arrow, mono_ptyp__var. }
      intros * Hcons.

      match goal with
      | |- e_sub_order _ _ ?Mg _ _ _ =>
          unshelve eapply (proj1 (IH1 (fnd_mode Mg)
                                    ltac:(simpl in Hfnd; lia)
                                    (nall_pskl _) (ndef_aenv _))
                             (hnall_pskl _) (size_pskl _))
      end;
        try apply le_n;
        try solve [ constructor ].
      +
        match goal with
        | Hl : lc_pskl (pskl_arrow _ _) |- _ =>
            apply lc_pskl_arrow_inv in Hl; destruct Hl; assumption
        end.
      +
        eapply e_consis_defs_mono; [ eassumption | ].
        repeat apply Forall_app_intro;
          eauto 10 using Forall_cons, Forall_nil, entry_def_mono_flex,
            entry_def_mono_def, mono_ptyp__arrow, mono_ptyp__var.
    -
      match goal with
      | He : entry_def_mono (_, abind_flex_mono_def _) |- _ =>
          unfold entry_def_mono in He; simpl in He
      end.
      unshelve eapply (proj1 (IH4 (ndef_aenv (Ξ ++ Θ0'))
                                ltac:(rewrite ndef_aenv_app in *; lia))
                         (hnall_pskl _) (size_pskl _));
        try apply le_n;
        try assumption;

        try solve [ rewrite nall_pskl_subst_nallfree
                      by auto using mono_pskl_nall; assumption ];
        try solve [ match goal with
                    | |- lc_pskl (if ?c then _ else _) => destruct c
                    end;
                    auto using ptyp_to_pskl_lc, mono_ptyp_lc;
                    constructor ];
        try solve [ apply subst_pskl_in_pskl_lc_pskl;
                    auto using ptyp_to_pskl_lc, mono_ptyp_lc;
                    constructor ];

        auto using Forall_app_intro.
    -
      split;
        (apply (IH6 (length Θ0')); [ lia | .. ];
         try assumption;
         repeat rewrite ndef_aenv_app; simpl;
         try lia;
         repeat apply Forall_app_intro;
         eauto using Forall_cons, Forall_nil, entry_def_mono_flex).
    -
      apply (IH6 (length Θ0')); [ lia | .. ];
        try assumption;
        repeat rewrite ndef_aenv_app; simpl;
        try lia;
        auto using Forall_app_intro.
    -
      apply (IH6 (length Θ0')); [ lia | .. ];
        try assumption;
        repeat rewrite ndef_aenv_app; simpl;
        try lia;
        auto using Forall_app_intro.
    -
      apply (IH6 (length Θ0')); [ lia | .. ];
        try assumption;
        repeat rewrite ndef_aenv_app; simpl;
        try lia;
        auto using Forall_app_intro. }
  split; [ | exact Hpsi ].

  intros n3; induction n3 as [n3 IH3] using lt_wf_ind;
    intros n5; induction n5 as [n5 IH5] using lt_wf_ind;
    intros * Hfnd Hnall Hndef Hh Hsz Hlc Hlc0 Hdm.
  constructor; intros; subst.
  -
    apply Hco; assumption.
  -
    simpl in Hnall.
    unshelve eapply (proj1 (IH2 (nall_pskl
                                   (open_pskl_wrt_pskl B
                                      (pskl_var_f (supply_fresh S0))))
                              ltac:(rewrite nall_pskl_open; lia)
                              (ndef_aenv _))
                       (hnall_pskl _) (size_pskl _));
      try apply le_n;
      try assumption.
    +
      eauto using lc_pskl_all_syn_inv.
    + constructor; [ apply entry_def_mono_tvar | assumption ].
  -
    apply (Hpsi (length Θ0));
      simpl; try assumption; try apply le_n.
  -
    split.
    { apply Hco;
        try solve [ match goal with
                    | Hl : lc_pskl (pskl_arrow _ _) |- _ =>
                        apply lc_pskl_arrow_inv in Hl; destruct Hl; assumption
                    end ];
        assumption. }
    intros * Hcons.
    repeat match goal with
    | Hl : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in Hl; destruct Hl
    end.
    match goal with
    | |- e_sub_order _ _ ?Mg _ _ _ =>
        unshelve eapply (proj1 (IH1 (fnd_mode Mg)
                                  ltac:(simpl in Hfnd; lia)
                                  (nall_pskl _) (ndef_aenv _))
                           (hnall_pskl _) (size_pskl _))
    end;
      try apply le_n;
      try assumption.
    eapply e_consis_defs_mono; eassumption.
  -
    match goal with
    | Hg : guarded_pskl _ \/ _ = pskl_ghost |- _ => idtac
    end.
    split.
    + apply e_extract_order_total;
        eauto using lc_pskl_all_syn_inv.
    + intros * Hxt Hwf.

      assert (Hlc1 : lc_pskl P1)
        by (eapply e_extract_lc;
            eauto using lc_pskl_all_syn_inv).
      unshelve eapply (IH3 (hnall_pskl (open_pskl_wrt_pskl Q P1))
                         ltac:(pose proof (@e_extract_forall_l_hnall
                                             (add (supply_fresh S0) S0)
                                             Θ0 NM (supply_fresh S0)
                                             M Q P0 S1 Ξ P1 Hxt
                                             ltac:(assumption));
                               lia)
                         (size_pskl _));
        try apply le_n;
        try assumption.
      *
        rewrite ndef_aenv_app.
        rewrite (all_flex_mono_ndef (e_extract_block_flex Hxt)).
        lia.
      *
        destruct (atom_fresh (ftvar_in_pskl Q)) as [x Hx].
        rewrite (subst_pskl_in_pskl_intro x) by assumption.
        apply subst_pskl_in_pskl_lc_pskl;
          eauto using lc_pskl_all_syn_inv.
      * apply Forall_app_intro;
          eauto using all_flex_mono_defs_mono, e_extract_block_flex.
  -
    simpl in Hh, Hsz.
    unshelve eapply (IH5 (size_pskl Q) ltac:(lia));
      try apply le_n;
      try assumption.
    eauto using lc_pskl_univ_ghost_inv.
Qed.

Theorem e_sub_order_total : forall S0 NM M P0 Θ0 P,
  lc_pskl P -> lc_pskl P0 -> aenv_defs_mono Θ0 ->
  e_sub_order S0 NM M P0 Θ0 P.
Proof.
  intros.
  unshelve eapply (proj1 (e_sub_order_total_n e_consis_order_total
                            (fnd_mode M) (nall_pskl P0) (ndef_aenv Θ0))
                     (hnall_pskl P) (size_pskl P));
    try apply le_n; assumption.
Qed.
