(** BASICS for the constraint-SOLVING layer ([a_solve_sub] / [a_solve_eq]),
    docs/DESIGN-subtyping.md §3.3(2).  These are the undecorated shadows of
    the decorated tag-solving ([a_solvetag_sub]/[a_solvetag_eq]); the
    subtyping-decoration lemmas invert [a_sub]'s Extract = look ∘ solve ∘ guess
    into a [solve]/[solvetag] pair, so [solve]'s outputs must be well-behaved.

    First: solving preserves local closure — a locally-closed problem has a
    locally-closed solution. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.

Set Implicit Arguments.

Scheme a_solve_sub_mutind := Induction for a_solve_sub Sort Prop
  with a_solve_eq_mutind  := Induction for a_solve_eq  Sort Prop.
Combined Scheme a_solve_sub_eq_mutind
  from a_solve_sub_mutind, a_solve_eq_mutind.

(** A guarded skeleton is locally closed. *)
Lemma guarded_pskl_lc : forall P, guarded_pskl P -> lc_pskl P.
Proof. intros P H; inversion H; subst; constructor; assumption. Qed.

Lemma lc_pskl_arrow_inv : forall P1 P2,
  lc_pskl (pskl_arrow P1 P2) -> lc_pskl P1 /\ lc_pskl P2.
Proof. intros P1 P2 H; inversion H; auto. Qed.

Lemma lc_pskl_tophole_inv : forall P,
  lc_pskl (pskl_tophole P) -> lc_pskl P.
Proof. intros P H; inversion H; auto. Qed.

Lemma lc_pskl_all_syn_inv : forall P,
  lc_pskl (pskl_all_syn P) ->
  forall α, lc_pskl (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof. intros P H; inversion H; auto. Qed.

(** Solving preserves local closure. *)
Lemma a_solve_sub_eq_lc :
  (forall Θ m P P0 P', Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' ->
     lc_pskl P -> lc_pskl P0 -> lc_pskl P') /\
  (forall Θ P P0 P', Θ ⊢ₑ P ∼ P0 ⤳ P' ->
     lc_pskl P -> lc_pskl P0 -> lc_pskl P').
Proof.
  apply a_solve_sub_eq_mutind; intros;
    (* peel structured, non-binder inputs *)
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_tophole _) |- _ => apply lc_pskl_tophole_inv in H
    | H : guarded_pskl _           |- _ => apply guarded_pskl_lc in H
    end;
    (* discharge every case with a non-binder output *)
    try solve
      [ assumption
      | eauto
      | constructor; eauto
      | apply lc_pskl_tophole; eauto
      | apply lc_pskl_tophole; constructor; eauto ].
  (* remaining: binder cases — exists-fresh + close: the rule's OWN β
     serves; the close/open round trip exposes the premise's output. *)
  - (* SS-ForallL : ∀P ≼ Q ⤳ ∀(close β P') *)
    match goal with
    | HP : lc_pskl (pskl_all_syn _) |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply (lc_pskl_all_syn_inv HP) | assumption ]
        end
    end.
  - (* SS-ForallR : A ≼ ∀B ⤳ P' (output passes through; β may escape) *)
    match goal with
    | HQ : lc_pskl (pskl_all_syn _),
      IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
        apply IH; [ assumption | apply (lc_pskl_all_syn_inv HQ) ]
    end.
  - (* SE-Forall : ∀P ∼ ∀Q ⤳ ∀(close β P') *)
    match goal with
    | HP : lc_pskl (pskl_all_syn ?p), HQ : lc_pskl (pskl_all_syn ?q)
      |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply (lc_pskl_all_syn_inv HP)
                      | apply (lc_pskl_all_syn_inv HQ) ]
        end
    end.
  - (* SE-GhostForall : ⫯P ∼ ∀Q ⤳ ∀(close β P') *)
    match goal with
    | HQ : lc_pskl (pskl_all_syn _)
      |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply lc_pskl_tophole; assumption
                      | apply (lc_pskl_all_syn_inv HQ) ]
        end
    end.
  - (* SE-ForallGhost : ∀P ∼ ⫯Q ⤳ ∀(close β P') *)
    match goal with
    | HP : lc_pskl (pskl_all_syn _)
      |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply (lc_pskl_all_syn_inv HP)
                      | apply lc_pskl_tophole; assumption ]
        end
    end.
Qed.

Lemma a_solve_sub_lc : forall Θ m P P0 P',
  Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' -> lc_pskl P -> lc_pskl P0 -> lc_pskl P'.
Proof. intros; eapply (proj1 a_solve_sub_eq_lc); eauto. Qed.

Lemma a_solve_eq_lc : forall Θ P P0 P',
  Θ ⊢ₑ P ∼ P0 ⤳ P' -> lc_pskl P -> lc_pskl P0 -> lc_pskl P'.
Proof. intros; eapply (proj2 a_solve_sub_eq_lc); eauto. Qed.

(** Solving a GUARDED subject yields a guarded solution: a guarded LHS only
    matches rules whose output is again guarded (no ghost/tophole/∀ can be
    introduced on the left).  Needed for the tophole cases of output
    well-formedness. *)
Lemma a_solve_sub_eq_guarded :
  (forall Θ m P P0 P', Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' ->
     lc_pskl P -> lc_pskl P0 -> guarded_pskl P -> guarded_pskl P') /\
  (forall Θ P P0 P', Θ ⊢ₑ P ∼ P0 ⤳ P' ->
     lc_pskl P -> lc_pskl P0 -> guarded_pskl P -> guarded_pskl P').
Proof.
  apply a_solve_sub_eq_mutind; intros;
    (* a non-guarded subject makes the case vacuous *)
    try solve [ match goal with H : guarded_pskl _ |- _ => inversion H end ];
    (* peel lc of the arrow / tophole subject/rhs *)
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ => apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_tophole _) |- _ => apply lc_pskl_tophole_inv in H
    end;
    try solve
      [ assumption
      | eauto
      | constructor; eauto using a_solve_sub_lc, a_solve_eq_lc ].
  - (* SS-ForallR : guarded LHS [A] carried through the ∀-RHS opening *)
    match goal with
    | HQ : lc_pskl (pskl_all_syn _),
      IH : lc_pskl _ -> lc_pskl _ -> guarded_pskl _ -> guarded_pskl _ |- _ =>
        apply IH;
          [ assumption | apply (lc_pskl_all_syn_inv HQ) | assumption ]
    end.
Qed.

Lemma a_solve_sub_guarded : forall Θ m P P0 P',
  Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' ->
  lc_pskl P -> lc_pskl P0 -> guarded_pskl P -> guarded_pskl P'.
Proof. intros; eapply (proj1 a_solve_sub_eq_guarded); eauto. Qed.

(** Free variables of the solution.  The EQ half is exact — every eq-∀
    rule CLOSES its output, so eq-solving introduces no new names.  The
    SUB half is DISJUNCTIVE: [SS-ForallR] deliberately lets its binder
    escape into the result (see the constructor comment), so an output
    variable is an input variable OR a name fresh for the context.
    Consumers pin the names they care about inside [dom Θ] (the looked-for
    variable, collected flexibles, binders), where the two readings
    coincide. *)
Lemma a_solve_sub_eq_ftv :
  (forall Θ m P P0 P', Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' ->
     forall α, α `in` ftvar_in_pskl P' ->
       α `in` (ftvar_in_pskl P `union` ftvar_in_pskl P0) \/
       α `notin` dom Θ) /\
  (forall Θ P P0 P', Θ ⊢ₑ P ∼ P0 ⤳ P' ->
     ftvar_in_pskl P' [<=] ftvar_in_pskl P `union` ftvar_in_pskl P0).
Proof.
  apply a_solve_sub_eq_mutind; intros;
    try solve
      [ (* eq-half exact goals + structure-free ones *)
        cbn [ftvar_in_pskl] in *; fsetdec
      | (* sub-half goals whose LEFT disjunct is direct *)
        cbn [ftvar_in_pskl] in *; left; fsetdec
      | (* eq-half CLOSE cases: the closed payload drops the binder *)
        match goal with
        | IH : ftvar_in_pskl ?p' [<=] _
          |- ftvar_in_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b ?p')) [<=] _ =>
            pose proof (ftvar_in_pskl_close_pskl_wrt_pskl p' b) as Hcl;
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b));
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f b));
            cbn [ftvar_in_pskl] in *; fsetdec
        end ].
  - (* SS-ForallL : disjunct through the close *)
    match goal with
    | IH : forall α, α `in` ftvar_in_pskl ?p' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b ?p'))
      |- _ =>
        pose proof (ftvar_in_pskl_close_pskl_wrt_pskl p' b) as Hcl;
        cbn [ftvar_in_pskl] in Hm;
        assert (Hin : a `in` ftvar_in_pskl p') by (clear - Hm Hcl; fsetdec);
        assert (Hne : a `notin` singleton b) by (clear - Hm Hcl; fsetdec);
        destruct (IH a Hin) as [Hl | Hr];
          [ pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b))
              as Hup; cbn [ftvar_in_pskl] in *; left; clear - Hl Hup Hne; fsetdec
          | right; exact Hr ]
    end.
  - (* SS-UnivGhostL *)
    match goal with
    | IH : forall α, α `in` ftvar_in_pskl ?p' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_tophole ?p') |- _ =>
        cbn [ftvar_in_pskl] in Hm;
        destruct (IH a Hm) as [Hl | Hr];
          [ left; cbn [ftvar_in_pskl] in *; clear - Hl; fsetdec
          | right; exact Hr ]
    end.
  - (* SS-ForallR : the leak — the output variable is an input variable,
       the escaped binder (fresh for dom Θ by the rule's own condition),
       or already fresh *)
    match goal with
    | Hfr : ?b `notin` _ ,
      IH : forall α, α `in` ftvar_in_pskl ?p' -> _ ,
      Hm : ?a `in` ftvar_in_pskl ?p' |- _ =>
        destruct (IH a Hm) as [Hl | Hr];
          [ pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
              as Hup; cbn [ftvar_in_pskl] in *;
            destruct (a == b) as [-> | Hne];
              [ right; clear - Hfr; fsetdec
              | left;
                assert (Hne' : a `notin` singleton b)
                  by (apply notin_singleton_2; auto);
                clear - Hl Hup Hne'; fsetdec ]
          | right; exact Hr ]
    end.
  - (* SS-Arrow : exact eq bound on the domain, disjunct on the codomain *)
    match goal with
    | He : ftvar_in_pskl ?e' [<=] _ ,
      IH : forall α, α `in` ftvar_in_pskl ?p2' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_arrow ?e' ?p2') |- _ =>
        cbn [ftvar_in_pskl] in Hm;
        apply union_1 in Hm; destruct Hm as [Hm | Hm];
          [ left; cbn [ftvar_in_pskl] in *; clear - Hm He; fsetdec
          | destruct (IH a Hm) as [Hl | Hr];
              [ left; cbn [ftvar_in_pskl] in *; clear - Hl; fsetdec
              | right; exact Hr ] ]
    end.
  - (* SS-GhostLF : both branches at ◇ *)
    match goal with
    | He : ftvar_in_pskl ?e' [<=] _ ,
      IH : forall α, α `in` ftvar_in_pskl ?p2' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_tophole (pskl_arrow ?e' ?p2')) |- _ =>
        cbn [ftvar_in_pskl] in Hm;
        apply union_1 in Hm; destruct Hm as [Hm | Hm];
          [ left; cbn [ftvar_in_pskl] in *; clear - Hm He; fsetdec
          | destruct (IH a Hm) as [Hl | Hr];
              [ left; cbn [ftvar_in_pskl] in *; clear - Hl; fsetdec
              | right; exact Hr ] ]
    end.
Qed.

Lemma a_solve_sub_ftv : forall Θ m P P0 P',
  Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' ->
  forall α, α `in` ftvar_in_pskl P' ->
    α `in` (ftvar_in_pskl P `union` ftvar_in_pskl P0) \/ α `notin` dom Θ.
Proof. intros; eapply (proj1 a_solve_sub_eq_ftv); eauto. Qed.

Lemma a_solve_eq_ftv : forall Θ P P0 P',
  Θ ⊢ₑ P ∼ P0 ⤳ P' ->
  ftvar_in_pskl P' [<=] ftvar_in_pskl P `union` ftvar_in_pskl P0.
Proof. intros; eapply (proj2 a_solve_sub_eq_ftv); eauto. Qed.

(* ===================================================================== *)
(*  RENAMING THROUGH THE SOLVE (freshness campaign, DESIGN.md §4.3).      *)
(*                                                                        *)
(*  Asymmetric: the TARGET β0 is fresh — for the context, both inputs,    *)
(*  AND THE OUTPUT.  The output exclusion is not bookkeeping: SS-ForallR  *)
(*  LEAKS its witness into the result, and renaming ONTO a leaked name is *)
(*  underivable (the leak pins the witness; a fresh witness produces a    *)
(*  differently-leaked output).  The SOURCE α0 only dodges [dom Θ].       *)
(*                                                                        *)
(*  SIZE induction (tagged: +1 for the sub half, whose Check row moves    *)
(*  sub ⤳ eq at unchanged sizes): when α0 or β0 collides with a recorded  *)
(*  witness the premise is renamed TWICE, and the second rename applies   *)
(*  to the result of the first — no sub-derivation (cluster-1 recipe).    *)
(* ===================================================================== *)

Lemma subst_pskl_var_same : forall P α,
  subst_pskl_in_pskl (pskl_var_f α) α P = P.
Proof.
  induction P; intros α0; simpl; f_equal; auto.
  destruct (α == α0); subst; reflexivity.
Qed.

(** "Close after renaming", pskl flavour (cf. [close_ptyp_subst_var]). *)
Lemma close_pskl_subst_var : forall P α β,
  β `notin` ftvar_in_pskl P ->
  close_pskl_wrt_pskl β (subst_pskl_in_pskl (pskl_var_f β) α P)
  = close_pskl_wrt_pskl α P.
Proof.
  intros P α β Hβ.
  rewrite subst_pskl_in_pskl_spec.
  apply close_pskl_wrt_pskl_open_pskl_wrt_pskl.
  pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P α) as Hcl.
  clear - Hβ Hcl. fsetdec.
Qed.

Lemma guarded_pskl_rename_var : forall P α β,
  guarded_pskl P ->
  guarded_pskl (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros P α β Hg; inversion Hg; subst; simpl.
  - constructor.
  - destruct (α0 == α); constructor.
  - constructor;
      (apply subst_pskl_in_pskl_lc_pskl; [ assumption | apply lc_pskl_var_f ]).
Qed.

Lemma a_non_flex_rename_var : forall Θ P α β,
  α `notin` dom Θ -> β `notin` dom Θ ->
  a_non_flex Θ P ->
  a_non_flex Θ (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros Θ P α β Hα Hβ [Hlc Hnf].
  split.
  - apply subst_pskl_in_pskl_lc_pskl; [ exact Hlc | constructor ].
  - intros Hf.
    destruct P; simpl in Hf; try solve [ inversion Hf ].
    match type of Hf with context [ if ?e then _ else _ ] =>
      destruct e end.
    + inversion Hf; subst;
        match goal with Hb : binds _ _ Θ |- _ =>
          apply binds_In in Hb; contradiction end.
    + apply Hnf; exact Hf.
Qed.

Lemma a_solve_sub_eq_rename_size : forall n,
  (forall Θ m P Q P',
     2 * (size_pskl P + size_pskl Q) + 1 <= n ->
     Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
     forall α0 β0,
     α0 `notin` dom Θ ->
     β0 `notin` dom Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
         `union` ftvar_in_pskl P' ->
     Θ ⊢ₛ (subst_pskl_in_pskl (pskl_var_f β0) α0 P) ≼[ m ]
          (subst_pskl_in_pskl (pskl_var_f β0) α0 Q)
          ⤳ (subst_pskl_in_pskl (pskl_var_f β0) α0 P')) /\
  (forall Θ P Q P',
     2 * (size_pskl P + size_pskl Q) <= n ->
     Θ ⊢ₑ P ∼ Q ⤳ P' ->
     forall α0 β0,
     α0 `notin` dom Θ ->
     β0 `notin` dom Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
         `union` ftvar_in_pskl P' ->
     Θ ⊢ₑ (subst_pskl_in_pskl (pskl_var_f β0) α0 P)
        ∼ (subst_pskl_in_pskl (pskl_var_f β0) α0 Q)
        ⤳ (subst_pskl_in_pskl (pskl_var_f β0) α0 P')).
Proof.
  induction n as [| n IHall];
    [ split; intros * Hsz Hd; inversion Hd; subst; cbn in Hsz; lia | ].
  destruct IHall as [IHs IHe].
  (* both halves handle [α0 = β0] upfront: the rename is then the identity *)
  split.
  (* ================= the [a_solve_sub] half ================= *)
  { intros Θ m P Q P' Hsz Hd α0 β0 Hα0 Hβ0.
    destruct (α0 == β0) as [-> | Hne0];
      [ rewrite ! subst_pskl_var_same; exact Hd | ].
    destruct Hd as
      [ Θ m α Q                                   (* SS-Var *)
      | Θ m P Q P' b Hfr Hp                       (* SS-ForallL *)
      | Θ m P Q P' Hp                             (* SS-UnivGhostL *)
      | Θ m P                                     (* SS-Vacuous *)
      | Θ P Q P' Hg1 Hg2 Hp                       (* SS-Check *)
      | Θ A B P' b Hfr Hp                         (* SS-ForallR *)
      | Θ m P1 P2 Q1 Q2 P1' P2' Hp1 Hp2           (* SS-Arrow *)
      | Θ m Q1 Q2 P1' P2' Hp1 Hp2                 (* SS-GhostLF *)
      | Θ B Hg ];                                 (* SS-GhostL *)
      cbn in Hsz; cbn [subst_pskl_in_pskl] in *.
    - (* SS-Var *) destruct (α == α0); apply a_solve_sub__var.
    - (* SS-ForallL — close case *)
      cbn in Hβ0.
      pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl.
      destruct (α0 == b) as [-> | Hα0b].
      + (* source = witness: every substitution is an identity *)
        rewrite (subst_pskl_in_pskl_fresh_eq P) by (clear - Hfr; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq Q) by (clear - Hfr; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq (close_pskl_wrt_pskl b P'))
          by (clear - Hcl; fsetdec).
        apply a_solve_sub__forall_l with (β := b); [ exact Hfr | exact Hp ].
      + destruct (β0 == b) as [-> | Hβ0b].
        * (* target = witness: move the witness to a fresh δ, then rename *)
          pick fresh δ for
            (dom Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
               `union` ftvar_in_pskl P' `union` singleton α0 `union` singleton b).
          assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
                              + size_pskl Q) + 1 <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
          pose proof (IHs _ _ _ _ _ Hsz1 Hp b δ ltac:(clear - Hfr; fsetdec)
                        ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            P (pskl_var_f b)) as Hup;
                              cbn in Hup; clear - Fr Hup; fsetdec)) as H1.
          rewrite <- (subst_pskl_in_pskl_intro b P (pskl_var_f δ))
            in H1 by (clear - Hfr; fsetdec).
          rewrite (subst_pskl_in_pskl_fresh_eq Q)
            in H1 by (clear - Hfr; fsetdec).
          assert (Hsz2 : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f δ))
                              + size_pskl Q) + 1 <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
          pose proof (IHs _ _ _ _ _ Hsz2 H1 α0 b ltac:(exact Hα0)
                        ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            P (pskl_var_f δ)) as Hup;
                              pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                                            P' (pskl_var_f δ) b) as Hs';
                              cbn in Hup, Hs';
                              clear - Hfr Hβ0 Hup Hs' Fr; fsetdec)) as H2.
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f b))
            in H2 by (solve [ clear - Fr; fsetdec | constructor ]).
          rewrite <- (@close_pskl_subst_var P' b δ) by (clear - Fr; fsetdec).
          rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl
                     (subst_pskl_in_pskl (pskl_var_f δ) b P')
                     (pskl_var_f b) α0 δ)
            by (solve [ constructor | clear - Fr; fsetdec
                      | cbn; clear - Fr; fsetdec ]).
          apply a_solve_sub__forall_l with (β := δ);
            [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            P (pskl_var_f b) α0) as HpP;
              pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            Q (pskl_var_f b) α0) as HpQ;
              cbn in HpP, HpQ; clear - Fr HpP HpQ; fsetdec
            | exact H2 ].
        * (* ordinary: keep the witness *)
          rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl P' (pskl_var_f β0) α0 b)
            by (solve [ constructor | assumption
                      | cbn; clear - Hβ0b;
                        apply notin_singleton_2; auto ]).
          apply a_solve_sub__forall_l with (β := b).
          { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          P (pskl_var_f β0) α0) as HpP;
            pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          Q (pskl_var_f β0) α0) as HpQ;
            cbn in HpP, HpQ.
            assert (Hbb : b `notin` singleton β0)
              by (clear - Hβ0b; apply notin_singleton_2; auto).
            clear - Hfr HpP HpQ Hbb; fsetdec. }
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f β0))
            by (solve [ auto | constructor ]).
          apply IHs with (m := m);
            [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
            | exact Hp | exact Hα0
            | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                            P (pskl_var_f b)) as Hup; cbn in Hup;
              assert (Hbb : β0 `notin` singleton b)
                by (clear - Hβ0b; apply notin_singleton_2; auto);
              clear - Hβ0 Hup Hbb Hcl; fsetdec ].
    - (* SS-UnivGhostL *)
      cbn in Hβ0.
      apply a_solve_sub__univ_ghost_l.
      apply IHs with (m := m);
        [ lia | exact Hp | exact Hα0 | clear - Hβ0; fsetdec ].
    - (* SS-Vacuous *) apply a_solve_sub__vacuous.
    - (* SS-Check *)
      apply a_solve_sub__check;
        [ apply guarded_pskl_rename_var; assumption
        | apply guarded_pskl_rename_var; assumption
        | apply IHe; [ lia | exact Hp | exact Hα0 | exact Hβ0 ] ].
    - (* SS-ForallR — the LEAK case *)
      cbn in Hβ0.
      destruct (α0 == b) as [-> | Hα0b].
      + (* source = witness: rename the premise b ⤳ β0 and re-bind at β0.
           [β0 ∉ ftv P'] (the lemma's output hypothesis) is what makes the
           new witness produce the RIGHT leaks. *)
        rewrite (subst_pskl_in_pskl_fresh_eq A) by (clear - Hfr; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq B) by (clear - Hfr; fsetdec).
        assert (Hsz1 : 2 * (size_pskl A
                            + size_pskl (open_pskl_wrt_pskl B (pskl_var_f b)))
                       + 1 <= n)
          by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
        pose proof (IHs _ _ _ _ _ Hsz1 Hp b β0 ltac:(clear - Hfr; fsetdec)
                      ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                          B (pskl_var_f b)) as Hup;
                            cbn in Hup;
                            assert (Hbb : β0 `notin` singleton b)
                              by (apply notin_singleton_2; auto);
                            clear - Hβ0 Hup Hbb; fsetdec)) as H1.
        rewrite (subst_pskl_in_pskl_fresh_eq A)
          in H1 by (clear - Hfr; fsetdec).
        rewrite <- (subst_pskl_in_pskl_intro b B (pskl_var_f β0))
          in H1 by (clear - Hfr; fsetdec).
        apply a_solve_sub__forall_r with (β := β0);
          [ clear - Hβ0; fsetdec | exact H1 ].
      + destruct (β0 == b) as [-> | Hβ0b].
        * (* target = witness.  Then the witness never leaked ([β0 ∉ ftv P']
             = [b ∉ ftv P']), so it can be moved to a fresh δ residue-free. *)
          pick fresh δ for
            (dom Θ `union` ftvar_in_pskl A `union` ftvar_in_pskl B
               `union` ftvar_in_pskl P' `union` singleton α0 `union` singleton b).
          assert (Hsz1 : 2 * (size_pskl A
                              + size_pskl (open_pskl_wrt_pskl B (pskl_var_f b)))
                         + 1 <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
          pose proof (IHs _ _ _ _ _ Hsz1 Hp b δ ltac:(clear - Hfr; fsetdec)
                        ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            B (pskl_var_f b)) as Hup;
                              cbn in Hup; clear - Fr Hup; fsetdec)) as H1.
          rewrite (subst_pskl_in_pskl_fresh_eq A)
            in H1 by (clear - Hfr; fsetdec).
          rewrite <- (subst_pskl_in_pskl_intro b B (pskl_var_f δ))
            in H1 by (clear - Hfr; fsetdec).
          rewrite (subst_pskl_in_pskl_fresh_eq P')
            in H1 by (clear - Hβ0; fsetdec).
          assert (Hsz2 : 2 * (size_pskl A
                              + size_pskl (open_pskl_wrt_pskl B (pskl_var_f δ)))
                         + 1 <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
          pose proof (IHs _ _ _ _ _ Hsz2 H1 α0 b ltac:(exact Hα0)
                        ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            B (pskl_var_f δ)) as Hup;
                              cbn in Hup;
                              clear - Hfr Hβ0 Hup Fr; fsetdec)) as H2.
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var B (pskl_var_f b))
            in H2 by (solve [ clear - Fr; fsetdec | constructor ]).
          apply a_solve_sub__forall_r with (β := δ);
            [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            A (pskl_var_f b) α0) as HpA;
              pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            B (pskl_var_f b) α0) as HpB;
              cbn in HpA, HpB; clear - Fr HpA HpB; fsetdec
            | exact H2 ].
        * (* ordinary *)
          apply a_solve_sub__forall_r with (β := b).
          { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          A (pskl_var_f β0) α0) as HpA;
            pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          B (pskl_var_f β0) α0) as HpB;
            cbn in HpA, HpB.
            assert (Hbb : b `notin` singleton β0)
              by (clear - Hβ0b; apply notin_singleton_2; auto).
            clear - Hfr HpA HpB Hbb; fsetdec. }
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var B (pskl_var_f β0))
            by (solve [ auto | constructor ]).
          apply IHs with (m := mode_tc);
            [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
            | exact Hp | exact Hα0
            | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                            B (pskl_var_f b)) as Hup; cbn in Hup;
              assert (Hbb : β0 `notin` singleton b)
                by (clear - Hβ0b; apply notin_singleton_2; auto);
              clear - Hβ0 Hup Hbb; fsetdec ].
    - (* SS-Arrow *)
      cbn in Hβ0.
      apply a_solve_sub__arrow;
        [ apply IHe; [ lia | exact Hp1 | exact Hα0 | clear - Hβ0; fsetdec ]
        | apply IHs with (m := m);
            [ lia | exact Hp2 | exact Hα0 | clear - Hβ0; fsetdec ] ].
    - (* SS-GhostLF : the ◇ subject is subst-invariant — [change] re-exposes
         the substitution so the IH's conclusion shape matches *)
      cbn in Hβ0.
      apply a_solve_sub__ghost_l_fn.
      + change (Θ ⊢ₑ subst_pskl_in_pskl (pskl_var_f β0) α0 pskl_hole
                   ∼ subst_pskl_in_pskl (pskl_var_f β0) α0 Q1
                   ⤳ subst_pskl_in_pskl (pskl_var_f β0) α0 P1').
        apply IHe; [ cbn; lia | exact Hp1 | exact Hα0 | clear - Hβ0; fsetdec ].
      + change (Θ ⊢ₛ subst_pskl_in_pskl (pskl_var_f β0) α0 pskl_hole ≼[ m ]
                   subst_pskl_in_pskl (pskl_var_f β0) α0 Q2
                   ⤳ subst_pskl_in_pskl (pskl_var_f β0) α0 P2').
        apply IHs with (m := m);
          [ cbn; lia | exact Hp2 | exact Hα0 | clear - Hβ0; fsetdec ].
    - (* SS-GhostL *)
      apply a_solve_sub__ghost_l. apply guarded_pskl_rename_var. exact Hg. }
  (* ================= the [a_solve_eq] half ================= *)
  { intros Θ P Q P' Hsz Hd α0 β0 Hα0 Hβ0.
    destruct (α0 == β0) as [-> | Hne0];
      [ rewrite ! subst_pskl_var_same; exact Hd | ].
    destruct Hd as
      [ Θ                                         (* SE-Unit *)
      | Θ α Q                                     (* SE-Var *)
      | Θ α P Hflex Hnf                           (* SE-FlexR *)
      | Θ Q                                       (* SE-GhostL *)
      | Θ P                                       (* SE-VacuousR *)
      | Θ P1 P2 Q1 Q2 P1' P2' Hp1 Hp2             (* SE-Arrow *)
      | Θ P Q P' b Hfr Hp                         (* SE-Forall *)
      | Θ P Q P' Hp                               (* SE-UnivGhost *)
      | Θ P Q P' b Hfr Hp                         (* SE-GhostForall *)
      | Θ P Q P' Hg Hp                            (* SE-GhostGuarded *)
      | Θ P Q P' b Hfr Hp                         (* SE-ForallGhost *)
      | Θ P Q P' Hg Hp ];                         (* SE-GuardedGhost *)
      cbn in Hsz; cbn [subst_pskl_in_pskl] in *.
    - apply a_solve_eq__unit.
    - destruct (α == α0); apply a_solve_eq__var.
    - (* SE-FlexR *)
      assert (Hαne : α <> α0)
        by (destruct Hflex as [Hb | [τ0 Hb]]; apply binds_In in Hb;
            intro Heq; subst; contradiction).
      repeat match goal with
             | |- context [ if ?e then _ else _ ] =>
                 destruct e; [ congruence | ]
             end.
      apply a_solve_eq__flex_r;
        [ exact Hflex | apply a_non_flex_rename_var;
            [ exact Hα0 | clear - Hβ0; fsetdec | exact Hnf ] ].
    - apply a_solve_eq__hole_l.
    - apply a_solve_eq__hole_r.
    - (* SE-Arrow *)
      cbn in Hβ0.
      apply a_solve_eq__arrow;
        [ apply IHe; [ lia | exact Hp1 | exact Hα0 | clear - Hβ0; fsetdec ]
        | apply IHe; [ lia | exact Hp2 | exact Hα0 | clear - Hβ0; fsetdec ] ].
    - (* SE-Forall — close case, both sides open *)
      cbn in Hβ0.
      pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl.
      destruct (α0 == b) as [-> | Hα0b].
      + rewrite (subst_pskl_in_pskl_fresh_eq P) by (clear - Hfr; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq Q) by (clear - Hfr; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq (close_pskl_wrt_pskl b P'))
          by (clear - Hcl; fsetdec).
        apply a_solve_eq__forall with (β := b); [ exact Hfr | exact Hp ].
      + destruct (β0 == b) as [-> | Hβ0b].
        * pick fresh δ for
            (dom Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
               `union` ftvar_in_pskl P' `union` singleton α0 `union` singleton b).
          assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
                              + size_pskl (open_pskl_wrt_pskl Q (pskl_var_f b)))
                         <= n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia).
          pose proof (IHe _ _ _ _ Hsz1 Hp b δ ltac:(clear - Hfr; fsetdec)
                        ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            P (pskl_var_f b)) as HupP;
                              pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            Q (pskl_var_f b)) as HupQ;
                              cbn in HupP, HupQ; clear - Fr HupP HupQ; fsetdec))
            as H1.
          rewrite <- (subst_pskl_in_pskl_intro b P (pskl_var_f δ))
            in H1 by (clear - Hfr; fsetdec).
          rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ))
            in H1 by (clear - Hfr; fsetdec).
          assert (Hsz2 : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f δ))
                              + size_pskl (open_pskl_wrt_pskl Q (pskl_var_f δ)))
                         <= n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia).
          pose proof (IHe _ _ _ _ Hsz2 H1 α0 b ltac:(exact Hα0)
                        ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            P (pskl_var_f δ)) as HupP;
                              pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            Q (pskl_var_f δ)) as HupQ;
                              pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                                            P' (pskl_var_f δ) b) as Hs';
                              cbn in HupP, HupQ, Hs';
                              clear - Hfr Hβ0 HupP HupQ Hs' Fr; fsetdec)) as H2.
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f b))
            in H2 by (solve [ clear - Fr; fsetdec | constructor ]).
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
            in H2 by (solve [ clear - Fr; fsetdec | constructor ]).
          rewrite <- (@close_pskl_subst_var P' b δ) by (clear - Fr; fsetdec).
          rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl
                     (subst_pskl_in_pskl (pskl_var_f δ) b P')
                     (pskl_var_f b) α0 δ)
            by (solve [ constructor | clear - Fr; fsetdec
                      | cbn; clear - Fr; fsetdec ]).
          apply a_solve_eq__forall with (β := δ);
            [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            P (pskl_var_f b) α0) as HpP;
              pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            Q (pskl_var_f b) α0) as HpQ;
              cbn in HpP, HpQ; clear - Fr HpP HpQ; fsetdec
            | exact H2 ].
        * rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl P' (pskl_var_f β0) α0 b)
            by (solve [ constructor | assumption
                      | cbn; clear - Hβ0b; apply notin_singleton_2; auto ]).
          apply a_solve_eq__forall with (β := b).
          { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          P (pskl_var_f β0) α0) as HpP;
            pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          Q (pskl_var_f β0) α0) as HpQ;
            cbn in HpP, HpQ.
            assert (Hbb : b `notin` singleton β0)
              by (clear - Hβ0b; apply notin_singleton_2; auto).
            clear - Hfr HpP HpQ Hbb; fsetdec. }
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f β0))
            by (solve [ auto | constructor ]).
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f β0))
            by (solve [ auto | constructor ]).
          apply IHe;
            [ rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia
            | exact Hp | exact Hα0
            | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                            P (pskl_var_f b)) as HupP;
              pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                            Q (pskl_var_f b)) as HupQ;
              cbn in HupP, HupQ;
              assert (Hbb : β0 `notin` singleton b)
                by (clear - Hβ0b; apply notin_singleton_2; auto);
              clear - Hβ0 HupP HupQ Hbb Hcl; fsetdec ].
    - (* SE-UnivGhost *)
      cbn in Hβ0.
      apply a_solve_eq__tophole_both.
      apply IHe; [ lia | exact Hp | exact Hα0 | clear - Hβ0; fsetdec ].
    - (* SE-GhostForall — close case, RHS opens *)
      cbn in Hβ0.
      pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl.
      destruct (α0 == b) as [-> | Hα0b].
      + rewrite (subst_pskl_in_pskl_fresh_eq P) by (clear - Hfr; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq Q) by (clear - Hfr; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq (close_pskl_wrt_pskl b P'))
          by (clear - Hcl; fsetdec).
        apply a_solve_eq__tophole_l_all with (β := b); [ exact Hfr | exact Hp ].
      + destruct (β0 == b) as [-> | Hβ0b].
        * pick fresh δ for
            (dom Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
               `union` ftvar_in_pskl P' `union` singleton α0 `union` singleton b).
          assert (Hsz1 : 2 * (size_pskl (pskl_tophole P)
                              + size_pskl (open_pskl_wrt_pskl Q (pskl_var_f b)))
                         <= n)
            by (cbn; rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn in Hsz; lia).
          pose proof (IHe _ _ _ _ Hsz1 Hp b δ ltac:(clear - Hfr; fsetdec)
                        ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            Q (pskl_var_f b)) as HupQ;
                              cbn in HupQ |- *; clear - Fr HupQ; fsetdec)) as H1.
          cbn [subst_pskl_in_pskl] in H1.
          rewrite (subst_pskl_in_pskl_fresh_eq P)
            in H1 by (clear - Hfr; fsetdec).
          rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ))
            in H1 by (clear - Hfr; fsetdec).
          assert (Hsz2 : 2 * (size_pskl (pskl_tophole P)
                              + size_pskl (open_pskl_wrt_pskl Q (pskl_var_f δ)))
                         <= n)
            by (cbn; rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn in Hsz; lia).
          assert (H1' : Θ ⊢ₑ (pskl_tophole P)
                          ∼ (open_pskl_wrt_pskl Q (pskl_var_f δ))
                          ⤳ (subst_pskl_in_pskl (pskl_var_f δ) b P'))
            by (cbn [subst_pskl_in_pskl]; exact H1).
          pose proof (IHe _ _ _ _ Hsz2 H1' α0 b ltac:(exact Hα0)
                        ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            Q (pskl_var_f δ)) as HupQ;
                              pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                                            P' (pskl_var_f δ) b) as Hs';
                              cbn in HupQ, Hs' |- *;
                              clear - Hfr Hβ0 HupQ Hs' Fr; fsetdec)) as H2.
          cbn [subst_pskl_in_pskl] in H2.
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
            in H2 by (solve [ clear - Fr; fsetdec | constructor ]).
          rewrite <- (@close_pskl_subst_var P' b δ) by (clear - Fr; fsetdec).
          rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl
                     (subst_pskl_in_pskl (pskl_var_f δ) b P')
                     (pskl_var_f b) α0 δ)
            by (solve [ constructor | clear - Fr; fsetdec
                      | cbn; clear - Fr; fsetdec ]).
          apply a_solve_eq__tophole_l_all with (β := δ);
            [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            P (pskl_var_f b) α0) as HpP;
              pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            Q (pskl_var_f b) α0) as HpQ;
              cbn in HpP, HpQ; clear - Fr HpP HpQ; fsetdec
            | exact H2 ].
        * rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl P' (pskl_var_f β0) α0 b)
            by (solve [ constructor | assumption
                      | cbn; clear - Hβ0b; apply notin_singleton_2; auto ]).
          apply a_solve_eq__tophole_l_all with (β := b).
          { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          P (pskl_var_f β0) α0) as HpP;
            pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          Q (pskl_var_f β0) α0) as HpQ;
            cbn in HpP, HpQ.
            assert (Hbb : b `notin` singleton β0)
              by (clear - Hβ0b; apply notin_singleton_2; auto).
            clear - Hfr HpP HpQ Hbb; fsetdec. }
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f β0))
            by (solve [ auto | constructor ]).
          change (Θ ⊢ₑ subst_pskl_in_pskl (pskl_var_f β0) α0 (pskl_tophole P)
                     ∼ subst_pskl_in_pskl (pskl_var_f β0) α0
                         (open_pskl_wrt_pskl Q (pskl_var_f b))
                     ⤳ subst_pskl_in_pskl (pskl_var_f β0) α0 P').
          apply IHe;
            [ cbn; rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn in Hsz; lia
            | exact Hp | exact Hα0
            | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                            Q (pskl_var_f b)) as HupQ;
              cbn in HupQ |- *;
              assert (Hbb : β0 `notin` singleton b)
                by (clear - Hβ0b; apply notin_singleton_2; auto);
              clear - Hβ0 HupQ Hbb Hcl; fsetdec ].
    - (* SE-GhostGuarded *)
      cbn in Hβ0.
      apply a_solve_eq__tophole_l_guarded;
        [ apply guarded_pskl_rename_var; exact Hg
        | apply IHe; [ cbn; cbn in Hsz; lia | exact Hp | exact Hα0
                     | clear - Hβ0; fsetdec ] ].
    - (* SE-ForallGhost — close case, LHS opens *)
      cbn in Hβ0.
      pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl.
      destruct (α0 == b) as [-> | Hα0b].
      + rewrite (subst_pskl_in_pskl_fresh_eq P) by (clear - Hfr; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq Q) by (clear - Hfr; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq (close_pskl_wrt_pskl b P'))
          by (clear - Hcl; fsetdec).
        apply a_solve_eq__all_l_tophole with (β := b); [ exact Hfr | exact Hp ].
      + destruct (β0 == b) as [-> | Hβ0b].
        * pick fresh δ for
            (dom Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
               `union` ftvar_in_pskl P' `union` singleton α0 `union` singleton b).
          assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
                              + size_pskl (pskl_tophole Q)) <= n)
            by (cbn; rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn in Hsz; lia).
          pose proof (IHe _ _ _ _ Hsz1 Hp b δ ltac:(clear - Hfr; fsetdec)
                        ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            P (pskl_var_f b)) as HupP;
                              cbn in HupP |- *; clear - Fr HupP; fsetdec)) as H1.
          cbn [subst_pskl_in_pskl] in H1.
          rewrite (subst_pskl_in_pskl_fresh_eq Q)
            in H1 by (clear - Hfr; fsetdec).
          rewrite <- (subst_pskl_in_pskl_intro b P (pskl_var_f δ))
            in H1 by (clear - Hfr; fsetdec).
          assert (Hsz2 : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f δ))
                              + size_pskl (pskl_tophole Q)) <= n)
            by (cbn; rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn in Hsz; lia).
          assert (H1' : Θ ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f δ))
                          ∼ (pskl_tophole Q)
                          ⤳ (subst_pskl_in_pskl (pskl_var_f δ) b P'))
            by (exact H1).
          pose proof (IHe _ _ _ _ Hsz2 H1' α0 b ltac:(exact Hα0)
                        ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                            P (pskl_var_f δ)) as HupP;
                              pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                                            P' (pskl_var_f δ) b) as Hs';
                              cbn in HupP, Hs' |- *;
                              clear - Hfr Hβ0 HupP Hs' Fr; fsetdec)) as H2.
          cbn [subst_pskl_in_pskl] in H2.
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f b))
            in H2 by (solve [ clear - Fr; fsetdec | constructor ]).
          rewrite <- (@close_pskl_subst_var P' b δ) by (clear - Fr; fsetdec).
          rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl
                     (subst_pskl_in_pskl (pskl_var_f δ) b P')
                     (pskl_var_f b) α0 δ)
            by (solve [ constructor | clear - Fr; fsetdec
                      | cbn; clear - Fr; fsetdec ]).
          apply a_solve_eq__all_l_tophole with (β := δ);
            [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            P (pskl_var_f b) α0) as HpP;
              pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            Q (pskl_var_f b) α0) as HpQ;
              cbn in HpP, HpQ; clear - Fr HpP HpQ; fsetdec
            | exact H2 ].
        * rewrite (subst_pskl_in_pskl_close_pskl_wrt_pskl P' (pskl_var_f β0) α0 b)
            by (solve [ constructor | assumption
                      | cbn; clear - Hβ0b; apply notin_singleton_2; auto ]).
          apply a_solve_eq__all_l_tophole with (β := b).
          { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          P (pskl_var_f β0) α0) as HpP;
            pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          Q (pskl_var_f β0) α0) as HpQ;
            cbn in HpP, HpQ.
            assert (Hbb : b `notin` singleton β0)
              by (clear - Hβ0b; apply notin_singleton_2; auto).
            clear - Hfr HpP HpQ Hbb; fsetdec. }
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f β0))
            by (solve [ auto | constructor ]).
          change (Θ ⊢ₑ subst_pskl_in_pskl (pskl_var_f β0) α0
                         (open_pskl_wrt_pskl P (pskl_var_f b))
                     ∼ subst_pskl_in_pskl (pskl_var_f β0) α0 (pskl_tophole Q)
                     ⤳ subst_pskl_in_pskl (pskl_var_f β0) α0 P').
          apply IHe;
            [ cbn; rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn in Hsz; lia
            | exact Hp | exact Hα0
            | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                            P (pskl_var_f b)) as HupP;
              cbn in HupP |- *;
              assert (Hbb : β0 `notin` singleton b)
                by (clear - Hβ0b; apply notin_singleton_2; auto);
              clear - Hβ0 HupP Hbb Hcl; fsetdec ].
    - (* SE-GuardedGhost *)
      cbn in Hβ0.
      apply a_solve_eq__tophole_r_guarded;
        [ apply guarded_pskl_rename_var; exact Hg
        | apply IHe; [ cbn; cbn in Hsz; lia | exact Hp | exact Hα0
                     | clear - Hβ0; fsetdec ] ]. }
Qed.

Lemma a_solve_sub_rename_var : forall Θ m P Q P' α0 β0,
  Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
  α0 `notin` dom Θ ->
  β0 `notin` dom Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
      `union` ftvar_in_pskl P' ->
  Θ ⊢ₛ (subst_pskl_in_pskl (pskl_var_f β0) α0 P) ≼[ m ]
       (subst_pskl_in_pskl (pskl_var_f β0) α0 Q)
       ⤳ (subst_pskl_in_pskl (pskl_var_f β0) α0 P').
Proof.
  intros. eapply (proj1 (a_solve_sub_eq_rename_size
                           (2 * (size_pskl P + size_pskl Q) + 1))); eauto.
Qed.

Lemma a_solve_eq_rename_var : forall Θ P Q P' α0 β0,
  Θ ⊢ₑ P ∼ Q ⤳ P' ->
  α0 `notin` dom Θ ->
  β0 `notin` dom Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
      `union` ftvar_in_pskl P' ->
  Θ ⊢ₑ (subst_pskl_in_pskl (pskl_var_f β0) α0 P)
     ∼ (subst_pskl_in_pskl (pskl_var_f β0) α0 Q)
     ⤳ (subst_pskl_in_pskl (pskl_var_f β0) α0 P').
Proof.
  intros. eapply (proj2 (a_solve_sub_eq_rename_size
                           (2 * (size_pskl P + size_pskl Q)))); eauto.
Qed.
