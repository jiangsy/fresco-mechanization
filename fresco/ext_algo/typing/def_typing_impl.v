Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_ln.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_uip.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.def_sub.
Require Import src.fresco.ext_algo.typing.def_pat.
Require Import src.fresco.ext_algo.typing.def_typing.
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.consistency.def_consis_impl.
Require Import src.fresco.ext_algo.subtyping.def_sub_impl.
Require Import src.fresco.ext_algo.typing.def_pat_impl.

Set Equations With UIP.

Open Scope fresco_e_scope.

Definition ptyp_arrow_split (A : ptyp)
    : option (sig (fun p : ptyp * ptyp
                   => A = ptyp_arrow (fst p) (snd p))) :=
  match A with
  | ptyp_arrow A1 A2 => Some (exist _ (A1, A2) eq_refl)
  | _ => None
  end.

Lemma e_typing_abs_check_step_close : forall α S0 S1 Θ0 Θ1 A0 e B' Ξ,
  a_suffix Ξ ->
  uniq (Ξ ++ Θ0) ->
  is_empty (inter (dom Ξ)
              (ftvar_in_ptyp (close_ptyp_wrt_ptyp α B'))) = true ->
  α `notin` S0 ->
  {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
     ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
     (exp_abs e) ⦂ B' ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ]
     (exp_abs e) ⦂ (ptyp_all (close_ptyp_wrt_ptyp α B')) ⊣ Θ1 }}e.
Proof.
  intros * Hsuf Huq Hγ Hα Hrun.
  eapply e_typing__abs_check_step with (A := close_ptyp_wrt_ptyp α B');
    try eassumption.
  - exact (inter_empty_notin_all _ _ Hγ).
  - rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp. fsetdec.
  - rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp. exact Hrun.
Qed.

Lemma e_typing_abs_anno_check_step_close :
  forall α S0 S1 Θ0 Θ1 A0 Aan e B' Ξ,
  a_suffix Ξ ->
  uniq (Ξ ++ Θ0) ->
  is_empty (inter (dom Ξ)
              (ftvar_in_ptyp (close_ptyp_wrt_ptyp α B'))) = true ->
  α `notin` S0 ->
  {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
     ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
     (exp_abs_anno Aan e) ⦂ B' ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ]
     (exp_abs_anno Aan e) ⦂ (ptyp_all (close_ptyp_wrt_ptyp α B')) ⊣ Θ1 }}e.
Proof.
  intros * Hsuf Huq Hγ Hα Hrun.
  eapply e_typing__abs_anno_check_step with (A := close_ptyp_wrt_ptyp α B');
    try eassumption.
  - exact (inter_empty_notin_all _ _ Hγ).
  - rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp. fsetdec.
  - rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp. exact Hrun.
Qed.

Inductive e_typing_order : supply -> mode -> aenv -> pskl -> exp -> Prop :=
| e_typing_order__intro : forall S0 m Θ0 P0 e,

    (forall e1 A, e = exp_anno e1 A ->
       e_typing_order S0 mode_tc Θ0 (ptyp_to_pskl A) e1) ->

    (forall e1, e = exp_freeze e1 ->
       e_typing_order S0 mode_ti Θ0 pskl_ghost e1) ->

    (forall e1, e = exp_abs e1 ->
       forall S1 Θ1 P Q, {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
       forall S2 αs A, e_guess_mono S1 P S2 αs A ->
       e_typing_order (add (supply_fresh S2) S2) (decr_mode m)
         ((supply_fresh S2 ~ abind_var_typ A) ++ αs ++ Θ1) Q
         (open_exp_wrt_exp e1 (exp_var_f (supply_fresh S2)))) ->

    (forall A e1, e = exp_abs_anno A e1 ->
       forall S1 Θ1 P Q, {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
       forall S2 Θ2 Qc,
         {{ S1 ↝ S2 ⊨ Θ1 ⊢[ empty | empty | P ]
            (ptyp_to_pskl A) ∼ Qc ⊣ Θ2 }}e ->
       e_typing_order (add (supply_fresh S2) S2) (decr_mode m)
         ((supply_fresh S2 ~ abind_var_typ A) ++ Θ2) Q
         (open_exp_wrt_exp e1 (exp_var_f (supply_fresh S2)))) ->
    (forall A0, P0 = ptyp_to_pskl (ptyp_all A0) ->
       e_typing_order (add (supply_fresh S0) S0) mode_tc
         ((supply_fresh S0 ~ abind_tvar) ++ Θ0)
         (ptyp_to_pskl
            (open_ptyp_wrt_ptyp A0 (ptyp_var_f (supply_fresh S0))))
         e) ->

    (forall e1, e = exp_abs e1 ->
       forall S1 Θ1 P' Q', {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P' ⇢ Q' ⊣ Θ1 }}e ->
       forall A B, P' = ptyp_to_pskl A -> Q' = ptyp_to_pskl B ->
       e_typing_order (add (supply_fresh S1) S1) mode_tc
         ((supply_fresh S1 ~ abind_var_typ A) ++ Θ1) (ptyp_to_pskl B)
         (open_exp_wrt_exp e1 (exp_var_f (supply_fresh S1)))) ->

    (forall A e1, e = exp_abs_anno A e1 ->
       forall S1 Θ1 P' Q', {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P' ⇢ Q' ⊣ Θ1 }}e ->
       forall S2 Θ2 Qc,
         {{ S1 ↝ S2 ⊨ Θ1 ⊢[ empty | empty | (ptyp_to_pskl A) ]
            P' ∼ Qc ⊣ Θ2 }}e ->
       forall B, Q' = ptyp_to_pskl B ->
       e_typing_order (add (supply_fresh S2) S2) mode_tc
         ((supply_fresh S2 ~ abind_var_typ A) ++ Θ2) (ptyp_to_pskl B)
         (open_exp_wrt_exp e1 (exp_var_f (supply_fresh S2)))) ->

    (forall e1 e2, e = exp_app e1 e2 ->
       e_pat_order S0 mode_tc Θ0 pskl_ghost e2) ->
    (forall e1 e2, e = exp_app e1 e2 ->
       forall S1 Θ1 P,
         {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] e2 ⦂ P ⊣ Θ1 }}e ->
       e_typing_order S1 (mode_fn m) Θ1 (pskl_arrow P P0) e1) ->
    (forall e1 e2, e = exp_app e1 e2 ->
       forall S1 Θ1 P,
         {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] e2 ⦂ P ⊣ Θ1 }}e ->
       forall S2 Θ2 A B,
         {{ S1 ↝ S2 ⊨ Θ1 ⊢[ (mode_fn m) ; (pskl_arrow P P0) ] e1
            ⦂ (ptyp_arrow A B) ⊣ Θ2 }}e ->
       e_typing_order S2 mode_tc Θ2 (ptyp_to_pskl A) e2) ->
    e_typing_order S0 m Θ0 P0 e.

Lemma e_typing_order_total_n : forall n1 n2 S0 m Θ0 P0 e,
  size_exp e <= n1 -> size_pskl P0 <= n2 ->
  e_typing_order S0 m Θ0 P0 e.
Proof.
  induction n1 as [ n1 IH1 ] using lt_wf_ind;
    induction n2 as [ n2 IH2 ] using lt_wf_ind;
    intros * Hsz Hp.
  destruct n1 as [ | n1' ];
    [ pose proof (size_exp_min e); exfalso; lia | ].
  constructor; intros; subst; simpl in Hsz;

    try solve [ apply e_pat_order_total ];

    try match goal with
        | |- e_typing_order _ _ _
               (ptyp_to_pskl (open_ptyp_wrt_ptyp ?A0 _)) _ =>
            eapply (IH2 (size_ptyp A0));
              [ rewrite size_pskl_ptyp_to_pskl in Hp; simpl in Hp; lia
              | exact Hsz
              | rewrite size_pskl_ptyp_to_pskl,
                  size_ptyp_open_ptyp_wrt_ptyp_var; lia ]
        end;

    (match goal with
     | |- e_typing_order _ _ _ _ ?e' => eapply (IH1 (size_exp e'))
     end;
     [ try rewrite size_exp_open_exp_wrt_exp_var; lia
     | apply le_n
     | apply le_n ]).
Qed.

Theorem e_typing_order_total : forall S0 m Θ0 P0 e,
  e_typing_order S0 m Θ0 P0 e.
Proof.
  intros; eapply e_typing_order_total_n; apply le_n.
Qed.

Record typing_result : Type := mk_typing_result {
  ty_supply : supply;
  ty_ctx    : aenv;
  ty_out    : ptyp
}.

Definition typing_spec (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) (r : typing_result) : Prop :=
  {{ S0 ↝ (ty_supply r) ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ (ty_out r)
     ⊣ (ty_ctx r) }}e.

#[local] Hint Resolve supply_fresh_notin mem_true_in mem_false_notin
  lc_pskl_ck_sound lc_ptyp_ck_sound defs_mono_ck_sound
  ptyp_to_pskl_lc pskl_eqb_sound ptyp_eqb_sound suffix_ck_sound
  uniq_ck_sound e_consis_order_total e_sub_order_total
  e_guess_mono_order_total e_consis_defs_mono lc_pskl_all_syn_inv
  e_typing_abs_check_step_close e_typing_abs_anno_check_step_close
  inter_empty_notin_all : typingdec.
#[local] Hint Constructors lc_pskl lc_ptyp : typingdec.
#[local] Hint Extern 4 (_ <> _) => congruence : typingdec.

#[local] Hint Extern 4 (Forall entry_def_mono _) =>
  repeat first [ assumption
               | apply defs_mono_ck_sound; assumption
               | apply Forall_app_intro
               | apply List.Forall_cons
               | apply List.Forall_nil ];
  auto using entry_def_mono_flex, entry_def_mono_tvar,
    entry_def_mono_var_typ, entry_def_mono_var_skl, entry_def_mono_def
  : typingdec.
#[local] Hint Extern 3 (e_consis_chk _ _ _ _ _ _) =>
  (unfold e_consis_chk; eexists; eassumption) : typingdec.

#[local] Ltac typing_impl_tac :=
  cbv zeta; intros;
  try match goal with
      | H : e_typing_order _ _ _ _ _ |- _ => inversion H; subst
      end;
  unfold typing_spec, pat_spec, split_spec, consis_spec, sub_spec,
    guess_spec in *;
  repeat match goal with
         | Hb : _ && _ = true |- _ => apply andb_prop in Hb; destruct Hb
         end;
  repeat match goal with
         | He : pskl_eqb _ _ = true |- _ => apply pskl_eqb_sound in He
         | He : ptyp_eqb _ _ = true |- _ => apply ptyp_eqb_sound in He
         end;
  cbn [ fst snd ty_supply ty_ctx ty_out pt_supply pt_ctx pt_skel
        sp_supply sp_ctx sp_dom sp_cod sb_supply sb_ctx sb_out
        cs_supply cs_ctx cs_out gr_supply gr_block gr_type ] in *;
  try subst;
  repeat match goal with
         | Hc : snd (fst _) = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : ty_ctx _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : ty_out _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : pt_ctx _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : pt_skel _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : sp_dom _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : sp_cod _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : sb_out _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : gr_type _ = _ |- _ => rewrite Hc in *; clear Hc
         end;
  try congruence;
  try solve [ eauto 7 with typingdec ];
  solve [ econstructor; eauto 6 with typingdec ].

#[tactic="typing_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_typing_impl (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) (H : e_typing_order S0 m Θ0 P0 e)
    : option (sig (typing_spec S0 m Θ0 P0 e)) by struct H :=

| S0, m, Θ0, P0, exp_unit, H =>
    match sumbool_of_bool (degree_pskl_ck 0 P0 && defs_mono_ck Θ0) with
    | right _ => None
    | left _ =>
        match e_sub_impl S0 a_sub_mode_ty m P0 Θ0 pskl_unit _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            match pskl_readback (sb_out r) with
            | None => None
            | Some (exist _ A HA) =>
                Some (exist _ (mk_typing_result (sb_supply r) (sb_ctx r)
                        A) _)
            end
        end
    end

| S0, m, Θ0, P0, exp_var_f x, H =>
    match lookup_binding x Θ0 with
    | None => None
    | Some (exist _ b Hb) =>
      match abind_var_typ_get b with
      | None => None
      | Some (exist _ A HA) =>
        match sumbool_of_bool (degree_ptyp_ck 0 A && degree_pskl_ck 0 P0
                               && defs_mono_ck Θ0) with
        | right _ => None
        | left _ =>
            match e_sub_impl S0 a_sub_mode_ty m P0 Θ0 (ptyp_to_pskl A)
                    _ _ _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                match pskl_readback (sb_out r) with
                | None => None
                | Some (exist _ B HB) =>
                    Some (exist _ (mk_typing_result (sb_supply r)
                            (sb_ctx r) B) _)
                end
            end
        end
      end
    end

| S0, m, Θ0, P0, exp_anno e1 A, H =>
    match e_typing_impl S0 mode_tc Θ0 (ptyp_to_pskl A) e1 _ with
    | None => None
    | Some (exist _ r1 Hr1) =>
        match sumbool_of_bool (ptyp_eqb (ty_out r1) A) with
        | right _ => None
        | left _ =>
            match sumbool_of_bool (degree_ptyp_ck 0 A
                                   && degree_pskl_ck 0 P0
                                   && defs_mono_ck (ty_ctx r1)) with
            | right _ => None
            | left _ =>
                match e_sub_impl (ty_supply r1) a_sub_mode_ty m P0
                        (ty_ctx r1) (ptyp_to_pskl A) _ _ _ _ with
                | None => None
                | Some (exist _ r Hr) =>
                    match pskl_readback (sb_out r) with
                    | None => None
                    | Some (exist _ B HB) =>
                        Some (exist _ (mk_typing_result (sb_supply r)
                                (sb_ctx r) B) _)
                    end
                end
            end
        end
    end

| S0, mode_tc, Θ0, P0, exp_freeze e1, H =>
    match pskl_readback P0 with
    | None => None
    | Some (exist _ A HA) =>
        match e_typing_impl S0 mode_ti Θ0 pskl_ghost e1 _ with
        | None => None
        | Some (exist _ r1 Hr1) =>
            match sumbool_of_bool (degree_ptyp_ck 0 (ty_out r1)
                                   && degree_ptyp_ck 0 A
                                   && defs_mono_ck (ty_ctx r1)) with
            | right _ => None
            | left _ =>
                match e_consis_impl empty empty (ty_supply r1) (ty_ctx r1)
                        (ptyp_to_pskl A) (ptyp_to_pskl (ty_out r1))
                        _ _ _ _ with
                | None => None
                | Some (exist _ rc Hrc) =>
                    Some (exist _ (mk_typing_result (cs_supply rc)
                            (cs_ctx rc) A) _)
                end
            end
        end
    end
| S0, m, Θ0, P0, exp_freeze e1, H => None

| S0, mode_ti, Θ0, P0, exp_abs e1, H =>
    match e_split_impl S0 Θ0 P0 with
    | None => None
    | Some (exist _ rs Hrs) =>
        match sumbool_of_bool (degree_pskl_ck 0 (sp_dom rs)) with
        | right _ => None
        | left _ =>
            let (rg, Hrg) := e_guess_mono_impl (sp_supply rs) (sp_dom rs)
                               _ in
            match e_typing_impl
                    (add (supply_fresh (gr_supply rg)) (gr_supply rg))
                    (decr_mode mode_ti)
                    ((supply_fresh (gr_supply rg)
                        ~ abind_var_typ (gr_type rg))
                       ++ gr_block rg ++ sp_ctx rs)
                    (sp_cod rs)
                    (open_exp_wrt_exp e1
                       (exp_var_f (supply_fresh (gr_supply rg)))) _ with
            | None => None
            | Some (exist _ r Hr) =>
                match split_at_key_typ (supply_fresh (gr_supply rg))
                        (ty_ctx r) with
                | None => None
                | Some (exist _ t HΘ) =>
                    match sumbool_of_bool
                            (ptyp_eqb (snd (fst t)) (gr_type rg)
                             && suffix_ck (fst (fst t))) with
                    | right _ => None
                    | left _ =>
                        Some (exist _ (mk_typing_result (ty_supply r)
                                (fst (fst t) ++ snd t)
                                (ptyp_arrow (gr_type rg) (ty_out r))) _)
                    end
                end
            end
        end
    end
| S0, mode_fn m', Θ0, P0, exp_abs e1, H =>
    match e_split_impl S0 Θ0 P0 with
    | None => None
    | Some (exist _ rs Hrs) =>
        match sumbool_of_bool (degree_pskl_ck 0 (sp_dom rs)) with
        | right _ => None
        | left _ =>
            let (rg, Hrg) := e_guess_mono_impl (sp_supply rs) (sp_dom rs)
                               _ in
            match e_typing_impl
                    (add (supply_fresh (gr_supply rg)) (gr_supply rg))
                    (decr_mode (mode_fn m'))
                    ((supply_fresh (gr_supply rg)
                        ~ abind_var_typ (gr_type rg))
                       ++ gr_block rg ++ sp_ctx rs)
                    (sp_cod rs)
                    (open_exp_wrt_exp e1
                       (exp_var_f (supply_fresh (gr_supply rg)))) _ with
            | None => None
            | Some (exist _ r Hr) =>
                match split_at_key_typ (supply_fresh (gr_supply rg))
                        (ty_ctx r) with
                | None => None
                | Some (exist _ t HΘ) =>
                    match sumbool_of_bool
                            (ptyp_eqb (snd (fst t)) (gr_type rg)
                             && suffix_ck (fst (fst t))) with
                    | right _ => None
                    | left _ =>
                        Some (exist _ (mk_typing_result (ty_supply r)
                                (fst (fst t) ++ snd t)
                                (ptyp_arrow (gr_type rg) (ty_out r))) _)
                    end
                end
            end
        end
    end

| S0, mode_tc, Θ0, P0, exp_abs e1, H =>
    match pskl_readback_all P0 with
    | Some (exist _ A0 HA0) =>
        match e_typing_impl (add (supply_fresh S0) S0) mode_tc
                ((supply_fresh S0 ~ abind_tvar) ++ Θ0)
                (ptyp_to_pskl
                   (open_ptyp_wrt_ptyp A0
                      (ptyp_var_f (supply_fresh S0))))
                (exp_abs e1) _ with
        | None => None
        | Some (exist _ r Hr) =>
            match split_at_tvar (supply_fresh S0) (ty_ctx r) with
            | None => None
            | Some (exist _ p Hp) =>
                match sumbool_of_bool
                        (suffix_ck (fst p) && uniq_ck (fst p ++ Θ0)
                         && is_empty
                              (inter (dom (fst p))
                                 (ftvar_in_ptyp
                                    (close_ptyp_wrt_ptyp
                                       (supply_fresh S0) (ty_out r)))))
                with
                | right _ => None
                | left _ =>
                    Some (exist _ (mk_typing_result (ty_supply r) (snd p)
                            (ptyp_all
                               (close_ptyp_wrt_ptyp (supply_fresh S0)
                                  (ty_out r)))) _)
                end
            end
        end
    | None =>
      match pskl_readback P0 with
      | None => None
      | Some (exist _ A0 HA0) =>
        match e_split_impl S0 Θ0 P0 with
        | None => None
        | Some (exist _ rs Hrs) =>
            match pskl_readback (sp_dom rs) with
            | None => None
            | Some (exist _ A HA) =>
                match pskl_readback (sp_cod rs) with
                | None => None
                | Some (exist _ B HB) =>
                    match e_typing_impl
                            (add (supply_fresh (sp_supply rs))
                               (sp_supply rs))
                            mode_tc
                            ((supply_fresh (sp_supply rs)
                                ~ abind_var_typ A) ++ sp_ctx rs)
                            (ptyp_to_pskl B)
                            (open_exp_wrt_exp e1
                               (exp_var_f
                                  (supply_fresh (sp_supply rs)))) _ with
                    | None => None
                    | Some (exist _ r Hr) =>
                        match split_at_key_typ
                                (supply_fresh (sp_supply rs))
                                (ty_ctx r) with
                        | None => None
                        | Some (exist _ t HΘ) =>
                            match sumbool_of_bool
                                    (ptyp_eqb (snd (fst t)) A
                                     && suffix_ck (fst (fst t))
                                     && uniq_ck (fst (fst t) ++ sp_ctx rs)
                                     && is_empty
                                          (inter (dom (fst (fst t)))
                                             (ftvar_in_ptyp
                                                (ty_out r)))) with
                            | right _ => None
                            | left _ =>
                                Some (exist _ (mk_typing_result
                                        (ty_supply r) (snd t)
                                        (ptyp_arrow A (ty_out r))) _)
                            end
                        end
                    end
                end
            end
        end
      end
    end

| S0, mode_ti, Θ0, P0, exp_abs_anno A e1, H =>
    match e_split_impl S0 Θ0 P0 with
    | None => None
    | Some (exist _ rs Hrs) =>
        match sumbool_of_bool (degree_ptyp_ck 0 A
                               && degree_pskl_ck 0 (sp_dom rs)
                               && defs_mono_ck (sp_ctx rs)) with
        | right _ => None
        | left _ =>
            match e_consis_impl empty empty (sp_supply rs) (sp_ctx rs)
                    (sp_dom rs) (ptyp_to_pskl A) _ _ _ _ with
            | None => None
            | Some (exist _ rc Hrc) =>
                match e_typing_impl
                        (add (supply_fresh (cs_supply rc)) (cs_supply rc))
                        (decr_mode mode_ti)
                        ((supply_fresh (cs_supply rc) ~ abind_var_typ A)
                           ++ cs_ctx rc)
                        (sp_cod rs)
                        (open_exp_wrt_exp e1
                           (exp_var_f
                              (supply_fresh (cs_supply rc)))) _ with
                | None => None
                | Some (exist _ r Hr) =>
                    match split_at_key_typ (supply_fresh (cs_supply rc))
                            (ty_ctx r) with
                    | None => None
                    | Some (exist _ t HΘ) =>
                        match sumbool_of_bool
                                (ptyp_eqb (snd (fst t)) A
                                 && suffix_ck (fst (fst t))) with
                        | right _ => None
                        | left _ =>
                            Some (exist _ (mk_typing_result (ty_supply r)
                                    (fst (fst t) ++ snd t)
                                    (ptyp_arrow A (ty_out r))) _)
                        end
                    end
                end
            end
        end
    end
| S0, mode_fn m', Θ0, P0, exp_abs_anno A e1, H =>
    match e_split_impl S0 Θ0 P0 with
    | None => None
    | Some (exist _ rs Hrs) =>
        match sumbool_of_bool (degree_ptyp_ck 0 A
                               && degree_pskl_ck 0 (sp_dom rs)
                               && defs_mono_ck (sp_ctx rs)) with
        | right _ => None
        | left _ =>
            match e_consis_impl empty empty (sp_supply rs) (sp_ctx rs)
                    (sp_dom rs) (ptyp_to_pskl A) _ _ _ _ with
            | None => None
            | Some (exist _ rc Hrc) =>
                match e_typing_impl
                        (add (supply_fresh (cs_supply rc)) (cs_supply rc))
                        (decr_mode (mode_fn m'))
                        ((supply_fresh (cs_supply rc) ~ abind_var_typ A)
                           ++ cs_ctx rc)
                        (sp_cod rs)
                        (open_exp_wrt_exp e1
                           (exp_var_f
                              (supply_fresh (cs_supply rc)))) _ with
                | None => None
                | Some (exist _ r Hr) =>
                    match split_at_key_typ (supply_fresh (cs_supply rc))
                            (ty_ctx r) with
                    | None => None
                    | Some (exist _ t HΘ) =>
                        match sumbool_of_bool
                                (ptyp_eqb (snd (fst t)) A
                                 && suffix_ck (fst (fst t))) with
                        | right _ => None
                        | left _ =>
                            Some (exist _ (mk_typing_result (ty_supply r)
                                    (fst (fst t) ++ snd t)
                                    (ptyp_arrow A (ty_out r))) _)
                        end
                    end
                end
            end
        end
    end

| S0, mode_tc, Θ0, P0, exp_abs_anno A e1, H =>
    match pskl_readback_all P0 with
    | Some (exist _ A0 HA0) =>
        match e_typing_impl (add (supply_fresh S0) S0) mode_tc
                ((supply_fresh S0 ~ abind_tvar) ++ Θ0)
                (ptyp_to_pskl
                   (open_ptyp_wrt_ptyp A0
                      (ptyp_var_f (supply_fresh S0))))
                (exp_abs_anno A e1) _ with
        | None => None
        | Some (exist _ r Hr) =>
            match split_at_tvar (supply_fresh S0) (ty_ctx r) with
            | None => None
            | Some (exist _ p Hp) =>
                match sumbool_of_bool
                        (suffix_ck (fst p) && uniq_ck (fst p ++ Θ0)
                         && is_empty
                              (inter (dom (fst p))
                                 (ftvar_in_ptyp
                                    (close_ptyp_wrt_ptyp
                                       (supply_fresh S0) (ty_out r)))))
                with
                | right _ => None
                | left _ =>
                    Some (exist _ (mk_typing_result (ty_supply r) (snd p)
                            (ptyp_all
                               (close_ptyp_wrt_ptyp (supply_fresh S0)
                                  (ty_out r)))) _)
                end
            end
        end
    | None =>
      match pskl_readback P0 with
      | None => None
      | Some (exist _ A0 HA0) =>
        match e_split_impl S0 Θ0 P0 with
        | None => None
        | Some (exist _ rs Hrs) =>
            match pskl_readback (sp_dom rs) with
            | None => None
            | Some (exist _ A' HA') =>
                match pskl_readback (sp_cod rs) with
                | None => None
                | Some (exist _ B HB) =>
                    match sumbool_of_bool
                            (degree_ptyp_ck 0 A
                             && degree_pskl_ck 0 (sp_dom rs)
                             && defs_mono_ck (sp_ctx rs)) with
                    | right _ => None
                    | left _ =>
                        match e_consis_impl empty empty (sp_supply rs)
                                (sp_ctx rs) (ptyp_to_pskl A) (sp_dom rs)
                                _ _ _ _ with
                        | None => None
                        | Some (exist _ rc Hrc) =>
                            match e_typing_impl
                                    (add (supply_fresh (cs_supply rc))
                                       (cs_supply rc))
                                    mode_tc
                                    ((supply_fresh (cs_supply rc)
                                        ~ abind_var_typ A)
                                       ++ cs_ctx rc)
                                    (ptyp_to_pskl B)
                                    (open_exp_wrt_exp e1
                                       (exp_var_f
                                          (supply_fresh
                                             (cs_supply rc)))) _ with
                            | None => None
                            | Some (exist _ r Hr) =>
                                match split_at_key_typ
                                        (supply_fresh (cs_supply rc))
                                        (ty_ctx r) with
                                | None => None
                                | Some (exist _ t HΘ) =>
                                    match sumbool_of_bool
                                            (ptyp_eqb (snd (fst t)) A
                                             && suffix_ck (fst (fst t))
                                             && uniq_ck
                                                  (fst (fst t)
                                                     ++ cs_ctx rc)
                                             && is_empty
                                                  (inter
                                                     (dom (fst (fst t)))
                                                     (ftvar_in_ptyp
                                                        (ty_out r))))
                                    with
                                    | right _ => None
                                    | left _ =>
                                        Some (exist _
                                                (mk_typing_result
                                                   (ty_supply r) (snd t)
                                                   (ptyp_arrow A'
                                                      (ty_out r))) _)
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
      end
    end

| S0, m, Θ0, P0, exp_app e1 e2, H =>
    match e_pat_impl S0 mode_tc Θ0 pskl_ghost e2 _ with
    | None => None
    | Some (exist _ r2 Hr2) =>
        match e_typing_impl (pt_supply r2) (mode_fn m) (pt_ctx r2)
                (pskl_arrow (pt_skel r2) P0) e1 _ with
        | None => None
        | Some (exist _ r1 Hr1) =>
            match ptyp_arrow_split (ty_out r1) with
            | None => None
            | Some (exist _ p Hp) =>
                match e_typing_impl (ty_supply r1) mode_tc (ty_ctx r1)
                        (ptyp_to_pskl (fst p)) e2 _ with
                | None => None
                | Some (exist _ r3 Hr3) =>
                    Some (exist _ (mk_typing_result (ty_supply r3)
                            (ty_ctx r3) (snd p)) _)
                end
            end
        end
    end

| S0, m, Θ0, P0, exp_var_b n, H => None.

Definition e_typing_run (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) : option typing_result :=
  match e_typing_impl S0 m Θ0 P0 e (e_typing_order_total S0 m Θ0 P0 e) with
  | Some r => Some (proj1_sig r)
  | None => None
  end.

Lemma e_typing_run_sound : forall S0 m Θ0 P0 e r,
  e_typing_run S0 m Θ0 P0 e = Some r ->
  {{ S0 ↝ (ty_supply r) ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ (ty_out r)
     ⊣ (ty_ctx r) }}e.
Proof.
  intros *. unfold e_typing_run.
  destruct (e_typing_impl S0 m Θ0 P0 e (e_typing_order_total S0 m Θ0 P0 e))
    as [ [r' Hr'] | ];
    intro Heq; inversion Heq; subst; exact Hr'.
Qed.
