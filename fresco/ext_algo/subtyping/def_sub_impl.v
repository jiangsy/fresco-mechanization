Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
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
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.subtyping.def_look_impl.
Require Import src.fresco.ext_algo.subtyping.def_solve_impl.
Require Import src.fresco.ext_algo.subtyping.def_extract_impl.
Require Import src.fresco.ext_algo.consistency.def_consis_impl.

Set Equations With UIP.

Open Scope fresco_e_scope.

Definition abind_is_tvar_dec (b : abind)
    : sumbool (b = abind_tvar) (b <> abind_tvar).
Proof.
  destruct b; first [ left; reflexivity | right; discriminate ].
Defined.

Definition split_at_tvar (α : atom)
    : forall Θ : aenv,
      option (sig (fun p : aenv * aenv
                   => Θ = fst p ++ (α ~ abind_tvar) ++ snd p)).
Proof.
  refine (fix go (Θ : aenv)
      : option (sig (fun p : aenv * aenv
                     => Θ = fst p ++ (α ~ abind_tvar) ++ snd p)) :=
    match Θ with
    | nil => None
    | (β, b) :: Θ' =>
        match abind_is_tvar_dec b with
        | left Hb =>
            match α == β with
            | left Heq => Some (exist _ (nil, Θ') _)
            | right _ =>
                match go Θ' with
                | Some (exist _ p Hp) =>
                    Some (exist _ ((β, b) :: fst p, snd p) _)
                | None => None
                end
            end
        | right _ =>
            match go Θ' with
            | Some (exist _ p Hp) =>
                Some (exist _ ((β, b) :: fst p, snd p) _)
            | None => None
            end
        end
    end).
  all: simpl;
       repeat match goal with
              | Hb' : _ = abind_tvar |- _ => rewrite Hb'; clear Hb'
              end;
       first [ reflexivity
             | match goal with
               | Hp' : _ = _ ++ _ |- _ => rewrite Hp' at 1; reflexivity
               end
             | match goal with
               | Heq' : _ = _ |- _ => rewrite Heq'; reflexivity
               end ].
Defined.

Record sub_result : Type := mk_sub_result {
  sb_supply : supply;
  sb_ctx    : aenv;
  sb_out    : pskl
}.

Definition sub_spec (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (P : pskl) (r : sub_result) : Prop :=
  {{ S0 ↝ (sb_supply r) ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ (sb_out r)
     ⊣ (sb_ctx r) }}e.

Definition sub_flex_spec (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 Ξ : aenv) (α : atom) (r : sub_result) : Prop :=
  e_sub_flex S0 NM M P0 Θ0 Ξ α (sb_out r) (sb_supply r) (sb_ctx r).

Inductive sub_call : Set :=
| sub_call_sub  (P : pskl)
| sub_call_flex (Ξ : aenv) (α : atom).

Derive NoConfusion for sub_call.

Definition sub_call_spec (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (c : sub_call) : sub_result -> Prop :=
  match c with
  | sub_call_sub P    => sub_spec S0 NM M P0 Θ0 P
  | sub_call_flex Ξ α => sub_flex_spec S0 NM M P0 Θ0 Ξ α
  end.

Definition sub_call_lc (c : sub_call) : Prop :=
  match c with
  | sub_call_sub P    => lc_pskl P
  | sub_call_flex _ _ => True
  end.

Definition sub_call_defs_mono (Θ0 : aenv) (c : sub_call) : Prop :=
  match c with
  | sub_call_sub _    => aenv_defs_mono Θ0
  | sub_call_flex Ξ _ => aenv_defs_mono (Ξ ++ Θ0)
  end.

Inductive e_sub_call_order : supply -> a_sub_mode -> mode -> pskl -> aenv
                             -> sub_call -> Prop :=
| e_sub_call_order__sub : forall S0 NM M P0 Θ0 P,

    (M = mode_tc -> e_consis_order empty empty S0 Θ0 P0 P) ->

    (forall B,
       M = mode_tc -> P0 = pskl_all_syn B ->
       e_sub_call_order (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
         ((supply_fresh S0 ~ abind_tvar) ++ Θ0) (sub_call_sub P)) ->

    (forall α M',
       P = pskl_var_f α -> M = mode_fn M' ->
       e_sub_call_order S0 NM M' P0 Θ0 (sub_call_flex nil α)) ->

    (forall M' P0a P0b P1 P2,
       M = mode_fn M' -> P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_order empty empty S0 Θ0 P0a P1) ->
    (forall M' P0a P0b P1 P2,
       M = mode_fn M' -> P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       forall S1 Θ1 Q1,
         {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
         e_sub_call_order S1 NM M' P0b Θ1 (sub_call_sub P2)) ->

    (forall Q,
       P = pskl_all_syn Q -> M <> mode_ti ->
       (guarded_pskl P0 \/ P0 = pskl_ghost) ->
       e_extract_order (add (supply_fresh S0) S0) Θ0 NM (supply_fresh S0) M
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0))) P0) ->
    (forall Q,
       P = pskl_all_syn Q -> M <> mode_ti ->
       (guarded_pskl P0 \/ P0 = pskl_ghost) ->
       forall S1 Ξ P1,
         {{ (add (supply_fresh S0) S0) ↝ S1 ⊨ Θ0
            ⊢ (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
            ⊳[ NM , (supply_fresh S0) , M ] P0 ⤳ Ξ ↪ P1 }}e ->
         {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
         e_sub_call_order S1 NM M P0 (Ξ ++ Θ0)
           (sub_call_sub (open_pskl_wrt_pskl Q P1))) ->

    (forall Q,
       P = pskl_univ_ghost Q -> M <> mode_ti ->
       e_sub_call_order S0 NM M P0 Θ0 (sub_call_sub Q)) ->
    e_sub_call_order S0 NM M P0 Θ0 (sub_call_sub P)

| e_sub_call_order__flex : forall S0 NM M P0 Θ0 Ξ α,

    (forall Θ0',
       Θ0 = (α ~ abind_flex_mono) ++ Θ0' ->
       e_sub_call_order
         (add (supply_fresh (add (supply_fresh S0) S0))
            (add (supply_fresh S0) S0))
         NM (mode_fn M) P0
         (Ξ ++ (α ~ abind_flex_mono_def
                      (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                         (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
             ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
             ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
         (sub_call_sub
            (pskl_arrow (pskl_var_f (supply_fresh S0))
               (pskl_var_f (supply_fresh (add (supply_fresh S0) S0)))))) ->

    (forall β τ Θ0',
       Θ0 = (β ~ abind_flex_mono_def τ) ++ Θ0' ->
       e_sub_call_order S0 NM (mode_fn M)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
         (Ξ ++ Θ0')
         (sub_call_sub
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->

    (forall β Θ0',
       Θ0 = (β ~ abind_flex_mono) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0'
         (sub_call_flex (Ξ ++ (β ~ abind_flex_mono)) α)) ->
    (forall β Θ0',
       Θ0 = (β ~ abind_flex_mono) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->

    (forall β Θ0',
       Θ0 = (β ~ abind_tvar) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->

    (forall x A Θ0',
       Θ0 = (x ~ abind_var_typ A) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall x Q Θ0',
       Θ0 = (x ~ abind_var_skl Q) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    e_sub_call_order S0 NM M P0 Θ0 (sub_call_flex Ξ α).

Derive Signature for e_sub_call_order.

Fixpoint e_sub_order_to_call S0 NM M P0 Θ0 P
    (H : e_sub_order S0 NM M P0 Θ0 P) {struct H}
  : e_sub_call_order S0 NM M P0 Θ0 (sub_call_sub P) :=
  match H with
  | e_sub_order__intro _ _ _ _ _ _ Hck Hfr Hfm Har Hfl Hug =>
      e_sub_call_order__sub _ _ _ _ _ _
        Hck
        (fun B E1 E2 =>
           e_sub_order_to_call _ _ _ _ _ _ (Hfr B E1 E2))
        (fun α M' E1 E2 =>
           e_sub_flex_order_to_call _ _ _ _ _ _ _ (Hfm α M' E1 E2))
        (fun M' P0a P0b P1 P2 E1 E2 E3 =>
           proj1 (Har M' P0a P0b P1 P2 E1 E2 E3))
        (fun M' P0a P0b P1 P2 E1 E2 E3 S1 Θ1 Q1 Hrun =>
           match Har M' P0a P0b P1 P2 E1 E2 E3 with
           | conj _ Hrec => e_sub_order_to_call _ _ _ _ _ _ (Hrec S1 Θ1 Q1 Hrun)
           end)
        (fun Q E1 E2 Hg => proj1 (Hfl Q E1 E2 Hg))
        (fun Q E1 E2 Hg S1 Ξ' P1 Hrun Hwf =>
           match Hfl Q E1 E2 Hg with
           | conj _ Hrec => e_sub_order_to_call _ _ _ _ _ _ (Hrec S1 Ξ' P1 Hrun Hwf)
           end)
        (fun Q E1 E2 =>
           e_sub_order_to_call _ _ _ _ _ _ (Hug Q E1 E2))
  end
with e_sub_flex_order_to_call S0 NM M P0 Θ0 Ξ α
    (H : e_sub_flex_order S0 NM M P0 Θ0 Ξ α) {struct H}
  : e_sub_call_order S0 NM M P0 Θ0 (sub_call_flex Ξ α) :=
  match H with
  | e_sub_flex_order__intro _ _ _ _ _ _ _ Hsv Has Hds Hrg Htv Hts =>
      e_sub_call_order__flex _ _ _ _ _ _ _
        (fun Θ0' E =>
           e_sub_order_to_call _ _ _ _ _ _ (Hsv Θ0' E))
        (fun β τ Θ0' E =>
           e_sub_order_to_call _ _ _ _ _ _ (Has β τ Θ0' E))
        (fun β Θ0' E =>
           match Hds β Θ0' E with conj h1 _ => e_sub_flex_order_to_call _ _ _ _ _ _ _ h1 end)
        (fun β Θ0' E =>
           match Hds β Θ0' E with conj _ h2 => e_sub_flex_order_to_call _ _ _ _ _ _ _ h2 end)
        (fun β Θ0' E =>
           e_sub_flex_order_to_call _ _ _ _ _ _ _ (Hrg β Θ0' E))
        (fun x A Θ0' E =>
           e_sub_flex_order_to_call _ _ _ _ _ _ _ (Htv x A Θ0' E))
        (fun x Q Θ0' E =>
           e_sub_flex_order_to_call _ _ _ _ _ _ _ (Hts x Q Θ0' E))
  end.

#[local] Hint Resolve supply_fresh_notin mem_true_in mem_false_notin
  guarded_shape_ck_sound ghost_free_ck_sound ghost_ck_sound
  suffix_ck_sound uniq_ck_sound wf_pskl_ck_sound a_wf_pskl_lc
  lc_pskl_all_syn_inv lc_pskl_open_graft
  subst_pskl_in_pskl_lc_pskl mono_ptyp_to_pskl_lc mono_ptyp_lc
  e_consis_defs_mono e_extract_block_flex all_flex_mono_defs_mono
  e_guess_run_sound : subdec.
#[local] Hint Constructors lc_pskl guarded_pskl : subdec.
#[local] Hint Extern 3 (e_consis_chk _ _ _ _ _ _) =>
  (unfold e_consis_chk; eexists; eassumption) : subdec.
#[local] Hint Extern 4 (_ <> _) => congruence : subdec.

#[local] Hint Extern 4 (Forall entry_def_mono _) =>
  repeat first [ assumption
               | apply all_flex_mono_defs_mono; eassumption
               | apply Forall_app_intro
               | apply List.Forall_cons
               | apply List.Forall_nil ];
  auto using entry_def_mono_flex, entry_def_mono_tvar,
    entry_def_mono_var_typ, entry_def_mono_var_skl, entry_def_mono_def,
    mono_ptyp__arrow, mono_ptyp__var, mono_ptyp__unit
  : subdec.

#[local] Ltac select_shape_premises :=
  repeat match goal with
         | Hp : forall _ _ _ _ _, _ = _ -> _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ _ _ eq_refl eq_refl eq_refl)
                   | clear Hp ]
         | Hp : forall _ _ _, _ = _ -> _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ eq_refl eq_refl eq_refl)
                   | clear Hp ]
         | Hp : forall _ _ _ _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _ _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _ _ _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ eq_refl) | clear Hp ]
         | Hp : forall _ _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ eq_refl) | clear Hp ]
         | Hp : forall _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ eq_refl) | clear Hp ]
         | Hp : ?m = ?m -> _ |- _ => specialize (Hp eq_refl)
         | Hp : mode_tc = mode_tc -> _ |- _ => specialize (Hp eq_refl)
         | Hp : _ = _ -> _ |- _ =>
             lazymatch type of Hp with
             | not _ => fail
             | _ <> _ -> _ => fail
             | _ => first [ specialize (Hp eq_refl) | clear Hp ]
             end
         | Hp : ?A <> ?B -> _ |- _ =>
             let Hne := fresh "Hne0" in
             assert (Hne : A <> B) by congruence;
             specialize (Hp Hne); clear Hne
         | Hp : (guarded_pskl ?P \/ ?P = pskl_ghost) -> _ |- _ =>
             let Hd := fresh "Hd0" in
             assert (Hd : guarded_pskl P \/ P = pskl_ghost)
               by (solve [ left; apply guarded_shape_ck_sound; assumption
                         | right; apply ghost_ck_sound; assumption
                         | right; reflexivity ]);
             specialize (Hp Hd); clear Hd
         | Hp : _ /\ _ |- _ => destruct Hp
         end.

#[local] Ltac saturate_defs :=
  repeat match goal with
         | HF : Forall _ (_ ++ _) |- _ =>
             apply Forall_app in HF; destruct HF
         | HF : Forall _ (_ :: _) |- _ => inversion HF; subst; clear HF
         | HF : Forall _ (one _) |- _ => inversion HF; subst; clear HF
         end.

#[local] Ltac sub_impl_tac :=
  cbv zeta; intros;
  try match goal with
      | H : e_sub_call_order _ _ _ _ _ _ |- _ => inversion H; subst
      end;
  try match goal with
      | Hlc : lc_pskl (pskl_var_b _) |- _ => inversion Hlc
      end;
  unfold sub_call_spec, sub_call_lc, sub_call_defs_mono,
         sub_spec, sub_flex_spec, consis_spec, extract_spec in *;
  cbv beta iota in *;
  repeat match goal with
         | He : pskl_eqb _ _ = true |- _ => apply pskl_eqb_sound in He
         end;
  repeat match goal with
         | Hc : sb_ctx _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : sb_out _ = _ |- _ => rewrite Hc in *; clear Hc
         end;
  repeat match goal with
         | Hb : _ && _ = true |- _ => apply andb_prop in Hb; destruct Hb
         | Hb : _ || _ = true |- _ => apply orb_prop in Hb; destruct Hb
         end;
  select_shape_premises; saturate_defs; saturate_lc; simpl in *;

  repeat match goal with
         | |- context [ if ?c then _ else _ ] => destruct c
         end;
  try congruence;
  try solve [ eauto 7 with subdec ];
  solve [ econstructor; eauto 6 with subdec ].

#[tactic="sub_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_sub_call_impl (c : sub_call) (S0 : supply) (NM : a_sub_mode)
    (M : mode) (P0 : pskl) (Θ0 : aenv)
    (HP : sub_call_lc c) (HP0 : lc_pskl P0) (HD : sub_call_defs_mono Θ0 c)
    (H : e_sub_call_order S0 NM M P0 Θ0 c)
    : option (sig (sub_call_spec S0 NM M P0 Θ0 c)) by struct H :=

| sub_call_sub P, S0, NM, M, P0, Θ0, HP, HP0, HD, H =>
  match M as M1 return M = M1
      -> option (sig (sub_call_spec S0 NM M P0 Θ0 (sub_call_sub P))) with

  | mode_ti => fun EM =>
      match P0 as P01 return P0 = P01
          -> option (sig (sub_call_spec S0 NM M P0 Θ0 (sub_call_sub P)))
      with
      | pskl_ghost => fun EP0 => Some (exist _ (mk_sub_result S0 Θ0 P) _)
      | _ => fun _ => None
      end eq_refl

  | mode_tc => fun EM =>
      match NM as NM1 return NM = NM1
          -> option (sig (sub_call_spec S0 NM M P0 Θ0 (sub_call_sub P)))
      with
      | a_sub_mode_ty => fun ENM =>
          match P0 as P01 return P0 = P01
              -> option (sig (sub_call_spec S0 NM M P0 Θ0 (sub_call_sub P)))
          with

          | pskl_all_syn B => fun EP0 =>
              match sumbool_of_bool (ghost_free_ck (pskl_all_syn B)) with
              | right _ => None
              | left _ =>
                  match e_sub_call_impl (sub_call_sub P)
                          (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
                          (open_pskl_wrt_pskl B
                             (pskl_var_f (supply_fresh S0)))
                          ((supply_fresh S0 ~ abind_tvar) ++ Θ0)
                          _ _ _ _ with
                  | None => None
                  | Some (exist _ r Hr) =>
                      match sumbool_of_bool
                              (pskl_eqb (sb_out r)
                                 (open_pskl_wrt_pskl B
                                    (pskl_var_f (supply_fresh S0)))) with
                      | right _ => None
                      | left _ =>
                          match split_at_tvar (supply_fresh S0)
                                  (sb_ctx r) with
                          | None => None
                          | Some (exist _ p Hp) =>
                              match sumbool_of_bool
                                      (suffix_ck (fst p)
                                       && uniq_ck (fst p ++ Θ0)) with
                              | right _ => None
                              | left _ =>
                                  Some (exist _ (mk_sub_result
                                          (sb_supply r) (snd p)
                                          (pskl_all_syn B)) _)
                              end
                          end
                      end
                  end
              end
          | _ => fun EP0 =>
              match P as P1 return P = P1
                  -> option (sig (sub_call_spec S0 NM M P0 Θ0
                                    (sub_call_sub P)))
              with

              | pskl_all_syn Q => fun EP =>
                  match sumbool_of_bool (guarded_shape_ck P0 || ghost_ck P0)
                  with
                  | right _ => None
                  | left _ =>
                      match e_extract_impl (add (supply_fresh S0) S0) Θ0 NM
                              (supply_fresh S0) mode_tc
                              (open_pskl_wrt_pskl Q
                                 (pskl_var_f (supply_fresh S0))) P0
                              _ _ _ with
                      | None => None
                      | Some (exist _ rx Hrx) =>
                          match sumbool_of_bool
                                  (wf_pskl_ck (size_pskl (ex_out rx))
                                     (ex_block rx ++ Θ0) empty (ex_out rx))
                          with
                          | right _ => None
                          | left _ =>
                              match e_sub_call_impl
                                      (sub_call_sub
                                         (open_pskl_wrt_pskl Q (ex_out rx)))
                                      (ex_supply rx) NM mode_tc P0
                                      (ex_block rx ++ Θ0) _ _ _ _ with
                              | None => None
                              | Some (exist _ r Hr) => Some (exist _ r _)
                              end
                          end
                      end
                  end

              | _ => fun EP =>
                  match sumbool_of_bool
                          (ghost_free_ck P && ghost_free_ck P0
                           && guarded_shape_ck P && guarded_shape_ck P0)
                  with
                  | right _ => None
                  | left _ =>
                      match e_consis_impl empty empty S0 Θ0 P0 P _ _ _ _
                      with
                      | None => None
                      | Some (exist _ r Hr) =>
                          Some (exist _ (mk_sub_result (cs_supply r)
                                  (cs_ctx r) P0) _)
                      end
                  end
              end eq_refl
          end eq_refl
      | a_sub_mode_sk => fun ENM =>
          match P as P1 return P = P1
              -> option (sig (sub_call_spec S0 NM M P0 Θ0 (sub_call_sub P)))
          with

          | pskl_all_syn Q => fun EP =>
              match sumbool_of_bool (guarded_shape_ck P0 || ghost_ck P0) with
              | right _ => None
              | left _ =>
                  match e_extract_impl (add (supply_fresh S0) S0) Θ0 NM
                          (supply_fresh S0) mode_tc
                          (open_pskl_wrt_pskl Q
                             (pskl_var_f (supply_fresh S0))) P0
                          _ _ _ with
                  | None => None
                  | Some (exist _ rx Hrx) =>
                      match sumbool_of_bool
                              (wf_pskl_ck (size_pskl (ex_out rx))
                                 (ex_block rx ++ Θ0) empty (ex_out rx)) with
                      | right _ => None
                      | left _ =>
                          match e_sub_call_impl
                                  (sub_call_sub
                                     (open_pskl_wrt_pskl Q (ex_out rx)))
                                  (ex_supply rx) NM mode_tc P0
                                  (ex_block rx ++ Θ0) _ _ _ _ with
                          | None => None
                          | Some (exist _ r Hr) => Some (exist _ r _)
                          end
                      end
                  end
              end

          | pskl_ghost => fun EP =>
              Some (exist _ (mk_sub_result S0 Θ0 P0) _)

          | pskl_univ_ghost Q => fun EP =>
              match e_sub_call_impl (sub_call_sub Q) S0 a_sub_mode_sk
                      mode_tc P0 Θ0 _ _ _ _ with
              | None => None
              | Some (exist _ r Hr) => Some (exist _ r _)
              end
          | _ => fun EP =>
              match P0 as P01 return P0 = P01
                  -> option (sig (sub_call_spec S0 NM M P0 Θ0
                                    (sub_call_sub P)))
              with

              | pskl_ghost => fun EP0 =>
                  match sumbool_of_bool (guarded_shape_ck P) with
                  | right _ => None
                  | left _ =>
                      Some (exist _ (mk_sub_result S0 Θ0
                              (pskl_univ_ghost P)) _)
                  end
              | _ => fun _ => None
              end eq_refl
          end eq_refl
      end eq_refl

  | mode_fn M' => fun EM =>
      match P as P1 return P = P1
          -> option (sig (sub_call_spec S0 NM M P0 Θ0 (sub_call_sub P)))
      with

      | pskl_all_syn Q => fun EP =>
          match sumbool_of_bool (guarded_shape_ck P0 || ghost_ck P0) with
          | right _ => None
          | left _ =>
              match e_extract_impl (add (supply_fresh S0) S0) Θ0 NM
                      (supply_fresh S0) (mode_fn M')
                      (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                      P0 _ _ _ with
              | None => None
              | Some (exist _ rx Hrx) =>
                  match sumbool_of_bool
                          (wf_pskl_ck (size_pskl (ex_out rx))
                             (ex_block rx ++ Θ0) empty (ex_out rx)) with
                  | right _ => None
                  | left _ =>
                      match e_sub_call_impl
                              (sub_call_sub
                                 (open_pskl_wrt_pskl Q (ex_out rx)))
                              (ex_supply rx) NM (mode_fn M') P0
                              (ex_block rx ++ Θ0) _ _ _ _ with
                      | None => None
                      | Some (exist _ r Hr) => Some (exist _ r _)
                      end
                  end
              end
          end

      | pskl_arrow P1 P2 => fun EP =>
          match P0 as P01 return P0 = P01
              -> option (sig (sub_call_spec S0 NM M P0 Θ0 (sub_call_sub P)))
          with
          | pskl_arrow P0a P0b => fun EP0 =>
              match e_consis_impl empty empty S0 Θ0 P0a P1 _ _ _ _ with
              | None => None
              | Some (exist _ r1 Hr1) =>
                  match e_sub_call_impl (sub_call_sub P2) (cs_supply r1)
                          NM M' P0b (cs_ctx r1) _ _ _ _ with
                  | None => None
                  | Some (exist _ r2 Hr2) =>
                      Some (exist _ (mk_sub_result (sb_supply r2)
                              (sb_ctx r2)
                              (pskl_arrow (cs_out r1) (sb_out r2))) _)
                  end
              end
          | _ => fun _ => None
          end eq_refl

      | pskl_var_f α => fun EP =>
          match e_sub_call_impl (sub_call_flex nil α) S0 NM M' P0 Θ0
                  _ _ _ _ with
          | None => None
          | Some (exist _ r Hr) => Some (exist _ r _)
          end

      | pskl_ghost => fun EP =>
          match NM as NM1 return NM = NM1
              -> option (sig (sub_call_spec S0 NM M P0 Θ0 (sub_call_sub P)))
          with
          | a_sub_mode_sk => fun ENM =>
              Some (exist _ (mk_sub_result S0 Θ0 P0) _)
          | a_sub_mode_ty => fun _ => None
          end eq_refl

      | pskl_univ_ghost Q => fun EP =>
          match NM as NM1 return NM = NM1
              -> option (sig (sub_call_spec S0 NM M P0 Θ0 (sub_call_sub P)))
          with
          | a_sub_mode_sk => fun ENM =>
              match e_sub_call_impl (sub_call_sub Q) S0 a_sub_mode_sk
                      (mode_fn M') P0 Θ0 _ _ _ _ with
              | None => None
              | Some (exist _ r Hr) => Some (exist _ r _)
              end
          | a_sub_mode_ty => fun _ => None
          end eq_refl
      | _ => fun _ => None
      end eq_refl
  end eq_refl

| sub_call_flex Ξ α, S0, NM, M, P0, nil,
  HP, HP0, HD, H => None

| sub_call_flex Ξ α, S0, NM, M, P0, ((γ, abind_flex_mono) :: Θ0'),
  HP, HP0, HD, H =>
    match γ == α with
    | left _ =>
        match e_sub_call_impl
                (sub_call_sub
                   (pskl_arrow (pskl_var_f (supply_fresh S0))
                      (pskl_var_f (supply_fresh (add (supply_fresh S0) S0)))))
                (add (supply_fresh (add (supply_fresh S0) S0))
                   (add (supply_fresh S0) S0))
                NM (mode_fn M) P0
                (Ξ ++ (γ ~ abind_flex_mono_def
                             (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                                (ptyp_var_f
                                   (supply_fresh (add (supply_fresh S0) S0)))))
                   ++ (supply_fresh (add (supply_fresh S0) S0)
                         ~ abind_flex_mono)
                   ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
                _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    | right _ =>
        match sumbool_of_bool (mem γ (ftvar_in_pskl P0)) with
        | left _ =>
            match e_sub_call_impl (sub_call_flex (Ξ ++ (γ ~ abind_flex_mono)) α) S0 NM M P0 Θ0'
            _ _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        | right _ =>
            match e_sub_call_impl (sub_call_flex Ξ α) S0 NM M P0 Θ0'
            _ _ _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_sub_result (sb_supply r)
                        ((γ ~ abind_flex_mono) ++ sb_ctx r)
                        (sb_out r)) _)
            end
        end
    end

| sub_call_flex Ξ α, S0, NM, M, P0, ((γ, abind_flex_mono_def τ) :: Θ0'),
  HP, HP0, HD, H =>
    match e_sub_call_impl (sub_call_sub
               (subst_pskl_in_pskl (ptyp_to_pskl τ) γ (pskl_var_f α))) S0 NM (mode_fn M)
            (subst_pskl_in_pskl (ptyp_to_pskl τ) γ P0)
            (Ξ ++ Θ0')
            _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_sub_result (sb_supply r)
                ((γ ~ abind_flex_mono_def τ) ++ sb_ctx r) (sb_out r)) _)
    end

| sub_call_flex Ξ α, S0, NM, M, P0, ((γ, abind_tvar) :: Θ0'),
  HP, HP0, HD, H =>
    match γ == α with
    | left _ => None
    | right _ =>
        match sumbool_of_bool (mem γ (ftvar_in_pskl P0)) with
        | left _ => None
        | right _ =>
            match e_sub_call_impl (sub_call_flex Ξ α) S0 NM M P0 Θ0'
            _ _ _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_sub_result (sb_supply r)
                        ((γ ~ abind_tvar) ++ sb_ctx r) (sb_out r)) _)
            end
        end
    end

| sub_call_flex Ξ α, S0, NM, M, P0, ((x, abind_var_typ A) :: Θ0'),
  HP, HP0, HD, H =>
    match e_sub_call_impl (sub_call_flex Ξ α) S0 NM M P0 Θ0'
            _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_sub_result (sb_supply r)
                ((x ~ abind_var_typ A) ++ sb_ctx r) (sb_out r)) _)
    end
| sub_call_flex Ξ α, S0, NM, M, P0, ((x, abind_var_skl Q) :: Θ0'),
  HP, HP0, HD, H =>
    match e_sub_call_impl (sub_call_flex Ξ α) S0 NM M P0 Θ0'
            _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_sub_result (sb_supply r)
                ((x ~ abind_var_skl Q) ++ sb_ctx r) (sb_out r)) _)
    end.

Definition e_sub_impl (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (P : pskl)
    (HP : lc_pskl P) (HP0 : lc_pskl P0) (HD : aenv_defs_mono Θ0)
    (H : e_sub_order S0 NM M P0 Θ0 P)
    : option (sig (sub_spec S0 NM M P0 Θ0 P)) :=
  e_sub_call_impl (sub_call_sub P) S0 NM M P0 Θ0 HP HP0 HD
    (e_sub_order_to_call _ _ _ _ _ _ H).

Definition e_sub_flex_impl (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (Ξ : aenv) (α : atom)
    (HP0 : lc_pskl P0) (HD : aenv_defs_mono (Ξ ++ Θ0))
    (H : e_sub_flex_order S0 NM M P0 Θ0 Ξ α)
    : option (sig (sub_flex_spec S0 NM M P0 Θ0 Ξ α)) :=
  e_sub_call_impl (sub_call_flex Ξ α) S0 NM M P0 Θ0 I HP0 HD
    (e_sub_flex_order_to_call _ _ _ _ _ _ _ H).

Definition e_sub_run (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (P : pskl)
    (HP : lc_pskl P) (HP0 : lc_pskl P0) (HD : aenv_defs_mono Θ0)
    : option sub_result :=
  match e_sub_impl S0 NM M P0 Θ0 P HP HP0 HD
          (@e_sub_order_total S0 NM M P0 Θ0 P HP HP0 HD) with
  | Some r => Some (proj1_sig r)
  | None => None
  end.

Lemma e_sub_run_sound : forall S0 NM M P0 Θ0 P HP HP0 HD r,
  e_sub_run S0 NM M P0 Θ0 P HP HP0 HD = Some r ->
  {{ S0 ↝ (sb_supply r) ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ (sb_out r)
     ⊣ (sb_ctx r) }}e.
Proof.
  intros *. unfold e_sub_run.
  destruct (e_sub_impl S0 NM M P0 Θ0 P HP HP0 HD
              (@e_sub_order_total S0 NM M P0 Θ0 P HP HP0 HD))
    as [ [r' Hr'] | ];
    intro Heq; inversion Heq; subst; exact Hr'.
Qed.
