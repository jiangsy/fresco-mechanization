(** ext_algo — algorithmic SUBTYPING and its flexible walk as EXECUTABLE
    FUNCTIONS, by Bove–Capretta.  Phase 4 step 6: a MUTUAL [Equations] on
    def_order.v §6, total at lc inputs over a defs-mono context
    (prop_termination.v §17, UNCONDITIONAL since §8b.6).

    Result shape, dispatch discipline and obligation-tactic recipe are
    def_look_impl.v's; the reference dispatch order is [sub]
    (type.ml:903-1009) and [sub_flex] (:1011-1053) — in particular
    ⭐ SI-ForallR (:911) BEFORE SI-ForallL (:958), the §8b.1 commitment:
    when both the checked type and the subject are ∀, the target's
    quantifier is peeled first.

    ⚙ TWO OUTPUT CHECKS THE RELATION FIXES AND THE RUNNER MUST TEST:
    - SI-ForallR's premise must return the counterpart the rule pins
      ([open B α]) — tested with [pskl_eqb] — and its output context must
      decompose as [Ξ ++ (α ~ tvar) ++ Θ1] with a flex-only, uniq junk
      suffix — split by [split_at_tvar], then [suffix_ck]/[uniq_ck] for the
      rule's kept premises (def_sub.v's header: [uniq (Ξ ++ Θ0)] is the one
      premise threading deliberately does not retire).
    - SI-ForallL recurses only behind the rule's wf check on the extracted
      instantiation ([wf_pskl_ck], type.ml:966's [is_wf p1]).

    ⚙ [e_sub_flex__skip_rigid] carries [α <> β]: a walk that reaches its
    own target as a RIGID entry rejects (the target must be flexible). *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.sub.prop_solve_sub.   (* lc_pskl_*_inv *)
Require Import src.frost.algo.consis.prop_soundness_consis. (* a_wf_pskl_lc *)
Require Import src.frost.prop_coercions.
Require Import src.frost.prop_ln.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_dec.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_guess_impl.
Require Import src.frost.ext_algo.def_guess_impl_sk.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.def_sub.
Require Import src.frost.ext_algo.def_order.
Require Import src.frost.ext_algo.prop_termination.
Require Import src.frost.ext_algo.def_look_impl.
Require Import src.frost.ext_algo.def_solve_impl.
Require Import src.frost.ext_algo.def_extract_impl.
Require Import src.frost.ext_algo.def_consis_impl.

(* ⚠️ NO [Set Implicit Arguments] in an implementation file — see
   def_guess_impl.v's header. *)

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  The result                                                        *)
(* ===================================================================== *)

(** Split a context at the FIRST occurrence of the rigid marker
    [(α, tvar)], with the decomposition equation — how the ForallR runner
    recovers the junk suffix [Ξ] and the surviving tail [Θ1] from its
    premise's output.  [sig] erases: this extracts to a plain option pair. *)
(* ⚠️ [sumbool] spelled out — the [{ b = … }] sugar is shadowed by the
   tree's substitution notations (def_guess_impl.v's §1 warning) *)
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
  (* ⚠️ the marker is recognised by [abind_is_tvar_dec], not by a
     constructor pattern beside a catch-all: the match compiler expands a
     catch-all row per constructor, and the duplicated holes no longer see
     the binding they were written with *)
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
  (* ⚠️ goal-only rewrites — [subst] on the atom equation would generalize
     over [go] (whose type mentions [α]) and break the guard *)
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
  sb_ctx    : aenv;      (* Θ1 — the updated context *)
  sb_out    : pskl       (* Q — the counterpart *)
}.

Definition sub_spec (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (P : pskl) (r : sub_result) : Prop :=
  {{ S0 ↝ (sb_supply r) ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ (sb_out r)
     ⊣ (sb_ctx r) }}e.

Definition sub_flex_spec (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 Ξ : aenv) (α : atom) (r : sub_result) : Prop :=
  e_sub_flex S0 NM M P0 Θ0 Ξ α (sb_out r) (sb_supply r) (sb_ctx r).

(* ===================================================================== *)
(*  §2  The obligation tactic                                             *)
(* ===================================================================== *)

#[local] Hint Resolve supply_fresh_notin mem_true_in mem_false_notin
  guarded_shape_ck_sound ghost_free_ck_sound hole_ck_sound
  suffix_ck_sound uniq_ck_sound wf_pskl_ck_sound a_wf_pskl_lc
  lc_pskl_all_syn_inv lc_pskl_open_graft
  subst_pskl_in_pskl_lc_pskl mono_ptyp_to_pskl_lc mono_ptyp_lc
  e_consis_defs_mono e_extract_block_flex all_flex_mono_defs_mono
  e_guess_run_sound : subdec.
#[local] Hint Constructors lc_pskl guarded_pskl : subdec.
(* the judgements are NOT hinted — the rule instance is built by the
   tactic's trailing [econstructor; eauto] step; see def_consis_impl.v *)
#[local] Hint Extern 3 (e_consis_chk _ _ _ _ _ _) =>
  (unfold e_consis_chk; eexists; eassumption) : subdec.
#[local] Hint Extern 4 (_ <> _) => congruence : subdec.
(* deterministic assembly — see def_consis_impl.v's ⚠️ on Forall_app_intro *)
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
         | Hp : (guarded_pskl ?P \/ ?P = pskl_hole) -> _ |- _ =>
             let Hd := fresh "Hd0" in
             assert (Hd : guarded_pskl P \/ P = pskl_hole)
               by (solve [ left; apply guarded_shape_ck_sound; assumption
                         | right; apply hole_ck_sound; assumption
                         | right; reflexivity ]);
             specialize (Hp Hd); clear Hd
         | Hp : _ /\ _ |- _ => destruct Hp
         end.

#[local] Ltac saturate_lc :=
  repeat match goal with
         | Hlc : lc_pskl (pskl_arrow ?a ?b) |- _ =>
             lazymatch goal with
             | _ : lc_pskl a, _ : lc_pskl b |- _ => fail
             | _ => let Hx := fresh "Hlc0" in
                    assert (Hx := Hlc); apply lc_pskl_arrow_inv in Hx;
                    destruct Hx
             end
         | Hlc : lc_pskl (pskl_tophole ?a) |- _ =>
             lazymatch goal with
             | _ : lc_pskl a |- _ => fail
             | _ => let Hx := fresh "Hlc0" in
                    assert (Hx := Hlc); apply lc_pskl_tophole_inv in Hx
             end
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
      | H : e_sub_order _ _ _ _ _ _ |- _ => inversion H; subst
      end;
  try match goal with
      | H : e_sub_flex_order _ _ _ _ _ _ _ |- _ => inversion H; subst
      end;
  try match goal with
      | Hlc : lc_pskl (pskl_var_b _) |- _ => inversion Hlc
      end;
  unfold sub_spec, sub_flex_spec, consis_spec, extract_spec in *;
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
  (* a substituted VARIABLE reduces under simpl to an if-form (§8b's ⚠️) *)
  repeat match goal with
         | |- context [ if ?c then _ else _ ] => destruct c
         end;
  try congruence;
  try solve [ eauto 7 with subdec ];
  solve [ econstructor; eauto 6 with subdec ].

(* ===================================================================== *)
(*  §3  The mutual walk                                                   *)
(* ===================================================================== *)

#[tactic="sub_impl_tac", derive(equations=no,eliminator=no)]
Equations e_sub_impl (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (P : pskl)
    (HP : lc_pskl P) (HP0 : lc_pskl P0) (HD : aenv_defs_mono Θ0)
    (H : e_sub_order S0 NM M P0 Θ0 P)
    : option (sig (sub_spec S0 NM M P0 Θ0 P)) by struct H :=

(* SI-Infer *)
| S0, NM, mode_ti, pskl_hole, Θ0, P, HP, HP0, HD, H =>
    Some (exist _ (mk_sub_result S0 Θ0 P) _)
| S0, NM, mode_ti, P0, Θ0, P, HP, HP0, HD, H => None

(* SI-ForallR — BEFORE ForallL, the §8b.1 commitment *)
| S0, a_sub_mode_ty, mode_tc, pskl_all_syn B, Θ0, P, HP, HP0, HD, H =>
    match sumbool_of_bool (ghost_free_ck (pskl_all_syn B)) with
    | right _ => None
    | left _ =>
        match e_sub_impl (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
                (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
                ((supply_fresh S0 ~ abind_tvar) ++ Θ0) P _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            match sumbool_of_bool
                    (pskl_eqb (sb_out r)
                       (open_pskl_wrt_pskl B
                          (pskl_var_f (supply_fresh S0)))) with
            | right _ => None
            | left _ =>
                match split_at_tvar (supply_fresh S0) (sb_ctx r) with
                | None => None
                | Some (exist _ p Hp) =>
                    match sumbool_of_bool
                            (suffix_ck (fst p) && uniq_ck (fst p ++ Θ0))
                    with
                    | right _ => None
                    | left _ =>
                        Some (exist _ (mk_sub_result (sb_supply r) (snd p)
                                (pskl_all_syn B)) _)
                    end
                end
            end
        end
    end

(* SI-ForallL, check mode *)
| S0, NM, mode_tc, P0, Θ0, pskl_all_syn P, HP, HP0, HD, H =>
    match sumbool_of_bool (guarded_shape_ck P0 || hole_ck P0) with
    | right _ => None
    | left _ =>
        match e_extract_impl (add (supply_fresh S0) S0) Θ0 NM
                (supply_fresh S0) mode_tc
                (open_pskl_wrt_pskl P (pskl_var_f (supply_fresh S0))) P0
                _ _ _ with
        | None => None
        | Some (exist _ rx Hrx) =>
            match sumbool_of_bool
                    (wf_pskl_ck (size_pskl (ex_out rx))
                       (ex_block rx ++ Θ0) empty (ex_out rx)) with
            | right _ => None
            | left _ =>
                match e_sub_impl (ex_supply rx) NM mode_tc P0
                        (ex_block rx ++ Θ0)
                        (open_pskl_wrt_pskl P (ex_out rx)) _ _ _ _ with
                | None => None
                | Some (exist _ r Hr) => Some (exist _ r _)
                end
            end
        end
    end

(* SI-ForallL, function mode *)
| S0, NM, mode_fn M', P0, Θ0, pskl_all_syn P, HP, HP0, HD, H =>
    match sumbool_of_bool (guarded_shape_ck P0 || hole_ck P0) with
    | right _ => None
    | left _ =>
        match e_extract_impl (add (supply_fresh S0) S0) Θ0 NM
                (supply_fresh S0) (mode_fn M')
                (open_pskl_wrt_pskl P (pskl_var_f (supply_fresh S0))) P0
                _ _ _ with
        | None => None
        | Some (exist _ rx Hrx) =>
            match sumbool_of_bool
                    (wf_pskl_ck (size_pskl (ex_out rx))
                       (ex_block rx ++ Θ0) empty (ex_out rx)) with
            | right _ => None
            | left _ =>
                match e_sub_impl (ex_supply rx) NM (mode_fn M') P0
                        (ex_block rx ++ Θ0)
                        (open_pskl_wrt_pskl P (ex_out rx)) _ _ _ _ with
                | None => None
                | Some (exist _ r Hr) => Some (exist _ r _)
                end
            end
        end
    end

(* SI-Arrow *)
| S0, NM, mode_fn M', pskl_arrow P0a P0b, Θ0, pskl_arrow P1 P2,
  HP, HP0, HD, H =>
    match e_consis_impl empty empty S0 Θ0 P0a P1 _ _ _ _ with
    | None => None
    | Some (exist _ r1 Hr1) =>
        match e_sub_impl (cs_supply r1) NM M' P0b (cs_ctx r1) P2
                _ _ _ _ with
        | None => None
        | Some (exist _ r2 Hr2) =>
            Some (exist _ (mk_sub_result (sb_supply r2) (sb_ctx r2)
                    (pskl_arrow (cs_out r1) (sb_out r2))) _)
        end
    end

(* SI-FlexMono *)
| S0, NM, mode_fn M', P0, Θ0, pskl_var_f α, HP, HP0, HD, H =>
    match e_sub_flex_impl S0 NM M' P0 Θ0 nil α _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end

(* SI-Ghost *)
| S0, a_sub_mode_sk, M, P0, Θ0, pskl_hole, HP, HP0, HD, H =>
    Some (exist _ (mk_sub_result S0 Θ0 P0) _)

(* SI-UnivGhostL, check and function modes *)
| S0, a_sub_mode_sk, mode_tc, P0, Θ0, pskl_tophole P, HP, HP0, HD, H =>
    match e_sub_impl S0 a_sub_mode_sk mode_tc P0 Θ0 P _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, a_sub_mode_sk, mode_fn M', P0, Θ0, pskl_tophole P, HP, HP0, HD, H =>
    match e_sub_impl S0 a_sub_mode_sk (mode_fn M') P0 Θ0 P _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end

(* SI-Check *)
| S0, a_sub_mode_ty, mode_tc, P0, Θ0, P, HP, HP0, HD, H =>
    match sumbool_of_bool (ghost_free_ck P && ghost_free_ck P0
                           && guarded_shape_ck P && guarded_shape_ck P0)
    with
    | right _ => None
    | left _ =>
        match e_consis_impl empty empty S0 Θ0 P0 P _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_sub_result (cs_supply r) (cs_ctx r) P0) _)
        end
    end

(* SI-UnivGhostR *)
| S0, a_sub_mode_sk, mode_tc, pskl_hole, Θ0, P, HP, HP0, HD, H =>
    match sumbool_of_bool (guarded_shape_ck P) with
    | right _ => None
    | left _ =>
        Some (exist _ (mk_sub_result S0 Θ0 (pskl_tophole P)) _)
    end

| S0, NM, M, P0, Θ0, P, HP, HP0, HD, H => None

(* ===================================================================== *)
with e_sub_flex_impl (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (Ξ : aenv) (α : atom)
    (HP0 : lc_pskl P0) (HD : aenv_defs_mono (Ξ ++ Θ0))
    (H : e_sub_flex_order S0 NM M P0 Θ0 Ξ α)
    : option (sig (sub_flex_spec S0 NM M P0 Θ0 Ξ α)) by struct H :=

| S0, NM, M, P0, nil, Ξ, α, HP0, HD, H => None

(* undefined flexible head *)
| S0, NM, M, P0, ((γ, abind_flex_mono) :: Θ0'), Ξ, α, HP0, HD, H =>
    match γ == α with
    | left _ =>                                           (* SI-Flex-Solve *)
        match e_sub_impl
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
                (pskl_arrow (pskl_var_f (supply_fresh S0))
                   (pskl_var_f (supply_fresh (add (supply_fresh S0) S0))))
                _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    | right _ =>
        match sumbool_of_bool (mem γ (ftvar_in_pskl P0)) with
        | left _ =>                                       (* SI-Flex-Depend *)
            match e_sub_flex_impl S0 NM M P0 Θ0'
                    (Ξ ++ (γ ~ abind_flex_mono)) α _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        | right _ =>                                      (* SI-Flex-Skip *)
            match e_sub_flex_impl S0 NM M P0 Θ0' Ξ α _ _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_sub_result (sb_supply r)
                        ((γ ~ abind_flex_mono) ++ sb_ctx r)
                        (sb_out r)) _)
            end
        end
    end

(* defined flexible head — SI-Flex-Assign *)
| S0, NM, M, P0, ((γ, abind_flex_mono_def τ) :: Θ0'), Ξ, α, HP0, HD, H =>
    match e_sub_impl S0 NM (mode_fn M)
            (subst_pskl_in_pskl (ptyp_to_pskl τ) γ P0)
            (Ξ ++ Θ0')
            (subst_pskl_in_pskl (ptyp_to_pskl τ) γ (pskl_var_f α))
            _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_sub_result (sb_supply r)
                ((γ ~ abind_flex_mono_def τ) ++ sb_ctx r) (sb_out r)) _)
    end

(* rigid head — SI-Flex-SkipRigid *)
| S0, NM, M, P0, ((γ, abind_tvar) :: Θ0'), Ξ, α, HP0, HD, H =>
    match γ == α with
    | left _ => None                    (* the target is not flexible *)
    | right _ =>
        match sumbool_of_bool (mem γ (ftvar_in_pskl P0)) with
        | left _ => None
        | right _ =>
            match e_sub_flex_impl S0 NM M P0 Θ0' Ξ α _ _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_sub_result (sb_supply r)
                        ((γ ~ abind_tvar) ++ sb_ctx r) (sb_out r)) _)
            end
        end
    end

(* term-variable heads — SI-Flex-SkipTmVar, both payload sorts *)
| S0, NM, M, P0, ((x, abind_var_typ A) :: Θ0'), Ξ, α, HP0, HD, H =>
    match e_sub_flex_impl S0 NM M P0 Θ0' Ξ α _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_sub_result (sb_supply r)
                ((x ~ abind_var_typ A) ++ sb_ctx r) (sb_out r)) _)
    end
| S0, NM, M, P0, ((x, abind_var_skl Q) :: Θ0'), Ξ, α, HP0, HD, H =>
    match e_sub_flex_impl S0 NM M P0 Θ0' Ξ α _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_sub_result (sb_supply r)
                ((x ~ abind_var_skl Q) ++ sb_ctx r) (sb_out r)) _)
    end.

(* ===================================================================== *)
(*  §4  Totality-backed argument-free runners, and their soundness        *)
(* ===================================================================== *)

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
