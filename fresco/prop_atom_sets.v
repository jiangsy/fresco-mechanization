(** Atom-set disjointness and freshness under extension, composition and
    truncation. These facts do not depend on any typing judgement. *)

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.

Lemma inter_empty_pointwise : forall Δ Δ',
  (forall α, α `in` Δ -> α `notin` Δ') ->
  Δ ∩ Δ' [=] empty.
Proof.
  intros Δ Δ' H α. split; intro Hα.
  - assert (H1 := inter_1 Hα).
    assert (H2 := inter_2 Hα).
    exfalso. apply (H α H1 H2).
  - exfalso. clear - Hα. fsetdec.
Qed.

Set Implicit Arguments.

(** RELAY.  A walk step pops the head [α1], recurses with [add α1 N], and
    re-attaches [α1].  [D0']/[D1'] are the sub-run's input/output domains,
    [D0]/[D1] the outer run's; [α1] is in the outer input. *)
Lemma avoid_relay : forall (α1 : atom) N (D0' D1' D0 D1 : atoms),
  (forall γ, γ `in` D1' -> γ `in` D0' \/ γ `notin` (add α1 N)) ->
  D0' [<=] D0 ->
  α1 `in` D0 ->
  D1 [<=] (add α1 D1') ->
  forall γ, γ `in` D1 -> γ `in` D0 \/ γ `notin` N.
Proof.
  intros α1 N D0' D1' D0 D1 Hnew Hsub Hα1 HD1 γ Hγ.
  destruct (γ == α1) as [-> | Hne]; [ left; exact Hα1 | ].
  assert (Hγ' : γ `in` D1') by (clear - Hγ HD1 Hne; fsetdec).
  destruct (Hnew γ Hγ') as [Hin | Hni];
    [ left; clear - Hin Hsub; fsetdec | right; clear - Hni; fsetdec ].
Qed.

(** DISCHARGE.  The relayed set is exactly what proves the walk's Barendregt
    output premise: the popped head is in [add α1 N] and fresh for the
    sub-run's input, so the sub-run cannot have produced it. *)
Lemma avoid_head_miss : forall (α1 : atom) N (D0' D1' : atoms),
  (forall γ, γ `in` D1' -> γ `in` D0' \/ γ `notin` (add α1 N)) ->
  α1 `notin` D0' ->
  α1 `notin` D1'.
Proof.
  intros α1 N D0' D1' Hnew Hnd Hin.
  destruct (Hnew α1 Hin) as [Hd | HN]; [ auto | clear - HN; fsetdec ].
Qed.

(** COMPOSE.  Two runs in sequence (the Arrow node) share one [N]. *)
Lemma avoid_compose : forall N (D0 D1 D2 : atoms),
  (forall γ, γ `in` D1 -> γ `in` D0 \/ γ `notin` N) ->
  (forall γ, γ `in` D2 -> γ `in` D1 \/ γ `notin` N) ->
  forall γ, γ `in` D2 -> γ `in` D0 \/ γ `notin` N.
Proof.
  intros N D0 D1 D2 H1 H2 γ Hγ.
  destruct (H2 γ Hγ) as [Hin | Hni]; [ apply H1; exact Hin | right; exact Hni ].
Qed.

(** TRUNCATE.  The ∀ rows run under their own rigid binder [α] and hand back
    the truncated output; [α] is fresh, so it is not in the tail. *)
Lemma avoid_truncate : forall (α : atom) N (D0 D1 : atoms),
  (forall γ, γ `in` (add α D1) -> γ `in` (add α D0) \/ γ `notin` N) ->
  α `notin` D1 ->
  forall γ, γ `in` D1 -> γ `in` D0 \/ γ `notin` N.
Proof.
  intros α N D0 D1 Hnew HαD1 γ Hγ.
  assert (Hne : γ <> α) by (intros ->; auto).
  destruct (Hnew γ ltac:(clear - Hγ; solve_notin_auto)) as [Hin | Hni];
    [ left; clear - Hin Hne; fsetdec | right; exact Hni ].
Qed.
