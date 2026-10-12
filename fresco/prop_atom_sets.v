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

Lemma avoid_head_miss : forall (α1 : atom) N (D0' D1' : atoms),
  (forall γ, γ `in` D1' -> γ `in` D0' \/ γ `notin` (add α1 N)) ->
  α1 `notin` D0' ->
  α1 `notin` D1'.
Proof.
  intros α1 N D0' D1' Hnew Hnd Hin.
  destruct (Hnew α1 Hin) as [Hd | HN]; [ auto | clear - HN; fsetdec ].
Qed.

Lemma avoid_compose : forall N (D0 D1 D2 : atoms),
  (forall γ, γ `in` D1 -> γ `in` D0 \/ γ `notin` N) ->
  (forall γ, γ `in` D2 -> γ `in` D1 \/ γ `notin` N) ->
  forall γ, γ `in` D2 -> γ `in` D0 \/ γ `notin` N.
Proof.
  intros N D0 D1 D2 H1 H2 γ Hγ.
  destruct (H2 γ Hγ) as [Hin | Hni]; [ apply H1; exact Hin | right; exact Hni ].
Qed.

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
