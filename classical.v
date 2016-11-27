Require Export Logic.Classical.

Theorem forall_to_exists: forall (X: Type) (P: X -> Prop),
  (forall x: X, P x) -> ~(exists x: X, ~ P x).
Proof.
  intros X P H. unfold not. intro. destruct H0.
  apply H0. apply H.
Qed.

Theorem exists_to_forall: forall (X: Type) (P: X -> Prop),
  (exists x: X, P x) -> ~(forall x: X, ~ P x).
Proof.
  unfold not. intros. destruct H. apply H0 with x. apply H.
Qed.

Theorem double_neg: forall P: Prop, ~~P <-> P.
Proof.
  intros. split.
  - unfold not. intros. destruct (classic P).
    + apply H0.
    + apply H in H0. inversion H0.
  - unfold not. intros. destruct (classic P).
    + apply H0. apply H.
    + apply H1. apply H.
Qed.

Theorem exists_double_neg_dist: forall (X: Type) (P: X -> Prop),
  (exists x: X, P x) <-> (exists x: X, ~~ P x).
Proof.
  intros X P. split.
  - intros [x Hx]. exists x. apply double_neg. apply Hx.
  - intros [x Hx]. exists x. apply double_neg. apply Hx.
Qed.

Theorem forall_double_neg_dist: forall (X: Type) (P: X -> Prop),
  (forall x: X, P x) <-> (forall x: X, ~~ P x).
Proof.
  intros X P. split.
  - intros. apply double_neg. apply H.
  - intros. apply double_neg. apply H.
Qed.

Theorem not_exists_to_forall: forall (X: Type) (P: X -> Prop),
  ~(exists x: X, P x) -> (forall x: X, ~ P x).
Proof.
  unfold not. intros. apply H.
  exists x. apply H0.
Qed.

Theorem not_forall_to_exists: forall (X: Type) (P: X -> Prop),
  (exists x: X, True) -> ~(forall x: X, P x) -> (exists x: X, ~ P x).
Proof.
  intros X P [x] HA.
  destruct (classic (exists x: X, ~ P x)).
  - apply H0.
  - exists x. unfold not. intro. apply HA.
    intro. apply double_neg. generalize x0. apply not_exists_to_forall.
    apply H0.
Qed.

Theorem exists_iff_forall: forall (X: Type) (P: X -> Prop),
  (exists x: X, True) -> (exists x: X, P x) <-> ~(forall x: X, ~ P x).
Proof.
  intros X P H. split.
  - apply exists_to_forall.
  - intro. apply exists_double_neg_dist. apply not_forall_to_exists.
    + apply H.
    + apply H0.
Qed.

Theorem forall_iff_exists: forall (X: Type) (P: X -> Prop),
  (forall x: X, P x) <-> ~(exists x: X, ~ P x).
Proof.
  intros X P. split.
  - intro. apply forall_to_exists. apply H.
  - intro. apply forall_double_neg_dist. apply not_exists_to_forall. apply H.
Qed.

Theorem contra_neg: forall P Q: Prop, (P -> Q) <-> (~Q -> ~P).
Proof.
  unfold not. intros.
  split.
  - intros. apply H0. apply H. apply H1.
  - intros. destruct (classic Q).
    + apply H1.
    + apply H in H1.
      * inversion H1.
      * apply H0.
Qed.

Theorem contra_neg_iff: forall P Q: Prop, (P <-> Q) <-> (~P <-> ~Q).
Proof.
  intros. split.
  - intros [H1 H2]. split.
    + generalize H2. apply contra_neg.
    + generalize H1. apply contra_neg.
  - intros [H1 H2]. split.
    + apply contra_neg. apply H2.
    + apply contra_neg. apply H1.
Qed.

Theorem unique_existence_to_eq: forall (X: Type) (P: X -> Prop),
  (exists! x: X, P x) -> (forall (x y: X), P x /\ P y -> x = y).
Proof.
  intros X P [z Hz] x y [Hx Hy]. unfold unique in Hz. destruct Hz.
  assert (z = x). { apply H0. apply Hx. }
  assert (z = y). { apply H0. apply Hy. }
  rewrite <- H1, <- H2. reflexivity.
Qed.
