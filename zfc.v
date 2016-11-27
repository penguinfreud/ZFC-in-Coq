Require Import classical.
Require Import Setoid.

Axiom set: Type.
Axiom Element: set.

Implicit Types u v w x y z X Y Z: set.

Axiom In: set->set->Prop.

Notation "x \in y" := (In x y) (at level 60).

Definition subset X Y := forall u, In u X -> In u Y.

Notation "x \subset y" := (subset x y) (at level 61).

Axiom extensionality: forall X Y, (forall u, u \in X <-> u \in Y) -> X = Y.

Definition non_empty X := exists u, u \in X.

Definition empty_set X := ~ non_empty X.

Definition separation_set (f: set->Prop) X Y := forall u, u \in Y <-> u \in X /\ f u.

Axiom separation_set_exists: forall (f: set->Prop) X, exists Y, separation_set f X Y.

Definition join_set X Y Z := separation_set (fun x => x \in Y) X Z.

Definition pair_set X Y Z := forall u, u \in Z <-> u=X \/ u=Y.

Definition singleton_set X Y := pair_set X X Y.

Axiom pair_set_exists: forall X Y, exists Z, pair_set X Y Z.

Definition union_set X Y := forall u, u \in Y <-> (exists v, v \in X /\ u \in v).

Axiom union_set_exists: forall X, exists Y, union_set X Y.

Definition power_set X Y := forall u, u \in Y <-> u \subset X.

Axiom power_set_exists: forall X, exists Y, power_set X Y.

Axiom regularity: forall X, non_empty X -> exists Y,
  Y \in X /\ ~(exists u, u \in X /\ u \in Y).

Definition is_function (f: set->set->Prop) X := forall x, x \in X -> (exists! y, f x y).

Definition image_set (f: set->set->Prop) X Y := forall u, u \in Y <-> (exists v, v \in X /\ f v u).

Axiom replacement: forall (f: set->set->Prop) X, is_function f X -> exists Y, image_set f X Y.

Definition succ X Y := forall u v, singleton_set X u -> pair_set X u v -> union_set v Y.

Axiom infinity: exists X, (forall u, empty_set u -> u \in X) /\
  (forall Y, Y \in X -> (forall v, succ Y v -> v \in X)).

Axiom AC: forall X, (forall u, empty_set u -> ~(u \in X)) /\
  (forall u v, (u \in X /\ v \in X) -> (forall w, w \subset u /\ w \subset v -> empty_set w)) ->
  (exists S: set, forall x Z, x \in X -> join_set S x Z -> (exists! y, singleton_set y Z)).


Theorem empty_set_exists: exists x, empty_set x.
Proof.
  destruct (separation_set_exists (fun x => False) Element).
  unfold empty_set. unfold non_empty.
  unfold separation_set in H.
  exists x.
  intro. destruct H0. apply H in H0.
  destruct H0. apply H1.
Qed.

Theorem empty_set_uniquely_exists: exists! X, empty_set X.
Proof.
  unfold Init.Logic.unique.
  destruct empty_set_exists.
  exists x.
  split.
  - apply H.
  - intros. apply extensionality.
    intros.
    unfold empty_set in H, H0.
    unfold non_empty in H, H0.
    rewrite exists_double_neg_dist in H, H0.
    rewrite <- forall_iff_exists in H, H0.
    rewrite contra_neg_iff.
    split.
    + intro. apply H0.
    + intro. apply H.
Qed.

Theorem separation_set_uniquely_exists: forall (f: set->Prop) X,
  exists! Y, separation_set f X Y.
Proof.
  intros f X. destruct (separation_set_exists f X) as [Z]. exists Z.
  unfold unique. split.
  - apply H.
  - intros. apply extensionality.
    intros.
    unfold separation_set in H, H0.
    rewrite (H u), (H0 u).
    reflexivity.
Qed.

Theorem join_set_uniquely_exists: forall X Y, exists! Z, join_set X Y Z.
Proof.
  intros X Y. destruct (separation_set_uniquely_exists (fun x => x \in Y) X) as [Z]. exists Z.
  unfold join_set. apply H.
Qed.

Theorem union_set_uniquely_exists: forall X, exists! Y, union_set X Y.
Proof.
  intros X. destruct (union_set_exists X) as [Y]. exists Y.
  unfold unique. split.
  - apply H.
  - intros. apply extensionality.
    intro. unfold union_set in H. rewrite H.
    unfold union_set in H0. rewrite H0.
    reflexivity.
Qed.

Theorem pair_set_uniquely_exists: forall X Y, exists! Z, pair_set X Y Z.
Proof.
  intros X Y. destruct (pair_set_exists X Y) as [Z]. exists Z.
  unfold unique. split.
  - apply H.
  - intros. apply extensionality.
    intro. unfold pair_set in H, H0.
    rewrite H, H0.
    reflexivity.
Qed.

Theorem singleton_set_uniquely_exists: forall X, exists! Y, singleton_set X Y.
Proof.
  intros X. destruct (pair_set_uniquely_exists X X) as [Y]. exists Y.
  unfold singleton_set. apply H.
Qed.

Theorem power_set_uniquely_exists: forall X, exists! Y, power_set X Y.
Proof.
  intros X. destruct (power_set_exists X) as [Y]. exists Y.
  unfold unique. split.
  - apply H.
  - intros. apply extensionality.
    intros.
    unfold power_set in H, H0.
    rewrite H, H0.
    reflexivity.
Qed.

Theorem image_set_uniquely_exists: forall (f: set->set->Prop) X,
  is_function f X -> exists! Y, image_set f X Y.
Proof.
  intros f X Hf. destruct (replacement f X Hf) as [Y]. exists Y.
  unfold unique. split.
  - apply H.
  - intros. apply extensionality.
    intros. unfold image_set in H, H0.
    rewrite H, H0. reflexivity.
Qed.

Theorem succ_exists: forall X, exists Y, succ X Y.
Proof.
  intros.
  destruct (singleton_set_uniquely_exists X) as [u Hu].
  destruct (pair_set_uniquely_exists X u) as [v Hv].
  destruct (union_set_uniquely_exists v) as [Y HY].
  exists Y. unfold succ.
  intros.
  unfold unique in Hu, Hv, HY.
  assert (u = u0). { apply (proj2 Hu). apply H. }
  assert (v = v0). { apply (proj2 Hv). rewrite H1. apply H0. }
  rewrite <- H2. apply (proj1 HY).
Qed.

Theorem separation_subset: forall (f: set->Prop) X Y, separation_set f X Y -> Y \subset X.
Proof.
  unfold separation_set. unfold subset. intros f X Y H u Hx.
  apply H. apply Hx.
Qed.

Definition set_forall (f: set -> Prop) X := forall u, u \in X -> f u.

Theorem subset_carries_property: forall (f: set->Prop) X Y,
  set_forall f X -> Y \subset X -> set_forall f Y.
Proof.
  unfold set_forall, subset. intros.
  apply H. apply H0. apply H1.
Qed.

Theorem separation_idempotent: forall (f: set->Prop) X Y,
  separation_set f X Y -> separation_set f Y Y.
Proof.
  unfold separation_set. intros.
  split.
  - intro. split.
    + apply H0.
    + apply H. apply H0.
  - intros [Hu Hfu]. apply Hu.
Qed.

Theorem separation_property: forall (f: set->Prop) X Y,
  separation_set f X Y -> set_forall f Y.
Proof.
  unfold set_forall, separation_set. intros.
  apply H. apply H0.
Qed.

Theorem join_set_subset: forall X Y Z, join_set X Y Z -> Z \subset X /\ Z \subset Y.
Proof.
  unfold join_set. intros.
  split.
  - apply separation_subset in H. apply H.
  - unfold subset. intros u Hu.
    unfold separation_set in H.
    apply H. apply Hu.
Qed.

Theorem union_set_property: forall (f: set->Prop) X Y,
  (forall x, x \in X -> set_forall f x) -> union_set X Y -> set_forall f Y.
Proof.
  unfold union_set, set_forall. intros.
  apply H0 in H1. destruct H1 as [v [Hvx Huv]].
  apply (H v).
  - apply Hvx.
  - apply Huv.
Qed.

Theorem subset_trans: forall X Y Z, X \subset Y -> Y \subset Z -> X \subset Z.
Proof.
  unfold subset. intros.
  apply H0. apply H. apply H1.
Qed.

Theorem subset_asymmetric: forall X Y, X \subset Y -> Y \subset X -> X = Y.
Proof.
  unfold subset. intros.
  apply extensionality.
  intros. split.
  - intro. apply H. apply H1.
  - intro. apply H0. apply H1.
Qed.

Theorem image_set_mono: forall (f: set->set->Prop) X Y, image_set f X Y ->
  (forall x y, x \subset X -> image_set f x y -> y \subset Y).
Proof.
  unfold image_set, subset. intros.
  apply H. apply H1 in H2. destruct H2.
  exists x0. split.
  - apply H0. apply H2.
  - apply H2.
Qed.

Theorem union_set_mono: forall x y, union_set x y ->
  (forall X Y, x \subset X -> union_set X Y -> y \subset Y).
Proof.
  unfold union_set, subset. intros.
  apply H1. apply H in H2.
  destruct H2. exists x0.
  split.
  - apply H0. apply H2.
  - apply H2.
Qed.

