Require Import Coq.Setoids.Setoid.

Definition excluded_middle := forall P: Prop, P \/ ~P.

Parameter set: Type.
Parameter In: set->set->Prop.
Parameter element: set.

Parameter descr: (set->Prop)->set.
Axiom Descr: forall (prop:set->Prop), (exists! x, prop x) -> prop (descr prop).

Lemma descr_eq: forall (prop:set->Prop) x,
  prop x -> uniqueness prop -> descr prop = x.
Proof.
  intros.
  symmetry.
  apply H0.
  apply H.
  apply Descr.
  exists x.
  split.
  - apply H.
  - intros. apply H0; trivial.
Qed.

Lemma descr_prop: forall (prop prop': set->Prop) x,
  prop x -> uniqueness prop -> prop' x -> prop' (descr prop).
Proof.
  intros.
  assert (descr prop = x) by (exact (descr_eq prop x H H0)).
  subst x.
  apply H1.
Qed.

Notation "x ':i' y" := (In x y) (at level 60).

Axiom extensionality: forall x y, (forall u, u :i x <-> u :i y) -> x = y.

Lemma ext_iff: forall x y, x=y <-> (forall u, u :i x <-> u :i y).
Proof.
  split.
  - intros. subst. split; auto.
  - apply extensionality.
Qed.

Definition subset x y := forall u, u :i x -> u :i y.
Notation "x ':s' y" := (subset x y) (at level 62).

Lemma subset_refl: forall x, x :s x.
Proof.
  unfold subset. trivial.
Qed.

Lemma subset_antisymmetric: forall x y, x :s y -> y :s x -> x = y.
Proof.
  unfold subset. intros. apply extensionality.
  split; [apply H | apply H0].
Qed.

Lemma subset_trans: forall x y z, x :s y -> y :s z -> x :s z.
Proof.
  unfold subset. intros.
  apply H0, H, H1.
Qed.

Definition is_sep (test: set->Prop) x y := forall u, u :i y <-> u :i x /\ test u.
Axiom Sep: forall (test: set->Prop) x, exists y, is_sep test x y.
Definition sep (test: set->Prop) x := descr (is_sep test x).

Lemma sep_iff: forall (test: set->Prop) x u,
  u :i (sep test x) <-> u :i x /\ test u.
Proof.
  intros. unfold sep. apply (Descr (is_sep test x)).
  destruct (Sep test x).
  exists x0. split; intros.
  - apply H.
  - apply extensionality.
    split; intros; [apply H0, H | apply H, H0 ];
    apply H1.
Qed.

Lemma sep_subset: forall (test: set->Prop) x, sep test x :s x.
Proof.
  unfold subset. intros.
  apply sep_iff in H; trivial.
  apply H.
Qed.

Lemma sep_elem_prop: forall (test: set->Prop) x, forall u, u :i sep test x -> test u.
Proof.
  intros.
  apply sep_iff in H; trivial. apply H.
Qed.


Lemma sep_idempotent: forall (test: set->Prop) x, sep test (sep test x) = sep test x.
Proof.
  intros. apply extensionality. intros.
  split; intros; rewrite sep_iff; rewrite sep_iff in H.
  - split; try apply H. destruct H.
    apply sep_subset in H. apply H.
  - split; try apply H. rewrite sep_iff. apply H.
Qed.



Definition empty_set := sep (fun x => False) element.
Definition nonempty x := exists u, u :i x.

Lemma empty_set_no_elem: forall x, ~x :i empty_set.
Proof.
  unfold not. intros. apply sep_elem_prop in H.
  apply H.
Qed.

Lemma nonempty_correct: forall x, nonempty x -> x <> empty_set.
Proof.
  unfold not. intros.
  destruct H. rewrite H0 in H. apply empty_set_no_elem in H.
  inversion H.
Qed.

Lemma nonempty_iff: excluded_middle -> forall x,
  nonempty x <-> x <> empty_set.
Proof.
  split; intros.
  - apply nonempty_correct. apply H0.
  - unfold nonempty.
    assert ((exists u, u :i x) \/ ~(exists u, u :i x)).
    apply H.
    destruct H1.
    + apply H1.
    + assert (x=empty_set).
      { apply extensionality. split; intros.
        assert (exists u, u :i x).
        exists u. apply H2.
        apply H1 in H3.
        inversion H3.
        apply empty_set_no_elem in H2.
        inversion H2. }
      contradiction.
Qed.

Lemma not_nonempty_iff: forall x, ~nonempty x <-> x = empty_set.
Proof.
  split; intros.
  - apply extensionality.
    split; intros.
    + assert (nonempty x).
      { exists u. apply H0. }
      apply H in H1. inversion H1.
    + apply empty_set_no_elem in H0. inversion H0.
  - unfold not. intros. rewrite H in H0.
    destruct H0. apply empty_set_no_elem in H0. inversion H0.
Qed.

Lemma empty_subset: forall x, empty_set :s x.
Proof.
  unfold subset. intros.
  apply empty_set_no_elem in H. inversion H.
Qed.

Lemma empty_subset_empty: forall x, x :s empty_set -> x = empty_set.
Proof.
  unfold subset. intros. apply extensionality.
  split.
  - apply H.
  - apply empty_subset.
Qed.

Lemma sep_empty_set: forall (test: set->Prop),
  sep test empty_set = empty_set.
Proof.
  intros. apply extensionality.
  split; intros.
  - apply sep_subset in H. apply H.
  - apply empty_set_no_elem in H. inversion H.
Qed.

Lemma empty_cases: excluded_middle -> forall x, x = empty_set \/ nonempty x.
Proof.
  intros EM x.
  destruct (EM (nonempty x)).
  - right. assumption.
  - left. apply not_nonempty_iff. assumption.
Qed.


Definition proper_subset x y := x :s y /\ exists u, u :i y /\ ~ u :i x.
Notation "x :ps y" := (proper_subset x y) (at level 62).


Definition is_pair x y z := forall u, u :i z <-> u=x \/ u=y.
Axiom Pair: forall x y, exists z, is_pair x y z.
Definition pair x y := descr (is_pair x y).

Lemma pair_iff: forall x y u, u :i pair x y <-> u=x \/ u=y.
  intros.
  unfold pair. apply (Descr (is_pair x y)). unfold unique.
  destruct (Pair x y) as [z H].
  exists z.
  split; intros.
  - apply H.
  - apply extensionality. split; intros; [apply H0, H | apply H, H0]; apply H1.
Qed.


Lemma pair_comm: forall x y, pair x y = pair y x.
Proof.
  intros. apply extensionality.
  split; intros;
  rewrite pair_iff in H; rewrite pair_iff;
  destruct H; auto.
Qed.


Definition is_union x y := forall u, u :i y <-> (exists z, z :i x /\ u :i z).
Axiom Union: forall x, exists y, is_union x y.
Definition union x := descr (is_union x).

Lemma union_iff: forall x u, u :i union x <-> (exists y, y :i x /\ u :i y).
Proof.
  intros. unfold union. apply (Descr (is_union x)).
  destruct (Union x) as [y H]. exists y.
  split; intros.
  - apply H.
  - apply extensionality. split; intros; [apply H0, H | apply H, H0]; apply H1.
Qed.


Lemma union_subset: forall x u, u :i x -> u :s union x.
Proof.
  intros.
  unfold subset. intros.
  apply union_iff.
  exists u. auto.
Qed.


Create HintDb zfc.

Hint Rewrite sep_iff: zfc.

Hint Rewrite sep_iff.
Hint Rewrite pair_iff.
Hint Rewrite union_iff.

Lemma set_eq_iff: forall x y, x=y <-> (forall u, u :i x <-> u :i y).
Proof.
  split; intros.
  - rewrite H. reflexivity.
  - apply extensionality. apply H.
Qed.

Hint Rewrite set_eq_iff: zfc.

Definition biunion x y := union (pair x y).
Definition intersection x y := sep (fun u => u :i y) x.
Definition diff x y := sep (fun x => ~x :i y) x.
Notation "x -- y" := (diff x y) (at level 56, left associativity).
Definition symm_diff x y := biunion (x -- y) (y -- x).

Lemma biunion_iff: forall x y u,
  u :i biunion x y <-> u :i x \/ u :i y.
Proof.
  unfold biunion.
  split; intros.
  - rewrite union_iff in H.
    destruct H as [z [Hz Hz2]].
    rewrite pair_iff in Hz.
    destruct Hz; subst; auto.
  - rewrite union_iff.
    destruct H; [exists x | exists y];
    split; trivial;
    apply pair_iff;
    [left|right]; trivial.
Qed.

Hint Rewrite biunion_iff: zfc.

Lemma intersection_iff: forall x y u,
  u :i intersection x y <-> u :i x /\ u :i y.
Proof.
  intros.
  split; intros;
  [apply sep_iff in H | apply sep_iff];
  destruct H; split; trivial.
Qed.

Hint Rewrite intersection_iff: zfc.

Lemma diff_iff: forall x y u, u :i x -- y <->
  u :i x /\ ~u :i y.
Proof.
  split; intros.
  - apply sep_iff in H. apply H.
  - apply sep_iff. apply H.
Qed.

Hint Rewrite diff_iff: zfc.

Lemma symm_diff_iff: forall x y u, u :i symm_diff x y <->
  (u :i x /\ ~u :i y) \/ (u :i y /\ ~u :i x).
Proof.
  unfold symm_diff; split; intros;
  autorewrite with zfc in *; auto.
Qed.

Hint Rewrite symm_diff_iff: zfc.

Ltac autoelim :=
  intros; repeat match goal with
    | [_:_ |- _ /\ _] => split; intros
    | [_:_ |- _ <-> _] => split; intros
    | [H: _ \/ _ |- _] => destruct H
    | [H: _ /\ _ |- _] => destruct H
    | [H: False |- _] => destruct H
    | [H: exists _, _ |- _] => destruct H
  end.

Ltac set_oper :=
  repeat (autorewrite with zfc in *;
    unfold subset; autoelim;
    repeat match goal with
      | [H: _ :i empty_set |- _] => apply empty_set_no_elem in H
      | [_:_ |- ~ _ :i empty_set] => apply empty_set_no_elem
    end; auto).

Lemma not_or_iff: excluded_middle ->
  forall A B: Prop, ~(A \/ B) <-> ~A /\ ~B.
Proof.
  intros EM A B. split; intros.
  - destruct (EM A).
    + destruct (H (or_introl H0)).
    + split; trivial. destruct (EM B).
      * destruct (H (or_intror H1)).
      * apply H1.
  - unfold not. intros. destruct H, H0; contradiction.
Qed.

Lemma not_and_iff: excluded_middle ->
  forall A B: Prop, ~(A /\ B) <-> ~A \/ ~B.
Proof.
  intro EM. split; intros.
  - destruct (EM A), (EM B).
    + destruct (H (conj H0 H1)).
    + right. trivial.
    + left. trivial.
    + left. trivial.
  - unfold not. intros [HA HB].
    destruct H; contradiction.
Qed.

Lemma not_imply_iff: excluded_middle ->
  forall A B: Prop, ~(A -> B) -> A /\ ~B.
Proof.
  intro EM. split; intros.
  - destruct (EM A); trivial.
    assert (A -> B).
    { intro. destruct (H0 H1). }
    destruct (H H1).
  - destruct (EM B).
    + assert (A -> B).
      { intro. trivial. }
      destruct (H H1).
    + trivial.
Qed.

Lemma not_exists_iff: excluded_middle ->
  forall (X: Type) (P: X->Prop),
    (~exists (x:X), P x) <-> forall (x: X), ~P x.
Proof.
  intro EM.
  unfold not.
  split; intros.
  - apply (H (ex_intro P x H0)).
  - destruct H0. apply (H x H0).
Qed.

Lemma double_neg: excluded_middle -> forall A: Prop, ~~A <-> A.
Proof.
  intro EM.
  split; intros.
  - destruct (EM A); trivial.
    destruct (H H0).
  - unfold not. intros. destruct (H0 H).
Qed.

Lemma not_forall_iff: excluded_middle ->
  forall (X: Type) (P: X->Prop),
    (exists (x: X), True) ->
      ((~forall (x:X), P x) <-> (exists (x:X), ~P x)).
Proof.
  intro EM.
  split; intros.
  - destruct (EM (exists (x: X), ~ P x)).
    + trivial.
    + rewrite not_exists_iff in H1; trivial.
      assert (forall (x: X), P x) by (intros; rewrite <- double_neg; trivial).
      apply H0 in H2. inversion H2.
  - unfold not. intros contra.
    destruct H0.
    apply (H0 (contra x)).
Qed.

Ltac classic :=
  repeat (autoelim; match goal with
    | [EM: excluded_middle, H: ~ (_ /\ _) |- _] => rewrite (not_and_iff EM) in H
    | [EM: excluded_middle, H: ~ (_ \/ _) |- _] => rewrite (not_or_iff EM) in H
    | [EM: excluded_middle, H: ~ (_ -> _) |- _] => rewrite (not_imply_iff EM) in H
    | [EM: excluded_middle, H: ~~ _ |- _] => rewrite (double_neg EM) in H
    | [EM: excluded_middle |- ~ (_ /\ _)] => rewrite (not_and_iff EM)
    | [EM: excluded_middle |- ~ (_ \/ _)] => rewrite (not_or_iff EM)
    | [EM: excluded_middle |- ~ (_ -> _)] => rewrite (not_imply_iff EM)
    | [EM: excluded_middle |- ~~ _] => rewrite (double_neg EM)
  end); autoelim.

Lemma biunion_subset_l: forall x y, x :s biunion x y. 
Proof.
  set_oper.
Qed.

Lemma biunion_comm: forall x y, biunion x y = biunion y x.
Proof.
  set_oper.
Qed.

Lemma biunion_subset_r: forall x y, y :s biunion x y.
Proof.
  set_oper.
Qed.

Lemma biuniona_assoc: forall x y z,
  biunion (biunion x y) z = biunion x (biunion y z).
Proof.
  set_oper.
Qed.

Lemma intersection_comm: forall x y, intersection x y = intersection y x.
Proof.
  set_oper.
Qed.

Lemma intersection_subset_l: forall x y, intersection x y :s x.
Proof.
  set_oper.
Qed.

Lemma intersection_subset_r: forall x y, intersection x y :s y.
Proof.
  set_oper.
Qed.

Lemma intersection_assoc: forall x y z, intersection (intersection x y) z = intersection x (intersection y z).
Proof.
  set_oper.
Qed.

Lemma intersection_biunion_dist: forall x y z,
  intersection x (biunion y z) = biunion (intersection x y) (intersection x z).
Proof.
  set_oper.
Qed.

Lemma intersection_empty_set: forall x, intersection empty_set x = empty_set.
Proof.
  set_oper.
Qed.

Lemma intersection_idempotent: forall x, intersection x x = x.
Proof.
  set_oper.
Qed.


Lemma biunion_empty_set: forall x, biunion empty_set x = x.
Proof.
  set_oper.
Qed.

Lemma biunion_intersection_dist: forall x y z,
  biunion x (intersection y z) = intersection (biunion x y) (biunion x z).
Proof.
  set_oper.
Qed.


Lemma empty_sub_x: forall x, empty_set -- x = empty_set.
Proof.
  set_oper.
Qed.

Lemma x_sub_empty: forall x, x -- empty_set = x.
Proof.
  set_oper.
Qed.

Lemma diff_intersection_assoc: forall x y z, intersection x (y--z) = intersection x y -- z.
Proof.
  set_oper.
Qed.

Lemma demorgan_intersection: excluded_middle ->
  forall x y z, x -- (intersection y z) = biunion (x -- y) (x -- z).
Proof.
  intro EM.
  repeat (set_oper; classic; auto).
Qed.

Lemma demorgan_biunion: forall x y z,
  x -- (biunion y z) = intersection (x -- y) (x -- z).
Proof.
  set_oper.
  unfold not. intros. destruct H3; contradiction.
Qed.

Lemma diff_subset: excluded_middle -> forall x y,
  x -- y = empty_set <-> x :s y.
Proof.
  intro EM.
  split; set_oper.
  - assert (~u :i empty_set). apply empty_set_no_elem.
    rewrite <- H in H1. rewrite diff_iff in H1.
    assert (u :i y \/ ~u :i y). apply EM.
    destruct H2.
    + apply H2.
    + destruct (H1 (conj H0 H2)).
  - apply H in H0. contradiction.
Qed.

Lemma symm_diff_comm: forall x y, symm_diff x y = symm_diff y x.
Proof.
  set_oper.
Qed.

Lemma symm_diff_assoc: excluded_middle -> forall x y z,
  symm_diff (symm_diff x y) z = symm_diff x (symm_diff y z).
Proof.
  intro EM.
  set_oper; classic; classic;
  [left | right | | | left | left | | | right | right];
  try contradiction; split; intros;
  classic; auto.
Qed.

Lemma subset_iff_intersection: forall x y, x :s y <-> intersection x y = x.
Proof.
  set_oper. apply H in H0. set_oper.
Qed.

Lemma subset_iff_biunion: forall x y, x :s y <-> biunion x y = y.
Proof.
  set_oper. apply H. set_oper.
Qed.

Lemma biunion_diff: forall x y, (biunion x y) -- y = x -- y.
Proof.
  set_oper. contradiction.
Qed.

Lemma diff_intersection: forall x y, x -- (intersection x y) = x -- y.
Proof.
  set_oper. unfold not. intros. destruct (H0 (proj2 H1)).
Qed.

Lemma diff_diff_intersection: excluded_middle ->
  forall x y, x -- (x -- y) = intersection x y.
Proof.
  set_oper; classic; try contradiction; auto; classic; auto.
Qed.

Lemma diff_x_diff_y_z__biunion_diff_x_y_intersection_x_z:
  excluded_middle -> forall x y z,
    x -- (y -- z) = biunion (x -- y) (intersection x z).
Proof.
  set_oper; classic; auto.
  rewrite (double_neg H) in H1.
  right. split; trivial.
Qed.

Definition any_intersection x y := sep (fun x => forall u, u :i y -> x :i u) x.

Lemma any_intersection_subset_l: forall x y u, u :i y -> any_intersection x y :s u.
Proof.
  unfold any_intersection, subset. intros.
  apply sep_elem_prop in H0. apply H0. apply H.
Qed.


Definition is_power_set x y := forall u, u :i y <-> u :s x.
Axiom Power_set: forall x, exists y, is_power_set x y.
Definition power_set x := descr (is_power_set x).

Lemma power_set_iff: forall x u, u :i power_set x <-> u :s x.
Proof.
  intros.
  unfold power_set. apply (Descr (is_power_set x)).
  destruct (Power_set x) as [y H]. exists y.
  split; intros.
  - apply H.
  - apply extensionality. split; intros; [apply H0, H | apply H, H0]; apply H1.
Qed.

Hint Rewrite power_set_iff: zfc.


Definition singleton x := pair x x.
Definition succ x := union (pair x (singleton x)).

Lemma singleton_iff: forall x u, u :i singleton x <-> u = x.
Proof.
  intros. split; intros.
  - apply pair_iff in H. destruct H; apply H.
  - apply pair_iff. left. apply H.
Qed.

Hint Rewrite singleton_iff: zfc.

Lemma succ_iff: forall x u, u :i succ x <-> u = x \/ u :i x.
Proof.
  split; intros.
  - apply union_iff in H. destruct H as [y [Hy Hy2]].
    apply pair_iff in Hy. destruct Hy.
    + right. rewrite H in Hy2. apply Hy2.
    + rewrite H in Hy2. apply singleton_iff in Hy2.
      left. apply Hy2.
  - apply union_iff. destruct H.
    + exists (singleton x).
      split.
      * apply pair_iff. right. reflexivity.
      * apply singleton_iff. apply H.
    + exists x. split.
      * apply pair_iff. left. reflexivity.
      * apply H.
Qed.

Hint Rewrite succ_iff: zfc.

Definition n0 := empty_set.
Definition n1 := succ n0.
Definition n2 := succ n1.


Definition induction_set x :=
  empty_set :i x /\ (forall u, u :i x -> succ u :i x).
Axiom Infinity: exists x, induction_set x.


Axiom Foundation: forall x, nonempty x ->
  (exists y, y :i x /\ intersection x y = empty_set).

Lemma no_self_ref: forall x, ~x :i x.
Proof.
  unfold not. intros.
  assert (x :i (singleton x)).
  apply singleton_iff. reflexivity.
  assert (nonempty (singleton x)).
  exists x. apply H0.
  apply Foundation in H1.
  destruct H1 as [y [Hy Hy2]].
  apply singleton_iff in Hy.
  rewrite Hy in Hy2.
  assert (x :i intersection (singleton x) x).
  { apply intersection_iff. split.
    - apply H0.
    - apply H. }
  assert (nonempty (intersection (singleton x) x)).
  exists x. apply H1.
  apply nonempty_correct in H2. contradiction.
Qed.

Lemma power_set_not_subset: forall x, ~power_set x :s x.
Proof.
  unfold not. set_oper.
  assert (x :i power_set x). {
    apply power_set_iff.
    apply subset_refl.
  }
  apply H in H0. apply no_self_ref in H0. trivial.
Qed.


Definition is_rep (fn: set->set) x y := forall u,
  u :i y <-> (exists z, z :i x /\ fn z = u).
Axiom Rep: forall (fn: set->set) x, exists y, is_rep fn x y.
Definition rep (fn: set->set) x := descr (is_rep fn x).

Lemma rep_iff: forall (fn: set->set) x u,
  u :i rep fn x <-> (exists z, z :i x /\ fn z = u).
Proof.
  intros. unfold rep. apply (Descr (is_rep fn x)).
  destruct (Rep fn x).
  exists x0.
  split; intros.
  - apply H.
  - apply extensionality. split; intros; [apply H0, H | apply H, H0]; apply H1.
Qed.


Definition disjoint x y := intersection x y = empty_set.
Definition mutual_disjoint X := forall x y, x :i X -> y :i X -> x=y \/ disjoint x y.

Definition is_choice_set X S := forall x,
  x :i X -> exists! y, intersection S X = singleton y.
Axiom Choice: forall X, nonempty X /\ mutual_disjoint X ->
  exists S, is_choice_set X S.


Definition ordered_pair x y := pair (singleton x) (pair x y).
Notation "x ,, y" := (ordered_pair x y) (right associativity, at level 54).

Lemma singleton_injective: forall x1 x2,
  x1 = x2 <-> singleton x1 = singleton x2.
Proof.
  split; intros.
  - rewrite H. reflexivity.
  - apply singleton_iff. rewrite <- H.
    apply singleton_iff. reflexivity.
Qed.

Lemma pair_in_l: forall x y, x :i pair x y.
Proof.
  intros. apply pair_iff. left. reflexivity.
Qed.

Lemma pair_in_r: forall x y, y :i pair x y.
Proof.
  intros. apply pair_iff. right. reflexivity.
Qed.

Lemma pair_eq_iff: forall x1 x2 y1 y2,
  pair x1 y1 = pair x2 y2 <->
    x1 = x2 /\ y1 = y2 \/
    x1 = y2 /\ y1 = x2.
Proof.
  split; intros.
  - assert (x1 :i pair x1 y1).
    apply pair_in_l.
    rewrite H in H0. apply pair_iff in H0.
    assert (y1 :i pair x1 y1).
    apply pair_in_r.
    rewrite H in H1. apply pair_iff in H1.
    assert (x2 :i pair x2 y2).
    apply pair_in_l.
    rewrite <- H in H2. apply pair_iff in H2.
    assert (y2 :i pair x2 y2).
    apply pair_in_r.
    rewrite <- H in H3. apply pair_iff in H3.
    destruct H0, H1, H2, H3; auto.
  - destruct H as [[H1 H2] | [H1 H2]]; rewrite H1, H2; auto.
    apply pair_comm.
Qed.

Hint Rewrite pair_eq_iff: zfc.

Lemma ordered_pair_injective: forall x1 x2 y1 y2,
  x1,,y1 = x2,,y2 <-> x1 = x2 /\ y1 = y2.
Proof.
  split; intros.
  - apply pair_eq_iff in H.
    destruct H as [[H1 H2] | [H1 H2]];
    apply pair_eq_iff in H1;
    apply pair_eq_iff in H2;
    destruct H1 as [[H3 H4] | [H3 H4]];
    destruct H2 as [[H5 H6] | [H5 H6]];
    split;
    subst x1; try subst x2; try subst y1; try subst y2; auto.
  - destruct H. subst. reflexivity.
Qed.

Lemma union_ind: forall (P: set->Prop) X,
  (forall x u, x :i X -> u :i x -> P u) ->
  (forall u, u :i union X -> P u).
Proof.
  intros.
  apply (union_iff X) in H0.
  destruct H0 as [z [Hz Hu]].
  apply H with z; trivial.
Qed.

Lemma rep_ind: forall (P: set->Prop) (f: set->set) X,
  (forall x, x :i X -> P (f x)) ->
  (forall x, x :i rep f X -> P x).
Proof.
  intros.
  apply (rep_iff f) in H0.
  destruct H0 as [z [Hz Hx]].
  rewrite <- Hx.
  apply H, Hz.
Qed.

Definition cartesian_prod X Y := union (rep (fun x => rep (fun y => x,, y) Y) X).
Notation "x ** y" := (cartesian_prod x y) (right associativity, at level 58).

Lemma cp_iff: forall X Y u, u :i X ** Y <->
  (exists x y, x :i X /\ y :i Y /\ u = x,,y).
Proof.
  intros X Y u.
  set (f := fun u => exists x y, x :i X /\ y :i Y /\ u=x,,y).
  split.
  - generalize u.
    apply union_ind.
    intros.
    apply rep_iff in H.
    destruct H as [z [Hz Hx]].
    generalize dependent u0.
    rewrite <- Hx.
    apply rep_ind.
    intros.
    exists z, x0.
    auto.
  - intros [x [y [Hx [Hy Hu]]]].
    apply union_iff.
    exists (rep (fun y => x,,y) Y).
    split.
    + apply (rep_iff (fun x => rep (fun y => x,,y) Y) X).
      exists x.
      split; trivial.
    + apply (rep_iff (fun y => x,,y) Y).
      exists y.
      symmetry in Hu.
      split; trivial.
Qed.

Lemma cp_iff_op: forall X Y x y, x,,y :i X ** Y <-> x :i X /\ y :i Y.
Proof.
  split; intros.
  - apply cp_iff in H.
    destruct H as [x0 [y0 [Hx [Hy Heq]]]].
    apply ordered_pair_injective in Heq.
    destruct Heq.
    subst.
    split; assumption.
  - apply cp_iff.
    exists x, y.
    destruct H.
    repeat split; try assumption; try reflexivity.
Qed.

Implicit Types P Q R: set->set->Prop.

Definition cp_sep R X Y := sep (fun p => forall x y, x,,y = p -> R x y) (X**Y).

Lemma cp_sep_iff: forall R X Y x y,
  x,,y :i cp_sep R X Y <-> x :i X /\ y :i Y /\ R x y.
Proof.
  unfold cp_sep.
  split; intros.
  - apply sep_iff in H.
    destruct H.
    apply cp_iff_op in H.
    destruct H.
    repeat split; try assumption.
    apply H0. reflexivity.
  - apply sep_iff.
    split.
    + apply cp_iff_op.
      split; apply H.
    + intros.
      apply ordered_pair_injective in H0.
      destruct H0; subst.
      apply H.
Qed.

Hint Rewrite cp_iff: zfc.
Hint Rewrite cp_sep_iff: zfc.


Definition relation X Y r := r :s X ** Y.
Definition is_relation r := exists X Y, relation X Y r.

Definition cast_rel r x y := x,,y :i r.

Definition uncast_rel X Y R :=
  sep (fun p => forall x y, x,,y = p -> R x y) (X**Y).


Definition relation3 X1 X2 X3 r := r :s X1**X2**X3.
Definition is_relation3 r := exists X1 X2 X3, relation3 X1 X2 X3 r.

Definition cast_rel3 r x1 x2 x3 := x1,,x2,,x3 :i r.
Definition uncast_rel3 X1 X2 X3 (R: set->set->set->Prop) :=
  sep (fun p => forall x1 x2 x3, x1,,x2,,x3 = p -> R x1 x2 x3) (X1**X2**X3).

Definition relation4 X1 X2 X3 X4 r := r :s X1**X2**X3**X4.
Definition is_relation4 r := exists X1 X2 X3 X4, relation4 X1 X2 X3 X4 r.

Definition cast_rel4 r x1 x2 x3 x4 := x1,,x2,,x3,,x4 :i r.
Definition uncast_rel4 X1 X2 X3 X4 (R: set->set->set->set->Prop) :=
  sep (fun p => forall x1 x2 x3 x4, x1,,x2,,x3,,x4 = p -> R x1 x2 x3 x4) (X1**X2**X3**X4).

Lemma rel_eq_subset: forall X Y P Q, (forall x y, P x y <-> Q x y) ->
  (uncast_rel X Y P) :s (uncast_rel X Y Q).
Proof.
  unfold subset. intros.
  apply sep_iff.
  apply sep_iff in H0.
  destruct H0.
  split.
  - apply H0.
  - intros.
    apply H.
    apply H1.
    assumption.
Qed.

Lemma rel_eq: forall X Y P Q, (forall x y, P x y <-> Q x y) ->
  (uncast_rel X Y P) = (uncast_rel X Y Q).
Proof.
  intros.
  apply subset_antisymmetric;
  apply rel_eq_subset;
  intros; [| symmetry]; apply H.
Qed.

Definition partial_function X R := forall x, x :i X -> uniqueness (R x).
Definition function X Y R := partial_function X R /\
  forall x, x :i X -> exists y, y :i Y /\ R x y.

Definition power X Y := sep (fun r => function X Y (cast_rel r)) (power_set (X**Y)).

Definition partial_function2 X1 X2 (R: set->set->set->Prop) :=
  forall x1 x2, x1 :i X1 -> x2 :i X2 -> uniqueness (R x1 x2).
Definition function2 X1 X2 Y (R: set->set->set->Prop) :=
  partial_function2 X1 X2 R /\
  (forall x1 x2, x1 :i X1 -> x2 :i X2 -> exists y, y :i Y /\ R x1 x2 y).

Definition partial_function3 X1 X2 X3 (R: set->set->set->set->Prop) :=
  forall x1 x2 x3, x1 :i X1 -> x2 :i X2 -> x3 :i X3 -> uniqueness (R x1 x2 x3).
Definition function3 X1 X2 X3 Y (R: set->set->set->set->Prop) :=
  partial_function3 X1 X2 X3 R /\
  (forall x1 x2 x3, x1 :i X1 -> x2 :i X2 -> x3 :i X3 ->
    exists y, y :i Y /\ R x1 x2 x3 y).


Definition reflexive X R := forall x, x :i X -> R x x.
Definition irreflexive R := forall x, ~R x x.
Definition symmetric R := forall x y, R x y -> R y x.
Definition asymmetric R := forall x y, R x y -> ~R y x.
Definition antisymmetric R := forall x y, R x y -> R y x -> x = y.
Definition transitive R := forall x y z, R x y -> R y z -> R x z.
Definition antitransitive R := forall x y z, R x y -> R y z -> ~R x z.
Definition trichotomous R := forall x y, R x y \/ R y x \/ x=y.

Definition partial_order R := antisymmetric R /\ transitive R.
Definition strict_partial_order R := irreflexive R /\ transitive R.
Definition total_order R := partial_order R /\ trichotomous R.
Definition strict_total_order R := strict_partial_order R /\ trichotomous R.

Definition equivalence_relation X R := reflexive X R /\ symmetric R /\ transitive R.
Definition partition X p := mutual_disjoint p /\ union p = X.

Definition dom X R := sep (fun x => exists y, R x y) X.
Definition ran Y R := sep (fun y => exists x, R x y) Y.

Definition restrict_dom R X x y := x :i X /\ R x y.
Definition restrict_ran R Y x y := y :i Y /\ R x y.
Definition image_set R X Y := ran Y (restrict_dom R X).
Definition inv_image_set R X Y := dom X (restrict_ran R Y).

Definition compose P Q x z := exists y, P x y /\ Q y z.
Definition inverse R y x := R x y.


Definition partition_to_equiv p x y:= exists z, x :i z /\ y :i z /\ z :i p.
Definition eq_class X R x := sep (fun y => R x y) X.
Definition equiv_to_partition X R :=
  sep (fun S => exists x, x :i X /\ S = eq_class X R x) (power_set X).

Definition minimal_elem X R a := a :i X /\ forall x, x :i X -> x=a \/ R a x.
Definition maximal_elem X R a := a :i X /\ forall x, x :i X -> x=a \/ R x a.
Definition lower_bound X R S a := a :i X /\ S :s X /\ forall x, x :i S -> R a x.
Definition upper_bound X R S a := a :i X /\ S :s X /\ forall x, x :i S -> R x a.
Definition inf X R S a := lower_bound X R S a /\ forall b, lower_bound X R S b -> R b a.
Definition sup X R S a := upper_bound X R S a /\ forall b, upper_bound X R S b -> R a b.

Definition minimal_elem_prop X R := forall S,
  S :s X -> nonempty S -> exists a, minimal_elem S R a.
Definition well_order X R := total_order R /\ minimal_elem_prop X R.
Definition strict_well_order X R := strict_total_order R /\ minimal_elem_prop X R.

Definition refl_closure R x y := x = y \/ R x y.

Lemma swo_subset: forall X Y R, strict_well_order X R ->
  Y :s X -> strict_well_order Y R.
Proof.
  unfold strict_well_order, minimal_elem_prop. intros.
  split.
  - apply H.
  - intros.
    apply (subset_trans S Y X) in H1.
    apply H in H1. destruct H1.
    exists x. apply H1.
    assumption. assumption.
Qed.



Definition injective R := forall x y z, R x z -> R y z -> x = y.
Definition surjective R Y := ran Y R = Y.
Definition bijective R X Y := dom X R = X /\ injective R /\ surjective R Y.
Definition isomorphism (f: set->set->Prop) X Y P Q :=
  bijective f X Y /\
  (forall x y x' y', x :i X -> y :i Y -> f x x' -> f y y' -> (P x y <-> Q x' y')).

Definition is_nat x := induction_set x /\ forall y, induction_set y -> x :s y.
Definition Nat := descr is_nat.

Lemma nat_exists: is_nat Nat.
Proof.
  unfold Nat. apply Descr.
  destruct Infinity as [x Hx].
  destruct (Sep (fun u => forall y, induction_set y -> u :i y) x) as [y Hy].
  exists y.
  repeat split.
  - apply Hy. split.
    + apply Hx.
    + intros. apply H.
  - intros. apply Hy.
    split.
    + apply Hy. apply Hy. split.
      * apply Hy in H. apply Hx. apply H. apply Hx.
      * intros. apply Hy in H. apply H in H0 as H1.
        apply H0. apply H1.
      * apply Hx.
    + intros.
      apply Hy in H. apply H in H0 as H1.
      apply H0. apply H1.
  - unfold subset. intros.
    apply Hy. apply H0. apply H.
  - intros. apply extensionality.
    split; intros.
    + apply Hy in H0. apply H0. apply H.
    + apply Hy. destruct H.
      split.
      * apply (H1 x) in H0. apply H0. apply Hx.
      * intros. apply H1. apply H2. apply H0.
Qed.

Definition pred x := union x.

Lemma nat_ind_weak: forall (P: set->Prop),
  P n0 -> (forall n, P n -> P (succ n)) ->
    (forall n, n :i Nat -> P n).
Proof.
  intros P H0 IH n Hnat.
  destruct Infinity as [Inf HInf].
  assert (induction_set (sep P Inf)).
  { unfold induction_set.
    split.
    - apply sep_iff. split.
      + apply HInf.
      + apply H0.
    - intros. apply sep_iff. apply sep_iff in H.
      split.
      + apply HInf. apply H.
      + apply IH. apply H.
  }
  assert (Nat :s (sep P Inf)).
  { apply nat_exists. apply H. }
  apply H1 in Hnat.
  eapply sep_iff. eassumption.
Qed.

Lemma nat_ind: forall (P: set->Prop),
  P n0 -> (forall n, n :i Nat -> P n -> P (succ n)) ->
    (forall n, n :i Nat -> P n).
Proof.
  intros P H0 IH.
  set (P' := fun x => x :i Nat /\ P x).
  assert (forall n, n :i Nat -> P' n).
  { apply nat_ind_weak.
    - split.
      apply (proj1 nat_exists).
      apply H0.
    - intros. split.
      apply (proj1 nat_exists). apply H.
      apply IH.
      apply H. apply H.
  }
  intros.
  apply H. apply H1.
Qed.

Lemma nat_cases: forall x, x :i Nat -> x = n0 \/ exists y, x = succ y /\ y :i Nat.
Proof.
  apply nat_ind.
  - left. reflexivity.
  - intros. right. exists n. split; trivial.
Qed.

Lemma nat_trans: forall z, z :i Nat -> (forall x y, x :i y -> y :i z -> x :i z).
Proof.
  set (P := fun z => forall x y, x :i y -> y :i z -> x :i z).
  apply (nat_ind P).
  - intros x y Hxy Hyz.
    apply empty_set_no_elem in Hyz.
    inversion Hyz.
  - intros n Hn H.
    intros x y Hxy Hyz.
    apply succ_iff in Hyz. destruct Hyz.
    + subst y. apply biunion_subset_l. apply Hxy.
    + apply H in Hxy. apply Hxy in H0.
      apply biunion_subset_l. apply H0.
Qed.

Lemma pred_correct: forall x, x :i Nat -> pred (succ x) = x.
Proof.
  apply nat_ind.
  - apply extensionality. split; intros.
    + apply union_iff in H.
      destruct H.
      set_oper.
      * apply H, H0.
      * apply empty_set_no_elem in H. inversion H.
    + apply empty_set_no_elem in H. inversion H.
  - intros n Hn H.
    apply extensionality. split; intros.
    + apply union_iff in H0.
      destruct H0. destruct H0.
      apply succ_iff in H0.
      destruct H0.
      * subst x.
        apply H1.
      * eapply nat_trans; try eassumption.
        apply (proj1 nat_exists). apply Hn.
    + apply union_iff.
      rewrite succ_iff in H0. destruct H0.
      * subst u. exists (succ n).
        split; apply succ_iff; left; reflexivity.
      * exists n. split; try assumption.
        apply succ_iff. right.
        apply succ_iff. left. reflexivity.
Qed.

Lemma O_is_nat: n0 :i Nat.
Proof.
  destruct (nat_exists).
  apply H.
Qed.

Lemma succ_nat: forall x, x :i Nat -> succ x :i Nat.
Proof.
  intros.
  destruct (nat_exists).
  apply H0. apply H.
Qed.

Lemma one_is_nat: n1 :i Nat.
Proof.
  apply succ_nat, O_is_nat.
Qed.

Definition lt m n := m :i n.
Definition le m n := lt m n \/ m = n.

Lemma nat_elem_is_nat: forall m n, n :i Nat -> m :i n -> m :i Nat.
Proof.
  intros m n Hn.
  apply nat_ind with (P := fun n => m :i n -> m :i Nat).
  - intros H. apply empty_set_no_elem in H.
    inversion H.
  - intros.
    rewrite succ_iff in H1. destruct H1.
    + subst m. assumption.
    + apply H0 in H1. apply H1.
  - apply Hn.
Qed.

Lemma n_lt_m__Sn_le_m: forall m n,
  n :i Nat -> lt m n -> le (succ m) n.
Proof.
  intros m n Hn.
  unfold le, lt.
  apply nat_ind with (P := fun n => m :i n -> succ m :i n \/ succ m = n).
  - intros H. apply empty_set_no_elem in H. inversion H.
  - intros.
    rewrite succ_iff in H1. destruct H1.
    + subst m. right. reflexivity.
    + left. apply succ_iff.
      apply H0 in H1. destruct H1; [right | left]; apply H1.
  - apply Hn.
Qed.

Lemma lt_implies_le: forall m n, lt m n -> le m n.
Proof.
  unfold le, lt.
  intros.
  left. apply H.
Qed.

Lemma lt_trans: forall m n o, o :i Nat -> lt m n -> lt n o -> lt m o.
Proof.
  unfold lt.
  intros m n o Ho.
  generalize dependent m.
  generalize dependent n.
  apply nat_ind with (n := o).
  - intros.
    apply empty_set_no_elem in H0.
    inversion H0.
  - intros.
    apply succ_iff in H2.
    destruct H2.
    + subst n3. apply succ_iff. right. trivial.
    + apply H0 in H1; trivial. apply succ_iff. right. trivial.
  - apply Ho.
Qed.

Lemma not_n_lt_zero: forall x, ~lt x n0.
Proof.
  unfold lt, le, not, subset.
  intros.
  apply empty_set_no_elem in H.
  apply H.
Qed.

Lemma zero_le_n: forall n, n :i Nat -> le n0 n.
Proof.
  unfold le, lt.
  apply nat_ind.
  - right. trivial.
  - intros. left.
    apply succ_iff.
    destruct H0.
    + right. trivial.
    + left. trivial.
Qed.

Lemma tighter_subset: excluded_middle -> forall x y z,
  x :s y -> intersection x z = empty_set -> x :s (diff y z).
Proof.
  intros EM. intros.
  set_oper; unfold not; classic.
  assert (u :i intersection x z) by (apply intersection_iff; split; trivial).
  apply H0 in H3.
  apply empty_set_no_elem in H3.
  inversion H3.
Qed.

Lemma subset_implies_proper_subset_or_eq:
  excluded_middle -> forall x y, x :s y -> x :ps y \/ x = y.
Proof.
  intros EM. intros.
  destruct (EM (x :ps y)).
  - left. apply H0.
  - right. apply extensionality.
    split; intros.
    + apply H. apply H1.
    + unfold proper_subset in H0.
      apply not_and_iff in H0; trivial.
      destruct H0.
      * destruct (H0 H).
      * rewrite (not_exists_iff EM) in H0.
        assert (~u :i y \/ ~~u :i x) by (rewrite <- (not_and_iff EM); apply H0).
        destruct H2.
        -- destruct (H2 H1).
        -- apply (double_neg EM). trivial.
Qed.

Lemma nat_in_iff_proper_subset: excluded_middle ->
  forall m n, m :i Nat -> n :i Nat -> m :ps n <-> m :i n.
Proof.
  intros EM.
  split; intros.
  - generalize dependent m.
    apply nat_ind with (n := n).
    + intros. destruct H1. destruct H2. destruct H2.
      apply empty_set_no_elem in H2. inversion H2.
    + intros.
      destruct H3 as [Hs [x [Hxn3 Hxm]]].
      assert (~n3 :i m).
      { unfold not. intros contra.
        assert (n3 :s m).
        { unfold subset. intros.
          apply lt_trans with (n := n3); trivial. }
        apply succ_iff in Hxn3.
        destruct Hxn3.
        - subst x.
          apply Hxm in contra. inversion contra.
        - apply H3 in H4. apply Hxm in H4. inversion H4.
      }
      assert (m :s n3).
      { replace n3 with (diff (succ n3) (singleton n3)).
        apply tighter_subset; trivial.
        apply subset_antisymmetric.
        - unfold subset. intros.
          apply intersection_iff in H4.
          destruct H4.
          apply singleton_iff in H5.
          subst u.
          apply H3 in H4. inversion H4.
        - apply empty_subset.
        - apply extensionality.
          split; intros.
          + apply diff_iff in H4. destruct H4.
            apply succ_iff in H4.
            rewrite singleton_iff in H5.
            destruct H4.
            * subst u. destruct (H5 (eq_refl n3)).
            * trivial.
          + apply diff_iff.
            split.
            * apply succ_iff. right. trivial.
            * rewrite singleton_iff. unfold not. intros contra.
              subst u. apply no_self_ref in H4. inversion H4.
      }
      apply (subset_implies_proper_subset_or_eq EM) in H4.
      destruct H4.
      * apply H1 in H4; trivial. apply succ_iff. right. trivial.
      * subst m. apply succ_iff. left. trivial.
    + trivial.
  - destruct (nat_cases n).
    + trivial.
    + subst n. apply empty_set_no_elem in H1. contradiction.
    + destruct H2. destruct H2. subst n.
      apply succ_iff in H1.
      destruct H1.
      * subst m. split.
          apply biunion_subset_l.
          exists x. split. apply succ_iff. left. trivial.
            apply no_self_ref.
      * split.
          unfold subset. intros. apply lt_trans with (n := m); trivial.
            apply lt_trans with (n := x); trivial.
            apply succ_iff. left. trivial.
          exists x. split.
            apply succ_iff. left. trivial.
            unfold not. intro contra.
            apply (lt_trans m x m) in H1; trivial.
            destruct (no_self_ref m H1).
Qed.

Lemma proper_subset_trans_l: forall x y z, x :ps y -> y :s z -> x :ps z.
Proof.
  unfold proper_subset, subset.
  split; intros.
  - apply H0. apply H. apply H1.
  - destruct (proj2 H).
    exists x0. split.
    + apply H0. apply H1.
    + apply H1.
Qed.

Lemma proper_subset_trans_r: forall x y z, x :s y -> y :ps z -> x :ps z.
Proof.
  intros. split.
  - eapply subset_trans. apply H. apply H0.
  - destruct H0 as [Hs [u Hu]].
    exists u. split.
      apply Hu.
      unfold not. intros contra.
      apply H in contra. apply (proj2 Hu) in contra.
      inversion contra.
Qed.

Lemma union_singleton: forall x, union (singleton x) = x.
Proof.
  intros. apply extensionality.
  split; intros.
  - apply union_iff in H.
    destruct H as [y [Hyx Huy]].
    apply singleton_iff in Hyx.
    subst y. apply Huy.
  - apply union_iff.
    exists x.
    split.
    + apply singleton_iff. reflexivity.
    + apply H.
Qed.

Definition fun_apply Y (f: set->set->Prop) x := union (sep (f x) Y).

Lemma fun_apply_correct: forall X Y (f: set->set->Prop) x,
  function X Y f ->
  x :i X ->
  f x (fun_apply Y f x).
Proof.
  intros.
  destruct H.
  apply H1 in H0 as H2.
  destruct H2 as [y [Hy Hfxy]].
  unfold fun_apply.
  assert (sep (f x) Y = singleton y).
  { apply extensionality.
    split; intros.
    - apply singleton_iff.
      apply sep_elem_prop in H2.
      apply (H x); trivial.
    - apply singleton_iff in H2.
      apply sep_iff.
      subst u.
      split; trivial.
  }
  rewrite H2.
  rewrite union_singleton.
  apply Hfxy.
Qed.

Lemma zero_not_succ: forall n, n0 <> succ n.
Proof.
  intros.
  assert (n :i succ n).
  { apply succ_iff. left. reflexivity. }
  unfold not. intro contra.
  rewrite <- contra in H.
  apply empty_set_no_elem in H.
  contradiction.
Qed.

Lemma n_lt_Sn: forall n, lt n (succ n).
Proof.
  intros.
  apply succ_iff. left. trivial.
Qed.

Lemma Sn_le_m__n_lt_m: forall n m, m :i Nat -> le (succ n) m -> lt n m.
Proof.
  intros n m Hm H.
  destruct H.
  - apply lt_trans with (n := succ n); trivial.
    apply n_lt_Sn.
  - rewrite <- H. apply n_lt_Sn.
Qed.

Lemma n_le_m__n_lt_Sm: forall n m, m :i  Nat -> le n m -> lt n (succ m).
Proof.
  intros n m Hm H.
  destruct H.
  - apply lt_trans with (n := m); trivial.
    apply succ_nat. apply Hm.
    apply n_lt_Sn.
  - rewrite H. apply n_lt_Sn.
Qed.

Lemma n_lt_Sm__n_le_m: forall n m, m :i Nat -> lt n (succ m) -> le n m.
Proof.
  intros n m Hm H.
  apply succ_iff in H.
  destruct H.
  - rewrite H. right. trivial.
  - apply lt_implies_le. trivial.
Qed.

Lemma Sn_lt_Sm__n_lt_m: forall n m, m :i Nat -> lt (succ n) (succ m) -> lt n m.
Proof.
  intros n m Hm H.
  apply n_lt_Sm__n_le_m in H; trivial.
  apply Sn_le_m__n_lt_m; trivial.
Qed.

Lemma not_Sn_le_n: forall n, n :i Nat -> ~ le (succ n) n.
Proof.
  unfold not.
  intros.
  apply Sn_le_m__n_lt_m in H0; trivial.
  apply no_self_ref in H0.
  contradiction.
Qed.

Lemma n_lt_m__Sn_lt_Sm: forall n m, m :i Nat ->
  lt n m -> lt (succ n) (succ m).
Proof.
  intros.
  apply n_le_m__n_lt_Sm; trivial.
  apply n_lt_m__Sn_le_m; trivial.
Qed.

Lemma Sn_eq_Sm__n_subset_m: forall n m, n :i Nat -> succ n = succ m -> n :s m.
Proof.
  unfold subset.
  intros.
  assert (u :i succ n).
  { apply succ_iff. right. trivial. }
  rewrite H0 in H2. apply succ_iff in H2.
  destruct H2.
  - subst u. apply n_lt_m__Sn_le_m in H1; trivial.
    rewrite <- H0 in H1. apply not_Sn_le_n in H1; trivial.
    contradiction.
  - trivial.
Qed.

Lemma zero_lt_Sn: forall n, n :i Nat -> lt n0 (succ n).
Proof.
  intros.
  apply n_le_m__n_lt_Sm; trivial.
  apply zero_le_n; trivial.
Qed.


Lemma succ_injective: forall n m, n :i Nat -> succ n = succ m -> n = m.
Proof.
  intros.
  apply subset_antisymmetric.
  - apply Sn_eq_Sm__n_subset_m; trivial.
  - apply succ_nat in H. rewrite H0 in H.
    symmetry in H0.
    apply Sn_eq_Sm__n_subset_m; trivial.
    apply nat_elem_is_nat with (n := succ m); trivial.
    apply n_lt_Sn.
Qed.

Lemma n_neq_Sn: forall n, n <> succ n.
Proof.
  unfold not.
  intros.
  assert (n :i n).
  { rewrite H at 2. apply succ_iff. left. trivial. }
  apply no_self_ref in H0.
  contradiction.
Qed.

Lemma lt_trichotomous: forall m n, m :i Nat -> n :i Nat ->
  lt m n \/ lt n m \/ n = m.
Proof.
  intros m n Hm.
  generalize dependent n.
  apply nat_ind with (n := m).
  - intros n Hn. destruct (nat_cases n Hn).
    + subst n.
      right. right. trivial.
    + left. destruct H as [n' [Hn' Hn'nat]]. subst n.
      apply zero_lt_Sn; trivial.
  - intros n Hn IH n' Hn'.
    destruct (IH n' Hn').
    + apply n_lt_m__Sn_le_m in H.
      destruct H.
      * left. trivial.
      * right. right. symmetry. trivial.
      * trivial.
    + destruct H.
      * right. left. apply lt_trans with (n := n); trivial.
        apply succ_nat; trivial.
        apply n_lt_Sn.
      * subst n. right. left. apply n_lt_Sn.
  - trivial.
Qed.

Lemma not_le_implies_lt: forall m n,
  m :i Nat -> n :i Nat -> ~le n m -> lt m n.
Proof.
  intros m n Hm Hn H.
  destruct (lt_trichotomous m n Hm Hn).
  - apply H0.
  - destruct H0.
    + apply lt_implies_le in H0.
      destruct (H H0).
    + assert (le n m) by (right; trivial).
      destruct (H H1).
Qed.

Lemma not_lt_implies_le: forall m n,
  m :i Nat -> n :i Nat -> ~lt n m -> le m n.
Proof.
  intros m n Hm Hn H.
  destruct (lt_trichotomous m n Hm Hn).
  - apply lt_implies_le. trivial.
  - destruct H0.
    + destruct (H H0).
    + right. symmetry. trivial.
Qed.

Lemma le_trans: forall m n o, o :i Nat -> le m n -> le n o -> le m o.
Proof.
  unfold le.
  intros.
  destruct H0, H1.
  - left. eapply lt_trans; eauto.
  - left. subst n. trivial.
  - left. subst m. trivial.
  - right. subst m. trivial.
Qed.

Lemma function2_restrict2:
  forall X1 X2 S Y (f: set->set->set->Prop),
    function2 X1 X2 Y f -> S :s X2 -> function2 X1 S Y f.
Proof.
  intros.
  destruct H.
  split.
  - intros x1 x2 Hx1 Hx2 y y' Hy Hy'.
    apply H0 in Hx2.
    apply (H x1 x2 Hx1 Hx2 y y' Hy Hy').
  - intros x1 x2 Hx1 Hx2.
    apply H0 in Hx2.
    apply (H1 x1 x2 Hx1 Hx2).
Qed.

Lemma lt_one: forall n, n :i n1 -> n = n0.
Proof.
  intros.
  apply succ_iff in H.
  destruct H; trivial.
  apply empty_set_no_elem in H.
  contradiction.
Qed.

Lemma not_Sn_lt_n: forall n, n :i Nat -> ~lt (succ n) n.
Proof.
  unfold not.
  intros.
  apply (lt_trans n (succ n) n) in H0; trivial.
  destruct (no_self_ref n H0).
  apply n_lt_Sn.
Qed.

Lemma fun_ran: forall X Y f x y,
  function X Y f -> x :i X -> f x y -> y :i Y.
Proof.
  intros.
  destruct H.
  apply H2 in H0 as H3.
  destruct H3.
  destruct H3.
  rewrite (H x H0 y x0); trivial.
Qed.

Lemma fun2_ran: forall X1 X2 Y f x1 x2 y,
  function2 X1 X2 Y f -> x1 :i X1 -> x2 :i X2 -> f x1 x2 y -> y :i Y.
Proof.
  intros.
  destruct H.
  apply (H3 x1 x2 H0) in H1 as H4.
  destruct H4.
  destruct H4.
  rewrite (H x1 x2 H0 H1 y x); trivial.
Qed.

Lemma fun3_ran: forall X1 X2 X3 Y f x1 x2 x3 y,
  function3 X1 X2 X3 Y f -> x1 :i X1 -> x2 :i X2 -> x3 :i X3 ->
    f x1 x2 x3 y -> y :i Y.
Proof.
  intros.
  destruct H.
  apply (H4 x1 x2 x3 H0 H1) in H2 as H5.
  destruct H5. destruct H5.
  rewrite (H x1 x2 x3 H0 H1 H2 y x); trivial.
Qed.

Lemma cp_subset_l: forall X Y S, S :s X -> S**Y :s X**Y.
Proof.
  unfold subset.
  intros.
  apply cp_iff in H0.
  apply cp_iff.
  destruct H0 as [x [y [Hx [Hy Hu]]]].
  exists x, y.
  apply H in Hx.
  split; [ | split]; trivial.
Qed.

Lemma cp_subset_r: forall X Y S, S :s Y -> X**S :s X**Y.
Proof.
  unfold subset.
  intros.
  apply cp_iff in H0.
  apply cp_iff.
  destruct H0 as [x [y [Hx [Hy Hu]]]].
  exists x, y.
  apply H in Hy.
  split; [ | split]; trivial.
Qed.



Section Recursion.

Variable P: set.
Variable A: set.
Variable a: set->set->Prop.
Variable g: set->set->set->set->Prop.
Variable Ha: function P A a.
Variable Hg: function3 P A Nat A g.


Definition approx (n: set) (f: set->set->set->Prop) :=
  function2 P (succ n) A f /\
  (forall p y, p :i P -> (f p n0 y <-> a p y)) /\
    (forall m p y, p :i P -> m :i Nat -> lt m n ->
      (f p (succ m) y <-> (forall y', f p m y' -> g p y' m y))).

Lemma approx_restrict: forall n m (f: set->set->set->Prop),
  m :i Nat -> le n m -> approx m f -> approx n f.
Proof.
  unfold approx.
  intros.
  destruct H0.
  - split; [| split].
    + eapply function2_restrict2. apply H1.
      unfold subset. intros u Hsn.
      apply succ_iff in Hsn.
      destruct Hsn.
      * subst u. apply lt_trans with (n := m); trivial.
        exact (succ_nat m H). apply n_lt_Sn.
      * apply lt_trans with (n := n); trivial.
        exact (succ_nat m H).
        apply lt_trans with (n := m); trivial.
        exact (succ_nat m H).
        apply n_lt_Sn.
    + apply H1.
    + intros. apply H1; trivial.
      apply lt_trans with (n := n); trivial.
  - subst n. apply H1.
Qed.

Lemma approx_unique: forall n (f1 f2: set->set->set->Prop),
  n :i Nat ->
  approx n f1 -> approx n f2 ->
  forall p m y, le m n -> p :i P -> (f1 p m y <-> f2 p m y).
Proof.
  intros n f1 f2 Hn Happrox1 Happrox2 p m y Hm.
  generalize Hm.
  generalize dependent y.
  apply nat_ind with (n := m).
  - intros y Hlt Hp. split; intros.
    + apply Happrox2; trivial.
      apply Happrox1; trivial.
    + apply Happrox1; trivial.
      apply Happrox2; trivial.
  - intros m' Hm' IH y Hlt Hp.
    assert (lt m' n) by (apply Sn_le_m__n_lt_m; trivial).
    split; intros.
    + apply Happrox2; trivial.
      intros y' Hy'.
      apply Happrox1; trivial.
      apply IH; trivial.
      apply lt_implies_le; trivial.
    + apply Happrox1; trivial.
      intros y' Hy'.
      apply Happrox2; trivial.
      apply IH; trivial.
      apply lt_implies_le; trivial.
  - destruct (Hm); [eapply nat_elem_is_nat | subst m]; eauto.
Qed.

Definition bounded_dom n (f: set->set->set->Prop) :=
  (forall p m y, m :i Nat -> f p m y -> le m n).

Ltac destruct_op :=
  repeat match goal with
    | [H: _,,_ = _,,_ |- _] =>
        rewrite ordered_pair_injective in H; destruct H
    | [_:_ |- _,,_ = _,,_] =>
        rewrite ordered_pair_injective; split
    | [H: _,,_ :i _ ** _ |- _] => rewrite cp_iff_op in H; destruct H
    | [_:_ |- _,,_ :i _ ** _] => apply cp_iff_op; split
  end.

Ltac order_contra :=
  autoelim; match goal with
    | [H: lt ?n ?n |- _] => destruct (no_self_ref n H)
    | [H: ?n :i ?n |- _] => destruct (no_self_ref n H)
  end.

Lemma approx_function_exists:
  forall n, n :i Nat -> exists f,
    f :s P**Nat**A /\
    approx n (cast_rel3 f) /\
    bounded_dom n (cast_rel3 f).
Proof.
  apply nat_ind.
  - destruct Ha.
    exists (uncast_rel3 P Nat A (fun p n y => n = n0 /\ a p y)).
    split; [ | split].
    + apply sep_subset.
    + split.
      * split.
        -- intros p n Hp Hn y y' Hy Hy'.
           unfold cast_rel3, uncast_rel3 in *.
           apply sep_iff in Hy. apply sep_iff in Hy'.
           assert (n = n0).
              { apply (proj2 Hy p n y). trivial. }
           assert (a p y).
           { apply (proj2 Hy p n y).
              destruct_op; trivial. }
           assert (a p y').
           { apply (proj2 Hy' p n y').
             destruct_op; trivial. }
           apply (H p Hp y y' H2 H3).
        -- intros.
           destruct (H0 x1 H1).
           exists x.
           split; [apply H3 | ].
           apply sep_iff.
           split.
           ++ destruct_op; trivial.
              eapply nat_elem_is_nat; eauto.
              apply succ_nat. apply O_is_nat.
              apply H3.
           ++ intros. destruct_op; split; subst; trivial.
              apply lt_one in H2.
              trivial.
              apply H3.
      * split.
        -- split; intros.
           ++ apply sep_iff in H2.
              apply (proj2 H2 p n0 y).
              trivial.
           ++ apply sep_iff.
              split.
              ** destruct_op; trivial.
                 apply O_is_nat.
                 eapply fun_ran; eauto.
              ** intros. destruct_op; split; subst; trivial.
           -- intros.
              apply empty_set_no_elem in H3.
              contradiction.
     + unfold bounded_dom. intros.
       apply sep_iff in H2.
       destruct H2.
       right.
       apply (H3 p m y).
       trivial.
  - intros.
    destruct H0.
    exists (uncast_rel3 P (succ (succ n)) A
      (fun p m y => lt m (succ n) /\ cast_rel3 x p m y \/
        m=succ n /\ (forall y', cast_rel3 x p n y' -> g p y' n y))).
    destruct H0 as [Hrel [[[Hpf Hdf] Happrox] Hdom]].
    split; [ | split; [split; split | ]].
    + eapply subset_trans.
      apply sep_subset.
      apply cp_subset_r.
      apply cp_subset_l.
      unfold subset.
      intros.
      apply nat_elem_is_nat in H0; trivial.
      apply succ_nat; trivial.
      apply succ_nat; trivial.
    + intros p m Hp Hm y y' Hy Hy'.
      apply succ_iff in Hm.
      apply sep_iff in Hy. apply sep_iff in Hy'.
      destruct Hy as [Hdomy Hy].
      destruct Hy' as [Hdomy' Hy'].
      destruct Hm as [Hm | Hm].
      * destruct Hg as [Hpg Hdg].
        destruct (Hdf p n Hp).
        apply succ_iff. left. trivial.
        apply (Hpg p x0 n Hp (proj1 H0) H y y');
        [destruct (Hy p m y (eq_refl (p,,m,,y)))|
         destruct (Hy' p m y' (eq_refl (p,,m,,y')))];
           subst; try order_contra;
           try (apply H1; apply H0).
      * apply (Hpf p m Hp Hm y y');
        [destruct (Hy p m y) | destruct (Hy' p m y')];
          trivial; try apply H0;
          autoelim; subst; try order_contra.
    + intros p m Hp Hm.
      apply succ_iff in Hm.
      destruct Hm as [Hm | Hm].
      * destruct (Hdf p n Hp).
        apply n_lt_Sn.
        destruct Hg as [Hpg Hdg].
        destruct (Hdg p x0 n Hp (proj1 H0) H).
        exists x1.
        split; [apply H1 | ].
        apply sep_iff.
        split.
        -- destruct_op; trivial.
           subst m. apply n_lt_Sn.
           apply H1.
        -- intros. destruct_op; subst.
           right. split; trivial.
           intros.
           rewrite (Hpf p n Hp (n_lt_Sn n) y' x0 H2 (proj2 H0)).
           apply H1.
      * destruct (Hdf p m Hp Hm).
        exists x0.
        split; [apply H0 | ].
        apply sep_iff.
        split.
        -- destruct_op; trivial.
           apply lt_trans with (n := succ n); trivial.
           apply succ_nat. apply succ_nat. trivial.
           apply n_lt_Sn.
           apply H0.
        -- intros. destruct_op; subst.
           left. split; trivial.
           apply H0.
    + intros p y Hp.
      split; intros.
      * rename H0 into Hf.
        apply sep_iff in Hf.
        destruct Hf.
        destruct (H1 p n0 y); trivial.
        -- destruct H2.
           apply Happrox; trivial.
        -- destruct (zero_not_succ n (proj1 H2)).
      * apply Happrox in H0; trivial.
        apply sep_iff.
        split.
        -- repeat rewrite cp_iff_op.
           repeat split; trivial.
           apply zero_lt_Sn.
           exact (succ_nat n H).
           destruct (Hdf p n0); trivial.
           apply zero_lt_Sn; trivial.
           destruct H1.
           rewrite (Hpf p n0 Hp (zero_lt_Sn n H) y x0 H0 H2).
           assumption.
        -- intros. left. destruct_op; subst.
           split.
             exact (zero_lt_Sn n H).
             assumption.
    + intros m p y Hp Hm Hlt. split; intros.
      * apply sep_iff in H0.
        assert (p,,succ m,,y = p,,succ m,,y) by (reflexivity).
        apply (proj2 H0) in H2.
        assert (p,,m,,y'=p,,m,,y') by reflexivity.
        apply sep_iff in H1.
        apply (proj2 H1) in H3.
        apply succ_iff in Hlt.
        destruct Hlt, H2.
        -- subst m. destruct (no_self_ref (succ n) (proj1 H2)).
        -- subst m. apply H2.
           destruct H3.
           ++ apply H3.
           ++ destruct (n_neq_Sn n (proj1 H3)).
        -- destruct H3.
           ++ apply Happrox; trivial. apply H2. apply H3.
           ++ rewrite (proj1 H3) in H4.
              destruct (not_Sn_lt_n n H H4).
        -- destruct H2. apply succ_injective in H2; trivial.
           subst m.
           destruct (no_self_ref n H4).
      * apply sep_iff.
        split.
        -- destruct_op; trivial.
           apply n_lt_m__Sn_lt_Sm; trivial.
           exact (succ_nat n H).
           destruct (Hdf p m); trivial.
           destruct H1.
           eapply fun3_ran; eauto.
           apply H0.
           apply sep_iff.
           split.
           destruct_op; trivial.
           apply lt_trans with (succ n); trivial.
           apply succ_nat; trivial. apply succ_nat; trivial.
           apply n_lt_Sn.
           intros.
           destruct_op; subst.
           left. split; trivial.
        -- intros.
           assert (m :i succ (succ n)).
           { apply lt_trans with (succ n); trivial.
             repeat apply succ_nat; trivial.
             apply n_lt_Sn. }
           apply succ_iff in Hlt.
           destruct_op; subst.
           destruct Hlt.
           ++ subst m. right. split; trivial.
              intros.
              apply H0.
              apply sep_iff. split.
              destruct_op; trivial.
              eapply fun2_ran.
              apply (conj Hpf Hdf).
              apply Hp.
              apply n_lt_Sn.
              apply H1.
              intros.
              destruct_op; subst.
              left. split; [apply n_lt_Sn | trivial].
           ++ left.
              split; [apply n_lt_m__Sn_lt_Sm | ]; trivial.
              apply Happrox; trivial.
              intros.
              assert (lt m (succ n)).
              { apply lt_trans with n; trivial.
                apply succ_nat; trivial.
                apply n_lt_Sn. }
              apply H0.
              apply sep_iff.
              split; [destruct_op; trivial | ].
              eapply fun2_ran in H3; trivial.
              apply H3.
              apply (conj Hpf Hdf).
              trivial. trivial.
              intros.
              destruct_op; subst.
              left.
              split; trivial.
    + intros p m y Hm Hy.
      apply sep_iff in Hy.
      destruct Hy. destruct_op.
      apply n_lt_Sm__n_le_m; trivial.
      apply succ_nat; trivial.
Qed.

Definition f := (union (sep
      (fun f => exists n, n :i Nat /\
        approx n (cast_rel3 f) /\
        bounded_dom n (cast_rel3 f)) 
    (power_set (P ** Nat ** A)))).

Ltac fapp :=
  match goal with
    | [H: cast_rel3 f _ _ _ |- _] =>
        unfold cast_rel3, f in H;
        apply union_iff in H;
        destruct H;
        repeat autoelim;
        try match goal with
          | [H: _ :i sep _ _ |- _] =>
              apply sep_iff in H
        end;
        repeat autoelim;
        try match goal with
          | [H: exists _, _ :i Nat /\ _ |- _] =>
              destruct H
        end
  end.

Lemma f_correct1: forall p y, p :i P -> (cast_rel3 f p n0 y <-> a p y).
Proof.
  split; intros.
  - fapp.
    apply H3; trivial.
  - apply union_iff.
    destruct (approx_function_exists n0 O_is_nat) as [f0 Hf0].
    unfold approx in Hf0.
    exists f0.
    split.
    + apply sep_iff.
      split.
      * apply power_set_iff. apply Hf0.
      * exists n0.
        split; [apply O_is_nat | ].
        apply Hf0.
    + apply Hf0; trivial.
Qed.

Lemma f_correct2: (forall m p y y',
  p :i P -> m :i Nat ->
    cast_rel3 f p m y -> (cast_rel3 f p (succ m) y' <-> g p y m y')).
Proof.
  intros.
  split; intros.
  - fapp. fapp.
    autoelim.
    assert (succ m :i Nat) by (apply succ_nat; trivial).
    apply H6 in H3 as Hsmx0; trivial.
    apply H10 in H7 as Hmx2; trivial.
    apply H5; trivial.
    + apply Sn_le_m__n_lt_m; trivial.
    + assert (approx m (cast_rel3 x1)).
      { apply approx_restrict with (m := x2); trivial. }
      assert (approx m (cast_rel3 x)).
      { apply approx_restrict with (m := x0); trivial.
        apply le_trans with (n := succ m); trivial.
        apply lt_implies_le. apply n_lt_Sn. }
      apply (approx_unique m (cast_rel3 x1) (cast_rel3 x) H0 H12 H13 p m y); trivial.
      right. trivial.
  - fapp.
    autoelim.
    apply H6 in H3 as Hmx0; trivial.
    unfold f.
    apply union_iff.
    destruct (approx_function_exists (succ m) (succ_nat m H0)) as [f' Hf'].
    exists f'.
    split.
    + apply sep_iff.
      split.
      * apply power_set_iff. apply Hf'.
      * exists (succ m).
        split.
        -- exact (succ_nat m H0).
        -- apply Hf'.
    + autoelim.
      assert (approx m (cast_rel3 x)).
      { apply approx_restrict with (m := x0); trivial. }
      assert (approx m (cast_rel3 f')).
      { apply approx_restrict with (m := succ m); trivial.
        exact (succ_nat m H0).
        apply lt_implies_le, n_lt_Sn. }
      apply (approx_unique m (cast_rel3 x) (cast_rel3 f') H0 H10 H11 p m y) in H3; trivial.
      apply H8; trivial.
      apply n_lt_Sn.
      intros.
      destruct H8.
      destruct H8.
      assert (m :i succ (succ m)).
      { apply lt_trans with (succ m).
        exact (succ_nat (succ m) (succ_nat m H0)).
        apply n_lt_Sn.
        apply n_lt_Sn. }
      apply (H8 p m H H15 y'0 y) in H12; trivial.
      subst y'0.
      trivial.
      right. trivial.
Qed.

Theorem nat_rec: exists f,
  function2 P Nat A f /\
  (forall p y, p :i P -> (f p n0 y <-> a p y)) /\
    (forall m p y y', p :i P -> m :i Nat ->
      f p m y -> (f p (succ m) y' <-> g p y m y')).
Proof.
  exists (cast_rel3 f).
  split.
  - split.
    + intros p m Hp Hm y y' Hy Hy'.
      fapp. fapp.
      autoelim.
      apply H8 in H5 as Hmx2; trivial.
      apply H3 in H0 as Hmx0; trivial.
      apply (approx_restrict m) in H2 as Happrox1; trivial.
      apply (approx_restrict m) in H7 as Happrox2; trivial.
      apply (approx_unique m (cast_rel3 x) (cast_rel3 x1) Hm Happrox1 Happrox2 p m y') in H0 as Hx1y'; trivial.
      destruct H7. destruct H7.
      assert (m :i (succ x2)).
      { apply n_le_m__n_lt_Sm; trivial. }
      apply (H7 p m Hp H11 y' y) in Hx1y'; trivial.
      symmetry. trivial.
      right. trivial.
    + intros.
      destruct (approx_function_exists x2 H0).
      destruct H1. destruct H2.
      assert (approx x2 (cast_rel3 x)) as Happrox by trivial.
      destruct H2. destruct H2.
      destruct (H5 x1 x2 H (n_lt_Sn x2)).
      exists x0.
      split.
      * apply H6.
      * apply union_iff.
        exists x.
        split.
        -- apply sep_iff.
           split.
           ++ apply power_set_iff. apply H1.
           ++ exists x2. split; trivial.
              split; trivial.
        -- apply H6.
  - apply (conj f_correct1 f_correct2).
Qed.

End Recursion.


Definition initial_segment X R I := total_order R /\ I :s X /\
  forall x y, x :i I -> y :i X -> R y x -> y :i I.
Definition strict_initial_segment X R I := strict_total_order R /\ I :s X /\
  forall x y, x :i I -> y :i X -> R y x -> y :i I.

Definition proper_initial_segment X R I := initial_segment X R I /\ I :ps X.
Definition strict_proper_initial_segment X R I
  := strict_initial_segment X R I /\ I :ps X.

Definition transitive_set X := forall x, x :i X -> x :s X.
Definition ordinal_number x := transitive_set x /\ strict_well_order x In.

Definition maximal_elem_prop X R := forall S,
  S :s X -> nonempty S -> exists a, maximal_elem S R a.

Definition inf_prop X R := forall S,
  S :s X -> (exists a, lower_bound X R S a) -> exists a, inf X R S a.
Definition sup_prop X R := forall S,
  S :s X -> (exists a, upper_bound X R S a) -> exists a, sup X R S a.

Lemma ordinal_elem: forall x y,
  ordinal_number x -> y :i x -> ordinal_number y.
Proof.
  unfold ordinal_number, transitive_set. intros.
  destruct H.
  split.
  - unfold subset. intros.
    apply ((proj2 (proj1 (proj1 H1))) u x0 y); auto.
  - apply swo_subset with x; auto.
Qed.

Lemma wo_init_seg_sup: excluded_middle -> forall W R S,
  strict_well_order W R ->
    strict_proper_initial_segment W R S ->
      exists a, a :i W /\ S = sep (fun x => R x a) W.
Proof.
  intros EM W R S. intros.
  assert (W -- S :s W).
  { set_oper. }
  destruct H. apply H2 in H1 as H3.
  destruct H0. destruct H4. destruct H5.
  assert (nonempty (W -- S)).
  { exists x. apply diff_iff. apply H5. }
  apply H3 in H6. destruct H6.
  exists x0. split.
  - apply H1. apply H6.
  - apply extensionality. split; intros.
    + apply sep_iff. split.
      * apply H0. apply H7.
      * destruct (proj2 H) with u x0 as [H8|H8].
        -- apply H8.
        -- assert (x0 :i W -- S). apply H6.
           apply diff_iff in H9. destruct H9.
           destruct H8.
           ++ assert (x0 :i S).
              { apply (proj2 (proj2 H0)) with u; auto. }
              contradiction.
           ++ rewrite H8 in H7. contradiction.
    + destruct (EM (u :i S)).
      * apply H8.
      * assert (u :i W -- S).
        { apply diff_iff. split.
          - apply sep_subset in H7. apply H7.
          - apply H8. }
        apply H6 in H9.
        destruct H9.
        -- apply sep_iff in H7. rewrite H9 in H7.
           destruct H7.
           apply H in H10. inversion H10.
        -- apply sep_iff in H7 as H10.
           destruct H10.
           apply ((proj2 (proj1 H)) u x0 u) in H11.
           apply H in H11. inversion H11.
           apply sep_subset in H7.
           apply H9.
Qed.

