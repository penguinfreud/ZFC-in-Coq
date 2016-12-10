Require Import Coq.Setoids.Setoid.

Definition excluded_middle := forall P: Prop, P \/ ~P.

Parameter set: Type.
Parameter In: set->set->Prop.
Parameter element: set.

Parameter descr: (set->Prop)->set.
Axiom Descr: forall (prop:set->Prop), (exists! x, prop x) -> prop (descr prop).

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

Lemma sep_exists: forall (test: set->Prop) x, is_sep test x (sep test x).
Proof.
  intros. unfold sep. apply Descr.
  unfold unique.
  destruct (Sep test x) as [y H].
  exists y.
  split; intros.
  - apply H.
  - apply extensionality. split; intros; [apply H0, H | apply H, H0]; apply H1.
Qed.

Lemma sep_subset: forall (test: set->Prop) x, sep test x :s x.
Proof.
  unfold subset. intros.
  apply sep_exists in H.
  apply H.
Qed.

Lemma sep_prop: forall (test: set->Prop) x, forall u, u :i sep test x -> test u.
Proof.
  intros.
  apply sep_exists in H. apply H.
Qed.

Lemma sep_idempotent: forall (test: set->Prop) x, sep test (sep test x) = sep test x.
Proof.
  intros. apply extensionality. intros.
  split; intros; apply sep_exists; apply sep_exists in H.
  - split; try apply H. destruct H.
    apply sep_subset in H. apply H.
  - split; try apply H. apply sep_exists. apply H.
Qed.


Definition empty_set := sep (fun x => False) element.
Definition nonempty x := exists u, u :i x.

Lemma empty_set_no_elem: forall x, ~x :i empty_set.
Proof.
  unfold not. intros. apply sep_exists in H.
  apply H.
Qed.

Lemma nonempty_correct: forall x, nonempty x -> x <> empty_set.
Proof.
  unfold not. intros.
  destruct H. rewrite H0 in H. apply empty_set_no_elem in H.
  inversion H.
Qed.

Lemma nonempty_complete: excluded_middle -> forall x,
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

Lemma empty_subset: forall x, empty_set :s x.
Proof.
  unfold subset. intros.
  apply sep_exists in H.
  destruct H. inversion H0.
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
  - apply sep_exists in H. apply H.
  - apply empty_set_no_elem in H. inversion H.
Qed.


Definition proper_subset x y := x :s y /\ exists u, u :i y /\ ~ u :i x.
Notation "x :ps y" := (proper_subset x y) (at level 62).


Definition is_pair x y z := forall u, u :i z <-> u=x \/ u=y.

Axiom Pair: forall x y, exists z, is_pair x y z.
Definition pair x y := descr (is_pair x y).

Lemma pair_exists: forall x y, is_pair x y (pair x y).
Proof.
  intros. unfold pair. apply Descr. unfold unique.
  destruct (Pair x y) as [z H].
  exists z.
  split; intros.
  - apply H.
  - apply extensionality. split; intros; [apply H0, H | apply H, H0]; apply H1.
Qed.

Lemma pair_comm: forall x y, pair x y = pair y x.
Proof.
  intros. apply extensionality.
  split; intros; apply pair_exists; apply pair_exists in H; destruct H; auto.
Qed.


Definition is_union x y := forall u, u :i y <-> (exists z, z :i x /\ u :i z).
Axiom Union: forall x, exists y, is_union x y.
Definition union x := descr (is_union x).

Lemma union_exists: forall x, is_union x (union x).
Proof.
  intros. unfold union. apply Descr.
  destruct (Union x) as [y H]. exists y.
  split; intros.
  - apply H.
  - apply extensionality. split; intros; [apply H0, H | apply H, H0]; apply H1.
Qed.

Lemma union_subset: forall x u, u :i x -> u :s union x.
Proof.
  intros. assert (is_union x (union x)); [apply union_exists|].
  unfold subset. intros.
  apply H0. exists u. auto.
Qed.


Definition biunion x y := union (pair x y).
Definition join x y := sep (fun u => u :i y) x.
Definition diff x y := sep (fun x => ~x :i y) x.
Notation "x -- y" := (diff x y) (at level 56, left associativity).

Lemma biunion_iff: forall x y u,
  u :i biunion x y <-> u :i x \/ u :i y.
Proof.
  split; intros.
  - apply union_exists in H.
    destruct H as [z [Hz Hz2]].
    apply pair_exists in Hz.
    destruct Hz as [Hz|Hz]; rewrite Hz in Hz2;
    [left|right]; trivial.
  - apply union_exists.
    destruct H; [exists x | exists y];
    split; trivial;
    apply pair_exists;
    [left|right]; trivial.
Qed.

Lemma join_iff: forall x y u,
  u :i join x y <-> u :i x /\ u :i y.
Proof.
  intros.
  split; intros;
  [apply sep_exists in H | apply sep_exists];
  destruct H; split; trivial.
Qed.

Lemma diff_iff: forall x y u, u :i x -- y <->
  u :i x /\ ~u :i y.
Proof.
  split; intros.
  - apply sep_exists in H. apply H.
  - apply sep_exists. apply H.
Qed.

Ltac set_oper :=
  repeat unfold subset; intros; match goal with
    | [_:_ |- _ = _] => try (apply extensionality; split; intros)
    | [H: _ = _ |- _] => try (apply extensionality in H; destruct H)
    | [_:_ |- ~_ :i empty_set] => apply empty_set_no_elem
    | [H: _ :i empty_set |- _] => apply empty_set_no_elem in H; inversion H
    | [_:_ |- _ :i biunion _ _] => rewrite ? biunion_iff, ? join_iff, ? diff_iff
    | [H: _ :i biunion _ _ |- _] => apply biunion_iff in H; destruct H
    | [_:_ |- _ :i join _ _] => apply join_iff; split
    | [H: _ :i join _ _ |- _] => apply join_iff in H; destruct H
    | [_:_ |- _ :i diff _ _] => apply diff_iff; split
    | [H: _ :i diff _ _ |- _] => apply diff_iff in H; destruct H
  end.

Ltac set_rewrite :=
  repeat rewrite ? biunion_iff, ? join_iff, ? diff_iff in *.

Lemma biunion_subset_l: forall x y, x :s biunion x y.
Proof.
  set_oper; auto.
Qed.

Lemma biunion_comm: forall x y, biunion x y = biunion y x.
Proof.
  repeat (set_oper; auto).
Qed.

Lemma biunion_subset_r: forall x y, y :s biunion x y.
Proof.
  intros. rewrite biunion_comm. apply biunion_subset_l.
Qed.

Lemma biuniona_assoc: forall x y z,
  biunion (biunion x y) z = biunion x (biunion y z).
Proof.
  repeat (set_oper; auto).
Qed.

Lemma join_comm: forall x y, join x y = join y x.
Proof.
  repeat (set_oper; auto).
Qed.

Lemma join_subset_l: forall x y, join x y :s x.
Proof.
  repeat (set_oper; auto).
Qed.

Lemma join_subset_r: forall x y, join x y :s y.
Proof.
  repeat (set_oper; auto).
Qed.

Lemma join_assoc: forall x y z, join (join x y) z = join x (join y z).
Proof.
  repeat (set_oper; auto).
Qed.

Lemma join_biunion_dist: forall x y z,
  join x (biunion y z) = biunion (join x y) (join x z).
Proof.
  repeat (set_oper; auto).
Qed.

Lemma join_empty_set: forall x, join empty_set x = empty_set.
Proof.
  repeat (set_oper; auto).
Qed.

Lemma join_idempotent: forall x, join x x = x.
Proof.
  repeat (set_oper; auto).
Qed.


Lemma biunion_empty_set: forall x, biunion empty_set x = x.
Proof.
  repeat (set_oper; auto).
Qed.

Lemma biunion_join_dist: forall x y z,
  biunion x (join y z) = join (biunion x y) (biunion x z).
Proof.
  repeat (set_oper; auto).
Qed.


Lemma empty_sub_x: forall x, empty_set -- x = empty_set.
Proof.
  intros.
  apply sep_empty_set.
Qed.

Lemma x_sub_empty: forall x, x -- empty_set = x.
Proof.
  repeat (set_oper; auto).
Qed.

Lemma diff_join_assoc: forall x y z, join x (y--z) = join x y -- z.
Proof.
  repeat (set_oper; auto).
Qed.

Lemma diff_join_biunion_assoc: excluded_middle ->
  forall x y z, x -- (join y z) = biunion (x -- y) (x -- z).
Proof.
  repeat set_oper; auto; unfold not in *; set_rewrite; intros; auto.
  - assert (u :i y \/ ~u :i y). apply H.
    destruct H2.
    + assert (u :i y -> ~u :i z).
      { unfold not. intros. apply H1. split; trivial. }
      apply H3 in H2.
      right. split; trivial.
    + left. split; trivial.
  - destruct H2. contradiction.
  - destruct H2. contradiction.
Qed.

Definition is_power_set x y := forall u, u :i y <-> u :s x.
Axiom Power_set: forall x, exists y, is_power_set x y.
Definition power_set x := descr (is_power_set x).

Lemma power_set_exists: forall x, is_power_set x (power_set x).
Proof.
  intros. unfold power_set. apply Descr.
  destruct (Power_set x) as [y H]. exists y.
  split; intros.
  - apply H.
  - apply extensionality. split; intros; [apply H0, H | apply H, H0]; apply H1.
Qed.

Lemma power_set_has_empty_set: forall x, empty_set :i power_set x.
Proof.
  intros. apply power_set_exists. apply empty_subset.
Qed.

Lemma power_set_x_has_x: forall x, x :i power_set x.
Proof.
  intros. apply power_set_exists. apply subset_refl.
Qed.


Definition singleton x := pair x x.
Definition succ x := union (pair x (singleton x)).

Lemma singleton_iff: forall x u, u :i singleton x <-> u = x.
Proof.
  intros. split; intros.
  - apply pair_exists in H. destruct H; apply H.
  - apply pair_exists. left. apply H.
Qed.

Lemma succ_iff: forall x u, u :i succ x <-> u = x \/ u :i x.
Proof.
  split; intros.
  - apply union_exists in H. destruct H as [y [Hy Hy2]].
    apply pair_exists in Hy. destruct Hy.
    + right. rewrite H in Hy2. apply Hy2.
    + rewrite H in Hy2. apply singleton_iff in Hy2.
      left. apply Hy2.
  - apply union_exists. destruct H.
    + exists (singleton x).
      split.
      * apply pair_exists. right. reflexivity.
      * apply singleton_iff. apply H.
    + exists x. split.
      * apply pair_exists. left. reflexivity.
      * apply H.
Qed.


Definition induction_set x :=
  empty_set :i x /\ (forall u, u :i x -> succ u :i x).
Axiom Infinity: exists x, induction_set x.


Axiom Foundation: forall x, nonempty x ->
  (exists y, y :i x /\ join x y = empty_set).

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
  assert (x :i join (singleton x) x).
  { apply join_iff. split.
    - apply H0.
    - apply H. }
  assert (nonempty (join (singleton x) x)).
  exists x. apply H1.
  apply nonempty_correct in H2. contradiction.
Qed.


Definition is_rep (fn: set->set) x y := forall u,
  u :i y <-> (exists z, z :i x /\ fn z = u).
Axiom Rep: forall (fn: set->set) x, exists y, is_rep fn x y.
Definition rep (fn: set->set) x := descr (is_rep fn x).

Lemma rep_exists: forall (fn: set->set) x, is_rep fn x (rep fn x).
Proof.
  intros. unfold rep. apply Descr.
  destruct (Rep fn x).
  exists x0.
  split; intros.
  - apply H.
  - apply extensionality. split; intros; [apply H0, H | apply H, H0]; apply H1.
Qed.


Definition disjoint x y := join x y = empty_set.
Definition mutual_disjoint X := forall x y, x :i X -> y :i X -> x=y \/ disjoint x y.

Definition is_choice_set X S := forall x,
  x :i X -> exists! y, join S X = singleton y.
Axiom Choice: forall X, nonempty X /\ mutual_disjoint X ->
  exists S, is_choice_set X S.


Definition ordered_pair x y := pair (singleton x) (pair x y).
Notation "x ,, y" := (ordered_pair x y) (at level 54).

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
  intros. apply pair_exists. left. reflexivity.
Qed.

Lemma pair_in_r: forall x y, y :i pair x y.
Proof.
  intros. apply pair_exists. right. reflexivity.
Qed.

Lemma pair_eq_iff: forall x1 x2 y1 y2,
  pair x1 y1 = pair x2 y2 <->
    x1 = x2 /\ y1 = y2 \/
    x1 = y2 /\ y1 = x2.
Proof.
  split; intros.
  - assert (x1 :i pair x1 y1).
    apply pair_in_l.
    rewrite H in H0. apply pair_exists in H0.
    assert (y1 :i pair x1 y1).
    apply pair_in_r.
    rewrite H in H1. apply pair_exists in H1.
    assert (x2 :i pair x2 y2).
    apply pair_in_l.
    rewrite <- H in H2. apply pair_exists in H2.
    assert (y2 :i pair x2 y2).
    apply pair_in_r.
    rewrite <- H in H3. apply pair_exists in H3.
    destruct H0, H1, H2, H3; auto.
  - destruct H as [[H1 H2] | [H1 H2]]; rewrite H1, H2; auto.
    apply pair_comm.
Qed.

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

Definition cartesian_prod X Y := union (rep (fun x => rep (fun y => x,, y) Y) X).
Notation "x ** y" := (cartesian_prod x y) (at level 58).

Definition relation X Y r := r :s X ** Y.

Implicit Types P Q R: set->set->Prop.

Definition cast_rel r x y := x,,y :i r.
Definition uncast_rel R := descr (fun r => forall u, u :i r <->
  exists x y, R x y /\ u = x,,y).

Definition function R := (forall x y z, R x y -> R x z -> y = z).

Implicit Types f: set->set.

Definition cast_fun R x := descr (fun y => R x y).
Definition uncast_fun X f x y := x :i X /\ f x = y.

Definition reflexive X R := forall x, x :i X -> R x x.
Definition irreflexive X R := forall x, x :i X -> ~R x x.
Definition symmetric R := forall x y, R x y -> R y x.
Definition asymmetric R := forall x y, R x y -> ~R y x.
Definition antisymmetric R := forall x y, R x y -> R y x -> x = y.
Definition transitive R := forall x y z, R x y -> R y z -> R x z.
Definition antitransitive R := forall x y z, R x y -> R y z -> ~R x z.
Definition trichotomous R := forall x y, R x y \/ R y x \/ x=y.

Definition partial_order X R := reflexive X R /\ antisymmetric R.
Definition strict_partial_order X R := irreflexive X R /\ antitransitive R.
Definition total_order X R := partial_order X R /\ trichotomous R.
Definition strict_total_order X R := strict_partial_order X R /\ trichotomous R.

Definition equivalence_relation X R := reflexive X R /\ symmetric R /\ transitive R.
Definition partition X p := mutual_disjoint p /\ union p = X.

Definition dom r := rep (fun op => descr (fun x => exists y, x,, y = op)) r.
Definition ran r := rep (fun op => descr (fun y => exists x, x,, y = op)) r.
Definition restrict_dom r X := sep (fun op => exists x y, x,, y = op /\ x :i X) r.
Definition restrict_ran r Y := sep (fun op => exists x y, x,, y = op /\ y :i Y) r.
Definition image_set r X := ran (restrict_dom r X).
Definition inv_image_set r Y := dom (restrict_ran r Y).

Definition compose P Q x z := exists y, P x y /\ Q y z.
Definition inverse R y x := R x y.


Definition partition_to_equiv p := union (rep (fun x => cartesian_prod x x) p).
Definition equiv_to_partition r := rep (fun x => image_set r (singleton x)) (dom r).

Definition minimal_elem X R a := a :i X /\ forall x, x :i X -> x=a \/ R a x.
Definition maximal_elem X R a := a :i X /\ forall x, x :i X -> x=a \/ R x a.
Definition lower_bound X R S a := a :i X /\ S :s X /\ forall x, x :i S -> R a x.
Definition upper_bound X R S a := a :i X /\ S :s X /\ forall x, x :i S -> R x a.
Definition inf X R S a := lower_bound X R S a /\ forall b, lower_bound X R S b -> R b a.
Definition sup X R S a := upper_bound X R S a /\ forall b, upper_bound X R S b -> R a b.

Definition minimal_elem_prop X R := forall S, S :s X -> exists a, minimal_elem S R a.
Definition well_order X R := total_order X R /\ minimal_elem_prop X R.
Definition strict_well_order X R := strict_total_order X R /\ minimal_elem_prop X R.

Definition injective R := forall x y z, R x z -> R y z -> x = y.
Definition surjective r Y := ran r = Y.
Definition bijective r X Y := dom r = X /\ injective (cast_rel r) /\ surjective r Y.
Definition homomorphism F X1 X2 (R1 R2: set->set->Prop) :=
  let f := cast_fun (cast_rel F) in bijective F X1 X2 /\
    forall x y, x :i X1 -> y :i X1 -> (R1 x y <-> R2 (f x) (f y)).

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

Definition n0 := empty_set.
Definition n1 := succ n0.
Definition n2 := succ n1.

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

Definition initial_segment X R I := total_order X R /\ I :s X /\
  forall x y, x :i I -> y :i X -> R y x -> y :i I.
Definition strict_initial_segment X R I := strict_total_order X R /\ I :s X /\
  forall x y, x :i I -> y :i X -> R y x -> y :i I.

Definition proper_initial_segment X R I := initial_segment X R I /\ I :ps X.
Definition strict_proper_initial_segment X R I
  := strict_initial_segment X R I /\ I :ps X.

Definition transitive_set X := forall x, x :i X -> x :s X.
Definition ordinal_number x := transitive_set x /\ strict_well_order x In.

Lemma wo_init_seg_sup: forall W R S, strict_well_order W R ->
  strict_proper_initial_segment W R S ->
  exists a, a :i W /\ S = sep (fun x => R x a) W.

