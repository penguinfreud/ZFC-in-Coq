Require Import zfc.
Require Import classical.

Implicit Types R P Q p q r S u v w x y z X Y Z: set.

Definition ordered_pair X Y Z := forall u v,
  singleton_set X u -> pair_set X Y v -> pair_set u v Z.

Theorem ordered_pair_uniquely_exists: forall X Y, exists! Z, ordered_pair X Y Z.
Proof.
  intros X Y.
  destruct (singleton_set_uniquely_exists X) as [u Hu].
  destruct (pair_set_uniquely_exists X Y) as [v Hv].
  destruct (pair_set_uniquely_exists u v) as [Z HZ].
  exists Z. unfold ordered_pair, unique.
  split.
  - intros.
    assert (u = u0). { apply (proj2 Hu). apply H. }
    assert (v = v0). { apply (proj2 Hv). apply  H0. }
    rewrite <- H1, <- H2. apply (proj1 HZ).
  - intros.
    apply (proj2 HZ). apply H.
    + apply (proj1 Hu).
    + apply (proj1 Hv).
Qed.

Lemma pair_set_eq: forall X Y x y Z,
  pair_set X Y Z -> pair_set x y Z ->
    (X = x /\ Y = y) \/ (X = y /\ Y = x).
Proof.
  intros X Y x y Z H1 H2.
  unfold pair_set in H1, H2.
  assert (X \in Z) as HX. { rewrite H1. left. reflexivity. }
  assert (Y \in Z) as HY. { rewrite H1. right. reflexivity. }
  assert (x \in Z) as Hx. { rewrite H2. left. reflexivity. }
  assert (y \in Z) as Hy. { rewrite H2. right. reflexivity. }
  rewrite H2 in HX, HY. rewrite H1 in Hx, Hy.
  destruct HX, HY, Hx, Hy; auto.
Qed.

Lemma singleton_set_eq: forall X x Y,
  singleton_set X Y -> singleton_set x Y -> X = x.
Proof.
  intros X x Y H1 H2.
  unfold singleton_set in H1, H2.
  apply (pair_set_eq X X x x Y) in H1.
  - destruct H1 as [H | H]; apply (proj1 H).
  - apply H2.
Qed.

Theorem ordered_pair_injective: forall X Y x y Z,
  ordered_pair X Y Z -> ordered_pair x y Z -> X = x /\ Y = y.
Proof.
  intros X Y x y Z H1 H2.
  unfold ordered_pair in H1, H2.
  destruct (singleton_set_uniquely_exists X) as [u [Hu _]].
  destruct (singleton_set_uniquely_exists x) as [u' [Hu' _]].
  destruct (pair_set_exists X Y) as [v Hv].
  destruct (pair_set_exists x y) as [v' Hv'].
  assert (pair_set u v Z). apply H1. apply Hu. apply Hv.
  apply (pair_set_eq u v u' v') in H.
  - destruct H.
    + apply (pair_set_eq X Y x y v) in Hv.
      * destruct Hv as [[Hv1 Hv2] | [Hv1 Hv2]].
        { rewrite Hv1, Hv2. auto. }
        { apply (singleton_set_eq X x u) in Hu.
          { split. apply Hu. rewrite Hv2, <- Hu, Hv1. reflexivity. }
          rewrite (proj1 H). apply Hu'. }
      * rewrite (proj2 H). apply Hv'.
    + unfold singleton_set in Hu.
      apply (pair_set_eq X X x y u) in Hu.
      { destruct Hu. split. apply (proj1 H0).
        apply (pair_set_eq x x X Y u') in Hu'.
        destruct Hu'. rewrite <- (proj2 H3), (proj1 H3), (proj2 H0). reflexivity.
        rewrite <- (proj2 H0), <- (proj1 H3), (proj2 H3). reflexivity.
        rewrite <- (proj2 H). apply Hv.
        split. apply H0. apply (pair_set_eq x x X Y u') in Hu'.
        destruct Hu'. rewrite <- (proj1 H0), (proj2 H0), (proj2 H3). reflexivity.
        rewrite <- (proj1 H0), (proj2 H0), (proj1 H3). reflexivity.
        rewrite <- (proj2 H). apply Hv. }
      rewrite (proj1 H). apply Hv'.
  - apply (H2 u' v' Hu' Hv').
Qed.

Definition cartesian_product X Y Z := forall w,
  image_set (fun x u => image_set
                (fun y v => ordered_pair x y v) Y u) X w ->
    union_set w Z.

Lemma cartesian_product_exists1: forall X Y x,
  x \in X -> (exists u, image_set (fun y v => ordered_pair x y v) Y u).
  intros. apply replacement. unfold is_function. intros.
    apply ordered_pair_uniquely_exists.
Qed.

Lemma cartesian_product_exists2: forall X Y,
  exists! w, image_set (fun x u => image_set (fun y v => ordered_pair x y v) Y u) X w.
  intros X Y. apply image_set_uniquely_exists.
  unfold is_function. intros. apply image_set_uniquely_exists.
  unfold is_function. intros. apply ordered_pair_uniquely_exists.
Qed.


Theorem cartesian_product_exists: forall X Y, exists Z, cartesian_product X Y Z.
Proof.
  intros X Y. unfold cartesian_product.
  destruct (cartesian_product_exists2 X Y) as [w Hw].
  destruct (union_set_exists w) as [Z HZ]. exists Z.
  intros.
  assert (w = w0).
  { apply unique_existence_to_eq with (fun w => image_set
       (fun x u : set => image_set (fun y v : set => ordered_pair x y v) Y u) X
       w).
       exists w. apply Hw.
       split. apply Hw. apply H. }
  rewrite <- H0. apply HZ.
Qed.

Definition is_ordered_pair u := exists x y, ordered_pair x y u.
Definition is_cartesian_product Z := exists X Y, cartesian_product X Y Z.

Lemma image_set_f_property: forall (f: set->set->Prop) (g: set->Prop) X Y,
  (forall x y, f x y -> g y) -> image_set f X Y -> set_forall g Y.
Proof.
  unfold image_set, set_forall. intros.
  apply H0 in H1. destruct H1 as [v [Hvx Hfvu]].
  apply H in Hfvu. apply Hfvu.
Qed.

Theorem cartesian_product_consists_of_ordered_pairs:
  forall Z, is_cartesian_product Z -> set_forall is_ordered_pair Z.
Proof.
  unfold is_cartesian_product. intros Z [X [Y H]].
  unfold cartesian_product in H.
  destruct (cartesian_product_exists2 X Y) as [w Hw].
  destruct Hw as [Hw Hw1].
  apply H in Hw as HZ.
  apply (union_set_property is_ordered_pair w).
  - intros. set (f := fun x u => image_set (fun y v => ordered_pair x y v) Y u).
    set (g := set_forall is_ordered_pair).
    assert (forall x y, f x y -> g y).
    { intros. unfold g.
      apply (image_set_f_property (fun y v => ordered_pair x0 y v) is_ordered_pair Y).
      - intros. unfold is_ordered_pair. exists x0. exists x1. apply H2.
      - unfold f in H1. apply H1. }
    apply (image_set_f_property f g X w).
    + apply H1.
    + apply Hw.
    + apply H0.
  - apply HZ.
Qed.

Definition car u x := exists y, ordered_pair x y u.
Definition cdr u y := exists x, ordered_pair x y u.
Definition caar u x := forall v, car u v -> car v x.
Definition cadr u x := forall v, car u v -> cdr v x.
Definition cdar u x := forall v, cdr u v -> car v x.
Definition cddr u x := forall v, cdr u v -> cdr v x.

Theorem ordered_pair_iff_car_cdr: forall x y z, ordered_pair x y z <-> car z x /\ cdr z y.
Proof.
  intros. unfold car. unfold cdr. split.
  - intros. split.
    + exists y. apply H.
    + exists x. apply H.
  - intros [[y0 Hy0] [x0 Hx0]].
    apply (ordered_pair_injective x y0 x0 y) in Hy0.
    + destruct Hy0. rewrite H. apply Hx0.
    + apply Hx0.
Qed.

Theorem car_unique: forall u, uniqueness (fun x => car u x).
Proof.
  unfold uniqueness. unfold car. intros u x1 x2 [y1 H1] [y2 H2].
  apply (ordered_pair_injective x1 y1 x2 y2) in H1.
  - apply H1.
  - apply H2.
Qed.

Theorem cdr_unique: forall u, uniqueness (fun x => cdr u x).
Proof.
  unfold uniqueness. unfold cdr. intros u y1 y2 [x1 H1] [x2 H2].
  apply (ordered_pair_injective x1 y1 x2 y2) in H1.
  - apply H1.
  - apply H2.
Qed.

Theorem ordered_pairs_make_relation:
  forall X Y z, set_forall
      (fun u => is_ordered_pair u /\
          (forall x, car u x -> x \in X) /\
          (forall y, cdr u y -> y \in Y)) z ->
      (forall Z, cartesian_product X Y Z -> z \subset Z).
Proof.
  unfold subset. intros.
  unfold cartesian_product, union_set in H0.
  destruct (cartesian_product_exists2 X Y) as [w Hw].
  destruct Hw as [Hw Hw1].
  apply (H0 w Hw).
  apply H in H1. destruct H1 as [[x [y Hxy]] [Hx Hy]].
  apply ordered_pair_iff_car_cdr in Hxy as Hcarcdr.
  destruct Hcarcdr as [Hcar Hcdr].
  apply Hx in Hcar. apply Hy in Hcdr.
  destruct (cartesian_product_exists1 X Y x Hcar).
  exists x0.
  split.
  - unfold image_set in Hw.
    apply Hw. exists x. split.
    + apply Hcar.
    + intros. split.
      * intros. apply H1 in H2. apply H2.
      * intro. apply H1. apply H2.
  - apply H1. exists y. split.
    + apply Hcdr.
    + apply Hxy.
Qed.

Definition relation X Y R := forall Z, cartesian_product X Y Z -> R \subset Z.

Definition id_rel X R := (forall u, u \in R -> (exists x, x \in X /\ ordered_pair x x u)) /\
  (forall x, x \in X -> (exists u, u \in R /\ ordered_pair x x u)).

Theorem id_is_rel: forall X R, id_rel X R -> relation X X R.
Proof.
  unfold id_rel, relation. intros.
  apply ordered_pairs_make_relation with X X.
  - unfold set_forall. intros.
    destruct H. apply H in H1. destruct H1 as[x [Hx Hxxu]].
    split.
    + exists x, x. apply Hxxu.
    + split.
      * intros. unfold car in H1.
        destruct H1. apply (ordered_pair_injective x0 x1 x x) in H1.
        { rewrite (proj1 H1). apply Hx. }
        { apply Hxxu. }
      * intros. unfold cdr in H1.
        destruct H1. apply (ordered_pair_injective x0 y x x) in H1.
        { rewrite (proj2 H1). apply Hx. }
        { apply Hxxu. }
  - apply H0.
Qed.

Theorem subset_is_relation: forall X Y R,
  relation X Y R -> (forall S, S \subset R -> relation X Y S).
Proof.
  unfold relation. intros.
  apply (subset_trans S R Z).
  - apply H0.
  - apply H. apply H1.
Qed.

Theorem cartesian_product_mono_l: forall x Y z,
  cartesian_product x Y z ->
    (forall X Z, x \subset X ->
      cartesian_product X Y Z -> z \subset Z).
Proof.
  intros.
  destruct (cartesian_product_exists2 x Y) as [w Hw].
  destruct (cartesian_product_exists2 X Y) as [W HW].
  apply union_set_mono with w W.
  - apply H. apply Hw.
  - unfold subset. intros.
    apply (proj1 HW).
    apply (proj1 Hw) in H2.
    destruct H2. exists x0.
    split.
    + apply H0. apply H2.
    + apply H2.
  - apply H1. apply HW.
Qed.

Theorem dom_superset_rel_l: forall x Y R, relation x Y R ->
  (forall X, x \subset X -> relation X Y R).
Proof.
  unfold relation. intros.
  destruct (cartesian_product_exists x Y) as [z Hz].
  apply H in Hz as H2.
  apply (subset_trans R z Z).
  - apply H2.
  - apply (cartesian_product_mono_l x Y z Hz X Z).
    + apply H0.
    + apply H1.
Qed.

Definition restriction_rel X Y R x S := relation X Y R /\
  (forall z, cartesian_product x Y z -> join_set z R S).

Definition restriction_rel_is_rel: forall X Y R x S,
  restriction_rel X Y R x S -> relation x Y S.
Proof.
  unfold relation, restriction_rel. intros X Y R x S [HR H] z Hz.
  destruct (cartesian_product_exists x Y) as [Z HZ].
  apply H in Hz as Hj.
  apply join_set_subset in Hj.
  apply Hj.
Qed.

Definition dom_rel X Y R u := relation X Y R /\
  image_set car R u.

Definition ran_rel X Y R u := relation X Y R /\
  image_set cdr R u.

Theorem id_dom: forall X R, id_rel X R -> dom_rel X X R X /\ ran_rel X X R X.
Proof.
  unfold id_rel, dom_rel, ran_rel. intros.
  split; split.
  - apply id_is_rel. apply H.
  - unfold image_set. intros. split.
    + intros. apply H in H0.
      destruct H0. exists x.
      split.
      * apply H0.
      * unfold car. exists u. apply H0.
    + intros. destruct H0 as [v [Hv Hcar]].
      apply H in Hv. destruct Hv as [x [Hx Hxxv]].
      unfold car in Hcar. destruct Hcar.
      apply (ordered_pair_injective x x u x0) in H0.
      * rewrite <- (proj1 H0). apply Hx.
      * apply Hxxv.
  - apply id_is_rel. apply H.
  - unfold image_set, cdr. intros.
    split.
    + intros. apply H in H0. destruct H0.
      exists x. split.
      * apply H0.
      * destruct H0. exists u. apply H1.
    + intros. destruct H0 as [v [Hv [x Hxuv]]].
      apply H in Hv. destruct Hv as [x' [Hx' Hxxv']].
      apply (ordered_pair_injective x' x' x u) in Hxxv'.
      * rewrite <- (proj2 Hxxv'). apply Hx'.
      * apply Hxuv.
Qed.

Definition image_rel X Y R x u := relation X Y R /\
  (forall S, restriction_rel X Y R x S -> ran_rel X Y S u).

Definition ordered_pair_inverse u v := forall x y, ordered_pair x y u <-> ordered_pair y x v.

Definition inv_rel X Y R S := relation X Y R /\ relation Y X S /\
  (forall u v, ordered_pair_inverse u v -> (u \in R <-> v \in S)).

Definition composition_rel X Y Z P Q R :=
  relation X Y P /\ relation Y Z Q /\ relation X Z R /\
  (forall u x z, u \in R -> car u x -> cdr u z ->
    (exists y, (forall p, ordered_pair x y p -> p \in P) /\
               (forall q, ordered_pair y z q -> q \in Q))) /\
  (forall x y z p q r, ordered_pair x y p -> ordered_pair y z q ->
      p \in P -> q \in Q -> ordered_pair x z r -> r \in R).