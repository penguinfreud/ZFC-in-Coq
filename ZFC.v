Parameter set: Type.
Parameter In: set->set->Prop.
Parameter element: set.

Parameter descr: (set->Prop)->set.
Axiom Descr: forall (prop:set->Prop), (exists! x, prop x) -> prop (descr prop).

Notation "x ':i' y" := (In x y) (at level 60).

Axiom extensionality: forall x y, (forall u, u :i x <-> u :i y) -> x = y.

Definition is_sep (test:set->Prop) x y := forall u, u :i y <-> u :i x /\ test u.
Axiom Sep: forall (test: set->Prop) x, exists y, is_sep test x y.
Definition sep (test:set->Prop) x := descr (is_sep test x).

Definition is_pair x y z := forall u, u :i z <-> u=x \/ u=y.
Axiom Pair: forall x y, exists z, is_pair x y z.
Definition pair x y := descr (is_pair x y).

Definition is_union x y := forall u, u :i y <-> (exists z, z :i x /\ u :i z).
Axiom Union: forall x, exists y, is_union x y.
Definition union x := descr (is_union x).

Definition subset x y := forall u, u :i x -> u :i y.
Notation "x ':s' y" := (subset x y) (at level 62).

Definition is_power_set x y := forall u, u :i y <-> u :s x.
Axiom Power_set: forall x, exists y, is_power_set x y.
Definition power_set x := descr (is_power_set x).

Definition singleton x := pair x x.
Definition succ x := union (pair x (singleton x)).
Definition empty_set := sep (fun x => False) element.

Definition induction_set x := empty_set :i x /\ (forall u, u :i x -> succ u :i x).
Axiom Infinity: exists x, induction_set x.

Definition nonempty x := exists u, u :i x.
Definition join x y := sep (fun u => u :i y) x.

Axiom Foundation: forall x, nonempty x ->
  (exists y, y :i x /\ join x y = empty_set).

Definition is_rep (fn: set->set) x y := forall u,
  u :i y <-> (exists z, z :i x /\ fn z = u).
Axiom Rep: forall (fn: set->set) x, exists y, is_rep fn x y.
Definition rep (fn: set->set) x := descr (is_rep fn x).

Definition disjoint x y := join x y = empty_set.
Definition mutual_disjoint X := forall x y, x :i X -> y :i X -> x=y \/ disjoint x y.

Axiom Choice: forall X, nonempty X /\ mutual_disjoint X ->
  exists S, forall x, x :i X -> exists! y, join S X = singleton y.

Definition ordered_pair x y := pair (singleton x) (pair x y).
Notation "x ,, y" := (ordered_pair x y) (at level 56).

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

Definition Nat := descr (fun x => induction_set x /\ forall y, induction_set y -> x :s y).

Definition initial_segment X R I := total_order X R /\ I :s X /\
  forall x y, x :i I -> y :i X -> R y x -> y :i I.
Definition strict_initial_segment X R I := strict_total_order X R /\ I :s X /\
  forall x y, x :i I -> y :i X -> R y x -> y :i I.

Definition transitive_set X := forall x, x :i X -> x :s X.
Definition ordinal_number x := transitive_set x /\ strict_well_order x In.

