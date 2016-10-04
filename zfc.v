Variable set: Type.
Axiom In: set->set->Prop.
Axiom Exi: exists x: set, True.
Axiom Ext: forall X Y: set, (forall u: set, In u X <-> In u Y) -> X=Y.
Definition sep_set (phi: set->Prop) (X Y: set) := forall u: set, In u Y <-> In u X /\ phi u.
Axiom Sep: forall phi: set->Prop, forall X: set, exists Y: set, sep_set phi X Y.
Definition Empty_set (X: set) : Prop := exists x: set, sep_set (fun _: set => False) x X.
Definition Subset (A B: set) : Prop := forall x: set, In x A -> In x B.
Definition pai_set (A B C: set) := forall x:set, In x C <-> (x=A \/ x=B).
Axiom Pai: forall A B:set, exists C:set, pai_set A B C.
Definition uni_set (X Y: set) := forall u:set, In u Y <-> (exists Z:set, In Z X /\ In u Z).
Axiom Uni: forall X:set, exists Y:set, uni_set X Y.
Definition pow_set (X Y: set) := forall u:set, In u Y <-> Subset u X.
Axiom Pow: forall X:set, exists Y:set, pow_set X Y.
Definition succ (x y:set) := forall u: set, In u y <-> (u=x \/ In u x).
Definition inductive_set (X: set) := (exists e: set, Empty_set e /\ In e X) /\
                        (forall x:set, In x X -> (exists y: set, succ x y /\ In y X)).
Axiom Inf: exists X: set, inductive_set X.
Definition join (x y z: set) := forall u: set, In u z <-> In u x /\ In u y.
Axiom Fnd: forall x:set, Empty_set x \/
           (exists y:set, In y x /\
                    (forall j: set, join x y j -> Empty_set j)).
Definition is_function (phi: set->set->Prop) (dom: set) := forall a: set, In a dom ->
              ((exists b: set, phi a b) /\
              (forall b c: set, phi a b /\ phi a c -> b=c)).
Definition rep_set (phi: set->set->Prop) (X Y: set) := forall x: set, In x X -> (exists y: set, In y Y /\ phi x y).
Axiom Rep: forall phi: set->set->Prop, forall X: set, is_function phi X -> (exists Y:set, rep_set phi X Y).
Definition unit_set (X Y: set) := forall u: set, In u Y <-> u=X.
Definition AC_set (X S: set) := forall x: set, In x X ->
          (exists y: set, exists j: set, join S x j /\ unit_set y j).
Axiom AC: forall X: set, ~Empty_set X /\
                        (exists e: set, Empty_set e /\ ~ In e X) /\
                        (forall x y: set, In x X /\ In y X ->
                                  (exists j: set, join x y j /\ Empty_set j))
                    -> (exists S: set, AC_set X S).