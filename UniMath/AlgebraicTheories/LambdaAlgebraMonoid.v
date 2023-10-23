(**************************************************************************************************

  The lambda algebra monoid

  For any algebra for a λ-theory, its functional elements form a monoid. This file defines this
  monoid. The functional elements are the elements f that are equal to λ x, f x.

  Contents
  1. The definition of the functional monoid [algebra_monoid]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.Examples.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.

Local Open Scope cat.
Local Open Scope vec.

(** * 1. The definition of the functional monoid [algebra_monoid] *)

Section Monoid.
  Variable lambda : lambda_calculus.
  Context (L := (lambda_calculus_lambda_theory lambda)).
  Variable A : algebra L.

  Lemma move_action_through_vector {n m : nat} (f : vec (L m : hSet) n) (a : stn m → A):
    weqvecfun _ (vec_map (λ fi, action fi a) f)
     = (λ i, action (weqvecfun _ f i) a).
  Proof.
    apply funextfun.
    intro.
    simpl.
    now rewrite el_vec_map.
  Qed.

  Lemma move_action_through_vector_1 {n : nat} (f : (L n : hSet)) (a : stn n → A) :
        weqvecfun 1 [(action f a)]
      = (λ i, action (weqvecfun 1 [(f)] i) a).
  Proof.
    exact (move_action_through_vector [(f)] _).
  Qed.

  Lemma move_action_through_vector_2 {n : nat} (f g : (L n : hSet)) (a : stn n → A) :
        weqvecfun _ [(action f a ; action g a )]
      = (λ i, action (weqvecfun _ [(f ; g)] i) a).
  Proof.
    exact (move_action_through_vector [(f ; g)] _).
  Qed.

  Ltac extend_tuple_1 := (
    rewrite (extend_tuple_last _ _ _ (idpath 0 : stntonat _ (make_stn 1 0 (idpath true)) = 0))
  ).

  Ltac extend_tuple_2 := (
    rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 2 0 (idpath true) < 1)) +
    rewrite (extend_tuple_last _ _ _ (idpath 1 : stntonat _ (make_stn 2 1 (idpath true)) = 1))
  ).

  Ltac extend_tuple_3 := (
    rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 3 0 (idpath true) < 2)) +
    rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 3 1 (idpath true) < 2)) +
    rewrite (extend_tuple_last _ _ _ (idpath 2 : stntonat _ (make_stn 3 2 (idpath true)) = 2))
  ).

  Definition compose
    (a b : A)
    : A
    := action (abs (app (var (make_stn 3 0 (idpath true))) (app (var (make_stn 3 1 (idpath true))) (var (make_stn 3 2 (idpath true))))) : (L 2 : hSet)) (weqvecfun _ [(a ; b)]).

  Lemma compose_assoc
    (a b c : A)
    : compose (compose a b) c = compose a (compose b c).
  Proof.
    unfold compose.
    pose (v := weqvecfun _ [(a ; b ; c)]).
    pose (Hv := λ i Hi,
      !(algebra_projects_component _ _ (make_stn 3 i Hi) v)).
    rewrite (Hv 0 (idpath true) : a = _).
    rewrite (Hv 1 (idpath true) : b = _).
    rewrite (Hv 2 (idpath true) : c = _).
    do 2 rewrite move_action_through_vector_2.
    do 2 rewrite <- algebra_is_assoc.
    cbn -[weqvecfun action].
    do 15 reduce_lambda.
    do 6 extend_tuple_3.
    do 2 rewrite move_action_through_vector_2.
    do 2 rewrite <- algebra_is_assoc.
    apply (maponpaths (λ x, action x v)).
    cbn -[weqvecfun v].
    do 12 reduce_lambda.
    do 6 extend_tuple_3.
    cbn -[v].
    now do 42 reduce_lambda.
  Qed.

  Definition one_1
    : A
    :=
    action (abs (var (make_stn 1 0 (idpath true))) : (L 0 : hSet)) (weqvecfun _ vnil).

  Lemma one_1_idempotent
    : compose one_1 one_1 = one_1.
  Proof.
    unfold compose, one_1.
    rewrite move_action_through_vector_2.
    rewrite <- algebra_is_assoc.
    apply (maponpaths (λ x, action x _)).
    cbn -[weqvecfun].
    do 6 reduce_lambda.
    do 3 extend_tuple_3.
    cbn.
    do 4 reduce_lambda.
    cbn.
    now do 4 reduce_lambda.
  Qed.

  Definition make_functional_1 (a : A)
    : A
    := compose one_1 a.

  Definition is_functional_1 (a: A)
    : UU
    := a = make_functional_1 a.

  Lemma isaprop_is_functional_1 (a : A) : isaprop (is_functional_1 a).
  Proof.
    apply setproperty.
  Qed.

  Definition one_2
    : A
    :=
    action (abs (abs (app (var (make_stn 2 0 (idpath true))) (var (make_stn 2 1 (idpath true))))) : (L 0 : hSet)) (weqvecfun _ vnil).

  Lemma one_2_idempotent
    : compose one_2 one_2 = one_2.
  Proof.
    unfold compose, one_2.
    rewrite move_action_through_vector_2.
    rewrite <- algebra_is_assoc.
    apply (maponpaths (λ x, action x _)).
    cbn -[weqvecfun].
    do 6 reduce_lambda.
    apply maponpaths.
    do 3 extend_tuple_3.
    cbn.
    do 7 reduce_lambda.
    apply maponpaths.
    do 4 reduce_lambda.
    do 2 extend_tuple_2.
    cbn.
    now do 28 reduce_lambda.
  Qed.

  Definition make_functional_2 (a : A)
    : A
    := compose one_2 a.

  Definition is_functional_2 (a: A)
    : UU
    := a = make_functional_2 a.

  Lemma isaprop_is_functional_2 (a : A) : isaprop (is_functional_2 a).
  Proof.
    apply setproperty.
  Qed.

  Lemma pr_is_var
    {n : nat}
    (i : stn n)
    : pr (T := L) i = var i.
  Proof.
    exact (subst_var _ _).
  Qed.

  Section Monoid.

    Lemma algebra_isaset_functionals
      (n : nat)
      : isaset (∑ (a: A), is_functional_1 a).
    Proof.
      apply isaset_total2.
      - apply setproperty.
      - intro a.
        apply isasetaprop.
        apply isaprop_is_functional_1.
    Qed.

    Definition algebra_functionals_set
      (n : nat)
      : hSet
      := make_hSet _ (algebra_isaset_functionals n).

    Lemma is_functional_1_compose
      (a b : algebra_functionals_set 1)
      : is_functional_1 (compose (pr1 a) (pr1 b)).
    Proof.
      unfold is_functional_1, make_functional_1.
      refine (!_ @ compose_assoc _ _ _).
      apply (maponpaths (λ x, compose x _)).
      exact (!pr2 a).
    Qed.

    Definition unit_element
      : A.
    Proof.
      exact (action (T := L) (abs (var (make_stn 1 0 (idpath true)))) (weqvecfun _ [()])).
    Defined.

    Lemma is_functional_1_unit_element
      : is_functional_1 unit_element.
    Proof.
      unfold unit_element, is_functional_1, make_functional_1, one_1, compose.
      rewrite move_action_through_vector_2.
      rewrite <- algebra_is_assoc.
      apply (maponpaths (λ x, action x _)).
      cbn -[weqvecfun action].
      do 6 reduce_lambda.
      do 3 extend_tuple_3.
      cbn.
      do 6 reduce_lambda.
      cbn.
      now do 4 reduce_lambda.
    Qed.

    Lemma is_unit_unit_element
      : isunit
        (λ a b, compose (pr1 a) (pr1 b) ,, is_functional_1_compose a b)
        (unit_element ,, is_functional_1_unit_element).
    Proof.
      split.
      - intro a.
        use subtypePairEquality.
        {
          intro.
          apply isaprop_is_functional_1.
        }
        exact (!pr2 a).
    - intro a.
      use subtypePairEquality.
      {
        intro.
        apply isaprop_is_functional_1.
      }
      refine (_ @ !pr2 a).
      refine (!_ @ maponpaths _ (algebra_projects_component _ _ (make_stn 1 0 (idpath true)) (weqvecfun 1 [(pr1 a)]))).
      refine (!_ @ maponpaths (λ x, _ x _) (algebra_projects_component _ _ (make_stn 1 0 (idpath true)) (weqvecfun 1 [(pr1 a)]))).
      rewrite pr_is_var.
      unfold make_functional_1, compose, one_1.
      refine (maponpaths (λ x, _ (_ [(_ ; x)])) (!lift_constant_action (A := A) 1 _ (weqvecfun 1 [(pr1 a)])) @ !_).
      refine (maponpaths (λ x, _ (_ [(x ; _)])) (!lift_constant_action (A := A) 1 _ (weqvecfun 1 [(pr1 a)])) @ !_).
      do 2 rewrite move_action_through_vector_2.
      do 2 rewrite <- algebra_is_assoc.
      apply (maponpaths (λ x, action (A := A) x _)).
      do 2 refine (subst_abs _ _ @ !_).
      apply maponpaths.
      do 4 rewrite subst_app.
      do 6 rewrite subst_var.
      do 2 refine (
        maponpaths (λ x, app x _) (extend_tuple_i _ _ _ _ (idpath true : make_stn 3 0 (idpath true) < 2)) @
        maponpaths (λ x, app _ (app x _)) (extend_tuple_i _ _ _ _ (idpath true : make_stn 3 1 (idpath true) < 2)) @
        maponpaths (λ x, app _ (app _ x)) (extend_tuple_last _ _ _ (idpath 2 : stntonat _ (make_stn 3 2 (idpath true)) = 2)) @ !_).
      cbn.
      do 8 reduce_lambda.
      extend_tuple_1.
      now do 7 reduce_lambda.
    Qed.

    Definition algebra_monoid : monoid.
    Proof.
      use tpair.
      - use tpair.
        + exact (algebra_functionals_set 1).
        + intros a b.
          exact (compose (pr1 a) (pr1 b) ,, is_functional_1_compose a b).
      - split.
        + abstract (
            intros a b c;
            apply subtypePairEquality; [intro; apply isaprop_is_functional_1 | ];
            apply compose_assoc
          ).
        + exact (_ ,, is_unit_unit_element).
    Defined.

  End Monoid.

End Monoid.
