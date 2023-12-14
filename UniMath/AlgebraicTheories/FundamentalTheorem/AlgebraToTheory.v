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
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.Examples.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.SpecificUtilities.LambdaTerms.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.SpecificUtilities.Utilities.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.CommonUtilities.MonoidActions.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.

Local Open Scope cat.
Local Open Scope vec.
Local Open Scope algebraic_theories.

(** * 1. The definition of the functional monoid [algebra_monoid] *)

Section Monoid.
  Context (lambda : lambda_calculus).
  Let L := (lambda_calculus_lambda_theory lambda).
  Context (A : algebra L).

  Definition compose
    (a b : A)
    : A
    := action (T := L) compose_λ (weqvecfun _ [(a ; b)]).

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
    do 4 (rewrite move_action_through_vector_2, <- algebra_is_assoc).
    apply (maponpaths (λ x, action x v)).
    do 3 rewrite (pr_is_var lambda).
    apply compose_assoc_λ.
  Qed.

  Lemma compose_compose_eq
    {a b c d : A}
    (H : a = compose c d)
    : compose a b = compose c (compose d b).
  Proof.
    refine (_ @ compose_assoc _ _ _).
    apply (maponpaths (λ x, compose x _)).
    exact H.
  Qed.

  Definition I1
    : A
    := action (T := L) I1_λ (weqvecfun _ vnil).

  Lemma I1_idempotent
    : compose I1 I1 = I1.
  Proof.
    unfold compose, I1.
    rewrite move_action_through_vector_2.
    rewrite <- algebra_is_assoc.
    apply (maponpaths (λ x, action x _)).
    apply compose_I1_abs_0_λ.
  Qed.

  Definition make_functional_1 (a : A)
    : A
    := compose I1 a.

  Definition is_functional_1 (a: A)
    : UU
    := a = make_functional_1 a.

  Lemma isaprop_is_functional_1 (a : A) : isaprop (is_functional_1 a).
  Proof.
    apply setproperty.
  Qed.

  Lemma is_functional_1_action_abs
    {n : nat}
    (f : (L (S n) : hSet))
    (v : stn n → A)
    : is_functional_1 (action (abs f : ((L n) : hSet)) v).
  Proof.
    unfold is_functional_1, make_functional_1, compose, I1.
    rewrite <- (lift_constant_action _ _ v).
    rewrite (move_action_through_vector_2 A).
    rewrite <- algebra_is_assoc.
    apply (maponpaths (λ x, action x _)).
    exact (!compose_I1_abs_λ _).
  Qed.

  Definition functional_1_set
    : hSet.
  Proof.
    use (total2_hSet (X := A)).
    intro a.
    exists (is_functional_1 a).
    abstract exact (isasetaprop (isaprop_is_functional_1 _)).
  Defined.

  Definition functional_1_eq
    (a a' : functional_1_set)
    (H : pr1 a = pr1 a')
    : a = a'.
  Proof.
    apply subtypePairEquality.
    {
      intro.
      apply isaprop_is_functional_1.
    }
    exact H.
  Qed.

  Section Monoid.

    Lemma is_functional_1_compose
      (a b : functional_1_set)
      : is_functional_1 (compose (pr1 a) (pr1 b)).
    Proof.
      exact (compose_compose_eq (pr2 a)).
    Qed.

    Lemma is_functional_1_I1
      : is_functional_1 I1.
    Proof.
      exact (!I1_idempotent).
    Qed.

    Lemma is_runit_I1
      (a : A)
      : compose a (I1) = make_functional_1 a.
    Proof.
      refine (!_ @ maponpaths _ (algebra_projects_component _ _ (make_stn 1 0 (idpath true)) (weqvecfun 1 [(a)]))).
      refine (!_ @ maponpaths (λ x, _ x _) (algebra_projects_component _ _ (make_stn 1 0 (idpath true)) (weqvecfun 1 [(a)]))).
      rewrite (pr_is_var lambda).
      unfold make_functional_1, compose, I1.
      refine (maponpaths (λ x, _ (_ [(_ ; x)])) (!lift_constant_action (A := A) 1 _ (weqvecfun 1 [(a)])) @ !_).
      refine (maponpaths (λ x, _ (_ [(x ; _)])) (!lift_constant_action (A := A) 1 _ (weqvecfun 1 [(a)])) @ !_).
      do 2 rewrite move_action_through_vector_2.
      do 2 rewrite <- algebra_is_assoc.
      apply (maponpaths (λ x, action (A := A) x _)).
      rewrite <- (inflate_is_lift_constant I1_λ : _ = lift_constant (T := L) _ _).
      apply I1_runit_λ.
    Qed.

    Lemma is_unit_I1
      : isunit
        (λ a b, compose (pr1 a) (pr1 b) ,, is_functional_1_compose a b)
        (I1 ,, is_functional_1_I1).
    Proof.
      split;
        intro a;
        apply functional_1_eq;
        refine (_ @ !pr2 a).
      - apply idpath.
      - apply is_runit_I1.
    Qed.

    Definition algebra_monoid : monoid.
    Proof.
      use tpair.
      - use tpair.
        + exact functional_1_set.
        + intros a b.
          exact (compose (pr1 a) (pr1 b) ,, is_functional_1_compose a b).
      - split.
        + abstract (
            intros a b c;
            apply functional_1_eq;
            apply compose_assoc
          ).
        + exact (_ ,, is_unit_I1).
    Defined.

  End Monoid.

  Section Theory.

    Definition I2
      : A
      :=
      action (T := L) I2_λ (weqvecfun _ vnil).

    Lemma I2_idempotent
      : compose I2 I2 = I2.
    Proof.
      unfold compose, I2.
      rewrite move_action_through_vector_2.
      rewrite <- algebra_is_assoc.
      apply (maponpaths (λ x, action x _)).
      apply compose_I2_abs_0_λ.
    Qed.

    Definition make_functional_2 (a : A)
      : A
      := compose I2 a.

    Definition is_functional_2 (a: A)
      : UU
      := a = make_functional_2 a.

    Lemma is_functional_2_action_abs
      {n : nat}
      (f : (L (S (S n)) : hSet))
      (v : stn n → A)
      : is_functional_2 (action (abs (abs f) : ((L n) : hSet)) v).
    Proof.
      unfold is_functional_2, make_functional_2, compose, I2.
      rewrite <- (lift_constant_action _ _ v).
      rewrite (move_action_through_vector_2 A).
      rewrite <- algebra_is_assoc.
      apply (maponpaths (λ x, action x _)).
      exact (!compose_I2_abs_λ _).
    Qed.

    Lemma isaprop_is_functional_2 (a : A) : isaprop (is_functional_2 a).
    Proof.
      apply setproperty.
    Qed.

    Definition functional_2_set
      : hSet.
    Proof.
      use (total2_hSet (X := A)).
      intro a.
      exists (is_functional_2 a).
      abstract exact (isasetaprop (isaprop_is_functional_2 _)).
    Defined.

    Definition functional_2_eq
      (a a' : functional_2_set)
      (H : pr1 a = pr1 a')
      : a = a'.
    Proof.
      apply subtypePairEquality.
      {
        intro.
        apply isaprop_is_functional_2.
      }
      exact H.
    Qed.

    Lemma compose_I1_I2
      : compose I1 I2 = I2.
    Proof.
      unfold compose, I1, I2.
      rewrite move_action_through_vector_2.
      rewrite <- algebra_is_assoc.
      apply (maponpaths (λ x, action x _)).
      apply compose_I1_abs_0_λ.
    Qed.

    Lemma is_functional_2_to_is_functional_1
      (a : A)
      (H : is_functional_2 a)
      : is_functional_1 a.
    Proof.
      rewrite H.
      exact (compose_compose_eq (!compose_I1_I2)).
    Qed.

    Lemma is_functional_2_compose
      (a : functional_2_set)
      (m : A)
      : is_functional_2 (compose (pr1 a) m).
    Proof.
      exact (compose_compose_eq (pr2 a)).
    Qed.

    Definition functional_2_monoid_action_data
      : monoid_action_data algebra_monoid.
    Proof.
      use make_monoid_action_data.
      - exact functional_2_set.
      - intros a m.
        exists (compose (pr1 a) (pr1 m)).
        apply is_functional_2_compose.
    Defined.

    Lemma functional_2_is_monoid_action
      : is_monoid_action _ functional_2_monoid_action_data.
    Proof.
      split.
      - intro x.
        apply functional_2_eq.
        simpl.
        apply (maponpaths pr1
          (runax algebra_monoid (_ ,, is_functional_2_to_is_functional_1 _ (pr2 x)))
        ).
      - intros.
        apply functional_2_eq.
        exact (!compose_assoc _ _ _).
    Qed.

    Definition functional_2_monoid_action
      : monoid_action algebra_monoid
      := make_monoid_action _ _ functional_2_is_monoid_action.

    Definition functional_2_to_monoid_action_morphism_data_term
      (d : functional_2_monoid_action)
      (a b : A)
      : A.
    Proof.
      pose (v := (weqvecfun _ [(pr1 d ; a ; b)])).
      exact (action (T := L) compose_2_λ v).
    Defined.

    Definition functional_2_to_monoid_action_morphism_data
      (d : functional_2_monoid_action)
      : monoid_action_morphism_data algebra_monoid (BinProductObject _ (binproducts_monoid_action_category algebra_monoid (monoid_monoid_action _) (monoid_monoid_action _)) : monoid_action _) (monoid_monoid_action _)
      := λ x, (functional_2_to_monoid_action_morphism_data_term d (pr11 x) (pr12 x) ,, is_functional_1_action_abs _ _).

    Lemma functional_2_to_monoid_action_is_morphism
      (d : functional_2_monoid_action)
      : is_monoid_action_morphism _ (functional_2_to_monoid_action_morphism_data d).
    Proof.
      intros x m.
      apply functional_1_eq.
      unfold functional_2_to_monoid_action_morphism_data.
      unfold functional_2_to_monoid_action_morphism_data_term.
      cbn -[weqvecfun action].
      pose (v := weqvecfun _ [(pr1 m ; pr1 d ; pr11 x ; pr12 x)]).
      unfold compose.
      rewrite <- (algebra_projects_component _ _ (make_stn 4 0 (idpath true)) v : _ = pr1 m).
      rewrite <- (algebra_projects_component _ _ (make_stn 4 1 (idpath true)) v : _ = pr1 d).
      rewrite <- (algebra_projects_component _ _ (make_stn 4 2 (idpath true)) v : _ = pr11 x).
      rewrite <- (algebra_projects_component _ _ (make_stn 4 3 (idpath true)) v : _ = pr12 x).
      do 2 rewrite move_action_through_vector_2.
      do 2 rewrite <- algebra_is_assoc.
      do 2 rewrite (move_action_through_vector_3 A).
      do 2 rewrite <- algebra_is_assoc.
      rewrite (move_action_through_vector_2 A).
      rewrite <- algebra_is_assoc.
      apply (maponpaths (λ x, action x v)).
      repeat rewrite (pr_is_var lambda).
      exact (!compose_compose_2_λ _ _ _ _).
    Qed.

    Definition functional_2_to_exponential_object_morphism_data
      : functional_2_monoid_action →
        (exponential_object _ (monoid_monoid_action _) (monoid_monoid_action _))
      := λ d, make_monoid_action_morphism _ _ (functional_2_to_monoid_action_is_morphism d).

    Definition exponential_object_to_functional_2_term
      (f : (exponential_object algebra_monoid (monoid_monoid_action _) (monoid_monoid_action _)))
      : A.
    Proof.
      refine (action (A := A) term_1_λ
        (weqvecfun _ [(_)])).
      apply (f : monoid_action_morphism _ _ _).
      split.
      - exact (action (A := A) T_λ (weqvecfun _ [()]) ,, is_functional_1_action_abs _ _).
      - exact (action (A := A) F_λ (weqvecfun _ [()]) ,, is_functional_1_action_abs _ _).
    Defined.

    Definition exponential_object_to_functional_2_morphism_data
      : monoid_action_morphism_data
        algebra_monoid
        (exponential_object algebra_monoid (monoid_monoid_action _) (monoid_monoid_action _))
        functional_2_monoid_action
      := λ x, (exponential_object_to_functional_2_term x ,, is_functional_2_action_abs _ _).

    Lemma functional_2_to_exponential_object_is_morphism
      : is_monoid_action_morphism algebra_monoid functional_2_to_exponential_object_morphism_data.
    Proof.
      intros a m.
      apply monoid_action_morphism_eq.
      intro x.
      apply functional_1_eq.
      unfold functional_2_to_exponential_object_morphism_data.
      unfold functional_2_to_monoid_action_morphism_data.
      unfold functional_2_to_monoid_action_morphism_data_term.
      cbn -[weqvecfun action].
      set (v := weqvecfun _ [(pr1 a ; pr1 m ; pr11 x ; pr12 x)]).
      rewrite <- (algebra_projects_component _ _ (make_stn 4 0 (idpath true)) v : _ = pr1 a).
      rewrite <- (algebra_projects_component _ _ (make_stn 4 1 (idpath true)) v : _ = pr1 m).
      rewrite <- (algebra_projects_component _ _ (make_stn 4 2 (idpath true)) v : _ = pr11 x).
      rewrite <- (algebra_projects_component _ _ (make_stn 4 3 (idpath true)) v : _ = pr12 x).
      unfold compose.
      do 2 rewrite move_action_through_vector_2.
      do 2 rewrite <- algebra_is_assoc.
      do 2 rewrite (move_action_through_vector_3 A).
      do 2 rewrite <- algebra_is_assoc.
      apply (maponpaths (λ x, action x v)).
      do 4 rewrite (pr_is_var lambda).
      cbn -[weqvecfun].
      apply compose_2_compose_λ.
    Qed.

    Definition term_2
      (a a' : A)
      := (action (A := A) term_2_λ (weqvecfun _ [(a ; a')]) ,, is_functional_1_action_abs _ _).

    Lemma compose_2_term_1
      (b : monoid_monoid_action algebra_monoid)
      (a a' : A)
      : action (A := A) compose_2_λ
        (weqvecfun 3 [(
          action (A := A) term_1_λ (weqvecfun 1 [(pr1 b)]);
          a;
          a'
        )])
      = pr1 (op algebra_monoid b (term_2 a a')).
    Proof.
      cbn -[weqvecfun action].
      set (v := weqvecfun _ [(pr1 b; a; a')]).
      unfold compose.
      rewrite <- (algebra_projects_component _ _ (make_stn 3 0 (idpath true)) v : _ = pr1 b).
      rewrite <- (algebra_projects_component _ _ (make_stn 3 1 (idpath true)) v : _ = a).
      rewrite <- (algebra_projects_component _ _ (make_stn 3 2 (idpath true)) v : _ = a').
      rewrite (move_action_through_vector_1 A).
      rewrite (move_action_through_vector_2 A).
      rewrite <- algebra_is_assoc.
      rewrite <- algebra_is_assoc.
      rewrite (move_action_through_vector_2 A).
      rewrite (move_action_through_vector_3 A).
      rewrite <- algebra_is_assoc.
      rewrite <- algebra_is_assoc.
      apply (maponpaths (λ x, action x v)).
      do 3 rewrite (pr_is_var lambda).
      cbn -[weqvecfun].
      apply compose_2_term_1_λ.
    Qed.

    Lemma is_z_iso_functional_2_exponential_object
      : is_inverse_in_precat
        (C := HSET)
        functional_2_to_exponential_object_morphism_data
        exponential_object_to_functional_2_morphism_data.
    Proof.
      split.
      - apply funextfun.
        intro a.
        apply functional_2_eq.
        set (v := weqvecfun _ [(pr1 a)]).
        unfold exponential_object_to_functional_2_morphism_data.
        unfold functional_2_to_exponential_object_morphism_data.
        unfold functional_2_to_monoid_action_morphism_data.
        unfold exponential_object_to_functional_2_term.
        unfold functional_2_to_monoid_action_morphism_data_term.
        cbn -[weqvecfun action].
        rewrite (pr2 a).
        rewrite <- (algebra_projects_component A _ (make_stn 1 0 (idpath true)) v : _ = pr1 a).
        unfold make_functional_2.
        unfold compose.
        unfold I2.
        do 3 rewrite <- (lift_constant_action _ _ v).
        rewrite (move_action_through_vector_2 A).
        rewrite <- algebra_is_assoc.
        rewrite (move_action_through_vector_3 A).
        rewrite <- algebra_is_assoc.
        rewrite (move_action_through_vector_1 A).
        rewrite <- algebra_is_assoc.
        apply (maponpaths (λ x, action x v)).
        rewrite (pr_is_var lambda).
        apply term_1_compose_2_λ.
      - apply funextfun.
        intro f.
        apply monoid_action_morphism_eq.
        intro a.
        apply functional_1_eq.
        refine (compose_2_term_1 _ _ _ @ _).
        refine (!base_paths _ _ (monoid_action_morphism_commutes _ f _ _) @ _).
        apply maponpaths.
        apply maponpaths.
        set (v := weqvecfun _ [(pr11 a ; pr12 a)]).
        apply pathsdirprod;
          apply functional_1_eq;
          [ refine (_ @ !pr21 a)
          | refine (_ @ !pr22 a) ];
          cbn -[weqvecfun action];
          unfold make_functional_1, compose, I1;
          rewrite <- (algebra_projects_component _ _ (make_stn 2 0 (idpath true)) v : _ = pr11 a);
          rewrite <- (algebra_projects_component _ _ (make_stn 2 1 (idpath true)) v : _ = pr12 a);
          rewrite <- (lift_constant_action _ _ v);
          rewrite <- (lift_constant_action _ _ v);
          rewrite (move_action_through_vector_2 A);
          rewrite (move_action_through_vector_2 A);
          rewrite <- algebra_is_assoc;
          rewrite <- algebra_is_assoc;
          rewrite (move_action_through_vector_2 A);
          rewrite <- algebra_is_assoc;
          apply (maponpaths (λ x, action x v));
          do 2 rewrite (pr_is_var lambda).
        + apply compose_T_λ.
        + apply compose_F_λ.
    Qed.

    Definition universal_monoid_exponential_iso
      : z_iso (C := monoid_action_category algebra_monoid)
        (functional_2_monoid_action)
        (exponential_object _ (monoid_monoid_action _) (monoid_monoid_action _)).
    Proof.
      use make_monoid_action_z_iso.
      - use make_z_iso.
        + exact functional_2_to_exponential_object_morphism_data.
        + exact exponential_object_to_functional_2_morphism_data.
        + exact is_z_iso_functional_2_exponential_object.
      - exact functional_2_to_exponential_object_is_morphism.
    Defined.

    Definition functional_app
      : monoid_action_morphism algebra_monoid (monoid_monoid_action _) functional_2_monoid_action.
    Proof.
      use make_monoid_action_morphism.
      - intro a.
        exists (compose I2 (pr1 a)).
        exact (compose_compose_eq (!I2_idempotent)).
      - intros a m.
        apply functional_2_eq.
        exact (!compose_assoc _ _ _).
    Defined.

    Definition functional_abs
      : monoid_action_morphism algebra_monoid functional_2_monoid_action (monoid_monoid_action _).
    Proof.
      use make_monoid_action_morphism.
      - intro a.
        exists (pr1 a).
        exact (is_functional_2_to_is_functional_1 _ (pr2 a)).
      - intros a m.
        now apply functional_1_eq.
    Defined.

    Definition lambda_algebra_theory
      : lambda_theory.
    Proof.
      use endomorphism_lambda_theory.
      - exact (monoid_action_category algebra_monoid).
      - apply terminal_monoid_action.
      - apply binproducts_monoid_action_category.
      - apply monoid_monoid_action.
      - apply is_exponentiable_monoid_action.
      - exact (inv_from_z_iso universal_monoid_exponential_iso · functional_abs).
      - exact ((functional_app : monoid_action_category _ ⟦_, _⟧) · morphism_from_z_iso _ _ universal_monoid_exponential_iso).
    Defined.

    Lemma lambda_algebra_theory_has_beta
      : has_beta lambda_algebra_theory.
    Proof.
      apply endomorphism_theory_has_beta.
      assert ((functional_abs : monoid_action_category _⟦_, _⟧) · functional_app = identity _).
      {
        apply monoid_action_morphism_eq.
        intro a.
        apply functional_2_eq.
        exact (!pr2 a).
      }
      refine (assoc' _ _ _ @ _).
      refine (maponpaths (λ x, _ · x) (assoc _ _ _ ) @ _).
      rewrite X.
      rewrite id_left.
      apply z_iso_after_z_iso_inv.
    Qed.

  End Theory.

End Monoid.
