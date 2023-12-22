Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraCategory.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.Examples.LambdaCalculus.

Require Import UniMath.AlgebraicTheories.FundamentalTheorem.CommonUtilities.MonoidActions.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.TheoryToAlgebra.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.AlgebraToTheory.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.SpecificUtilities.Utilities.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.SpecificUtilities.LambdaTerms.

Local Open Scope cat.
Local Open Scope vec.

Section FundamentalTheorem.

  Context (lambda : lambda_calculus).
  Let L := lambda_calculus_lambda_theory lambda.

  Lemma theory_to_algebra_is_fully_faithful
    : fully_faithful (theory_to_algebra_functor lambda).
  Proof.
    intros l l'.
    use isweq_iso.
    - refine (λ (F : algebra_morphism (theory_to_algebra_functor lambda l : algebra _) (theory_to_algebra_functor lambda l' : algebra _)), (_ ,, tt)).
      use make_lambda_theory_morphism.
      + use make_algebraic_theory_morphism'.
        * intro.
          induction n as [ | n IHn].
          -- exact F.
          -- exact (λ t, LambdaTheories.app (IHn (LambdaTheories.abs t))).
        * use make_is_algebraic_theory_morphism'.
          -- admit.
          -- intro n.
            induction n as [ | n IHn].
            ++ exact (λ i, fromstn0 i).
            ++ intro i.
              cbn.
            intros m n f g.
            induction m as [ | m IHm];
            induction n as [ | n IHn].
            ++ cbn.
          --
            apply app.
          unfold algebra_morphism in F.
          cbn in X.
          use make_algebraic_theory_morphism'_data.
  Defined.

  Lemma theory_to_algebra_is_full
    : full (theory_to_algebra_functor lambda).
  Admitted.

  Lemma injective_to_faithful
    {C D : category}
    (F : C ⟶ D)
    (H : ∏ (c c' : C) (f f' : C⟦c, c'⟧), # F f = # F f' → f = f')
    : faithful F.
  Proof.
    intros c c'.
    apply (invmap (incl_injectivity _)).
    intros f f'.
    use isweq_iso.
    - apply H.
    - intro.
      apply homset_property.
    - intro.
      apply homset_property.
  Qed.

  Lemma theory_to_algebra_is_faithful
    : faithful (theory_to_algebra_functor lambda).
  Proof.
    apply injective_to_faithful.
    intros L' L'' G G' H.
    use subtypePath.
    {
      intro.
      apply isapropunit.
    }
    apply lambda_theory_morphism_eq.
    intros n f.
    induction n as [ | n IHn].
    * exact (maponpaths (λ x, (x : algebra_morphism (theory_to_algebra _ _ _) ((theory_to_algebra _ _ _))) f) H).
    * do 2 refine (!_ @ pr2 L'' _ _).
      do 2 refine (!_ @ maponpaths _ (lambda_theory_morphism_preserves_abs _ _ _)).
      now rewrite IHn.
  Qed.

  Definition app_λ
    : lambda 2
    := app
        (var (make_stn 2 0 (idpath true)))
        (var (make_stn 2 1 (idpath true))).

  Lemma action_is_app_action
    {n : nat}
    {A' : algebra L}
    (f : (L (S n) : hSet))
    (a : stn (S n) → A')
    : action f a
    = action (A := A') app_λ (weqvecfun _ [(action (A := A') (abs f) (λ i, a (dni lastelement i)) ; a lastelement)]).
  Proof.
    rewrite <- algebra_projects_component.
    pose (invmap (weqvecfun n) (var (L := lambda))).
    assert ((λ i, a (dni lastelement i)) = (λ i, action (A := A') (var (dni lastelement i)) a)).
    {
      apply funextfun.
      intro i.
      rewrite <- pr_is_var.
      now rewrite algebra_projects_component.
    }
    rewrite X.
    rewrite <- algebra_is_assoc.
    rewrite move_action_through_vector_2.
    rewrite <- algebra_is_assoc.
    rewrite (pr_is_var lambda).
    apply (maponpaths (λ x, action x _)).
    cbn -[weqvecfun action].
    unfold app_λ.
    rewrite subst_app.
    rewrite subst_abs.
    do 2 rewrite subst_var.
    cbn.
    rewrite beta_equality.
    rewrite subst_subst.
    refine (!subst_l_var _ @ !_).
    apply maponpaths.
    apply funextfun.
    intro i.
    rewrite <- (homotweqinvweq stnweq i).
    induction (invmap stnweq i) as [i' | i'];
      refine (maponpaths (λ x, _ (_ x) _) (homotinvweqweq stnweq _) @ _);
      cbn.
    - rewrite inflate_var.
      rewrite subst_var.
      now rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    - rewrite subst_var.
      now rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
  Qed.

  Lemma preserves_app_constants_to_preserves_action
    {A' A'' : algebra L}
    (F : A' → A'')
    (Happ : ∏ (a a' : A'),
      F (action (A := A') app_λ (weqvecfun _ [(a; a')]))
      = action (A := A'') app_λ (weqvecfun _ [(F a; F a')]))
    (Hconst : ∏ (l : lambda 0),
      F (action (A := A') l (weqvecfun _ [()]))
      = action (A := A'') l (weqvecfun _ [()]))
    : preserves_action F.
  Proof.
    intros n f a.
    induction n as [ | n IHn].
    - rewrite (empty_vector_eq A' _).
      rewrite (empty_vector_eq A'' _).
      exact (Hconst _).
    - refine (maponpaths _ (action_is_app_action _ _) @ !_).
      refine (action_is_app_action _ _ @ !_).
      refine (Happ _ _ @ _).
      refine (maponpaths (λ x, _ (_ [(x ; _)])) _).
      apply IHn.
  Qed.

  Section EssentiallySurjective.

    Context (A : algebra (lambda_calculus_lambda_theory lambda)).

    Definition theory_to_algebra_preimage
      : β_lambda_theory_cat.
    Proof.
      exists (lambda_algebra_theory lambda A).
      apply lambda_algebra_theory_has_beta.
    Defined.

    Definition preimage_image_to_algebra_set
      (a : fixpoint_set _ (monoid_monoid_action (algebra_monoid lambda A)))
      : A.
    Proof.
      use (action (n := 1) _ _).
      -- exact (app
          (var (make_stn 1 0 (idpath true)))
          (abs (var (make_stn 2 1 (idpath true))))).
      -- exact (weqvecfun _ [(pr11 a)]).
    Defined.

    Definition algebra_to_preimage_image_set_functional
      (a : A)
      : monoid_monoid_action (algebra_monoid _ A).
    Proof.
      refine (_ ,, is_functional_1_action_abs _ _ _ _).
      - exact (var (make_stn 2 0 (idpath true))).
      - exact (weqvecfun _ [(a)]).
    Defined.

    Lemma algebra_to_preimage_image_set_fixpoint
      (a : A)
      : ∏ m, op _ (algebra_to_preimage_image_set_functional a) m = (algebra_to_preimage_image_set_functional a).
    Proof.
      intro m.
      apply functional_1_eq.
      cbn -[action weqvecfun].
      unfold compose.
      unfold compose_λ.
      set (v := weqvecfun _ [(a ; pr1 m)]).
      rewrite <- (algebra_projects_component _ _ (make_stn 2 0 (idpath true)) v : _ = a).
      rewrite <- (algebra_projects_component _ _ (make_stn 2 1 (idpath true)) v : _ = pr1 m).
      rewrite (move_action_through_vector_1 A).
      rewrite <- algebra_is_assoc.
      rewrite (move_action_through_vector_2 A).
      rewrite <- algebra_is_assoc.
      apply (maponpaths (λ x, action (A := A) x _)).
      rewrite pr_is_var.
      cbn -[weqvecfun].
      rewrite subst_var.
      do 2 rewrite subst_abs.
      rewrite subst_var.
      do 2 rewrite subst_app.
      do 3 rewrite subst_var.
      extend_tuple_3.
      extend_tuple_2_0.
      cbn.
      do 2 rewrite inflate_var.
      rewrite inflate_abs.
      rewrite beta_equality.
      rewrite subst_var.
      rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
      do 2 rewrite inflate_var.
      rewrite subst_var.
      now rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    Qed.

    Definition algebra_to_preimage_image_set
      (a : A)
      : fixpoint_set _ (monoid_monoid_action (algebra_monoid lambda A))
      := _ ,, algebra_to_preimage_image_set_fixpoint a.

    Lemma preimage_image_algebra_inverse
      : is_inverse_in_precat (C := HSET) preimage_image_to_algebra_set algebra_to_preimage_image_set.
    Proof.
      split.
      - apply funextfun.
        intro a.
        cbn -[op] in a.
        use subtypePath.
        {
          intro.
          apply impred_isaprop.
          intro.
          apply setproperty.
        }
        refine (_ @ pr2 a (_ ,, is_functional_1_action_abs _ _ (abs (var (make_stn 2 1 (idpath true)))) (weqvecfun _ [()]))).
        apply functional_1_eq.
        refine (_ @ (idpath _ : compose _ _ _ _ = _)).
        unfold compose.
        unfold algebra_to_preimage_image_set.
        unfold preimage_image_to_algebra_set.
        cbn -[action weqvecfun].
        set (v := weqvecfun _ [(pr11 a)]).
        refine (_ @ maponpaths (λ x, _ (_ [(x; _)])) (algebra_projects_component _ _ (make_stn 1 0 (idpath true)) v)).
        rewrite <- (lift_constant_action _ _ v).
        rewrite (move_action_through_vector_1 A).
        rewrite (move_action_through_vector_2 A).
        do 2 rewrite <- algebra_is_assoc.
        rewrite pr_is_var.
        apply (maponpaths (λ x, action (A := A) x _)).
        unfold compose_λ.
        cbn -[weqvecfun].
        do 4 rewrite subst_abs.
        do 2 rewrite subst_var.
        do 2 rewrite subst_app.
        do 3 rewrite subst_var.
        extend_tuple_3.
        extend_tuple_2_0.
        cbn.
        rewrite inflate_var.
        rewrite inflate_app.
        do 2 rewrite inflate_abs.
        rewrite beta_equality.
        rewrite subst_var.
        do 2 rewrite subst_abs.
        rewrite subst_subst.
        rewrite inflate_var.
        rewrite subst_var.
        rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
        rewrite subst_var.
        rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
        now extend_tuple_2_1.
      - apply funextfun.
        intro a.
        refine (_ @ algebra_projects_component _ _ (make_stn 1 0 (idpath true)) (weqvecfun _ [(a)])).
        rewrite pr_is_var.
        unfold algebra_to_preimage_image_set.
        unfold preimage_image_to_algebra_set.
        cbn -[action weqvecfun].
        rewrite (move_action_through_vector_1 A).
        rewrite <- algebra_is_assoc.
        apply (maponpaths (λ x, action (A := A) x _)).
        cbn -[weqvecfun].
        rewrite subst_app.
        rewrite subst_abs.
        do 2 rewrite subst_var.
        extend_tuple_2_1.
        cbn.
        rewrite beta_equality.
        rewrite subst_var.
        now extend_tuple_2_0.
    Qed.

    Definition preimage_image_set_z_iso
      : z_iso (C := HSET) ((theory_to_algebra_functor lambda theory_to_algebra_preimage : algebra _) : hSet) (A : hSet).
    Proof.
      use (z_iso_comp (monoid_action_global_element_fixpoint_iso _ _)).
      use make_z_iso.
      - exact preimage_image_to_algebra_set.
      - exact algebra_to_preimage_image_set.
      - exact preimage_image_algebra_inverse.
    Defined.

    Definition app_I1_λ : lambda 1 :=
      app
        (var (make_stn 1 0 (idpath true)))
        (abs (var (make_stn 2 1 (idpath true)))).

    Lemma app_I1_compose_2_λ
      : subst (
          subst app_I1_λ (weqvecfun 1 [(
            compose_2_λ)])
        ) (weqvecfun 3 [(
          subst compose_λ (weqvecfun 2 [(
            subst I2_λ (weqvecfun 0 [()]);
            var (make_stn 2 0 (idpath true)))]);
          subst I1_λ (weqvecfun 0 [()]);
          var (make_stn 2 1 (idpath true)))])
      = subst app_λ (weqvecfun 2 [(
          subst app_I1_λ (weqvecfun 1 [(
            var (make_stn 2 0 (idpath true)))]);
          subst app_I1_λ (weqvecfun 1 [(
            var (make_stn 2 1 (idpath true)))]))]).
    Proof.
      unfold app_I1_λ, compose_2_λ, compose_λ, app_λ, I2_λ, I1_λ.
      do 5 rewrite subst_app .
      do 8 rewrite subst_abs .
      do 2 rewrite subst_subst .
      do 9 rewrite subst_var .
      do 3 rewrite subst_app .
      do 5 rewrite subst_var .
      extend_tuple_3.
      extend_tuple_2.
      do 2 extend_tuple_1.
      cbn.
      rewrite subst_var .
      rewrite subst_abs .
      do 2 rewrite inflate_var .
      rewrite inflate_abs .
      do 2 rewrite beta_equality .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      do 8 rewrite subst_app .
      do 2 rewrite subst_abs .
      do 5 rewrite subst_subst .
      do 4 rewrite subst_var .
      rewrite subst_app .
      do 2 rewrite subst_var .
      rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _) .
      do 2 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      rewrite subst_var .
      rewrite inflate_var .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      rewrite subst_var .
      rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _) .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      rewrite inflate_app .
      do 2 rewrite inflate_var .
      extend_tuple_4.
      cbn.
      rewrite subst_var .
      rewrite inflate_var .
      do 2 rewrite inflate_abs .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      do 2 rewrite subst_var .
      do 4 rewrite subst_abs .
      rewrite subst_subst .
      do 2 rewrite beta_equality .
      rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _) .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      rewrite subst_var .
      do 2 rewrite subst_app .
      rewrite subst_abs .
      rewrite beta_equality .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      do 4 rewrite subst_var .
      do 4 rewrite subst_app .
      do 6 rewrite subst_subst .
      do 3
      rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _) .
      do 3 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      rewrite subst_var .
      do 4 rewrite inflate_var .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      do 3 rewrite subst_var .
      do 4
      rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _) .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      rewrite subst_var .
      do 3 rewrite inflate_var .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      do 2 rewrite subst_var .
      do 3
      rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _) .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      rewrite inflate_var .
      rewrite inflate_abs .
      do 2 rewrite subst_var .
      rewrite subst_abs .
      rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _) .
      rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
      rewrite subst_var .
      now rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _) .
    Qed.

    Lemma app_I1_compose_2
      (a a' : A)
      : action (A := A) app_I1_λ (weqvecfun 1 [(
          action (A := A) compose_2_λ (weqvecfun 3 [(
            action (A := A) compose_λ (weqvecfun 2 [(
              I2 lambda A;
              a)]);
            I1 lambda A;
            a')]))]) =
        action (A := A) app_λ (weqvecfun 2 [(
          action (A := A) app_I1_λ (weqvecfun 1 [(
            a)]);
          action (A := A) app_I1_λ (weqvecfun 1 [(
            a')]))]).
    Proof.
      set (v := weqvecfun _ [(a ; a')]).
      rewrite <- (algebra_projects_component _ _ (make_stn 2 0 (idpath true)) v : _ = a).
      rewrite <- (algebra_projects_component _ _ (make_stn 2 1 (idpath true)) v : _ = a').
      unfold I1, I2.
      do 2 rewrite <- (lift_constant_action _ _ v).
      do 3 rewrite (move_action_through_vector_1 A).
      do 3 rewrite <- algebra_is_assoc.
      do 2 rewrite (move_action_through_vector_2 A).
      do 2 rewrite <- algebra_is_assoc.
      rewrite (move_action_through_vector_3 A).
      rewrite <- algebra_is_assoc.
      do 2 rewrite pr_is_var.
      refine (maponpaths (λ x, action x v) _).
      cbn -[weqvecfun].
      exact app_I1_compose_2_λ.
    Qed.

    Lemma TODO {X : UU} : X.
    Admitted.

    Lemma preimage_image_set_z_iso_preserves_app
      (A' := (theory_to_algebra_functor lambda theory_to_algebra_preimage : algebra L))
      (a a' : A')
      : (morphism_from_z_iso _ _ preimage_image_set_z_iso) (action (A := A') app_λ (weqvecfun 2 [(a; a')]))
      = action (A := A) app_λ (weqvecfun 2 [(
          (morphism_from_z_iso _ _ preimage_image_set_z_iso) a;
          (morphism_from_z_iso _ _ preimage_image_set_z_iso) a'
        )]).
    Proof.
      refine (maponpaths (λ x, action (A := A) _ (weqvecfun _ [(x)])) _ @ _).
      - refine (maponpaths (λ x, pr1 (_ x _)) (lambda_calculus_rect_app _ _) @ _).
        do 2 rewrite lambda_calculus_rect_var.
        refine (maponpaths
          (functional_2_to_monoid_action_morphism_data_term lambda A _ _)
          (idpath _ : _ = pr1 (monoid_action_morphism_to_function _ a' tt)) @ _).
        refine (maponpaths (λ x, _ (_ x) _ _) _).
        + refine (maponpaths _ _ @ _).
          * refine (maponpaths (λ x, _ x _ _) (extend_tuple_inl _ _ _) @ _).
            refine (maponpaths (λ x, _ (_ x _) _) (extend_tuple_inl _ _ _) @ _).
            refine (maponpaths
              (λ x, x ,, _)
              (idpath _ : _ = ((a' : monoid_action_morphism _ _ _) tt))
              @ maponpaths _ _).
            refine (maponpaths _ (idpath _ : _ = tt) @ _).
            refine (maponpaths (λ x, x ,, _) _).
            exact (maponpaths
              (λ x, _ (sn_power_projection _ _ _) (_ (_ x) _ _))
              (homotinvweqweq _ (inl lastelement))
              : _ = (a : monoid_action_morphism _ _ _) tt).
          * exact (maponpaths
              (λ x, _ (sn_power_projection _ _ _) (_ (_ x) _ _))
              (homotinvweqweq _ (inl (make_stn 1 0 (idpath true))))
              : _ = (a : monoid_action_morphism _ _ _) tt).
      - exact (app_I1_compose_2 _ _).
    Time Qed.

    Lemma preimage_image_set_z_iso_preserves_action
      : preserves_action (morphism_from_z_iso _ _ preimage_image_set_z_iso).
    Proof.
      apply preserves_app_constants_to_preserves_action.
      - intros a a'.
      -
    Qed.

    Definition preimage_image_z_iso
      : z_iso (C := algebra_cat (lambda_calculus_lambda_theory lambda)) (theory_to_algebra_functor _ theory_to_algebra_preimage) A.
    Proof.
      use make_algebra_z_iso.
      - exact preimage_image_set_z_iso.
      - exact preimage_image_set_z_iso_preserves_action.
    Qed.

  End EssentiallySurjective.

  Theorem FundamentalTheorem
    : adj_equivalence_of_cats (theory_to_algebra_functor lambda).
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univalent_β_lambda_theory_cat.
    - apply weq_fully_faithful_full_and_faithful.
      split.
      + exact theory_to_algebra_is_full.
      + exact theory_to_algebra_is_faithful.
    - intro A.
      apply hinhpr.
      exists (theory_to_algebra_preimage A).
      apply preimage_image_z_iso.
  Defined.

End FundamentalTheorem.
