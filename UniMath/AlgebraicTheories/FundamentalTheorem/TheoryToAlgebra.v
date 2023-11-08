Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.AlgebraCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.Examples.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Section Functor.

  Context (lambda : lambda_calculus).
  Let L
    : lambda_theory
    := lambda_calculus_lambda_theory lambda.

  Section LambdaInitial.

    Context (L' : lambda_theory).
    Context (H : has_beta L').

    Definition initial_morphism_data'
      : ∏ n, (L n : hSet) → (L' n : hSet).
    Proof.
      use lambda_calculus_rect.
      - exact (λ _ i, pr i).
      - intros n l l'.
        refine ((app l) • (extend_tuple pr l')).
      - exact (λ _ l, abs l).
      - exact (λ _ _ f g, f • g).
      - abstract (
          repeat split;
          [ apply algebraic_theory_comp_projects_component
          | intros m n al al' af;
            rewrite lambda_theory_app_compatible_with_comp;
            do 2 refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ !_);
            apply maponpaths;
            apply funextfun;
            intro i;
            rewrite <- (homotweqinvweq stnweq i);
            induction (invmap stnweq i) as [i' | i'];
              do 2 refine (maponpaths (λ x, (_ x) • _) (homotinvweqweq _ _) @ !_);
            [ cbn;
              rewrite algebraic_theory_comp_projects_component;
              rewrite algebraic_theory_functor_uses_projections;
              rewrite algebraic_theory_comp_is_assoc;
              refine (!algebraic_theory_comp_identity_projections _ _ _ @ _);
              apply maponpaths;
              apply funextfun;
              intro j;
              rewrite algebraic_theory_comp_projects_component;
              exact (!extend_tuple_inl _ _ _)
            | cbn;
              rewrite algebraic_theory_comp_projects_component;
              exact (!extend_tuple_inr _ _)]
          | intros m n al af;
            rewrite <- lambda_theory_abs_compatible_with_comp;
            apply (maponpaths (λ x, abs (al • x)));
            apply extend_tuple_eq;
            [ intro i;
              refine (_ @ !maponpaths _ (homotinvweqweq stnweq _));
              now rewrite algebraic_theory_functor_uses_projections
            | exact (!maponpaths _ (homotinvweqweq stnweq _)) ]
          | intros l m n a ag af;
            apply algebraic_theory_comp_is_assoc
          | intros n af ag;
            exact (maponpaths (λ x, x • _) (H _ _))]
        ).
    Defined.

    Lemma initial_is_algebraic_theory_morphism'
      : is_algebraic_theory_morphism' initial_morphism_data'.
    Proof.
      split.
      - exact (λ _ _, lambda_calculus_rect_subst).
      - intros n i.
        rewrite (pr_is_var lambda).
        exact (lambda_calculus_rect_var _).
    Qed.

    Lemma initial_preserves_app
      {n : nat}
      (t : (L n : hSet))
      : initial_morphism_data' _ (app t) = app (initial_morphism_data' _ t).
    Proof.
      refine (lambda_calculus_rect_app _ _ @ _).
      unfold inflate.
      rewrite lambda_calculus_rect_subst.
      rewrite lambda_calculus_rect_var.
      refine (maponpaths (λ x, x • _) (lambda_theory_app_compatible_with_comp _ _) @ _).
      refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ _).
      refine (_ @ algebraic_theory_comp_identity_projections _ _ _).
      apply maponpaths.
      apply funextfun.
      intro i.
      rewrite <- (homotweqinvweq stnweq i).
      induction (invmap stnweq i) as [i' | i'];
        refine (maponpaths (λ x, _ x • _) (homotinvweqweq stnweq _) @ _).
      - cbn.
        rewrite lambda_calculus_rect_var.
        rewrite algebraic_theory_functor_uses_projections.
        do 2 rewrite algebraic_theory_comp_projects_component.
        apply extend_tuple_inl.
      - cbn.
        rewrite algebraic_theory_comp_projects_component.
        apply extend_tuple_inr.
    Qed.

    Lemma initial_preserves_abs
      {n : nat}
      (t : (L (S n) : hSet))
      : initial_morphism_data' _ (abs t) = abs (initial_morphism_data' _ t).
    Proof.
      exact (lambda_calculus_rect_abs _).
    Qed.

    Definition initial_morphism
      : lambda_theory_morphism L L'.
    Proof.
      use make_lambda_theory_morphism.
      use make_lambda_theory_data_morphism.
      - use make_algebraic_theory_morphism'.
        + exact initial_morphism_data'.
        + exact initial_is_algebraic_theory_morphism'.
      - exact (λ _, initial_preserves_app).
      - exact (λ _, initial_preserves_abs).
    Defined.

    Lemma initial_morphism_unique
      (F : lambda_theory_morphism L L')
      : F = initial_morphism.
    Proof.
      apply lambda_theory_morphism_eq.
      use (lambda_calculus_ind_prop (λ n f, (_ ,, (_ : isaprop _))) _ _ _ _).
      - apply setproperty.
      - intros n i.
        do 2 refine (!_ @ maponpaths _ (pr_is_var lambda _)).
        now do 2 refine (algebraic_theory_morphism_preserves_projections _ _ @ !_).
      - intros n l l' Hl Hl'.
        refine (_ @ !lambda_calculus_rect_app _ _).
        refine (_ @ maponpaths (λ x, app x • _) Hl).
        refine (_ @ maponpaths (λ x, _ (_ x)) Hl').
        refine (maponpaths _ (!_ : _ = app (L := L) l • extend_tuple (pr (T := L)) l') @ _).
        + cbn.
          rewrite subst_app.
          rewrite subst_var.
          unfold inflate.
          rewrite subst_subst.
          refine (maponpaths _ (extend_tuple_inr _ _) @ _).
          apply (maponpaths (λ x, _ x _)).
          refine (_ @ subst_l_var _).
          apply maponpaths.
          apply funextfun.
          intro.
          rewrite subst_var.
          refine (extend_tuple_inl _ _ _ @ _).
          apply pr_is_var.
        + refine (algebraic_theory_morphism_preserves_composition _ _ _ _ _ @ _).
          refine (maponpaths (λ x, x • _) (lambda_theory_data_morphism_preserves_app _ _ _) @ !_).
          apply maponpaths.
          apply extend_tuple_eq.
          * intro i.
            refine (!algebraic_theory_morphism_preserves_projections F _ @ _).
            apply maponpaths.
            exact (!maponpaths _ (homotinvweqweq stnweq _)).
          * refine (!_).
            exact (maponpaths (λ x, _ (_ x)) (homotinvweqweq stnweq _)).
      - intros n l Hl.
        refine (lambda_theory_data_morphism_preserves_abs _ _ _ @ !_).
        refine (lambda_theory_data_morphism_preserves_abs initial_morphism _ _ @ !_).
        apply maponpaths.
        exact Hl.
      - intros m n f g Hf Hg.
        refine (algebraic_theory_morphism_preserves_composition _ _ _ _ _ @ !_).
        refine (algebraic_theory_morphism_preserves_composition initial_morphism _ _ _ _ @ !_).
        refine (maponpaths (λ x, x • _) Hf @ _).
        apply maponpaths.
        apply funextfun.
        exact Hg.
    Qed.

  End LambdaInitial.

  Definition theory_to_algebra_data
    (L' : lambda_theory)
    (H : has_beta L')
    : algebra_data L.
  Proof.
    use make_algebra_data.
    - exact (pr1 L' 0).
    - intros n f a.
      pose (f' := initial_morphism L' H _ f).
      exact (f' • a).
  Defined.

  Lemma theory_to_is_algebra
    (L' : lambda_theory)
    (H : has_beta L')
    : is_algebra (theory_to_algebra_data L' H).
  Proof.
    use make_is_algebra'.
    - intros m n f g a.
      refine (_ @ algebraic_theory_comp_is_assoc _ _ _ _ _ _ _).
      apply (maponpaths (λ x, x • _)).
      apply (algebraic_theory_morphism_preserves_composition (initial_morphism _ _)).
    - intros n i a.
      refine (maponpaths (λ x, x • _) (algebraic_theory_morphism_preserves_projections (initial_morphism _ _) _) @ _).
      apply algebraic_theory_comp_projects_component.
  Qed.

  Definition theory_to_algebra
    (L' : lambda_theory)
    (H : has_beta L')
    : algebra L
    := make_algebra _ (theory_to_is_algebra L' H).

  Definition theory_morphism_to_algebra_morphism_data
    {L' L'' : lambda_theory}
    (HL' : has_beta L')
    (HL'' : has_beta L'')
    (F : lambda_theory_morphism L' L'')
    : algebra_morphism_data (theory_to_algebra L' HL') (theory_to_algebra L'' HL'')
    := (pr1 F) 0.

  Lemma theory_morphism_to_is_algebra_morphism
    {L' L'' : lambda_theory}
    (HL' : has_beta L')
    (HL'' : has_beta L'')
    (F : lambda_theory_morphism L' L'')
    : preserves_action (theory_morphism_to_algebra_morphism_data HL' HL'' F).
  Proof.
    intros n f a.
    refine (algebraic_theory_morphism_preserves_composition _ _ _ _ _ @ _).
    apply (maponpaths (λ x, x • _)).
    exact (maponpaths
      (λ x, (x : lambda_theory_morphism L _) n f)
      (initial_morphism_unique _ _ ((initial_morphism _ _ : lambda_theory_cat⟦_, _⟧) · _))).
  Qed.

  Definition theory_morphism_to_algebra_morphism
    {L' L'' : lambda_theory}
    (HL' : has_beta L')
    (HL'' : has_beta L'')
    (F : lambda_theory_morphism L' L'')
    : algebra_morphism (theory_to_algebra L' HL') (theory_to_algebra L'' HL'')
    := make_algebra_morphism _ (theory_morphism_to_is_algebra_morphism HL' HL'' F).

  Definition theory_to_algebra_functor_data
    : functor_data β_lambda_theory_cat (algebra_cat L)
    := make_functor_data (C := β_lambda_theory_cat) (C' := algebra_cat L)
      (λ L', theory_to_algebra (pr1 L') (pr2 L'))
      (λ L' L'' F, theory_morphism_to_algebra_morphism (pr2 L') (pr2 L'') (pr1 F)).

  Lemma theory_to_algebra_is_functor
    : is_functor theory_to_algebra_functor_data.
  Proof.
    split.
    - intro L'.
      apply displayed_algebra_morphism_eq.
      apply funextfun.
      intro.
      exact (!maponpaths (λ x, x _ _) (transportb_const _ _)).
    - intros L' L'' L''' F F'.
      apply displayed_algebra_morphism_eq.
      now refine (_ @ !algebra_mor_comp _ _).
  Qed.

  Definition theory_to_algebra_functor
    : β_lambda_theory_cat ⟶ algebra_cat L
    := make_functor
      theory_to_algebra_functor_data
      theory_to_algebra_is_functor.

End Functor.
