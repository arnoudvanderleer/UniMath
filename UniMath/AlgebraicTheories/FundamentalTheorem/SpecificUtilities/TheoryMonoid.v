Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Setcategories.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.

Require Import UniMath.AlgebraicTheories.FundamentalTheorem.CommonUtilities.MonoidToCategory.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.SpecificUtilities.LawvereTheory.

Local Open Scope algebraic_theories.
Local Open Scope cat.

Section TheoryMonoid.

  Context (T : algebraic_theory).

  Definition theory_monoid : monoid.
  Proof.
    use make_monoid.
    - use make_setwithbinop.
      + exact (T 1).
      + intros a b.
        exact (a • (λ _, b)).
    - use make_ismonoidop.
      + intros a b c.
        apply algebraic_theory_comp_is_assoc.
      + exists (id_pr).
        split.
        * intro m.
          apply algebraic_theory_comp_is_unital.
        * intro m.
          refine (_ @ algebraic_theory_comp_identity_projections _ _ _).
          apply (maponpaths (comp m)).
          apply funextfun.
          intro i.
          refine (algebraic_theory_id_pr_is_pr _ @ _).
          apply maponpaths.
          apply isconnectedstn1.
  Defined.

  Definition monoid_to_lawvere
    : monoid_to_category_ob theory_monoid ⟶ lawvere_theory T.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro t.
        exact 1.
      + intros t t' f i.
        exact f.
    - split.
      + abstract (
          intro t;
          apply funextfun;
          intro i;
          refine (algebraic_theory_id_pr_is_pr _ @ _);
          apply (maponpaths pr);
          apply isconnectedstn1
        ).
      + abstract easy.
  Defined.

End TheoryMonoid.
