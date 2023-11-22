Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.

Local Open Scope cat.

Section Morphism.

  Context {C C' : category}.

  Context (C_terminal : Terminal C).
  Context (C_bin_products : BinProducts C).
  Context (X : C).

  Context (C'_terminal : Terminal C').
  Context (C'_bin_products : BinProducts C').
  Context (X' : C').

  Context (F : C ⟶ C').
  Context (F_preserves_X : z_iso (F X) X').
  Context (F_preserves_terminal : preserves_terminal F).
  Context (F_preserves_binproduct : preserves_binproduct F).

  Let power
    (n : nat)
    : Product (stn n) C (λ _, X)
    := bin_product_power C X C_terminal C_bin_products n.

  Let power'
    (n : nat)
    : Product (stn n) C' (λ _, X')
    := bin_product_power C' X' C'_terminal C'_bin_products n.

  Definition F_power_iso
    (n : nat)
    : z_iso (F (power n)) (power' n).
  Proof.
    induction n as [ | n IHn].
    - apply (z_iso_Terminals (make_Terminal _ (F_preserves_terminal _ (pr2 C_terminal))) C'_terminal).
    - refine (z_iso_comp (preserves_binproduct_to_z_iso _ F_preserves_binproduct _ (C'_bin_products _ _)) _).
      apply binproduct_of_z_iso.
      + exact F_preserves_X.
      + exact IHn.
  Defined.

  Lemma F_preserves_power_pr
    {n : nat}
    (i : stn n)
    : #F (ProductPr _ _ (power n) i)
      = F_power_iso n · ProductPr _ _ (power' n) i · inv_from_z_iso F_preserves_X.
  Proof.
    induction n as [ | n IHn].
    - induction (negnatlthn0 _ (stnlt i)).
    - rewrite <- (homotweqinvweq stnweq i).
      induction (invmap stnweq i) as [i' | i'];
        refine (maponpaths (λ x, # F(_ x)) (homotinvweqweq stnweq _) @ !_);
        refine (maponpaths (λ x, _ · _ x · _) (homotinvweqweq stnweq _) @ !_).
      + refine (_ @ maponpaths (λ x, x · _) (assoc' _ _ _)).
        refine (_ @ maponpaths (λ x, x · _ · _) (assoc _ _ _)).
        refine (_ @ !maponpaths (λ x, _ · x · _ · _) (BinProductOfArrowsPr2 _ _ _ _ _)).
        refine (_ @ maponpaths (λ x, x · _ · _) (assoc' _ _ _)).
        refine (_ @ !maponpaths (λ x, x · _ · _ · _) (BinProductPr2Commutes _ _ _ _ _ _ _)).
        refine (functor_comp _ _ _ @ _).
        refine (maponpaths _ (IHn _) @ _).
        refine (assoc _ _ _ @ _).
        exact (maponpaths (λ x, x · _) (assoc _ _ _)).
      + cbn.
        refine (_ @ maponpaths (λ x, x · _) (assoc _ _ _)).
        refine (_ @ !maponpaths (λ x, _ x · _) (BinProductOfArrowsPr1 _ _ _ _ _)).
        refine (_ @ maponpaths (λ x, x · _) (assoc' _ _ _)).
        refine (_ @ assoc _ _ _).
        refine (_ @ !maponpaths _ (z_iso_inv_after_z_iso _)).
        refine (_ @ !id_right _).
        exact (!BinProductPr1Commutes _ _ _ _ _ _ _).
  Qed.

  Lemma F_preserves_product_arrow
    {n : nat}
    (Y : C)
    (f : stn n → C⟦Y, X⟧)
    : #F (ProductArrow _ _ (power n) f)
      = ProductArrow _ _ (power' n) (λ i, #F (f i) · F_preserves_X) · inv_from_z_iso (F_power_iso n).
  Proof.
    apply z_iso_inv_on_left.
    apply ProductArrow_eq.
    intro i.
    refine (!_ @ assoc _ _ _).
    refine (!maponpaths _ ((z_iso_inv_to_right _ _ _ _ _ _ (F_preserves_power_pr _))) @ _).
    refine (assoc _ _ _ @ _).
    refine (!maponpaths (λ x, x · _) (functor_comp _ _ _) @ _).
    refine (maponpaths (λ x, #F x · _) (ProductPrCommutes _ _ _ _ _ _ _) @ !_).
    exact (ProductPrCommutes _ _ _ _ _ _ _).
  Qed.

  Definition functor_to_algebraic_theory_morphism'_data
    : algebraic_theory_morphism'_data
      (endomorphism_theory C_terminal C_bin_products X)
      (endomorphism_theory C'_terminal C'_bin_products X')
    := λ _ f, inv_from_z_iso (F_power_iso _) · #F f · F_preserves_X.

  Lemma functor_to_is_algebraic_theory_morphism'
    : is_algebraic_theory_morphism' functor_to_algebraic_theory_morphism'_data.
  Proof.
    use make_is_algebraic_theory_morphism'.
    - intros m n f g.
      refine (assoc' _ _ _ @ _).
      apply z_iso_inv_on_right.
      do 2 refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ x, x · _) (assoc' _ _ _)).
      apply (maponpaths (λ x, x · _)).
      refine (functor_comp _ _ _ @ _).
      apply (maponpaths (λ x, x · _)).
      refine (F_preserves_product_arrow _ _ @ _).
      apply (maponpaths (λ x, x · _)).
      apply ProductArrow_eq.
      intro i.
      refine (ProductPrCommutes _ _ _ _ _ _ _ @ !_).
      refine (assoc' _ _ _ @ _).
      refine (maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ _).
      refine (assoc _ _ _ @ _).
      refine (maponpaths (λ x, x · _) (assoc _ _ _) @ _).
      refine (maponpaths (λ x, x · _ · _) (z_iso_inv_after_z_iso _) @ _).
      exact (maponpaths (λ x, x · _) (id_left _)).
    - intros n i.
      refine (maponpaths _ (pr_is_pr' _ _) @ !_).
      refine (pr_is_pr' _ _ @ !_).
      refine (maponpaths (λ x, _ · x · _) (F_preserves_power_pr _) @ _).
      apply z_iso_inv_to_right.
      apply z_iso_inv_on_right.
      apply assoc'.
  Qed.

  Definition functor_to_algebraic_theory_morphism
    : algebraic_theory_morphism
      (endomorphism_theory C_terminal C_bin_products X)
      (endomorphism_theory C'_terminal C'_bin_products X')
    := make_algebraic_theory_morphism' _ functor_to_is_algebraic_theory_morphism'.

  Context (E : is_exponentiable C_bin_products X).
  Context (abs : C⟦pr1 E X, X⟧).
  Context (app : C⟦X, pr1 E X⟧).

  Context (E' : is_exponentiable C'_bin_products X').
  Context (abs' : C'⟦pr1 E' X', X'⟧).
  Context (app' : C'⟦X', pr1 E' X'⟧).

  Let L := endomorphism_lambda_theory C_terminal C_bin_products X E abs app.
  Let L' := endomorphism_lambda_theory C'_terminal C'_bin_products X' E' abs' app'.

  Context (F_preserves_E : z_iso (F (pr1 E X)) (pr1 E' X')).
  Context (F_preserves_φ_adj_inv
    : #F (φ_adj_inv (pr2 E) app)
    = preserves_binproduct_to_z_iso _ F_preserves_binproduct (C_bin_products _ _) (C'_bin_products _ _)
      · binproduct_of_z_iso _ _ F_preserves_X F_preserves_X
      · φ_adj_inv (pr2 E') app'
      · inv_from_z_iso F_preserves_X).

  Context (F_preserves_φ_adj
    : #F (φ_adj (pr2 E) (id_pr (T := L)))
    = preserves_terminal_to_z_iso _ F_preserves_terminal C_terminal _
      · φ_adj (pr2 E') (id_pr (T := L'))
      · inv_from_z_iso F_preserves_E).

  Context (F_preserves_app_abs_abs
    : #F (# (pr1 E) (app · abs) · abs)
    = F_preserves_E
      · # (pr1 E') (app' · abs') · abs'
      · inv_from_z_iso F_preserves_X).

  Lemma functor_to_morphism_preserves_app
    {n : nat}
    (t : (L n : hSet))
    : functor_to_algebraic_theory_morphism _ (LambdaTheories.app (id_pr (T := L)))
    = LambdaTheories.app (id_pr (T := L')).
  Proof.
    refine (maponpaths _ (φ_adj_inv_natural_precomp _ _ _ _ _ _) @ !_).
    refine (φ_adj_inv_natural_precomp (pr2 E') _ _ _ _ _ @ !_).
    refine (maponpaths (λ x, _ · x · _) (functor_comp _ _ _) @ _).
    apply z_iso_inv_to_right.
    apply z_iso_inv_on_right.
    refine (maponpaths (λ x, _ · x) F_preserves_φ_adj_inv @ _).
    do 2 refine (assoc _ _ _ @ !_).
    apply (maponpaths (λ x, x · _)).
    do 2 refine (assoc _ _ _ @ !_).
    apply (maponpaths (λ x, x · _)).
    refine (maponpaths (λ x, x · _) (preserves_binproduct_to_preserves_arrow _ F_preserves_binproduct _ (C'_bin_products _ _) _ _) @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ x, x · _) (assoc' _ _ _) @ _).
    refine (maponpaths (λ x, _ · x · _) (z_iso_after_z_iso_inv _) @ _).
    refine (maponpaths (λ x, x · _) (id_right _) @ _).
    apply BinProductArrowsEq;
      do 2 refine (assoc' _ _ _ @ !_).
    - do 2 refine (maponpaths _ (BinProductOfArrowsPr1 _ _ _ _ _) @ !_).
      refine (assoc _ _ _ @ _).
      refine (maponpaths (λ x, x · _) (BinProductPr1Commutes _ _ _ _ _ _ _) @ _).
      refine (maponpaths (λ x, x · _) (functor_comp _ _ _) @ _).
      refine (maponpaths (λ x, x · _ · _) (preserves_binproduct_to_preserves_pr1 _ F_preserves_binproduct _ (C'_bin_products _ _)) @ _).
      refine (maponpaths (λ x, _ · x · _) (functor_id _ _) @ _).
      refine (maponpaths (λ x, x · _) (id_right _) @ !_).

      refine (maponpaths _ (id_right _) @ _).
      refine (assoc' _ _ _ @ _).
      refine (maponpaths (λ x, _ · x) (BinProductPr1Commutes _ _ _ _ _ _ _) @ _).
      exact (assoc _ _ _).
    - do 2 refine (maponpaths _ (BinProductOfArrowsPr2 _ _ _ _ _) @ !_).
      refine (assoc _ _ _ @ _).
      refine (maponpaths (λ x, x · _) (BinProductPr2Commutes _ _ _ _ _ _ _) @ _).
      refine (maponpaths (λ x, x · _) (functor_comp _ _ _) @ _).
      refine (maponpaths (λ x, x · _ · _) (preserves_binproduct_to_preserves_pr2 _ F_preserves_binproduct _ (C'_bin_products _ _)) @ _).
      refine (maponpaths (λ x, _ · x · _) (preserves_binproduct_to_preserves_pr1 _ F_preserves_binproduct _ (C'_bin_products _ _)) @ _).
      refine (maponpaths (λ x, x · _) (assoc _ _ _) @ !_).

      refine (assoc _ _ _ @ _).
      refine (maponpaths (λ x, x · _) (assoc' _ _ _) @ _).
      refine (maponpaths (λ x, _ · x · _) (BinProductPr2Commutes _ _ _ _ _ _ _) @ _).
      do 2 refine (maponpaths (λ x, x · _) (assoc _ _ _) @ _).
      refine (assoc' _ _ _ @ _).
      refine (maponpaths _ (BinProductOfArrowsPr1 _ _ _ _ _) @ _).
      exact (assoc _ _ _).
  Qed.

  Lemma functor_to_morphism_preserves_1
    {n : nat}
    (t : (L n : hSet))
    : functor_to_algebraic_theory_morphism _ (LambdaTheories.abs (LambdaTheories.abs (LambdaTheories.app (id_pr (T := L)))))
    = (LambdaTheories.abs (LambdaTheories.abs (LambdaTheories.app (id_pr (T := L'))))).
  Proof.
    refine (maponpaths (λ x, _ (_ (x · _) · _)) (φ_adj_after_φ_adj_inv _ _) @ _).
    refine (maponpaths (λ x, _ (_ x · _)) (assoc' _ _ _) @ _).
    refine (maponpaths (λ x, _ (x · _)) (φ_adj_natural_postcomp _ _ _ _ _ _) @ _).
    refine (maponpaths _ (assoc' _ _ _) @ _).
    refine (maponpaths (λ x, _ · x · _) (functor_comp _ _ _) @ _).
    refine (maponpaths (λ x, _ · (x · _) · _) F_preserves_φ_adj @ _).
    refine (assoc' _ _ _ @ !_).
    refine (maponpaths (λ x, _ (x · _) · _) (φ_adj_after_φ_adj_inv _ _) @ _).
    refine (maponpaths (λ x, _ x · _) (assoc' _ _ _) @ _).
    refine (maponpaths (λ x, x · _) (φ_adj_natural_postcomp _ _ _ _ _ _) @ !_).
    apply z_iso_inv_on_right.
    do 3 refine (assoc' _ _ _ @ _).
    apply (maponpaths (λ x, _ · x)).
    refine (_ @ assoc _ _ _).
    apply (maponpaths (λ x, φ_adj (pr2 E') (id_pr (T := L')) · x)).
    apply z_iso_inv_on_right.
    refine (_ @ assoc' _ _ _).
    apply z_iso_inv_to_right.
    apply F_preserves_app_abs_abs.
  Qed.

End Morphism.
