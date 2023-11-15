(**************************************************************************************************

  The category of algebraic theory algebras

  Defines the category of algebras for an algebraic theory. First, the category of dependent pairs
  of theories and algebras is formalized as a stack of displayed categories, then the category of
  algebras is a fiber of a (repeated) sigma category of this. The displayed category structure is
  then leveraged to show that the category is univalent.

  Contents
  1. The dependent product category of theories and algebras [algebra_full_cat]
  2. The category of algebras [algebra_cat]
  3. Univalence [is_univalent_algebra_cat]
  4. A characterization of isomorphisms of algebras [make_algebra_z_iso]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.Algebras.

Local Open Scope cat.

(** * 1. The dependent product category of theories and algebras *)

Definition algebra_data_full_disp_cat
  : disp_cat (cartesian algebraic_theory_cat HSET).
Proof.
  use disp_struct.
  - intro X.
    pose (T := pr1 X : algebraic_theory).
    pose (A := pr2 X : hSet).
    exact (∏ n, (T n : hSet) → (stn n → A) → A).
  - intros X X' action action' Y.
    pose (A := make_algebra_data (pr2 X) action).
    pose (A' := make_algebra_data (pr2 X') action').
    pose (F := pr1 Y : algebraic_theory_morphism _ _).
    pose (G := pr2 Y : A → A').
    exact (∏ n f a, G (action n f a) = action' n (F _ f) (λ i, G (a i))).
  - abstract (
      intros;
      do 3 (apply impred_isaprop; intro);
      apply setproperty
    ).
  - abstract (
      intros X action n f a;
      now rewrite ((eqtohomot (transportf_const _ ((pr2 X : hSet) → (pr2 X : hSet))) _)
        : pr2 (identity X) = identity _)
    ).
  - abstract (
      intros X X' X'' action action' action'' y y' Gcommutes G'commutes n f a;
      rewrite ((eqtohomot (transportf_const _ ((pr2 X : hSet) → (pr2 X'' : hSet))) _)
        : pr2 (y · y') = ((pr2 y) : HSET⟦_, _⟧) · (pr2 y'));
      unfold compose;
      simpl;
      now rewrite Gcommutes, G'commutes
    ).
Defined.

Definition algebra_data_full_cat : category
  := total_category algebra_data_full_disp_cat.

Definition algebra_full_disp_cat
  : disp_cat algebra_data_full_cat
  := disp_full_sub algebra_data_full_cat
    (λ X, is_algebra (make_algebra_data (pr21 X) (pr2 X))).

Definition algebra_full_cat : category
  := total_category algebra_full_disp_cat.

(** * 2. The category of algebras *)

Definition algebra_disp_cat
  : disp_cat algebraic_theory_cat
  := sigma_disp_cat (sigma_disp_cat algebra_full_disp_cat).

Definition algebra_cat
  (T : algebraic_theory)
  := fiber_category algebra_disp_cat T.

Lemma algebra_mor_comp
  {T : algebraic_theory}
  {A A' A'' : algebra_cat T}
  (F : algebra_cat T⟦A, A'⟧)
  (F' : algebra_cat T⟦A', A''⟧)
  : pr1 (F · F') = (pr1 F : HSET⟦_, _⟧) · (pr1 F').
Proof.
  refine (pr1_transportf _ _ @ _).
  now do 2 refine (eqtohomot (transportf_const _ _) _ @ _).
Qed.

Lemma algebra_identity
  {T : algebraic_theory}
  (A : algebra_cat T)
  : pr1 (identity A) = identity (C := HSET) ((A : algebra T) : hSet).
Proof.
  exact (eqtohomot (transportb_const _ _) _).
Qed.

Lemma displayed_algebra_morphism_eq
  {T T' : algebraic_theory}
  {F : algebraic_theory_morphism T T'}
  {A : algebra T}
  {A' : algebra T'}
  (G G' : (A : algebra_disp_cat _) -->[F] A')
  (H : pr1 G = pr1 G')
  : G = G'.
Proof.
  refine (subtypePath _ H).
  intro x.
  use (isapropdirprod _ _ _ isapropunit).
  repeat (apply impred_isaprop; intro).
  apply setproperty.
Qed.

(** * 3. Univalence *)

Lemma is_univalent_disp_algebra_data_full_disp_cat
  : is_univalent_disp algebra_data_full_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros TA action action'.
  use isweq_iso.
  - intro f.
    do 3 (apply funextsec; intro).
    refine (!_ @ pr1 f _ _ _ @ maponpaths (action' _ _) _).
    + refine (maponpaths (λ a, a _) (transportf_set _ _ _ _)).
      exact (isasetaprop (isasetunit _ _)).
    + apply funextfun.
      intro.
      refine (maponpaths (λ a, a _) (transportf_set _ _ _ _)).
      exact (isasetaprop (isasetunit _ _)).
  - intro.
    do 3 (apply impred_isaset; intro).
    apply setproperty.
  - intro.
    apply z_iso_eq.
    do 3 (apply impred_isaprop; intro).
    apply setproperty.
Qed.

Lemma is_univalent_algebra_data_full_cat
  : is_univalent algebra_data_full_cat.
Proof.
  use is_univalent_total_category.
  - rewrite cartesian_is_binproduct.
    exact (is_univalent_category_binproduct is_univalent_algebraic_theory_cat is_univalent_HSET).
  - exact is_univalent_disp_algebra_data_full_disp_cat.
Qed.

Lemma is_univalent_disp_algebra_full_disp_cat
  : is_univalent_disp algebra_full_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact (λ _, isaprop_is_algebra _).
Qed.

Lemma is_univalent_algebra_full_cat
  : is_univalent algebra_full_cat.
Proof.
  apply (is_univalent_total_category is_univalent_algebra_data_full_cat).
  exact is_univalent_disp_algebra_full_disp_cat.
Qed.

Lemma is_univalent_algebra_cat (T : algebraic_theory)
  : is_univalent (algebra_cat T).
Proof.
  refine (is_univalent_fiber_cat _ _ _).
  unfold algebra_disp_cat.
  repeat use is_univalent_sigma_disp.
  - apply is_univalent_reindex_disp_cat.
    apply is_univalent_disp_disp_over_unit.
    exact is_univalent_HSET.
  - exact is_univalent_disp_algebra_data_full_disp_cat.
  - exact is_univalent_disp_algebra_full_disp_cat.
Qed.

Section Test.
  Goal ∏ T, ob (algebra_cat T) = algebra T.
    exact (λ _, idpath _).
  Qed.
  Goal ∏ (T : algebraic_theory) (A A' : algebra T),
    (algebra_cat T)⟦A, A'⟧ = algebra_morphism A A'.
    exact (λ _ _ _, idpath _).
  Qed.
End Test.

(** * 4. A characterization of isomorphisms of algebras *)

Section Iso.

  Context {T : algebraic_theory}.
  Context {A A' : algebra T}.
  Context (F : z_iso (C := HSET) (A : hSet) (A' : hSet)).
  Context (H : preserves_action (morphism_from_z_iso _ _ F)).

  Definition algebra_mor
    : algebra_morphism A A'
    := make_algebra_morphism (morphism_from_z_iso _ _ F) H.

  Definition algebra_inv_data
    : algebra_morphism_data A' A
    := inv_from_z_iso F.

  Lemma algebra_inv_is_morphism
    : preserves_action algebra_inv_data.
  Proof.
    intros n f a.
    refine (_ @ eqtohomot (z_iso_inv_after_z_iso F) _).
    refine (_ @ maponpaths _ (!H _ _ _)).
    refine (maponpaths (λ x, _ (_ x)) _).
    apply funextfun.
    intro i.
    exact (eqtohomot (!z_iso_after_z_iso_inv F) _).
  Qed.

  Definition algebra_inv
    : algebra_morphism A' A
    := make_algebra_morphism algebra_inv_data algebra_inv_is_morphism.

  Lemma algebra_is_inverse
    : is_inverse_in_precat (C := algebra_cat T) algebra_mor algebra_inv.
  Proof.
    split.
    - apply (algebra_morphism_eq (T := T) (A := A) (A' := A)).
      intro.
      refine (eqtohomot (algebra_mor_comp _ _) _ @ _).
      refine (eqtohomot (z_iso_inv_after_z_iso F) _ @ _).
      exact (!eqtohomot (algebra_identity _) _).
    - apply (algebra_morphism_eq (T := T) (A := A') (A' := A')).
      intro.
      refine (eqtohomot (algebra_mor_comp _ _) _ @ _).
      refine (eqtohomot (z_iso_after_z_iso_inv F) _ @ _).
      exact (!eqtohomot (algebra_identity _) _).
  Qed.

  Definition make_algebra_z_iso
    : z_iso (C := algebra_cat T) A A'.
  Proof.
    use make_z_iso.
    - exact algebra_mor.
    - exact algebra_inv.
    - exact algebra_is_inverse.
  Defined.

End Iso.
