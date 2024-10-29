Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Require Import UniMath.WIP.MorphismSelections.
Require Import UniMath.WIP.ComprehensionCategory.
Require Import UniMath.WIP.DisplayMaps.
Require Import UniMath.WIP.RestrictedSlices.

Local Open Scope cat.

Section LeftAdjoint.

  Context {C : category}.
  Context {D : morphism_selection C}.

  Context (HC : selected_morphism_composed_map_ax D).
  Context (P : selected_morphism_pullback_ax D).
  Context (HP : selected_morphism_pullback_map_ax D).

  Context {X Y : C}.
  Context (f : selected_morphism D X Y).

  (* Postcomposition *)

  Definition postcomposition_functor_data
    : functor_data (restricted_slice D X) (restricted_slice D Y).
  Proof.
    use make_functor_data.
    - refine (λ (g : restricted_slice_ob D X), _).
      exact (make_restricted_slice_ob _ (make_selected_morphism _ (HC _ _ _ g f))).
    - refine (λ (g h : restricted_slice_ob D X) (i : restricted_slice_mor g h), _).
      use make_restricted_slice_mor.
      * exact i.
      * abstract (
          refine (assoc _ _ _ @ _);
          refine (maponpaths (λ x, x · _) (restricted_slice_mor_commutes i) @ _);
          refine (maponpaths (λ x, x · _) (id_right _) @ _);
          exact (!id_right _)
        ).
  Defined.

  Lemma postcomposition_is_functor
    : is_functor postcomposition_functor_data.
  Proof.
    split.
    - refine (λ (g : restricted_slice_ob D X), _).
      now apply restricted_slice_mor_eq.
    - repeat intro.
      apply restricted_slice_mor_eq.
      refine (restricted_slice_mor_comp (X := X) _ _ @ !_).
      now refine (restricted_slice_mor_comp (X := Y) (# postcomposition_functor_data f0) (# _ g) @ !_).
  Qed.

  Definition postcomposition_functor
    : restricted_slice D X ⟶ restricted_slice D Y
    := make_functor _ postcomposition_is_functor.

  (* Adjunction *)

  Definition pullback_hom_weq
    (g : restricted_slice_ob D X)
    (h : restricted_slice_ob D Y)
    : restricted_slice_mor (postcomposition_functor g) h
    ≃ restricted_slice_mor g (fiber_functor_from_cleaving _ (restricted_slice_cleaving P HP) f h).
  Proof.
    use weq_iso;
      intro i.
    - use make_restricted_slice_mor.
      + use (PullbackArrow (P _ _ _ f h)).
        * exact g.
        * exact i.
        * abstract (
            refine (_ @ !restricted_slice_mor_commutes i);
            exact (!id_right _)
          ).
      + abstract (
          refine (_ @ !id_right _);
          exact (PullbackArrow_PullbackPr1 _ _ _ _ _)
        ).
    - use make_restricted_slice_mor.
      + refine ((i : C⟦_, _⟧) · PullbackPr2 _).
      + abstract (
          refine (_ @ !id_right _);
          refine (_ @ maponpaths (λ x, x · _) (id_right _));
          refine (!_ @ maponpaths (λ x, x · _) (restricted_slice_mor_commutes i));
          do 2 refine (assoc' _ _ _ @ !_);
          apply maponpaths;
          apply (PullbackSqrCommutes (P _ _ _ f h))
        ).
    - abstract (
        apply restricted_slice_mor_eq;
        exact (PullbackArrow_PullbackPr2 _ _ _ _ _)
      ).
    - abstract (
        apply restricted_slice_mor_eq;
        apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _)));
        [ refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ !_);
          refine (_ @ id_right _);
          exact (restricted_slice_mor_commutes i)
        | apply PullbackArrow_PullbackPr2 ]
      ).
  Defined.

  Lemma pullback_adjoint_natural_left
    (g : restricted_slice_ob D X)
    (h : restricted_slice_ob D Y)
    (i : restricted_slice_mor (postcomposition_functor g) h)
    (j : restricted_slice_ob D X)
    (k : restricted_slice_mor j g)
    : pullback_hom_weq j h (# (postcomposition_functor) k · i)
      = k · pullback_hom_weq g h i.
  Proof.
    apply restricted_slice_mor_eq.
    refine (_ @ !restricted_slice_mor_comp _ (pullback_hom_weq g h i)).
    apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _))).
    - refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ !_).
      refine (assoc' _ _ _ @ _).
      refine (maponpaths _ (PullbackArrow_PullbackPr1 _ _ _ _ _) @ _).
      refine (_ @ id_right _).
      exact (restricted_slice_mor_commutes k).
    - refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
      refine (_ @ assoc _ _ _).
      refine (restricted_slice_mor_comp (# _ k) i @ _).
      exact (!maponpaths (λ x, _ · x) (PullbackArrow_PullbackPr2 _ _ _ _ _)).
  Qed.

  Lemma pullback_adjoint_natural_right
    (g : restricted_slice_ob D X)
    (h : restricted_slice_ob D Y)
    (i : restricted_slice_mor (postcomposition_functor g) h)
    (j : restricted_slice_ob D Y)
    (k : restricted_slice_mor h j)
    : pullback_hom_weq g j (i · k)
      = pullback_hom_weq g h i · # (fiber_functor_from_cleaving _ (restricted_slice_cleaving P HP) f) k.
  Proof.
    apply restricted_slice_mor_eq.
    refine (_ @ !restricted_slice_mor_comp (pullback_hom_weq g h i) (# _ k)).
    apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _))).
    - refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ !_).
      refine (assoc' _ _ _ @ _).
      refine (maponpaths _ (PullbackArrow_PullbackPr1 _ _ _ _ _) @ _).
      refine (assoc _ _ _ @ _).
      refine (id_right _ @ _).
      exact (PullbackArrow_PullbackPr1 _ _ _ _ _).
    - refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
      refine (restricted_slice_mor_comp i k @ !_).
      refine (assoc' _ _ _ @ _).
      refine (maponpaths (λ x, _ · x) (PullbackArrow_PullbackPr2 _ _ _ _ _) @ _).
      refine (maponpaths (λ x, _ · pr1 x) (pr1_transportf _ _) @ _).
      refine (maponpaths _ (pr1_transportf (B := λ x, C⟦P Y X (restricted_slice_ob_domain h) f h, pr11 j⟧) _ _) @ _).
      refine (maponpaths _ (eqtohomot (transportf_const _ _) _) @ _).
      refine (assoc _ _ _ @ _).
      exact (maponpaths (λ x, x · _) (PullbackArrow_PullbackPr2 _ _ _ _ _)).
  Qed.

  Definition pullback_is_adjoint
    : are_adjoints postcomposition_functor (fiber_functor_from_cleaving _ (restricted_slice_cleaving P HP) f).
  Proof.
    use (invmap adjunction_homsetiso_weq).
    use tpair.
    - exact pullback_hom_weq.
    - split.
      + apply pullback_adjoint_natural_left.
      + apply pullback_adjoint_natural_right.
  Defined.

End LeftAdjoint.

Section DependentSums.

  Context {C : category}.
  Context {D : morphism_selection C}.

  Context (HC : selected_morphism_composed_map_ax D).
  Context (P : selected_morphism_pullback_ax D).
  Context (HP : selected_morphism_pullback_map_ax D).

  Definition restricted_morphisms_dependent_sum
    {X Y : C}
    (f : selected_morphism D X Y)
    : dependent_sum (restricted_slice_cleaving P HP) f.
  Proof.
    exists (postcomposition_functor HC f).
    apply pullback_is_adjoint.
  Defined.

End DependentSums.
