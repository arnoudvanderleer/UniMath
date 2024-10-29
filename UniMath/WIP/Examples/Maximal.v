Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.WIP.MorphismSelections.
Require Import UniMath.WIP.DisplayMaps.
Require Import UniMath.WIP.RelativelyCartesianClosed.
Require Import UniMath.WIP.RestrictedSlices.
Require Import UniMath.WIP.ComprehensionCategory.

Require Import UniMath.WIP.Examples.Preliminaries.

Local Open Scope cat.

Section MaximalExample.

  Context {C : category}.
  Context (T : Terminal C).
  Context (P : Pullbacks C).

  Definition maximal_display_maps
    : display_maps C.
  Proof.
    exists (λ X Y f, htrue).
    use make_is_display_map_class.
    - exact T.
    - intro X.
      exact tt.
    - intros X Y Z f g.
      exact tt.
    - intros X Y Z f g.
      apply P.
    - intros X Y Z f g.
      exact tt.
  Defined.

  Definition restricted_slice_equivalence
    (X : C)
    : adj_equiv (restricted_slice maximal_display_maps X) (C / X).
  Proof.
    refine (_ ,, fiber_equiv _ _).
    apply sigma_contractible_equivalence;
      intros;
      apply iscontrunit.
  Defined.

  Section PullbackFunctorsIso.

    Context {X Y : C}.
    Context (f : X --> Y).

    Let HP
      : selected_morphism_pullback_map_ax maximal_display_maps _
      := display_maps_pullback_map maximal_display_maps.

    Definition restricted_slice_slice_pullback_iso_nat_trans_data
      : nat_trans_data
        (restricted_slice_equivalence Y ∙ cod_pb P f)
        (pullback_functor HP f ∙ restricted_slice_equivalence X).
    Proof.
      refine (λ (g : restricted_slice_ob _ Y), _).
      refine (invmap (z_iso_disp_z_iso_fiber _ X _ _) _).
      use iso_to_disp_iso.
      - exact (z_iso_from_Pullback_to_Pullback (P _ _ _ g f) (switchPullback (P _ _ _ f g))).
      - abstract exact (!PullbackArrow_PullbackPr1 _ _ _ _ _).
    Defined.

    Lemma restricted_slice_slice_pullback_iso_is_nat_trans
      : is_nat_trans _ _ restricted_slice_slice_pullback_iso_nat_trans_data.
    Proof.
      refine (λ (g1 g2 : restricted_slice_ob _ Y) h, _).
      apply eq_cod_mor.
      do 2 refine (transportf_cod_disp _ _ _ @ !_).
      apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _)));
        do 2 refine (assoc' _ _ _ @ !_).
      - do 2 refine (maponpaths _ (PullbackArrow_PullbackPr1 _ _ _ _ _) @ !_).
        refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
        refine (id_right _ @ !_).
        exact (PullbackArrow_PullbackPr1 _ _ _ _ _).
      - do 2 refine (maponpaths _ (PullbackArrow_PullbackPr2 _ _ _ _ _) @ !_).
        refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @  _).
        refine (transportf_cod_disp _ _ _ @ !_).
        refine (assoc _ _ _ @ _);
        exact (maponpaths (λ x, x · _) (PullbackArrow_PullbackPr2 _ _ _ _ _)).
    Qed.

    Definition restricted_slice_slice_pullback_iso_nat_trans
      : restricted_slice_equivalence Y ∙ cod_pb P f
        ⟹ pullback_functor HP f ∙ restricted_slice_equivalence X
      := make_nat_trans _ _ _ restricted_slice_slice_pullback_iso_is_nat_trans.

    Definition restricted_slice_slice_pullback_iso
      : z_iso (C := [_, _])
        (restricted_slice_equivalence Y
          ∙ cod_pb P f)
        (fiber_functor_from_cleaving _ (restricted_slice_cleaving HP) f
          ∙ restricted_slice_equivalence X).
    Proof.
      apply (invmap (z_iso_is_nat_z_iso _ _)).
      refine (nat_z_iso_comp _ (post_whisker_nat_z_iso
        (z_iso_is_nat_z_iso _ _ (z_iso_inv (fiber_pullback_iso _ f))) _)).
      use make_nat_z_iso.
      - exact restricted_slice_slice_pullback_iso_nat_trans.
      - intro g.
        apply z_iso_is_z_isomorphism.
    Defined.

  End PullbackFunctorsIso.

  Definition locally_to_relatively_cartesian_closed
    (H : is_locally_cartesian_closed P)
    : is_relatively_cartesian_closed maximal_display_maps.
  Proof.
    intros X Y f.
    refine (is_left_adjoint_closed_under_iso _ _ _ _).
    - refine (invmap (adjoint_equivalence_iso_weq
        (adj_equiv_inv (postcomp_equiv (restricted_slice_equivalence X)))) _).
      apply restricted_slice_slice_pullback_iso.
    - apply is_left_adjoint_functor_composite;
        [apply is_left_adjoint_functor_composite | ].
      + exact (restricted_slice_equivalence Y).
      + exact (pr2 (H X Y f)).
      + exact (adj_equiv_inv (restricted_slice_equivalence X)).
  Defined.

  Definition relatively_to_locally_cartesian_closed
    (H : is_relatively_cartesian_closed maximal_display_maps)
    : is_locally_cartesian_closed P.
  Proof.
    intros X Y f.
    refine (is_left_adjoint_closed_under_iso _ _ _ _).
    - refine (z_iso_comp (associator _ _ _) _).
      refine (invmap (adjoint_equivalence_iso_weq
        (precomp_equiv (restricted_slice_equivalence Y))) _).
      apply z_iso_inv.
      apply restricted_slice_slice_pullback_iso.
    - apply is_left_adjoint_functor_composite;
        [apply is_left_adjoint_functor_composite | ].
      + exact (adj_from_equiv _ _ _ (adj_equiv_inv (restricted_slice_equivalence Y))).
      + exact (pr2 (H X Y (f ,, tt))).
      + exact (adj_from_equiv _ _ _ (restricted_slice_equivalence X)).
  Defined.

End MaximalExample.
