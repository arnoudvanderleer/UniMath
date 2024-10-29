Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Require Import UniMath.WIP.MorphismSelections.
Require Import UniMath.WIP.DisplayMaps.
Require Import UniMath.WIP.RestrictedSlices.

Local Open Scope mor_disp.
Local Open Scope cat.

Section ComprehensionCat.

  Context {C : category}.
  Context {D : morphism_selection C}.
  Context {P : selected_morphism_pullback_ax D}.
  Context (HP : selected_morphism_pullback_map_ax D P).

  Section Fibration.

    Section CartesianLift.

      Context {X Y : C}.
      Context (f : Y --> X).
      Context (g : restricted_slice_disp D X).

      Definition restricted_slice_cleaving_object
        : restricted_slice_disp D Y
        := make_restricted_slice_ob _
          (make_selected_morphism _ (HP _ _ _ f (g : restricted_slice_ob D X))).

      Definition restricted_slice_cleaving_morphism
        : restricted_slice_cleaving_object -->[f] g.
      Proof.
        refine ((PullbackPr2 _ ,, _) ,, tt).
        abstract exact (!PullbackSqrCommutes _).
      Defined.

      Section IsCartesian.

        Context {Z : C}.
        Context {h : C⟦Z, Y⟧}.
        Context {i : restricted_slice_disp D Z}.
        Context (j : i -->[h · f] g).

        Definition restricted_slice_cleaving_is_cartesian_morphism
          : i -->[h] restricted_slice_cleaving_object.
        Proof.
          use ((_ ,, _) ,, tt).
          - use PullbackArrow.
            + exact ((i : restricted_slice_ob D Z) · h).
            + exact (pr11 j).
            + abstract (
                refine (_ @ !pr21 j);
                apply assoc'
              ).
          - abstract apply PullbackArrow_PullbackPr1.
        Defined.

        Lemma restricted_slice_cleaving_is_cartesian_commutes
          : restricted_slice_cleaving_is_cartesian_morphism ;; restricted_slice_cleaving_morphism
          = j.
        Proof.
          apply restricted_slice_mor_eq.
          apply PullbackArrow_PullbackPr2.
        Qed.

        Lemma restricted_slice_cleaving_is_cartesian_unique
          (k : i -->[h] restricted_slice_cleaving_object)
          (Hk : k ;; restricted_slice_cleaving_morphism = j)
          : k = restricted_slice_cleaving_is_cartesian_morphism.
        Proof.
          apply restricted_slice_mor_eq.
          apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _))).
          - refine (_ @ !PullbackArrow_PullbackPr1 _ _ _ _ _).
            exact (pr21 k).
          - refine (_ @ !PullbackArrow_PullbackPr2 _ _ _ _ _).
            exact (base_paths _ _ (base_paths _ _ Hk)).
        Qed.

      End IsCartesian.

    End CartesianLift.

    Definition restricted_slice_cleaving
      : cleaving (restricted_slice_disp D).
    Proof.
      intros X Y f g.
      simple refine (_ ,, _ ,, _).
      - exact (restricted_slice_cleaving_object f g).
      - exact (restricted_slice_cleaving_morphism f g).
      - intros Z h i j.
        use unique_exists.
        + apply (restricted_slice_cleaving_is_cartesian_morphism f g j).
        + apply restricted_slice_cleaving_is_cartesian_commutes.
        + abstract (intro; apply homsets_disp).
        + apply restricted_slice_cleaving_is_cartesian_unique.
    Defined.

  End Fibration.

  Section CartesianProjection.

    Context (X1 X2 : C).
    Context (f : X2 --> X1).
    Context (g1 : restricted_slice_disp D X1).

    Section UniqueExistence.

      Context {Y : C}.
      Context {i : Y --> X2}.
      Context {j : disp_codomain C Y}.
      Context (k : j -->[i · f] pr1 g1).

      Definition restricted_slice_comprehension_is_cartesian_morphism
        : j -->[i] pr1 (object_of_cartesian_lift g1 f (restricted_slice_cleaving X1 X2 f g1)).
      Proof.
        use tpair.
        - use PullbackArrow.
          + refine (pr2 j · i).
          + exact (pr1 k).
          + abstract (
              refine (_ @ !pr2 k);
              apply assoc'
            ).
        - abstract apply PullbackArrow_PullbackPr1.
      Defined.

      Lemma restricted_slice_comprehension_is_cartesian_morphism_commutes
        : restricted_slice_comprehension_is_cartesian_morphism ;; pr1 (mor_disp_of_cartesian_lift g1 f (restricted_slice_cleaving X1 X2 f g1)) = k.
      Proof.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        apply PullbackArrow_PullbackPr2.
      Qed.

      Lemma restricted_slice_comprehension_is_cartesian_morphism_unique
        (y : j -->[i] pr1 (object_of_cartesian_lift g1 f (restricted_slice_cleaving X1 X2 f g1)))
        (Hy : y ;; pr1 (mor_disp_of_cartesian_lift g1 f (restricted_slice_cleaving X1 X2 f g1)) = k)
        : y = restricted_slice_comprehension_is_cartesian_morphism.
      Proof.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _))).
        - refine (_ @ !PullbackArrow_PullbackPr1 _ _ _ _ _).
          exact (pr2 y).
        - refine (_ @ !PullbackArrow_PullbackPr2 _ _ _ _ _).
          exact (base_paths _ _ Hy).
      Qed.

    End UniqueExistence.

    Lemma is_cartesian_cleaving_lift
      : is_cartesian (pr1 (mor_disp_of_cartesian_lift
          g1
          f
          (restricted_slice_cleaving X1 X2 f g1))).
    Proof.
      intros Y i j k.
      use unique_exists.
      + exact (restricted_slice_comprehension_is_cartesian_morphism k).
      + exact (restricted_slice_comprehension_is_cartesian_morphism_commutes k).
      + abstract (
          intro;
          apply homsets_disp
        ).
      + exact (restricted_slice_comprehension_is_cartesian_morphism_unique k).
    Defined.

  End CartesianProjection.

  Definition selected_morphism_comprehension_cat
    : comprehension_cat_structure C.
  Proof.
    exists (restricted_slice_disp D).
    exists restricted_slice_cleaving.
    exists (sigmapr1_disp_functor _).
    apply (cartesian_functor_from_cleaving restricted_slice_cleaving).
    exact is_cartesian_cleaving_lift.
  Defined.

End ComprehensionCat.
