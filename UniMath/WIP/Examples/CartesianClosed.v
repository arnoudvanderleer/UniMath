Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Require Import UniMath.WIP.MorphismSelections.
Require Import UniMath.WIP.DisplayMaps.

Local Open Scope cat.

Section CartesianClosed.

  Context {C : category}.

  (* We need univalence to make sure that pullbacks are a proposition *)
  Context (U : is_univalent C).

  Context (T : Terminal C).
  Context (BP : BinProducts C).

  Definition cartesian_closed_morphism_selection
    : morphism_selection C
    := λ X A f, ∃ (B : C) (g : X --> B), isBinProduct _ _ _ _ f g.

  Lemma cartesian_closed_terminal_map
    : selected_morphism_terminal_map_ax cartesian_closed_morphism_selection T.
  Proof.
    intro X.
    use hinhpr.
    exists X.
    exists (identity X).
    apply terminal_binprod_l.
  Qed.

  Lemma cartesian_closed_composed_map
    : selected_morphism_composed_map_ax cartesian_closed_morphism_selection.
  Proof.
    intros X Y Z f g.
    refine (hinhfun2 _ (selected_morphism_is_selected f) (selected_morphism_is_selected g)).
    intros Hf Hg.
    refine (_ ,, _ ,, _).
    exact (is_binproduct_assoc
      (make_BinProduct _ _ _ _ _ _ (pr22 Hg))
      (BP _ _)
      (make_BinProduct _ _ _ _ _ _ (pr22 Hf))).
  Qed.

(** For the next two lemmas, we have a diagram
<<
       f×id          π2
  Y×A ------> X×A -------> A
   |           |           |
 π1|           |g          |!
   v           v           v
   Y --------> X --------> T
        f            !
>>
*)
  Definition cartesian_closed_pullback
    : selected_morphism_pullback_ax cartesian_closed_morphism_selection.
  Proof.
    intros X Y Z f g.
    refine (hinhuniv
      (P := make_hProp _ (isaprop_Pullback _ U f g)) _
      (selected_morphism_is_selected g)).
    intro Hg.
    simple refine (make_Pullback _ (isPullback_two_pullback
      Y
      (BP Y (pr1 Hg)) _
      f _ _
      (invmap (is_terminal_pullback_binproduct_weq T _ _ _ _) (pr22 Hg)) _ _)).
    - apply BinProductPr1.
    - apply (BinProductArrow _ (make_BinProduct _ _ _ _ _ _ (pr22 Hg))).
      + exact (BinProductPr1 _ _ · f).
      + apply BinProductPr2.
    - abstract exact (!BinProductPr1Commutes _ _ _ (make_BinProduct _ _ _ _ _ _ (pr22 Hg)) _ _ _).
    - refine (isPullback_mor_paths _ _ _ _ _ _ _).
      5: {
        apply (invmap (is_terminal_pullback_binproduct_weq T _ _ _ _)).
        apply (isBinProduct_BinProduct _ (BP Y (pr1 Hg))).
      }
      + abstract exact (TerminalArrowEq _ _).
      + abstract apply TerminalArrowEq.
      + abstract reflexivity.
      + abstract exact (!BinProductPr2Commutes _ _ _ (make_BinProduct _ _ _ _ _ _ (pr22 Hg)) _ _ _).
  Defined.

  Lemma cartesian_closed_pullback_map
    : selected_morphism_pullback_map_ax cartesian_closed_morphism_selection.
  Proof.
    intros X Y Z f g P.
    refine (hinhfun _ (selected_morphism_is_selected g)).
    intro Hg.
    exists (pr1 Hg).
    exists (PullbackPr2 _ · pr12 Hg).
    apply (is_terminal_pullback_binproduct_weq T).
    refine (isPullback_mor_paths _ _ _ _ _ _ _).
    - apply TerminalArrowEq.
    - apply TerminalArrowEq.
    - reflexivity.
    - reflexivity.
    - refine (isPullbackGluedSquare _ (isPullback_Pullback P)).
      apply ((invmap (is_terminal_pullback_binproduct_weq T _ _ _ _) )).
      apply (pr22 Hg).
  Qed.

  Definition cartesian_closed_display_maps
    : display_maps C.
  Proof.
    use make_display_maps.
    - exact cartesian_closed_morphism_selection.
    - use make_is_display_map_class.
      + exact T.
      + exact cartesian_closed_terminal_map.
      + exact cartesian_closed_composed_map.
      + exact cartesian_closed_pullback.
      + exact cartesian_closed_pullback_map.
  Defined.

End CartesianClosed.
