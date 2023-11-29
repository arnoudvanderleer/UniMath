Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.LeftKanExtension.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.AlgebraicTheories.FundamentalTheorem.SurjectivePrecomposition.

Local Open Scope cat.

Section AdjointEquivalenceFromComp.

  Context {C C' C'' : category}.
  Context (F : C ⟶ C').
  Context (F' : C' ⟶ C'').
  Context (H : fully_faithful F').

  Context (D : category).
  Context (HD1 : Colims D).
  Context (HD2 : is_univalent D).

  Context (Hequiv : adj_equivalence_of_cats (pre_comp_functor (C := D) F' ∙ pre_comp_functor F)).

  Let Hes := functor_from_equivalence_is_essentially_surjective _ _ _ Hequiv.
  Let Hff := fully_faithful_from_equivalence _ _ _ Hequiv.

  Definition lan_after_pre_comp_iso
    (P : [C'', D])
    : z_iso (lan_functor HD1 F' (pre_comp_functor F' P)) P.
  Proof.
    refine (iso_from_fully_faithful_reflection Hff _).
    apply (functor_on_z_iso (pre_comp_functor F)).
    exact (pr2 (pre_comp_split_essentially_surjective F' H D HD1 (pre_comp_functor F' P))).
  Defined.

  Definition precomp_mor_weq
    (P P' : [C'', D])
    : [C'', D] ⟦ P, P' ⟧ ≃ [C', D] ⟦ pre_comp_functor F' P, pre_comp_functor F' P' ⟧.
  Proof.
    refine (weqcomp _ (adjunction_hom_weq (lan_precomposition_are_adjoints HD1 F') _ _)).
    refine (make_weq _ (pr2 (z_iso_to_iso _) _)).
    apply lan_after_pre_comp_iso.
  Defined.

  Definition precomp_fully_faithful
    : fully_faithful (pre_comp_functor (C := D) F').
  Proof.
    intros P P'.
    use isweqhomot.
    - apply precomp_mor_weq.
    - intro f.
      refine (φ_adj_natural_postcomp _ _ _ _ _ _ @ _).
      refine (_ @ id_left _).
      apply (maponpaths (λ x, x · _)).
      refine (_ @ triangle_id_right_ad (lan_precomposition_are_adjoints HD1 F') P).
      apply (maponpaths (λ x, _ · # (pre_comp_functor F') x)).
      apply invmap_eq.
      apply (maponpaths (pre_whisker_in_funcat _ _ _ _)).
      apply nat_trans_eq_alt.
      intro c.
      apply colim_mor_eq.
      intro v.
      refine (colimArrowCommutes (lan_colim _ _ _ _) _ _ _ @ !_).
      refine (colim_mor_commute (lan_colim _ _ _ _) _ _ _ _ @ !_).
      apply (maponpaths #(P : C'' ⟶ D)).
      apply (homotweqinvweq (weq_from_fully_faithful _ _ _)).
    - apply weqproperty.
  Defined.

  Definition adjoint_equivalence_1_from_comp
    : adj_equivalence_of_cats (pre_comp_functor (C := D) F' ).
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_functor_category.
      apply HD2.
    - apply precomp_fully_faithful.
    - intro P.
      apply hinhpr.
      exact (pre_comp_split_essentially_surjective F' H D HD1 P).
  Defined.

End AdjointEquivalenceFromComp.
