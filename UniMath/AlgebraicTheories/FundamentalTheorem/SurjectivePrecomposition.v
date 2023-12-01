Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.LeftKanExtension.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

Section PrecompositionEssentiallySurjective.

  Context {C C' : category}.
  Context (F : C ⟶ C').
  Context (H : fully_faithful F).

  Context (D : category).
  Context (HD : Colims D).

  Let Fweq := weq_from_fully_faithful H.

  Section Iso.

    Context (P : [C, D]).

    Definition pre_comp_z_iso_mor_data
      : nat_trans_data (pre_comp_functor F (lan_functor HD F P) : C ⟶ D) (P : C ⟶ D).
    Proof.
      intro c.
      use (colimArrow _ _ (make_cocone _ _)).
      - intros v.
        exact (#(P : _ ⟶ _) (invmap (Fweq _ _) (pr2 v))).
      - abstract (
          intros u v e;
          refine (!functor_comp P _ _ @ _);
          apply (maponpaths (# (P : _ ⟶ _)));
          refine (!invmap_eq _ _ _ (!_));
          refine (functor_comp _ _ _ @ _);
          refine (maponpaths _ (homotweqinvweq (Fweq _ _) _) @ _);
          exact (!pr2 e @ id_right _)
        ).
    Defined.

    Lemma pre_comp_z_iso_mor_is_nat_trans
      : is_nat_trans _ _ pre_comp_z_iso_mor_data.
    Proof.
      intros c c' f.
      apply colim_mor_eq.
      intro v.
      do 2 refine (assoc _ _ _ @ !_).
      refine (maponpaths (λ x, x · _) (lan_mor_colimIn _ _ _ _ _ (pr2 v) _) @ !_).
      refine (maponpaths (λ x, x · _) (colimArrowCommutes _ _ _ v) @ !_).
      refine (colimArrowCommutes (lan_colim _ _ _ _) _ _ ((pr11 v ,, _) ,, pr2 v · #F f) @ _).
      refine (_ @ functor_comp P _ _).
      apply (maponpaths #(P : _ ⟶ _)).
      apply invmap_eq.
      refine (_ @ !functor_comp F _ _).
      exact (!maponpaths (λ x, x · _) (homotweqinvweq (Fweq _ _) _)).
    Qed.

    Definition pre_comp_z_iso_mor
      : nat_trans (pre_comp_functor F (lan_functor HD F P) : C ⟶ D) (P : C ⟶ D)
      := make_nat_trans _ _ _ pre_comp_z_iso_mor_is_nat_trans.

    Lemma pre_comp_z_iso_is_iso
      : is_inverse_in_precat (C := [C, D]) pre_comp_z_iso_mor (unit_from_right_adjoint (is_right_adjoint_precomposition HD F) P).
    Proof.
      split.
      - apply nat_trans_eq_alt.
        intro c.
        apply colim_mor_eq.
        intro v.
        refine (assoc _ _ _ @ _).
        match goal with
        | [ |- _ · ?a = _ ] => refine (maponpaths (λ x, x · a) (colimArrowCommutes _ _ _ _) @ _)
        end.
        use (colimInCommutes _ v ((c ,, tt) ,, identity (F c)) ((make_dirprod _ _) ,, _) @ _).
        + now induction (pr21 v).
        + refine (maponpaths (λ x, x · _) _).
          exact (!homotweqinvweq (Fweq _ _) _).
        + exact (!id_right _).
      - apply nat_trans_eq_alt.
        intro c.
        refine (_ @ functor_id P _).
        refine (colimArrowCommutes (lan_colim HD F P (F c)) _ _ ((c ,, tt) ,, identity (F c)) @ _).
        refine (maponpaths (λ f, # (P : _ ⟶ _) f) (_ : invmap (Fweq c c) _ = _)).
        apply invmap_eq.
        exact (!functor_id F _).
    Qed.

    Definition pre_comp_after_lan_iso
      : z_iso (pre_comp_functor F (lan_functor HD F P)) P
      := make_z_iso _ _ pre_comp_z_iso_is_iso.

  End Iso.

  Definition pre_comp_split_essentially_surjective
    : split_essentially_surjective (pre_comp_functor F)
    := λ c, lan_functor HD F c ,, pre_comp_after_lan_iso c.

End PrecompositionEssentiallySurjective.
