Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section StandardIsos.

  Definition associator
    {C1 C2 C3 C4 : category}
    (F1 : C1 ⟶ C2)
    (F2 : C2 ⟶ C3)
    (F3 : C3 ⟶ C4)
    : z_iso (C := [_, _]) ((F1 ∙ F2) ∙ F3) (F1 ∙ (F2 ∙ F3)).
  Proof.
    use make_z_iso.
    - exact (nat_trans_id _).
    - exact (nat_trans_id _).
    - abstract (
        use make_is_inverse_in_precat;
        apply nat_trans_eq_alt;
        intro;
        apply id_left
      ).
  Defined.

  Definition right_unitor
    {C1 C2 : category}
    (F1 : C1 ⟶ C2)
    : z_iso (C := [_, _]) (F1 ∙ functor_identity _) F1.
  Proof.
    use make_z_iso.
    - exact (nat_trans_id _).
    - exact (nat_trans_id _).
    - abstract (
        use make_is_inverse_in_precat;
        apply nat_trans_eq_alt;
        intro;
        apply id_left
      ).
  Defined.

  Definition left_unitor
    {C1 C2 : category}
    (F1 : C1 ⟶ C2)
    : z_iso (C := [_, _]) (functor_identity _ ∙ F1) F1.
  Proof.
    use make_z_iso.
    - exact (nat_trans_id _).
    - exact (nat_trans_id _).
    - abstract (
        use make_is_inverse_in_precat;
        apply nat_trans_eq_alt;
        intro;
        apply id_left
      ).
  Defined.

End StandardIsos.

Section PostcompEquiv.

  Context {C D E : category}.

  Section AdjunctionData.

    Context (F : adjunction_data D E).

    Definition postcomp_adjunction_data_functor
      : [C, D] ⟶ [C, E]
      := post_comp_functor (left_functor F).

    Definition postcomp_adjunction_data_inverse
      : [C, E] ⟶ [C, D]
      := post_comp_functor (right_functor F).

    Definition postcomp_adjunction_data_unit_data
      : nat_trans_data
        (functor_identity [C, D])
        (postcomp_adjunction_data_functor ∙ postcomp_adjunction_data_inverse)
      := λ G,
          nat_trans_comp _ _ _ (z_iso_inv (right_unitor _) : _ --> _)
          (nat_trans_comp _ _ _ (pre_whisker _ (adjunit F))
          (z_iso_inv (associator _ _ _) : _ --> _)).

    Lemma postcomp_adjunction_data_unit_is_nat_trans
      : is_nat_trans _ _ postcomp_adjunction_data_unit_data.
    Proof.
      intros X Y f.
      apply nat_trans_eq_alt.
      intro Z.
      refine (maponpaths _ (id_left _) @ _).
      refine (maponpaths _ (id_right _) @ !_).
      refine (maponpaths (λ x, x · _) (id_left _) @ _).
      refine (maponpaths (λ x, x · _) (id_right _) @ !_).
      exact (nat_trans_ax (adjunit F) _ _ ((f : _ ⟹ _) Z)).
    Qed.

    Definition postcomp_adjunction_data_unit
      : functor_identity [C, D] ⟹ postcomp_adjunction_data_functor ∙ postcomp_adjunction_data_inverse
      := make_nat_trans _ _ _ postcomp_adjunction_data_unit_is_nat_trans.

    Definition postcomp_adjunction_data_counit_data
      : nat_trans_data
        (postcomp_adjunction_data_inverse ∙ postcomp_adjunction_data_functor)
        (functor_identity [C, E])
      := λ G,
          nat_trans_comp _ _ _ (associator _ _ _ : _ --> _)
          (nat_trans_comp _ _ _ (pre_whisker _ (adjcounit F))
          (right_unitor _ : _ --> _)).

    Lemma postcomp_adjunction_data_counit_is_nat_trans
      : is_nat_trans _ _ postcomp_adjunction_data_counit_data.
    Proof.
      intros X Y f.
      apply nat_trans_eq_alt.
      intro Z.
      refine (maponpaths _ (id_left _) @ _).
      refine (maponpaths _ (id_right _) @ !_).
      refine (maponpaths (λ x, x · _) (id_left _) @ _).
      refine (maponpaths (λ x, x · _) (id_right _) @ !_).
      exact (nat_trans_ax (adjcounit F) _ _ ((f : _ ⟹ _) Z)).
    Qed.

    Definition postcomp_adjunction_data_counit
      : postcomp_adjunction_data_inverse ∙ postcomp_adjunction_data_functor ⟹ functor_identity [C, E]
      := make_nat_trans _ _ _ postcomp_adjunction_data_counit_is_nat_trans.

    Definition postcomp_adjunction_data
      : adjunction_data [C, D] [C, E]
      := make_adjunction_data
          postcomp_adjunction_data_functor
          postcomp_adjunction_data_inverse
          postcomp_adjunction_data_unit
          postcomp_adjunction_data_counit.

  End AdjunctionData.

  Section Adjunction.

    Lemma postcomp_form_adjunction
      (F : adjunction D E)
      : form_adjunction' (postcomp_adjunction_data F).
    Proof.
      split;
        intro G;
        apply nat_trans_eq_alt;
        intro X.
      - refine (maponpaths _ (id_left _) @ _).
        refine (maponpaths _ (id_right _) @ _).
        refine (maponpaths (λ x, # (left_functor F) x · _) (id_left _) @ _).
        refine (maponpaths (λ x, # (left_functor F) x · _) (id_right _) @ _).
        apply (triangle_1_statement_from_adjunction F).
      - refine (maponpaths (λ x, _ · # (right_functor F) x) (id_left _) @ _).
        refine (maponpaths (λ x, _ · # (right_functor F) x) (id_right _) @ _).
        refine (maponpaths (λ x, x · _) (id_left _) @ _).
        refine (maponpaths (λ x, x · _) (id_right _) @ _).
        apply (triangle_2_statement_from_adjunction F).
    Qed.

    Definition postcomp_adjunction
      (F : adjunction D E)
      : adjunction [C, D] [C, E]
      := make_adjunction _ (postcomp_form_adjunction F).

  End Adjunction.

  Section Equivalence.

    Definition postcomp_forms_equivalence
      (F : equivalence_of_cats D E)
      : forms_equivalence (postcomp_adjunction_data F).
    Proof.
      split;
        intro G;
        apply nat_trafo_z_iso_if_pointwise_z_iso;
        intro X.
      - repeat apply is_z_isomorphism_comp.
        + apply is_z_isomorphism_identity.
        + exact (pr2 (adjunitiso F _)).
        + apply is_z_isomorphism_identity.
      - repeat apply is_z_isomorphism_comp.
        + apply is_z_isomorphism_identity.
        + exact (pr2 (adjcounitiso F _)).
        + apply is_z_isomorphism_identity.
    Defined.

    Definition postcomp_equivalence
      (F : equivalence_of_cats D E)
      : equivalence_of_cats [C, D] [C, E]
      := make_equivalence_of_cats _ (postcomp_forms_equivalence F).

  End Equivalence.

  Definition postcomp_equiv
      (F : adj_equiv D E)
    : adj_equiv [C, D] [C, E]
    := _ ,,
        make_adj_equivalence_of_cats _ _ _ _
          (postcomp_form_adjunction F)
          (postcomp_forms_equivalence F).

End PostcompEquiv.

Section PrecompEquiv.

  Context {C D E : category}.

  Section AdjunctionData.

    Context (F : adjunction_data C D).

    Definition precomp_adjunction_data_functor
      : [C, E] ⟶ [D, E]
      := pre_comp_functor (right_functor F).

    Definition precomp_adjunction_data_inverse
      : [D, E] ⟶ [C, E]
      := pre_comp_functor (left_functor F).

    Definition precomp_adjunction_data_unit_data
      : nat_trans_data
        (functor_identity [C, E])
        (precomp_adjunction_data_functor ∙ precomp_adjunction_data_inverse)
      := λ G,
      nat_trans_comp _ _ _ (z_iso_inv (left_unitor _) : _ --> _)
      (nat_trans_comp _ _ _ (post_whisker (adjunit F) _)
      (associator _ _ _ : _ --> _)).

    Lemma precomp_adjunction_data_unit_is_nat_trans
      : is_nat_trans _ _ precomp_adjunction_data_unit_data.
    Proof.
      intros G G' f.
      apply nat_trans_eq_alt.
      intro Z.
      refine (maponpaths _ (id_left _) @ _).
      refine (maponpaths _ (id_right _) @ !_).
      refine (maponpaths (λ x, x · _) (id_left _) @ _).
      refine (maponpaths (λ x, x · _) (id_right _) @ _).
      apply (nat_trans_ax f).
    Qed.

    Definition precomp_adjunction_data_unit
      : functor_identity [C, E] ⟹ precomp_adjunction_data_functor ∙ precomp_adjunction_data_inverse
      := make_nat_trans _ _ _ precomp_adjunction_data_unit_is_nat_trans.

    Definition precomp_adjunction_data_counit_data
      : nat_trans_data
        (precomp_adjunction_data_inverse ∙ precomp_adjunction_data_functor)
        (functor_identity [D, E])
      := λ G,
          nat_trans_comp _ _ _ (z_iso_inv (associator _ _ _) : _ --> _)
          (nat_trans_comp _ _ _ (post_whisker (adjcounit F) _)
          (left_unitor _ : _ --> _)).

    Lemma precomp_adjunction_data_counit_is_nat_trans
      : is_nat_trans _ _ precomp_adjunction_data_counit_data.
    Proof.
      intros G G' f.
      apply nat_trans_eq_alt.
      intro Z.
      refine (maponpaths _ (id_left _) @ _).
      refine (maponpaths _ (id_right _) @ !_).
      refine (maponpaths (λ x, x · _) (id_left _) @ _).
      refine (maponpaths (λ x, x · _) (id_right _) @ _).
      apply (nat_trans_ax f).
    Qed.

    Definition precomp_adjunction_data_counit
      : precomp_adjunction_data_inverse ∙ precomp_adjunction_data_functor ⟹ functor_identity [D, E]
      := make_nat_trans _ _ _ precomp_adjunction_data_counit_is_nat_trans.

    Definition precomp_adjunction_data
      : adjunction_data [C, E] [D, E]
      := make_adjunction_data
          precomp_adjunction_data_functor
          precomp_adjunction_data_inverse
          precomp_adjunction_data_unit
          precomp_adjunction_data_counit.

  End AdjunctionData.

  Section Adjunction.

    Lemma precomp_form_adjunction
      (F : adjunction C D)
      : form_adjunction' (precomp_adjunction_data F).
    Proof.
      split;
        intro G;
        apply nat_trans_eq_alt;
        intro X;
        refine (maponpaths _ (id_left _) @ _);
        refine (maponpaths _ (id_right _) @ _);
        refine (maponpaths (λ x, x · _) (id_left _) @ _);
        refine (maponpaths (λ x, x · _) (id_right _) @ _);
        refine (!_ @ functor_id G _);
        refine (!_ @ functor_comp G _ _);
        apply maponpaths.
      - apply (triangle_2_statement_from_adjunction F).
      - apply (triangle_1_statement_from_adjunction F).
    Qed.

    Definition precomp_adjunction
      (F : adjunction C D)
      : adjunction [C, E] [D, E]
      := make_adjunction _ (precomp_form_adjunction F).

  End Adjunction.

  Section Equivalence.

    Definition precomp_forms_equivalence
      (F : equivalence_of_cats C D)
      : forms_equivalence (precomp_adjunction_data F).
    Proof.
      split;
        intro G;
        apply nat_trafo_z_iso_if_pointwise_z_iso;
        intro X.
      - repeat apply is_z_isomorphism_comp.
        + apply is_z_isomorphism_identity.
        + apply functor_on_is_z_isomorphism.
          exact (pr2 (adjunitiso F _)).
        + apply is_z_isomorphism_identity.
      - repeat apply is_z_isomorphism_comp.
        + apply is_z_isomorphism_identity.
        + apply (functor_on_is_z_isomorphism G).
          exact (pr2 (adjcounitiso F _)).
        + apply is_z_isomorphism_identity.
    Defined.

    Definition precomp_equivalence
      (F : equivalence_of_cats C D)
      : equivalence_of_cats [C, E] [D, E]
      := make_equivalence_of_cats _ (precomp_forms_equivalence F).

  End Equivalence.

  Definition precomp_equiv
      (F : adj_equiv C D)
    : adj_equiv [C, E] [D, E]
    := _ ,,
        make_adj_equivalence_of_cats _ _ _ _
          (precomp_form_adjunction F)
          (precomp_forms_equivalence F).

End PrecompEquiv.

Section EquivalenceOnIso.

  Context {C D : category}.
  Context (F : adj_equiv C D).
  Context {X : C}.
  Context {Y : D}.
  Context (f : z_iso (F X) Y).

  Definition adjoint_equivalence_on_iso_mor
    : X --> adj_equiv_inv F Y
    := φ_adj F f.

  Definition adjoint_equivalence_on_iso_inv
    : adj_equiv_inv F Y --> X
    := φ_adj_inv (adj_equiv_inv F) (z_iso_inv f).

  Lemma adjoint_equivalence_on_iso_is_inverse
    : is_inverse_in_precat
      adjoint_equivalence_on_iso_mor
      adjoint_equivalence_on_iso_inv.
  Proof.
    split;
      refine (assoc _ _ _ @ _);
      refine (maponpaths (λ x, x · _) (assoc' _ _ _) @ _).
    - refine (!maponpaths (λ x, _ · x · _) (functor_comp _ _ _) @ _).
      refine (maponpaths (λ x, _ · # _ x · _) (z_iso_inv_after_z_iso f) @ _).
      refine (maponpaths (λ x, _ · x · _) (functor_id _ _) @ _).
      refine (maponpaths (λ x, x · _) (id_right _) @ _).
      exact (z_iso_inv_after_z_iso (adjunitiso F _)).
    - refine (maponpaths (λ x, _ · x · _) (z_iso_after_z_iso_inv (adjunitiso F _)) @ _).
      refine (maponpaths (λ x, x · _) (id_right _) @ _).
      refine (!functor_comp (adj_equiv_inv F) _ _ @ _).
      refine (maponpaths _ (z_iso_after_z_iso_inv f) @ _).
      exact (functor_id _ _).
  Qed.

  Definition adjoint_equivalence_on_iso
    : z_iso X (adj_equiv_inv F Y)
    := make_z_iso _ _
        adjoint_equivalence_on_iso_is_inverse.

End EquivalenceOnIso.

Definition adjoint_equivalence_iso_weq
  {C D : category}
  (F : adj_equiv C D)
  {X : C} {Y : D}
  : z_iso (F X) Y ≃ z_iso X (adj_equiv_inv F Y).
Proof.
  use weq_iso.
  - exact (adjoint_equivalence_on_iso F).
  - intro f.
    exact (z_iso_inv (adjoint_equivalence_on_iso (adj_equiv_inv F) (z_iso_inv f))).
  - abstract (
      intro f;
      apply z_iso_eq;
      exact (homotinvweqweq (adjunction_hom_weq F _ _) f)
    ).
  - abstract (
      intro f;
      apply z_iso_eq;
      exact (homotweqinvweq (adjunction_hom_weq F _ _) f)
    ).
Defined.
