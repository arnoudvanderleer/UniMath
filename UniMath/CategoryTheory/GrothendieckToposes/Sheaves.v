Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.yoneda.

Require Import UniMath.CategoryTheory.GrothendieckTopos.Sieves.
Require Import UniMath.CategoryTheory.GrothendieckTopos.GrothendieckTopology.

Local Open Scope cat.

Section Sheaves.

  Context (C : category).
  Context (GT : Grothendieck_topology C).

  Section SheafProperties.

    Context (P : PreShv C).

    (** This is a formalization of the definition on page 122 *)
    Definition is_sheaf : UU :=
      ∏ (c : C)
        (S : Grothendieck_topology_sieve_selection GT c)
        (τ : sieve_functor (pr1carrier _ S) ⟹ (P : _ ⟶ _)),
      ∃! (η : yoneda_objects _ c ⟹ (P : _ ⟶ _)),
        nat_trans_comp _ _ _ (sieve_nat_trans (pr1carrier _ S)) η = τ.

    Lemma isaprop_is_sheaf : isaprop is_sheaf.
    Proof.
      apply impred_isaprop; intros t.
      apply impred_isaprop; intros S.
      apply impred_isaprop; intros τ.
      apply isapropiscontr.
    Qed.

    Section EqualizerSheafProperty.

      Context (c : C).
      Context (S : Grothendieck_topology_sieve_selection GT c).

      Definition is_sheaf_equalizer_domain
        : hSet.
      Proof.
        use (ProductObject _ _ (ProductsHSET _ _)).
        - exact (∑ (V : C), (sieve_functor (pr1carrier _ S) V : hSet)).
        - intro Vf.
          apply P.
          exact (pr1 Vf).
      Defined.

      Definition is_sheaf_equalizer_codomain
        : hSet.
      Proof.
        use (ProductObject _ _ (ProductsHSET _ _)).
        - exact (∑ (V W : C), (sieve_functor (pr1carrier _ S) V : hSet) × C⟦W, V⟧).
        - intro VWfg.
          apply P.
          exact (pr12 VWfg).
      Defined.

      Definition is_sheaf_equalizer_arrow1
        : is_sheaf_equalizer_domain → is_sheaf_equalizer_codomain.
      Proof.
        apply (ProductArrow _ SET).
        intro VWfg.
        refine (ProductPr _ _ _ (_ ,, _)).
        exact (# (sieve_functor _) (pr222 VWfg) (pr122 VWfg)).
      Defined.

      Definition is_sheaf_equalizer_arrow2
        : is_sheaf_equalizer_domain → is_sheaf_equalizer_codomain.
      Proof.
        apply (ProductArrow _ SET).
        intro VWfg.
        refine (ProductPr _ _ _ (pr1 VWfg ,, pr122 VWfg) · _).
        apply (# (P : _ ⟶ _)).
        exact (pr222 VWfg).
      Defined.

      Definition is_sheaf_equalizer_inducer_arrow
        : ((P : _ ⟶ _) c : hSet) → is_sheaf_equalizer_domain.
      Proof.
        apply (ProductArrow _ SET).
        intro Vf.
        apply (# (P : _ ⟶ _)).
        exact (sieve_nat_trans (pr1carrier _ S) _ (pr2 Vf)).
      Defined.

      Lemma is_sheaf_equalizer_inducer_arrow_commutes
        : (is_sheaf_equalizer_arrow1 ∘ is_sheaf_equalizer_inducer_arrow =
          is_sheaf_equalizer_arrow2 ∘ is_sheaf_equalizer_inducer_arrow)%functions.
      Proof.
        apply (ProductArrow_eq _ SET).
        intro VWfg.
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ _).
        refine (ProductPrCommutes _ _ _ _ _ _ (pr12 VWfg ,, _) @ !_).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ _).
        refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (ProductPrCommutes _ _ _ _ _ _ _) @ !_).
        refine (_ @ functor_comp _ _ _).
        apply maponpaths.
        exact (eqtohomot (nat_trans_ax (sieve_nat_trans (pr1carrier _ S)) _ _ (pr222 VWfg)) (pr122 VWfg)).
      Qed.

      Definition is_sheaf_equalizer_induced_arrow
        : SET⟦(P : _ ⟶ _) c, Equalizers_in_HSET _ _ is_sheaf_equalizer_arrow1 is_sheaf_equalizer_arrow2⟧
        := EqualizerIn (C := SET) _ _ _ is_sheaf_equalizer_inducer_arrow_commutes.

    End EqualizerSheafProperty.

    Definition is_sheaf' : UU
      := ∏ c S,
        is_z_isomorphism (is_sheaf_equalizer_induced_arrow c S).

    Lemma isaprop_is_sheaf'
      : isaprop is_sheaf'.
    Proof.
      do 2 (apply impred_isaprop; intro).
      apply isaprop_is_z_isomorphism.
    Qed.

    Definition locality
      : UU
      := ∏ (c : C)
          (S : Grothendieck_topology_sieve_selection GT c)
          (f g : ((P : _ ⟶ _) c : hSet)),
          (∏
            (h : sieve_selected_morphism (pr1carrier _ S)),
              # (P : _ ⟶ _) h f
            = # (P : _ ⟶ _) h g)
          → f = g.

    Lemma isaprop_locality
      : isaprop locality.
    Proof.
      repeat (apply impred_isaprop; intro).
      apply setproperty.
    Qed.

    Definition glueing
      : UU
      := ∏
        (c : C)
        (S : Grothendieck_topology_sieve_selection GT c)
        (x : ∏
          (f : sieve_selected_morphism (pr1carrier _ S)),
          ((P : _ ⟶ _) (sieve_selected_morphism_domain f) : hSet)),
        (∏ (f : sieve_selected_morphism (pr1carrier _ S))
          (W : C)
          (g : C⟦W, sieve_selected_morphism_domain f⟧),
          x (sieve_selected_morphism_compose f g)
          = # (P : _ ⟶ _) g (x f))
        → ∑ (z : (P : _ ⟶ _) c : hSet),
            ∏ (f : sieve_selected_morphism (pr1carrier _ S)),
              # (P : _ ⟶ _) f z
              = x f.

    Lemma isaprop_glueing
      (H : locality)
      : isaprop glueing.
    Proof.
      apply impred_isaprop.
      intro c.
      apply impred_isaprop.
      intro S.
      apply impred_isaprop.
      intro x.
      apply impred_isaprop.
      intro Hx.
      apply invproofirrelevance.
      intros z z'.
      apply subtypePath.
      {
        intro.
        repeat (apply impred_isaprop; intro).
        apply setproperty.
      }
      apply (H c S).
      intro f.
      exact (pr2 z _ @ !pr2 z' _).
    Qed.

    Definition is_sheaf''
      : UU
      := locality × glueing.

    Lemma isaprop_is_sheaf''
      : isaprop is_sheaf''.
    Proof.
      use (isaprop_total2 (make_hProp _ _) (λ H, make_hProp _ _)).
      - exact isaprop_locality.
      - exact (isaprop_glueing H).
    Qed.

    Lemma is_sheaf_to_is_sheaf'
      : is_sheaf → is_sheaf'.
    Proof.
      intros H c S.
      specialize (H c S).
      use (make_is_z_isomorphism _ _ (make_dirprod _ _)).
      - intro VfH.
        refine (pr11 (H _) _ (identity c)).
        use make_nat_trans.
        * intros d f.
          refine (pr1 VfH (d ,, f)).
        * abstract (
            intros d d' f;
            apply funextfun;
            intro g;
            exact (eqtohomot (pr2 VfH) (_ ,, _ ,, _ ,, _))
          ).
      - apply funextfun.
        intro x.
        use (!eqtohomot (nat_trans_eq_pointwise (path_to_ctr _ _ (H _) (make_nat_trans _ _ _ _) _) _) _ @ _).
        + intros d g.
          refine (# (P : _ ⟶ _) g x).
        + intros d d' g.
          apply funextfun.
          intro g'.
          exact (eqtohomot (functor_comp (P : _ ⟶ _) g' g) x).
        + apply nat_trans_eq_alt.
          reflexivity.
        + exact (eqtohomot (functor_id P c) x).
      - apply funextfun.
        intro w.
        apply subtypePath.
        {
          intro.
          apply impred_isaset.
          intro.
          apply setproperty.
        }
        apply funextsec.
        intro Vf.
        refine (!eqtohomot (nat_trans_ax (pr11 (H _)) _ _ _) _ @ _).
        refine (_ @ eqtohomot (nat_trans_eq_pointwise (pr21 (H (make_nat_trans _ _ _ (is_sheaf_to_is_sheaf'_subproof c S w)))) (pr1 Vf)) (pr2 Vf)).
        apply (maponpaths (pr11 (H _) _)).
        apply id_right.
    Qed.

    Lemma is_sheaf'_to_is_sheaf''
      : is_sheaf' → is_sheaf''.
    Proof.
      intro H.
      split;
        intros c S;
        specialize (H c S);
        pose (i := make_z_iso' _ H).
      - intros f g Hfg.
        refine (!_ @ eqtohomot (z_iso_inv_after_z_iso i) g).
        refine (!_ @ eqtohomot (z_iso_inv_after_z_iso i) f).
        apply (maponpaths (inv_from_z_iso i)).
        apply subtypePath.
        {
          intro.
          apply propproperty.
        }
        apply funextsec.
        intro Vf.
        apply Hfg.
      - intros f Hf.
        use tpair.
        + refine (inv_from_z_iso i _).
          exists (λ Vf, f Vf).
          apply funextsec.
          intro VWfg.
          apply (Hf (_ ,, _)).
        + intros g.
          refine (maponpaths (λ x, pr1 (x _) _) (z_iso_after_z_iso_inv i)).
    Qed.

  End SheafProperties.

  (** The category of sheaves is the full subcategory of presheaves consisting of the presheaves
      which satisfy the is_sheaf proposition. *)
  Definition hsubtype_obs_is_sheaf
    (P : PreShv C)
    : hProp
    := make_hProp _ (isaprop_is_sheaf P).

  Definition sheaf_cat :
    sub_precategories (PreShv C) :=
    full_sub_precategory hsubtype_obs_is_sheaf.

End Sheaves.
