(* Defines the category of presheaves for an algebraic theory and shows that it is univalent and has all limits *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.Presheaves.

Local Open Scope algebraic_theories.
Local Open Scope cat.
Local Open Scope mor_disp.

Definition creates_limits_presheaf_base_disp
  : creates_limits (disp_cartesian algebraic_theory_cat base_functor_category).
Proof.
  intros J d L.
  use creates_limits_disp_cartesian.
  - apply limits_base_functor_category.
Defined.

Definition limits_presheaf_base
  : Lims (cartesian algebraic_theory_cat base_functor_category).
Proof.
  intros J d.
  use total_limit.
  - apply limits_algebraic_theory_cat.
  - apply creates_limits_presheaf_base_disp.
Defined.

(* The displayed category of presheaf data *)
Definition presheaf_data_disp_cat
  : disp_cat (cartesian algebraic_theory_cat base_functor_category).
Proof.
  use disp_struct.
  - intro X.
    pose (T := pr1 X : algebraic_theory).
    pose (A := pr2 X : finite_set_skeleton_category ⟶ HSET).
    exact (∏ m n, (A m : hSet) → (stn m → (T n : hSet)) → (A n : hSet)).
  - intros X X' action action' Y.
    pose (A := pr2 X : finite_set_skeleton_category ⟶ HSET).
    pose (A' := pr2 X' : finite_set_skeleton_category ⟶ HSET).
    pose (F := pr1 Y : algebraic_theory_morphism _ _).
    pose (G := pr2 Y : nat_trans A A').
    exact (∏ m n a f, G n (action m n a f) = action' m n (G m a) (λ i, F n (f i))).
  - abstract (
      intros;
      do 4 (apply impred_isaprop; intro);
      apply setproperty
    ).
  - abstract (
      intros X action n m f a;
      now refine (maponpaths (λ x, _ (x _) _ _) (transportf_const _ _) @ _ @ !maponpaths (λ x, _ (_ (x _) _ _) _) (transportf_const _ _))
    ).
  - abstract (
      intros X X' X'' action action' action'' y y' Gcommutes G'commutes m n a f;
      refine (maponpaths (λ x, _ (x _) _ _) (transportf_const _ _) @ _ @ !maponpaths (λ x, _ (_ (x _) _ _) _) (transportf_const _ _));
      exact (maponpaths _ (Gcommutes _ _ _ _) @ (G'commutes _ _ _ _))
    ).
Defined.

Lemma is_univalent_disp_presheaf_data_disp_cat
  : is_univalent_disp presheaf_data_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros TA action action'.
  use isweq_iso.
  - intro F.
    do 4 (apply funextsec; intro).
    now refine (!maponpaths (λ x, _ (x _) _ _) (transportf_const _ _) @ pr1 F _ _ _ _ @ maponpaths (λ x, _ (_ (x _) _ _) _) (transportf_const _ _) @ _).
  - intro.
    do 4 (apply impred_isaset; intro).
    apply setproperty.
  - intro.
    apply z_iso_eq.
    do 4 (apply impred_isaprop; intro).
    apply setproperty.
Qed.

Section Limits.
  Context (D := presheaf_data_disp_cat).
  Context {J : graph}.
  Context (d : diagram J (total_category D)).
  Context (L := limits_presheaf_base J (mapdiagram (pr1_category _) d)).

  Definition tip_presheaf_data_disp_cat
    : D (lim L).
  Proof.
    intros m n a f.
    use tpair.
    - intro u.
      exact (pr2 (dob d u) m n (pr1 a u) (λ i, pr1 (f i) u)).
    - abstract (
        intros u v e;
        refine (pr2 (dmor d e) _ _ _ _ @ _);
        refine (maponpaths (λ x, _ x _) _ @ maponpaths _ _);
        [ exact (pr2 a u v e)
        | apply funextfun;
          intro;
          exact (pr2 (f _) u v e) ]
      ).
  Defined.

  Lemma cone_presheaf_data_disp_cat
    (j : vertex J)
    : tip_presheaf_data_disp_cat -->[limOut L j] pr2 (dob d j).
  Proof.
    easy.
  Qed.

  Lemma uniqueness_presheaf_data_disp_cat
    (d' : D (lim L))
    (cone_out : ∏ j, d' -->[limOut L j] (pr2 (dob d j)))
    : d' = tip_presheaf_data_disp_cat.
  Proof.
    do 4 (apply funextsec; intro).
    apply subtypePairEquality.
    - intro.
      repeat (apply impred_isaprop; intro).
      apply setproperty.
    - apply funextsec.
      intro.
      exact (cone_out _ _ _ _ _).
  Qed.

  Lemma is_limit_presheaf_data_disp_cat
    (d' : total_category D)
    (cone_out : ∏ u, d' --> (dob d u))
    (is_cone : ∏ u v e, cone_out u · (dmor d e) = cone_out v)
    : pr2 d' -->[limArrow L _ (make_cone (d := (mapdiagram (pr1_category D) d)) _ (λ u v e, (maponpaths pr1 (is_cone u v e))))] tip_presheaf_data_disp_cat.
  Proof.
    intros m n f g.
    apply subtypePairEquality.
    - intro.
      repeat (apply impred_isaprop; intro).
      exact (setproperty _ _ _).
    - apply funextsec.
      intro i.
      exact (pr2 (cone_out i) m n f g).
  Qed.

End Limits.

Definition creates_limits_presheaf_data_disp_cat
  {J}
  (d : diagram J _)
  : creates_limit presheaf_data_disp_cat d (limits_presheaf_base _ _)
  := creates_limit_disp_struct _
    (tip_presheaf_data_disp_cat _)
    (cone_presheaf_data_disp_cat _)
    (is_limit_presheaf_data_disp_cat _).

Definition creates_limits_unique_presheaf_data_disp_cat
  {J}
  (d : diagram J _)
  : creates_limit_unique presheaf_data_disp_cat d (limits_presheaf_base _ _)
  := creates_limit_unique_disp_struct _
    (creates_limits_presheaf_data_disp_cat _)
    (uniqueness_presheaf_data_disp_cat _).

Definition presheaf_data_cat
  : category
  := total_category presheaf_data_disp_cat.

Lemma is_univalent_presheaf_data_cat
  : is_univalent presheaf_data_cat.
Proof.
  apply is_univalent_total_category.
  - rewrite cartesian_is_binproduct.
    exact (is_univalent_category_binproduct is_univalent_algebraic_theory_cat (is_univalent_functor_category _ _ is_univalent_HSET)).
  - exact is_univalent_disp_presheaf_data_disp_cat.
Qed.

Definition limits_presheaf_data_cat
  : Lims presheaf_data_cat
  := λ _ _, (total_limit _ _ (creates_limits_presheaf_data_disp_cat _)).

(* The category of presheaves *)
Definition presheaf_full_disp_cat
  : disp_cat presheaf_data_cat
  := disp_full_sub presheaf_data_cat
    (λ X, is_presheaf (make_presheaf_data (pr21 X) (pr2 X))).

Lemma is_univalent_disp_presheaf_full_disp_cat
  : is_univalent_disp presheaf_full_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact (λ _, isaprop_is_presheaf _).
Qed.

Definition creates_limits_presheaf_full_disp_cat
  {J : graph}
  (d : diagram J _)
  : creates_limit presheaf_full_disp_cat d (limits_presheaf_data_cat _ _).
Proof.
  apply creates_limit_disp_full_sub.
  - intro.
    apply isaprop_is_presheaf.
  - use make_is_presheaf;
      repeat intro;
      (use total2_paths_f;
      [ apply funextsec;
        intro
      | do 3 (apply impred_isaprop; intro);
        apply setproperty ]).
    + apply (pr1 (pr2 (dob d _))).
    + apply (pr12 (pr2 (dob d _))).
    + apply (pr22 (pr2 (dob d _))).
Defined.

Definition creates_limits_unique_presheaf_full_disp_cat
  {J : graph}
  (d : diagram J _)
  : creates_limit_unique presheaf_full_disp_cat d (limits_presheaf_data_cat _ _)
  := creates_limit_unique_disp_full_sub
    (λ _, isaprop_is_presheaf _)
    _
    (creates_limits_presheaf_full_disp_cat _).

Definition presheaf_full_cat
  : category
  := total_category presheaf_full_disp_cat.

Lemma is_univalent_presheaf_full_cat
  : is_univalent presheaf_full_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_presheaf_data_cat.
  - exact is_univalent_disp_presheaf_full_disp_cat.
Qed.

Definition limits_presheaf_full_cat
  : Lims presheaf_full_cat
  := λ _ _, (total_limit _ _ (creates_limits_presheaf_full_disp_cat _)).

Definition presheaf_disp_cat
  : disp_cat algebraic_theory_cat
  := sigma_disp_cat (sigma_disp_cat presheaf_full_disp_cat).

Lemma is_univalent_disp_presheaf_disp_cat
  : is_univalent_disp presheaf_disp_cat.
Proof.
  repeat use is_univalent_sigma_disp.
  - apply is_univalent_reindex_disp_cat.
    apply is_univalent_disp_disp_over_unit.
    apply is_univalent_functor_category.
    exact is_univalent_HSET.
  - exact is_univalent_disp_presheaf_data_disp_cat.
  - exact is_univalent_disp_presheaf_full_disp_cat.
Qed.

Definition creates_limits_presheaf_disp_cat
  {J : graph}
  (d : diagram J _)
  : creates_limit presheaf_disp_cat d (limits_algebraic_theory_cat _ _).
Proof.
  repeat use creates_limits_sigma_disp_cat.
  - exact (creates_limits_presheaf_base_disp _ _ _).
  - exact (creates_limits_presheaf_data_disp_cat _).
  - exact (creates_limits_presheaf_full_disp_cat _).
Defined.

Lemma displayed_presheaf_morphism_eq
  {T T' : algebraic_theory}
  {F : algebraic_theory_morphism T T'}
  {P : presheaf T}
  {P' : presheaf T'}
  (G G' : (P : presheaf_disp_cat _) -->[F] P')
  (H : pr1 G = pr1 G')
  : G = G'.
Proof.
  apply (subtypePairEquality' H).
  use (isapropdirprod _ _ _ isapropunit).
  do 4 (apply impred_isaprop; intro).
  apply setproperty.
Qed.

Definition presheaf_cat
  (T : algebraic_theory)
  : category
  := fiber_category presheaf_disp_cat T.

Lemma is_univalent_presheaf_cat
  (T : algebraic_theory)
  : is_univalent (presheaf_cat T).
Proof.
  refine (is_univalent_fiber_cat _ _ _).
  exact is_univalent_disp_presheaf_disp_cat.
Qed.

Section fibration.

  Section lift.

    Context {c c' : algebraic_theory}.
    Context (f : algebraic_theory_morphism c' c).
    Context (d : presheaf c).

    Definition lifted_presheaf_data
      : presheaf_data c'.
    Proof.
      use make_presheaf_data.
      - exact (pr1 d).
      - intros m n s t.
        exact (action (P := d) s (λ i, f _ (t i))).
    Defined.

    Definition lifted_is_presheaf
      : is_presheaf lifted_presheaf_data.
    Proof.
      use make_is_presheaf.
      - do 6 intro.
        cbn.
        refine (presheaf_is_assoc d _ _ _ _ _ _ @ _).
        apply maponpaths.
        apply funextfun.
        intro.
        symmetry.
        apply algebraic_theory_morphism_preserves_composition.
      - do 2 intro.
        cbn.
        refine (_ @ presheaf_identity_projections d _ _).
        apply maponpaths.
        apply funextfun.
        intro.
        apply algebraic_theory_morphism_preserves_projections.
      - do 6 intro.
        apply presheaf_action_is_natural.
    Qed.

    Definition lifted_presheaf
      : presheaf c'
      := make_presheaf _ lifted_is_presheaf.

    Definition lifted_presheaf_morphism
      : (lifted_presheaf : presheaf_disp_cat c') -->[f] d.
    Proof.
      use tpair.
      - apply nat_trans_id.
      - refine (_ ,, tt).
        now do 4 intro.
    Defined.

    Section cartesian.

      Context {c'': algebraic_theory}.
      Context {g: algebraic_theory_morphism c'' c'}.
      Context {d'': presheaf c''}.
      Context (hh: (d'' : presheaf_disp_cat c'') -->[(g : algebraic_theory_cat ⟦ _, _ ⟧) · f] d).

      Definition induced_morphism
        : (d'' : presheaf_disp_cat c'') -->[ g] lifted_presheaf.
      Proof.
        use tpair.
        - exact (pr1 hh).
        - refine (_ ,, tt).
          do 4 intro.
          exact (pr12 hh _ _ _ _).
      Defined.

      Lemma induced_morphism_commutes
        : (induced_morphism ;; lifted_presheaf_morphism) = hh.
      Proof.
        apply displayed_presheaf_morphism_eq.
        refine (comp_disp_cartesian _ _ _ _ @ _).
        apply (nat_trans_eq (homset_property HSET)).
        intro.
        apply funextfun.
        now intro.
      Qed.

      Lemma induced_morphism_unique
        (t : ∑ induced_morphism', (induced_morphism' ;; lifted_presheaf_morphism) = hh)
        : t = induced_morphism ,, induced_morphism_commutes.
      Proof.
        apply subtypePairEquality'; [ | apply homsets_disp].
        apply displayed_presheaf_morphism_eq.
        refine (
          nat_trans_eq (homset_property HSET) _ _ _ _ _ @
          !comp_disp_cartesian _ _ (pr11 t) _ @
          maponpaths _ (pr2 t)
        ).
        intro.
        apply funextfun.
        now intro.
      Qed.

    End cartesian.

    Definition lifted_presheaf_morphism_is_cartesian
      : is_cartesian lifted_presheaf_morphism.
    Proof.
      intros c'' g d'' hh.
      use ((_ ,, _) ,, _).
      - exact (induced_morphism hh).
      - exact (induced_morphism_commutes hh).
      - exact (induced_morphism_unique hh).
    Defined.

  End lift.

  Definition presheaf_cleaving
    : cleaving presheaf_disp_cat
    := λ c c' f d,
      (lifted_presheaf f d) ,,
      (lifted_presheaf_morphism f d) ,,
      (lifted_presheaf_morphism_is_cartesian f d).

  Definition presheaf_fibration
    : fibration algebraic_theory_cat
    := presheaf_disp_cat ,, presheaf_cleaving.

End fibration.

Definition limits_presheaf_cat
  (T : algebraic_theory)
  : Lims (presheaf_cat T).
Proof.
  intros J d.
  use fiber_limit.
  - apply limits_algebraic_theory_cat.
  - apply creates_limits_presheaf_disp_cat.
  - apply presheaf_cleaving.
Defined.

Section Test.
  Goal ∏ T, ob (presheaf_cat T) = presheaf T.
    exact (λ _, idpath _).
  Qed.
  Goal ∏ (T : algebraic_theory) (P P' : presheaf T), (presheaf_cat T)⟦P, P'⟧ = presheaf_morphism P P'.
    intros.
    apply idpath.
  Qed.
End Test.