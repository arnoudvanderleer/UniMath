(**************************************************************************************************

  The category of relative monads

  Defines the category of relative monads, shows that it is univalent, defines the types of relative
  monads and relative monad morphisms, and shows that the category of relative monads on the
  embedding of finite_set_skeleton into HSET is equivalent to the category of algebraic theories.

  Contents
  1. The category and types of relative monads
  1.1. The category of relative monad data [relative_monad_data_cat]
  1.2. The type of relative monad data [relative_monad_data]
  1.3. The category of relative monads [relative_monad_cat]
  1.4. The type of relative monads [relative_monad]
  1.5. The type of relative monad morphisms [relative_monad_morphism]
  2. Univalence [is_univalent_relative_monad_cat]
  3. Precomposing relative monads with a functor [relative_monad_precomp_functor]
  4. The adjoint equivalence between relative monads on the embedding and algebraic theories
    [monad_theory_equivalence]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. The category and types of relative monads *)

Section RelativeMonad.

  Context {C D : category}.

  Definition η_ax
    (J : C ⟶ D)
    (T : C ⟶ D)
    : UU
    := J ⟹ T.

  Definition ext_ax
    (J : C ⟶ D)
    (T : C ⟶ D)
    (c d : C)
    (f : D⟦J c, T d⟧)
    : UU
    := D⟦T c, T d⟧.

  Let mor_η_ax'
    {J : C ⟶ D}
    {T T' : C ⟶ D}
    (F : T ⟹ T')
    (η : η_ax J T)
    (η' : η_ax J T')
    (c : C)
    : UU
    := ((η : _ ⟹ _) c) · F c = ((η' : _ ⟹ _) c).

  Let mor_ext_ax'
    {J : C ⟶ D}
    {T T' : C ⟶ D}
    (F : T ⟹ T')
    (ext : ∏ c d f, ext_ax J T c d f)
    (ext' : ∏ c d f, ext_ax J T' c d f)
    (c d : C)
    (f : D⟦J c, T d⟧)
    : UU
    := ext _ _ f · F d = F c · ext' _ _ (f · F d).

(** ** 1.1. The category of relative monad data *)

  Definition relative_monad_data_disp_cat
    (J : C ⟶ D)
    : disp_cat [C, D].
  Proof.
    use disp_struct.
    - use (λ T, _ × _).
      + exact (η_ax J T).
      + exact (∏ c d f, ext_ax J T c d f).
    - refine (λ T T' Tdata T'data F, _ × _).
      + exact (∏ c, mor_η_ax' F (pr1 Tdata) (pr1 T'data) c).
      + exact (∏ c d f, mor_ext_ax' F (pr2 Tdata) (pr2 T'data) c d f).
    - abstract(
        intros;
        apply isapropdirprod;
        repeat (apply impred_isaprop; intro);
        apply homset_property
      ).
    - abstract (
        intros;
        split;
        intros;
        [ apply id_right
        | refine (id_right _ @ !_);
          refine (id_left _ @ _);
          apply maponpaths;
          apply id_right ]
      ).
    - abstract (
        intros T T' T'' Tdata T'data T''data F F' Fdata F'data;
        split;
        [ intro c;
          refine (_ @ pr1 F'data _);
          refine (assoc _ _ _ @ _);
          apply (maponpaths (λ x, x · _));
          apply (pr1 Fdata)
        | intros c d f;
          refine (assoc _ _ _ @ _);
          refine (maponpaths (λ x, x · _) (pr2 Fdata _ _ _) @ _);
          refine (assoc' _ _ _ @ _);
          refine (maponpaths _ (pr2 F'data _ _ _) @ _);
          refine (_ @ assoc _ _ _);
          do 3 apply maponpaths;
          apply assoc' ]
      ).
  Defined.

  Definition relative_monad_data_cat
    (J : C ⟶ D)
    : category
    := total_category (relative_monad_data_disp_cat J).

(** ** 1.2. The type of relative monad data *)

  Definition relative_monad_data
    (J : C ⟶ D)
    : UU
    := relative_monad_data_cat J.

  Coercion relative_monad_data_to_functor
    {J : C ⟶ D}
    (T : relative_monad_data J)
    : C ⟶ D
    := pr1 T.

  Definition η
    {J : C ⟶ D}
    (T : relative_monad_data J)
    : J ⟹ T
    := (pr12 T : _ ⟹ _).

  Definition ext
    {J : C ⟶ D}
    (T : relative_monad_data J)
    {c d : C}
    (f : D⟦J c, T d⟧)
    : D⟦T c, T d⟧
    := pr22 T c d f.

  Definition make_relative_monad_data
    {J : C ⟶ D}
    (T : C ⟶ D)
    (η : η_ax J T)
    (ext : ∏ c d f, ext_ax J T c d f)
    : relative_monad_data J
    := T ,, η ,, ext.

  Definition mor_η_ax
    {J : C ⟶ D}
    {T T' : relative_monad_data J}
    (F : T ⟹ T')
    (c : C)
    : UU
    := mor_η_ax' F (η T) (η T') c.

  Definition mor_ext_ax
    {J : C ⟶ D}
    {T T' : relative_monad_data J}
    (F : T ⟹ T')
    (c d : C)
    (f : D⟦J c, T d⟧)
    : UU
    := mor_ext_ax' F (@ext J T) (@ext J T') c d f.

(** ** 1.3. The category of relative monads *)

  Definition ext_natural_ax
    {J : C ⟶ D}
    (T : relative_monad_data J)
    (c c' d d' : C)
    (fc : C⟦c', c⟧)
    (f: D⟦J c, T d⟧)
    (fd : C⟦d, d'⟧)
    : UU
    := ext T (#J fc · f · #T fd) = #T fc · ext T f · #T fd.

  Definition ext_η_ax
    {J : C ⟶ D}
    (T : relative_monad_data J)
    (c : C)
    : UU
    := ext T (η T c) = identity (T c).

  Definition η_ext_ax
    {J : C ⟶ D}
    (T : relative_monad_data J)
    (c d : C)
    (f : D⟦J c, T d⟧)
    : UU
    := f = η T c · ext T f.

  Definition ext_ext_ax
    {J : C ⟶ D}
    (T : relative_monad_data J)
    (c d e : C)
    (f : D⟦J c, T d⟧)
    (g : D⟦J d, T e⟧)
    : UU
    := ext T (f · ext T g) = ext T f · ext T g.

  Definition is_relative_monad
    {J : C ⟶ D}
    (T : relative_monad_data J)
    : UU
    := (∏ c c' d d' fc f fd, ext_natural_ax T c c' d d' fc f fd)
    × (∏ c, ext_η_ax T c)
    × (∏ c d f, η_ext_ax T c d f)
    × (∏ c d e f g, ext_ext_ax T c d e f g).

  Lemma isaprop_is_relative_monad
    {J : C ⟶ D}
    (T : relative_monad_data J)
    : isaprop (is_relative_monad T).
  Proof.
    repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply homset_property.
  Qed.

  Definition relative_monad_cat
    (J : C ⟶ D)
    : category
    := full_subcat (relative_monad_data_cat J) is_relative_monad.

(** ** 1.4. The type of relative monads *)

  Definition relative_monad
    (J : C ⟶ D)
    : UU
    := ∑ (T : relative_monad_data J), is_relative_monad T.

  Coercion relative_monad_to_relative_monad_data
    {J : C ⟶ D}
    (T : relative_monad J)
    : relative_monad_data J
    := pr1 T.

  Definition ext_natural
    {J : C ⟶ D}
    (T : relative_monad J)
    {c c' d d' : C}
    (fc : C⟦c', c⟧)
    (f : D⟦J c, T d⟧)
    (fd : C⟦d, d'⟧)
    : ext_natural_ax T c c' d d' fc f fd
    := pr12 T c c' d d' fc f fd.

  Definition ext_η
    {J : C ⟶ D}
    (T : relative_monad J)
    (c : C)
    : ext_η_ax T c
    := pr122 T c.

  Definition η_ext
    {J : C ⟶ D}
    (T : relative_monad J)
    {c d : C}
    (f : D⟦J c, T d⟧)
    : η_ext_ax T c d f
    := pr1 (pr222 T) c d f.

  Definition ext_ext
    {J : C ⟶ D}
    (T : relative_monad J)
    {c d e : C}
    (f : D⟦J c, T d⟧)
    (g : D⟦J d, T e⟧)
    : ext_ext_ax T c d e f g
    := pr2 (pr222 T) c d e f g.

  Definition make_relative_monad
    {J : C ⟶ D}
    (T : relative_monad_data J)
    (H : is_relative_monad T)
    : relative_monad J
    := T ,, H.

  Lemma relative_monad_functor_on_morphisms
    {J : C ⟶ D}
    {c d : C}
    (f : C⟦c, d⟧)
    (T : relative_monad J)
    : # T f = ext T (# J f · η T d).
  Proof.
    refine (_ @ maponpaths _ (id_right _)).
    refine (!_ @ maponpaths (λ x, _ (_ x)) (functor_id T d)).
    refine (ext_natural _ _ _ _ @ _).
    refine (maponpaths _ (functor_id T d) @ _).
    refine (id_right _ @ _).
    refine (maponpaths _ (ext_η _ _) @ _).
    apply id_right.
  Qed.

(** ** 1.5. The type of relative monad morphisms *)

  Definition relative_monad_morphism
    {J : C ⟶ D}
    (T T' : relative_monad J)
    : UU
    := relative_monad_cat J⟦T, T'⟧.

  Coercion relative_monad_morphism_to_nat_trans
    {J : C ⟶ D}
    (T T' : relative_monad J)
    (F : relative_monad_morphism T T')
    : T ⟹ T'
    := pr11 F.

  Definition mor_η
    {J : C ⟶ D}
    {T T' : relative_monad J}
    (F : relative_monad_morphism T T')
    (c : C)
    : mor_η_ax F c
    := pr121 F c.

  Definition mor_ext
    {J : C ⟶ D}
    {T T' : relative_monad J}
    (F : relative_monad_morphism T T')
    {c d : C}
    (f : D⟦J c, T d⟧)
    : mor_ext_ax F c d f
    := pr221 F c d f.

  Definition make_relative_monad_morphism
    {J : C ⟶ D}
    {T T' : relative_monad J}
    (F : T ⟹ T')
    (mor_η : ∏ c, mor_η_ax F c)
    (mor_ext : ∏ c d f, mor_ext_ax F c d f)
    : relative_monad_morphism T T'
    := (F ,, (mor_η ,, mor_ext)) ,, tt.

  Lemma relative_monad_morphism_eq
    {J : C ⟶ D}
    {T T' : relative_monad J}
    (F F' : relative_monad_morphism T T')
    (H : ∏ c, F c = F' c)
    : F = F'.
  Proof.
    apply subtypePath.
    {
      intro F''.
      apply isapropunit.
    }
    apply subtypePath.
    {
      intro F''.
      apply isapropdirprod;
      repeat (apply impred_isaprop; intro);
      apply homset_property.
    }
    apply nat_trans_eq_alt.
    exact H.
  Qed.

(** * 2. Univalence *)

  Lemma is_univalent_disp_relative_monad_data_disp_cat
    (J : C ⟶ D)
    : is_univalent_disp (relative_monad_data_disp_cat J).
  Proof.
    apply is_univalent_disp_iff_fibers_are_univalent.
    intros T Tdata T'data.
    use isweq_iso.
    - intro f.
      apply pathsdirprod;
        repeat (apply funextsec; intro).
      + apply nat_trans_eq_alt.
        intro c.
        refine (!id_right _ @ _).
        apply (pr11 f).
      + pose (pr21 f).
        refine (!id_right _ @ _).
        refine (pr21 f _ _ _ @ _).
        refine (id_left _ @ _).
        apply maponpaths.
        apply id_right.
    - intro.
      apply isasetdirprod;
        repeat (apply impred_isaset; intro).
      + apply isaset_nat_trans.
        apply homset_property.
      + apply homset_property.
    - intro.
      apply z_iso_eq.
      use pathsdirprod;
        repeat (apply funextsec; intro);
        apply homset_property.
  Qed.

  Lemma is_univalent_relative_monad_data_cat
    (J : C ⟶ D)
    (H : is_univalent D)
    : is_univalent (relative_monad_data_cat J).
  Proof.
    apply is_univalent_total_category.
    - apply (is_univalent_functor_category _ _ H).
    - apply is_univalent_disp_relative_monad_data_disp_cat.
  Qed.

  Lemma is_univalent_relative_monad_cat
    (J : C ⟶ D)
    (H : is_univalent D)
    : is_univalent (relative_monad_cat J).
  Proof.
    apply is_univalent_full_subcat.
    - exact (is_univalent_relative_monad_data_cat J H).
    - exact isaprop_is_relative_monad.
  Qed.

End RelativeMonad.

Arguments η_ax /.
Arguments ext_ax /.
Arguments mor_η_ax /.
Arguments mor_ext_ax /.
Arguments ext_natural_ax /.
Arguments ext_η_ax /.
Arguments η_ext_ax /.
Arguments ext_ext_ax /.

(** * 3. Precomposing relative monads with a functor *)

Definition relative_monad_precomp
  {C C' E : category}
  (F : C' ⟶ C)
  {J : C ⟶ E}
  (T : relative_monad J)
  : relative_monad (F ∙ J).
Proof.
  use make_relative_monad.
  - use make_relative_monad_data.
    + exact (F ∙ (T : C ⟶ E)).
    + exact (pre_whisker F (η T)).
    + exact (λ _ _, ext T).
  - abstract (
      repeat split;
      intros;
      apply (pr2 T)
    ).
Defined.

Definition relative_monad_morphism_precomp
  {C C' E : category}
  (F : C' ⟶ C)
  {J : C ⟶ E}
  {T T' : relative_monad J}
  (f : relative_monad_morphism T T')
  : relative_monad_morphism (relative_monad_precomp F T) (relative_monad_precomp F T').
Proof.
  use make_relative_monad_morphism.
  - exact (pre_whisker F f).
  - abstract (
      intro c;
      apply (mor_η f)
    ).
  - abstract (
      intros c d s;
      apply (mor_ext f)
    ).
Defined.

Definition relative_monad_precomp_functor
  {C C' E : category}
  (F : C' ⟶ C)
  (J : C ⟶ E)
  : relative_monad_cat J ⟶ relative_monad_cat (F ∙ J).
Proof.
  use make_functor.
  - use make_functor_data.
    + apply relative_monad_precomp.
    + apply relative_monad_morphism_precomp.
  - abstract (
      split;
      repeat intro;
      now apply relative_monad_morphism_eq
    ).
Defined.

(** * 4. The adjoint equivalence between relative monads on the embedding and algebraic theories *)

Section TheoryToMonad.

  Context (C : algebraic_theory).

  Definition theory_to_functor_data
    : functor_data finite_set_skeleton_category HSET.
  Proof.
    use tpair.
    - exact C.
    - intros m n a f.
      exact (f • (λ i, pr (a i))).
  Defined.

  Lemma theory_to_is_functor
    : is_functor theory_to_functor_data.
  Proof.
    split.
    - intro n.
      apply funextfun.
      intro f.
      apply comp_pr.
    - intros l m n a b.
      apply funextfun.
      intro f.
      refine (_ @ !comp_comp C f _ _).
      apply (maponpaths (comp f)).
      apply funextfun.
      intro i.
      exact (!pr_comp C (a i) _).
  Qed.

  Definition theory_to_functor
    : finite_set_skeleton_category ⟶ HSET
    := make_functor _ theory_to_is_functor.

  Definition theory_to_nat_trans_data
    : nat_trans_data HSET_embedding theory_to_functor
    := λ n, pr.

  Lemma theory_to_is_nat_trans
    : is_nat_trans _ _ theory_to_nat_trans_data.
  Proof.
    intros m n a.
    apply funextfun.
    intro i.
    exact (!pr_comp _ _ _).
  Qed.

  Definition theory_to_nat_trans
    : HSET_embedding ⟹ theory_to_functor
    := make_nat_trans _ _ _ theory_to_is_nat_trans.

  Definition theory_to_lift
    (m n : nat)
    (f : stn m → C n)
    (g : C m)
    : C n
    := g • f.

  Definition theory_to_monad_data
    : relative_monad_data HSET_embedding
    := make_relative_monad_data theory_to_functor theory_to_nat_trans theory_to_lift.

  Lemma theory_to_is_monad
    : is_relative_monad theory_to_monad_data.
  Proof.
    repeat split.
    - intros m m' n n' fm f fn.
      apply funextfun.
      intro g.
      refine (_ @ !maponpaths (λ x, x • _) (comp_comp C _ _ _)).
      refine (_ @ !comp_comp C g _ _).
      apply (maponpaths (comp g)).
      apply funextfun.
      intro i.
      exact (!maponpaths (λ x, x • _) (pr_comp C (fm i) _)).
    - intro m.
      apply funextfun.
      intro f.
      apply comp_pr.
    - intros m n a.
      apply funextfun.
      intro i.
      exact (!pr_comp _ _ _).
    - intros l m n a b.
      apply funextfun.
      intro f.
      exact (!comp_comp C f _ _).
  Qed.

  Definition theory_to_monad
    : relative_monad _
    := make_relative_monad _ theory_to_is_monad.

End TheoryToMonad.

Section MonadToTheory.

  Context (T : relative_monad HSET_embedding).

  Definition monad_to_theory_data
    : algebraic_theory_data.
  Proof.
    use make_algebraic_theory_data.
    - exact T.
    - intros n i.
      exact (η T n i).
    - intros m n f g.
      exact (ext T g f).
  Defined.

  Lemma monad_to_is_theory
    : is_algebraic_theory monad_to_theory_data.
  Proof.
    use make_is_algebraic_theory.
    - intros l m n f_l f_m f_n.
      exact (!eqtohomot (ext_ext T f_m f_n) f_l).
    - intros m n i f.
      exact (!eqtohomot (η_ext T f) i).
    - intros n f.
      exact (eqtohomot (ext_η T n) f).
  Qed.

  Definition monad_to_theory
    : algebraic_theory
    := make_algebraic_theory _ monad_to_is_theory.

End MonadToTheory.

Section MonadToTheoryMorphism.

  Context (T T' : relative_monad HSET_embedding).
  Context (F : relative_monad_morphism T T').

  Definition monad_morphism_to_theory_morphism_data
    : algebraic_theory_morphism_data (monad_to_theory T) (monad_to_theory T')
    := F.

  Lemma monad_morphism_to_is_theory_morphism
    : is_algebraic_theory_morphism monad_morphism_to_theory_morphism_data.
  Proof.
    use make_is_algebraic_theory_morphism.
    - intros n i.
      apply (eqtohomot (mor_η F n) i).
    - intros m n s t.
      apply (eqtohomot (mor_ext F t)).
  Qed.

  Definition monad_morphism_to_theory_morphism
    : algebraic_theory_morphism (monad_to_theory T) (monad_to_theory T')
    := make_algebraic_theory_morphism _ monad_morphism_to_is_theory_morphism.

End MonadToTheoryMorphism.

Definition monad_to_theory_functor
  : relative_monad_cat HSET_embedding ⟶ algebraic_theory_cat.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact monad_to_theory.
    + exact monad_morphism_to_theory_morphism.
  - abstract (
      split;
      repeat intro;
      now apply algebraic_theory_morphism_eq
    ).
Defined.

Section TheoryToMonadMorphism.

  Context {T T' : relative_monad HSET_embedding}.
  Context (F : algebraic_theory_morphism (monad_to_theory T) (monad_to_theory T')).

  Definition theory_morphism_to_nat_trans_data
    : nat_trans_data T T'
    := F.

  Lemma theory_morphism_to_is_nat_trans
    : is_nat_trans _ _ theory_morphism_to_nat_trans_data.
  Proof.
    intros m n f.
    refine (maponpaths (λ x, x · _) (relative_monad_functor_on_morphisms _ _) @ !_).
    refine (maponpaths _ (relative_monad_functor_on_morphisms _ _) @ !_).
    apply funextfun.
    intro t.
    refine (mor_comp F _ _ @ _).
    apply (maponpaths (λ x, ext T' x _)).
    apply funextfun.
    intro i.
    apply (mor_pr F).
  Qed.

  Definition theory_morphism_to_nat_trans
    : T ⟹ T'
    := make_nat_trans _ _ _ theory_morphism_to_is_nat_trans.

  Lemma theory_morphism_to_mor_η_ax
    (n : finite_set_skeleton_category)
    : mor_η_ax theory_morphism_to_nat_trans n.
  Proof.
    apply funextfun.
    intro i.
    apply (mor_pr F).
  Qed.

  Lemma theory_morphism_to_mor_ext_ax
    (m n : finite_set_skeleton_category)
    (s : HSET⟦HSET_embedding m, T n⟧)
    : mor_ext_ax theory_morphism_to_nat_trans m n s.
  Proof.
    apply funextfun.
    intro i.
    apply (mor_comp F).
  Qed.

  Definition theory_morphism_to_monad_morphism
    : relative_monad_morphism T T'
    := make_relative_monad_morphism
      theory_morphism_to_nat_trans
      theory_morphism_to_mor_η_ax
      theory_morphism_to_mor_ext_ax.

End TheoryToMonadMorphism.

Definition monad_theory_equivalence
  : adj_equivalence_of_cats monad_to_theory_functor.
Proof.
  apply rad_equivalence_of_cats.
  - apply is_univalent_relative_monad_cat.
    apply is_univalent_HSET.
  - intros T T'.
    use isweq_iso.
    + exact theory_morphism_to_monad_morphism.
    + abstract now
        intro F;
        apply relative_monad_morphism_eq.
    + abstract now
        intro F;
        apply algebraic_theory_morphism_eq.
  - intro C.
    apply hinhpr.
    exists (theory_to_monad C).
    use make_algebraic_theory_z_iso.
    + intro n.
      apply identity_z_iso.
    + abstract easy.
    + abstract easy.
Defined.
