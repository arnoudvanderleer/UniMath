Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.PVectors.
Require Import UniMath.Algebra.AbelianGroups.
Require Import UniMath.PAdics.fps.

Require Import UniMath.Algebra.Domains_and_Fields.

Local Open Scope ring.

Definition polynomial_ring
  (R : ring)
  : UU
  := ∑ (P : ring) (f : ringfun R P),
      ∏ (Q : ring) (g : ringfun R Q),
        (∑ (h : ringfun P Q), rigfuncomp f h = g)
        ≃ Q.

Coercion polynomial_ring_to_ring
  {R : ring}
  (PR : polynomial_ring R)
  : ring
  := pr1 PR.

Definition constant_polynomial
  {R : ring}
  (PR : polynomial_ring R)
  : ringfun R PR
  := pr12 PR.

Definition polynomial_ring_ind_map
  {R : ring}
  (PR : polynomial_ring R)
  (Q : ring)
  : ringfun PR Q → ringfun R Q
  := rigfuncomp (constant_polynomial PR).

Definition polynomial_ring_ind_X
  {R : ring}
  (PR : polynomial_ring R)
  (Q : ring)
  : ringfun PR Q → Q
  := λ h, pr22 PR Q (polynomial_ring_ind_map PR Q h) (h ,, idpath _).

Definition polynomial_ring_ind_inv
  {R : ring}
  (PR : polynomial_ring R)
  {Q : ring}
  (g : ringfun R Q)
  (q : Q)
  : ringfun PR Q
  := pr1 (invmap (pr22 PR Q g) q).

Section PolynomialRing.

  Context (R : ring).
  Context (PR : polynomial_ring R).

  Definition X
    : pr1 PR
    := polynomial_ring_ind_X PR PR (idfun _ ,, (pr2 (idrigiso _))).

  Definition Xn
    (n : ℕ)
    : pr1 PR.
  Proof.
    induction n as [|n IHn].
    - exact 1.
    - exact (IHn * X).
  Defined.

  (* Definition polynomial
    (n : nat)
    (a : stn n → R)
    : PR.
  Proof.
    induction n.
    - exact 0.
    - exact (
        IHn (a ∘ dni lastelement)
        + constant_polynomial PR (a lastelement) * Xn n
      ).
  Defined. *)

  Definition evaluate
    (f : PR)
    (a : R)
    : R
    := polynomial_ring_ind_inv PR (idfun _ ,, (pr2 (idrigiso _))) a f.

End PolynomialRing.

Section PowerSeries.

  Context {R : commring}.

  Definition vec_to_series
    {m : ℕ}
    (f : vec R m)
    : fpscommring R.
  Proof.
    intro n.
    induction (natgthorleh m n) as [Hn | Hn].
    - exact (el f (make_stn m n Hn)).
    - exact 0.
  Defined.

  Definition vec_to_series_gt
    {m : ℕ}
    {f : vec R m}
    {n : ℕ}
    (Hn : m > n)
    : vec_to_series f n = el f (make_stn _ n Hn).
  Proof.
    unfold vec_to_series.
    induction (natgthorleh m n) as [Hn' | Hn'].
    - apply (maponpaths (λ x, el f (make_stn _ _ x))).
      apply propproperty.
    - induction (isirreflnatgth _ (natgehgthtrans _ _ _ Hn' Hn)).
  Qed.

  Definition vec_to_series_le
    {m : ℕ}
    {f : vec R m}
    {n : ℕ}
    (Hn : m ≤ n)
    : vec_to_series f n = 0.
  Proof.
    unfold vec_to_series.
    induction (natgthorleh m n) as [Hn' | Hn'].
    - induction (isirreflnatgth _ (natgehgthtrans _ _ _ Hn Hn')).
    - reflexivity.
  Qed.

  Definition vec_to_series_add
    {n : ℕ}
    (f g : vec R n)
    : vec_to_series (vec_map (λ (fg : R × R), dirprod_pr1 fg + dirprod_pr2 fg) (vec_zip f g))
      = vec_to_series f + vec_to_series g.
  Proof.
    apply funextfun.
    intro m.
    induction (natgthorleh n m) as [Hm | Hm].
    - refine (vec_to_series_gt Hm @ _).
      refine (el_vec_map _ _ _ @ _).
      refine (two_arg_paths (maponpaths pr1 (el_vec_zip _ _ _)) (maponpaths dirprod_pr2 (el_vec_zip _ _ _)) @ !_).
      exact (two_arg_paths (vec_to_series_gt Hm) (vec_to_series_gt Hm)).
    - refine (vec_to_series_le Hm @ !_).
      refine (two_arg_paths (vec_to_series_le Hm) (vec_to_series_le Hm) @ !_).
      exact (!ringlunax1 _ _).
  Qed.

  Definition constant_series_data
    (r : R)
    : fpscommring R
    := vec_to_series ([( r )]).

  Lemma isringfun_constant_series
    : isringfun constant_series_data.
  Proof.
    apply make_isrigfun.
    - apply make_ismonoidfun.
      + intros x y.
        exact (vec_to_series_add [(x)] [(y)]).
      + apply funextfun.
        intro n.
        induction n;
          reflexivity.
    - apply make_ismonoidfun.
      * intros x y.
        apply funextfun.
        intro n.
        induction n.
        -- reflexivity.
        -- refine (_ @ !natsummationae0bottom _ _).
          ++ exact (!ringmultx0 R _).
          ++ intros m Hm.
            induction m; [induction (nopathsfalsetotrue Hm)|].
            exact (ringmult0x R _).
      * apply funextfun.
        intro n.
        induction n;
          reflexivity.
  Qed.

  Definition constant_series
    : ringfun R (fpscommring R)
    := ringfunconstr isringfun_constant_series.

End PowerSeries.

Section PolynomialRing.

  Context (R : commring).

  Definition is_polynomial
    : hsubtype (fpscommring R)
    := λ f, ∃ n, ∀ m, (m > n ⇒ f m = 0)%logic.

  Definition natlehandminusl (n m k : ℕ) (is : natgeh n m)
    : natgeh (k - m) (k - n).
  Proof.
    revert m k is.
    induction n as [ | n IHn ].
    intros. rewrite (nat0gehtois0 _ is).
    apply isreflnatleh. intro m. induction m. intros.
    destruct k.
    apply natminuslehn. apply natminuslehn.
    intro k. induction k. intro is.
    apply isreflnatleh. intro is.
    apply (IHn m k). apply is.
  Qed.

  Local Lemma aux1
    {k l m n : ℕ}
    (H1 : k > m + n)
    (H2 : l ≤ m)
    : k - l > n.
  Proof.
    refine (natgehgthtrans _ _ _ (natlehandminusl _ _ _ H2) _).
    refine (natgthandpluslinv _ _ m _).
    refine (transportb (λ x, x > _) _ H1).
    refine (natplusminusle _ @ _).
    {
      apply natgthtogeh.
      apply (natgthgehtrans _ _ _ H1).
      apply natgehplusnmn.
    }
    rewrite natpluscomm.
    refine (!natplusminusle (isreflnatgeh _) @ _).
    rewrite minusxx.
    apply natplusr0.
  Qed.

  Lemma issubring_is_polynomial
    : issubring is_polynomial.
  Proof.
    apply make_issubring.
    - apply make_issubgr.
      + apply make_issubmonoid.
        * intros f g.
          refine (hinhfun2 _ (pr2 f) (pr2 g)).
          intros Hf Hg.
          exists (pr1 Hf + pr1 Hg)%nat.
          intros m Hm.
          refine (two_arg_paths (pr2 Hf m _) (pr2 Hg m _) @ ringlunax1 _ _);
            apply (natgthgehtrans _ _ _ Hm).
          -- apply natgehplusnmn.
          -- apply natgehplusnmm.
        * exact (hinhpr (0%nat ,, λ _ _, idpath 0)).
      + intros f.
        refine (hinhfun _).
        intro Hf.
        exists (pr1 Hf).
        intros m Hm.
        refine (maponpaths _ (pr2 Hf m Hm) @ _).
        apply ringinvunel1.
    - apply make_issubmonoid.
      + intros f g.
        refine (hinhfun2 _ (pr2 f) (pr2 g)).
        intros Hf Hg.
        exists (pr1 Hf + pr1 Hg)%nat.
        intros m Hm.
        assert (Hfg : ∏ n, pr1 f n * pr1 g (m - n)%nat = 0).
        {
          intro n.
          induction (natgthorleh n (pr1 Hf)) as [Hn | Hn].
          -- refine (maponpaths (λ x, x * _) (pr2 Hf n Hn) @ _).
            apply ringmult0x.
          -- refine (maponpaths (λ x, _ * x) (pr2 Hg _ _) @ ringmultx0 _ _).
            exact (aux1 Hm Hn).
        }
        refine (natsummationae0bottom m _ @ _);
          intros;
          apply Hfg.
      + apply hinhpr.
        exists 1%nat.
        intros m Hm.
        destruct m.
        * induction (nopathsfalsetotrue Hm).
        * reflexivity.
  Qed.

  Lemma vec_to_is_polynomial
    {n : ℕ}
    (f : vec R n)
    : is_polynomial (vec_to_series f).
  Proof.
    apply hinhpr.
    exists n.
    intros m Hm.
    refine (vec_to_series_le _).
    now apply natgthtogeh.
  Qed.

  Definition polynomial_subring
    : subring (fpscommring R)
    := make_subring _ issubring_is_polynomial.

  Definition polynomial_ring_embedding
    : ringfun R polynomial_subring
    := ringfun_to_subring
      (A := polynomial_subring)
      constant_series
      (λ _, vec_to_is_polynomial _).

  Definition vec_to_polynomial
    {n : ℕ}
    (f : vec R n)
    : polynomial_subring
    := make_carrier _ (vec_to_series f) (vec_to_is_polynomial f).

  Definition polynomial_subring_X
    : polynomial_subring
    := vec_to_polynomial [(0 ; 1)].

End PolynomialRing.
