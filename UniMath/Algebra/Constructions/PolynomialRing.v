Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.
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
    (n : nat)
    : pr1 PR.
  Proof.
    induction n as [|n IHn].
    - exact 1.
    - exact (IHn * X).
  Defined.

  Definition polynomial
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
  Defined.

  Definition evaluate
    (f : PR)
    (a : R)
    : R
    := polynomial_ring_ind_inv PR (idfun _ ,, (pr2 (idrigiso _))) a f.

End PolynomialRing.

Section PolynomialRing.

  Context (R : commring).

  Definition is_polynomial
    : hsubtype (fpscommring R)
    := λ f, ∃ n, ∀ m, (m > n ⇒ f m = 0)%logic.

  Definition natlehandminusl (n m k : nat) (is : natgeh n m)
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
          refine (two_arg_paths (pr2 Hf m _) (pr2 Hg m _) @ _).
          -- apply (natgthgehtrans _ _ _ Hm).
            refine (transportb (λ x, x > _) (plus_n_Sm _ _) _).
            refine (transportf (λ x, _ > x) (natplusr0 _) _).
            apply (natgthandplusl (S (pr1 Hg)) 0 (pr1 Hf)).
            apply natgthsn0.
          -- apply (natgthgehtrans _ _ _ Hm).
            apply (natgthandplusr (S (pr1 Hf)) 0).
            apply natgthsn0.
          -- apply (lunax (ringaddabgr _)).
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
            refine (natgehgthtrans _ _ _ (natlehandminusl _ _ m Hn) _).
            refine (natgthandpluslinv _ _ (pr1 Hf) _).
            refine (transportb (λ x, x > _) _ Hm).
            refine (natplusminusle _ @ _).
            {
              apply natgthtogeh.
              apply (natgthgehtrans _ _ _ Hm).
              apply natgehplusnmn.
            }
            rewrite natpluscomm.
            refine (!natplusminusle (isreflnatgeh _) @ _).
            rewrite minusxx.
            apply natplusr0.
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

End PolynomialRing.
