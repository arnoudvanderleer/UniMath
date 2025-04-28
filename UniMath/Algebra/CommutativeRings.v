(** * Algebra I. Part D.  Rigs and rings. Vladimir Voevodsky. Aug. 2011 - . *)
Require Import UniMath.Algebra.Groups.
(** Contents
- Standard Algebraic Structures
 - Commutative rings
  - General definitions
  - Computational lemmas for commutative rings
  - Subobjects
  - Quotient objects
  - Direct products
  - Opposite commutative rings
  - Commutative rigs to commutative rings
  - Rings of fractions
  - Canonical homomorphism to the ring of fractions
  - Ring of fractions in the case when all elements which are being
    inverted are cancelable
  - Relations similar to "greater" or "greater or equal" on the rings
    of fractions
  - Relations and the canonical homomorphism to the ring of fractions
*)


(** ** Preamble *)

(** Settings *)

Unset Kernel Term Sharing.

(** Imports *)

Require Import UniMath.MoreFoundations.Sets.
Require Import UniMath.MoreFoundations.Orders.
Require Export UniMath.Algebra.Monoids.

Local Open Scope logic.

(** *** Commutative rings *)

(** **** General definitions *)

Definition iscommring (X : setwith2binop) : UU := iscommringops (@op1 X) (@op2 X).

Definition commring : UU := ∑ (X : setwith2binop), iscommringops (@op1 X) (@op2 X).

Definition make_commring (X : setwith2binop) (is : iscommringops (@op1 X) (@op2 X)) :
  ∑ X0 : setwith2binop, iscommringops op1 op2 :=
  X ,, is.

Definition commringconstr {X : hSet} (opp1 opp2 : binop X)
           (ax11 : isgrop opp1) (ax12 : iscomm opp1)
           (ax21 : ismonoidop opp2) (ax22 : iscomm opp2)
           (dax : isdistr opp1 opp2) : commring :=
  @make_commring (make_setwith2binop X (opp1 ,, opp2))
               ((((ax11 ,, ax12) ,, ax21) ,, dax) ,, ax22).

Definition commringtoring : commring → ring := λ X, @make_ring (pr1 X) (pr1 (pr2 X)).
Coercion commringtoring : commring >-> ring.

Definition ringcomm2 (X : commring) : iscomm (@op2 X) := pr2 (pr2 X).

Definition commringop2axs (X : commring) : isabmonoidop (@op2 X) :=
  ringop2axs X ,, ringcomm2 X.

Definition ringmultabmonoid (X : commring) : abmonoid :=
  make_abmonoid (make_setwithbinop X op2) (ringop2axs X ,, ringcomm2 X).

Definition commringtocommrig (X : commring) : commrig := make_commrig _ (pr2 X).
Coercion commringtocommrig : commring >-> commrig.


(** **** (X = Y) ≃ (ringiso X Y)
    We use the following composition

                          (X = Y) ≃ (make_commring' X = make_commring' Y)
                                  ≃ ((pr1 (make_commring' X)) = (pr1 (make_commring' Y)))
                                  ≃ (ringiso X Y)

    where the third weak equivalence is given by univalence for ring, [ring_univalence]. We define
    [commring'] to be able to use [ring_univalence].
 *)

Local Definition commring' : UU :=
  ∑ D : (∑ X : setwith2binop, isringops (@op1 X) (@op2 X)), iscomm (@op2 (pr1 D)).

Local Definition make_commring' (CR : commring) : commring' :=
  (pr1 CR ,, dirprod_pr1 (pr2 CR)) ,, dirprod_pr2 (pr2 CR).

Definition commring_univalence_weq1 : commring ≃ commring' :=
  weqtotal2asstol
    (λ X : setwith2binop, isringops (@op1 X) (@op2 X))
    (λ (y : (∑ (X : setwith2binop), isringops (@op1 X) (@op2 X))), iscomm (@op2 (pr1 y))).

Definition commring_univalence_weq1' (X Y : commring) : (X = Y) ≃ (make_commring' X = make_commring' Y) :=
  make_weq _ (@isweqmaponpaths commring commring' commring_univalence_weq1 X Y).

Definition commring_univalence_weq2 (X Y : commring) :
  ((make_commring' X) = (make_commring' Y)) ≃ ((pr1 (make_commring' X)) = (pr1 (make_commring' Y))).
Proof.
  use subtypeInjectivity.
  intros w. use isapropiscomm.
Defined.
Opaque commring_univalence_weq2.

Definition commring_univalence_weq3 (X Y : commring) :
  ((pr1 (make_commring' X)) = (pr1 (make_commring' Y))) ≃ (ringiso X Y) :=
  ring_univalence (pr1 (make_commring' X)) (pr1 (make_commring' Y)).

Definition commring_univalence_map (X Y : commring) : (X = Y) → (ringiso X Y).
Proof.
  intros e. induction e. exact (idrigiso X).
Defined.

Lemma commring_univalence_isweq (X Y : commring) : isweq (commring_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (commring_univalence_weq1' X Y)
                   (weqcomp (commring_univalence_weq2 X Y) (commring_univalence_weq3 X Y))).
  - intros e. induction e.
    refine (weqcomp_to_funcomp_app @ _).
    exact weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque commring_univalence_isweq.

Definition commring_univalence (X Y : commring) : (X = Y) ≃ (ringiso X Y)
  := make_weq
    (commring_univalence_map X Y)
    (commring_univalence_isweq X Y).


(** **** Computational lemmas for commutative rings *)

Local Open Scope ring_scope.

Lemma commringismultcancelableif (X : commring) (x : X) (isl : ∏ y, x * y = 0 → y = 0) :
  iscancelable op2 x.
Proof.
  intros. split.
  - apply (ringismultlcancelableif X x isl).
  - assert (isr : ∏ y, y * x = 0 → y = 0).
    intros y e. rewrite (ringcomm2 X _ _) in e. apply (isl y e).
    apply (ringismultrcancelableif X x isr).
Qed.

Close Scope ring_scope.


(** **** Subobjects *)

Lemma iscommringcarrier {X : commring} (A : @subring X) : iscommringops (@op1 A) (@op2 A).
Proof.
  intros. exists (isringcarrier A).
  apply (pr2 (@isabmonoidcarrier (ringmultabmonoid X) (multsubmonoid A))).
Defined.

Definition carrierofasubcommring {X : commring} (A : @subring X) : commring :=
  make_commring A (iscommringcarrier A).


(** **** Quotient objects *)

Lemma iscommringquot {X : commring} (R : @ringeqrel X) :
  iscommringops (@op1 (setwith2binopquot R)) (@op2 (setwith2binopquot R)).
Proof.
  intros. exists (isringquot R).
  apply (pr2 (@isabmonoidquot (ringmultabmonoid X) (ringmultmonoideqrel R))).
Defined.

Definition commringquot {X : commring} (R : @ringeqrel X) : commring :=
  make_commring (setwith2binopquot R) (iscommringquot R).


(** **** Direct products *)

Lemma iscommringdirprod (X Y : commring) :
  iscommringops (@op1 (setwith2binopdirprod X Y)) (@op2 (setwith2binopdirprod X Y)).
Proof.
  intros. exists (isringdirprod X Y).
  apply (pr2 (isabmonoiddirprod (ringmultabmonoid X) (ringmultabmonoid Y))).
Defined.

Definition commringdirprod (X Y : commring) : commring :=
  make_commring (setwith2binopdirprod X Y) (iscommringdirprod X Y).

(** **** Opposite commutative rings *)

Local Open Scope ring.

(** We reuse much of the proof for general rigs *)
Definition opposite_commring (X : commring) : commring :=
  pr1 (X⁰),, pr2 (X⁰) ,, λ x y, @ringcomm2 X y x.

(** Commutativity makes taking the opposite trivial *)
Definition iso_commring_opposite (X : commring) : rigiso X (opposite_commring X) :=
  iso_commrig_opposite X.

Local Close Scope rig.

(** **** Commutative rigs to commutative rings *)

Local Open Scope rig_scope.

Lemma commrigtocommringcomm2 (X : commrig) : iscomm (rigtoringop2 X).
Proof.
  unfold iscomm.
  apply (setquotuniv2prop _ (λ x x', _ = _)).
  intros x x'.
  change (setquotpr (eqrelrigtoring X) (rigtoringop2int X x x')
        = setquotpr (eqrelrigtoring X) (rigtoringop2int X x' x)).
  apply (maponpaths (setquotpr (eqrelrigtoring X))).
  unfold rigtoringop2int.
  set (cm1 := rigcomm1 X). set (cm2 := rigcomm2 X).
  apply pathsdirprod.
  - rewrite (cm2 (pr1 x) (pr1 x')). rewrite (cm2 (pr2 x) (pr2 x')).
    apply idpath.
  - rewrite (cm2 (pr1 x) (pr2 x')). rewrite (cm2 (pr2 x) (pr1 x')).
    apply cm1.
Qed.

Definition commrigtocommring (X : commrig) : commring.
Proof.
  exists (rigtoring X). split.
  - apply (pr2 (rigtoring X)).
  - apply (commrigtocommringcomm2 X).
Defined.

Close Scope rig_scope.


(** **** Rings of fractions *)

Local Open Scope ring_scope.

Definition commringfracop1int (X : commring) (S : @subabmonoid (ringmultabmonoid X))
  : binop (X × S)
  := λ (x1s1 x2s2 : X × S),
      pr1 (pr2 x2s2) * pr1 x1s1 + pr1 (pr2 x1s1) * pr1 x2s2 ,,
      op (pr2 x1s1) (pr2 x2s2).

Definition commringfracop2int (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  binop (X × S) := abmonoidfracopint (ringmultabmonoid X) S.

Definition commringfracunel1int (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  X × S := 0 ,, unel S.

Definition commringfracunel2int (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  X × S := 1 ,, unel S.

Definition commringfracinv1int (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  X × S → X × S := λ xs, -1 * pr1 xs ,, pr2 xs.

Definition eqrelcommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  eqrel (X × S) := eqrelabmonoidfrac (ringmultabmonoid X) S.

Lemma commringfracl1 (X : commring) (x1 x2 x3 x4 a1 a2 s1 s2 s3 s4 : X)
      (eq1 : (x1 * s2) * a1 = (x2 * s1) * a1)
      (eq2 : (x3 * s4) * a2 = (x4 * s3) * a2) :
  ((s3 * x1 + s1 * x3) * (s2 * s4)) * (a1 * a2)
= ((s4 * x2 + s2 * x4) * (s1 * s3)) * (a1 * a2).
Proof.
  intros.
  set (rdistr := ringrdistr X). set (assoc2 := ringassoc2 X).
  set (op2axs := commringop2axs X). set (comm2 := ringcomm2 X).
  set (rer := abmonoidoprer op2axs).

  rewrite (rdistr (s3 * x1) (s1 * x3)  (s2 * s4)).
  rewrite (rdistr (s4 * x2) (s2 * x4) (s1 * s3)).
  rewrite (rdistr ((s3 * x1) * (s2 * s4)) ((s1 * x3) * (s2 * s4)) (a1 * a2)).
  rewrite (rdistr ((s4 * x2) * (s1 * s3)) ((s2 * x4) * (s1 * s3)) (a1 * a2)).
  clear rdistr.
  assert (e1 : ((s3 * x1) * (s2 * s4)) * (a1 * a2)
             = ((s4 * x2) * (s1 * s3)) * (a1 * a2)).
  {
    induction (assoc2 (s3 * x1) s2 s4).
    rewrite (assoc2 s3 x1 s2). rewrite (rer (s3 * (x1 * s2)) s4 a1 a2).
    rewrite (assoc2 s3 (x1 * s2) a1).
    induction (assoc2 (s4 * x2) s1 s3).
    rewrite (assoc2 s4 x2 s1). rewrite (rer (s4 * (x2 * s1)) s3 a1 a2).
    rewrite (assoc2 s4 (x2 * s1) a1). induction eq1.
    rewrite (comm2 s3 ((x1 * s2) * a1)). rewrite (comm2 s4 ((x1 * s2) * a1)).
    rewrite (rer ((x1 * s2) * a1) s3 s4 a2).
    apply idpath.
  }
  assert (e2 : ((s1 * x3) * (s2 * s4)) * (a1 * a2)
             = ((s2 * x4) * (s1 * s3)) * (a1 * a2)).
  {
    induction (comm2 s4 s2). induction (comm2 s3 s1). induction (comm2 a2 a1).
    induction (assoc2 (s1 * x3) s4 s2). induction (assoc2 (s2 * x4) s3 s1).
    rewrite (assoc2 s1 x3 s4). rewrite (assoc2 s2 x4 s3).
    rewrite (rer (s1 * (x3 * s4)) s2 a2 a1).
    rewrite (rer (s2 * (x4 * s3)) s1 a2 a1).
    rewrite (assoc2 s1 (x3 * s4) a2).
    rewrite (assoc2 s2 (x4 * s3) a2).
    induction eq2. induction (comm2 ((x3 * s4) * a2) s1).
    induction (comm2 ((x3 *s4) * a2) s2).
    rewrite (rer ((x3 * s4) * a2) s1 s2 a1).
    apply idpath.
  }
  induction e1. induction e2. apply idpath.
Qed.

Lemma commringfracop1comp (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  iscomprelrelfun2 (eqrelcommringfrac X S) (eqrelcommringfrac X S) (commringfracop1int X S).
Proof.
  intros. intros xs1 xs2 xs3 xs4. simpl.
  set (ff := @hinhfun2). simpl in ff. apply ff. clear ff.
  intros tt1 tt2. exists (@op S (pr1 tt1) (pr1 tt2)).
  set (eq1 := pr2 tt1). simpl in eq1.
  set (eq2 := pr2 tt2). simpl in eq2.
  unfold pr1carrier.
  apply (commringfracl1 X (pr1 xs1) (pr1 xs2) (pr1 xs3) (pr1 xs4)
                       (pr1 (pr1 tt1)) (pr1 (pr1 tt2)) (pr1 (pr2 xs1))
                       (pr1 (pr2 xs2)) (pr1 (pr2 xs3)) (pr1 (pr2 xs4)) eq1 eq2).
Qed.

Definition commringfracop1 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  binop (setquotinset (eqrelcommringfrac X S)) :=
  setquotfun2 (eqrelcommringfrac X S) (eqrelcommringfrac X S)
              (commringfracop1int X S) (commringfracop1comp X S).

Lemma commringfracl2 (X : commring) (x x' x'' s s' s'' : X) :
  s'' * (s' * x + s * x') + (s * s') * x''
= (s' * s'') * x + s * (s'' * x' + s' * x'').
Proof.
  intros.
  set (ldistr := ringldistr X). set (comm2 := ringcomm2 X).
  set (assoc2 := ringassoc2 X). set (assoc1 := ringassoc1 X).
  rewrite (ldistr (s' * x) (s * x') s'').
  rewrite (ldistr (s'' * x') (s' * x'') s).
  induction (comm2 s'' s').
  induction (assoc2 s'' s' x). induction (assoc2 s'' s x').
  induction (assoc2 s s'' x').
  induction (comm2 s s'').
  induction (assoc2 s s' x'').
  apply (assoc1 ((s'' * s') * x) ((s * s'') * x') ((s * s') * x'')).
Qed.

Lemma commringfracassoc1 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  isassoc (commringfracop1 X S).
Proof.
  intros.
  set (R := eqrelcommringfrac X S).
  set (add1int := commringfracop1int X S).
  set (add1 := commringfracop1 X S).
  unfold isassoc.
  assert (int : ∏ (xs xs' xs'' : X × S),
                setquotpr R (add1int (add1int xs xs') xs'')
              = setquotpr R (add1int xs (add1int xs' xs''))).
  unfold add1int. unfold commringfracop1int. intros xs xs' xs''.
  apply (@maponpaths _ _ (setquotpr R)). simpl. apply pathsdirprod.
  - unfold pr1carrier.
    apply (commringfracl2 X (pr1 xs) (pr1 xs') (pr1 xs'') (pr1 (pr2 xs))
                         (pr1 (pr2 xs')) (pr1 (pr2 xs''))).
  - apply (invmaponpathsincl _ (isinclpr1carrier (pr1 S))).
    unfold pr1carrier. simpl. set (assoc2 := ringassoc2 X).
    apply (assoc2 (pr1 (pr2 xs)) (pr1 (pr2 xs')) (pr1 (pr2 xs''))).
  - apply (setquotuniv3prop R (λ x x' x'', _ = _)), int.
Qed.

Lemma commringfraccomm1 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  iscomm (commringfracop1 X S).
Proof.
  intros.
  set (R := eqrelcommringfrac X S).
  set (add1int := commringfracop1int X S).
  set (add1 := commringfracop1 X S).
  unfold iscomm.
  apply (setquotuniv2prop _ (λ x x', _ = _)).
  intros xs xs'.
  apply (@maponpaths _ _ (setquotpr R) (add1int xs xs') (add1int xs' xs)).
  unfold add1int. unfold commringfracop1int.
  induction xs as [ x s ]. induction s as [ s iss ].
  induction xs' as [ x' s' ]. induction s' as [ s' iss' ].
  simpl.
  apply pathsdirprod.
  - change (s' * x + s * x' = s * x' + s' * x).
    induction (ringcomm1 X (s' * x) (s * x')). apply idpath.
  - apply (invmaponpathsincl _ (isinclpr1carrier (pr1 S))).
    simpl. change (s * s' = s' * s). apply (ringcomm2 X).
Qed.

Definition commringfracunel1 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  setquot (eqrelcommringfrac X S) := setquotpr (eqrelcommringfrac X S) (commringfracunel1int X S).

Definition commringfracunel2 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  setquot (eqrelcommringfrac X S) := setquotpr (eqrelcommringfrac X S) (commringfracunel2int X S).

Lemma commringfracinv1comp (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  iscomprelrelfun (eqrelcommringfrac X S) (eqrelcommringfrac X S) (commringfracinv1int X S).
Proof.
  intros.
  set (assoc2 := ringassoc2 X). intros xs xs'. simpl.
  set (ff := @hinhfun). simpl in ff. apply ff. clear ff.
  intro tt0. exists (pr1 tt0).
  set (x := pr1 xs). set (s := pr1 (pr2 xs)).
  set (x' := pr1 xs'). set (s' := pr1 (pr2 xs')).
  set (a0 := pr1 (pr1 tt0)).
  change (-1 * x * s' * a0 = -1 * x' * s * a0).
  rewrite (assoc2 -1 x s'). rewrite (assoc2 -1 x' s).
  rewrite (assoc2 -1 (x * s') a0). rewrite (assoc2 -1 (x' * s) a0).
  apply (maponpaths (λ x0 : X, -1 * x0) (pr2 tt0)).
Defined.

Definition commringfracinv1 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  setquot (eqrelcommringfrac X S) → setquot (eqrelcommringfrac X S) :=
  setquotfun (eqrelcommringfrac X S) (eqrelcommringfrac X S)
             (commringfracinv1int X S) (commringfracinv1comp X S).

Lemma commringfracisinv1 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  isinv (commringfracop1 X S) (commringfracunel1 X S) (commringfracinv1 X S).
Proof.
  intros.
  assert (isl : islinv (commringfracop1 X S) (commringfracunel1 X S) (commringfracinv1 X S)).
  {
    set (R := eqrelcommringfrac X S).
    set (add1int := commringfracop1int X S).
    set (add1 := commringfracop1 X S).
    set (inv1 := commringfracinv1 X S).
    set (inv1int := commringfracinv1int X S).
    set (qunel1int := commringfracunel1int X S).
    set (qunel1 := commringfracunel1 X S).
    set (assoc2 := ringassoc2 X).
    unfold islinv.
    apply (setquotunivprop _ (λ x, _ = _)).
    intro xs.
    apply (iscompsetquotpr R  (add1int (inv1int xs) xs) qunel1int).
    simpl. apply hinhpr. exists (unel S).
    set (x := pr1 xs). set (s := pr1 (pr2 xs)).
    change ((s * (-1 * x) + s * x) * 1 * 1 = 0 * (s * s) * 1).
    induction (ringldistr X (-1 * x) x s).
    rewrite (ringmultwithminus1 X x). rewrite (ringlinvax1 X x).
    rewrite (ringmultx0 X s). rewrite (ringmult0x X 1).
    rewrite (ringmult0x X 1). rewrite (ringmult0x X (s * s)).
    exact (!ringmult0x X 1).
  }
  exact (isl ,, weqlinvrinv _ (commringfraccomm1 X S) _ (commringfracinv1 X S) isl).
Qed.

Lemma commringfraclunit1 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  islunit (commringfracop1 X S) (commringfracunel1 X S).
Proof.
  intros.
  set (R := eqrelcommringfrac X S). set (add1int := commringfracop1int X S).
  set (add1 := commringfracop1 X S). set (un1 := commringfracunel1 X S).
  unfold islunit.
  apply (setquotunivprop R (λ x, _ = _)).
  intro xs.
  assert (e0 : add1int (commringfracunel1int X S) xs = xs).
  {
    unfold add1int. unfold commringfracop1int.
    induction xs as [ x s ]. induction s as [ s iss ].
    apply pathsdirprod.
    - simpl. change (s * 0 + 1 * x = x).
      rewrite (@ringmultx0 X s).
      rewrite (ringlunax2 X x).
      rewrite (ringlunax1 X x).
      apply idpath.
    - apply (invmaponpathsincl _ (isinclpr1carrier (pr1 S))).
      change (1 * s = s). apply (ringlunax2 X s).
  }
  apply (maponpaths (setquotpr R) e0).
Qed.

Lemma commringfracrunit1 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  isrunit (commringfracop1 X S) (commringfracunel1 X S).
Proof.
  intros.
  apply (weqlunitrunit (commringfracop1 X S) (commringfraccomm1 X S)
                       (commringfracunel1 X S) (commringfraclunit1 X S)).
Qed.

Definition commringfracunit1 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  ismonoidop (commringfracop1 X S)
  := commringfracassoc1 X S ,,
    commringfracunel1 X S ,,
    commringfraclunit1 X S ,,
    commringfracrunit1 X S.

Definition commringfracop2 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  binop (setquotinset (eqrelcommringfrac X S)) := abmonoidfracop (ringmultabmonoid X) S.

Lemma commringfraccomm2 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  iscomm (commringfracop2 X S).
Proof.
  intros.
  apply (commax (abmonoidfrac (ringmultabmonoid X) S)).
Qed.

Lemma commringfracldistr (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  isldistr (commringfracop1 X S) (commringfracop2 X S).
Proof.
  intros.
  set (R := eqrelcommringfrac X S).
  set (mult1int := commringfracop2int X S).
  set (mult1 := commringfracop2 X S).
  set (add1int := commringfracop1int X S).
  set (add1 := commringfracop1 X S).
  unfold isldistr.
  apply (setquotuniv3prop _ (λ x x' x'', _ = _)).
  intros xs xs' xs''.
  apply (iscompsetquotpr R (mult1int xs'' (add1int xs xs'))
                         (add1int (mult1int xs'' xs) (mult1int xs'' xs'))).

  induction xs as [ x s ]. induction xs' as [ x' s' ].
  induction xs'' as [ x'' s'' ]. induction s'' as [ s'' iss'' ].
  simpl. apply hinhpr. exists (unel S).
  induction s as [ s iss ]. induction s' as [ s' iss' ]. simpl.

  change (((x'' * (s' * x + s * x')) * ((s'' * s) * (s'' * s'))) * 1
        = (((s'' * s') * (x'' * x) + (s'' * s) * (x'' * x')) * (s'' * (s * s'))) * 1).

  rewrite (ringldistr X (s' * x) (s * x') x'').
  rewrite (ringrdistr X _ _ ((s'' * s) * (s'' * s'))).
  rewrite (ringrdistr X _ _ (s'' * (s * s'))).
  set (assoc := ringassoc2 X). set (comm := ringcomm2 X).
  set (rer := @abmonoidoprer X (@op2 X) (commringop2axs X)).

  assert (e1 : (x'' * (s' * x)) * ((s'' * s) * (s'' * s'))
             = ((s'' * s') * (x'' * x)) * (s'' * (s * s'))).
  {
    induction (assoc x'' s' x). induction (comm s' x'').
    rewrite (assoc s' x'' x). induction (comm (x'' * x) s').
    induction (comm (x'' * x) (s'' * s')). induction (assoc s'' s s').
    induction (comm (s'' * s') (s'' * s)). induction (comm s' (s'' * s)).
    induction (rer (x'' * x) s' (s'' * s') (s'' * s)).
    apply idpath.
  }
  assert (e2 : (x'' * (s * x')) * ((s'' * s) * (s'' * s'))
             = ((s'' * s) * (x'' * x')) * (s'' * (s * s'))).
  {
    induction (assoc x'' s x'). induction (comm s x'').
    rewrite (assoc s x'' x'). induction (comm (x'' * x') s).
    induction (comm (x'' * x') (s'' * s)).
    induction (rer (x'' * x') (s'' * s) s (s'' * s')).
    induction (assoc s s'' s'). induction (assoc s'' s s').
    induction (comm s s'').
    apply idpath.
  }
  rewrite e1. rewrite e2. apply idpath.
Qed.

Lemma commringfracrdistr (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  isrdistr (commringfracop1 X S) (commringfracop2 X S).
Proof.
  intros.
  apply (weqldistrrdistr (commringfracop1 X S) (commringfracop2 X S)
                         (commringfraccomm2 X S) (commringfracldistr X S)).
Defined.

(** Notes :

1. Construction of the addition on the multiplicative monoid of fractions
   requires only commutativity and associativity of multiplication and (right)
   distributivity. No properties of the addition are used.

2. The proof of associtivity for the addition on the multiplicative monoid of
   fractions requires in the associativity of the original addition but no other
   properties.
*)

Definition commringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) : commring.
Proof.
  intros.
  set (R := eqrelcommringfrac  X S).
  set (mult1 := commringfracop2 X S).
  set (add1 := commringfracop1 X S).
  set (uset := setquotinset R).
  apply (commringconstr add1 mult1).
  - exists (commringfracunit1 X S).
    exists (commringfracinv1 X S).
    apply (commringfracisinv1 X S).
  - apply (commringfraccomm1 X S).
  - apply (pr2 (abmonoidfrac (ringmultabmonoid X) S)).
  - apply (commringfraccomm2 X S).
  - apply (commringfracldistr X S ,, commringfracrdistr X S).
Defined.

Definition prcommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  X → S → commringfrac X S := λ x s, setquotpr _ (x ,, s).

Lemma invertibilityincommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  ∏ a a' : S, isinvertible (@op2 (commringfrac X S)) (prcommringfrac X S (pr1 a) a').
Proof.
  intros.
  apply (invertibilityinabmonoidfrac (ringmultabmonoid X) S).
Defined.


(** **** Canonical homomorphism to the ring of fractions *)

Definition tocommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) (x : X) :
  commringfrac X S := setquotpr _ (x ,, unel S).

Lemma isbinop1funtocommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  @isbinopfun X (commringfrac X S) (tocommringfrac X S).
Proof.
  intros. unfold isbinopfun. intros x x'.
  change (setquotpr (eqrelcommringfrac X S) (x + x' ,, unel S)
        = setquotpr _ (commringfracop1int X S (x ,, unel S) (x' ,, unel S))).
  apply (maponpaths (setquotpr _)). unfold commringfracop1int.
  simpl. apply pathsdirprod.
  - rewrite (ringlunax2 X _). rewrite (ringlunax2 X _). apply idpath.
  - change (unel S = op (unel S) (unel S)).
    exact (!runax S _).
Qed.

Lemma isunital1funtocommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  (tocommringfrac X S 0) = 0.
Proof.
  intros.
  apply idpath.
Qed.

Definition isaddmonoidfuntocommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  @ismonoidfun X (commringfrac X S) (tocommringfrac X S) :=
  isbinop1funtocommringfrac X S ,, isunital1funtocommringfrac X S.

Definition tocommringfracandminus0 (X : commring) (S : @subabmonoid (ringmultabmonoid X)) (x : X) :
  tocommringfrac X S (- x) = - tocommringfrac X S x :=
  binopfun_preserves_inv _ (isbinop1funtocommringfrac X S) x.

Definition tocommringfracandminus (X : commring) (S : @subabmonoid (ringmultabmonoid X)) (x y : X) :
  tocommringfrac X S (x - y) = tocommringfrac X S x - tocommringfrac X S y.
Proof.
  intros.
  rewrite ((isbinop1funtocommringfrac X S x (- y)) :
             tocommringfrac X S (x - y)
           = tocommringfrac X S x + tocommringfrac X S (- y)).
  rewrite (tocommringfracandminus0 X S y).
  apply idpath.
Qed.

Definition isbinop2funtocommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  @isbinopfun (ringmultmonoid X) (ringmultmonoid (commringfrac X S)) (tocommringfrac X S) :=
  isbinopfuntoabmonoidfrac (ringmultabmonoid X) S.

Lemma isunital2funtocommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  (tocommringfrac X S 1) = 1.
Proof.
  intros.
  apply idpath.
Qed.

Definition ismultmonoidfuntocommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  @ismonoidfun (ringmultmonoid X) (ringmultmonoid (commringfrac X S)) (tocommringfrac X S) :=
  isbinop2funtocommringfrac X S ,, isunital2funtocommringfrac X S.

Definition isringfuntocommringfrac (X : commring) (S : @subabmonoid (ringmultabmonoid X)) :
  @isringfun X (commringfrac X S) (tocommringfrac X S) :=
  isaddmonoidfuntocommringfrac X S ,, ismultmonoidfuntocommringfrac X S.


(** **** Ring of fractions in the case when all elements which are being inverted are cancelable *)

Definition hrelcommringfrac0 (X : commring) (S : @submonoid (ringmultabmonoid X)) :
  hrel (X × S) :=
  λ xa yb : setdirprod X S, (pr1 xa) * (pr1 (pr2 yb)) = (pr1 yb) * (pr1 (pr2 xa)).

Lemma weqhrelhrel0commringfrac (X : commring) (S : @submonoid (ringmultabmonoid X))
      (iscanc : ∏ a : S, isrcancelable (@op2 X) (pr1carrier _ a)) (xa xa' : X × S) :
  (eqrelcommringfrac X S xa xa') ≃ (hrelcommringfrac0 X S xa xa').
Proof.
  intros. unfold eqrelabmonoidfrac. unfold hrelabmonoidfrac. simpl.
  apply weqimplimpl.
  - apply (@hinhuniv _ (_ = _)).
    intro ae. induction ae as [ a eq ].
    apply (invmaponpathsincl _ (iscanc a) _ _ eq).
  - intro eq. apply hinhpr. exists (unel S).
    rewrite (ringrunax2 X). rewrite (ringrunax2 X).
    apply eq.
  - apply (isapropishinh _).
  - apply (setproperty X).
Qed.

Lemma isinclprcommringfrac (X : commring) (S : @submonoid (ringmultabmonoid X))
      (iscanc : ∏ a : S, isrcancelable (@op2 X) (pr1carrier _ a)) :
  ∏ a' : S, isincl (λ x, prcommringfrac X S x a').
Proof.
  intros. apply isinclbetweensets.
  apply (setproperty X). apply (setproperty (commringfrac X S)).
  intros x x'. intro e.
  set (e' := invweq (weqpathsinsetquot
                       (eqrelcommringfrac X S) (x ,, a') (x' ,, a')) e).
  set (e'' := weqhrelhrel0commringfrac
                X S iscanc (_ ,, _) (_ ,, _) e').
  simpl in e''. apply (invmaponpathsincl _ (iscanc a')). apply e''.
Defined.

Definition isincltocommringfrac (X : commring) (S : @submonoid (ringmultabmonoid X))
           (iscanc : ∏ a : S, isrcancelable (@op2 X) (pr1carrier _ a)) :
  isincl (tocommringfrac X S) := isinclprcommringfrac X S iscanc (unel S).

Lemma isdeceqcommringfrac (X : commring) (S : @submonoid (ringmultabmonoid X))
      (iscanc : ∏ a : S, isrcancelable (@op2 X) (pr1carrier _ a)) (is : isdeceq X) :
  isdeceq (commringfrac X S).
Proof.
  intros. apply (isdeceqsetquot (eqrelcommringfrac X S)). intros xa xa'.
  apply (isdecpropweqb (weqhrelhrel0commringfrac X S iscanc xa xa')).
  apply isdecpropif. unfold isaprop. simpl.
  set (int := setproperty X (pr1 xa * pr1 (pr2 xa')) (pr1 xa' * pr1 (pr2 xa))).
  simpl in int. apply int. unfold hrelcommringfrac0.
  simpl. apply (is _ _).
Defined.


(** **** Relations similar to "greater" or "greater or equal"  on the rings of fractions *)

Lemma ispartbinopcommringfracgt (X : commring) (S : @submonoid (ringmultabmonoid X)) {R : hrel X}
      (is0 : @isbinophrel (rigaddabmonoid X) R) (is1 : isringmultgt X R)
      (is2 : ∏ c : X, S c → R c 0) : @ispartbinophrel (ringmultabmonoid X) S R.
Proof.
  intros. split.
  - intros a b c s rab.
    apply (isringmultgttoislringmultgt X is0 is1 _ _ _ (is2 c s) rab).
  - intros a b c s rab.
    apply (isringmultgttoisrringmultgt X is0 is1 _ _ _ (is2 c s) rab).
Defined.

Definition commringfracgt (X : commring) (S : @submonoid (ringmultabmonoid X)) {R : hrel X}
           (is0 : @isbinophrel (rigaddabmonoid X) R) (is1 : isringmultgt X R)
           (is2 : ∏ c : X, S c → R c 0) : hrel (commringfrac X S) :=
  abmonoidfracrel (ringmultabmonoid X) S (ispartbinopcommringfracgt X S is0 is1 is2).

Lemma isringmultcommringfracgt (X : commring) (S : @submonoid (ringmultabmonoid X)) {R : hrel X}
      (is0 : @isbinophrel (rigaddabmonoid X) R) (is1 : isringmultgt X R)
      (is2 : ∏ c : X, S c → R c 0) : isringmultgt (commringfrac X S) (commringfracgt X S is0 is1 is2).
Proof.
  intros.
  set (rer2 := abmonoidrer (ringmultabmonoid X) :
                ∏ a b c d : X, (a * b) * (c * d) = (a * c) * (b * d)).
  apply islringmultgttoisringmultgt.
  assert (int : ∏ (a b c : ringaddabgr (commringfrac X S)),
                isaprop (commringfracgt X S is0 is1 is2 c 0 →
                         commringfracgt X S is0 is1 is2 a b →
                         commringfracgt X S is0 is1 is2 (c * a) (c * b))).
  {
    intros a b c.
    apply impred. intro.
    apply impred. intro.
    apply (pr2 _).
  }
  apply (setquotuniv3prop _ (λ a b c, make_hProp _ (int a b c))).
  intros xa1 xa2 xa3.
  change (abmonoidfracrelint (ringmultabmonoid X) S R xa3 (0 ,, unel S) →
          abmonoidfracrelint (ringmultabmonoid X) S R xa1 xa2 →
          abmonoidfracrelint (ringmultabmonoid X) S R
                             (commringfracop2int X S xa3 xa1)
                             (commringfracop2int X S xa3 xa2)).
  simpl. apply hinhfun2. intros t21 t22.
  set (c1s := pr1 t21). set (c1 := pr1 c1s). set (r1 := pr2 t21).
  set (c2s := pr1 t22). set (c2 := pr1 c2s). set (r2 := pr2 t22).
  set (x1 := pr1 xa1). set (a1 := pr1 (pr2 xa1)).
  set (x2 := pr1 xa2). set (a2 := pr1 (pr2 xa2)).
  set (x3 := pr1 xa3). set (a3 := pr1 (pr2 xa3)).
  exists (@op S c1s c2s).
  change (pr1 (R (x3 * x1 * (a3 * a2) * (c1 * c2))
                 (x3 * x2 * (a3 * a1) * (c1 * c2)))).
  rewrite (ringcomm2 X a3 a2).
  rewrite (ringcomm2 X a3 a1).
  rewrite (ringassoc2 X _ _ (c1 * c2)).
  rewrite (ringassoc2 X (x3 * x2) _ (c1 * c2)).
  rewrite (rer2 _ a3 c1 _).
  rewrite (rer2 _ a3 c1 _).
  rewrite (ringcomm2 X a2 c1).
  rewrite (ringcomm2 X a1 c1).
  rewrite <- (ringassoc2 X (x3 * x1) _ _).
  rewrite <- (ringassoc2 X (x3 * x2) _ _).
  rewrite (rer2 _ x1 c1 _). rewrite (rer2 _ x2 c1 _).
  rewrite (ringcomm2 X a3 c2).
  rewrite <- (ringassoc2 X _ c2 a3).
  rewrite <- (ringassoc2 X _ c2 _).
  apply ((isringmultgttoisrringmultgt X is0 is1) _ _ _ (is2 _ (pr2 (pr2 xa3)))).
  rewrite (ringassoc2 X _ _ c2). rewrite (ringassoc2 X _ (x2 * a1) c2).

  simpl in r1. clearbody r1. simpl in r2. clearbody r2.
  change (pr1 (R (x3 * 1 * c1) (0 * a3 * c1))) in r1.
  rewrite (ringrunax2 _ _) in r1. rewrite (ringmult0x X _) in r1.
  rewrite (ringmult0x X _) in r1.
  apply ((isringmultgttoislringmultgt X is0 is1) _ _ _ r1 r2).
Qed.

Lemma isringaddcommringfracgt (X : commring) (S : @submonoid (ringmultabmonoid X)) {R : hrel X}
      (is0 : @isbinophrel (rigaddabmonoid X) R) (is1 : isringmultgt X R)
      (is2 : ∏ c : X, S c → R c 0) : @isbinophrel (commringfrac X S) (commringfracgt X S is0 is1 is2).
Proof.
  intros.
  set (rer2 := (abmonoidrer (ringmultabmonoid X)) :
                 ∏ a b c d : X, (a * b) * (c * d) = (a * c) * (b * d)).
  apply isbinophrelif. intros a b. apply (ringcomm1 (commringfrac X S) a b).

  assert (int : ∏ (a b c : ringaddabgr (commringfrac X S)),
                isaprop (commringfracgt X S is0 is1 is2 a b →
                         commringfracgt X S is0 is1 is2 (op c a) (op c b))).
  {
    intros a b c.
    apply impred. intro.
    apply (pr2 _).
  }
  apply (setquotuniv3prop _ (λ a b c, make_hProp _ (int a b c))).
  intros xa1 xa2 xa3.
  change (abmonoidfracrelint (ringmultabmonoid X) S R xa1 xa2 →
          abmonoidfracrelint (ringmultabmonoid X) S R
                             (commringfracop1int X S xa3 xa1)
                             (commringfracop1int X S xa3 xa2)).
  simpl. apply hinhfun. intro t2.
  set (c0s := pr1 t2). set (c0 := pr1 c0s). set (r := pr2 t2).
  exists c0s.
  set (x1 := pr1 xa1). set (a1 := pr1 (pr2 xa1)).
  set (x2 := pr1 xa2). set (a2 := pr1 (pr2 xa2)).
  set (x3 := pr1 xa3). set (a3 := pr1 (pr2 xa3)).
  change (pr1 (R ((a1 * x3 + a3 * x1) * (a3 * a2) * c0)
                 ((a2 * x3 + a3 * x2) * (a3 * a1) * c0))).
  rewrite (ringassoc2 X _ _ c0). rewrite (ringassoc2 X _ (a3 * _) c0).
  rewrite (ringrdistr X _ _ _). rewrite (ringrdistr X _ _ _).
  rewrite (rer2 _ x3 _ _).  rewrite (rer2 _ x3 _ _).
  rewrite (ringcomm2 X a3 a2). rewrite (ringcomm2 X a3 a1).
  rewrite <- (ringassoc2 X a1 a2 a3).
  rewrite <- (ringassoc2 X a2 a1 a3).
  rewrite (ringcomm2 X a1 a2).  apply ((pr1 is0) _ _ _).
  rewrite (ringcomm2 X a2 a3). rewrite (ringcomm2 X  a1 a3).
  rewrite (ringassoc2 X a3 a2 c0). rewrite (ringassoc2 X a3 a1 c0).
  rewrite (rer2 _ x1 a3 _). rewrite (rer2 _ x2 a3 _).
  rewrite <- (ringassoc2 X x1 _ _).
  rewrite <- (ringassoc2 X x2 _ _).
  apply ((isringmultgttoislringmultgt X is0 is1)
           _ _ _ (is2 _ (pr2 (@op S (pr2 xa3) (pr2 xa3)))) r).
Qed.

Definition isdeccommringfracgt (X : commring) (S : @submonoid (ringmultabmonoid X)) {R : hrel X}
           (is0 : @isbinophrel (rigaddabmonoid X) R) (is1 : isringmultgt X R)
           (is2 : ∏ c : X, S c → R c 0) (is' : @ispartinvbinophrel (ringmultabmonoid X) S R)
           (isd : isdecrel R) : isdecrel (commringfracgt X S is0 is1 is2).
Proof.
  intros.
  apply (isdecabmonoidfracrel
           (ringmultabmonoid X) S (ispartbinopcommringfracgt X S is0 is1 is2) is' isd).
Defined.

Lemma StrongOrder_correct_commrngfrac (X : commring) (Y : @subabmonoid (ringmultabmonoid X))
      (gt : StrongOrder X)
      Hgt Hle Hmult Hpos :
  commringfracgt X Y (R := gt) Hle Hmult Hpos = StrongOrder_abmonoidfrac Y gt Hgt.
Proof.
  apply funextfun ; intros x.
  apply funextfun ; intros y.
  apply (maponpaths (λ H, abmonoidfracrel (ringmultabmonoid X) Y H x y)).
  apply isaprop_ispartbinophrel.
Defined.

(** **** Relations and the canonical homomorphism to the ring of fractions *)

Lemma iscomptocommringfrac (X : commring) (S : @submonoid (ringmultabmonoid X)) {L : hrel X}
           (is0 : @isbinophrel (rigaddabmonoid X) L) (is1 : isringmultgt X L)
           (is2 : ∏ c : X, S c → L c 0) :
  iscomprelrelfun L (commringfracgt X S is0 is1 is2) (tocommringfrac X S).
Proof.
  apply (iscomptoabmonoidfrac (ringmultabmonoid X)).
Qed.

Close Scope ring_scope.

(* End of the file *)
