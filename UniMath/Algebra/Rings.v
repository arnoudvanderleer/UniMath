(** * Algebra I. Part D.  Rigs and rings. Vladimir Voevodsky. Aug. 2011 - . *)
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Rigs.
(** Contents
- Standard Algebraic Structures
 - Rings
  - General definitions
  - Homomorphisms of rings
  - Computation lemmas for rings
  - Relations compatible with the additive structure on rings
  - Relations compatible with the multiplicative structure on rings
  - Relations "inversely compatible" with the multiplicative structure
    on rings
  - Relations on rings and ring homomorphisms
  - Subobjects
  - Quotient objects
  - Direct products
  - Opposite rings
  - Ring of differences associated with a rig
  - Canonical homomorphism to the ring associated with a rig (ring of
    differences)
  - Relations similar to "greater" or "greater or equal" on the ring
    associated with a rig
  - Relations and the canonical homomorphism to the ring associated
    with a rig (ring of differences)
*)


(** ** Preamble *)

(** Settings *)

Unset Kernel Term Sharing.

(** Imports *)

Require Import UniMath.MoreFoundations.Sets.
Require Import UniMath.MoreFoundations.Orders.
Require Export UniMath.Algebra.Monoids.

Local Open Scope logic.

(** *** Rings *)


(** **** General definitions *)

Definition ring : UU := ∑ (X : setwith2binop), isringops (@op1 X) (@op2 X).

Definition make_ring {X : setwith2binop} (is : isringops (@op1 X) (@op2 X)) : ring :=
  X ,, is.

Definition pr1ring : ring → setwith2binop :=
  @pr1 _ (λ X : setwith2binop, isringops (@op1 X) (@op2 X)).
Coercion pr1ring : ring >-> setwith2binop.

Definition ringaxs (X : ring) : isringops (@op1 X) (@op2 X) := pr2 X.

Definition ringop1axs (X : ring) : isabgrop (@op1 X) := pr1 (pr1 (pr2 X)).

Definition ringassoc1 (X : ring) : isassoc (@op1 X) := assocax_is (ringop1axs X).

Definition ringunel1 {X : ring} : X := unel_is (ringop1axs X).

Definition ringlunax1 (X : ring) : islunit op1 (@ringunel1 X) := lunax_is (ringop1axs X).

Definition ringrunax1 (X : ring) : isrunit op1 (@ringunel1 X) := runax_is (ringop1axs X).

Definition ringinv1 {X : ring} : X → X := grinv_is (ringop1axs X).

Definition ringlinvax1 (X : ring) : ∏ x : X, op1 (ringinv1 x) x = ringunel1 :=
  grlinvax_is (ringop1axs X).

Definition ringrinvax1 (X : ring) : ∏ x : X, op1 x (ringinv1 x) = ringunel1 :=
  grrinvax_is (ringop1axs X).

Definition ringcomm1 (X : ring) : iscomm (@op1 X) := commax_is (ringop1axs X).

Definition ringop2axs (X : ring) : ismonoidop (@op2 X) := pr2 (pr1 (pr2 X)).

Definition ringassoc2 (X : ring) : isassoc (@op2 X) := assocax_is (ringop2axs X).

Definition ringunel2 {X : ring} : X := unel_is (ringop2axs X).

Definition ringlunax2 (X : ring) : islunit op2 (@ringunel2 X) := lunax_is (ringop2axs X).

Definition ringrunax2 (X : ring) : isrunit op2 (@ringunel2 X) := runax_is (ringop2axs X).

Definition ringdistraxs (X : ring) : isdistr (@op1 X) (@op2 X) := pr2 (pr2 X).

Definition ringldistr (X : ring) : isldistr (@op1 X) (@op2 X) := pr1 (pr2 (pr2 X)).

Definition ringrdistr (X : ring) : isrdistr (@op1 X) (@op2 X) := pr2 (pr2 (pr2 X)).

Definition ringconstr {X : hSet} (opp1 opp2 : binop X) (ax11 : isgrop opp1) (ax12 : iscomm opp1)
           (ax2 : ismonoidop opp2) (dax : isdistr opp1 opp2) : ring :=
  @make_ring (make_setwith2binop X (opp1 ,, opp2))
           (((ax11 ,, ax12) ,, ax2) ,, dax).

Definition ringmultx0 (X : ring) : ∏ x : X, (op2 x ringunel1) = ringunel1 :=
  ringmultx0_is (ringaxs X).

Definition ringmult0x (X : ring) : ∏ x : X, (op2 ringunel1 x) = ringunel1 :=
  ringmult0x_is (ringaxs X).

Definition ringminus1 {X : ring} : X := ringminus1_is (ringaxs X).

Definition ringmultwithminus1 (X : ring) : ∏ x : X, op2 ringminus1 x = ringinv1 x :=
  ringmultwithminus1_is (ringaxs X).

Definition ringaddabgr (X : ring) : abgr := make_abgr (make_setwithbinop X op1) (ringop1axs X).
Coercion ringaddabgr : ring >-> abgr.

Definition ringmultmonoid (X : ring) : monoid := make_monoid (make_setwithbinop X op2) (ringop2axs X).

Declare Scope ring_scope.
Notation "x + y" := (op1 x y) : ring_scope.
Notation "x - y" := (op1 x (ringinv1 y)) : ring_scope.
Notation "x * y" := (op2 x y) : ring_scope.
Notation "0" := (ringunel1) : ring_scope.
Notation "1" := (ringunel2) : ring_scope.
Notation "-1" := (ringminus1) (at level 0) : ring_scope.
Notation " - x " := (ringinv1 x) : ring_scope.

Delimit Scope ring_scope with ring.

Definition ringtorig (X : ring) : rig := @make_rig _ (pr2 X).
Coercion ringtorig : ring >-> rig.

(** **** Homomorphisms of rings *)

Definition isringfun {X Y : ring} (f : X → Y) := @isrigfun X Y f.

Definition ringfun (X Y : ring) := rigfun X Y.

Lemma isaset_ringfun (X Y : ring) : isaset (ringfun X Y).
Proof.
   apply (isofhleveltotal2 2).
   - use impred_isaset. intro x.
     apply setproperty.
   - intro f. apply isasetaprop.
     apply isapropisrigfun.
Defined.

Definition ringfunconstr {X Y : ring} {f : X → Y} (is : isringfun f) : ringfun X Y := rigfunconstr is.
Identity Coercion id_ringfun : ringfun >-> rigfun.

Definition ringaddfun {X Y : ring} (f : ringfun X Y) : monoidfun X Y := make_monoidfun (pr1 (pr2 f)).

Definition ringmultfun {X Y : ring} (f : ringfun X Y) :
  monoidfun (ringmultmonoid X) (ringmultmonoid Y) := make_monoidfun (pr2 (pr2 f)).

Definition ringiso (X Y : ring) := rigiso X Y.

Definition make_ringiso {X Y : ring} (f : X ≃ Y) (is : isringfun f) : ringiso X Y := f ,, is.
Identity Coercion id_ringiso : ringiso >-> rigiso.

Definition isringfuninvmap {X Y : ring} (f : ringiso X Y) : isringfun (invmap f) := isrigfuninvmap f.


(** **** (X = Y) ≃ (ringiso X Y)
    We use the following composition

                           (X = Y) ≃ (make_ring' X = make_ring' Y)
                                   ≃ ((pr1 (make_ring' X)) = (pr1 (make_ring' Y)))
                                   ≃ (ringiso X Y)

    where the third weak equivalence is given by univalence for rigs, [rig_univalence]. We define
    ring' to be able to apply [rig_univalence].
 *)

Local Definition ring' : UU :=
  ∑ D : (∑ X : setwith2binop, isrigops (@op1 X) (@op2 X)),
        invstruct (@op1 (pr1 D)) (dirprod_pr1 (dirprod_pr1 (pr1 (pr1 (pr2 D))))).

Local Definition make_ring' (R : ring) : ring'.
Proof.
  use tpair.
  - exists (pr1 R).
    use make_isrigops.
    + use make_isabmonoidop.
      * exact (pr1 (dirprod_pr1 (dirprod_pr1 (dirprod_pr1 (pr2 R))))).
      * exact (dirprod_pr2 (dirprod_pr1 (dirprod_pr1 (pr2 R)))).
    + exact (dirprod_pr2 (dirprod_pr1 (pr2 R))).
    + exact (@mult0x_is_l (pr1 R) (@op1 (pr1 R)) (@op2 (pr1 R))
                          (dirprod_pr1 (dirprod_pr1 (dirprod_pr1 (pr2 R))))
                          (dirprod_pr2 (dirprod_pr1 (pr2 R))) (dirprod_pr2 (pr2 R))).
    + exact (@multx0_is_l (pr1 R) (@op1 (pr1 R)) (@op2 (pr1 R))
                          (dirprod_pr1 (dirprod_pr1 (dirprod_pr1 (pr2 R))))
                          (dirprod_pr2 (dirprod_pr1 (pr2 R))) (dirprod_pr2 (pr2 R))).
    + exact (dirprod_pr2 (pr2 R)).
  - exact (pr2 (dirprod_pr1 (dirprod_pr1 (dirprod_pr1 (pr2 R))))).
Defined.

Local Definition make_ring_from_ring' (R : ring') : ring.
Proof.
  use make_ring.
  - exact (pr1 (pr1 R)).
  - use make_isringops.
    + use make_isabgrop.
      * use make_isgrop.
        -- exact (dirprod_pr1 (dirprod_pr1 (pr1 (dirprod_pr1 (pr2 (pr1 R)))))).
        -- exact (pr2 R).
      * exact (dirprod_pr2 (dirprod_pr1 (pr1 (dirprod_pr1 (pr2 (pr1 R)))))).
    + exact (dirprod_pr2 (pr1 (dirprod_pr1 (pr2 (pr1 R))))).
    + exact (dirprod_pr2 (pr2 (pr1 R))).
Defined.

Definition ring_univalence_weq1 : ring ≃ ring'.
Proof.
  use make_weq.
  - intros R. exact (make_ring' R).
  - use isweq_iso.
    + intros R'. exact (make_ring_from_ring' R').
    + intros R. use idpath.
    + intros R'.
      use total2_paths_f.
      * use total2_paths_f.
        -- use idpath.
        -- use proofirrelevance. use isapropisrigops.
      * use proofirrelevance. use isapropinvstruct.
Defined.

Definition ring_univalence_weq1' (X Y : ring) : (X = Y) ≃ (make_ring' X = make_ring' Y) :=
  make_weq _ (@isweqmaponpaths ring ring' ring_univalence_weq1 X Y).

Definition ring_univalence_weq2 (X Y : ring) :
  ((make_ring' X) = (make_ring' Y)) ≃ ((pr1 (make_ring' X)) = (pr1 (make_ring' Y))).
Proof.
  use subtypeInjectivity.
  intros w. use isapropinvstruct.
Defined.
Opaque ring_univalence_weq2.

Definition ring_univalence_weq3 (X Y : ring) :
  ((pr1 (make_ring' X)) = (pr1 (make_ring' Y))) ≃ (rigiso X Y) :=
  rig_univalence (pr1 (make_ring' X)) (pr1 (make_ring' Y)).

Definition ring_univalence_map (X Y : ring) : (X = Y) → (ringiso X Y).
Proof.
  intros e. induction e. exact (idrigiso X).
Defined.

Lemma ring_univalence_isweq (X Y : ring) : isweq (ring_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (ring_univalence_weq1' X Y)
                   (weqcomp (ring_univalence_weq2 X Y) (ring_univalence_weq3 X Y))).
  - intros e. induction e.
    refine (weqcomp_to_funcomp_app @ _).
    exact weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque ring_univalence_isweq.

Definition ring_univalence (X Y : ring) : (X = Y) ≃ (ringiso X Y)
  := make_weq
    (ring_univalence_map X Y)
    (ring_univalence_isweq X Y).


(** **** Computation lemmas for rings *)

Local Open Scope ring_scope.

Definition ringinvunel1 (X : ring) : -0 = 0 := grinvunel X.

Lemma ringismultlcancelableif (X : ring) (x : X) (isl : ∏ y, x * y = 0 → y = 0) :
  islcancelable op2 x.
Proof.
  intros.
  apply (@isinclbetweensets X X).
  - apply setproperty.
  - apply setproperty.
  - intros x1 x2 e.
    set (e' := maponpaths (λ a, a + (x * (-x2))) e). simpl in e'.
    rewrite <- (ringldistr X _ _ x) in e'.
    rewrite <- (ringldistr X _ _ x) in e'.
    rewrite (ringrinvax1 X x2) in e'.
    rewrite (ringmultx0 X _) in e'.
    set (e'' := isl (x1 - x2) e').
    set (e''' := maponpaths (λ a, a + x2) e''). simpl in e'''.
    rewrite (ringassoc1 X _ _ x2) in e'''.
    rewrite (ringlinvax1 X x2) in e'''.
    rewrite (ringlunax1 X _) in e'''.
    rewrite (ringrunax1 X _) in e'''.
    apply e'''.
Qed.

Lemma ringismultrcancelableif (X : ring) (x : X) (isr : ∏ y, y * x = 0 → y = 0) :
  isrcancelable op2 x.
Proof.
  intros. apply (@isinclbetweensets X X).
  - apply setproperty.
  - apply setproperty.
  - intros x1 x2 e.
    set (e' := maponpaths (λ a, a + ((-x2) * x)) e).  simpl in e'.
    rewrite <- (ringrdistr X _ _ x) in e'.
    rewrite <- (ringrdistr X _ _ x) in e'.
    rewrite (ringrinvax1 X x2) in e'.
    rewrite (ringmult0x X _) in e'.
    set (e'' := isr (x1 - x2) e').
    set (e''' := maponpaths (λ a, a + x2) e''). simpl in e'''.
    rewrite (ringassoc1 X _ _ x2) in e'''.
    rewrite (ringlinvax1 X x2) in e'''.
    rewrite (ringlunax1 X _) in e'''.
    rewrite (ringrunax1 X _) in e'''.
    apply e'''.
Qed.

Lemma ringismultcancelableif (X : ring) (x : X) (isl : ∏ y, x * y = 0 → y = 0)
      (isr : ∏ y, y * x = 0 → y = 0) : iscancelable op2 x.
Proof.
  intros.
  exact (ringismultlcancelableif X x isl ,, ringismultrcancelableif X x isr).
Defined.

Lemma ringlmultminus (X : ring) (a b : X) : -a * b = -(a * b).
Proof.
  intros. apply (@grrcan X _ _ (a * b)).
  change (-a * b + a * b = - (a * b) + a * b).
  rewrite (ringlinvax1 X _). rewrite <- (ringrdistr X _ _ _).
  rewrite (ringlinvax1 X _). rewrite (ringmult0x X _).
  apply idpath.
Qed.

Lemma ringrmultminus (X : ring) (a b : X) : a * -b = -(a * b).
Proof.
  intros. apply (@grrcan X _ _ (a * b)).
  change (a * (- b) + a * b = - (a * b) + a * b).
  rewrite (ringlinvax1 X _). rewrite <- (ringldistr X _ _ _).
  rewrite (ringlinvax1 X _). rewrite (ringmultx0 X _).
  apply idpath.
Qed.

Lemma ringmultminusminus (X : ring) (a b : X) : -a * -b = a * b.
Proof.
  intros. apply (@grrcan X _ _ (- a * b)). simpl.
  rewrite <- (ringldistr X _ _ (- a)).
  rewrite <- (ringrdistr X _ _ b).
  rewrite (ringlinvax1 X b). rewrite (ringrinvax1 X a).
  rewrite (ringmult0x X _). rewrite (ringmultx0 X _).
  apply idpath.
Qed.

Lemma ringminusminus (X : ring) (a : X) : --a = a.
Proof. intros. apply (grinvinv X a). Defined.

Definition ringinvmaponpathsminus (X : ring) {a b : X} : -a = -b → a = b := grinvmaponpathsinv X.


(** **** Relations compatible with the additive structure on rings *)

Definition ringfromgt0 (X : ring) {R : hrel X} (is0 : @isbinophrel X R)
           {x : X} (is : R x 0) : R 0 (- x) := grfromgtunel X is0 is.

Definition ringtogt0 (X : ring) {R : hrel X} (is0 : @isbinophrel X R) {x : X}
           (is : R 0 (- x)) : R x 0 := grtogtunel X is0 is.

Definition ringfromlt0 (X : ring) {R : hrel X} (is0 : @isbinophrel X R) {x : X}
           (is : R 0 x) : R (- x) 0 := grfromltunel X is0 is.

Definition ringtolt0 (X : ring) {R : hrel X} (is0 : @isbinophrel X R) {x : X}
           (is : R (- x) 0) : R 0 x := grtoltunel X is0 is.


(** **** Relations compatible with the multiplicative structure on rings *)

Definition isringmultgt (X : ring) (R : hrel X) : UU := ∏ a b, R a 0 → R b 0 → R (a * b) 0.

Lemma ringmultgt0lt0 (X : ring) {R : hrel X} (is0 : @isbinophrel X R) (is : isringmultgt X R) {x y : X}
      (isx : R x 0) (isy : R 0 y) : R 0 (x * y).
Proof.
  intros.
  set (isy' := grfromltunel X is0 isy).
  assert (r := is _ _ isx isy').
  change (pr1 (R (x * (- y)) 0)) in r.
  rewrite (ringrmultminus X _ _) in r.
  assert (r' := grfromgtunel X is0 r).
  change (pr1 (R 0 (- - (x * y)))) in r'.
  rewrite (ringminusminus X (x * y)) in r'.
  apply r'.
Qed.

Lemma ringmultlt0gt0 (X : ring) {R : hrel X} (is0 : @isbinophrel X R) (is : isringmultgt X R) {x y : X}
      (isx : R 0 x) (isy : R y 0) : R 0 (x * y).
Proof.
  intros.
  set (isx' := grfromltunel X is0 isx).
  assert (r := is _ _ isx' isy).
  change (pr1 (R ((- x) * y) 0)) in r.
  rewrite (ringlmultminus X _ _) in r.
  assert (r' := grfromgtunel X is0 r).
  change (pr1 (R 0 (- - (x * y)))) in r'.
  rewrite (ringminusminus X (x * y)) in r'.
  apply r'.
Qed.

Lemma ringmultlt0lt0 (X : ring) {R : hrel X} (is0 : @isbinophrel X R) (is : isringmultgt X R) {x y : X}
      (isx : R 0 x) (isy : R 0 y) : R (x * y) 0.
Proof.
  intros.
  set (rx := ringfromlt0 _ is0 isx).
  assert (ry := ringfromlt0 _ is0 isy).
  assert (int := is _ _ rx ry).
  rewrite (ringmultminusminus X _ _) in int.
  apply int.
Qed.

Lemma isringmultgttoislringmultgt (X : ring) {R : hrel X} (is0 : @isbinophrel X R)
      (is : isringmultgt X R) : ∏ a b c : X, R c 0 → R a b → R (c * a) (c * b).
Proof.
  intros a b c rc0 rab.
  set (rab':= (pr2 is0) _ _ (- b) rab). clearbody rab'.
  change (pr1 (R (a - b) (b - b))) in rab'.
  rewrite (ringrinvax1 X b) in rab'.
  set (r' := is _ _ rc0 rab'). clearbody r'.
  set (r'' := (pr2 is0) _ _ (c * b) r').  clearbody r''.
  change (pr1 (R (c * (a - b) + c * b) (0 + c * b))) in r''.
  rewrite (ringlunax1 X _) in r''.
  rewrite <- (ringldistr X _ _ c) in r''.
  rewrite (ringassoc1 X a _ _) in r''.
  rewrite (ringlinvax1 X b) in r''.
  rewrite (ringrunax1 X _) in r''.
  apply r''.
Qed.

Lemma islringmultgttoisringmultgt (X : ring) {R : hrel X}
      (is : ∏ a b c : X, R c 0 → R a b → R (c * a) (c * b)) : isringmultgt X R.
Proof.
  intros. intros a b ra rb.
  set (int := is b 0 a ra rb). clearbody int. rewrite (ringmultx0 X _) in int.
  apply int.
Qed.

Lemma isringmultgttoisrringmultgt (X : ring) {R : hrel X} (is0 : @isbinophrel X R)
      (is : isringmultgt X R) : ∏ a b c : X, R c 0 → R a b → R (a * c) (b * c).
Proof.
  intros a b c rc0 rab.
  set (rab' := (pr2 is0) _ _ (- b) rab). clearbody rab'.
  change (pr1 (R (a - b) (b - b))) in rab'.
  rewrite (ringrinvax1 X b) in rab'.
  set (r' := is _ _ rab' rc0). clearbody r'.
  set (r'' :=  (pr2 is0) _ _ (b * c) r'). clearbody r''.
  change (pr1 (R ((a - b) * c + b * c) (0 + b * c))) in r''.
  rewrite (ringlunax1 X _) in r''.
  rewrite <- (ringrdistr X _ _ c) in r''.
  rewrite (ringassoc1 X a _ _) in r''.
  rewrite (ringlinvax1 X b) in r''.
  rewrite (ringrunax1 X _) in r''.
  apply r''.
Qed.

Lemma isrringmultgttoisringmultgt (X : ring) {R : hrel X}
      (is1 : ∏ a b c : X, R c 0 → R a b → R (a * c) (b * c)) : isringmultgt X R.
Proof.
  intros. intros a b ra rb.
  set (int := is1 _ _ _ rb ra). clearbody int.
  rewrite (ringmult0x X _) in int. apply int.
Qed.

Lemma isringmultgtaspartbinophrel (X : ring) (R : hrel X) (is0 : @isbinophrel X R) :
  (isringmultgt X R) <-> (@ispartbinophrel (ringmultmonoid X) (λ a, R a 0) R).
Proof.
  intros. split.
  - intro ism. split.
    + apply (isringmultgttoislringmultgt X is0 ism).
    + apply (isringmultgttoisrringmultgt X is0 ism).
  - intro isp. apply (islringmultgttoisringmultgt X (pr1 isp)).
Defined.

Lemma isringmultgttoisrigmultgt (X : ring) {R : hrel X} (is0 : @isbinophrel X R)
      (is : isringmultgt X R) : isrigmultgt X R.
Proof.
  intros. set (rer := abmonoidrer X). simpl in rer.
  intros a b c d rab rcd.
  assert (intab : R (a - b) 0).
  {
    induction (ringrinvax1 X b).
    apply ((pr2 is0) _ _ (- b)).
    apply rab.
  }
  assert (intcd : R (c - d) 0).
  {
    induction (ringrinvax1 X d).
    apply ((pr2 is0) _ _ (- d)).
    apply rcd.
  }
  set (int := is _ _ intab intcd). rewrite (ringrdistr X _ _ _) in int.
  rewrite (ringldistr X _ _ _) in int. rewrite (ringldistr X _ _ _) in int.
  set (int' := (pr2 is0) _ _ (a * d + b * c) int). clearbody int'.
  simpl in int'.
  rewrite (ringlunax1 _) in int'. rewrite (ringcomm1 X (- b * c) _) in int'.
  rewrite (rer _ (a * - d) _ _) in int'.
  rewrite (ringassoc1 X  _ (a * - d + - b * c) _) in int'.
  rewrite (rer _ _ (a * d) _) in int'.
  rewrite <- (ringldistr X _ _ a) in int'.
  rewrite (ringlinvax1 X d) in int'.
  rewrite (ringmultx0 X _) in int'.
  rewrite <- (ringrdistr X _ _ c) in int'.
  rewrite (ringlinvax1 X b) in int'.
  rewrite (ringmult0x X _) in int'.
  rewrite (ringrunax1 X _) in int'.
  rewrite (ringrunax1 X _) in int'.
  rewrite (ringmultminusminus X b d) in int'.
  apply int'.
Qed.

Lemma isrigmultgttoisringmultgt (X : ring) {R : hrel X} (is : isrigmultgt X R) : isringmultgt X R.
Proof.
  intros. intros a b ra0 rb0. set (is' := is _ _ _ _ ra0 rb0). simpl in is'.
  fold (pr1ring) in is'. rewrite 2? (ringmult0x X _) in is'.
  rewrite (ringmultx0 X _) in is'. rewrite 2? (ringrunax1 X _) in is'.
  exact is'.
Qed.

(** **** Relations "inversely compatible" with the multiplicative structure on rings *)


Definition isinvringmultgt (X : ring) (R : hrel X) : UU :=
  (∏ a b, R (a * b) 0 → R a 0 → R b 0) ×
  (∏ a b, R (a * b) 0 → R b 0 → R a 0).

Lemma isinvringmultgttoislinvringmultgt (X : ring) {R : hrel X} (is0 : @isbinophrel X R)
      (is : isinvringmultgt X R) : ∏ a b c : X, R c 0 → R (c * a) (c * b) → R a b.
Proof.
  intros a b c rc0 r.
  set (rab':= (pr2 is0) _ _ (c * - b) r).
  clearbody rab'.
  change (pr1 (R (c * a + c * - b) (c * b + c * - b))) in rab'.
  rewrite <- (ringldistr X _ _ c) in rab'.
  rewrite <- (ringldistr X _ _ c) in rab'.
  rewrite (ringrinvax1 X b) in rab'. rewrite (ringmultx0 X _) in rab'.
  set (r' := (pr1 is) _ _ rab' rc0). clearbody r'.
  set (r'' := (pr2 is0) _ _ b r'). clearbody r''.
  change (pr1 (R (a - b + b) (0 + b))) in r''.
  rewrite (ringlunax1 X _) in r''. rewrite (ringassoc1 X a _ _) in r''.
  rewrite (ringlinvax1 X b) in r''. rewrite (ringrunax1 X _) in r''.
  apply r''.
Qed.

Lemma isinvringmultgttoisrinvringmultgt (X : ring) {R : hrel X} (is0 : @isbinophrel X R)
      (is : isinvringmultgt X R) : ∏ a b c : X, R c 0 → R (a * c) (b * c) → R a b.
Proof.
  intros a b c rc0 r.
  set (rab':= (pr2 is0) _ _ (- b * c) r). clearbody rab'.
  change (pr1 (R (a * c + - b * c) (b * c + - b * c))) in rab'.
  rewrite <- (ringrdistr X _ _ c) in rab'.
  rewrite <- (ringrdistr X _ _ c) in rab'.
  rewrite (ringrinvax1 X b) in rab'.
  rewrite (ringmult0x X _) in rab'.
  set (r' := (pr2 is) _ _ rab' rc0).
  clearbody r'. set (r'' := (pr2 is0) _ _ b r').
  clearbody r''. change (pr1 (R (a - b + b) (0 + b))) in r''.
  rewrite (ringlunax1 X _) in r''. rewrite (ringassoc1 X a _ _) in r''.
  rewrite (ringlinvax1 X b) in r''. rewrite (ringrunax1 X _) in r''.
  apply r''.
Qed.

Lemma islrinvringmultgttoisinvringmultgt (X : ring) {R : hrel X}
      (isl : ∏ a b c : X, R c 0 → R (c * a) (c * b) → R a b)
      (isr : ∏ a b c : X, R c 0 → R (a * c) (b * c) → R a b) : isinvringmultgt X R.
Proof.
  intros. split.
  - intros a b rab ra.
    rewrite <- (ringmultx0 X a) in rab.
    apply (isl _ _ _ ra rab).
  - intros a b rab rb.
    rewrite <- (ringmult0x X b) in rab.
    apply (isr _ _ _ rb rab).
Qed.

Lemma isinvringmultgtaspartinvbinophrel (X : ring) (R : hrel X) (is0 : @isbinophrel X R) :
  (isinvringmultgt X R) <-> (@ispartinvbinophrel (ringmultmonoid X) (λ a, R a 0) R).
Proof.
  intros. split.
  - intro ism. split.
    + apply (isinvringmultgttoislinvringmultgt X is0 ism).
    + apply (isinvringmultgttoisrinvringmultgt X is0 ism).
  - intro isp.
    apply (islrinvringmultgttoisinvringmultgt X (pr1 isp) (pr2 isp)).
Defined.

Lemma isinvringmultgttoisinvrigmultgt (X : ring) {R : hrel X}
      (is0 : @isbinophrel X R) (is : isinvringmultgt X R) : isinvrigmultgt X R.
Proof.
  intros. set (rer := abmonoidrer X). simpl in rer. split.
  - intros a b c d r rab.
    set (r' := (pr2 is0) _ _ (a * - d + - b * c) r). clearbody r'. simpl in r'.
    rewrite (rer _ (b * c) _ _) in r'.
    rewrite <- (ringldistr X _ _ a) in r'.
    rewrite <- (ringrdistr X _ _ c) in r'.
    rewrite (ringrinvax1 X d) in r'.
    rewrite (ringrinvax1 X b) in r'.
    rewrite (ringmult0x X _) in r'.
    rewrite (ringmultx0 X _) in r'.
    rewrite (ringlunax1 X) in r'.
    rewrite (rer _ (b * d) _ _) in r'.
    rewrite <- (ringldistr X _ _ a) in r'.
    simpl in r'.
    fold pr1ring in r'.     (* fold stopped working *)
    change (pr1 X) with (pr1ring X) in r'.
    rewrite <- (ringmultminusminus X b d) in r'.
    rewrite <- (ringldistr X _ _ (- b)) in r'.
    rewrite (ringcomm1 X _ c) in r'.
    rewrite <- (ringrdistr X _ _ _) in r'.
    set (rab' := (pr2 is0) _ _ (- b) rab). clearbody rab'.
    simpl in rab'. rewrite (ringrinvax1 X b) in rab'.
    set (rcd' := (pr1 is) _ _ r' rab').
    set (rcd'' := (pr2 is0) _ _ d rcd'). simpl in rcd''.
    rewrite (ringassoc1 _ _ _) in rcd''. rewrite (ringlinvax1 X _) in rcd''.
    rewrite (ringlunax1 X _) in rcd''. rewrite (ringrunax1 X _) in rcd''.
    apply rcd''.
  - intros a b c d r rcd.
    set (r' := (pr2 is0) _ _ (a * - d + - b * c) r). clearbody r'. simpl in r'.
    rewrite (rer _ (b * c) _ _) in r'.
    rewrite <- (ringldistr X _ _ a) in r'.
    rewrite <- (ringrdistr X _ _ c) in r'.
    rewrite (ringrinvax1 X d) in r'.
    rewrite (ringrinvax1 X b) in r'.
    rewrite (ringmult0x X _) in r'.
    rewrite (ringmultx0 X _) in r'.
    rewrite (ringlunax1 X) in r'.
    rewrite (rer _ (b * d) _ _) in r'.
    rewrite <- (ringldistr X _ _ a) in r'.
    simpl in r'.
    fold pr1ring in r'. (* fold stopped working *)
    change (pr1 X) with (pr1ring X) in r'.
    rewrite <- (ringmultminusminus X b d) in r'.
    rewrite <- (ringldistr X _ _ (- b)) in r'.
    rewrite (ringcomm1 X _ c) in r'.
    rewrite <- (ringrdistr X _ _ _) in r'.
    set (rcd' := (pr2 is0) _ _ (- d) rcd). clearbody rcd'. simpl in rcd'.
    rewrite (ringrinvax1 X d) in rcd'.
    set (rab' := (pr2 is) _ _ r' rcd').
    set (rab'' := (pr2 is0) _ _ b rab'). simpl in rab''.
    rewrite (ringassoc1 _ _ _) in rab''.
    rewrite (ringlinvax1 X _) in rab''.
    rewrite (ringlunax1 X _) in rab''.
    rewrite (ringrunax1 X _) in rab''.
    apply rab''.
Qed.


(** **** Relations on rings and ring homomorphisms *)

Lemma ringaddhrelandfun {X Y : ring} (f : ringfun X Y) (R : hrel Y) (isr : @isbinophrel Y R) :
  @isbinophrel X (λ x x', R (f x) (f x')).
Proof. intros. apply (binophrelandfun (ringaddfun f) R isr). Defined.

Lemma ringmultgtandfun {X Y : ring} (f : ringfun X Y) (R : hrel Y) (isr : isringmultgt Y R) :
  isringmultgt X (λ x x', R (f x) (f x')).
Proof.
  intros. intros a b ra rb.
  set (ax0 := (pr2 (pr1 (pr2 f))) : (f 0) = 0).
  set (ax1 := (pr1 (pr2 (pr2 f))) : ∏ a b, f (a * b) = f a * f b).
  rewrite ax0 in ra. rewrite ax0 in rb.
  rewrite ax0. rewrite (ax1 _ _).
  apply (isr _ _ ra rb).
Defined.

Lemma ringinvmultgtandfun {X Y : ring} (f : ringfun X Y) (R : hrel Y) (isr : isinvringmultgt Y R) :
  isinvringmultgt X (λ x x', R (f x) (f x')).
Proof.
  intros.
  set (ax0 := (pr2 (pr1 (pr2 f))) : (f 0) = 0).
  set (ax1 := (pr1 (pr2 (pr2 f))) : ∏ a b, f (a * b) = f a * f b).
  split.
  - intros a b rab ra.
    rewrite ax0 in ra. rewrite ax0 in rab.
    rewrite ax0. rewrite (ax1 _ _) in rab.
    apply ((pr1 isr) _ _ rab ra).
  - intros a b rab rb. rewrite ax0 in rb.
    rewrite ax0 in rab. rewrite ax0.
    rewrite (ax1 _ _) in rab.
    apply ((pr2 isr) _ _ rab rb).
Defined.

Close Scope ring_scope.


(** **** Subobjects *)

Definition issubring {X : ring} (A : hsubtype X) : UU :=
  (@issubgr X A) ×
  (@issubmonoid (ringmultmonoid X) A).

Lemma isapropissubring {X : ring} (A : hsubtype X) : isaprop (issubring A).
Proof.
  intros. apply (isofhleveldirprod 1).
  - apply isapropissubgr.
  - apply isapropissubmonoid.
Defined.

Definition subring (X : ring) : UU := ∑ (A : hsubtype X), issubring A.

Definition make_gsubring {X : ring}
  (t : hsubtype X)
  (H : issubring t)
  : subring X
  := t ,, H.

Definition pr1subring (X : ring) : @subring X → hsubtype X :=
  @pr1 _ (λ A : hsubtype X, issubring A).

Definition subringtosubsetswith2binop (X : ring) : subring X → @subsetswith2binop X :=
  λ A, make_subsetswith2binop
              (pr1 A) (pr1 (pr1 (pr1 (pr2 A))) ,, pr1 (pr2 (pr2 A))).
Coercion subringtosubsetswith2binop : subring >-> subsetswith2binop.

Definition addsubgr {X : ring} : subring X → @subgr X :=
  λ A, @make_subgr X (pr1 A) (pr1 (pr2 A)).

Definition multsubmonoid {X : ring} : subring X → @submonoid (ringmultmonoid X) :=
  λ A, @make_submonoid (ringmultmonoid X) (pr1 A) (pr2 (pr2 A)).

Lemma isringcarrier {X : ring} (A : subring X) : isringops (@op1 A) (@op2 A).
Proof.
  intros.
  exists (isabgrcarrier (addsubgr A) ,, ismonoidcarrier (multsubmonoid A)).
  split.
  - intros a b c.
    apply (invmaponpathsincl _ (isinclpr1carrier A)).
    simpl. apply ringldistr.
  - intros a b c.
    apply (invmaponpathsincl _ (isinclpr1carrier A)).
    simpl. apply ringrdistr.
Defined.

Definition carrierofasubring (X : ring) (A : subring X) : ring.
Proof. intros. exists A. apply isringcarrier. Defined.
Coercion carrierofasubring : subring >-> ring.


(** **** Quotient objects *)

Definition ringeqrel {X : ring} := @twobinopeqrel X.
Identity Coercion id_ringeqrel : ringeqrel >-> twobinopeqrel.

Definition ringaddabgreqrel {X : ring} (R : @ringeqrel X) :
  @binopeqrel X := @make_binopeqrel X (pr1 R) (pr1 (pr2 R)).

Definition ringmultmonoideqrel {X : ring} (R : @ringeqrel X) :
  @binopeqrel (ringmultmonoid X) := @make_binopeqrel (ringmultmonoid X) (pr1 R) (pr2 (pr2 R)).

Lemma isringquot {X : ring} (R : @ringeqrel X) :
  isringops (@op1 (setwith2binopquot R)) (@op2 (setwith2binopquot R)).
Proof.
  intros.
  exists (isabgrquot (ringaddabgreqrel R) ,, ismonoidquot (ringmultmonoideqrel R)).
  simpl.
  set (opp1 := @op1 (setwith2binopquot R)).
  set (opp2 := @op2 (setwith2binopquot R)).
  split.
  - unfold isldistr.
    apply (setquotuniv3prop
             R (λ x x' x'', make_hProp _ (setproperty (setwith2binopquot R) (opp2  x'' (opp1 x x'))
                                                      (opp1 (opp2 x'' x) (opp2 x'' x'))))).
    intros x x' x''. apply (maponpaths (setquotpr R) (ringldistr X x x' x'')).
  - unfold isrdistr.
    apply (setquotuniv3prop
             R (λ x x' x'', make_hProp _ (setproperty (setwith2binopquot R) (opp2  (opp1 x x') x'')
                                                      (opp1 (opp2 x x'') (opp2 x' x''))))).
    intros x x' x''. apply (maponpaths (setquotpr R) (ringrdistr X x x' x'')).
Defined.

Definition ringquot {X : ring} (R : @ringeqrel X) : ring :=
  @make_ring (setwith2binopquot R) (isringquot R).


(** **** Direct products *)

Lemma isringdirprod (X Y : ring) :
  isringops (@op1 (setwith2binopdirprod X Y)) (@op2 (setwith2binopdirprod X Y)).
Proof.
  intros.
  exists (isabgrdirprod X Y ,, ismonoiddirprod (ringmultmonoid X) (ringmultmonoid Y)).
  simpl. split.
  - intros xy xy' xy''. unfold setwith2binopdirprod.
    unfold op1. unfold op2. simpl.
    apply pathsdirprod.
    + apply (ringldistr X).
    + apply (ringldistr Y).
  - intros xy xy' xy''. unfold setwith2binopdirprod.
    unfold op1. unfold op2. simpl.
    apply pathsdirprod.
    + apply (ringrdistr X).
    + apply (ringrdistr Y).
Defined.

Definition ringdirprod (X Y : ring) : ring := @make_ring (setwith2binopdirprod X Y) (isringdirprod X Y).

(** **** Opposite rings *)

Local Open Scope rig.

(** We just need to reuse and rearrange the opposite rig *)
Definition opposite_ring (X : ring) : ring.
Proof.
  refine (pr1 (X⁰),, _).
  split.
  - split.
    apply make_isabgrop.
    * exact (pr1 (rigop1axs (X⁰)),, pr2 (pr1 (ringop1axs X))).
    * exact (pr2 (ringop1axs X)).
    * exact (rigop2axs (X⁰)).
  - exact (rigdistraxs (X⁰)).
Defined.

Notation "X ⁰" := (opposite_ring X) (at level 12) : ring_scope.

Local Close Scope rig.

(** **** Ring of differences associated with a rig *)

Local Open Scope rig_scope.

Definition rigtoringaddabgr (X : rig) : abgr := abgrdiff (rigaddabmonoid X).

Definition rigtoringcarrier (X : rig) : hSet := pr1 (pr1 (rigtoringaddabgr X)).

Definition rigtoringop1int (X : rig) : binop (X × X) :=
  λ x x', pr1 x + pr1 x' ,, pr2 x + pr2 x'.

Definition rigtoringop1 (X : rig) : binop (rigtoringcarrier X) := @op (rigtoringaddabgr X).

Definition rigtoringop1axs (X : rig) : isabgrop (rigtoringop1 X) := pr2 (rigtoringaddabgr X).

Definition rigtoringunel1 (X : rig) : rigtoringcarrier X := unel (rigtoringaddabgr X).

Definition eqrelrigtoring (X : rig) : eqrel (X × X) := eqrelabgrdiff (rigaddabmonoid X).

Definition rigtoringop2int (X : rig) : binop (X × X) :=
  λ xx xx' : X × X,
   pr1 xx * pr1 xx' + pr2 xx * pr2 xx' ,, pr1 xx * pr2 xx' + pr2 xx * pr1 xx'.

Definition rigtoringunel2int (X : rig) : X × X := 1 ,, 0.

Lemma rigtoringop2comp (X : rig) :
  iscomprelrelfun2 (eqrelrigtoring X) (eqrelrigtoring X) (rigtoringop2int X).
Proof.
  intros. apply iscomprelrelfun2if.
  - intros xx xx' aa. simpl.
    apply @hinhfun. intro tt1. induction tt1 as [ x0 e ].
    exists (x0 * pr2 aa + x0 * pr1 aa).
    set (rd := rigrdistr X). set (cm1 := rigcomm1 X).
    set (as1 := rigassoc1 X). set (rr := abmonoidoprer (rigop1axs X)).

    rewrite (cm1 (pr1 xx * pr1 aa) (pr2 xx  * pr2 aa)).
    rewrite (rr _ (pr1 xx * pr1 aa) (pr1 xx' * pr2 aa) _).
    rewrite (cm1 (pr2 xx * pr2 aa) (pr1 xx' * pr2 aa)).
    induction (rd (pr1 xx) (pr2 xx') (pr1 aa)).
    induction (rd (pr1 xx') (pr2 xx) (pr2 aa)).
    rewrite (rr ((pr1 xx' + pr2 xx) * pr2 aa)
                ((pr1 xx + pr2 xx') * pr1 aa) (x0 * pr2 aa) (x0 * pr1 aa)).
    induction (rd (pr1 xx' + pr2 xx) x0 (pr2 aa)).
    induction (rd (pr1 xx + pr2 xx') x0 (pr1 aa)).

    rewrite (cm1 (pr1 xx' * pr1 aa) (pr2 xx'  * pr2 aa)).
    rewrite (rr _ (pr1 xx' * pr1 aa) (pr1 xx * pr2 aa) _).
    rewrite (cm1 (pr2 xx' * pr2 aa) (pr1 xx * pr2 aa)).
    induction (rd (pr1 xx') (pr2 xx) (pr1 aa)).
    induction (rd (pr1 xx) (pr2 xx') (pr2 aa)).
    rewrite (rr ((pr1 xx + pr2 xx') * pr2 aa)
                ((pr1 xx' + pr2 xx) * pr1 aa) (x0 * pr2 aa) (x0 * pr1 aa)).
    induction (rd (pr1 xx + pr2 xx') x0 (pr2 aa)).
    induction (rd (pr1 xx' + pr2 xx) x0 (pr1 aa)).
    induction e. apply idpath.

  - intros aa xx xx'. simpl. apply @hinhfun. intro tt1.
    induction tt1 as [ x0 e ]. exists (pr1 aa * x0 + pr2 aa * x0).
    set (ld := rigldistr X). set (cm1 := rigcomm1 X).
    set (as1 := rigassoc1 X). set (rr := abmonoidoprer (rigop1axs X)).

    rewrite (rr _ (pr2 aa * pr2 xx) (pr1 aa * pr2 xx') _).
    induction (ld (pr1 xx) (pr2 xx') (pr1 aa)).
    induction (ld (pr2 xx) (pr1 xx') (pr2 aa)).
    rewrite (rr _ (pr2 aa * (pr2 xx + pr1 xx')) (pr1 aa * x0) _).
    induction (ld (pr1 xx + pr2 xx') x0 (pr1 aa)).
    induction (ld (pr2 xx + pr1 xx') x0 (pr2 aa)).

    rewrite (rr _ (pr2 aa * pr2 xx') (pr1 aa * pr2 xx) _).
    induction (ld (pr1 xx') (pr2 xx) (pr1 aa)).
    induction (ld (pr2 xx') (pr1 xx) (pr2 aa)).
    rewrite (rr _ (pr2 aa * (pr2 xx' + pr1 xx)) (pr1 aa * x0) _).
    induction (ld (pr1 xx' + pr2 xx) x0 (pr1 aa)).
    induction (ld (pr2 xx' + pr1 xx) x0 (pr2 aa)).
    rewrite (cm1 (pr2 xx) (pr1 xx')).
    rewrite (cm1 (pr2 xx') (pr1 xx)).
    induction e. apply idpath.
Qed.

Definition rigtoringop2 (X : rig) : binop (rigtoringcarrier X) :=
  setquotfun2 (eqrelrigtoring X) (eqrelrigtoring X) (rigtoringop2int X) (rigtoringop2comp X).

Lemma rigtoringassoc2 (X : rig) : isassoc (rigtoringop2 X).
Proof.
  unfold isassoc.
  apply (setquotuniv3prop _ (λ x x' x'', _ = _)).
  intros x x' x''.
  change (setquotpr (eqrelrigtoring X) (rigtoringop2int X (rigtoringop2int X x x') x'')
        = setquotpr (eqrelrigtoring X) (rigtoringop2int X x (rigtoringop2int X x' x''))).
  apply (maponpaths (setquotpr (eqrelrigtoring X))). unfold rigtoringop2int.
  simpl.
  set (rd := rigrdistr X). set (ld := rigldistr X).
  set (cm1 := rigcomm1 X).
  set (as1 := rigassoc1 X). set (as2 := rigassoc2 X).
  set (rr := abmonoidoprer (rigop1axs X)). apply pathsdirprod.

  rewrite (rd _ _ (pr1 x'')). rewrite (rd _ _ (pr2 x'')).
  rewrite (ld _ _ (pr1 x)). rewrite (ld _ _ (pr2 x)).
  induction (as2 (pr1 x) (pr1 x') (pr1 x'')).
  induction (as2 (pr1 x) (pr2 x') (pr2 x'')).
  induction (as2 (pr2 x) (pr1 x') (pr2 x'')).
  induction (as2 (pr2 x) (pr2 x') (pr1 x'')).
  induction (cm1 (pr2 x * pr2 x' * pr1 x'') (pr2 x * pr1 x' * pr2 x'')).
  rewrite (rr _ (pr2 x * pr2 x' * pr1 x'') (pr1 x * pr2 x' * pr2 x'') _).
  apply idpath.

  rewrite (rd _ _ (pr1 x'')). rewrite (rd _ _ (pr2 x'')).
  rewrite (ld _ _ (pr1 x)). rewrite (ld _ _ (pr2 x)).
  induction (as2 (pr1 x) (pr1 x') (pr2 x'')).
  induction (as2 (pr1 x) (pr2 x') (pr1 x'')).
  induction (as2 (pr2 x) (pr1 x') (pr1 x'')).
  induction (as2 (pr2 x) (pr2 x') (pr2 x'')).
  induction (cm1 (pr2 x * pr2 x' * pr2 x'') (pr2 x * pr1 x' * pr1 x'')).
  rewrite (rr _ (pr1 x * pr2 x' * pr1 x'') (pr2 x * pr2 x' * pr2 x'') _).
  apply idpath.
Qed.

Definition rigtoringunel2 (X : rig) : rigtoringcarrier X :=
  setquotpr (eqrelrigtoring X) (rigtoringunel2int X).

Lemma rigtoringlunit2 (X : rig) : islunit (rigtoringop2 X) (rigtoringunel2 X).
Proof.
  unfold islunit.
  apply (setquotunivprop _ (λ x, _ = _)).
  intro x.
  change (setquotpr (eqrelrigtoring X) (rigtoringop2int X (rigtoringunel2int X) x)
        = setquotpr (eqrelrigtoring X) x).
  apply (maponpaths (setquotpr (eqrelrigtoring X))).
  unfold rigtoringop2int. simpl. induction x as [ x1 x2 ]. simpl.
  set (lu2 := riglunax2 X). set (ru1 := rigrunax1 X). set (m0x := rigmult0x X).
  apply pathsdirprod.
  - rewrite (lu2 x1). rewrite (m0x x2). apply (ru1 x1).
  - rewrite (lu2 x2). rewrite (m0x x1). apply (ru1 x2).
Qed.

Lemma rigtoringrunit2 (X : rig) : isrunit (rigtoringop2 X) (rigtoringunel2 X).
Proof.
  unfold isrunit.
  apply (setquotunivprop _ (λ x, _ = _)).
  intro x.
  change (setquotpr (eqrelrigtoring X) (rigtoringop2int X x (rigtoringunel2int X))
        = setquotpr (eqrelrigtoring X) x).
  apply (maponpaths (setquotpr (eqrelrigtoring X))). unfold rigtoringop2int.
  simpl. induction x as [ x1 x2 ]. simpl.
  set (ru1 := rigrunax1 X). set (ru2 := rigrunax2 X).
  set (lu1 := riglunax1 X). set (mx0 := rigmultx0 X).
  apply pathsdirprod.
  - rewrite (ru2 x1). rewrite (mx0 x2). apply (ru1 x1).
  - rewrite (ru2 x2). rewrite (mx0 x1). apply (lu1 x2).
Qed.

Definition rigtoringisunit (X : rig) : isunit (rigtoringop2 X) (rigtoringunel2 X) :=
  rigtoringlunit2 X ,, rigtoringrunit2 X.

Definition rigtoringisunital (X : rig) : isunital (rigtoringop2 X) :=
  rigtoringunel2 X ,, rigtoringisunit X.

Definition rigtoringismonoidop2 (X : rig) : ismonoidop (rigtoringop2 X) :=
  rigtoringassoc2 X ,, rigtoringisunital X.

Lemma rigtoringldistr (X : rig) : isldistr (rigtoringop1 X) (rigtoringop2 X).
Proof.
  unfold isldistr.
  apply (setquotuniv3prop _ (λ x x' x'', _ = _)).
  intros x x' x''.
  change (setquotpr (eqrelrigtoring X) (rigtoringop2int X x'' (rigtoringop1int X x x'))
        = setquotpr _ (rigtoringop1int X (rigtoringop2int X x'' x) (rigtoringop2int X x'' x'))).
  apply (maponpaths (setquotpr (eqrelrigtoring X))).
  unfold rigtoringop1int. unfold rigtoringop2int. simpl.
  set (ld := rigldistr X). set (cm1 := rigcomm1 X).
  set (rr := abmonoidoprer (rigop1axs X)).
  apply pathsdirprod.
  - rewrite (ld _ _ (pr1 x'')). rewrite (ld _ _ (pr2 x'')).
    apply (rr _ (pr1 x'' * pr1 x') (pr2 x'' * pr2 x) _).
  - rewrite (ld _ _ (pr1 x'')). rewrite (ld _ _ (pr2 x'')).
    apply (rr _ (pr1 x'' * pr2 x') (pr2 x'' * pr1 x) _).
Qed.

Lemma rigtoringrdistr (X : rig) : isrdistr (rigtoringop1 X) (rigtoringop2 X).
Proof.
  unfold isrdistr.
  apply (setquotuniv3prop _ (λ x x' x'', _ = _)).
  intros x x' x''.
  change (setquotpr (eqrelrigtoring X) (rigtoringop2int X (rigtoringop1int X x x') x'')
        = setquotpr _ (rigtoringop1int X (rigtoringop2int X x x'') (rigtoringop2int X x' x''))).
  apply (maponpaths (setquotpr (eqrelrigtoring X))).
  unfold rigtoringop1int. unfold rigtoringop2int. simpl.
  set (rd := rigrdistr X). set (cm1 := rigcomm1 X).
  set (rr := abmonoidoprer (rigop1axs X)).
  apply pathsdirprod.
  - rewrite (rd _ _ (pr1 x'')). rewrite (rd _ _ (pr2 x'')).
    apply (rr _ (pr1 x' * pr1 x'') (pr2 x * pr2 x'') _).
  - rewrite (rd _ _ (pr1 x'')). rewrite (rd _ _ (pr2 x'')).
    apply (rr _ (pr1 x' * pr2 x'') (pr2 x * pr1 x'') _).
Qed.

Definition rigtoringdistr (X : rig) : isdistr (rigtoringop1 X) (rigtoringop2 X) :=
  rigtoringldistr X ,, rigtoringrdistr X.

Definition rigtoring (X : rig) : ring.
Proof.
  exists (@make_setwith2binop (rigtoringcarrier X) (rigtoringop1 X ,, rigtoringop2 X)).
  split.
  - apply (rigtoringop1axs X ,, rigtoringismonoidop2 X).
  - apply (rigtoringdistr X).
Defined.


(** **** Canonical homomorphism to the ring associated with a rig (ring of differences) *)

Definition toringdiff (X : rig) (x : X) : rigtoring X := setquotpr _ (x ,, 0).

Lemma isbinop1funtoringdiff (X : rig) : @isbinopfun (rigaddabmonoid X) (rigtoring X) (toringdiff X).
Proof.
  intros. unfold isbinopfun. intros x x'.
  apply (isbinopfuntoabgrdiff (rigaddabmonoid X) x x').
Qed.

Lemma isunital1funtoringdiff (X : rig) : (toringdiff X 0) = 0%ring.
Proof.
  apply idpath.
Qed.

Definition isaddmonoidfuntoringdiff (X : rig) :
  @ismonoidfun (rigaddabmonoid X) (rigtoring X) (toringdiff X) :=
  isbinop1funtoringdiff X ,, isunital1funtoringdiff X.

Lemma isbinop2funtoringdiff (X : rig) :
  @isbinopfun (rigmultmonoid X) (ringmultmonoid (rigtoring X)) (toringdiff X).
Proof.
  intros. unfold isbinopfun. intros x x'.
  change (setquotpr (eqrelrigtoring X) (x * x' ,, 0)
        = setquotpr _ (rigtoringop2int X (x ,, 0) (x' ,, 0))).
  apply (maponpaths (setquotpr _)). unfold rigtoringop2int. simpl.
  apply pathsdirprod.
  - rewrite (rigmultx0 X _). rewrite (rigrunax1 X _). apply idpath.
  - rewrite (rigmult0x X _). rewrite (rigmultx0 X _). rewrite (rigrunax1 X _).
    apply idpath.
Defined.

Lemma isunital2funtoringdiff  (X : rig) : (toringdiff X 1) = 1%ring.
Proof.
  apply idpath.
Qed.

Definition ismultmonoidfuntoringdiff (X : rig) :
  @ismonoidfun (rigmultmonoid X) (ringmultmonoid (rigtoring X)) (toringdiff X) :=
  isbinop2funtoringdiff X ,, isunital2funtoringdiff X.

Definition isrigfuntoringdiff (X : rig) : @isrigfun X (rigtoring X) (toringdiff X) :=
  isaddmonoidfuntoringdiff X ,, ismultmonoidfuntoringdiff X.

Definition isincltoringdiff (X : rig) (iscanc : ∏ x : X, @isrcancelable X (@op1 X) x) :
  isincl (toringdiff X) := isincltoabgrdiff (rigaddabmonoid X) iscanc.


(** **** Relations similar to "greater" or "greater or equal" on the ring associated with a rig *)

Definition rigtoringrel (X : rig) {R : hrel X} (is : @isbinophrel (rigaddabmonoid X) R) :
  hrel (rigtoring X) := abgrdiffrel (rigaddabmonoid X) is.

Lemma isringrigtoringmultgt (X : rig) {R : hrel X} (is0 : @isbinophrel (rigaddabmonoid X) R)
      (is : isrigmultgt X R) : isringmultgt (rigtoring X) (rigtoringrel X is0).
Proof.
  intros.
  set (assoc := rigassoc1 X). set (comm := rigcomm1 X).
  set (rer := (abmonoidrer (rigaddabmonoid X)) :
                ∏ a b c d : X, (a + b) + (c + d) = (a + c) + (b + d)).
  set (ld := rigldistr X). set (rd := rigrdistr X).
  assert (int : ∏ a b, isaprop (rigtoringrel X is0 a ringunel1 → rigtoringrel X is0 b ringunel1 →
                                rigtoringrel X is0 (a * b) ringunel1)).
  {
    intros a b.
    apply impred. intro.
    apply impred. intro.
    apply (pr2 _).
  }
  unfold isringmultgt.
  apply (setquotuniv2prop _ (λ a b, make_hProp _ (int a b))).

  intros xa1 xa2.
  change ((abgrdiffrelint (rigaddabmonoid X) R) xa1 (@rigunel1 X ,, @rigunel1 X) →
          (abgrdiffrelint (rigaddabmonoid X) R) xa2 (@rigunel1 X ,, @rigunel1 X) →
          (abgrdiffrelint (rigaddabmonoid X) R (@rigtoringop2int X xa1 xa2)
                          (@rigunel1 X ,, @rigunel1 X))).
  unfold abgrdiffrelint. simpl. apply hinhfun2. intros t22 t21.
  set (c2 := pr1 t21). set (c1 := pr1 t22).
  set (r1 := pr2 t21). set (r2 := pr2 t22).
  set (x1 := pr1 xa1). set (a1 := pr2 xa1).
  set (x2 := pr1 xa2). set (a2 := pr2 xa2).
  exists
  ((x1 * c2 + a1 * c2) + ((c1 * x2 + c1 * c2) + (c1 * a2 + c1 * c2))).
  change (pr1 (R (x1 * x2 + a1 * a2 + 0 +
                  ((x1 * c2 + a1 * c2) + ((c1 * x2 + c1 * c2) + (c1 * a2 + c1 * c2))))
                 (0 + (x1 * a2 + a1 * x2) +
                  (x1 * c2 + a1 * c2 + ((c1 * x2 + c1 * c2) + (c1 * a2 + c1 * c2)))))).
  rewrite (riglunax1 X _). rewrite (rigrunax1 X _).
  rewrite (assoc (x1 * c2) _ _).
  rewrite (rer _ (a1 * a2) _ _). rewrite (rer _ (a1 * x2) _ _).
  rewrite <- (assoc (a1 * a2) _ _).
  rewrite <- (assoc (a1 * x2) _ _).
  rewrite <- (assoc (x1 * x2 + _) _ _).
  rewrite <- (assoc (x1 * a2 + _) _ _).
  rewrite (rer _ (a1 * a2 + _) _ _). rewrite (rer _ (a1 * x2 + _) _ _).
  rewrite <- (ld _ _ x1). rewrite <- (ld _ _ x1).
  rewrite <- (ld _ _ c1). rewrite <- (ld _ _ c1).
  rewrite <- (ld _ _ a1). rewrite <- (ld _ _ a1).
  rewrite <- (rd _ _ (x2 + c2)).
  rewrite <- (rd _ _ (a2 + c2)).
  rewrite (comm (a1 * _) _).  rewrite (rer _ (c1 * _) _ _).
  rewrite <- (rd _ _ (x2 + c2)).
  rewrite <- (rd _ _ (a2 + c2)).
  clearbody r1. clearbody r2.
  change (pr1 (R (x2 + 0 + c2) (0 + a2 + c2))) in r1.
  change (pr1 (R (x1 + 0 + c1) (0 + a1 + c1))) in r2.
  rewrite (rigrunax1 X _) in r1. rewrite (riglunax1 X _) in r1.
  rewrite (rigrunax1 X _) in r2. rewrite (riglunax1 X _) in r2.
  rewrite (comm c1 a1).
  apply (is _ _ _ _ r2 r1).
Qed.

Definition isdecrigtoringrel (X : rig) {R : hrel X} (is : @isbinophrel (rigaddabmonoid X) R)
           (is' : @isinvbinophrel (rigaddabmonoid X) R) (isd : isdecrel R) :
  isdecrel (rigtoringrel X is).
Proof. intros. apply (isdecabgrdiffrel (rigaddabmonoid X) is is' isd). Defined.

Lemma isinvringrigtoringmultgt (X : rig) {R : hrel X} (is0 : @isbinophrel (rigaddabmonoid X) R)
      (is1 : @isinvbinophrel (rigaddabmonoid X) R) (is : isinvrigmultgt X R) :
  isinvringmultgt (rigtoring X) (rigtoringrel X is0).
Proof.
  intros. split.
  - assert (int : ∏ a b, isaprop (rigtoringrel X is0 (a * b) ringunel1 →
                                  rigtoringrel X is0 a ringunel1 →
                                  rigtoringrel X is0 b ringunel1)).
    intros.
    apply impred. intro.
    apply impred. intro.
    apply (pr2 _).
    apply (setquotuniv2prop _ (λ a b, make_hProp _ (int a b))).

    intros xa1 xa2.
    change ((abgrdiffrelint (rigaddabmonoid X) R (@rigtoringop2int X xa1 xa2)
                            (@rigunel1 X ,, @rigunel1 X)) →
            (abgrdiffrelint (rigaddabmonoid X) R) xa1 (@rigunel1 X ,, @rigunel1 X) →
            (abgrdiffrelint (rigaddabmonoid X) R) xa2 (@rigunel1 X ,, @rigunel1 X)).
    unfold abgrdiffrelint. simpl. apply hinhfun2. intros t22 t21.
    set (c2 := pr1 t22). set (c1 := pr1 t21).
    set (r1 := pr2 t21). set (r2 := pr2 t22).
    set (x1 := pr1 xa1). set (a1 := pr2 xa1).
    set (x2 := pr1 xa2). set (a2 := pr2 xa2).
    simpl in r2. clearbody r2.
    change (pr1 (R (x1 * x2 + a1 * a2 + 0 + c2) (0 + (x1 * a2 + a1 * x2) + c2))) in r2.
    rewrite (riglunax1 X _) in r2. rewrite (rigrunax1 X _) in r2.
    rewrite (rigrunax1 X _). rewrite (riglunax1 X _).
    set (r2' := (pr2 is1) _ _ c2 r2). clearbody r1.
    change (pr1 (R (x1 + 0 + c1) (0 + a1 + c1))) in r1.
    rewrite (riglunax1 X _) in r1. rewrite (rigrunax1 X _) in r1.
    set (r1' := (pr2 is1) _ _ c1 r1). exists 0.
    rewrite (rigrunax1 X _). rewrite (rigrunax1 X _).
    apply ((pr1 is) _ _ _ _ r2' r1').

  - assert (int : ∏ a b, isaprop (rigtoringrel X is0 (a * b) ringunel1 →
                                  rigtoringrel X is0 b ringunel1 →
                                  rigtoringrel X is0 a ringunel1)).
    intros.
    apply impred. intro.
    apply impred. intro.
    apply (pr2 _).
    apply (setquotuniv2prop _ (λ a b, make_hProp _ (int a b))).

    intros xa1 xa2.
    change ((abgrdiffrelint (rigaddabmonoid X) R (@rigtoringop2int X xa1 xa2)
                            (@rigunel1 X ,, @rigunel1 X)) →
            (abgrdiffrelint (rigaddabmonoid X) R) xa2 (@rigunel1 X ,, @rigunel1 X) →
            (abgrdiffrelint (rigaddabmonoid X) R) xa1 (@rigunel1 X ,, @rigunel1 X)).
    unfold abgrdiffrelint. simpl. apply hinhfun2. intros t22 t21.
    set (c2 := pr1 t22). set (c1 := pr1 t21).
    set (r1 := pr2 t21). set (r2 := pr2 t22).
    set (x1 := pr1 xa1). set (a1 := pr2 xa1).
    set (x2 := pr1 xa2). set (a2 := pr2 xa2).
    simpl in r2. clearbody r2.
    change (pr1 (R (x1 * x2 + a1 * a2 + 0 + c2)
                   (0 + (x1 * a2 + a1 * x2) + c2))) in r2.
    rewrite (riglunax1 X _) in r2. rewrite (rigrunax1 X _) in r2.
    rewrite (rigrunax1 X _). rewrite (riglunax1 X _).
    set (r2' := (pr2 is1) _ _ c2 r2). clearbody r1.
    change (pr1 (R (x2 + 0 + c1) (0 + a2 + c1))) in r1.
    rewrite (riglunax1 X _) in r1. rewrite (rigrunax1 X _) in r1.
    set (r1' := (pr2 is1) _ _ c1 r1). exists 0.
    rewrite (rigrunax1 X _). rewrite (rigrunax1 X _).
    apply ((pr2 is) _ _ _ _ r2' r1').
Qed.


(** **** Relations and the canonical homomorphism to the ring associated with a rig (ring of differences) *)

Lemma iscomptoringdiff (X : rig) {L : hrel X} (is0 : @isbinophrel (rigaddabmonoid X) L) :
  iscomprelrelfun L (rigtoringrel X is0) (toringdiff X).
Proof.
  apply (iscomptoabgrdiff (rigaddabmonoid X)).
Qed.

Close Scope rig_scope.
