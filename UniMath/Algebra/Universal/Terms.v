(** * Terms for a given signature *)

(**
   This file contains a formalization of terms over a signature, defined as a sequence of
   function symbols. This sequence is though to be executed by a stack machine: each
   symbol of arity n pops n elements from the stack and pushes a new element.
   A sequence of function symbols is a term when the result of the execution is a stack
   with a single element and no stack underflow occurs.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.Maybe.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Signatures.

Local Open Scope stn.

(** ** Definition of oplist (operation list) *)
(**
   An oplist is a list of function symbols, interpreted as commands to be executed by a stack
   machine: each symbol of arity n pops n elements from the stack and pushes a new element.
   Therefore, to each oplist is associated a status, which may be either a natural number, giving
   the number of elements in the stack after the list is ececuted, or an error condition, when
   executing the oplist generates a stack underflow. A term is an oplist with status one.
 *)

Section Oplist.

  Local Definition oplist (σ: signature):= list σ.
  
  Identity Coercion oplistislist: oplist >-> list.
  
  Local Corollary isasetoplist (σ: signature): isaset (oplist σ).
  Proof.
    apply isofhlevellist.
    induction σ as [ S  [ O  ar ] ].
    apply setproperty.
  Defined.

  Local Definition status (σ: signature): UU := maybe (list (sorts σ)).

  Local Definition statusok {σ: signature}: list (sorts σ) → status σ := just.

  Local Definition statuserror {σ: signature}: status σ := nothing.

  Local Lemma isasetstatus (σ: signature): isaset (status σ).
  Proof.
    apply isasetmaybe.
    apply isofhlevellist.
    induction σ as [ S  [ O  ar ] ].
    apply isasetifdeceq.
    apply decproperty.
  Defined.

  Context {σ: signature}.

  (** *** The [statuscons] and [oplist2status] functions *)
  (**
     [statuscons] returns the status of executing the function symbol [nm] when the current
     stack status is [s]. The [statuserror] status is propagated by [statuscons]. Building
     over [statuscons], [oplist2status] returns the status corresponding to an oplist.
   *)
 
  Local Definition statuscons (nm: σ) (s: status σ): status σ :=
    flatmap (λ tl, (statusok ((sort nm) :: tl))) (flatmap (λ s, prefix_remove (arity nm) s) s).

  (*
  Local Definition statuscons (nm: σ) (s: status σ): status σ.
  Proof.
    induction s as [s | serror].
    - induction (prefix_remove (deceqnames σ) (arity nm) s) as [tail | _].
      + exact (statusok ((sort nm) :: tail) ).
      + exact statuserror.
    - exact statuserror.
  Defined.
  *)

  Local Definition oplist2status (l: oplist σ): status σ := foldr statuscons (statusok nil) l.
  
  Local Definition isaterm (l: oplist σ) := ∑ s: sorts σ, oplist2status l = statusok ([s]).

  (** TODO: Quite complex... make it shorter *)
  Local Lemma isapropisaterm (l: oplist σ): isaprop (isaterm l).
  Proof.
    cbn.
    intros.
    unfold isaterm in x, x'.
    unfold iscontr.
    induction x as [s liss].
    induction x' as [s' liss'].
    set (p := (! liss') @ liss).
    apply ii1_injectivity in p.
    apply cons_inj1 in p.
    induction p.
    assert (liss = liss').
    {
      apply proofirrelevance.
      apply isasetstatus.
    }
    induction X.
    exists (idpath _).
    intro.
    apply proofirrelevance.
    apply isaset_total2.
    - apply isasetifdeceq.
      apply decproperty.
    - intros.
    apply isasetaprop.
    apply isasetstatus.
  Defined.

End Oplist.

Section OplistProps.

  Context {σ: signature}.

  (** **** Properties of [statuscons] and [oplist2status] *)

(*
  Local Lemma statuscons_statusok_f {nm: names sigma} {n: nat} (aritynm: arity nm ≤ n)
    : statuscons nm (statusok n) = statusok (S (n - arity nm)).
  Proof.
    cbn [statuscons statusok some coprod_rect].
    induction (isdecrelnatleh (arity nm) n) as [arityok | arityerror] ; cbn.
    - apply idpath.
    - contradiction.
  Defined.

  Local Lemma statuscons_statusok_b {nm: names σ} {s: status σ} {l: list (sorts σ)}
    : statuscons nm s = statusok l → length l > 0 × s = statusok (cons (sort nm) (prefix_remove (deceqnames σ) (arity nm) l)).
  Proof.
    intro scons.
    induction s as [s | serror].
    - cbn [statuscons statusok coprod_rect] in scons.
      induction (isdecrelnatleh (arity nm) s) as [arityok | arityerror]; cbn in scons.
      + apply ii1_injectivity in scons.
        split.
        * rewrite <- scons.
          apply natgthsn0.
        * apply maponpaths.
          apply statuscons_arith ; assumption.
      + apply negpathsii2ii1 in scons.
        contradiction.
    - apply negpathsii2ii1 in scons.
      contradiction.
  Defined.
*)

  Local Lemma statuscons_dec (nm: names σ) (l: list (sorts σ))
    : ((statuscons nm (ii1 l) = statuserror) × (prefix_remove (arity nm) l = nothing))
              ⨿   ∑ (p: list (sorts σ)), (statuscons nm (ii1 l) = statusok ((sort nm) :: p))
                       × (prefix_remove (arity nm) l = statusok p).
  Proof.
    unfold statuscons.
    rewrite flatmap_just.
    induction (prefix_remove (arity nm) l) as [ p | error ].
    - apply ii2.
      exists p.
      split; apply idpath.
    - apply ii1.
      split.
      + apply idpath.
      + induction error.
        apply idpath.
  Defined.
  
  Local Lemma statuscons_neq_nil {nm: names σ} {s: status σ}
    : ¬ (statuscons nm s = statusok nil).
  Proof.
    induction s as [l | error].
    - set (H := statuscons_dec nm l).
      induction H as [H | H].
      + apply pr1 in H.
        intro H'.
        set (H'' :=  (!!H @ H')).
        apply negpathsii1ii2 in H''.
        assumption.
      + induction H as [p H].
        apply pr1 in H.
        intro H'.
        set (H'' :=  (!!H @ H')).
        apply ii1_injectivity in H''.
        apply negpathsnilcons in H''.
        assumption.
    - apply negpathsii2ii1.
  Defined.

  Local Lemma oplist2status_cons {nm: names σ} {l: oplist σ}
    : oplist2status (cons nm l) = statuscons nm (oplist2status l).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplist2status_zero_b {l: oplist σ}
    : oplist2status l = statusok nil → l = nil.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs _ lstatus.
      rewrite oplist2status_cons in lstatus.
      apply statuscons_neq_nil in lstatus.
      contradiction.
  Defined.

  Local Lemma oplist2status_positive_b {l: oplist σ} (so: sorts σ) (sos: list (sorts σ))
    : oplist2status l = statusok (cons so sos)
      → ∑ (x: names σ) (xs: oplist σ), l = cons x xs.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - intro nilstatus.
      cbn in nilstatus.
      apply ii1_injectivity in nilstatus.
      apply negpathsnilcons in nilstatus.
      contradiction.
    - intros x xs _ lstatus.
      exists x.
      exists xs.
      apply idpath.
  Defined.

  Local Definition statusconcatenate (s1 s2: status σ): status σ
    := flatmap (λ s2', flatmap (λ s1', statusok (s1' ++ s2')) s1) s2.

  Local Definition flatmap_comp {A B C: UU} {f: A → B} {g: B → C} {a: maybe A}:
     flatmap (λ x: B, just (g x)) (flatmap (λ y: A, just (f y)) a) = flatmap (λ y:A, just (g (f y))) a.
  Proof.
     induction a as [a' | aerror]  ; apply idpath.
  Defined.
  
  Local Lemma statusconcatenate_statuscons {nm: names σ} {s1 s2: status σ}
    : (statuscons nm s1 != statuserror)
      → statusconcatenate (statuscons nm s1) s2 = statuscons nm (statusconcatenate s1 s2).
  Proof.
    induction s1 as [s1' | ].
    2: contradiction.
    induction s2 as [s2'| ].
    2: reflexivity.
    intro H.
    set (X := statuscons_dec nm s1').
    induction X as [Xerr | Xok].
    - contradicts H (pr1 Xerr).
    - induction Xok as [tl [scons pref]].
      rewrite scons.
      simpl.
      rewrite concatenateStep.
      unfold statuscons.
      simpl.
      erewrite prefix_remove_concatenate.
      + rewrite flatmap_just.
        apply idpath.
      + assumption.
  Defined.

 Local Lemma oplist2status_concatenate {l1 l2: oplist σ}
    : oplist2status l1 != statuserror
      → oplist2status (concatenate l1 l2)
        = statusconcatenate (oplist2status l1) (oplist2status l2).
  Proof.
    revert l1.
    refine (list_ind _ _ _).
    - intros.
      change (concatenate nil l2) with (l2).
      induction (oplist2status l2) as [s2 | s2error].
      + apply idpath.
      + induction s2error.
        apply idpath.
    - intros x xs IH noerror.
      rewrite oplist2status_cons.
      rewrite statusconcatenate_statuscons by (assumption).
      rewrite <- IH.
      + apply idpath.
      + intro error.
        rewrite oplist2status_cons in noerror.
        rewrite error in noerror.
        contradiction.
  Defined.

  (** *** The [oplistsplit] function *)
  (**
     [oplistsplit] splits an oplist in an oplist of up to [n] terms and an oplist of the remaining
     terms.
   *)

  Local Definition oplistsplit (l: oplist σ) (n: nat): oplist σ × oplist σ.
  Proof.
    revert l n.
    refine (list_ind _ _ _).
    - intros.
      exact (nil,, nil).
    - intros x xs IH n.
      induction n.
      + exact (nil,, (cons x xs)).
      + induction (IH (n + arity x)) as [IHfirst IHsecond].
        exact (cons x IHfirst ,, IHsecond).
  Defined.

  Local Lemma oplistsplit_zero {l: oplist σ}: oplistsplit l 0 = nil,, l.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - apply idpath.
    - reflexivity.
  Defined.

  Local Lemma oplistsplit_nil {n: nat}: oplistsplit nil n = nil,, nil.
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_cons {x: names σ} {xs: oplist σ} {n: nat}
    : oplistsplit (cons x xs) (S n)
      = cons x (pr1 (oplistsplit xs (n + arity x))) ,, (pr2 (oplistsplit xs (n + arity x))).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_concatenate (l1 l2: oplist σ) {m: nat} (n: nat)
    : oplist2status l1 = statusok m → n ≤ m
      → oplistsplit (concatenate l1 l2) n
        = pr1 (oplistsplit l1 n) ,, concatenate (pr2 (oplistsplit l1 n)) l2.
  Proof.
    revert l1 m n.
    refine (list_ind _ _ _).
    - intros m n l1status nlehm.
      apply ii1_injectivity in l1status.
      rewrite <- l1status in *.
      apply natleh0tois0 in nlehm.
      rewrite nlehm.
      rewrite oplistsplit_zero.
      apply idpath.
    - intros x1 xs1 IH m n l1status nlehm.
      rewrite concatenateStep.
      induction n.
      + apply idpath.
      + rewrite oplist2status_cons in l1status.
        apply statuscons_statusok_b in l1status.
        induction l1status as [_ xs1status].
        assert (newnok: S n + arity x1 - 1 ≤ m + arity x1 - 1).
        {
          apply natgehandminusl, natlehandplusr.
          assumption.
        }
        set (IHinst := IH (m + arity x1 - 1) (S n + arity x1 - 1) xs1status newnok).
        rewrite oplistsplit_arith1 in IHinst.
        do 2 rewrite oplistsplit_cons.
        apply pathsdirprod.
        * cbn.
          apply maponpaths.
          apply (maponpaths pr1) in IHinst.
          cbn in IHinst.
          assumption.
        * apply (maponpaths dirprod_pr2) in IHinst.
          assumption.
  Defined.

  Local Lemma concatenate_oplistsplit (l: oplist σ) (n: nat)
    : concatenate (pr1 (oplistsplit l n)) (pr2 (oplistsplit l n)) = l.
  Proof.
    revert l n.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs IH n.
      induction n.
      + apply idpath.
      + rewrite oplistsplit_cons.
        cbn - [concatenate].
        rewrite concatenateStep.
        rewrite IH.
        apply idpath.
  Defined.

  Local Lemma oplist2status_oplistsplit (l: oplist σ) {m: nat} (n: nat)
    : oplist2status l = statusok m → n ≤ m
      → dirprod
          (oplist2status (pr1 (oplistsplit l n)) = statusok n)
          (oplist2status (pr2 (oplistsplit l n)) = statusok (m - n)).
  Proof.
    revert l m n.
    refine (list_ind _ _ _).
    - intros m n nilstatus nlehm.
      cbn.
      apply ii1_injectivity in nilstatus.
      rewrite <- nilstatus in *.
      apply natleh0tois0 in nlehm.
      rewrite nlehm.
      split ; apply idpath.
    - intros x xs IH m n lstatus nlehm.
      induction n.
      + rewrite oplistsplit_zero.
        rewrite natminuseqn.
        split ; [apply idpath | assumption].
      + rewrite oplistsplit_cons.
        cbn - [oplist2status].
        rewrite oplist2status_cons in lstatus.
        apply statuscons_statusok_b in lstatus.
        induction lstatus as [ _ xsstatus].
        eapply oplistsplit_arith2 in nlehm.
        induction (IH (m + arity x - 1) (n + arity x) xsstatus nlehm) as [IH1 IH2].
        split.
        * rewrite oplist2status_cons.
          rewrite IH1.
          rewrite statuscons_statusok_f.
          -- apply maponpaths.
             rewrite plusminusnmm.
             apply idpath.
          -- rewrite natpluscomm.
             apply natleh_plusright.
             apply isreflnatleh.
        * rewrite IH2.
          apply maponpaths.
          rewrite natminusminus.
          rewrite <- natplusassoc.
          rewrite (natpluscomm (1+n) (arity x)).
          rewrite <- natminusminus.
          rewrite plusminusnmm.
          apply idpath.
  Defined.

  Local Corollary oplistsplit_self {l: oplist σ} {n: nat}
    : oplist2status l = statusok n → oplistsplit l n = l ,, nil.
  Proof.
    intro lstatus.
    set (H := oplist2status_oplistsplit l n lstatus (isreflnatleh n)).
    induction H as [l1status l2status].
    set (normalization := concatenate_oplistsplit l n).
    rewrite minuseq0' in l2status.
    apply oplist2status_zero_b in l2status.
    rewrite l2status in normalization.
    rename l2status into oplistsplit_first.
    rewrite concatenate_nil in normalization.
    rename normalization into oplisplit_second.
    apply dirprodeq ; assumption.
  Defined.

  (** *** The [vecoplist2oplist] and [oplist2vecoplist] functions *)
  (**
     These functions transform a vector of [n] oplists into an oplists of status [n]
     ([vecoplist2oplist]) and viceversa ([oplist2vecoplist]).
   *)

  Local Definition vecoplist2oplist {n: nat} (v: Vector (oplist σ) n): oplist σ
    := vector_foldr concatenate nil v.

  Local Lemma vecoplist2oplist_vcons {n: nat} (x: oplist σ) (v: Vector (oplist σ) n)
    : vecoplist2oplist (vcons x v) = concatenate x (vecoplist2oplist v).
  Proof.
    apply idpath.
  Defined.

  Local Lemma vecoplist2oplist_inj {n : nat} {v1 v2: Vector (oplist σ) n}
        (v1status: ∏ (i: ⟦ n ⟧), isaterm (el v1 i))
        (v2status: ∏ (i: ⟦ n ⟧), isaterm (el v2 i))
    : vecoplist2oplist v1 = vecoplist2oplist v2 → v1 = v2.
  Proof.
    intro eq.
    induction n.
    - induction v1.
      induction v2.
      apply idpath.
    - change v1 with (vcons (hd v1) (tl v1)) in *.
      change v2 with (vcons (hd v2) (tl v2)) in *.
      do 2 rewrite vecoplist2oplist_vcons in eq.
      apply (maponpaths (λ l, oplistsplit l 1)) in eq.
      rewrite (oplistsplit_concatenate _ _ 1 (v1status firstelement) (isreflnatleh _)) in eq.
      rewrite (oplistsplit_concatenate _ _ 1 (v2status firstelement) (isreflnatleh _)) in eq.
      rewrite (oplistsplit_self (v1status firstelement)) in eq.
      rewrite (oplistsplit_self (v2status firstelement)) in eq.
      cbn in eq.
      apply map_on_two_paths.
      + apply (maponpaths pr1 eq).
      + apply IHn.
        * intro i.
          rewrite el_tl.
          apply v1status.
        * intro i.
          rewrite el_tl.
          apply v2status.
        * apply (maponpaths (λ l, pr2 l: oplist σ)) in eq.
          assumption.
  Defined.

  Local Lemma oplist2status_vecoplist2oplist {n: nat} {v: Vector (oplist σ) n}
        (vstatus: ∏ (i: ⟦ n ⟧), isaterm (el v i))
    : oplist2status (vecoplist2oplist v) = statusok n.
  Proof.
    induction n.
    - induction v.
      apply idpath.
    - change v with (vcons (hd v) (tl v)).
      rewrite vecoplist2oplist_vcons.
      rewrite oplist2status_concatenate.
      + rewrite IHn.
        * change (hd v) with (el v firstelement).
          rewrite (vstatus firstelement).
          apply idpath.
        * intro.
          rewrite el_tl.
          apply vstatus.
      + change (hd v) with (el v firstelement).
        rewrite (vstatus firstelement).
        apply negpathsii1ii2.
  Defined.

  Local Definition oplist2vecoplist (l: oplist σ) {n: nat}
        (lstatus: oplist2status l = statusok n)
    : ∑ (v: Vector (oplist σ) n)
      , (∏ (i: ⟦ n ⟧), isaterm (el v i))
          × (∏ (i: ⟦ n ⟧), length (el v i) ≤ length l)
          × vecoplist2oplist v = l.
  Proof.
    revert l lstatus.
    induction n.
    - intros.
      exists vnil.
      repeat split.
      + intro i.
        apply fromstn0.
        assumption.
      + intro i.
        apply fromstn0.
        assumption.
      + apply oplist2status_zero_b in lstatus.
        rewrite lstatus.
        apply idpath.
    - intros.
      induction (oplist2status_oplistsplit l 1 lstatus (natleh0n 0)) as [firststatus reststatus].
      set (first := pr1 (oplistsplit l 1)) in *.
      set (rest := pr2 (oplistsplit l 1)) in *.
      cbn in rest.
      change (S n) with (1 + n) in reststatus.
      rewrite natpluscomm in reststatus.
      rewrite plusminusnmm in reststatus.
      induction (IHn rest reststatus) as [v [vstatus [vlen vflatten]]].
      exists (vcons first v).
      repeat split.
      + intro i.
        induction i as [i ilehsn].
        induction i.
        * exact firststatus.
        * change (S i ,, ilehsn) with (dni_firstelement (i,, ilehsn)).
          rewrite el_vcons_tl.
          exact (vstatus (i ,, ilehsn)).
      + intro i.
        induction i as [i ilehsn].
        induction i.
        * change (el (vcons first v) (0,, ilehsn)) with first.
          rewrite <- (concatenate_oplistsplit l 1).
          apply length_sublist1.
        * change (S i ,, ilehsn) with (dni_firstelement (i,, ilehsn)).
          rewrite el_vcons_tl.
          eapply istransnatleh.
          -- exact (vlen (i ,, ilehsn)).
          -- rewrite <- (concatenate_oplistsplit l 1).
             apply length_sublist2.
      + rewrite vecoplist2oplist_vcons.
        rewrite vflatten.
        apply concatenate_oplistsplit.
  Defined.

  Local Definition oplist_build_term (nm: names σ) (v: Vector (oplist σ) (arity nm))
    : oplist σ := cons nm (vecoplist2oplist v).

  Local Lemma oplist_build_term_status (nm: names σ) (v: Vector (oplist σ) (arity nm))
        (vstatus: (∏ (i: ⟦ arity nm ⟧), isaterm (el v i)))
    : isaterm (oplist_build_term nm v).
  Proof.
    unfold oplist_build_term, isaterm.
    rewrite oplist2status_cons.
    rewrite oplist2status_vecoplist2oplist.
    - rewrite statuscons_statusok_f.
      + rewrite minuseq0'.
        apply idpath.
      + apply isreflnatleh.
    - exact vstatus.
  Defined.

  Local Definition oplist_decompose (l: oplist σ) (l1status: isaterm l):
    ∑ (nm:names σ) (v: Vector (oplist σ) (arity nm))
    , (∏ (i: ⟦ arity nm ⟧), isaterm (el v i))
        × (∏ (i: ⟦ arity nm  ⟧), length (el v i) < length l)
        × oplist_build_term nm v = l.
  Proof.
    revert l l1status.
    refine (list_ind _ _ _).
    - intro l1status.
      apply ii1_injectivity in l1status.
      apply negpaths0sx in l1status.
      contradiction.
    - intros x xs IH l1status.
      exists x.
      unfold isaterm in l1status.
      rewrite oplist2status_cons in l1status.
      apply statuscons_statusok_b in l1status.
      induction l1status as [_ statusxs].
      rewrite natpluscomm in statusxs.
      rewrite plusminusnmm in statusxs.
      induction (oplist2vecoplist xs statusxs) as [vtail [vstatus [vlen vflatten]]].
      exists vtail.
      repeat split.
      + exact vstatus.
      + intro i.
        apply natlehtolthsn.
        apply vlen.
      + unfold oplist_build_term.
        rewrite vflatten.
        apply idpath.
  Defined.

End OplistProps.

(** ** Terms and related constructors and destructors *)

Section Term.

  (** A term is an oplist together with the proof it is a term *)

  Definition term (σ: signature)
    := ∑ s: oplist σ, isaterm s.

  Definition make_term {σ: signature} (l: oplist σ) (lstatus: isaterm l)
    : term σ := l ,, lstatus.

  Coercion term2oplist {σ: signature}: term σ → oplist σ := pr1.

  Definition term2proof {σ: signature}: ∏ t: term σ, isaterm t := pr2.

  Lemma isasetterm(σ: signature): isaset (term σ).
  Proof.
    apply isaset_total2.
    - apply isasetoplist.
    - intros.
      apply isasetaprop.
      apply isasetstatus.
  Defined.

  Definition termset (σ : signature): hSet
    := make_hSet (term σ) (isasetterm σ).

  Context {σ: signature}.

  Lemma term_extens {t1 t2 : term σ} (p : term2oplist t1 = term2oplist t2)
    : t1 = t2.
  Proof.
    apply subtypePairEquality'.
    2: apply isapropisaterm.
    exact p.
  Defined.

  (* [build_term] builds a term starting from its principal function symbols and its subterms *)

  Definition build_term (nm: names σ) (v: Vector (term σ) (arity nm)): term σ.
  Proof.
    exists (oplist_build_term nm (vector_map term2oplist v)).
    apply oplist_build_term_status.
    intro i.
    rewrite el_vector_map.
    exact (term2proof (el v i)).
  Defined.

  (** [princop] returns the principal function symbol of a term *)

  Definition princop (t: term σ): names σ
    := pr1 (oplist_decompose t (term2proof t)).

  (** [subterms] retusn the subterms of a term term *)

  Definition subterms (t: term σ): Vector (term σ) (arity (princop t)).
  Proof.
    unfold princop.
    induction (oplist_decompose t (term2proof t)) as [nm [v [vstatus [vlen normalization]]]].
    exact (mk_vector (λ (i: ⟦ arity nm ⟧), make_term (el v i) (vstatus i))).
  Defined.

  Local Lemma subterms_length (t: term σ): ∏ (i: ⟦ arity (princop t) ⟧), length (el (subterms t) i) < length t.
  Proof.
    unfold subterms, princop.
    induction (oplist_decompose t (term2proof t)) as [nm [v [vstatus [vlen normalization]]]].
    intro i.
    rewrite el_mk_vector.
    cbn - [natlth].
    exact (vlen i).
  Defined.

  Local Lemma term_normalization (t: term σ): build_term (princop t) (subterms t) = t.
  Proof.
    unfold princop, subterms.
    induction (oplist_decompose t (term2proof t)) as [nm [v [vstatus [vlen normalization]]]].
    apply subtypePairEquality'.
    2: apply isapropisaterm.
    rewrite vector_map_mk_vector.
    unfold funcomp.
    cbn.
    rewrite mk_vector_el.
    apply normalization.
  Defined.

  Local Lemma princop_build_term (nm: names σ) (v: Vector (term σ) (arity nm))
    : princop (build_term nm v) = nm.
  Proof.
    apply idpath.
  Defined.

  Local Lemma subterms_build_term (nm: names σ) (v: Vector (term σ) (arity nm))
    : subterms (build_term nm v) = v.
  Proof.
    set (t := build_term nm v).
    set (v0norm := term_normalization t).
    unfold build_term in v0norm.
    unfold oplist_build_term in v0norm.
    set (v0norm_list := maponpaths pr1 v0norm).
    cbn [pr1] in v0norm_list.
    apply cons_inj2 in v0norm_list.
    apply vecoplist2oplist_inj in v0norm_list.
    unfold term2oplist in v0norm_list.
    - apply vector_extens.
      intro i.
      apply term_extens.
      apply (maponpaths (λ v, el v i)) in v0norm_list.
      do 2 rewrite el_vector_map in v0norm_list.
      apply v0norm_list.
    - intro i.
      rewrite el_vector_map.
      apply (el (subterms t) i).
    - intro i.
      rewrite el_vector_map.
      apply (el v i).
  Defined.

  Local Lemma length_term (t: term σ): length t > 0.
  Proof.
    induction t as [l statusl].
    induction (oplist2status_positive_b statusl) as [x [xs lstruct]].
    induction (! lstruct).
    cbn.
    apply idpath.
  Defined.

  Local Lemma term_notnil {X: UU} {t: term σ}: length t ≤ 0 → X.
  Proof.
    intro tlen.
    apply natlehneggth in tlen.
    contradicts tlen (length_term t).
  Defined.

End Term.

(** ** Term induction and recursion *)

Section TermInduction.

  Context {σ: signature}.

  Definition term_ind_HP (P: term σ → UU) :=
    ∏ (nm: names σ)
      (v: Vector (term σ) (arity nm))
      (IH: ∏ (i:  ⟦ arity nm ⟧), P (el v i))
    , P (build_term nm v).

  Local Lemma term_ind_onlength (P: term σ → UU) (R: term_ind_HP P)
    : ∏ (n: nat) (t: term σ), length t ≤ n →  P t.
  Proof.
    induction n.
    - intros t tlen.
      exact (term_notnil tlen).
    - intros t tlen.
      apply (transportf P (term_normalization t)).
      (* rewrite <- (term_normalization t).  *)
      (* induction (term_normalization t). *)
      apply (R (princop t) (subterms t)).
      intro i.
      apply (IHn (el (subterms t) i)).
      change (S (length (el (subterms t) i)) ≤ S n).
      eapply istransnatleh.
      -- apply natlthtolehsn.
         apply (subterms_length t).
      -- apply tlen.
  Defined.

  Theorem term_ind (P: term σ → UU) (R: term_ind_HP P) (t: term σ)
    : P t.
  Proof.
    exact (term_ind_onlength P R (length t) t (isreflnatleh _)).
  Defined.

  Local Lemma term_ind_onlength_nirrelevant (P: term σ → UU) (R: term_ind_HP P)
    : ∏ (n m1 m2: nat)
        (m1lehn: m1 ≤ n) (m2lehn: m2 ≤ n)
        (t: term σ)
        (lenm1: length t ≤ m1) (lenm2: length t ≤ m2)
      , term_ind_onlength P R m1 t lenm1 = term_ind_onlength P R m2 t lenm2.
  Proof.
    induction n.
    - intros.
      set (tlen := istransnatleh lenm1 m1lehn).
      exact (term_notnil tlen).
    - intros.
      induction m1.
      + exact (term_notnil lenm1).
      + induction m2.
        * exact (term_notnil lenm2).
        * simpl.
          do 2 apply maponpaths.
          apply funextsec.
          intro i.
          apply IHn.
          -- apply m1lehn.
          -- apply m2lehn.
  Defined.

  Lemma term_ind_step (P: term σ → UU) (R: term_ind_HP P)
        (nm: names σ) (v: Vector (term σ) (arity nm))
    : term_ind P R (build_term nm v)
      = R nm v (λ i:  ⟦ arity nm ⟧, term_ind P R (el v i)).
  Proof.
    unfold term_ind.
    set (t := build_term nm v).
    simpl (length (term2oplist _)).
    unfold term_ind_onlength at 1.
    rewrite nat_rect_step.
    set (v0len := subterms_length t).
    set (v0norm := term_normalization t).
    clearbody v0len v0norm.  (* Needed to make induction work *)
    induction (! (subterms_build_term nm v: subterms t = v)).
    assert (v0normisid: v0norm = idpath _).
    {
      apply proofirrelevance.
      apply isasetterm.
    }
    rewrite v0normisid.
    rewrite idpath_transportf.
    apply maponpaths.
    apply funextsec.
    intro i.
    unfold term_ind_onlength.
    apply (term_ind_onlength_nirrelevant P R (length (vecoplist2oplist (vector_map pr1 v)))).
    - apply isreflnatleh.
    - apply natlthsntoleh.
      apply (v0len i).
  Defined.

  Definition depth: term σ → nat
    := term_ind (λ _, nat) (λ (nm: names σ) (vterm: Vector (term σ) (arity nm))
                (levels: ∏ i : ⟦ arity nm ⟧, (λ _ : term σ, nat) (el vterm i)),
                1 + vector_foldr max 0 (mk_vector levels)).

  Definition fromterm {A:UU}
             (op : ∏ (nm : names σ), Vector A (arity nm) → A)
    : term σ → A
    := term_ind (λ _, A) (λ nm _ rec, op nm (mk_vector rec)).

  Lemma fromtermstep {A: UU} (nm: names σ) (op : ∏ (nm : names σ), Vector A (arity nm) → A)
                     (v: Vector (term σ) (arity nm))
    : fromterm op (build_term nm v) = op nm (vector_map (fromterm op) v).
  Proof.
    unfold fromterm.
    rewrite term_ind_step.
    rewrite vector_map_as_mk_vector.
    apply idpath.
  Defined.

End TermInduction.

(** * Iterated version of [build_term] *)
(**
   Defines a curried version of [build_term] which is easier to use in practice.
 **)

Section iterbuild.

  (**
     [iterfun A B n] is the curried version of [Vector A n → B], i.e.
     [iterfun A B n] =  [A → (A → ...... → (A → B)] with A repeated n times
   *)

  Definition iterfun (A B: UU) (n: nat): UU
    := nat_rect (λ _, UU) B (λ (n: nat) (IH: UU), A → IH) n.

  Definition itercurry {A B: UU} {n: nat} (f: Vector A n → B): iterfun A B n.
  Proof.
    induction n.
    - cbn. exact (f vnil).
    - unfold iterfun.
      rewrite nat_rect_step.
      intro x.
      set (f' := λ (v: Vector A n), f (vcons x v)).
      apply (IHn f').
  Defined.

  Definition build_term_curried {σ: signature} (nm: names σ)
    : iterfun (term σ) (term σ) (arity nm)
    := itercurry (build_term nm).

End iterbuild.
