(*******************************************************)
(*                                                     *)
(*                Theory of pi-calculus.               *)
(*                                                     *)
(*******************************************************)
(*                                                     *)
(* File   : picalcth.v                                 *)
(* Author : Ivan Scagnetto (scagnett@dimi.uniud.it),   *)
(*          Dipartimento di Matematica e Informatica,  *)
(*          University of Udine                        *)
(* Date   : July 1998                                  *)
(*                                                     *)
(*******************************************************)
(*                                                     *)
(* This file is part of "Pi-calculus in (Co)Inductive  *)
(* Type Theory", a joint work with Furio Honsell and   *)
(* Marino Miculan (accepted for publication on TCS).   *)
(* If you are interested you can find more information *)
(* (and a gzipped PostScript version of the article)   *)
(* at the following URL:                               *)
(* http://www.dimi.uniud.it/~scagnett/pi-calculus.html *)
(*                                                     *)
(*******************************************************)

Section picalc_syntax.

(******************************************************)
(* Type representing names - notice that it is NOT an *)
(* inductive set.                                     *)
(******************************************************)

Parameter name : Set.

(********************************************************)
(* Type representing (finite) list of names: such       *)
(* lists are useful in keeping track of names occurring *)
(* in the environment in order to correctly reify       *)
(* freshness.                                           *)
(********************************************************)

Inductive Nlist : Set :=
  | empty : Nlist
  | cons : name -> Nlist -> Nlist.

(*******************************************************)
(* Inductive predicate checking that a given name does *)
(* not occur in a given (finite) list.                 *)
(*******************************************************)

Inductive Nlist_notin (x : name) : Nlist -> Prop :=
  | Nlist_notin_empty : Nlist_notin x empty
  | Nlist_notin_cons :
      forall (y : name) (l : Nlist),
      x <> y -> Nlist_notin x l -> Nlist_notin x (cons y l).

(*****************************************************)
(* Inductive type representing the set of processes. *)
(*****************************************************)

Inductive proc : Set :=
  | nil : proc
  | bang : proc -> proc
  | tau_pref : proc -> proc
  | par : proc -> proc -> proc
  | sum : proc -> proc -> proc
  | nu : (name -> proc) -> proc
  | match_ : name -> name -> proc -> proc
  | mismatch : name -> name -> proc -> proc
  | in_pref : name -> (name -> proc) -> proc
  | out_pref : name -> name -> proc -> proc.

(*****************************************************)
(* Inductive encoding of the predicate checking if a *)
(* given name occurs in a given process.             *)
(*****************************************************)

Inductive isin (x : name) : proc -> Prop :=
  | isin_bang : forall p : proc, isin x p -> isin x (bang p)
  | isin_tau : forall p : proc, isin x p -> isin x (tau_pref p)
  | isin_par1 : forall p q : proc, isin x p -> isin x (par p q)
  | isin_par2 : forall p q : proc, isin x q -> isin x (par p q)
  | isin_sum1 : forall p q : proc, isin x p -> isin x (sum p q)
  | isin_sum2 : forall p q : proc, isin x q -> isin x (sum p q)
  | isin_nu :
      forall p : name -> proc,
      (forall z : name, isin x (p z)) -> isin x (nu p)
  | isin_match1 :
      forall (p : proc) (y z : name), isin x p -> isin x (match_ y z p)
  | isin_match2 : forall (p : proc) (y : name), isin x (match_ x y p)
  | isin_match3 : forall (p : proc) (y : name), isin x (match_ y x p)
  | isin_mismatch1 :
      forall (p : proc) (y z : name), isin x p -> isin x (mismatch y z p)
  | isin_mismatch2 : forall (p : proc) (y : name), isin x (mismatch x y p)
  | isin_mismatch3 : forall (p : proc) (y : name), isin x (mismatch y x p)
  | isin_in1 :
      forall (p : name -> proc) (y : name),
      (forall z : name, isin x (p z)) -> isin x (in_pref y p)
  | isin_in2 : forall p : name -> proc, isin x (in_pref x p)
  | isin_out1 :
      forall (p : proc) (y z : name), isin x p -> isin x (out_pref y z p)
  | isin_out2 : forall (p : proc) (y : name), isin x (out_pref x y p)
  | isin_out3 : forall (p : proc) (y : name), isin x (out_pref y x p).

(***************************************************)
(* Inductive encoding of the predicate checking if *)
(* a given name does not occur in a given process. *)
(***************************************************)

Inductive notin (x : name) : proc -> Prop :=
  | notin_nil : notin x nil
  | notin_bang : forall p : proc, notin x p -> notin x (bang p)
  | notin_tau : forall p : proc, notin x p -> notin x (tau_pref p)
  | notin_par :
      forall p q : proc, notin x p -> notin x q -> notin x (par p q)
  | notin_sum :
      forall p q : proc, notin x p -> notin x q -> notin x (sum p q)
  | notin_nu :
      forall p : name -> proc,
      (forall z : name, x <> z -> notin x (p z)) -> notin x (nu p)
  | notin_match :
      forall (p : proc) (y z : name),
      x <> y -> x <> z -> notin x p -> notin x (match_ y z p)
  | notin_mismatch :
      forall (p : proc) (y z : name),
      x <> y -> x <> z -> notin x p -> notin x (mismatch y z p)
  | notin_in :
      forall (p : name -> proc) (y : name),
      x <> y ->
      (forall z : name, x <> z -> notin x (p z)) -> notin x (in_pref y p)
  | notin_out :
      forall (p : proc) (y z : name),
      x <> y -> x <> z -> notin x p -> notin x (out_pref y z p).

(****************************************************)
(* Axiom stating that a name can either appear in a *)
(* given process or not.                            *)
(****************************************************)

Axiom LEM_OC : forall (p : proc) (x : name), isin x p \/ notin x p.

(*******************************************************)
(* Law of excluded middle over names: this allows case *)
(* analysis over names.                                *)
(*******************************************************)

Lemma LEM_name : forall x y : name, x = y \/ x <> y.

Proof.

intros; elim (LEM_OC (match_ y y nil) x); intro;
 [ left; inversion_clear H; [ inversion_clear H0 | trivial | trivial ]
 | right; inversion_clear H; assumption ].

Qed.

(****************************************************)
(* Axiom stating that we can always choose a fresh  *)
(* name w.r.t. a given process and a given (finite) *)
(* list of names.                                   *)
(****************************************************)

Axiom
  unsat :
    forall (p : proc) (l : Nlist),
    exists x : name, notin x p /\ Nlist_notin x l.

(*****************************************************)
(* The following two lemmata provide a way to switch *)
(* from a context involving the notin predicate to a *)
(* context involving an isin predicate.              *)
(*****************************************************)

Lemma isin_to_notin : forall (p : proc) (x : name), ~ notin x p -> isin x p.

Proof.

intros; elim (LEM_OC p x); intro;
 [ assumption | absurd (notin x p); assumption ].

Qed.

Lemma notin_to_isin : forall (p : proc) (x : name), ~ isin x p -> notin x p.

Proof.

intros; elim (LEM_OC p x); intro;
 [ absurd (isin x p); assumption | assumption ].

Qed.

(*****************************************************)
(* Separation lemma: a name occurring in a process P *)
(* is different from a name not occurring in P.      *)
(*****************************************************)

Lemma Sep_proc :
 forall (x y : name) (p : proc), isin x p -> notin y p -> x <> y.

Proof.

simple induction p; intros.

inversion_clear H.

inversion_clear H0.
inversion_clear H1.
apply H; assumption.

inversion_clear H0.
inversion_clear H1.
apply H; assumption.

inversion_clear H2.
inversion_clear H1.
apply H; assumption.
apply H0; assumption.

inversion_clear H2.
inversion_clear H1.
apply H; assumption.
apply H0; assumption.

inversion_clear H1.
inversion_clear H0.

elim (unsat (nu p0) (cons x (cons y empty))); intros.
inversion_clear H0.
inversion_clear H4.
inversion_clear H5.
clear H6; apply H with x0; [ apply H1 | apply H2; auto ].

inversion_clear H1.
inversion_clear H0; [ apply H; assumption | auto | auto ].

inversion_clear H1.
inversion_clear H0; [ apply H; assumption | auto | auto ].

inversion_clear H1.
inversion_clear H0.
elim (unsat (nu p0) (cons x (cons y (cons n empty)))); intros.
inversion_clear H0.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
clear H8; apply H with x0; [ apply H1 | apply H3; auto ].
auto.

inversion_clear H1.
inversion_clear H0; [ apply H; assumption | auto | auto ].

Qed.

(*********************************************)
(* Inductive type representing free actions. *)
(*********************************************)

Inductive f_act : Set :=
  | tau : f_act
  | Out : name -> name -> f_act.

(******************************************************)
(* Occur checking predicates and definitions for free *)
(* actions.                                           *)
(******************************************************)

Inductive f_act_isin (x : name) : f_act -> Prop :=
  | f_act_isin_Out1 : forall y : name, f_act_isin x (Out x y)
  | f_act_isin_Out2 : forall y : name, f_act_isin x (Out y x).

Inductive f_act_notin (x : name) : f_act -> Prop :=
  | f_act_notin_tau : f_act_notin x tau
  | f_act_notin_Out :
      forall y z : name, x <> y -> x <> z -> f_act_notin x (Out y z).

Definition f_act_notin_ho (x : name) (a : name -> f_act) :=
  forall y : name, x <> y -> f_act_notin x (a y).

(**************************************)
(* Separation lemma for free actions. *)
(**************************************)

Lemma Sep_f_act :
 forall (a : f_act) (x y : name), f_act_isin x a -> f_act_notin y a -> x <> y.

Proof.

simple induction a; intros.

inversion_clear H.

inversion_clear H0.
inversion_clear H; auto.

Qed.

(**********************************************)
(* Inductive type representing bound actions. *)
(**********************************************)

Inductive b_act : Set :=
  | In : name -> b_act
  | bOut : name -> b_act.

(*******************************************************)
(* Occur checking predicates and definitions for bound *)
(* actions.                                            *)
(*******************************************************)

Inductive b_act_isin (x : name) : b_act -> Prop :=
  | b_act_isin_In : b_act_isin x (In x)
  | b_act_isin_bOut : b_act_isin x (bOut x).

Inductive b_act_notin (x : name) : b_act -> Prop :=
  | b_act_notin_In : forall y : name, x <> y -> b_act_notin x (In y)
  | b_act_notin_bOut : forall y : name, x <> y -> b_act_notin x (bOut y).

Definition b_act_notin_ho (x : name) (a : name -> b_act) :=
  forall y : name, x <> y -> b_act_notin x (a y).

(***************************************)
(* Separation lemma for bound actions. *)
(***************************************)

Lemma Sep_b_act :
 forall (a : b_act) (x y : name), b_act_isin x a -> b_act_notin y a -> x <> y.

Proof.

simple induction a; intros.

inversion_clear H0.
inversion_clear H; auto.

inversion_clear H0.
inversion_clear H; auto.

Qed.

End picalc_syntax.

(*********************************************************)
(* Encoding of the operational semantics of pi-calculus. *)
(*********************************************************)

Section picalc_LTS.

(****************************************************************)
(* Mutual inductive predicates ftrans, btrans encoding the LTS. *)
(****************************************************************)

Inductive ftrans : proc -> f_act -> proc -> Prop :=
  | TAU : forall p : proc, ftrans (tau_pref p) tau p
  | OUT : forall (p : proc) (x y : name), ftrans (out_pref x y p) (Out x y) p
  | fSUM1 :
      forall (p1 p2 p : proc) (a : f_act),
      ftrans p1 a p -> ftrans (sum p1 p2) a p
  | fSUM2 :
      forall (p1 p2 p : proc) (a : f_act),
      ftrans p2 a p -> ftrans (sum p1 p2) a p
  | fPAR1 :
      forall (p1 p2 p : proc) (a : f_act),
      ftrans p1 a p -> ftrans (par p1 p2) a (par p p2)
  | fPAR2 :
      forall (p1 p2 p : proc) (a : f_act),
      ftrans p2 a p -> ftrans (par p1 p2) a (par p1 p)
  | fMATCH :
      forall (x : name) (p q : proc) (a : f_act),
      ftrans p a q -> ftrans (match_ x x p) a q
  | fMISMATCH :
      forall (x y : name) (p q : proc) (a : f_act),
      x <> y -> ftrans p a q -> ftrans (mismatch x y p) a q
  | fBANG :
      forall (p q : proc) (a : f_act),
      ftrans (par p (bang p)) a q -> ftrans (bang p) a q
  | COM1 :
      forall (p1 p2 q2 : proc) (q1 : name -> proc) (x y : name),
      btrans p1 (In x) q1 ->
      ftrans p2 (Out x y) q2 -> ftrans (par p1 p2) tau (par (q1 y) q2)
  | COM2 :
      forall (p1 p2 q1 : proc) (q2 : name -> proc) (x y : name),
      ftrans p1 (Out x y) q1 ->
      btrans p2 (In x) q2 -> ftrans (par p1 p2) tau (par q1 (q2 y))
  | fRES :
      forall (p1 p2 : name -> proc) (a : f_act) (l : Nlist),
      (forall y : name,
       notin y (nu p1) ->
       notin y (nu p2) ->
       Nlist_notin y l -> f_act_notin y a -> ftrans (p1 y) a (p2 y)) ->
      ftrans (nu p1) a (nu p2)
  | CLOSE1 :
      forall (p1 p2 : proc) (q1 q2 : name -> proc) (x : name),
      btrans p1 (In x) q1 ->
      btrans p2 (bOut x) q2 ->
      ftrans (par p1 p2) tau (nu (fun z : name => par (q1 z) (q2 z)))
  | CLOSE2 :
      forall (p1 p2 : proc) (q1 q2 : name -> proc) (x : name),
      btrans p1 (bOut x) q1 ->
      btrans p2 (In x) q2 ->
      ftrans (par p1 p2) tau (nu (fun z : name => par (q1 z) (q2 z)))
with btrans : proc -> b_act -> (name -> proc) -> Prop :=
  | IN : forall (p : name -> proc) (x : name), btrans (in_pref x p) (In x) p
  | bSUM1 :
      forall (p1 p2 : proc) (a : b_act) (p : name -> proc),
      btrans p1 a p -> btrans (sum p1 p2) a p
  | bSUM2 :
      forall (p1 p2 : proc) (a : b_act) (p : name -> proc),
      btrans p2 a p -> btrans (sum p1 p2) a p
  | bPAR1 :
      forall (p1 p2 : proc) (a : b_act) (p : name -> proc),
      btrans p1 a p -> btrans (par p1 p2) a (fun x : name => par (p x) p2)
  | bPAR2 :
      forall (p1 p2 : proc) (a : b_act) (p : name -> proc),
      btrans p2 a p -> btrans (par p1 p2) a (fun x : name => par p1 (p x))
  | bMATCH :
      forall (x : name) (p : proc) (a : b_act) (q : name -> proc),
      btrans p a q -> btrans (match_ x x p) a q
  | bMISMATCH :
      forall (x y : name) (p : proc) (a : b_act) (q : name -> proc),
      x <> y -> btrans p a q -> btrans (mismatch x y p) a q
  | bBANG :
      forall (p : proc) (a : b_act) (q : name -> proc),
      btrans (par p (bang p)) a q -> btrans (bang p) a q
  | bRES :
      forall (p1 : name -> proc) (a : b_act) (p2 : name -> name -> proc)
        (l : Nlist),
      (forall y : name,
       notin y (nu p1) ->
       notin y (nu (fun z : name => nu (p2 z))) ->
       b_act_notin y a -> Nlist_notin y l -> btrans (p1 y) a (p2 y)) ->
      btrans (nu p1) a (fun y : name => nu (fun z : name => p2 z y))
  | OPEN :
      forall (p1 p2 : name -> proc) (x : name) (l : Nlist),
      (forall y : name,
       notin y (nu p1) ->
       notin y (nu p2) ->
       x <> y -> Nlist_notin y l -> ftrans (p1 y) (Out x y) (p2 y)) ->
      btrans (nu p1) (bOut x) p2.

End picalc_LTS.

(****************************************************)
(* Encoding of Strong Late Bisimilarity - two ways. *)
(****************************************************)

Section picalc_SLB.

(*****************************************************************)
(* Strong Late Bisimilarity encoding as a coinductive predicate. *)
(*****************************************************************)

CoInductive StBisim : proc -> proc -> Prop :=
    sb :
      forall p q : proc,
      (forall a : f_act,
       (forall p1 : proc,
        ftrans p a p1 -> exists q1 : proc, ftrans q a q1 /\ StBisim p1 q1) /\
       (forall q1 : proc,
        ftrans q a q1 -> exists p1 : proc, ftrans p a p1 /\ StBisim p1 q1)) /\
      (forall x : name,
       (forall p1 : name -> proc,
        btrans p (In x) p1 ->
        exists q1 : name -> proc,
          btrans q (In x) q1 /\ (forall y : name, StBisim (p1 y) (q1 y))) /\
       (forall q1 : name -> proc,
        btrans q (In x) q1 ->
        exists p1 : name -> proc,
          btrans p (In x) p1 /\ (forall y : name, StBisim (p1 y) (q1 y)))) /\
      (forall x : name,
       (forall p1 : name -> proc,
        btrans p (bOut x) p1 ->
        exists q1 : name -> proc,
          btrans q (bOut x) q1 /\
          (forall y : name,
           notin y (nu p1) -> notin y (nu q1) -> StBisim (p1 y) (q1 y))) /\
       (forall q1 : name -> proc,
        btrans q (bOut x) q1 ->
        exists p1 : name -> proc,
          btrans p (bOut x) p1 /\
          (forall y : name,
           notin y (nu p1) -> notin y (nu q1) -> StBisim (p1 y) (q1 y)))) ->
      StBisim p q.

(**********************************************************************)
(* Inductive representation of the Strong Late Bisimilarity operator. *)
(**********************************************************************)

Inductive Op_StBisim (R : proc -> proc -> Prop) (p q : proc) : Prop :=
    op_sb :
      (forall a : f_act,
       (forall p1 : proc,
        ftrans p a p1 -> exists q1 : proc, ftrans q a q1 /\ R p1 q1) /\
       (forall q1 : proc,
        ftrans q a q1 -> exists p1 : proc, ftrans p a p1 /\ R p1 q1)) /\
      (forall x : name,
       (forall p1 : name -> proc,
        btrans p (In x) p1 ->
        exists q1 : name -> proc,
          btrans q (In x) q1 /\ (forall y : name, R (p1 y) (q1 y))) /\
       (forall q1 : name -> proc,
        btrans q (In x) q1 ->
        exists p1 : name -> proc,
          btrans p (In x) p1 /\ (forall y : name, R (p1 y) (q1 y)))) /\
      (forall x : name,
       (forall p1 : name -> proc,
        btrans p (bOut x) p1 ->
        exists q1 : name -> proc,
          btrans q (bOut x) q1 /\
          (forall y : name,
           notin y (nu p1) -> notin y (nu q1) -> R (p1 y) (q1 y))) /\
       (forall q1 : name -> proc,
        btrans q (bOut x) q1 ->
        exists p1 : name -> proc,
          btrans p (bOut x) p1 /\
          (forall y : name,
           notin y (nu p1) -> notin y (nu q1) -> R (p1 y) (q1 y)))) ->
      Op_StBisim R p q.

(*******************************************************)
(* Definition of the inclusion relation between binary *)
(* relations over processes.                           *)
(*******************************************************)

Definition Inclus (R1 R2 : proc -> proc -> Prop) :=
  forall p1 p2 : proc, R1 p1 p2 -> R2 p1 p2.

(********************************)
(* Op_StBisim's GFP definition. *)
(********************************)

Inductive StBisim' (p1 p2 : proc) : Prop :=
    Co_Ind :
      forall R : proc -> proc -> Prop,
      Inclus R (Op_StBisim R) -> R p1 p2 -> StBisim' p1 p2.

End picalc_SLB.