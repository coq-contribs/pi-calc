(*************************************************************)
(*                                                           *)
(*      Congruence of Strong (Late) Bisimilarity w.r.t.      *)
(* the ! (bang) operator (since this result is particularly  *)
(*        cumbersome, we put it in a separate file).         *)
(*                                                           *)
(*************************************************************)
(*                                                           *)
(* File   : bangpack.v                                       *)
(* Author : Ivan Scagnetto (scagnett@dimi.uniud.it),         *)
(*          Dipartimento di Matematica e Informatica,        *)
(*          University of Udine                              *)
(* Date   : July 1998                                        *)
(*                                                           *)
(*************************************************************)
(*                                                           *)
(* This file is part of "Pi-calculus in (Co)Inductive        *)
(* Type Theory", a joint work with Furio Honsell and         *)
(* Marino Miculan (accepted for publication on TCS).         *)
(* If you are interested you can find more information       *)
(* (and a gzipped PostScript version of the article)         *)
(* at the following URL:                                     *)
(* http://www.dimi.uniud.it/~scagnett/pi-calculus.html       *)
(*                                                           *)
(*************************************************************)

(*************************************************************)
(* In the following we will prove the congruence             *)
(* of Strong (Late) Bisimilarity w.r.t. the ! operator.      *)
(* Since the transition rules fBANG and bBANG do not satisfy *)
(* a subformula property, this is a long and difficult task  *)
(* and requires the formulation of a canonical form theory   *)
(* concerning the reducts of the processes                   *)
(* whose head constructor is the bang operator.              *)
(*************************************************************)

Require Export alglaws.

Section structural_congruence3.

(*************************************************************)
(* Auxiliary recursive definitions useful to build processes *)
(* with an unlimited (although finite) number of parallel    *)
(* compositions.                                             *)
(*************************************************************)

Fixpoint cf_f_act (p q : proc) (n : nat) {struct n} : proc :=
  match n with
  | O => par q (bang p)
  | S m => par p (cf_f_act p q m)
  end.

Fixpoint cf_b_act (p : proc) (q : name -> proc) (n : nat) {struct n} :
 name -> proc :=
  match n with
  | O => fun n : name => par (q n) (bang p)
  | S m => fun n : name => par p (cf_b_act p q m n)
  end.

Fixpoint cf_tau1 (p q : proc) (r : name -> proc) (x : name) 
 (n m : nat) {struct m} : proc :=
  match m with
  | O => par (r x) (cf_f_act p q n)
  | S m' => par p (cf_tau1 p q r x n m')
  end.

Fixpoint cf_tau2 (p q : proc) (r : name -> proc) (x : name) 
 (n m : nat) {struct m} : proc :=
  match m with
  | O => par q (cf_b_act p r n x)
  | S m' => par p (cf_tau2 p q r x n m')
  end.

Fixpoint cf_tau3 (p : proc) (q r : name -> proc) (n m : nat) {struct m} :
 proc :=
  match m with
  | O => nu (fun n0 : name => par (q n0) (cf_b_act p r n n0))
  | S m' => par p (cf_tau3 p q r n m')
  end.

Fixpoint frepl1 (p q : proc) (n : nat) {struct n} : proc :=
  match n with
  | O => q
  | S m => par p (frepl1 p q m)
  end.

Fixpoint frepl2 (p q : proc) (r : name -> proc) (x : name) 
 (n m : nat) {struct m} : proc :=
  match m with
  | O => par (r x) (frepl1 p q n)
  | S m' => par p (frepl2 p q r x n m')
  end.

Fixpoint frepl3 (p q : proc) (r : name -> proc) (x : name) 
 (n m : nat) {struct m} : proc :=
  match m with
  | O => par q (frepl1 p (r x) n)
  | S m' => par p (frepl3 p q r x n m')
  end.

Fixpoint frepl4 (p : proc) (q r : name -> proc) (n m : nat) {struct m} :
 proc :=
  match m with
  | O => nu (fun n0 : name => par (q n0) (frepl1 p (r n0) n))
  | S m' => par p (frepl4 p q r n m')
  end.

(*******************************************************************)
(* Lemmata about canonical forms of reducts derived from processes *)
(* whose head constructor is the ! operator.                       *)
(*******************************************************************)

Lemma BANG_OUT :
 forall (p q : proc) (x y : name),
 ftrans (bang p) (Out x y) q ->
 exists r : proc,
   (exists n : nat, q = cf_f_act p r n /\ ftrans p (Out x y) r).

Proof.

simple induction q; intros; auto.

inversion_clear H; inversion_clear H0.

inversion_clear H0; inversion_clear H1.

inversion_clear H0; inversion_clear H1.

inversion_clear H1; inversion H2.
exists p0; exists 0; simpl in |- *; split; [ trivial | assumption ].
rewrite <- H6 in H5; rewrite <- H6; elim (H0 x y H5); intros.
inversion_clear H8.
inversion_clear H9.
exists x0; exists (S x1); split;
 [ simpl in |- *; rewrite H8; trivial | assumption ].

inversion_clear H1; inversion_clear H2.

inversion_clear H0; inversion_clear H1.

inversion_clear H0; inversion_clear H1.

inversion_clear H0; inversion_clear H1.

inversion_clear H0; inversion_clear H1.

inversion_clear H0; inversion_clear H1.

Qed.


Lemma PRE_BANG_BTR :
 forall (p q : proc) (r : name -> proc) (a : b_act) (x : name),
 notin x (nu r) ->
 notin x p ->
 q = r x ->
 btrans (bang p) a r ->
 exists s : name -> proc,
   (exists n : nat, r = cf_b_act p s n /\ btrans p a s).


Proof.

simple induction q; intros; auto.

cut (r = (fun _ : name => nil)); [ intro | apply proc_ext with x; auto ].
rewrite H3 in H2; inversion_clear H2.
inversion H4;
 [ absurd (par (p0 x) (bang p) = nil);
    [ discriminate
    | change
        ((fun n : name => par (p0 n) (bang p)) x = (fun _ : name => nil) x)
       in |- *; rewrite H8; trivial ]
 | absurd (par p (p0 x) = nil);
    [ discriminate
    | change ((fun n : name => par p (p0 n)) x = (fun _ : name => nil) x)
       in |- *; rewrite H8; trivial ] ].
apply notin_nu; intros; apply notin_nil.

elim (proc_exp p0 x); intros.
inversion_clear H4.
rewrite H6 in H2.
cut (r = (fun n : name => bang (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H4 in H3; inversion_clear H3.
inversion H7;
 [ absurd (par (p3 x) (bang p) = bang (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n : name => bang (x0 n)) x) in |- *; 
       rewrite H11; trivial ]
 | absurd (par p (p3 x) = bang (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x = (fun n : name => bang (x0 n)) x)
       in |- *; rewrite H11; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_bang; auto.

elim (proc_exp p0 x); intros.
inversion_clear H4.
rewrite H6 in H2.
cut (r = (fun n : name => tau_pref (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H4 in H3; inversion_clear H3.
inversion H7;
 [ absurd (par (p3 x) (bang p) = tau_pref (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n : name => tau_pref (x0 n)) x) in |- *; 
       rewrite H11; trivial ]
 | absurd (par p (p3 x) = tau_pref (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n : name => tau_pref (x0 n)) x) in |- *; 
       rewrite H11; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_tau; auto.

inversion_clear H4.
inversion H5.
exists p4; exists 0; simpl in |- *; split; [ trivial | assumption ].
cut (p1 = p4 x); [ intro | rewrite <- H8 in H3; inversion_clear H3; trivial ].
cut (notin x (nu p4)); [ intro | rewrite <- H8 in H1; inversion_clear H1 ].
cut
 (exists s : name -> proc,
    (exists n : nat, p4 = cf_b_act p s n /\ btrans p a s));
 [ intro | apply H0 with x; auto ].
inversion_clear H12.
inversion_clear H13.
inversion_clear H12.
exists x0; exists (S x1); split;
 [ simpl in |- *; rewrite <- H13; trivial | assumption ].
apply notin_nu; intros; cut (notin x (par p (p4 z))); [ intro | auto ].
inversion_clear H12; assumption.

elim (proc_exp p0 x); intros; elim (proc_exp p1 x); intros.
inversion_clear H5; inversion_clear H6.
rewrite H8 in H3; rewrite H9 in H3.
cut (r = (fun n : name => sum (x0 n) (x1 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H6 in H4; inversion_clear H4.
inversion H10;
 [ absurd (par (p4 x) (bang p) = sum (x0 x) (x1 x));
    [ discriminate
    | change
        ((fun n : name => par (p4 n) (bang p)) x =
         (fun n : name => sum (x0 n) (x1 n)) x) in |- *; 
       rewrite H14; trivial ]
 | absurd (par p (p4 x) = sum (x0 x) (x1 x));
    [ discriminate
    | change
        ((fun n : name => par p (p4 n)) x =
         (fun n : name => sum (x0 n) (x1 n)) x) in |- *; 
       rewrite H14; trivial ] ].
apply notin_nu; intros; inversion_clear H7; inversion_clear H5;
 apply notin_sum; auto.

elim (ho_proc_exp p0 x); intros.
inversion_clear H4.
rewrite H6 in H2.
cut (r = (fun n : name => nu (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H4 in H3; inversion_clear H3.
inversion H7;
 [ absurd (par (p3 x) (bang p) = nu (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n : name => nu (x0 n)) x) in |- *; rewrite H11; 
       trivial ]
 | absurd (par p (p3 x) = nu (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x = (fun n : name => nu (x0 n)) x)
       in |- *; rewrite H11; trivial ] ].

elim (proc_exp p0 x); intros.
inversion_clear H4.
rewrite H6 in H2.
elim (LEM_name n x); intros; elim (LEM_name n0 x); intros.
rewrite H4 in H2; rewrite H7 in H2.
cut (r = (fun n : name => match_ n n (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = match_ x x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n : name => match_ n n (x0 n)) x) in |- *; 
       rewrite H13; trivial ]
 | absurd (par p (p3 x) = match_ x x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n : name => match_ n n (x0 n)) x) in |- *; 
       rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_match; auto.

rewrite H4 in H2.
cut (r = (fun n : name => match_ n n0 (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = match_ x n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n : name => match_ n n0 (x0 n)) x) in |- *; 
       rewrite H13; trivial ]
 | absurd (par p (p3 x) = match_ x n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n : name => match_ n n0 (x0 n)) x) in |- *; 
       rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_match; auto.

rewrite H7 in H2.
cut (r = (fun n0 : name => match_ n n0 (x0 n0)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = match_ n x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n0 : name => match_ n n0 (x0 n0)) x) 
       in |- *; rewrite H13; trivial ]
 | absurd (par p (p3 x) = match_ n x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n0 : name => match_ n n0 (x0 n0)) x) 
       in |- *; rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_match; auto.

cut (r = (fun n1 : name => match_ n n0 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = match_ n n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n1 : name => match_ n n0 (x0 n1)) x) 
       in |- *; rewrite H13; trivial ]
 | absurd (par p (p3 x) = match_ n n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n1 : name => match_ n n0 (x0 n1)) x) 
       in |- *; rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_match; auto.

elim (proc_exp p0 x); intros.
inversion_clear H4.
rewrite H6 in H2.
elim (LEM_name n x); intros; elim (LEM_name n0 x); intros.
rewrite H4 in H2; rewrite H7 in H2.
cut (r = (fun n : name => mismatch n n (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = mismatch x x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n : name => mismatch n n (x0 n)) x) in |- *; 
       rewrite H13; trivial ]
 | absurd (par p (p3 x) = mismatch x x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n : name => mismatch n n (x0 n)) x) in |- *; 
       rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_mismatch; auto.

rewrite H4 in H2.
cut (r = (fun n : name => mismatch n n0 (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = mismatch x n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n : name => mismatch n n0 (x0 n)) x) 
       in |- *; rewrite H13; trivial ]
 | absurd (par p (p3 x) = mismatch x n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n : name => mismatch n n0 (x0 n)) x) 
       in |- *; rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_mismatch; auto.

rewrite H7 in H2.
cut (r = (fun n0 : name => mismatch n n0 (x0 n0)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = mismatch n x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n0 : name => mismatch n n0 (x0 n0)) x) 
       in |- *; rewrite H13; trivial ]
 | absurd (par p (p3 x) = mismatch n x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n0 : name => mismatch n n0 (x0 n0)) x) 
       in |- *; rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_mismatch; auto.

cut (r = (fun n1 : name => mismatch n n0 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = mismatch n n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n1 : name => mismatch n n0 (x0 n1)) x) 
       in |- *; rewrite H13; trivial ]
 | absurd (par p (p3 x) = mismatch n n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n1 : name => mismatch n n0 (x0 n1)) x) 
       in |- *; rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_mismatch; auto.

elim (ho_proc_exp p0 x); intros.
inversion_clear H4.
rewrite H6 in H2.
elim (LEM_name n x); intros.
rewrite H4 in H2.
cut (r = (fun n : name => in_pref n (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H7 in H3; inversion_clear H3.
inversion H8;
 [ absurd (par (p3 x) (bang p) = in_pref x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n : name => in_pref n (x0 n)) x) in |- *; 
       rewrite H12; trivial ]
 | absurd (par p (p3 x) = in_pref x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n : name => in_pref n (x0 n)) x) in |- *; 
       rewrite H12; trivial ] ].
apply notin_nu; intros; inversion_clear H5.
cut (notin x (nu (x0 z))); [ intro | auto ].
inversion_clear H5; apply notin_in; intros; auto.

cut (r = (fun n0 : name => in_pref n (x0 n0)));
 [ intro | apply proc_ext with x; auto ].
rewrite H7 in H3; inversion_clear H3.
inversion H8;
 [ absurd (par (p3 x) (bang p) = in_pref n (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n0 : name => in_pref n (x0 n0)) x) in |- *; 
       rewrite H12; trivial ]
 | absurd (par p (p3 x) = in_pref n (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n0 : name => in_pref n (x0 n0)) x) in |- *; 
       rewrite H12; trivial ] ].
apply notin_nu; intros; inversion_clear H5.
cut (notin x (nu (x0 z))); [ intro | auto ].
inversion_clear H5; apply notin_in; intros; auto.

elim (proc_exp p0 x); intros.
inversion_clear H4.
rewrite H6 in H2.
elim (LEM_name n x); intros; elim (LEM_name n0 x); intros.
rewrite H4 in H2; rewrite H7 in H2.
cut (r = (fun n : name => out_pref n n (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = out_pref x x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n : name => out_pref n n (x0 n)) x) in |- *; 
       rewrite H13; trivial ]
 | absurd (par p (p3 x) = out_pref x x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n : name => out_pref n n (x0 n)) x) in |- *; 
       rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_out; auto.

rewrite H4 in H2.
cut (r = (fun n : name => out_pref n n0 (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = out_pref x n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n : name => out_pref n n0 (x0 n)) x) 
       in |- *; rewrite H13; trivial ]
 | absurd (par p (p3 x) = out_pref x n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n : name => out_pref n n0 (x0 n)) x) 
       in |- *; rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_out; auto.

rewrite H7 in H2.
cut (r = (fun n0 : name => out_pref n n0 (x0 n0)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = out_pref n x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n0 : name => out_pref n n0 (x0 n0)) x) 
       in |- *; rewrite H13; trivial ]
 | absurd (par p (p3 x) = out_pref n x (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n0 : name => out_pref n n0 (x0 n0)) x) 
       in |- *; rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_out; auto.

cut (r = (fun n1 : name => out_pref n n0 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8 in H3; inversion_clear H3.
inversion H9;
 [ absurd (par (p3 x) (bang p) = out_pref n n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par (p3 n) (bang p)) x =
         (fun n1 : name => out_pref n n0 (x0 n1)) x) 
       in |- *; rewrite H13; trivial ]
 | absurd (par p (p3 x) = out_pref n n0 (x0 x));
    [ discriminate
    | change
        ((fun n : name => par p (p3 n)) x =
         (fun n1 : name => out_pref n n0 (x0 n1)) x) 
       in |- *; rewrite H13; trivial ] ].
apply notin_nu; intros; inversion_clear H5; apply notin_out; auto.

Qed.

Lemma BANG_BTR :
 forall (p : proc) (q : name -> proc) (a : b_act),
 btrans (bang p) a q ->
 exists r : name -> proc,
   (exists n : nat, q = cf_b_act p r n /\ btrans p a r).

Proof.

intros; elim (unsat (par p (nu q)) empty); intros; inversion_clear H0;
 inversion_clear H1; clear H2; apply PRE_BANG_BTR with (q x) x; 
 auto.

Qed.

Lemma BANG_TAU :
 forall p q : proc,
 ftrans (bang p) tau q ->
 (exists r : proc, (exists n : nat, q = cf_f_act p r n /\ ftrans p tau r)) \/
 (exists r : proc,
    (exists s : name -> proc,
       (exists x : name,
          (exists y : name,
             (exists n : nat,
                (exists m : nat,
                   q = cf_tau1 p r s y n m /\
                   ftrans p (Out x y) r /\ btrans p (In x) s)))))) \/
 (exists r : proc,
    (exists s : name -> proc,
       (exists x : name,
          (exists y : name,
             (exists n : nat,
                (exists m : nat,
                   q = cf_tau2 p r s y n m /\
                   ftrans p (Out x y) r /\ btrans p (In x) s)))))) \/
 (exists r : name -> proc,
    (exists s : name -> proc,
       (exists x : name,
          (exists n : nat,
             (exists m : nat,
                q = cf_tau3 p r s n m /\
                btrans p (In x) r /\ btrans p (bOut x) s))))) \/
 (exists r : name -> proc,
    (exists s : name -> proc,
       (exists x : name,
          (exists n : nat,
             (exists m : nat,
                q = cf_tau3 p s r n m /\
                btrans p (In x) r /\ btrans p (bOut x) s))))).

Proof.

simple induction q; intros; auto.

inversion_clear H; inversion_clear H0.

inversion_clear H0; inversion_clear H1.

inversion_clear H0; inversion_clear H1.

inversion_clear H1; inversion H2.
left; exists p0; exists 0; split; [ simpl in |- *; trivial | assumption ].
rewrite <- H6 in H5; rewrite <- H6; elim (H0 H5); intros.
inversion_clear H8.
inversion_clear H9.
inversion_clear H8.
left; exists x; exists (S x0); split;
 [ simpl in |- *; rewrite H9; trivial | assumption ].
elim H8; intros.
inversion_clear H9.
inversion_clear H10.
inversion_clear H9.
inversion_clear H10.
inversion_clear H9.
inversion_clear H10.
inversion_clear H9.
right; left; exists x; exists x0; exists x1; exists x2; exists x3;
 exists (S x4); split; [ simpl in |- *; rewrite H10; trivial | assumption ].
elim H9; intros.
inversion_clear H10.
inversion_clear H11.
inversion_clear H10.
inversion_clear H11.
inversion_clear H10.
inversion_clear H11.
inversion_clear H10.
right; right; left; exists x; exists x0; exists x1; exists x2; exists x3;
 exists (S x4); split; [ simpl in |- *; rewrite H11; trivial | assumption ].
elim H10; intros.
inversion_clear H11.
inversion_clear H12.
inversion_clear H11.
inversion_clear H12.
inversion_clear H11.
inversion_clear H12.
right; right; right; left; exists x; exists x0; exists x1; exists x2;
 exists (S x3); split; [ simpl in |- *; rewrite H11; trivial | assumption ].
inversion_clear H11.
inversion_clear H12.
inversion_clear H11.
inversion_clear H12.
inversion_clear H11.
inversion_clear H12.
right; right; right; right; exists x; exists x0; exists x1; exists x2;
 exists (S x3); split; [ simpl in |- *; rewrite H11; trivial | assumption ].

elim (BANG_OUT p p1 x y H7); intros.
inversion_clear H8.
inversion_clear H9.
right; left; exists x0; exists q1; exists x; exists y; exists x1; exists 0;
 split; [ simpl in |- *; rewrite H8; trivial | split; assumption ].

elim (BANG_BTR p q2 (In x) H7); intros.
inversion_clear H8.
inversion_clear H9.
right; right; left; exists p0; exists x0; exists x; exists y; exists x1;
 exists 0; split; [ simpl in |- *; rewrite H8; trivial | split; assumption ].

inversion_clear H1; inversion_clear H2.

inversion_clear H0; inversion_clear H1.
elim (BANG_BTR p q2 (bOut x) H2); intros.
inversion_clear H1.
inversion_clear H3.
right; right; right; left; exists q1; exists x0; exists x; exists x1;
 exists 0; split; [ simpl in |- *; rewrite H1; trivial | split; assumption ].
elim (BANG_BTR p q2 (In x) H2); intros.
inversion_clear H1.
inversion_clear H3.
right; right; right; right; exists x0; exists q1; exists x; exists x1;
 exists 0; split; [ simpl in |- *; rewrite H1; trivial | split; assumption ].

inversion_clear H0; inversion_clear H1.

inversion_clear H0; inversion_clear H1.

inversion_clear H0; inversion_clear H1.

inversion_clear H0; inversion_clear H1.

Qed.

(*******************************************************)
(* Technical lemmata needed in order to isolate        *)
(* the recursive component from the canonical reducts. *)
(*******************************************************)

Lemma SB_CF_F_ACT :
 forall (p q : proc) (n : nat),
 StBisim (cf_f_act p q n) (par (frepl1 p q n) (bang p)).

Proof.

simple induction n; intros.

simpl in |- *; apply REF.

simpl in |- *; apply TRANS with (par p (par (frepl1 p q n0) (bang p)));
 [ apply PAR_S2; [ apply REF | assumption ] | apply SYM; apply ASS_PAR ].

Qed.

Lemma SB_CF_B_ACT :
 forall (p : proc) (q : name -> proc) (n : nat) (x : name),
 StBisim (cf_b_act p q n x) (par (frepl1 p (q x) n) (bang p)).

Proof.

simple induction n; intros.

simpl in |- *; apply REF.

simpl in |- *; apply TRANS with (par p (par (frepl1 p (q x) n0) (bang p)));
 [ apply PAR_S2; [ apply REF | auto ] | apply SYM; apply ASS_PAR ].

Qed.

Lemma SB_CF_TAU1 :
 forall (p q : proc) (r : name -> proc) (y : name) (n m : nat),
 StBisim (cf_tau1 p q r y n m) (par (frepl2 p q r y n m) (bang p)).

Proof.

simple induction m; intros.

simpl in |- *; apply TRANS with (par (r y) (par (frepl1 p q n) (bang p)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_F_ACT ]
 | apply SYM; apply ASS_PAR ].

simpl in |- *.

simpl in |- *; apply TRANS with (par p (par (frepl2 p q r y n n0) (bang p)));
 [ apply PAR_S2; [ apply REF | assumption ] | apply SYM; apply ASS_PAR ].

Qed.

Lemma SB_CF_TAU2 :
 forall (p q : proc) (r : name -> proc) (y : name) (n m : nat),
 StBisim (cf_tau2 p q r y n m) (par (frepl3 p q r y n m) (bang p)).

Proof.

simple induction m; intros.

simpl in |- *; apply TRANS with (par q (par (frepl1 p (r y) n) (bang p)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT ]
 | apply SYM; apply ASS_PAR ].

simpl in |- *; apply TRANS with (par p (par (frepl3 p q r y n n0) (bang p)));
 [ apply PAR_S2; [ apply REF | assumption ] | apply SYM; apply ASS_PAR ].

Qed.

Lemma SB_CF_TAU3 :
 forall (p : proc) (q r : name -> proc) (y : name) (n m : nat),
 StBisim (cf_tau3 p q r n m) (par (frepl4 p q r n m) (bang p)).

Proof.

simple induction m; intros.

simpl in |- *;
 apply
  TRANS
   with (nu (fun n0 : name => par (q n0) (par (frepl1 p (r n0) n) (bang p))));
 [ apply NU_S; intros; apply PAR_S2; [ apply REF | apply SB_CF_B_ACT ]
 | apply
    TRANS
     with
       (nu (fun n0 : name => par (par (q n0) (frepl1 p (r n0) n)) (bang p)));
    [ apply NU_S; intros; apply SYM; apply ASS_PAR
    | change
        (StBisim
           (nu
              (fun n0 : name =>
               par ((fun u : name => par (q u) (frepl1 p (r u) n)) n0)
                 (bang p)))
           (par (nu (fun n0 : name => par (q n0) (frepl1 p (r n0) n)))
              (bang p))) in |- *; apply NU_EXTR ] ].

simpl in |- *; apply TRANS with (par p (par (frepl4 p q r n n0) (bang p)));
 [ apply PAR_S2; [ apply REF | assumption ] | apply SYM; apply ASS_PAR ].

Qed.

(**********************************************************)
(* Technical lemmata about equivalences between processes *)
(* with an unlimited number of parallel compositions.     *)
(**********************************************************)

Lemma F_REPL1 :
 forall (p q r s : proc) (n : nat),
 StBisim p q -> StBisim r s -> StBisim (frepl1 p r n) (frepl1 q s n).

Proof.

simple induction n; intros.
simpl in |- *; assumption.
simpl in |- *; apply PAR_S2; [ assumption | apply H; assumption ].

Qed.

Lemma F_REPL2 :
 forall (p q r s : proc) (t u : name -> proc) (x : name) (n m : nat),
 StBisim p q ->
 StBisim r s ->
 StBisim (t x) (u x) -> StBisim (frepl2 p r t x n m) (frepl2 q s u x n m).

Proof.

simple induction m; intros.

simpl in |- *; apply PAR_S2; [ assumption | apply F_REPL1; assumption ].

simpl in |- *; apply PAR_S2; auto.

Qed.

Lemma F_REPL3 :
 forall (p q r s : proc) (t u : name -> proc) (x : name) (n m : nat),
 StBisim p q ->
 StBisim r s ->
 StBisim (t x) (u x) -> StBisim (frepl3 p r t x n m) (frepl3 q s u x n m).

Proof.

simple induction m; intros.

simpl in |- *; apply PAR_S2; [ assumption | apply F_REPL1; assumption ].

simpl in |- *; apply PAR_S2; auto.

Qed.

Lemma FREPL1_NOTIN :
 forall (p q : proc) (n : nat) (x : name),
 notin x (frepl1 p q n) -> notin x q.

Proof.

simple induction n; intros.

simpl in H; assumption.

simpl in H0; inversion_clear H0; apply H; assumption.

Qed.

Lemma F_REPL4 :
 forall (p q : proc) (r s t u : name -> proc) (n m : nat),
 StBisim p q ->
 (forall x : name, notin x (nu r) -> notin x (nu s) -> StBisim (r x) (s x)) ->
 (forall x : name, notin x (nu t) -> notin x (nu u) -> StBisim (t x) (u x)) ->
 StBisim (frepl4 p r t n m) (frepl4 q s u n m).

Proof.

simple induction m; intros.

simpl in |- *; apply NU_S; intros; apply PAR_S2.
apply H0; inversion_clear H2; apply notin_nu; intros.
cut (notin x (par (r z) (frepl1 p (t z) n))); [ intro | auto ].
inversion_clear H5; assumption.
inversion_clear H3; cut (notin x (par (s z) (frepl1 q (u z) n)));
 [ intro | auto ].
inversion_clear H3; assumption.
apply F_REPL1.
assumption.
apply H1; inversion_clear H2; apply notin_nu; intros.
cut (notin x (par (r z) (frepl1 p (t z) n))); [ intro | auto ].
inversion_clear H5.
apply FREPL1_NOTIN with p n; assumption.
inversion_clear H3.
cut (notin x (par (s z) (frepl1 q (u z) n))); [ intro | auto ].
inversion_clear H3.
apply FREPL1_NOTIN with q n; assumption.

simpl in |- *; apply PAR_S2; [ assumption | apply H; auto ].

Qed.

(*******************************************************************)
(* Other technical lemmata needed in order to prove the congruence *)
(* of Strong (Late) Bisimilarity w.r.t. the ! operator.            *)
(*******************************************************************)

Lemma CF_B_ACT_NOTIN :
 forall (p : proc) (q : name -> proc) (n : nat) (x : name),
 notin x (nu (cf_b_act p q n)) -> notin x (nu q).

Proof.

simple induction n; intros.

simpl in H; inversion_clear H; apply notin_nu; intros.
cut (notin x (par (q z) (bang p))); [ intro | auto ].
inversion_clear H1; assumption.

simpl in H0; inversion_clear H0; apply H; auto.
apply notin_nu; intros.
cut (notin x (par p (cf_b_act p q n0 z))); [ intro | auto ].
inversion_clear H2; assumption.

Qed.

Lemma BANG_FTR_AUX :
 forall (p q : proc) (a : f_act) (n : nat),
 ftrans p a q -> ftrans (bang p) a (cf_f_act p q n).

Proof.

simple induction n; intros.
simpl in |- *; apply fBANG; apply fPAR1; assumption.
simpl in |- *; apply fBANG; apply fPAR2; apply H; auto.

Qed.

Lemma BANG_BTR_AUX :
 forall (p : proc) (q : name -> proc) (a : b_act) (n : nat),
 btrans p a q -> btrans (bang p) a (cf_b_act p q n).

Proof.

simple induction n; intros.
simpl in |- *; apply bBANG; apply bPAR1; assumption.
simpl in |- *; apply bBANG; apply bPAR2; apply H; auto.

Qed.

Lemma BANG_TAU_AUX1 :
 forall (p q : proc) (r : name -> proc) (x y : name) (n m : nat),
 ftrans p (Out x y) q ->
 btrans p (In x) r -> ftrans (bang p) tau (cf_tau1 p q r y n m).

Proof.

simple induction m; intros.
simpl in |- *; apply fBANG; apply COM1 with x;
 [ assumption | apply BANG_FTR_AUX; assumption ].
simpl in |- *; apply fBANG; apply fPAR2; apply H; assumption.

Qed.

Lemma BANG_TAU_AUX2 :
 forall (p q : proc) (r : name -> proc) (x y : name) (n m : nat),
 ftrans p (Out x y) q ->
 btrans p (In x) r -> ftrans (bang p) tau (cf_tau2 p q r y n m).

Proof.

simple induction m; intros.
simpl in |- *; apply fBANG; apply COM2 with x;
 [ assumption | apply BANG_BTR_AUX; assumption ].
simpl in |- *; apply fBANG; apply fPAR2; apply H; assumption.

Qed.

Lemma BANG_TAU_AUX3 :
 forall (p : proc) (q r : name -> proc) (x : name) (n m : nat),
 btrans p (In x) q ->
 btrans p (bOut x) r -> ftrans (bang p) tau (cf_tau3 p q r n m).

Proof.

simple induction m; intros.
simpl in |- *; apply fBANG; apply CLOSE1 with x;
 [ assumption | apply BANG_BTR_AUX; assumption ].
simpl in |- *; apply fBANG; apply fPAR2; apply H; assumption.

Qed.

Lemma BANG_TAU_AUX4 :
 forall (p : proc) (q r : name -> proc) (x : name) (n m : nat),
 btrans p (bOut x) q ->
 btrans p (In x) r -> ftrans (bang p) tau (cf_tau3 p q r n m).

Proof.

simple induction m; intros.
simpl in |- *; apply fBANG; apply CLOSE2 with x;
 [ assumption | apply BANG_BTR_AUX; assumption ].
simpl in |- *; apply fBANG; apply fPAR2; apply H; assumption.

Qed.

(************************************************)
(* Finally the main goal of this package:       *)
(* the congruence of Strong (Late) Bisimilarity *)
(* w.r.t. the ! operator.                       *)
(************************************************)

Inductive BisBANG_S : proc -> proc -> Prop :=
    bisbang_s :
      forall p q : proc,
      StBisim p q ->
      forall r s : proc,
      StBisim r s -> BisBANG_S (par r (bang p)) (par s (bang q)).

Lemma BANG_S_L6 :
 forall (p q : name -> proc) (x : name),
 notin x (nu p) ->
 notin x (nu q) ->
 BisBANG_S (p x) (q x) ->
 forall y : name, notin y (nu p) -> notin y (nu q) -> BisBANG_S (p y) (q y).

Proof.

intros; elim (LEM_name x y); intro.

rewrite <- H4; assumption.

inversion H1.
elim (proc_exp r x); elim (proc_exp s x); elim (proc_exp p0 x);
 elim (proc_exp q0 x); intros.
inversion_clear H9; inversion_clear H10; inversion_clear H11;
 inversion_clear H12.
rewrite H14 in H6; rewrite H15 in H5; rewrite H16 in H6; rewrite H17 in H5.
cut (p = (fun n : name => par (x3 n) (bang (x1 n))));
 [ intro | apply proc_ext with x; auto ].
cut (q = (fun n : name => par (x2 n) (bang (x0 n))));
 [ intro | apply proc_ext with x; auto ].
rewrite H12; rewrite H18; apply bisbang_s; auto.
rewrite H14 in H7; rewrite H15 in H7; apply L6_Light with x; auto.
rewrite H12 in H2; inversion_clear H2; apply notin_nu; intros;
 cut (notin y (par (x3 z) (bang (x1 z)))); [ intro | auto ];
 inversion_clear H15; inversion_clear H20; inversion_clear H21; 
 assumption.
rewrite H18 in H3; inversion_clear H3; apply notin_nu; intros;
 cut (notin y (par (x2 z) (bang (x0 z)))); [ intro | auto ];
 inversion_clear H15; inversion_clear H20; inversion_clear H21; 
 assumption.
rewrite H16 in H8; rewrite H17 in H8; apply L6_Light with x; auto.
rewrite H12 in H2; inversion_clear H2; apply notin_nu; intros;
 cut (notin y (par (x3 z) (bang (x1 z)))); [ intro | auto ];
 inversion_clear H15; inversion_clear H20; assumption.
rewrite H18 in H3; inversion_clear H3; apply notin_nu; intros;
 cut (notin y (par (x2 z) (bang (x0 z)))); [ intro | auto ];
 inversion_clear H15; inversion_clear H20; assumption.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H10; auto | apply notin_bang; inversion_clear H13; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H11; auto | apply notin_bang; inversion_clear H9; auto ].

Qed.

Lemma BisBANG_S_FTR1 :
 forall p q : proc,
 BisBANG_S p q ->
 forall x y : name,
 (forall p1 : proc,
  ftrans p (Out x y) p1 ->
  exists q1 : proc, ftrans q (Out x y) q1 /\ SB_R_SB BisBANG_S p1 q1) /\
 (forall q1 : proc,
  ftrans q (Out x y) q1 ->
  exists p1 : proc, ftrans p (Out x y) p1 /\ SB_R_SB BisBANG_S p1 q1).

Proof.

intros; inversion H; split; intros.

inversion H4.

inversion_clear H1; inversion_clear H10.
elim (H1 (Out x y)); intros.
elim (H10 p4 H9); intros; inversion_clear H13.
exists (par x0 (bang q0)); split;
 [ apply fPAR1; assumption
 | unfold SB_R_SB in |- *; exists (par p4 (bang p0));
    exists (par x0 (bang q0)); split;
    [ apply REF | split; [ apply bisbang_s; auto | apply REF ] ] ].

elim (BANG_OUT p0 p4 x y H9); intros; inversion_clear H10;
 inversion_clear H11.
inversion H0; inversion_clear H11.
elim (H15 (Out x y)); intros.
elim (H11 x0 H12); intros; inversion_clear H18.
exists (par s (cf_f_act q0 x2 x1)); split.
apply fPAR2; apply BANG_FTR_AUX; assumption.
rewrite H10; unfold SB_R_SB in |- *;
 exists (par (par r (frepl1 p0 x0 x1)) (bang p0));
 exists (par (par s (frepl1 q0 x2 x1)) (bang q0)); 
 split.
apply TRANS with (par r (par (frepl1 p0 x0 x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_F_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s; auto; apply PAR_S2;
    [ assumption | apply F_REPL1; assumption ]
 | apply TRANS with (par s (par (frepl1 q0 x2 x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_F_ACT; assumption ] ] ].

inversion H4.

inversion_clear H1; inversion_clear H10.
elim (H1 (Out x y)); intros.
elim (H12 p3 H9); intros; inversion_clear H13.
exists (par x0 (bang p0)); split;
 [ apply fPAR1; assumption
 | unfold SB_R_SB in |- *; exists (par x0 (bang p0));
    exists (par p3 (bang q0)); split;
    [ apply REF | split; [ apply bisbang_s; auto | apply REF ] ] ].

elim (BANG_OUT q0 p3 x y H9); intros; inversion_clear H10;
 inversion_clear H11.
inversion H0; inversion_clear H11.
elim (H15 (Out x y)); intros.
elim (H17 x0 H12); intros; inversion_clear H18.
exists (par r (cf_f_act p0 x2 x1)); split.
apply fPAR2; apply BANG_FTR_AUX; assumption.
rewrite H10; unfold SB_R_SB in |- *;
 exists (par (par r (frepl1 p0 x2 x1)) (bang p0));
 exists (par (par s (frepl1 q0 x0 x1)) (bang q0)); 
 split.
apply TRANS with (par r (par (frepl1 p0 x2 x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_F_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s; auto; apply PAR_S2;
    [ assumption | apply F_REPL1; assumption ]
 | apply TRANS with (par s (par (frepl1 q0 x0 x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_F_ACT; assumption ] ] ].

Qed.

Lemma BisBANG_S_IN :
 forall p q : proc,
 BisBANG_S p q ->
 forall x : name,
 (forall p1 : name -> proc,
  btrans p (In x) p1 ->
  exists q1 : name -> proc,
    btrans q (In x) q1 /\ (forall y : name, SB_R_SB BisBANG_S (p1 y) (q1 y))) /\
 (forall q1 : name -> proc,
  btrans q (In x) q1 ->
  exists p1 : name -> proc,
    btrans p (In x) p1 /\ (forall y : name, SB_R_SB BisBANG_S (p1 y) (q1 y))).

Proof.

intros; inversion H; split; intros.

inversion H4.

inversion_clear H1; inversion_clear H10; inversion_clear H11.
elim (H10 x); intros.
elim (H11 p4 H9); intros; inversion_clear H14.
exists (fun n : name => par (x0 n) (bang q0)); split;
 [ apply bPAR1; assumption
 | intro; unfold SB_R_SB in |- *; exists (par (p4 y) (bang p0));
    exists (par (x0 y) (bang q0)); split;
    [ apply REF | split; [ apply bisbang_s; auto | apply REF ] ] ].

elim (BANG_BTR p0 p4 (In x) H9); intros; inversion_clear H10;
 inversion_clear H11.
inversion H0; inversion_clear H11; inversion_clear H16.
elim (H11 x); intros.
elim (H16 x0 H12); intros; inversion_clear H19.
exists (fun n : name => par s (cf_b_act q0 x2 x1 n)); split.
apply bPAR2; apply BANG_BTR_AUX; assumption.
rewrite H10; intro; unfold SB_R_SB in |- *;
 exists (par (par r (frepl1 p0 (x0 y) x1)) (bang p0));
 exists (par (par s (frepl1 q0 (x2 y) x1)) (bang q0)); 
 split.
apply TRANS with (par r (par (frepl1 p0 (x0 y) x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s; auto; apply PAR_S2; [ assumption | apply F_REPL1; auto ]
 | apply TRANS with (par s (par (frepl1 q0 (x2 y) x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_B_ACT; assumption ] ] ].

inversion H4.

inversion_clear H1; inversion_clear H10; inversion_clear H11.
elim (H10 x); intros.
elim (H13 p3 H9); intros; inversion_clear H14.
exists (fun n : name => par (x0 n) (bang p0)); split;
 [ apply bPAR1; assumption
 | intro; unfold SB_R_SB in |- *; exists (par (x0 y) (bang p0));
    exists (par (p3 y) (bang q0)); split;
    [ apply REF | split; [ apply bisbang_s; auto | apply REF ] ] ].

elim (BANG_BTR q0 p3 (In x) H9); intros; inversion_clear H10;
 inversion_clear H11.
inversion H0; inversion_clear H11; inversion_clear H16.
elim (H11 x); intros.
elim (H18 x0 H12); intros; inversion_clear H19.
exists (fun n : name => par r (cf_b_act p0 x2 x1 n)); split.
apply bPAR2; apply BANG_BTR_AUX; assumption.
rewrite H10; intro; unfold SB_R_SB in |- *;
 exists (par (par r (frepl1 p0 (x2 y) x1)) (bang p0));
 exists (par (par s (frepl1 q0 (x0 y) x1)) (bang q0)); 
 split.
apply TRANS with (par r (par (frepl1 p0 (x2 y) x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s; auto; apply PAR_S2; [ assumption | apply F_REPL1; auto ]
 | apply TRANS with (par s (par (frepl1 q0 (x0 y) x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_B_ACT; assumption ] ] ].

Qed.

Lemma BisBANG_S_bOUT :
 forall p q : proc,
 BisBANG_S p q ->
 forall x : name,
 (forall p1 : name -> proc,
  btrans p (bOut x) p1 ->
  exists q1 : name -> proc,
    btrans q (bOut x) q1 /\
    (forall y : name,
     notin y (nu p1) -> notin y (nu q1) -> SB_R_SB BisBANG_S (p1 y) (q1 y))) /\
 (forall q1 : name -> proc,
  btrans q (bOut x) q1 ->
  exists p1 : name -> proc,
    btrans p (bOut x) p1 /\
    (forall y : name,
     notin y (nu p1) -> notin y (nu q1) -> SB_R_SB BisBANG_S (p1 y) (q1 y))).

Proof.

intros; inversion H; split; intros.

inversion H4.

inversion_clear H1; inversion_clear H10; inversion_clear H11.
elim (H12 x); intros.
elim (H11 p4 H9); intros; inversion_clear H14.
exists (fun n : name => par (x0 n) (bang q0)); split;
 [ apply bPAR1; assumption
 | intros; unfold SB_R_SB in |- *; exists (par (p4 y) (bang p0));
    exists (par (x0 y) (bang q0)); split;
    [ apply REF
    | split; [ apply bisbang_s; auto; apply H16; auto | apply REF ] ] ].
inversion_clear H14; apply notin_nu; intros;
 cut (notin y (par (p4 z) (bang p0))); [ intro | auto ]; 
 inversion_clear H19; auto.
inversion_clear H17; apply notin_nu; intros;
 cut (notin y (par (x0 z) (bang q0))); [ intro | auto ]; 
 inversion_clear H19; auto.

elim (BANG_BTR p0 p4 (bOut x) H9); intros; inversion_clear H10;
 inversion_clear H11.
inversion H0; inversion_clear H11; inversion_clear H16.
elim (H17 x); intros.
elim (H16 x0 H12); intros; inversion_clear H19.
exists (fun n : name => par s (cf_b_act q0 x2 x1 n)); split.
apply bPAR2; apply BANG_BTR_AUX; assumption.
rewrite H10; intros; unfold SB_R_SB in |- *;
 exists (par (par r (frepl1 p0 (x0 y) x1)) (bang p0));
 exists (par (par s (frepl1 q0 (x2 y) x1)) (bang q0)); 
 split.
apply TRANS with (par r (par (frepl1 p0 (x0 y) x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s; auto; apply PAR_S2;
    [ assumption
    | apply F_REPL1; auto; apply H21;
       [ apply CF_B_ACT_NOTIN with p0 x1; apply notin_nu; intros;
          inversion_clear H19; cut (notin y (par r (cf_b_act p0 x0 x1 z)));
          [ intro | auto ]; inversion_clear H19; auto
       | apply CF_B_ACT_NOTIN with q0 x1; apply notin_nu; intros;
          inversion_clear H22; cut (notin y (par s (cf_b_act q0 x2 x1 z)));
          [ intro | auto ]; inversion_clear H22; auto ] ]
 | apply TRANS with (par s (par (frepl1 q0 (x2 y) x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_B_ACT; assumption ] ] ].

inversion H4.

inversion_clear H1; inversion_clear H10; inversion_clear H11.
elim (H12 x); intros.
elim (H13 p3 H9); intros; inversion_clear H14.
exists (fun n : name => par (x0 n) (bang p0)); split;
 [ apply bPAR1; assumption
 | intros; unfold SB_R_SB in |- *; exists (par (x0 y) (bang p0));
    exists (par (p3 y) (bang q0)); split;
    [ apply REF
    | split; [ apply bisbang_s; auto; apply H16; auto | apply REF ] ] ].
inversion_clear H14; apply notin_nu; intros;
 cut (notin y (par (x0 z) (bang p0))); [ intro | auto ]; 
 inversion_clear H19; auto.
inversion_clear H17; apply notin_nu; intros;
 cut (notin y (par (p3 z) (bang q0))); [ intro | auto ]; 
 inversion_clear H19; auto.

elim (BANG_BTR q0 p3 (bOut x) H9); intros; inversion_clear H10;
 inversion_clear H11.
inversion H0; inversion_clear H11; inversion_clear H16.
elim (H17 x); intros.
elim (H18 x0 H12); intros; inversion_clear H19.
exists (fun n : name => par r (cf_b_act p0 x2 x1 n)); split.
apply bPAR2; apply BANG_BTR_AUX; assumption.
rewrite H10; intros; unfold SB_R_SB in |- *;
 exists (par (par r (frepl1 p0 (x2 y) x1)) (bang p0));
 exists (par (par s (frepl1 q0 (x0 y) x1)) (bang q0)); 
 split.
apply TRANS with (par r (par (frepl1 p0 (x2 y) x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s; auto; apply PAR_S2;
    [ assumption
    | apply F_REPL1; auto; apply H21;
       [ apply CF_B_ACT_NOTIN with p0 x1; apply notin_nu; intros;
          inversion_clear H19; cut (notin y (par r (cf_b_act p0 x2 x1 z)));
          [ intro | auto ]; inversion_clear H19; auto
       | apply CF_B_ACT_NOTIN with q0 x1; apply notin_nu; intros;
          inversion_clear H22; cut (notin y (par s (cf_b_act q0 x0 x1 z)));
          [ intro | auto ]; inversion_clear H22; auto ] ]
 | apply TRANS with (par s (par (frepl1 q0 (x0 y) x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_B_ACT; assumption ] ] ].

Qed.

Lemma BisBANG_S_FTR2 :
 forall p q : proc,
 BisBANG_S p q ->
 (forall p1 : proc,
  ftrans p tau p1 ->
  exists q1 : proc,
    ftrans q tau q1 /\
    ((exists p1' : proc,
        (exists q1' : proc,
           StBisim p1 p1' /\ BisBANG_S p1' q1' /\ StBisim q1' q1)) \/
     (exists p1' : name -> proc,
        (exists q1' : name -> proc,
           StBisim p1 (nu p1') /\
           (forall z : name,
            notin z (nu p1') -> notin z (nu q1') -> BisBANG_S (p1' z) (q1' z)) /\
           StBisim (nu q1') q1)))) /\
 (forall q1 : proc,
  ftrans q tau q1 ->
  exists p1 : proc,
    ftrans p tau p1 /\
    ((exists p1' : proc,
        (exists q1' : proc,
           StBisim p1 p1' /\ BisBANG_S p1' q1' /\ StBisim q1' q1)) \/
     (exists p1' : name -> proc,
        (exists q1' : name -> proc,
           StBisim p1 (nu p1') /\
           (forall z : name,
            notin z (nu p1') -> notin z (nu q1') -> BisBANG_S (p1' z) (q1' z)) /\
           StBisim (nu q1') q1)))).

Proof.

intros; inversion H; split; intros.

inversion H4.

inversion_clear H1; inversion_clear H10.
elim (H1 tau); intros.
elim (H10 p4 H9); intros; inversion_clear H13.
exists (par x (bang q0)); split;
 [ apply fPAR1; assumption
 | left; exists (par p4 (bang p0)); exists (par x (bang q0)); split;
    [ apply REF | split; [ apply bisbang_s; auto | apply REF ] ] ].

elim (BANG_TAU p0 p4 H9); intros; inversion_clear H10; inversion_clear H11;
 inversion_clear H10.
inversion H0; inversion_clear H10.
elim (H15 tau); intros.
elim (H10 x H12); intros; inversion_clear H18.
exists (par s (cf_f_act q0 x1 x0)); split;
 [ apply fPAR2; apply BANG_FTR_AUX; assumption
 | rewrite H11; left; exists (par (par r (frepl1 p0 x x0)) (bang p0));
    exists (par (par s (frepl1 q0 x1 x0)) (bang q0)); 
    split ].
apply TRANS with (par r (par (frepl1 p0 x x0) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_F_ACT ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ assumption | apply F_REPL1; assumption ] ]
 | apply TRANS with (par s (par (frepl1 q0 x1 x0) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_F_ACT ] ] ].

inversion_clear H11; inversion_clear H10; inversion_clear H11;
 inversion_clear H10; inversion_clear H11; inversion_clear H12.
inversion H0; inversion_clear H12; inversion_clear H17.
elim (H16 (Out x1 x2)); elim (H12 x1); intros.
elim (H17 x0 H13); elim (H20 x H11); intros; inversion_clear H22;
 inversion_clear H23.
exists (par s (cf_tau1 q0 x5 x6 x2 x3 x4)); split;
 [ apply fPAR2; apply BANG_TAU_AUX1 with x1; assumption
 | rewrite H10; left;
    exists (par (par r (frepl2 p0 x x0 x2 x3 x4)) (bang p0));
    exists (par (par s (frepl2 q0 x5 x6 x2 x3 x4)) (bang q0)); 
    split ].
apply TRANS with (par r (par (frepl2 p0 x x0 x2 x3 x4) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_TAU1 ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ assumption | apply F_REPL2; auto ] ]
 | apply TRANS with (par s (par (frepl2 q0 x5 x6 x2 x3 x4) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_TAU1 ] ] ].

inversion_clear H11; inversion_clear H10; inversion_clear H11;
 inversion_clear H10; inversion_clear H11; inversion_clear H10;
 inversion_clear H12.
inversion H0; inversion_clear H12; inversion_clear H17.
elim (H16 (Out x1 x2)); elim (H12 x1); intros.
elim (H17 x0 H13); elim (H20 x H10); intros; inversion_clear H22;
 inversion_clear H23.
exists (par s (cf_tau2 q0 x5 x6 x2 x3 x4)); split;
 [ apply fPAR2; apply BANG_TAU_AUX2 with x1; assumption
 | rewrite H11; left;
    exists (par (par r (frepl3 p0 x x0 x2 x3 x4)) (bang p0));
    exists (par (par s (frepl3 q0 x5 x6 x2 x3 x4)) (bang q0)); 
    split ].
apply TRANS with (par r (par (frepl3 p0 x x0 x2 x3 x4) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_TAU2 ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ assumption | apply F_REPL3; auto ] ]
 | apply TRANS with (par s (par (frepl3 q0 x5 x6 x2 x3 x4) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_TAU2 ] ] ].

inversion_clear H11; inversion_clear H10; inversion_clear H11;
 inversion_clear H10; inversion_clear H11; inversion_clear H10;
 inversion_clear H12.
inversion H0; inversion_clear H12; inversion_clear H17.
elim (H12 x1); elim (H18 x1); intros.
elim (H17 x0 H13); elim (H20 x H10); intros; inversion_clear H22;
 inversion_clear H23.
exists (par s (cf_tau3 q0 x4 x5 x2 x3)); split.
apply fPAR2; apply BANG_TAU_AUX3 with x1; assumption.
rewrite H11; left; exists (par (par r (frepl4 p0 x x0 x2 x3)) (bang p0));
 exists (par (par s (frepl4 q0 x4 x5 x2 x3)) (bang q0)); 
 split.
apply TRANS with (par r (par (frepl4 p0 x x0 x2 x3) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_TAU3; auto ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ assumption | apply F_REPL4; auto ] ]
 | apply TRANS with (par s (par (frepl4 q0 x4 x5 x2 x3) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_TAU3; assumption ] ] ].

inversion_clear H11; inversion_clear H10; inversion_clear H11;
 inversion_clear H10; inversion_clear H11; inversion_clear H10;
 inversion_clear H12.
inversion H0; inversion_clear H12; inversion_clear H17.
elim (H12 x1); elim (H18 x1); intros.
elim (H17 x0 H13); elim (H20 x H10); intros; inversion_clear H22;
 inversion_clear H23.
exists (par s (cf_tau3 q0 x5 x4 x2 x3)); split.
apply fPAR2; apply BANG_TAU_AUX4 with x1; assumption.
rewrite H11; left; exists (par (par r (frepl4 p0 x0 x x2 x3)) (bang p0));
 exists (par (par s (frepl4 q0 x5 x4 x2 x3)) (bang q0)); 
 split.
apply TRANS with (par r (par (frepl4 p0 x0 x x2 x3) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_TAU3; auto ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ assumption | apply F_REPL4; auto ] ]
 | apply TRANS with (par s (par (frepl4 q0 x5 x4 x2 x3) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_TAU3; assumption ] ] ].

elim (BANG_OUT p0 q2 x y H8); intros; inversion_clear H10;
 inversion_clear H11; inversion H0; inversion H1; inversion_clear H11;
 inversion_clear H15; inversion_clear H20.
elim (H18 (Out x y)); elim (H15 x); intros.
elim (H20 q1 H7); elim (H23 x0 H12); intros; inversion_clear H25;
 inversion_clear H26.
exists (par (x3 y) (cf_f_act q0 x2 x1)); split.
apply COM1 with x; [ assumption | apply BANG_FTR_AUX; assumption ].
rewrite H10; left; exists (par (par (q1 y) (frepl1 p0 x0 x1)) (bang p0));
 exists (par (par (x3 y) (frepl1 q0 x2 x1)) (bang q0)); 
 split.
apply TRANS with (par (q1 y) (par (frepl1 p0 x0 x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_F_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ auto | apply F_REPL1; assumption ] ]
 | apply TRANS with (par (x3 y) (par (frepl1 q0 x2 x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_F_ACT; assumption ] ] ].

elim (BANG_BTR p0 q2 (In x) H8); intros; inversion_clear H10;
 inversion_clear H11; inversion H0; inversion H1; inversion_clear H11;
 inversion_clear H15; inversion_clear H19.
elim (H11 (Out x y)); elim (H15 x); intros.
elim (H19 x0 H12); elim (H23 q1 H7); intros; inversion_clear H25;
 inversion_clear H26.
exists (par x2 (cf_b_act q0 x3 x1 y)); split.
apply COM2 with x; [ assumption | apply BANG_BTR_AUX; assumption ].
rewrite H10; left; exists (par (par q1 (frepl1 p0 (x0 y) x1)) (bang p0));
 exists (par (par x2 (frepl1 q0 (x3 y) x1)) (bang q0)); 
 split.
apply TRANS with (par q1 (par (frepl1 p0 (x0 y) x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ auto | apply F_REPL1; auto ] ]
 | apply TRANS with (par x2 (par (frepl1 q0 (x3 y) x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_B_ACT; assumption ] ] ].

elim (BANG_BTR p0 q2 (bOut x) H8); intros; inversion_clear H10;
 inversion_clear H11; inversion H0; inversion H1; inversion_clear H11;
 inversion_clear H15; inversion_clear H19; inversion_clear H20.
elim (H19 x); elim (H21 x); intros.
elim (H20 x0 H12); elim (H24 q1 H7); intros; inversion_clear H26;
 inversion_clear H27.
exists (nu (fun n : name => par (x2 n) (cf_b_act q0 x3 x1 n))); split.
apply CLOSE1 with x; [ assumption | apply BANG_BTR_AUX; assumption ].
rewrite H10; right.
exists (fun n : name => par (par (q1 n) (frepl1 p0 (x0 n) x1)) (bang p0));
 exists (fun n : name => par (par (x2 n) (frepl1 q0 (x3 n) x1)) (bang q0));
 split.
apply NU_S; intros;
 apply TRANS with (par (q1 x4) (par (frepl1 p0 (x0 x4) x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ intros; apply bisbang_s;
    [ assumption
    | apply PAR_S2;
       [ auto
       | apply F_REPL1; auto; apply H30;
          [ apply notin_nu; intros; apply FREPL1_NOTIN with p0 x1;
             inversion_clear H27;
             cut
              (notin z (par (par (q1 z0) (frepl1 p0 (x0 z0) x1)) (bang p0)));
             [ intro | auto ]; inversion_clear H27; 
             inversion_clear H34; assumption
          | apply notin_nu; intros; apply FREPL1_NOTIN with q0 x1;
             inversion_clear H31;
             cut
              (notin z (par (par (x2 z0) (frepl1 q0 (x3 z0) x1)) (bang q0)));
             [ intro | auto ]; inversion_clear H31; 
             inversion_clear H34; assumption ] ] ]
 | apply NU_S; intros;
    apply TRANS with (par (x2 x4) (par (frepl1 q0 (x3 x4) x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_B_ACT; assumption ] ] ].

elim (BANG_BTR p0 q2 (In x) H8); intros; inversion_clear H10;
 inversion_clear H11; inversion H0; inversion H1; inversion_clear H11;
 inversion_clear H15; inversion_clear H19; inversion_clear H20.
elim (H15 x); elim (H22 x); intros.
elim (H20 q1 H7); elim (H24 x0 H12); intros; inversion_clear H26;
 inversion_clear H27.
exists (nu (fun n : name => par (x3 n) (cf_b_act q0 x2 x1 n))); split.
apply CLOSE2 with x; [ assumption | apply BANG_BTR_AUX; assumption ].
rewrite H10; right.
exists (fun n : name => par (par (q1 n) (frepl1 p0 (x0 n) x1)) (bang p0));
 exists (fun n : name => par (par (x3 n) (frepl1 q0 (x2 n) x1)) (bang q0));
 split.
apply NU_S; intros;
 apply TRANS with (par (q1 x4) (par (frepl1 p0 (x0 x4) x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ intros; apply bisbang_s;
    [ assumption
    | apply PAR_S2;
       [ apply H30;
          [ apply notin_nu; intros; inversion_clear H27;
             cut
              (notin z (par (par (q1 z0) (frepl1 p0 (x0 z0) x1)) (bang p0)));
             [ intro | auto ]; inversion_clear H27; 
             inversion_clear H34; assumption
          | apply notin_nu; intros; inversion_clear H31;
             cut
              (notin z (par (par (x3 z0) (frepl1 q0 (x2 z0) x1)) (bang q0)));
             [ intro | auto ]; inversion_clear H31; 
             inversion_clear H34; assumption ]
       | apply F_REPL1; auto ] ]
 | apply NU_S; intros;
    apply TRANS with (par (x3 x4) (par (frepl1 q0 (x2 x4) x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_B_ACT; assumption ] ] ].

inversion H4.

inversion_clear H1; inversion_clear H10.
elim (H1 tau); intros.
elim (H12 p3 H9); intros; inversion_clear H13.
exists (par x (bang p0)); split;
 [ apply fPAR1; assumption
 | left; exists (par x (bang p0)); exists (par p3 (bang q0)); split;
    [ apply REF | split; [ apply bisbang_s; auto | apply REF ] ] ].

elim (BANG_TAU q0 p3 H9); intros; inversion_clear H10; inversion_clear H11;
 inversion_clear H10.
inversion H0; inversion_clear H10.
elim (H15 tau); intros.
elim (H17 x H12); intros; inversion_clear H18.
exists (par r (cf_f_act p0 x1 x0)); split;
 [ apply fPAR2; apply BANG_FTR_AUX; assumption
 | rewrite H11; left; exists (par (par r (frepl1 p0 x1 x0)) (bang p0));
    exists (par (par s (frepl1 q0 x x0)) (bang q0)); 
    split ].
apply TRANS with (par r (par (frepl1 p0 x1 x0) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_F_ACT ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ assumption | apply F_REPL1; assumption ] ]
 | apply TRANS with (par s (par (frepl1 q0 x x0) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_F_ACT ] ] ].

inversion_clear H11; inversion_clear H10; inversion_clear H11;
 inversion_clear H10; inversion_clear H11; inversion_clear H12.
inversion H0; inversion_clear H12; inversion_clear H17.
elim (H16 (Out x1 x2)); elim (H12 x1); intros.
elim (H19 x0 H13); elim (H21 x H11); intros; inversion_clear H22;
 inversion_clear H23.
exists (par r (cf_tau1 p0 x5 x6 x2 x3 x4)); split;
 [ apply fPAR2; apply BANG_TAU_AUX1 with x1; assumption
 | rewrite H10; left;
    exists (par (par r (frepl2 p0 x5 x6 x2 x3 x4)) (bang p0));
    exists (par (par s (frepl2 q0 x x0 x2 x3 x4)) (bang q0)); 
    split ].
apply TRANS with (par r (par (frepl2 p0 x5 x6 x2 x3 x4) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_TAU1 ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ assumption | apply F_REPL2; auto ] ]
 | apply TRANS with (par s (par (frepl2 q0 x x0 x2 x3 x4) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_TAU1 ] ] ].

inversion_clear H11; inversion_clear H10; inversion_clear H11;
 inversion_clear H10; inversion_clear H11; inversion_clear H10;
 inversion_clear H12.
inversion H0; inversion_clear H12; inversion_clear H17.
elim (H16 (Out x1 x2)); elim (H12 x1); intros.
elim (H19 x0 H13); elim (H21 x H10); intros; inversion_clear H22;
 inversion_clear H23.
exists (par r (cf_tau2 p0 x5 x6 x2 x3 x4)); split;
 [ apply fPAR2; apply BANG_TAU_AUX2 with x1; assumption
 | rewrite H11; left;
    exists (par (par r (frepl3 p0 x5 x6 x2 x3 x4)) (bang p0));
    exists (par (par s (frepl3 q0 x x0 x2 x3 x4)) (bang q0)); 
    split ].
apply TRANS with (par r (par (frepl3 p0 x5 x6 x2 x3 x4) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_TAU2 ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ assumption | apply F_REPL3; auto ] ]
 | apply TRANS with (par s (par (frepl3 q0 x x0 x2 x3 x4) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_TAU2 ] ] ].

inversion_clear H11; inversion_clear H10; inversion_clear H11;
 inversion_clear H10; inversion_clear H11; inversion_clear H10;
 inversion_clear H12.
inversion H0; inversion_clear H12; inversion_clear H17.
elim (H12 x1); elim (H18 x1); intros.
elim (H19 x0 H13); elim (H21 x H10); intros; inversion_clear H22;
 inversion_clear H23.
exists (par r (cf_tau3 p0 x4 x5 x2 x3)); split.
apply fPAR2; apply BANG_TAU_AUX3 with x1; assumption.
rewrite H11; left; exists (par (par r (frepl4 p0 x4 x5 x2 x3)) (bang p0));
 exists (par (par s (frepl4 q0 x x0 x2 x3)) (bang q0)); 
 split.
apply TRANS with (par r (par (frepl4 p0 x4 x5 x2 x3) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_TAU3; auto ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ assumption | apply F_REPL4; auto ] ]
 | apply TRANS with (par s (par (frepl4 q0 x x0 x2 x3) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_TAU3; assumption ] ] ].

inversion_clear H11; inversion_clear H10; inversion_clear H11;
 inversion_clear H10; inversion_clear H11; inversion_clear H10;
 inversion_clear H12.
inversion H0; inversion_clear H12; inversion_clear H17.
elim (H12 x1); elim (H18 x1); intros.
elim (H19 x0 H13); elim (H21 x H10); intros; inversion_clear H22;
 inversion_clear H23.
exists (par r (cf_tau3 p0 x5 x4 x2 x3)); split.
apply fPAR2; apply BANG_TAU_AUX4 with x1; assumption.
rewrite H11; left; exists (par (par r (frepl4 p0 x5 x4 x2 x3)) (bang p0));
 exists (par (par s (frepl4 q0 x0 x x2 x3)) (bang q0)); 
 split.
apply TRANS with (par r (par (frepl4 p0 x5 x4 x2 x3) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_TAU3; auto ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ assumption | apply F_REPL4; auto ] ]
 | apply TRANS with (par s (par (frepl4 q0 x0 x x2 x3) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_TAU3; assumption ] ] ].

elim (BANG_OUT q0 q2 x y H8); intros; inversion_clear H10;
 inversion_clear H11; inversion H0; inversion H1; inversion_clear H11;
 inversion_clear H15; inversion_clear H20.
elim (H18 (Out x y)); elim (H15 x); intros.
elim (H22 q3 H7); elim (H24 x0 H12); intros; inversion_clear H25;
 inversion_clear H26.
exists (par (x3 y) (cf_f_act p0 x2 x1)); split.
apply COM1 with x; [ assumption | apply BANG_FTR_AUX; assumption ].
rewrite H10; left; exists (par (par (x3 y) (frepl1 p0 x2 x1)) (bang p0));
 exists (par (par (q3 y) (frepl1 q0 x0 x1)) (bang q0)); 
 split.
apply TRANS with (par (x3 y) (par (frepl1 p0 x2 x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_F_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ auto | apply F_REPL1; assumption ] ]
 | apply TRANS with (par (q3 y) (par (frepl1 q0 x0 x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_F_ACT; assumption ] ] ].

elim (BANG_BTR q0 q3 (In x) H8); intros; inversion_clear H10;
 inversion_clear H11; inversion H0; inversion H1; inversion_clear H11;
 inversion_clear H15; inversion_clear H19.
elim (H11 (Out x y)); elim (H15 x); intros.
elim (H22 x0 H12); elim (H24 q2 H7); intros; inversion_clear H25;
 inversion_clear H26.
exists (par x2 (cf_b_act p0 x3 x1 y)); split.
apply COM2 with x; [ assumption | apply BANG_BTR_AUX; assumption ].
rewrite H10; left; exists (par (par x2 (frepl1 p0 (x3 y) x1)) (bang p0));
 exists (par (par q2 (frepl1 q0 (x0 y) x1)) (bang q0)); 
 split.
apply TRANS with (par x2 (par (frepl1 p0 (x3 y) x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ apply bisbang_s;
    [ assumption | apply PAR_S2; [ auto | apply F_REPL1; auto ] ]
 | apply TRANS with (par q2 (par (frepl1 q0 (x0 y) x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_B_ACT; assumption ] ] ].

elim (BANG_BTR q0 q3 (bOut x) H8); intros; inversion_clear H10;
 inversion_clear H11; inversion H0; inversion H1; inversion_clear H11;
 inversion_clear H15; inversion_clear H19; inversion_clear H20.
elim (H19 x); elim (H21 x); intros.
elim (H23 x0 H12); elim (H25 q2 H7); intros; inversion_clear H26;
 inversion_clear H27.
exists (nu (fun n : name => par (x2 n) (cf_b_act p0 x3 x1 n))); split.
apply CLOSE1 with x; [ assumption | apply BANG_BTR_AUX; assumption ].
rewrite H10; right.
exists (fun n : name => par (par (x2 n) (frepl1 p0 (x3 n) x1)) (bang p0));
 exists (fun n : name => par (par (q2 n) (frepl1 q0 (x0 n) x1)) (bang q0));
 split.
apply NU_S; intros;
 apply TRANS with (par (x2 x4) (par (frepl1 p0 (x3 x4) x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ intros; apply bisbang_s;
    [ assumption
    | apply PAR_S2;
       [ auto
       | apply F_REPL1; auto; apply H30;
          [ apply notin_nu; intros; apply FREPL1_NOTIN with p0 x1;
             inversion_clear H27;
             cut
              (notin z (par (par (x2 z0) (frepl1 p0 (x3 z0) x1)) (bang p0)));
             [ intro | auto ]; inversion_clear H27; 
             inversion_clear H34; assumption
          | apply notin_nu; intros; apply FREPL1_NOTIN with q0 x1;
             inversion_clear H31;
             cut
              (notin z (par (par (q2 z0) (frepl1 q0 (x0 z0) x1)) (bang q0)));
             [ intro | auto ]; inversion_clear H31; 
             inversion_clear H34; assumption ] ] ]
 | apply NU_S; intros;
    apply TRANS with (par (q2 x4) (par (frepl1 q0 (x0 x4) x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_B_ACT; assumption ] ] ].

elim (BANG_BTR q0 q3 (In x) H8); intros; inversion_clear H10;
 inversion_clear H11; inversion H0; inversion H1; inversion_clear H11;
 inversion_clear H15; inversion_clear H19; inversion_clear H20.
elim (H15 x); elim (H22 x); intros.
elim (H23 q2 H7); elim (H25 x0 H12); intros; inversion_clear H26;
 inversion_clear H27.
exists (nu (fun n : name => par (x3 n) (cf_b_act p0 x2 x1 n))); split.
apply CLOSE2 with x; [ assumption | apply BANG_BTR_AUX; assumption ].
rewrite H10; right.
exists (fun n : name => par (par (x3 n) (frepl1 p0 (x2 n) x1)) (bang p0));
 exists (fun n : name => par (par (q2 n) (frepl1 q0 (x0 n) x1)) (bang q0));
 split.
apply NU_S; intros;
 apply TRANS with (par (x3 x4) (par (frepl1 p0 (x2 x4) x1) (bang p0)));
 [ apply PAR_S2; [ apply REF | apply SB_CF_B_ACT; assumption ]
 | apply SYM; apply ASS_PAR ].
split;
 [ intros; apply bisbang_s;
    [ assumption
    | apply PAR_S2;
       [ apply H30;
          [ apply notin_nu; intros; inversion_clear H27;
             cut
              (notin z (par (par (x3 z0) (frepl1 p0 (x2 z0) x1)) (bang p0)));
             [ intro | auto ]; inversion_clear H27; 
             inversion_clear H34; assumption
          | apply notin_nu; intros; inversion_clear H31;
             cut
              (notin z (par (par (q2 z0) (frepl1 q0 (x0 z0) x1)) (bang q0)));
             [ intro | auto ]; inversion_clear H31; 
             inversion_clear H34; assumption ]
       | apply F_REPL1; auto ] ]
 | apply NU_S; intros;
    apply TRANS with (par (q2 x4) (par (frepl1 q0 (x0 x4) x1) (bang q0)));
    [ apply ASS_PAR
    | apply PAR_S2; [ apply REF | apply SYM; apply SB_CF_B_ACT; assumption ] ] ].

Qed.

Lemma BisBANG_S_UPTO : UpTo BisBANG_S.

Proof.

unfold UpTo in |- *; intros.

split; intros.

rewrite H2 in H; rewrite H3 in H; apply BANG_S_L6 with x; auto.

split; intros.

apply BisBANG_S_FTR1; auto.

split; intros.

apply BisBANG_S_IN; assumption.

split; intros.

apply BisBANG_S_bOUT; assumption.

apply BisBANG_S_FTR2; assumption.

Qed.

Lemma BANG_S : forall p q : proc, StBisim p q -> StBisim (bang p) (bang q).

Proof.

intros; apply Completeness; apply Co_Ind with (SBUPTO BisBANG_S);
 [ apply UPTO_SB'; exact BisBANG_S_UPTO
 | apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *;
    exists (par nil (bang p)); exists (par nil (bang q)); 
    split;
    [ apply SYM; apply TRANS with (par (bang p) nil);
       [ apply COMM_PAR | apply ID_PAR ]
    | split;
       [ apply bisbang_s; [ assumption | apply REF ]
       | apply TRANS with (par (bang q) nil);
          [ apply COMM_PAR | apply ID_PAR ] ] ] ].

Qed.

End structural_congruence3.