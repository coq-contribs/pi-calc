(*******************************************************)
(*                                                     *)
(*                  Contexts Theory.                   *)
(*                                                     *)
(*******************************************************)
(*                                                     *)
(* File   : hoaspack.v                                 *)
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

Require Export picalcth.

Section monotonicity.

(*******************************************************)
(* The next axiom states that if a name does not occur *)
(* in an applied context, then it cannot occur in the  *)
(* context itself.                                     *)
(*******************************************************)

Axiom
  proc_mono :
    forall (p : name -> proc) (x y : name), notin x (p y) -> notin x (nu p).

(*********************************************)
(* Same as above, for free and bound labels. *)
(*********************************************)

Axiom
  f_act_mono :
    forall (a : name -> f_act) (x y : name),
    f_act_notin x (a y) -> f_act_notin_ho x a.

Axiom
  b_act_mono :
    forall (a : name -> b_act) (x y : name),
    b_act_notin x (a y) -> b_act_notin_ho x a.

End monotonicity.

Section expansions.

(*****************************************************)
(* Expansion of processes contexts into higher order *)
(* process contexts applied to names.                *)
(*****************************************************)

Axiom
  ho_proc_exp :
    forall (p : name -> proc) (x : name),
    exists q : name -> name -> proc,
      notin x (nu (fun y : name => nu (q y))) /\ p = q x.

Axiom
  ho2_proc_exp :
    forall (p : name -> name -> proc) (x : name),
    exists q : name -> name -> name -> proc,
      notin x (nu (fun y : name => nu (fun z : name => nu (q y z)))) /\
      p = q x.

(*******************************)
(* Same as above, for process. *)
(*******************************)

Lemma proc_exp :
 forall (p : proc) (x : name),
 exists q : name -> proc, notin x (nu q) /\ p = q x.

Proof.

simple induction p; intros.

exists (fun _ : name => nil); split;
 [ apply notin_nu; intros; apply notin_nil | try trivial ].

elim (H x); intros.
exists (fun n : name => bang (x0 n)); split.
apply notin_nu; intros.
apply notin_bang; inversion H0.
inversion H2; auto.
inversion H0.
rewrite <- H2; trivial.

elim (H x); intros.
exists (fun n : name => tau_pref (x0 n)); split.
apply notin_nu; intros.
apply notin_tau; inversion H0.
inversion H2; auto.
inversion H0.
rewrite <- H2; trivial.

elim (H x); elim (H0 x); intros.
inversion_clear H1; inversion_clear H2.
exists (fun n : name => par (x1 n) (x0 n)); split.
apply notin_nu; intros.
apply notin_par; [ inversion H1; auto | inversion H3; auto ].
rewrite <- H4; rewrite <- H5; trivial.

elim (H x); elim (H0 x); intros.
inversion_clear H1; inversion_clear H2.
exists (fun n : name => sum (x1 n) (x0 n)); split.
apply notin_nu; intros.
apply notin_sum; [ inversion H1; auto | inversion H3; auto ].
rewrite <- H4; rewrite <- H5; trivial.

elim (ho_proc_exp p0 x); intros.
inversion_clear H0; exists (fun n : name => nu (x0 n)); split;
 [ assumption | rewrite H2; trivial ].

elim (H x); intros.
inversion_clear H0.
elim (LEM_name x n); elim (LEM_name x n0); intros.
rewrite <- H0; rewrite <- H3; exists (fun n : name => match_ n n (x0 n));
 split.
apply notin_nu; intros; inversion H1; apply notin_match; auto.
rewrite H2; trivial.
rewrite <- H3; exists (fun n : name => match_ n n0 (x0 n)); split.
apply notin_nu; intros; inversion H1; apply notin_match; auto.
rewrite H2; trivial.
rewrite <- H0; exists (fun n1 : name => match_ n n1 (x0 n1)); split.
apply notin_nu; intros; inversion H1; apply notin_match; auto.
rewrite H2; trivial.
exists (fun n1 : name => match_ n n0 (x0 n1)); split.
apply notin_nu; intros; inversion H1; apply notin_match; auto.
rewrite H2; trivial.

elim (H x); intros.
inversion_clear H0.
elim (LEM_name x n); elim (LEM_name x n0); intros.
rewrite <- H0; rewrite <- H3;
 exists (fun n1 : name => mismatch n1 n1 (x0 n1)); 
 split.
apply notin_nu; intros; inversion H1; apply notin_mismatch; auto.
rewrite H2; trivial.
rewrite <- H3; exists (fun n1 : name => mismatch n1 n0 (x0 n1)); split.
apply notin_nu; intros; inversion H1; apply notin_mismatch; auto.
rewrite H2; trivial.
rewrite <- H0; exists (fun n1 : name => mismatch n n1 (x0 n1)); split.
apply notin_nu; intros; inversion H1; apply notin_mismatch; auto.
rewrite H2; trivial.
exists (fun n1 : name => mismatch n n0 (x0 n1)); split.
apply notin_nu; intros; inversion H1; apply notin_mismatch; auto.
rewrite H2; trivial.

elim (ho_proc_exp p0 x); intros.
inversion_clear H0; elim (LEM_name x n); intros.
rewrite <- H0; exists (fun n0 : name => in_pref n0 (x0 n0)); split;
 [ apply notin_nu; intros; apply notin_in; intros;
    [ assumption
    | inversion H1; cut (notin x (nu (x0 z))); [ intro | auto ];
       inversion_clear H7; auto ]
 | rewrite H2; trivial ].
exists (fun n0 : name => in_pref n (x0 n0)); split;
 [ apply notin_nu; intros; apply notin_in; intros;
    [ auto
    | inversion H1; cut (notin x (nu (x0 z))); [ intro | auto ];
       inversion_clear H7; auto ]
 | rewrite H2; trivial ].

elim (H x); intros.
inversion_clear H0.
elim (LEM_name x n); elim (LEM_name x n0); intros.
rewrite <- H0; rewrite <- H3;
 exists (fun n1 : name => out_pref n1 n1 (x0 n1)); 
 split.
apply notin_nu; intros; inversion H1; apply notin_out; auto.
rewrite H2; trivial.
rewrite <- H3; exists (fun n1 : name => out_pref n1 n0 (x0 n1)); split.
apply notin_nu; intros; inversion H1; apply notin_out; auto.
rewrite H2; trivial.
rewrite <- H0; exists (fun n1 : name => out_pref n n1 (x0 n1)); split.
apply notin_nu; intros; inversion H1; apply notin_out; auto.
rewrite H2; trivial.
exists (fun n1 : name => out_pref n n0 (x0 n1)); split.
apply notin_nu; intros; inversion H1; apply notin_out; auto.
rewrite H2; trivial.

Qed.

(*************************************************)
(* Expansion of free labels into label contexts. *)
(*************************************************)

Lemma f_act_exp :
 forall (a : f_act) (x : name),
 exists b : name -> f_act, f_act_notin_ho x b /\ a = b x.

Proof.

unfold f_act_notin_ho in |- *; simple induction a; intros.

exists (fun x : name => tau); split; [ intros | trivial ].
apply f_act_notin_tau.

elim (LEM_name n x); elim (LEM_name n0 x); intros.
exists (fun x : name => Out x x); split.
intros; apply f_act_notin_Out; auto.
rewrite H; rewrite H0; try trivial.

exists (fun x : name => Out x n0); split.
intros; apply f_act_notin_Out; auto.
rewrite H0; try trivial.

exists (fun x : name => Out n x); split.
intros; apply f_act_notin_Out; auto.
rewrite H; try trivial.

exists (fun x : name => Out n n0); split;
 [ intros; apply f_act_notin_Out; auto | trivial ].

Qed.

(**************************************************)
(* Expansion of bound labels into label contexts. *)
(**************************************************)

Lemma b_act_exp :
 forall (a : b_act) (x : name),
 exists b : name -> b_act, b_act_notin_ho x b /\ a = b x.

Proof.

unfold b_act_notin_ho in |- *; simple induction a; intros.

elim (LEM_name n x); intros.
exists (fun x : name => In x); split.
intros; apply b_act_notin_In; auto.
rewrite H; try trivial.

exists (fun x : name => In n); split.
intros; apply b_act_notin_In; auto.
trivial.

elim (LEM_name n x); intros.
exists (fun x : name => bOut x); split.
intros; apply b_act_notin_bOut; auto.
rewrite H; try trivial.

exists (fun x : name => bOut n); split.
intros; apply b_act_notin_bOut; auto.
trivial.

Qed.

End expansions.

(**********************************************************************)
(* Leibniz equality is a congruence w.r.t. replacement of free names. *)
(**********************************************************************)

Section eq_congr.

Variable x y : name.

Axiom
  ho_proc_ext :
    forall (p q : name -> name -> proc) (x : name),
    notin x (nu (fun y : name => nu (p y))) ->
    notin x (nu (fun y : name => nu (q y))) -> p x = q x -> p = q.

Axiom
  proc_ext :
    forall (p q : name -> proc) (x : name),
    notin x (nu p) -> notin x (nu q) -> p x = q x -> p = q.

Lemma proc_spec :
 forall p q : name -> proc, p = q -> forall x : name, p x = q x.

Proof.

intros; rewrite H; trivial.

Qed.

Lemma proc_sub_congr :
 forall p q : name -> proc,
 notin x (nu p) -> notin x (nu q) -> p x = q x -> p y = q y.

Proof.

intros; apply proc_spec; apply proc_ext with x; auto.

Qed.

Lemma ho_proc_sub_congr :
 forall p q : name -> name -> proc,
 notin x (nu (fun z : name => nu (p z))) ->
 notin x (nu (fun z : name => nu (q z))) -> p x = q x -> p y = q y.

Proof.

intros;
 elim
  (unsat
     (par (nu (fun z : name => nu (p z))) (nu (fun z : name => nu (q z))))
     (cons x (cons y empty))); intros.
inversion_clear H; inversion_clear H0; inversion_clear H2; inversion_clear H0;
 inversion_clear H4; inversion_clear H2; inversion_clear H5;
 inversion_clear H6; clear H7.

apply proc_ext with x0; auto.

change ((fun n : name => p n x0) y = (fun n : name => q n x0) y) in |- *;
 apply proc_sub_congr; try apply notin_nu; intros;
 [ cut (notin x (nu (p z))) | cut (notin x (nu (q z))) | apply proc_spec ];
 auto; intro; inversion_clear H7; auto.

Qed.

Axiom
  f_act_ext :
    forall (a b : name -> f_act) (x : name),
    f_act_notin_ho x a -> f_act_notin_ho x b -> a x = b x -> a = b.

Lemma f_act_spec :
 forall a b : name -> f_act, a = b -> forall x : name, a x = b x.

Proof.

intros; rewrite H; trivial.

Qed.

Lemma f_act_sub_congr :
 forall a b : name -> f_act,
 f_act_notin_ho x a -> f_act_notin_ho x b -> a x = b x -> a y = b y.

Proof.

intros; apply f_act_spec; apply f_act_ext with x; auto.

Qed.

Axiom
  b_act_ext :
    forall (a b : name -> b_act) (x : name),
    b_act_notin_ho x a -> b_act_notin_ho x b -> a x = b x -> a = b.

Lemma b_act_spec :
 forall a b : name -> b_act, a = b -> forall x : name, a x = b x.

Proof.

intros; rewrite H; trivial.

Qed.

Lemma b_act_sub_congr :
 forall a b : name -> b_act,
 b_act_notin_ho x a -> b_act_notin_ho x b -> a x = b x -> a y = b y.

Proof.

intros; apply b_act_spec; apply b_act_ext with x; auto.

Qed.

End eq_congr.

Section eta.

(*******************************)
(* Eta-equivalence of contexts *)
(*******************************)

Lemma PRE_ETA_EQ :
 forall (q : proc) (x : name) (p : name -> proc),
 notin x (nu p) -> q = p x -> nu p = nu (fun x : name => p x).

Proof.

intro; case q; intros.

cut (p = (fun _ : name => nil)); [ intro | apply proc_ext with x; auto ].
rewrite H1; trivial.
apply notin_nu; intros; apply notin_nil.

elim (proc_exp p x); intros.
inversion_clear H1.
rewrite H3 in H0; cut (p0 = (fun n : name => bang (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H1; trivial.
apply notin_nu; intros; apply notin_bang; inversion_clear H2; auto.

elim (proc_exp p x); intros.
inversion_clear H1.
rewrite H3 in H0; cut (p0 = (fun n : name => tau_pref (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H1; trivial.
apply notin_nu; intros; apply notin_tau; inversion_clear H2; auto.

elim (proc_exp p x); elim (proc_exp p0 x); intros.
inversion_clear H1; inversion_clear H2.
rewrite H4 in H0; rewrite H5 in H0;
 cut (p1 = (fun n : name => par (x1 n) (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H2; trivial.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H1 | inversion_clear H3 ]; auto.

elim (proc_exp p x); elim (proc_exp p0 x); intros.
inversion_clear H1; inversion_clear H2.
rewrite H4 in H0; rewrite H5 in H0;
 cut (p1 = (fun n : name => sum (x1 n) (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H2; trivial.
apply notin_nu; intros; apply notin_sum;
 [ inversion_clear H1 | inversion_clear H3 ]; auto.

elim (ho_proc_exp p x); intros.
inversion_clear H1.
rewrite H3 in H0; cut (p0 = (fun n : name => nu (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H1; trivial.

elim (LEM_name x n); elim (LEM_name x n0); intros.

rewrite <- H1 in H0; rewrite <- H2 in H0; elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => match_ n1 n1 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_match; auto.

rewrite <- H2 in H0; elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => match_ n1 n0 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_match; auto.

rewrite <- H1 in H0; elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => match_ n n1 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_match; auto.

elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => match_ n n0 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_match; auto.

elim (LEM_name x n); elim (LEM_name x n0); intros.

rewrite <- H1 in H0; rewrite <- H2 in H0; elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => mismatch n1 n1 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_mismatch; auto.

rewrite <- H2 in H0; elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => mismatch n1 n0 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_mismatch; auto.

rewrite <- H1 in H0; elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => mismatch n n1 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_mismatch; auto.

elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => mismatch n n0 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_mismatch; auto.

elim (LEM_name x n); intro.

rewrite <- H1 in H0; elim (ho_proc_exp p x); intros.
inversion_clear H2.
rewrite H4 in H0; cut (p0 = (fun n1 : name => in_pref n1 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H2; trivial.
apply notin_nu; intros; apply notin_in; intros; inversion_clear H3; auto.
cut (notin x (nu (x0 z))); [ intro | auto ].
inversion_clear H3; auto.

elim (ho_proc_exp p x); intros.
inversion_clear H2.
rewrite H4 in H0; cut (p0 = (fun n1 : name => in_pref n (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H2; trivial.
apply notin_nu; intros; apply notin_in; intros; inversion_clear H3; auto.
cut (notin x (nu (x0 z))); [ intro | auto ].
inversion_clear H3; auto.

elim (LEM_name x n); elim (LEM_name x n0); intros.

rewrite <- H1 in H0; rewrite <- H2 in H0; elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => out_pref n1 n1 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_out; auto.

rewrite <- H2 in H0; elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => out_pref n1 n0 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_out; auto.

rewrite <- H1 in H0; elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => out_pref n n1 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_out; auto.

elim (proc_exp p x); intros.
inversion_clear H3.
rewrite H5 in H0; cut (p0 = (fun n1 : name => out_pref n n0 (x0 n1)));
 [ intro | apply proc_ext with x; auto ].
rewrite H3; trivial.
apply notin_nu; intros; inversion_clear H4; apply notin_out; auto.

Qed.

Lemma ETA_EQ : forall p : name -> proc, nu p = nu (fun x : name => p x).

Proof.

intro; elim (unsat (nu p) empty); intros.
inversion_clear H; clear H1.
apply PRE_ETA_EQ with (p x) x; auto.

Qed.

(********************************************)
(* Same as above, for higher-order contexts *)
(********************************************)

Lemma ETA_EQ2 :
 forall p : name -> name -> proc,
 nu (fun x : name => nu (p x)) =
 nu (fun x : name => nu (fun y : name => p x y)).

Proof.

intro;
 cut
  ((fun x : name => nu (p x)) = (fun x : name => nu (fun y : name => p x y)));
 [ intro; rewrite H; trivial | idtac ].
elim (unsat (nu (fun x : name => nu (p x))) empty); intros; inversion_clear H;
 clear H1.
apply proc_ext with x; auto.

Qed.

End eta.