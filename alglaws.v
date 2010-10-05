(*******************************************************)
(*                                                     *)
(*         Formalization of the Algebraic Laws         *)
(*            of Strong Late Bisimilarity.             *)
(*                                                     *)
(*******************************************************)
(*                                                     *)
(* File   : alglaws.v                                  *)
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

Require Export basiclemmata.

(* Section equivalence. *)

Lemma REF : forall p : proc, StBisim p p.

Proof. (* This lemma is proved from scratch: it is a coinductive proof. *)

cofix; intro; apply sb; do 3 try (split; intros).
exists p1; split; auto.
exists q1; split; auto.
exists p1; split; [ assumption | intro; auto ].
exists q1; split; [ assumption | intro; auto ].
exists p1; split; [ assumption | intros; auto ].
exists q1; split; [ assumption | intros; auto ].

Qed.

Lemma SYM : forall p q : proc, StBisim p q -> StBisim q p.

Proof. (* This lemma is proved from scratch: it is a coinductive proof. *)

cofix; intros; apply sb; do 3 try (split; intros).

inversion H.
elim H1; intros.
elim (H4 a); intros.
elim (H7 p1 H0); intros.
elim H8; intros; exists x; split; [ assumption | apply SYM; assumption ].

inversion H.
elim H1; intros.
elim (H4 a); intros.
elim (H6 q1 H0); intros.
elim H8; intros; exists x; split; [ assumption | apply SYM; assumption ].

inversion H.
elim H1; intros.
elim H5; intros.
elim (H6 x); intros.
elim (H9 p1 H0); intros.
elim H10; intros; exists x0; split; [ assumption | intro; apply SYM; auto ].

inversion H.
elim H1; intros.
elim H5; intros.
elim (H6 x); intros.
elim (H8 q1 H0); intros.
elim H10; intros; exists x0; split; [ assumption | intro; apply SYM; auto ].

inversion H.
elim H1; intros.
elim H5; intros.
elim (H7 x); intros.
elim (H9 p1 H0); intros.
elim H10; intros; exists x0; split;
 [ assumption | intros; apply SYM; apply H12; auto ].

inversion H.
elim H1; intros.
elim H5; intros.
elim (H7 x); intros.
elim (H8 q1 H0); intros.
elim H10; intros; exists x0; split;
 [ assumption | intros; apply SYM; apply H12; auto ].

Qed.

Lemma TRANS : forall p q r : proc, StBisim p q -> StBisim q r -> StBisim p r.

Proof. (* This lemma depends on Lemma L6_Light: it is a coinductive proof. *)

cofix.
do 4 intro.
inversion_clear H.
intro.
inversion_clear H.
apply sb.
split.
intro.
cut
 ((forall p1 : proc,
   ftrans p a p1 -> exists q1 : proc, ftrans q a q1 /\ StBisim p1 q1) /\
  (forall q1 : proc,
   ftrans q a q1 -> exists p1 : proc, ftrans p a p1 /\ StBisim p1 q1)).
intro.
cut
 ((forall p1 : proc,
   ftrans q a p1 -> exists q1 : proc, ftrans r a q1 /\ StBisim p1 q1) /\
  (forall q1 : proc,
   ftrans r a q1 -> exists p1 : proc, ftrans q a p1 /\ StBisim p1 q1)).
intro.
inversion_clear H.
inversion_clear H2.
split.
intros.
cut (exists q1 : proc, ftrans q a q1 /\ StBisim p1 q1).
intro.
inversion_clear H6.
cut (exists q1 : proc, ftrans r a q1 /\ StBisim x q1).
intro.
inversion_clear H6.
exists x0.
split.
tauto.

apply TRANS with x.
tauto.

tauto.

apply H.
tauto.

apply H3.
assumption.

intros.
cut (exists p1 : proc, ftrans q a p1 /\ StBisim p1 q1).
intro.
inversion_clear H6.
cut (exists p1 : proc, ftrans p a p1 /\ StBisim p1 x).
intro.
inversion_clear H6.
exists x0.
split.
tauto.

apply TRANS with x.
tauto.

tauto.

apply H4.
tauto.

apply H5.
assumption.

elim H1.
intros.
apply H2.

elim H0.
intros.
apply H.

split.
intro.
cut
 ((forall p1 : name -> proc,
   btrans p (In x) p1 ->
   exists q1 : name -> proc,
     btrans q (In x) q1 /\ (forall y : name, StBisim (p1 y) (q1 y))) /\
  (forall q1 : name -> proc,
   btrans q (In x) q1 ->
   exists p1 : name -> proc,
     btrans p (In x) p1 /\ (forall y : name, StBisim (p1 y) (q1 y)))).
intro.
cut
 ((forall p1 : name -> proc,
   btrans q (In x) p1 ->
   exists q1 : name -> proc,
     btrans r (In x) q1 /\ (forall y : name, StBisim (p1 y) (q1 y))) /\
  (forall q1 : name -> proc,
   btrans r (In x) q1 ->
   exists p1 : name -> proc,
     btrans q (In x) p1 /\ (forall y : name, StBisim (p1 y) (q1 y)))).
intro.
inversion_clear H.
inversion_clear H2.
split.
intros.

cut
 (exists q1 : name -> proc,
    btrans q (In x) q1 /\ (forall y : name, StBisim (p1 y) (q1 y))).
intro.
inversion_clear H6.
cut
 (exists q1 : name -> proc,
    btrans r (In x) q1 /\ (forall y : name, StBisim (x0 y) (q1 y))).
intro.
inversion_clear H6.
exists x1.
split.
tauto.

intro.
apply TRANS with (x0 y).
generalize y.
case H7; trivial.

generalize y.
case H8; trivial.

apply H.
tauto.

apply H3.
assumption.

intros.
cut
 (exists p1 : name -> proc,
    btrans q (In x) p1 /\ (forall y : name, StBisim (p1 y) (q1 y))).
intro.
inversion_clear H6.
cut
 (exists p1 : name -> proc,
    btrans p (In x) p1 /\ (forall y : name, StBisim (p1 y) (x0 y))).
intro.
inversion_clear H6.
exists x1.
split.
tauto.

intro.
apply TRANS with (x0 y).
generalize y.
case H8; trivial.

generalize y.
case H7; trivial.

apply H4.
tauto.

apply H5.
assumption.

elim H1.
intros.
elim H3.
intros.
apply H4.

elim H0.
intros.
elim H2.
intros.
apply H3.

intro.
cut
 ((forall p1 : name -> proc,
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
      notin y (nu p1) -> notin y (nu q1) -> StBisim (p1 y) (q1 y)))).
intro.
cut
 ((forall p1 : name -> proc,
   btrans q (bOut x) p1 ->
   exists q1 : name -> proc,
     btrans r (bOut x) q1 /\
     (forall y : name,
      notin y (nu p1) -> notin y (nu q1) -> StBisim (p1 y) (q1 y))) /\
  (forall q1 : name -> proc,
   btrans r (bOut x) q1 ->
   exists p1 : name -> proc,
     btrans q (bOut x) p1 /\
     (forall y : name,
      notin y (nu p1) -> notin y (nu q1) -> StBisim (p1 y) (q1 y)))).
intro.
inversion_clear H.
inversion_clear H2.
split.
intros.
cut
 (exists q1 : name -> proc,
    btrans q (bOut x) q1 /\
    (forall y : name,
     notin y (nu p1) -> notin y (nu q1) -> StBisim (p1 y) (q1 y))).
intro.
inversion_clear H6.
cut
 (exists q1 : name -> proc,
    btrans r (bOut x) q1 /\
    (forall y : name,
     notin y (nu x0) -> notin y (nu q1) -> StBisim (x0 y) (q1 y))).
intro.
inversion_clear H6.
exists x1.
split.
tauto.

intros.
elim (ho_proc_exp x0 y); intros.
inversion_clear H10.
elim
 (unsat
    (par (nu p1) (par (nu x0) (par (nu x1) (nu (fun w : name => nu (x2 w))))))
    (cons y empty)); intros.
inversion_clear H10.
inversion_clear H13.
inversion_clear H15.
inversion_clear H16.
inversion_clear H14.
clear H18.

apply TRANS with (x2 x3 y).
elim
 (unsat (par (nu p1) (par (nu (x2 x3)) (nu x0))) (cons x3 (cons y empty)));
 intros.
inversion_clear H14.
inversion_clear H18.
inversion_clear H20.
inversion_clear H19.
inversion_clear H22.
clear H23.
apply L6_Light with x4.

assumption. assumption.

change (StBisim ((fun z : name => p1 x4) x3) ((fun z : name => x2 z x4) x3))
 in |- *.
apply L6_Light with y.

apply notin_nu.
intros.
inversion H6.
apply H24.
auto.

apply notin_nu.
intros.
inversion H11.
cut (notin y (nu (x2 z))); [ intro | auto ].
inversion H25.
cut (notin y (x2 z x4)); [ intro | auto ].
assumption.

inversion_clear H7.
rewrite <- H12; apply H23.
assumption.
assumption.

apply notin_nu.
intros.
inversion H10.
apply H24; auto.

apply notin_nu.
intros.
inversion H17.
cut (notin x3 (nu (x2 z))); [ intro | auto ].
inversion H25.
cut (notin x3 (x2 z x4)); [ intro | auto ].
assumption.

assumption.

apply notin_nu. intros.
inversion H11.
cut (notin y (nu (x2 x3))); [ intro | auto ].
inversion H25.
cut (notin y (x2 x3 z)); [ intro | auto ].
assumption.

elim
 (unsat (par (nu x1) (par (nu (x2 x3)) (nu x0))) (cons x3 (cons y empty)));
 intros.
inversion_clear H14.
inversion_clear H18.
inversion_clear H20.
inversion_clear H19.
inversion_clear H22.
clear H23.
apply L6_Light with x4.

assumption. assumption.

change (StBisim ((fun z : name => x2 z x4) x3) ((fun z : name => x1 x4) x3))
 in |- *.
apply L6_Light with y.

apply notin_nu.
intros.
inversion H11.
cut (notin y (nu (x2 z))); [ intro | auto ].
inversion H25.
cut (notin y (x2 z x4)); [ intro | auto ].
assumption.

apply notin_nu.
intros.
inversion H9.
apply H24.
auto.

inversion_clear H8.
rewrite <- H12; apply H23.
assumption.
assumption.

apply notin_nu.
intros.
inversion H17.
cut (notin x3 (nu (x2 z))); [ intro | auto ].
inversion H25.
cut (notin x3 (x2 z x4)); [ intro | auto ].
assumption.

apply notin_nu.
intros.
inversion H15.
apply H24; auto.

apply notin_nu. intros.
inversion H11.
cut (notin y (nu (x2 x3))); [ intro | auto ].
inversion H25.
cut (notin y (x2 x3 z)); [ intro | auto ].
assumption.

assumption.

apply H. tauto.
apply H3. tauto.

intros.
cut
 (exists p1 : name -> proc,
    btrans q (bOut x) p1 /\
    (forall y : name,
     notin y (nu p1) -> notin y (nu q1) -> StBisim (p1 y) (q1 y))).
intro.
inversion_clear H6.
cut
 (exists p1 : name -> proc,
    btrans p (bOut x) p1 /\
    (forall y : name,
     notin y (nu p1) -> notin y (nu x0) -> StBisim (p1 y) (x0 y))).
intro.
inversion_clear H6.
exists x1.
split.
tauto.

intros.
elim (ho_proc_exp x0 y); intros.
inversion_clear H10.
elim
 (unsat
    (par (nu x1) (par (nu x0) (par (nu q1) (nu (fun w : name => nu (x2 w))))))
    (cons y empty)); intros.
inversion_clear H10.
inversion_clear H13.
inversion_clear H15.
inversion_clear H16.
inversion_clear H14.
clear H18.
apply TRANS with (x2 x3 y).
elim
 (unsat (par (nu x1) (par (nu (x2 x3)) (nu x0))) (cons x3 (cons y empty)));
 intros.
inversion_clear H14.
inversion_clear H18.
inversion_clear H20.
inversion_clear H19.
inversion_clear H22.
clear H23.
apply L6_Light with x4.

assumption. assumption.

change (StBisim ((fun z : name => x1 x4) x3) ((fun z : name => x2 z x4) x3))
 in |- *.
apply L6_Light with y.

apply notin_nu.
intros.
inversion H6.
apply H24.
auto.

apply notin_nu.
intros.
inversion H11.
cut (notin y (nu (x2 z))); [ intro | auto ].
inversion H25.
cut (notin y (x2 z x4)); [ intro | auto ].
assumption.

inversion_clear H8.
rewrite <- H12; apply H23.
assumption.

assumption.

apply notin_nu.
intros.
inversion H10.
apply H24; auto.

apply notin_nu.
intros.
inversion H17.
cut (notin x3 (nu (x2 z))); [ intro | auto ].
inversion H25.
cut (notin x3 (x2 z x4)); [ intro | auto ].
assumption.

assumption.

apply notin_nu. intros.
inversion H11.
cut (notin y (nu (x2 x3))); [ intro | auto ].
inversion H25.
cut (notin y (x2 x3 z)); [ intro | auto ].
assumption.

elim
 (unsat (par (nu q1) (par (nu (x2 x3)) (nu x0))) (cons x3 (cons y empty)));
 intros.
inversion_clear H14.
inversion_clear H18.
inversion_clear H20.
inversion_clear H19.
inversion_clear H22.
clear H23.
apply L6_Light with x4.

assumption. assumption.

change (StBisim ((fun z : name => x2 z x4) x3) ((fun z : name => q1 x4) x3))
 in |- *.
apply L6_Light with y.

apply notin_nu.
intros.
inversion H11.
cut (notin y (nu (x2 z))); [ intro | auto ].
inversion H25.
cut (notin y (x2 z x4)); [ intro | auto ].
assumption.

apply notin_nu.
intros.
inversion H9.
apply H24.
auto.

inversion_clear H7.
rewrite <- H12; apply H23.
assumption.

assumption.

apply notin_nu.
intros.
inversion H17.
cut (notin x3 (nu (x2 z))); [ intro | auto ].
inversion H25.
cut (notin x3 (x2 z x4)); [ intro | auto ].
assumption.

apply notin_nu.
intros.
inversion H15.
apply H24; auto.

apply notin_nu. intros.
inversion H11.
cut (notin y (nu (x2 x3))); [ intro | auto ].
inversion H25.
cut (notin y (x2 x3 z)); [ intro | auto ].
assumption.

assumption.

apply H4. tauto.
apply H5. tauto.

elim H1.
intros.
elim H3.
intros.
apply H5.

elim H0.
intros.
elim H2.
intros.
apply H4.

Qed.

(* End equivalence. *)

(* Section structural_congruence1. *)

Lemma TAU_S :
 forall p q : proc, StBisim p q -> StBisim (tau_pref p) (tau_pref q).

Proof. (* This lemma is proved from scratch. *)

intros; apply sb; do 3 try (split; intros).
inversion H0; exists q; split; [ apply TAU | rewrite <- H3 ]; assumption.
inversion H0; exists p; split; [ apply TAU | rewrite <- H3 ]; assumption.
inversion_clear H0.
inversion_clear H0.
inversion_clear H0.
inversion_clear H0.

Qed.

Lemma SUM_S : forall p q r : proc, StBisim p q -> StBisim (sum p r) (sum q r).

Proof. (* This lemma depends on Lemma REF. *)

intros; apply sb; do 3 try (split; intros).

inversion H0.
inversion H.
inversion_clear H6.
elim (H9 a); intros.
elim (H6 p1 H5); intros.
exists x; split; [ apply fSUM1; tauto | tauto ].
exists p1; split; [ apply fSUM2; tauto | apply REF ].

inversion H0.
inversion H.
inversion_clear H6.
elim (H9 a); intros.
elim (H11 q1 H5); intros.
exists x; split; [ apply fSUM1; tauto | tauto ].
exists q1; split; [ apply fSUM2; tauto | apply REF ].

inversion H0.
inversion H.
inversion_clear H6.
inversion_clear H10.
elim (H6 x); intros.
elim (H10 p1 H5); intros.
exists x0; split; [ apply bSUM1; tauto | intuition ].
exists p1; split; [ apply bSUM2; tauto | intro; apply REF ].

inversion H0.
inversion H.
inversion_clear H6.
inversion_clear H10.
elim (H6 x); intros.
elim (H12 q1 H5); intros.
exists x0; split; [ apply bSUM1; tauto | intuition ].
exists q1; split; [ apply bSUM2; tauto | intro; apply REF ].

inversion H0.
inversion H.
inversion_clear H6.
inversion_clear H10.
elim (H11 x); intros.
elim (H10 p1 H5); intros.
exists x0; split; [ apply bSUM1; tauto | intuition ].
exists p1; split; [ apply bSUM2; tauto | intros; apply REF ].

inversion H0.
inversion H.
inversion_clear H6.
inversion_clear H10.
elim (H11 x); intros.
elim (H12 q1 H5); intros.
exists x0; split; [ apply bSUM1; tauto | intuition ].
exists q1; split; [ apply bSUM2; tauto | intros; apply REF ].

Qed.

Lemma NU_S :
 forall p q : name -> proc,
 (forall x : name, notin x (nu p) -> notin x (nu q) -> StBisim (p x) (q x)) ->
 StBisim (nu p) (nu q).

Proof. (* This lemma depends on Lemmata FTR_L3, BTR_L3 and L6_Light:
        * it is a coinductive proof.
        *)

cofix; intros; apply sb; do 3 try (split; intros).
inversion H0.
generalize H2.
generalize H0.
elim a.
intros.
elim (unsat (par (nu p) (par (nu q) (nu p2))) l); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H10.
cut (StBisim (p x) (q x)); [ intro | auto ].
inversion_clear H10.
inversion_clear H12.
elim (H10 tau); intros.
cut (ftrans (p x) tau (p2 x)); [ intro | apply H6; auto ].
elim (H12 (p2 x) H15); intros.
inversion_clear H16.
elim (proc_exp x0 x); intros.
inversion_clear H16.
rewrite H20 in H17.
rewrite H20 in H18.
exists (nu x1); split.

apply fRES with empty; intros; auto.
clear H22 H23.
change (ftrans (q y) ((fun _ : name => tau) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply NU_S; intros.
apply L6_Light with x; auto.
apply f_act_notin_tau.

intros.
elim (unsat (par (nu p) (par (nu q) (nu p2))) (cons n (cons n0 l))); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H10.
inversion_clear H9.
inversion_clear H12.
cut (StBisim (p x) (q x)); [ intro | auto ].
inversion_clear H12.
inversion_clear H14.
elim (H12 (Out n n0)); intros.
cut (ftrans (p x) (Out n n0) (p2 x)); [ intro | apply H6; auto ].
elim (H14 (p2 x) H17); intros.
inversion_clear H18.
elim (proc_exp x0 x); intros.
inversion_clear H18.
rewrite H22 in H19.
rewrite H22 in H20.
exists (nu x1); split.
apply fRES with empty; intros; auto.
change (ftrans (q y) ((fun _ : name => Out n n0) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
clear H24.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
inversion_clear H25.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply NU_S; intros.
apply L6_Light with x; auto.

apply f_act_notin_Out; auto.

inversion H0.
generalize H2.
generalize H0.
elim a.
intros.
elim (unsat (par (nu p) (par (nu q) (nu p2))) l); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H10.
cut (StBisim (p x) (q x)); [ intro | auto ].
inversion_clear H10.
inversion_clear H12.
elim (H10 tau); intros.
cut (ftrans (q x) tau (p2 x)); [ intro | apply H6; auto ].
elim (H14 (p2 x) H15); intros.
inversion_clear H16.
elim (proc_exp x0 x); intros.
inversion_clear H16.
rewrite H20 in H17.
rewrite H20 in H18.
exists (nu x1); split.
apply fRES with empty; intros; auto.
change (ftrans (p y) ((fun _ : name => tau) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply NU_S; intros.
apply L6_Light with x; auto.
apply f_act_notin_tau.

intros.
elim (unsat (par (nu p) (par (nu q) (nu p2))) (cons n (cons n0 l))); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H10.
inversion_clear H9.
inversion_clear H12.
cut (StBisim (p x) (q x)); [ intro | auto ].
inversion_clear H12.
inversion_clear H14.
elim (H12 (Out n n0)); intros.
cut (ftrans (q x) (Out n n0) (p2 x)); [ intro | apply H6; auto ].
elim (H16 (p2 x) H17); intros.
inversion_clear H18.
elim (proc_exp x0 x); intros.
inversion_clear H18.
rewrite H22 in H19.
rewrite H22 in H20.
exists (nu x1); split.
apply fRES with empty; intros; auto.
clear H24.
change (ftrans (p y) ((fun _ : name => Out n n0) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
inversion_clear H25.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply NU_S; intros.
apply L6_Light with x; auto.
apply f_act_notin_Out; auto.

inversion H0.
elim
 (unsat (par (nu p) (par (nu q) (nu (fun z : name => nu (p2 z))))) (cons x l));
 intros.
inversion_clear H5.
inversion_clear H6.
inversion_clear H8.
inversion_clear H7.
cut (StBisim (p x0) (q x0)); [ intro | auto ].
inversion_clear H7.
inversion_clear H11.
inversion_clear H12.
elim (H11 x); intros.
cut (btrans (p x0) (In x) (p2 x0)); [ intro | apply H2; auto ].
elim (H12 (p2 x0) H15); intros.
inversion_clear H16.
elim (ho_proc_exp x1 x0); intros.
inversion_clear H16.
rewrite H20 in H17.
rewrite H20 in H18.
exists (fun n : name => nu (fun z : name => x2 z n)); split.
apply bRES with empty; intros; auto.
clear H23.
inversion_clear H22.
change (btrans (q y) ((fun _ : name => In x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In.
assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In.
assumption.
intro.
apply NU_S; intros.
elim (LEM_name x0 x3); intros.
rewrite <- H22; auto.
elim (LEM_name x0 y); intros.
rewrite <- H23; auto.
rewrite <- H23 in H16.
rewrite <- H23 in H21.
elim
 (unsat
    (par (nu (fun z : name => nu (p2 z))) (nu (fun z : name => nu (x2 z))))
    (cons x0 (cons x3 empty))); intros.
inversion_clear H24.
inversion_clear H25.
inversion_clear H26.
inversion_clear H28.
clear H29.
change
  (StBisim ((fun n : name => p2 n x0) x3) ((fun n : name => x2 n x0) x3))
 in |- *.
apply L6_Light with x4; auto.
apply notin_nu; intros.
inversion_clear H24.
cut (notin x4 (nu (p2 z))); [ intro | auto ].
inversion_clear H24.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x4 (nu (x2 z))); [ intro | auto ].
inversion_clear H27.
auto.
elim
 (unsat
    (par (nu (fun z : name => nu (p2 z))) (nu (fun z : name => nu (x2 z))))
    (cons x0 (cons x4 empty))); intros.
inversion_clear H28.
inversion_clear H29.
inversion_clear H30.
inversion_clear H32.
clear H33.
apply L6_Light with x5; auto.
apply notin_nu; intros.
inversion_clear H28.
cut (notin x5 (nu (p2 x4))); [ intro | auto ].
inversion_clear H28.
auto.
apply notin_nu; intros.
inversion_clear H31.
cut (notin x5 (nu (x2 x4))); [ intro | auto ].
inversion_clear H31.
auto.
change
  (StBisim ((fun n : name => p2 n x5) x4) ((fun n : name => x2 n x5) x4))
 in |- *.
apply L6_Light with x0; auto.
apply notin_nu; intros.
inversion_clear H9.
cut (notin x0 (nu (p2 z))); [ intro | auto ].
inversion_clear H9.
auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H19.
auto.
apply notin_nu; intros.
inversion_clear H24.
cut (notin x4 (nu (p2 z))); [ intro | auto ].
inversion_clear H24.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x4 (nu (x2 z))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H9.
cut (notin x0 (nu (p2 x4))); [ intro | auto ].
inversion_clear H9.
auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 x4))); [ intro | auto ].
inversion_clear H19.
auto.
change (StBisim ((fun n : name => p2 n y) x3) ((fun n : name => x2 n y) x3))
 in |- *.
apply L6_Light with x0; auto.
apply notin_nu; intros.
inversion_clear H9.
cut (notin x0 (nu (p2 z))); [ intro | auto ].
inversion_clear H9.
auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H19.
auto.
apply b_act_notin_In; auto.

inversion H0.
elim
 (unsat (par (nu p) (par (nu q) (nu (fun z : name => nu (p2 z))))) (cons x l));
 intros.
inversion_clear H5.
inversion_clear H6.
inversion_clear H8.
inversion_clear H7.
cut (StBisim (p x0) (q x0)); [ intro | auto ].
inversion_clear H7.
inversion_clear H11.
inversion_clear H12.
elim (H11 x); intros.
cut (btrans (q x0) (In x) (p2 x0)); [ intro | apply H2; auto ].
elim (H14 (p2 x0) H15); intros.
inversion_clear H16.
elim (ho_proc_exp x1 x0); intros.
inversion_clear H16.
rewrite H20 in H17.
rewrite H20 in H18.
exists (fun n : name => nu (fun z : name => x2 z n)); split.
apply bRES with empty; intros; auto.
clear H23.
inversion_clear H22.
change (btrans (p y) ((fun _ : name => In x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In.
assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In.
assumption.
intro.
apply NU_S; intros.
elim (LEM_name x0 x3); intros.
rewrite <- H22; auto.
elim (LEM_name x0 y); intros.
rewrite <- H23; auto.
rewrite <- H23 in H16.
rewrite <- H23 in H21.

elim
 (unsat
    (par (nu (fun z : name => nu (x2 z))) (nu (fun z : name => nu (p2 z))))
    (cons x0 (cons x3 l))); intros.
inversion_clear H24.
inversion_clear H25.
inversion_clear H26.
inversion_clear H28.
change
  (StBisim ((fun n : name => x2 n x0) x3) ((fun n : name => p2 n x0) x3))
 in |- *.
apply L6_Light with x4; auto.
apply notin_nu; intros.
inversion_clear H24.
cut (notin x4 (nu (x2 z))); [ intro | auto ].
inversion_clear H24.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x4 (nu (p2 z))); [ intro | auto ].
inversion_clear H27.
auto.
elim
 (unsat
    (par (nu (fun z : name => nu (x2 z))) (nu (fun z : name => nu (p2 z))))
    (cons x0 (cons x4 l))); intros.
inversion_clear H28.
inversion_clear H30.
inversion_clear H31.
inversion_clear H33.
apply L6_Light with x5; auto.
apply notin_nu; intros.
inversion_clear H28.
cut (notin x5 (nu (x2 x4))); [ intro | auto ].
inversion_clear H28.
auto.
apply notin_nu; intros.
inversion_clear H32.
cut (notin x5 (nu (p2 x4))); [ intro | auto ].
inversion_clear H32.
auto.
change
  (StBisim ((fun n : name => x2 n x5) x4) ((fun n : name => p2 n x5) x4))
 in |- *.
apply L6_Light with x0; auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H19.
auto.
apply notin_nu; intros.
inversion_clear H9.
cut (notin x0 (nu (p2 z))); [ intro | auto ].
inversion_clear H9.
auto.
apply notin_nu; intros.
inversion_clear H24.
cut (notin x4 (nu (x2 z))); [ intro | auto ].
inversion_clear H24.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x4 (nu (p2 z))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 x4))); [ intro | auto ].
inversion_clear H19.
auto.
apply notin_nu; intros.
inversion_clear H9.
cut (notin x0 (nu (p2 x4))); [ intro | auto ].
inversion_clear H9.
auto.
change (StBisim ((fun n : name => x2 n y) x3) ((fun n : name => p2 n y) x3))
 in |- *.
apply L6_Light with x0; auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H19.
auto.
apply notin_nu; intros.
inversion_clear H9.
cut (notin x0 (nu (p2 z))); [ intro | auto ].
inversion_clear H9.
auto.
apply b_act_notin_In; auto.

inversion H0.
elim
 (unsat (par (nu p) (par (nu q) (nu (fun z : name => nu (p2 z))))) (cons x l));
 intros.
inversion_clear H5.
inversion_clear H6.
inversion_clear H8.
inversion_clear H7.
cut (StBisim (p x0) (q x0)); [ intro | auto ].
inversion_clear H7.
inversion_clear H11.
inversion_clear H12.
elim (H13 x); intros.
cut (btrans (p x0) (bOut x) (p2 x0)); [ intro | apply H2; auto ].
elim (H12 (p2 x0) H15); intros.
inversion_clear H16.
elim (ho_proc_exp x1 x0); intros.
inversion_clear H16.
rewrite H20 in H17.
rewrite H20 in H18.
exists (fun n : name => nu (fun z : name => x2 z n)); split.
apply bRES with empty; intros; auto.
clear H23.
inversion_clear H22.
change (btrans (q y) ((fun _ : name => bOut x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut.
assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut.
assumption.
intros.
apply NU_S; intros.
elim
 (unsat
    (par (nu (fun z : name => nu (p2 z))) (nu (fun z : name => nu (x2 z))))
    (cons x0 (cons x3 (cons y l)))); intros.
inversion_clear H24.
inversion_clear H25.
inversion_clear H26.
inversion_clear H28.
inversion_clear H29.
change (StBisim ((fun n : name => p2 n y) x3) ((fun n : name => x2 n y) x3))
 in |- *.
apply L6_Light with x4; auto.
apply notin_nu; intros.
inversion_clear H24.
cut (notin x4 (nu (p2 z))); [ intro | auto ].
inversion_clear H24.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x4 (nu (x2 z))); [ intro | auto ].
inversion_clear H27.
auto.
elim
 (unsat
    (par (nu (fun z : name => nu (p2 z))) (nu (fun z : name => nu (x2 z))))
    (cons x0 (cons x4 (cons y l)))); intros.
inversion_clear H29.
inversion_clear H31.
inversion_clear H32.
inversion_clear H34.
inversion_clear H35.
apply L6_Light with x5; auto.
apply notin_nu; intros.
inversion_clear H29.
cut (notin x5 (nu (p2 x4))); [ intro | auto ].
inversion_clear H29.
auto.
apply notin_nu; intros.
inversion_clear H33.
cut (notin x5 (nu (x2 x4))); [ intro | auto ].
inversion_clear H33.
auto.
change
  (StBisim ((fun n : name => p2 n x5) x4) ((fun n : name => x2 n x5) x4))
 in |- *.
apply L6_Light with x0; auto.
apply notin_nu; intros.
inversion_clear H9.
cut (notin x0 (nu (p2 z))); [ intro | auto ].
inversion_clear H9.
auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H19.
auto.
apply H18.
apply notin_nu; intros.
inversion_clear H29.
cut (notin x5 (nu (p2 x0))); [ intro | auto ].
inversion_clear H29.
auto.
apply notin_nu; intros.
inversion_clear H33.
cut (notin x5 (nu (x2 x0))); [ intro | auto ].
inversion_clear H33.
auto.
apply notin_nu; intros.
inversion_clear H24.
cut (notin x4 (nu (p2 z))); [ intro | auto ].
inversion_clear H24.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x4 (nu (x2 z))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H16.
cut (notin y (nu (fun z0 : name => p2 z0 z))); [ intro | auto ].
inversion_clear H16.
auto.
apply notin_nu; intros.
inversion_clear H21.
cut (notin y (nu (fun z0 : name => x2 z0 z))); [ intro | auto ].
inversion_clear H21.
auto.
apply b_act_notin_bOut; assumption.

elim (unsat (par (nu p) (par (nu q) (nu p1))) (cons x l)); intros.
inversion_clear H5.
inversion_clear H6.
inversion_clear H8.
inversion_clear H7.
cut (StBisim (p x1) (q x1)); [ intro | auto ].
inversion_clear H7.
inversion_clear H11.
elim (H7 (Out x x1)); intros.
cut (ftrans (p x1) (Out x x1) (p1 x1)); [ intro | apply H3; auto ].
elim (H11 (p1 x1) H14); intros.
inversion_clear H15.
elim (proc_exp x2 x1); intros.
inversion_clear H15.
rewrite H19 in H16.
rewrite H19 in H17.
exists x3; split.
apply OPEN with empty; intros; auto.
clear H22.
change (ftrans (q y) ((fun n : name => Out x n) y) (x3 y)) in |- *;
 apply FTR_L3 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out.
assumption.
assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out.
auto.
assumption.
intros.
apply L6_Light with x1; auto.

inversion H0.
elim
 (unsat (par (nu p) (par (nu q) (nu (fun z : name => nu (p2 z))))) (cons x l));
 intros.
inversion_clear H5.
inversion_clear H6.
inversion_clear H8.
inversion_clear H7.
cut (StBisim (p x0) (q x0)); [ intro | auto ].
inversion_clear H7.
inversion_clear H11.
inversion_clear H12.
elim (H13 x); intros.
cut (btrans (q x0) (bOut x) (p2 x0)); [ intro | apply H2; auto ].
elim (H14 (p2 x0) H15); intros.
inversion_clear H16.
elim (ho_proc_exp x1 x0); intros.
inversion_clear H16.
rewrite H20 in H17.
rewrite H20 in H18.
exists (fun n : name => nu (fun z : name => x2 z n)); split.
apply bRES with empty; intros; auto.
clear H23.
inversion_clear H22.
change (btrans (p y) ((fun _ : name => bOut x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut.
assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut.
assumption.
intros.
apply NU_S; intros.
elim
 (unsat
    (par (nu (fun z : name => nu (p2 z))) (nu (fun z : name => nu (x2 z))))
    (cons x0 (cons x3 (cons y l)))); intros.
inversion_clear H24.
inversion_clear H25.
inversion_clear H26.
inversion_clear H28.
inversion_clear H29.
change (StBisim ((fun n : name => x2 n y) x3) ((fun n : name => p2 n y) x3))
 in |- *.
apply L6_Light with x4; auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x4 (nu (x2 z))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H24.
cut (notin x4 (nu (p2 z))); [ intro | auto ].
inversion_clear H24.
auto.
elim
 (unsat
    (par (nu (fun z : name => nu (p2 z))) (nu (fun z : name => nu (x2 z))))
    (cons x0 (cons x4 (cons y l)))); intros.
inversion_clear H29.
inversion_clear H31.
inversion_clear H32.
inversion_clear H34.
inversion_clear H35.
apply L6_Light with x5; auto.
apply notin_nu; intros.
inversion_clear H33.
cut (notin x5 (nu (x2 x4))); [ intro | auto ].
inversion_clear H33.
auto.
apply notin_nu; intros.
inversion_clear H29.
cut (notin x5 (nu (p2 x4))); [ intro | auto ].
inversion_clear H29.
auto.
change
  (StBisim ((fun n : name => x2 n x5) x4) ((fun n : name => p2 n x5) x4))
 in |- *.
apply L6_Light with x0; auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H19.
auto.
apply notin_nu; intros.
inversion_clear H9.
cut (notin x0 (nu (p2 z))); [ intro | auto ].
inversion_clear H9.
auto.
apply H18.
apply notin_nu; intros.
inversion_clear H33.
cut (notin x5 (nu (x2 x0))); [ intro | auto ].
inversion_clear H33.
auto.
apply notin_nu; intros.
inversion_clear H29.
cut (notin x5 (nu (p2 x0))); [ intro | auto ].
inversion_clear H29.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x4 (nu (x2 z))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H24.
cut (notin x4 (nu (p2 z))); [ intro | auto ].
inversion_clear H24.
auto.
apply notin_nu; intros.
inversion_clear H16.
cut (notin y (nu (fun z0 : name => x2 z0 z))); [ intro | auto ].
inversion_clear H16.
auto.
apply notin_nu; intros.
inversion_clear H21.
cut (notin y (nu (fun z0 : name => p2 z0 z))); [ intro | auto ].
inversion_clear H21.
auto.
apply b_act_notin_bOut; assumption.

elim (unsat (par (nu p) (par (nu q) (nu q1))) (cons x l)); intros.
inversion_clear H5.
inversion_clear H6.
inversion_clear H8.
inversion_clear H7.
cut (StBisim (p x1) (q x1)); [ intro | auto ].
inversion_clear H7.
inversion_clear H11.
elim (H7 (Out x x1)); intros.
cut (ftrans (q x1) (Out x x1) (q1 x1)); [ intro | apply H3; auto ].
elim (H13 (q1 x1) H14); intros.
inversion_clear H15.
elim (proc_exp x2 x1); intros.
inversion_clear H15.
rewrite H19 in H16.
rewrite H19 in H17.
exists x3; split.
apply OPEN with empty; intros; auto.
clear H22.
change (ftrans (p y) ((fun n : name => Out x n) y) (x3 y)) in |- *;
 apply FTR_L3 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out.
assumption.
assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out.
auto.
assumption.
intros.
apply L6_Light with x1; auto.

Qed.

(*****************************************************)
(* Congruence of StBisim w.r.t. parallel composition *)
(* is proved by means of internal cross adequacy.    *)
(*****************************************************)

(* The next four definitions allow to build the
 * strong late bisimulation needed to prove the
 * congruence of StBisim w.r.t. parallel composition.
 *)

Inductive BisPAR_S : proc -> proc -> Prop :=
    bispar_s :
      forall p q : proc,
      StBisim p q -> forall r : proc, BisPAR_S (par p r) (par q r).

Inductive Op_PAR_S (R : proc -> proc -> Prop) : proc -> proc -> Prop :=
    op_par_s :
      forall p q : name -> proc,
      (forall z : name, notin z (nu p) -> notin z (nu q) -> R (p z) (q z)) ->
      Op_PAR_S R (nu p) (nu q).

Fixpoint PAR_S_fun (n : nat) : proc -> proc -> Prop :=
  match n with
  | O => BisPAR_S
  | S m => Op_PAR_S (PAR_S_fun m)
  end.

Inductive SBPAR_S (p q : proc) : Prop :=
    sbpar_s : forall n : nat, PAR_S_fun n p q -> SBPAR_S p q.

(* Next we establish a property of PAR_S_fun
 * similar to that of L6_Light for StBisim.
 *)

Lemma PAR_S_RW :
 forall (n : nat) (p q : name -> proc) (x : name),
 notin x (nu p) ->
 notin x (nu q) ->
 PAR_S_fun n (p x) (q x) ->
 forall y : name, notin y (nu p) -> notin y (nu q) -> PAR_S_fun n (p y) (q y).

Proof.

intros; elim (LEM_name x y); intro.

rewrite <- H4; assumption.

generalize p q x H H0 y H4 H2 H3 H1; clear H H0 H2 H3 H4 y H1 x p q;
 induction  n as [| n Hrecn]; intros.

(* Base Case *)

simpl in H1; inversion H1; simpl in |- *.
elim (proc_exp p0 x); elim (proc_exp q0 x); elim (proc_exp r x); intros.
inversion_clear H8; inversion_clear H9; inversion_clear H10.
rewrite H14 in H5; rewrite H13 in H6; rewrite H12 in H5; rewrite H12 in H6;
 cut (p = (fun n : name => par (x2 n) (x0 n)));
 [ intro | apply proc_ext with x; auto ].
cut (q = (fun n : name => par (x1 n) (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H10; rewrite H15; apply bispar_s.
rewrite H10 in H1; rewrite H15 in H1; inversion_clear H1.
apply L6 with x; auto.
rewrite H10 in H2; inversion_clear H2; apply notin_nu; intros.
cut (notin y (par (x2 z) (x0 z))); [ intro | auto ].
inversion_clear H17; assumption.
rewrite H15 in H3; inversion_clear H3; apply notin_nu; intros.
cut (notin y (par (x1 z) (x0 z))); [ intro | auto ].
inversion_clear H17; assumption.
inversion_clear H8; inversion_clear H11; apply notin_nu; intros;
 apply notin_par; auto.
inversion_clear H9; inversion_clear H11; apply notin_nu; intros;
 apply notin_par; auto.

(* Inductive Step *)

simpl in H1; inversion H1; simpl in |- *.
elim (ho_proc_exp p0 x); elim (ho_proc_exp q0 x); intros.
inversion_clear H8; inversion_clear H9.
rewrite H12 in H5; rewrite H11 in H6.
cut (p = (fun n : name => nu (x1 n)));
 [ intro | apply proc_ext with x; auto ].
cut (q = (fun n : name => nu (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H9; rewrite H13; apply op_par_s; intros.
elim
 (unsat
    (par (nu p)
       (par (nu q)
          (par (nu (fun n : name => nu (x0 n)))
             (nu (fun n : name => nu (x1 n))))))
    (cons x (cons y (cons z empty)))); intros.
inversion_clear H16.
inversion_clear H17; inversion_clear H18.
inversion_clear H19; inversion_clear H20.
inversion_clear H21; inversion_clear H22.
clear H24.
apply Hrecn with x2; auto.
inversion_clear H23; auto.
inversion_clear H20; auto.
change
  (PAR_S_fun n ((fun n : name => x1 n x2) y) ((fun n : name => x0 n x2) y))
 in |- *; apply Hrecn with x; auto.
inversion_clear H8; apply notin_nu; intros.
cut (notin x (nu (x1 z0))); [ intro | auto ].
inversion_clear H24; auto.
inversion_clear H10; apply notin_nu; intros.
cut (notin x (nu (x0 z0))); [ intro | auto ].
inversion_clear H24; auto.
apply proc_mono with x; inversion_clear H2.
cut (notin y (p x)); [ rewrite <- H5; intro | auto ].
inversion_clear H2; auto.
apply proc_mono with x; inversion_clear H3.
cut (notin y (q x)); [ rewrite <- H6; intro | auto ].
inversion_clear H3; auto.
rewrite <- H11; rewrite <- H12; apply H7; auto.
inversion_clear H23.
cut (notin x2 (nu (x1 x))); [ intro | auto ]; rewrite H12; assumption.
inversion_clear H20.
cut (notin x2 (nu (x0 x))); [ intro | auto ]; rewrite H11; assumption.

Qed.

(* Now we prove that SBPAR_S is indeed a strong late bisimulation. *)

Lemma SBPAR_S_TO_SB' : Inclus SBPAR_S (Op_StBisim SBPAR_S).

Proof.

unfold Inclus in |- *; intros.
inversion_clear H.
cut (PAR_S_fun n p1 p2);
 [ generalize p1 p2; generalize n; simple induction n0; intros | assumption ].

(* Base case *)

simpl in H; inversion H.
inversion_clear H1.
inversion_clear H4.
inversion_clear H5.
apply op_sb; split; intros.

elim a; intros; split; intros.

inversion_clear H5.

elim (H1 tau); intros.
elim (H5 p7 H7); intros.
inversion_clear H9.
exists (par x r); split; [ apply fPAR1; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; assumption.
exists (par q p7); split; [ apply fPAR2; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; rewrite <- H2 in H;
 rewrite <- H3 in H; inversion_clear H; assumption.

elim (H4 x); intros.
elim (H5 q1 H7); intros.
inversion_clear H10.
exists (par (x0 y) q2); split; [ apply COM1 with x; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; auto.
elim (H1 (Out x y)); intros.
elim (H5 q1 H7); intros.
inversion_clear H10.
exists (par x0 (q2 y)); split; [ apply COM2 with x; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; assumption.

elim (H4 x); intros.
elim (H5 q1 H7); intros.
inversion_clear H10.
exists (nu (fun n : name => par (x0 n) (q2 n))); split;
 [ apply CLOSE1 with x; assumption | idtac ].
apply sbpar_s with 1; simpl in |- *; apply op_par_s; intros; apply bispar_s;
 auto.

elim (H6 x); intros.
elim (H5 q1 H7); intros.
inversion_clear H10.
exists (nu (fun n : name => par (x0 n) (q2 n))); split;
 [ apply CLOSE2 with x; assumption | idtac ].
apply sbpar_s with 1; simpl in |- *; apply op_par_s; intros; apply bispar_s;
 apply H12; auto.
inversion_clear H10; apply notin_nu; intros.
cut (notin z (par (q1 z0) (q2 z0))); [ intro | auto ].
inversion_clear H15; assumption.
inversion_clear H13; apply notin_nu; intros.
cut (notin z (par (x0 z0) (q2 z0))); [ intro | auto ].
inversion_clear H15; assumption.

inversion_clear H5.

elim (H1 tau); intros.
elim (H8 p6 H7); intros.
inversion_clear H9.
exists (par x r); split; [ apply fPAR1; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; assumption.
exists (par p p6); split; [ apply fPAR2; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; rewrite <- H2 in H;
 rewrite <- H3 in H; inversion_clear H; assumption.

elim (H4 x); intros.
elim (H9 q0 H7); intros.
inversion_clear H10.
exists (par (x0 y) q2); split; [ apply COM1 with x; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; auto.
elim (H1 (Out x y)); intros.
elim (H9 q0 H7); intros.
inversion_clear H10.
exists (par x0 (q2 y)); split; [ apply COM2 with x; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; assumption.

elim (H4 x); intros.
elim (H9 q0 H7); intros.
inversion_clear H10.
exists (nu (fun n : name => par (x0 n) (q2 n))); split;
 [ apply CLOSE1 with x; assumption | idtac ].
apply sbpar_s with 1; simpl in |- *; apply op_par_s; intros; apply bispar_s;
 auto.

elim (H6 x); intros.
elim (H9 q0 H7); intros.
inversion_clear H10.
exists (nu (fun n : name => par (x0 n) (q2 n))); split;
 [ apply CLOSE2 with x; assumption | idtac ].
apply sbpar_s with 1; simpl in |- *; apply op_par_s; intros; apply bispar_s;
 apply H12; auto.
inversion_clear H10; apply notin_nu; intros.
cut (notin z (par (x0 z0) (q2 z0))); [ intro | auto ].
inversion_clear H15; assumption.
inversion_clear H13; apply notin_nu; intros.
cut (notin z (par (q0 z0) (q2 z0))); [ intro | auto ].
inversion_clear H15; assumption.

inversion_clear H5.
elim (H1 (Out n1 n2)); intros.
elim (H5 p7 H7); intros.
inversion_clear H9.
exists (par x r); split; [ apply fPAR1; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; assumption.
exists (par q p7); split; [ apply fPAR2; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; rewrite <- H2 in H;
 rewrite <- H3 in H; inversion_clear H; assumption.

inversion_clear H5.
elim (H1 (Out n1 n2)); intros.
elim (H8 p6 H7); intros.
inversion_clear H9.
exists (par x r); split; [ apply fPAR1; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; assumption.
exists (par p p6); split; [ apply fPAR2; assumption | idtac ].
apply sbpar_s with 0; simpl in |- *; apply bispar_s; rewrite <- H2 in H;
 rewrite <- H3 in H; inversion_clear H; assumption.

(* Input actions case *)

split; intros.

elim (H4 x); intros; split; intros.

inversion_clear H8.
elim (H5 p7 H9); intros.
inversion_clear H8.
exists (fun n : name => par (x0 n) r); split;
 [ apply bPAR1; assumption | idtac ].
intro; apply sbpar_s with 0; simpl in |- *; apply bispar_s; auto.
exists (fun n : name => par q (p7 n)); split;
 [ apply bPAR2; assumption | idtac ].
intro; apply sbpar_s with 0; simpl in |- *; apply bispar_s;
 rewrite <- H2 in H; rewrite <- H3 in H; inversion_clear H; 
 assumption.

inversion_clear H8.
elim (H7 p6 H9); intros.
inversion_clear H8.
exists (fun n : name => par (x0 n) r); split;
 [ apply bPAR1; assumption | idtac ].
intro; apply sbpar_s with 0; simpl in |- *; apply bispar_s; auto.
exists (fun n : name => par p (p6 n)); split;
 [ apply bPAR2; assumption | idtac ].
intro; apply sbpar_s with 0; simpl in |- *; apply bispar_s;
 rewrite <- H2 in H; rewrite <- H3 in H; inversion_clear H; 
 assumption.

(* Bound Output actions case *)

elim (H6 x); intros; split; intros.

inversion_clear H8.
elim (H5 p7 H9); intros.
inversion_clear H8.
exists (fun n : name => par (x0 n) r); split;
 [ apply bPAR1; assumption | idtac ].
intros; apply sbpar_s with 0; simpl in |- *; apply bispar_s; apply H11; auto.
inversion_clear H8; apply notin_nu; intros.
cut (notin y (par (p7 z) r)); [ intro | auto ].
inversion_clear H14; assumption.
inversion_clear H12; apply notin_nu; intros.
cut (notin y (par (x0 z) r)); [ intro | auto ].
inversion_clear H14; assumption.
exists (fun n : name => par q (p7 n)); split;
 [ apply bPAR2; assumption | idtac ].
intros; apply sbpar_s with 0; simpl in |- *; apply bispar_s;
 rewrite <- H2 in H; rewrite <- H3 in H; inversion_clear H; 
 assumption.

inversion_clear H8.
elim (H7 p6 H9); intros.
inversion_clear H8.
exists (fun n : name => par (x0 n) r); split;
 [ apply bPAR1; assumption | idtac ].
intros; apply sbpar_s with 0; simpl in |- *; apply bispar_s; apply H11; auto.
inversion_clear H8; apply notin_nu; intros.
cut (notin y (par (x0 z) r)); [ intro | auto ].
inversion_clear H14; assumption.
inversion_clear H12; apply notin_nu; intros.
cut (notin y (par (p6 z) r)); [ intro | auto ].
inversion_clear H14; assumption.
exists (fun n : name => par p (p6 n)); split;
 [ apply bPAR2; assumption | idtac ].
intros; apply sbpar_s with 0; simpl in |- *; apply bispar_s;
 rewrite <- H2 in H; rewrite <- H3 in H; inversion_clear H; 
 assumption.

(* Inductive Step *)

simpl in H1; inversion H1.
apply op_sb; split; intros.

elim a; intros; split; intros.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_S (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu p6))) l); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H10.
cut (ftrans (p x) tau (p6 x)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_S (p x) (q x)); [ intro | apply H5; auto ].
inversion_clear H12.
inversion_clear H13.
elim (H12 tau); intros.
elim (H13 (p6 x) H10); intros.
inversion_clear H16.
elim (proc_exp x0 x); intros.
inversion_clear H16.
rewrite H20 in H17; rewrite H20 in H18.
exists (nu x1); split; [ apply fRES with l; intros | idtac ].
change (ftrans (q y) ((fun _ : name => tau) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
inversion_clear H18.
apply sbpar_s with (S n2); simpl in |- *; apply op_par_s; intros.
apply PAR_S_RW with x; auto.
apply f_act_notin_tau.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_S (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu p5))) l); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H10.
cut (ftrans (q x) tau (p5 x)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_S (p x) (q x)); [ intro | apply H5; auto ].
inversion_clear H12.
inversion_clear H13.
elim (H12 tau); intros.
elim (H15 (p5 x) H10); intros.
inversion_clear H16.
elim (proc_exp x0 x); intros.
inversion_clear H16.
rewrite H20 in H17; rewrite H20 in H18.
exists (nu x1); split; [ apply fRES with l; intros | idtac ].
change (ftrans (p y) ((fun _ : name => tau) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
inversion_clear H18.
apply sbpar_s with (S n2); simpl in |- *; apply op_par_s; intros.
apply PAR_S_RW with x; auto.
apply f_act_notin_tau.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_S (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu p6))) (cons n2 (cons n3 l))); intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (ftrans (p x) (Out n2 n3) (p6 x)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_S (p x) (q x)); [ intro | apply H5; auto ].
inversion_clear H14.
inversion_clear H15.
elim (H14 (Out n2 n3)); intros.
elim (H15 (p6 x) H11); intros.
inversion_clear H18.
elim (proc_exp x0 x); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (nu x1); split; [ apply fRES with l; intros | idtac ].
inversion_clear H25.
change (ftrans (q y) ((fun _ : name => Out n2 n3) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
inversion_clear H20.
apply sbpar_s with (S n4); simpl in |- *; apply op_par_s; intros.
apply PAR_S_RW with x; auto.
apply f_act_notin_Out; auto.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_S (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu p5))) (cons n2 (cons n3 l))); intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (ftrans (q x) (Out n2 n3) (p5 x)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_S (p x) (q x)); [ intro | apply H5; auto ].
inversion_clear H14.
inversion_clear H15.
elim (H14 (Out n2 n3)); intros.
elim (H17 (p5 x) H11); intros.
inversion_clear H18.
elim (proc_exp x0 x); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (nu x1); split; [ apply fRES with l; intros | idtac ].
inversion_clear H25.
change (ftrans (p y) ((fun _ : name => Out n2 n3) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
inversion_clear H20.
apply sbpar_s with (S n4); simpl in |- *; apply op_par_s; intros.
apply PAR_S_RW with x; auto.
apply f_act_notin_Out; auto.

split; intros.

split; intros.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_S (p x) (q x));
 [ intro | auto ].
elim
 (unsat (par (nu p) (par (nu q) (nu (fun n : name => nu (p6 n))))) (cons x l));
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (btrans (p x0) (In x) (p6 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_S (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
elim (H14 x); intros.
elim (H15 (p6 x0) H10); intros.
inversion_clear H18.
elim (ho_proc_exp x1 x0); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (fun n : name => nu (fun u : name => x2 u n)); split;
 [ apply bRES with l; intros | idtac ].
inversion_clear H24;
 change (btrans (q y) ((fun _ : name => In x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
intro; elim (LEM_name x0 y); intro.

rewrite <- H18;
 elim
  (unsat
     (par (nu (fun n : name => nu (p6 n))) (nu (fun n : name => nu (x2 n))))
     (cons x0 empty)); intros.
inversion_clear H23.
inversion_clear H24; inversion_clear H25.
clear H27; cut (SBPAR_S (p6 x0 x3) (x2 x0 x3)); [ intro | auto ].
inversion_clear H25.
apply sbpar_s with (S n2); simpl in |- *; apply op_par_s; intros.
elim
 (unsat
    (par (nu (fun n : name => nu (p6 n))) (nu (fun n : name => nu (x2 n))))
    (cons x0 (cons x3 (cons z empty)))); intros.
inversion_clear H29.
inversion_clear H30; inversion_clear H31.
inversion_clear H33.
inversion_clear H34.
clear H35.
cut (PAR_S_fun n2 (p6 x4 x3) (x2 x4 x3));
 [ intro
 | change
     (PAR_S_fun n2 ((fun n : name => p6 n x3) x4)
        ((fun n : name => x2 n x3) x4)) in |- *; apply PAR_S_RW with x0; 
    auto ].
change
  (PAR_S_fun n2 ((fun n : name => p6 n x0) z) ((fun n : name => x2 n x0) z))
 in |- *; apply PAR_S_RW with x4; auto.
inversion_clear H29; apply notin_nu; intros.
cut (notin x4 (nu (p6 z0))); [ intro | auto ].
inversion_clear H36; auto.
inversion_clear H32; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H36; auto.
apply PAR_S_RW with x3; auto.
inversion_clear H23; auto.
inversion_clear H26; auto.
inversion_clear H12; auto.
inversion_clear H21; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p6 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H29; apply notin_nu; intros.
cut (notin x4 (nu (p6 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H32; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H35; auto.

cut (SBPAR_S (p6 x0 y) (x2 x0 y)); [ intro | auto ].
inversion_clear H23.
apply sbpar_s with (S n2); simpl in |- *; apply op_par_s; intros.
change
  (PAR_S_fun n2 ((fun n : name => p6 n y) z) ((fun n : name => x2 n y) z))
 in |- *; apply PAR_S_RW with x0; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p6 z0))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H27; auto.
apply b_act_notin_In; auto.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_S (p x) (q x));
 [ intro | auto ].
elim
 (unsat (par (nu p) (par (nu q) (nu (fun n : name => nu (p5 n))))) (cons x l));
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (btrans (q x0) (In x) (p5 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_S (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
elim (H14 x); intros.
elim (H17 (p5 x0) H10); intros.
inversion_clear H18.
elim (ho_proc_exp x1 x0); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (fun n : name => nu (fun u : name => x2 u n)); split;
 [ apply bRES with l; intros | idtac ].
inversion_clear H24;
 change (btrans (p y) ((fun _ : name => In x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
intro; elim (LEM_name x0 y); intro.

rewrite <- H18;
 elim
  (unsat
     (par (nu (fun n : name => nu (p5 n))) (nu (fun n : name => nu (x2 n))))
     (cons x0 empty)); intros.
inversion_clear H23.
inversion_clear H24; inversion_clear H25.
clear H27; cut (SBPAR_S (x2 x0 x3) (p5 x0 x3)); [ intro | auto ].
inversion_clear H25.
apply sbpar_s with (S n2); simpl in |- *; apply op_par_s; intros.
elim
 (unsat
    (par (nu (fun n : name => nu (p5 n))) (nu (fun n : name => nu (x2 n))))
    (cons x0 (cons x3 (cons z empty)))); intros.
inversion_clear H29.
inversion_clear H30; inversion_clear H31.
inversion_clear H33.
inversion_clear H34.
clear H35.
cut (PAR_S_fun n2 (x2 x4 x3) (p5 x4 x3));
 [ intro
 | change
     (PAR_S_fun n2 ((fun n : name => x2 n x3) x4)
        ((fun n : name => p5 n x3) x4)) in |- *; apply PAR_S_RW with x0; 
    auto ].
change
  (PAR_S_fun n2 ((fun n : name => x2 n x0) z) ((fun n : name => p5 n x0) z))
 in |- *; apply PAR_S_RW with x4; auto.
inversion_clear H32; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H36; auto.
inversion_clear H29; apply notin_nu; intros.
cut (notin x4 (nu (p5 z0))); [ intro | auto ].
inversion_clear H36; auto.
apply PAR_S_RW with x3; auto.
inversion_clear H26; auto.
inversion_clear H23; auto.
inversion_clear H21; auto.
inversion_clear H12; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p5 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H32; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H29; apply notin_nu; intros.
cut (notin x4 (nu (p5 z0))); [ intro | auto ].
inversion_clear H35; auto.

cut (SBPAR_S (x2 x0 y) (p5 x0 y)); [ intro | auto ].
inversion_clear H23.
apply sbpar_s with (S n2); simpl in |- *; apply op_par_s; intros.
change
  (PAR_S_fun n2 ((fun n : name => x2 n y) z) ((fun n : name => p5 n y) z))
 in |- *; apply PAR_S_RW with x0; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p5 z0))); [ intro | auto ].
inversion_clear H27; auto.
apply b_act_notin_In; auto.

split; intros.

inversion_clear H5.

cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_S (p x) (q x));
 [ intro | auto ].
elim
 (unsat (par (nu p) (par (nu q) (nu (fun n : name => nu (p6 n))))) (cons x l));
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (btrans (p x0) (bOut x) (p6 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_S (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
elim (H16 x); intros.
elim (H15 (p6 x0) H10); intros.
inversion_clear H18.
elim (ho_proc_exp x1 x0); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (fun n : name => nu (fun u : name => x2 u n)); split;
 [ apply bRES with l; intros | idtac ].
inversion_clear H24;
 change (btrans (q y) ((fun _ : name => bOut x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
intros; elim (LEM_name x0 y); intro.

rewrite <- H24;
 elim
  (unsat
     (par (nu (fun n : name => nu (p6 n))) (nu (fun n : name => nu (x2 n))))
     (cons x0 empty)); intros.
inversion_clear H25.
inversion_clear H26; inversion_clear H27.
clear H29; cut (SBPAR_S (p6 x0 x3) (x2 x0 x3)); [ intro | apply H20; auto ].
inversion_clear H27.
apply sbpar_s with (S n2); simpl in |- *; apply op_par_s; intros.
elim
 (unsat
    (par (nu (fun n : name => nu (p6 n))) (nu (fun n : name => nu (x2 n))))
    (cons x0 (cons x3 (cons z empty)))); intros.
inversion_clear H31.
inversion_clear H32; inversion_clear H33.
inversion_clear H35.
inversion_clear H36.
clear H37.
cut (PAR_S_fun n2 (p6 x4 x3) (x2 x4 x3));
 [ intro
 | change
     (PAR_S_fun n2 ((fun n : name => p6 n x3) x4)
        ((fun n : name => x2 n x3) x4)) in |- *; apply PAR_S_RW with x0; 
    auto ].
change
  (PAR_S_fun n2 ((fun n : name => p6 n x0) z) ((fun n : name => x2 n x0) z))
 in |- *; apply PAR_S_RW with x4; auto.
inversion_clear H31; apply notin_nu; intros.
cut (notin x4 (nu (p6 z0))); [ intro | auto ].
inversion_clear H38; auto.
inversion_clear H34; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H38; auto.
apply PAR_S_RW with x3; auto.
inversion_clear H25; auto.
inversion_clear H28; auto.
inversion_clear H12; auto.
inversion_clear H21; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p6 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H31; apply notin_nu; intros.
cut (notin x4 (nu (p6 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H34; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H25; auto.
inversion_clear H28; auto.

cut (SBPAR_S (p6 x0 y) (x2 x0 y)); [ intro | apply H20; auto ].
inversion_clear H25.
apply sbpar_s with (S n2); simpl in |- *; apply op_par_s; intros.
change
  (PAR_S_fun n2 ((fun n : name => p6 n y) z) ((fun n : name => x2 n y) z))
 in |- *; apply PAR_S_RW with x0; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p6 z0))); [ intro | auto ].
inversion_clear H29; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H29; auto.
inversion_clear H18; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => p6 z0 z))); [ intro | auto ].
inversion_clear H26; auto.
inversion_clear H23; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => x2 z0 z))); [ intro | auto ].
inversion_clear H26; auto.
apply b_act_notin_bOut; auto.

cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_S (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu p4))) (cons x l)); intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (ftrans (p x0) (Out x x0) (p4 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_S (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
elim (H13 (Out x x0)); intros.
elim (H14 (p4 x0) H10); intros.
inversion_clear H17.
elim (proc_exp x1 x0); intros.
inversion_clear H17.
rewrite H21 in H18; rewrite H21 in H19.
exists x2; split; [ apply OPEN with l; intros | idtac ].
change (ftrans (q y) (Out x y) (x2 y)) in |- *; apply FTR_L3 with x0; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
intros; inversion_clear H19.
apply sbpar_s with n2; apply PAR_S_RW with x0; auto.

inversion_clear H5.

cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_S (p x) (q x));
 [ intro | auto ].
elim
 (unsat (par (nu p) (par (nu q) (nu (fun n : name => nu (p5 n))))) (cons x l));
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (btrans (q x0) (bOut x) (p5 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_S (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
elim (H16 x); intros.
elim (H17 (p5 x0) H10); intros.
inversion_clear H18.
elim (ho_proc_exp x1 x0); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (fun n : name => nu (fun u : name => x2 u n)); split;
 [ apply bRES with l; intros | idtac ].
inversion_clear H24;
 change (btrans (p y) ((fun _ : name => bOut x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
intros; elim (LEM_name x0 y); intro.

rewrite <- H24;
 elim
  (unsat
     (par (nu (fun n : name => nu (p5 n))) (nu (fun n : name => nu (x2 n))))
     (cons x0 empty)); intros.
inversion_clear H25.
inversion_clear H26; inversion_clear H27.
clear H29; cut (SBPAR_S (x2 x0 x3) (p5 x0 x3)); [ intro | apply H20; auto ].
inversion_clear H27.
apply sbpar_s with (S n2); simpl in |- *; apply op_par_s; intros.
elim
 (unsat
    (par (nu (fun n : name => nu (p5 n))) (nu (fun n : name => nu (x2 n))))
    (cons x0 (cons x3 (cons z empty)))); intros.
inversion_clear H31.
inversion_clear H32; inversion_clear H33.
inversion_clear H35.
inversion_clear H36.
clear H37.
cut (PAR_S_fun n2 (x2 x4 x3) (p5 x4 x3));
 [ intro
 | change
     (PAR_S_fun n2 ((fun n : name => x2 n x3) x4)
        ((fun n : name => p5 n x3) x4)) in |- *; apply PAR_S_RW with x0; 
    auto ].
change
  (PAR_S_fun n2 ((fun n : name => x2 n x0) z) ((fun n : name => p5 n x0) z))
 in |- *; apply PAR_S_RW with x4; auto.
inversion_clear H34; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H38; auto.
inversion_clear H31; apply notin_nu; intros.
cut (notin x4 (nu (p5 z0))); [ intro | auto ].
inversion_clear H38; auto.
apply PAR_S_RW with x3; auto.
inversion_clear H28; auto.
inversion_clear H25; auto.
inversion_clear H21; auto.
inversion_clear H12; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p5 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H34; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H31; apply notin_nu; intros.
cut (notin x4 (nu (p5 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H28; auto.
inversion_clear H25; auto.

cut (SBPAR_S (x2 x0 y) (p5 x0 y)); [ intro | apply H20; auto ].
inversion_clear H25.
apply sbpar_s with (S n2); simpl in |- *; apply op_par_s; intros.
change
  (PAR_S_fun n2 ((fun n : name => x2 n y) z) ((fun n : name => p5 n y) z))
 in |- *; apply PAR_S_RW with x0; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H29; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p5 z0))); [ intro | auto ].
inversion_clear H29; auto.
inversion_clear H18; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => x2 z0 z))); [ intro | auto ].
inversion_clear H26; auto.
inversion_clear H23; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => p5 z0 z))); [ intro | auto ].
inversion_clear H26; auto.
apply b_act_notin_bOut; auto.

cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_S (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu q1))) (cons x l)); intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (ftrans (q x0) (Out x x0) (q1 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_S (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
elim (H13 (Out x x0)); intros.
elim (H16 (q1 x0) H10); intros.
inversion_clear H17.
elim (proc_exp x1 x0); intros.
inversion_clear H17.
rewrite H21 in H18; rewrite H21 in H19.
exists x2; split; [ apply OPEN with l; intros | idtac ].
change (ftrans (p y) (Out x y) (x2 y)) in |- *; apply FTR_L3 with x0; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
intros; inversion_clear H19.
apply sbpar_s with n2; apply PAR_S_RW with x0; auto.

Qed.

(* Finally, the main goal, i.e., the congruence of StBisim
 * w.r.t. parallel composition.
 *)

Lemma PAR_S : forall p q r : proc, StBisim p q -> StBisim (par p r) (par q r).

Proof.

intros; apply Completeness; apply Co_Ind with SBPAR_S;
 [ exact SBPAR_S_TO_SB'
 | apply sbpar_s with 0; simpl in |- *; apply bispar_s; assumption ].

Qed.

Lemma MATCH_S :
 forall p q : proc,
 StBisim p q -> forall x y : name, StBisim (match_ x y p) (match_ x y q).

Proof. (* This lemma is proved from scratch. *)

intros; apply sb; do 3 try (split; intros).
inversion H0.
inversion H.
inversion_clear H7.
elim (H10 a); intros.
elim (H7 p1 H6); intros.
exists x1; split; [ apply fMATCH; tauto | tauto ].

inversion H0.
inversion H.
inversion_clear H7.
elim (H10 a); intros.
elim (H12 q1 H6); intros.
exists x1; split; [ apply fMATCH; tauto | tauto ].

inversion H0.
inversion H.
inversion_clear H7.
inversion_clear H11.
elim (H7 x0); intros.
elim (H11 p1 H6); intros.
inversion_clear H14.
exists x2; split; [ apply bMATCH; assumption | intro; auto ].

inversion H0.
inversion H.
inversion_clear H7.
inversion_clear H11.
elim (H7 x0); intros.
elim (H13 q1 H6); intros.
inversion_clear H14.
exists x2; split; [ apply bMATCH; assumption | intro; auto ].

inversion H0.
inversion H.
inversion_clear H7.
inversion_clear H11.
elim (H12 x0); intros.
elim (H11 p1 H6); intros.
inversion_clear H14.
exists x2; split; [ apply bMATCH; assumption | intros; auto ].

inversion H0.
inversion H.
inversion_clear H7.
inversion_clear H11.
elim (H12 x0); intros.
elim (H13 q1 H6); intros.
inversion_clear H14.
exists x2; split; [ apply bMATCH; assumption | intros; auto ].

Qed.

Lemma MISMATCH_S :
 forall p q : proc,
 StBisim p q -> forall x y : name, StBisim (mismatch x y p) (mismatch x y q).

Proof. (* This lemma is proved from scratch. *)

intros; apply sb; do 3 try (split; intros).
inversion H0.
inversion H.
inversion_clear H8.
elim (H11 a); intros.
elim (H8 p1 H7); intros.
exists x1; split; [ apply fMISMATCH; tauto | tauto ].

inversion H0.
inversion H.
inversion_clear H8.
elim (H11 a); intros.
elim (H13 q1 H7); intros.
exists x1; split; [ apply fMISMATCH; tauto | tauto ].

inversion H0.
inversion H.
inversion_clear H8.
inversion_clear H12.
elim (H8 x0); intros.
elim (H12 p1 H7); intros.
inversion_clear H15.
exists x2; split; [ apply bMISMATCH; assumption | intro; auto ].

inversion H0.
inversion H.
inversion_clear H8.
inversion_clear H12.
elim (H8 x0); intros.
elim (H14 q1 H7); intros.
inversion_clear H15.
exists x2; split; [ apply bMISMATCH; assumption | intro; auto ].

inversion H0.
inversion H.
inversion_clear H8.
inversion_clear H12.
elim (H13 x0); intros.
elim (H12 p1 H7); intros.
inversion_clear H15.
exists x2; split; [ apply bMISMATCH; assumption | intros; auto ].

inversion H0.
inversion H.
inversion_clear H8.
inversion_clear H12.
elim (H13 x0); intros.
elim (H14 q1 H7); intros.
inversion_clear H15.
exists x2; split; [ apply bMISMATCH; assumption | intros; auto ].

Qed.

Lemma IN_S :
 forall (p' q' : name -> proc) (x y : name),
 notin y (nu p') ->
 notin y (nu q') ->
 (forall z : name,
  isin z (nu p') \/ isin z (nu q') \/ z = y -> StBisim (p' z) (q' z)) ->
 StBisim (in_pref x p') (in_pref x q').

Proof. (* This lemma depends on Lemma L6_Light. *)

intros; apply sb; do 3 try (split; intros).

inversion_clear H2.

inversion_clear H2.

inversion H2.
rewrite <- H3 in H2; rewrite <- H5 in H2; rewrite <- H6 in H2.
exists q'; split.
apply IN.
rewrite <- H3; intro.
elim (LEM_OC (par (nu p') (par (nu q') (out_pref y y nil))) y0); intro.
inversion_clear H7;
 [ apply H1; left; assumption
 | inversion_clear H8;
    [ apply H1; right; left; assumption
    | inversion H7;
       [ inversion_clear H9
       | apply H1; right; right; trivial
       | apply H1; right; right; trivial ] ] ].
inversion_clear H7.
inversion_clear H9.
inversion_clear H10.
clear H11 H12.
apply L6_Light with y; auto.

inversion H2.
rewrite <- H3 in H2; rewrite <- H5 in H2; rewrite <- H6 in H2.
exists p'; split.
apply IN.
rewrite <- H3; intro.
elim (LEM_OC (par (nu p') (par (nu q') (out_pref y y nil))) y0); intro.
inversion_clear H7;
 [ apply H1; left; assumption
 | inversion_clear H8;
    [ apply H1; right; left; assumption
    | inversion H7;
       [ inversion_clear H9
       | apply H1; right; right; trivial
       | apply H1; right; right; trivial ] ] ].
inversion_clear H7.
inversion_clear H9.
inversion_clear H10.
clear H11 H12.
apply L6_Light with y; auto.

inversion_clear H2.

inversion_clear H2.

Qed.

Lemma OUT_S :
 forall p q : proc,
 StBisim p q -> forall x y : name, StBisim (out_pref x y p) (out_pref x y q).

Proof. (* This lemma is proved from scratch. *)

intros; apply sb; do 3 try (split; intros).
inversion H0.
exists q; split; [ apply OUT | rewrite <- H5; assumption ].

inversion H0.
exists p; split; [ apply OUT | rewrite <- H5; assumption ].

inversion_clear H0.

inversion_clear H0.

inversion_clear H0.

inversion_clear H0.

Qed.

(* End structural_congruence1. *)

(* Section monoidal_sum. *)

Lemma ID_SUM : forall p : proc, StBisim (sum p nil) p.

Proof. (* This lemma depends on Lemma REF. *)

intro; apply sb; do 3 try (split; intros).

inversion_clear H.
exists p1; split; [ assumption | apply REF ].
inversion_clear H0.
exists q1; split; [ apply fSUM1; assumption | apply REF ].

inversion_clear H.
exists p1; split; [ assumption | intro; apply REF ].
inversion_clear H0.
exists q1; split; [ apply bSUM1; assumption | intro; apply REF ].

inversion_clear H.
exists p1; split; [ assumption | intros; apply REF ].
inversion_clear H0.
exists q1; split; [ apply bSUM1; assumption | intros; apply REF ].

Qed.

Lemma IDEM_SUM : forall p : proc, StBisim (sum p p) p.

Proof. (* This lemma depends on Lemma REF. *)

intro; apply sb; do 3 try (split; intros).

inversion_clear H.
exists p1; split; [ assumption | apply REF ].
exists p1; split; [ assumption | apply REF ].
exists q1; split; [ apply fSUM1; assumption | apply REF ].

inversion_clear H.
exists p1; split; [ assumption | intro; apply REF ].
exists p1; split; [ assumption | intro; apply REF ].
exists q1; split; [ apply bSUM1; assumption | intro; apply REF ].

inversion_clear H.
exists p1; split; [ assumption | intros; apply REF ].
exists p1; split; [ assumption | intros; apply REF ].
exists q1; split; [ apply bSUM1; assumption | intros; apply REF ].

Qed.

Lemma COMM_SUM : forall p q : proc, StBisim (sum p q) (sum q p).

Proof. (* This lemma depends on Lemma REF. *)

intros; apply sb; do 3 try (split; intros).

inversion_clear H.
exists p1; split; [ apply fSUM2; assumption | apply REF ].
exists p1; split; [ apply fSUM1; assumption | apply REF ].

inversion_clear H.
exists q1; split; [ apply fSUM2; assumption | apply REF ].
exists q1; split; [ apply fSUM1; assumption | apply REF ].

inversion_clear H.
exists p1; split; [ apply bSUM2; assumption | intro; apply REF ].
exists p1; split; [ apply bSUM1; assumption | intro; apply REF ].

inversion_clear H.
exists q1; split; [ apply bSUM2; assumption | intro; apply REF ].
exists q1; split; [ apply bSUM1; assumption | intro; apply REF ].

inversion_clear H.
exists p1; split; [ apply bSUM2; assumption | intros; apply REF ].
exists p1; split; [ apply bSUM1; assumption | intros; apply REF ].

inversion_clear H.
exists q1; split; [ apply bSUM2; assumption | intros; apply REF ].
exists q1; split; [ apply bSUM1; assumption | intros; apply REF ].

Qed.

Lemma ASS_SUM :
 forall p q r : proc, StBisim (sum p (sum q r)) (sum (sum p q) r).

Proof. (* This lemma depends on Lemma REF. *)

intros; apply sb; do 3 try (split; intros).

inversion_clear H.
exists p1; split; [ apply fSUM1; apply fSUM1; assumption | apply REF ].
inversion_clear H0.
exists p1; split; [ apply fSUM1; apply fSUM2; assumption | apply REF ].
exists p1; split; [ apply fSUM2; assumption | apply REF ].

inversion_clear H.
inversion_clear H0.
exists q1; split; [ apply fSUM1; assumption | apply REF ].
exists q1; split; [ apply fSUM2; apply fSUM1; assumption | apply REF ].
exists q1; split; [ apply fSUM2; apply fSUM2; assumption | apply REF ].

inversion_clear H.
exists p1; split; [ apply bSUM1; apply bSUM1; assumption | intro; apply REF ].
inversion_clear H0.
exists p1; split; [ apply bSUM1; apply bSUM2; assumption | intro; apply REF ].
exists p1; split; [ apply bSUM2; assumption | intro; apply REF ].

inversion_clear H.
inversion_clear H0.
exists q1; split; [ apply bSUM1; assumption | intro; apply REF ].
exists q1; split; [ apply bSUM2; apply bSUM1; assumption | intro; apply REF ].
exists q1; split; [ apply bSUM2; apply bSUM2; assumption | intro; apply REF ].

inversion_clear H.
exists p1; split;
 [ apply bSUM1; apply bSUM1; assumption | intros; apply REF ].
inversion_clear H0.
exists p1; split;
 [ apply bSUM1; apply bSUM2; assumption | intros; apply REF ].
exists p1; split; [ apply bSUM2; assumption | intros; apply REF ].

inversion_clear H.
inversion_clear H0.
exists q1; split; [ apply bSUM1; assumption | intros; apply REF ].
exists q1; split;
 [ apply bSUM2; apply bSUM1; assumption | intros; apply REF ].
exists q1; split;
 [ apply bSUM2; apply bSUM2; assumption | intros; apply REF ].

Qed.

(* End monoidal_sum. *)

(* Section bang_unfolding. *)

Lemma BANG_UNF : forall p : proc, StBisim (bang p) (par p (bang p)).

Proof. (* This lemma depends on Lemma REF. *)

intro; apply sb; do 3 try (split; intros).
exists p1; split; [ inversion_clear H; assumption | apply REF ].
exists q1; split; [ apply fBANG; assumption | apply REF ].
exists p1; split; [ inversion_clear H; assumption | intro; apply REF ].
exists q1; split; [ apply bBANG; assumption | intro; apply REF ].
exists p1; split; [ inversion_clear H; assumption | intros; apply REF ].
exists q1; split; [ apply bBANG; assumption | intros; apply REF ].

Qed.

(* End bang_unfolding. *)

(* Section restriction_laws1. *)

Lemma NU_NIL : StBisim (nu (fun x : name => nil)) nil.

Proof. (* This lemma is proved from scratch. *)

apply sb; do 3 try (split; intros).

generalize H; clear H; elim a; intros.

inversion_clear H.
elim (unsat (par (nu (fun _ : name => nil)) (nu p2)) l); intros.
inversion_clear H.
inversion_clear H1.
cut (ftrans nil tau (p2 x)); [ intro | apply H0; auto ].
inversion_clear H1.
apply f_act_notin_tau.

inversion_clear H.
elim (unsat (par (nu (fun _ : name => nil)) (nu p2)) (cons n (cons n0 l)));
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H4.
cut (ftrans nil (Out n n0) (p2 x)); [ intro | apply H0; auto ].
inversion_clear H4.
apply f_act_notin_Out; auto.

inversion_clear H.

inversion_clear H.
elim
 (unsat (par (nu (fun _ : name => nil)) (nu (fun z : name => nu (p2 z))))
    (cons x l)); intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans nil (In x) (p2 x0)); [ intro | apply H0; auto ].
inversion_clear H2.
apply b_act_notin_In; auto.

inversion_clear H.

inversion_clear H.
elim
 (unsat (par (nu (fun _ : name => nil)) (nu (fun z : name => nu (p2 z))))
    (cons x l)); intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans nil (bOut x) (p2 x0)); [ intro | apply H0; auto ].
inversion_clear H2.
apply b_act_notin_bOut; auto.

elim (unsat (par (nu (fun _ : name => nil)) (nu p1)) (cons x l)); intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (ftrans nil (Out x x0) (p1 x0)); [ intro | apply H0; auto ].
inversion_clear H2.

inversion_clear H.

Qed.

Lemma NU_NIL1 :
 forall (p : proc) (x : name),
 StBisim (nu (fun y : name => out_pref y x p)) nil.

Proof. (* This lemma is proved from scratch. *)

intros; apply sb; do 3 try (split; intros).
generalize H; clear H; elim a; intros.
inversion_clear H.
elim (unsat (par (nu (fun y0 : name => out_pref y0 x p)) (nu p2)) l); intros.
inversion_clear H.
inversion_clear H1.
cut (ftrans (out_pref x0 x p) tau (p2 x0)); [ intro | apply H0; auto ].
inversion_clear H1.
apply f_act_notin_tau.
inversion_clear H.
elim
 (unsat (par (nu (fun y0 : name => out_pref y0 x p)) (nu p2))
    (cons n (cons n0 l))); intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H4.
cut (ftrans (out_pref x0 x p) (Out n n0) (p2 x0)); [ intro | apply H0; auto ].
inversion H4.
absurd (x0 = n); auto.
apply f_act_notin_Out; auto.
inversion_clear H.

inversion_clear H.
elim
 (unsat
    (par (nu (fun y0 : name => out_pref y0 x p))
       (nu (fun z : name => nu (p2 z)))) (cons x0 l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (out_pref x1 x p) (In x0) (p2 x1)); [ intro | apply H0; auto ].
inversion_clear H2.
apply b_act_notin_In; auto.
inversion_clear H.

inversion_clear H.
elim
 (unsat
    (par (nu (fun y0 : name => out_pref y0 x p))
       (nu (fun z : name => nu (p2 z)))) (cons x0 l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (out_pref x1 x p) (bOut x0) (p2 x1)); [ intro | apply H0; auto ].
inversion_clear H2.
apply b_act_notin_bOut; auto.
elim
 (unsat (par (nu (fun y0 : name => out_pref y0 x p)) (nu p1)) (cons x0 l));
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (ftrans (out_pref x1 x p) (Out x0 x1) (p1 x1));
 [ intro | apply H0; auto ].
inversion H2.
absurd (x1 = x0); auto.
inversion_clear H.

Qed.

Lemma NU_NIL2 :
 forall p : name -> proc, StBisim (nu (fun y : name => in_pref y p)) nil.

Proof. (* This lemma is proved from scratch. *)

intros; apply sb; do 3 try (split; intros).
generalize H; clear H; elim a; intros.
inversion_clear H.
elim (unsat (par (nu (fun y0 : name => in_pref y0 p)) (nu p2)) l); intros.
inversion_clear H.
inversion_clear H1.
cut (ftrans (in_pref x p) tau (p2 x)); [ intro | apply H0; auto ].
inversion_clear H1.
apply f_act_notin_tau.
inversion_clear H.
elim
 (unsat (par (nu (fun y0 : name => in_pref y0 p)) (nu p2))
    (cons n (cons n0 l))); intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H4.
cut (ftrans (in_pref x p) (Out n n0) (p2 x)); [ intro | apply H0; auto ].
inversion H4.
apply f_act_notin_Out; auto.
inversion_clear H.

inversion_clear H.
elim
 (unsat
    (par (nu (fun y0 : name => in_pref y0 p))
       (nu (fun z : name => nu (p2 z)))) (cons x l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (in_pref x0 p) (In x) (p2 x0)); [ intro | apply H0; auto ].
inversion H2.
absurd (x0 = x); auto.
apply b_act_notin_In; auto.
inversion_clear H.

inversion_clear H.
elim
 (unsat
    (par (nu (fun y0 : name => in_pref y0 p))
       (nu (fun z : name => nu (p2 z)))) (cons x l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (in_pref x0 p) (bOut x) (p2 x0)); [ intro | apply H0; auto ].
inversion_clear H2.
apply b_act_notin_bOut; auto.
elim (unsat (par (nu (fun y0 : name => in_pref y0 p)) (nu p1)) (cons x l));
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (ftrans (in_pref x0 p) (Out x x0) (p1 x0)); [ intro | apply H0; auto ].
inversion_clear H2.
inversion_clear H.

Qed.

Lemma NU_COMM :
 forall p : name -> name -> proc,
 StBisim (nu (fun y : name => nu (fun z : name => p y z)))
   (nu (fun z : name => nu (fun y : name => p y z))).

Proof. (* This lemma depends on Lemmata FTR_L3, BTR_L3:
        * it is a coinductive proof.
        *)

cofix; intro; apply sb; do 3 try (split; intros).
generalize H; clear H; elim a; intros.

(* TAU action case *)

inversion_clear H.
elim
 (unsat (par (nu (fun y0 : name => nu (fun z : name => p y0 z))) (nu p2)) l);
 intros.
inversion_clear H.
inversion_clear H1.
cut (ftrans (nu (fun z : name => p x z)) tau (p2 x));
 [ intro | apply H0; auto ].
inversion H1.
elim (unsat (par (nu (fun z : name => p x z)) (nu p3)) l0); intros.
inversion_clear H8.
inversion_clear H9.
cut (ftrans (p x x0) tau (p3 x0)); [ intro | apply H7; auto ].
elim (ho_proc_exp p3 x); intros.
inversion_clear H12.
exists (nu (fun z : name => nu (fun y : name => x1 y z))); split.
apply fRES with (cons x (cons x0 empty)); intros.
inversion_clear H16.
inversion_clear H19.
clear H17 H20.
apply fRES with (cons x (cons x0 empty)); intros.
inversion_clear H20.
inversion_clear H23.
clear H21 H24.
change
  (ftrans ((fun n : name => p n y) y0) ((fun _ : name => tau) y0)
     ((fun n : name => x1 n y) y0)) in |- *; apply FTR_L3 with x; 
 auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H23; auto.
inversion_clear H13; apply notin_nu; intros.
cut (notin x (nu (x1 z))); [ intro | auto ].
inversion_clear H23; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
change (ftrans (p x y) ((fun _ : name => tau) y) (x1 x y)) in |- *;
 apply FTR_L3 with x0; auto.
rewrite <- H14; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
rewrite <- H14; assumption.
inversion_clear H12; apply notin_nu; intros.
cut (notin y (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H23; auto.
inversion_clear H15; apply notin_nu; intros.
cut (notin y (nu (fun y0 : name => x1 y0 z))); [ intro | auto ].
inversion_clear H23; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
rewrite H14 in H5; cut (p2 = (fun n : name => nu (x1 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H12;
 cut
  (nu (fun n : name => nu (x1 n)) =
   nu (fun n : name => nu (fun u : name => x1 n u)));
 [ intro | apply ETA_EQ2 ].
rewrite H15; apply NU_COMM.
apply f_act_notin_tau.
apply f_act_notin_tau.

(* OUT action case *)

inversion_clear H.
elim
 (unsat (par (nu (fun y0 : name => nu (fun z : name => p y0 z))) (nu p2))
    (cons n (cons n0 l))); intros.
inversion_clear H.
inversion_clear H1; inversion_clear H2.
inversion_clear H4.
cut (ftrans (nu (fun z : name => p x z)) (Out n n0) (p2 x));
 [ intro | apply H0; auto ].
inversion H4.
elim (unsat (par (nu (fun z : name => p x z)) (nu p3)) (cons n (cons n0 l0)));
 intros.
inversion_clear H10.
inversion_clear H11; inversion_clear H12.
inversion_clear H14.
cut (ftrans (p x x0) (Out n n0) (p3 x0)); [ intro | apply H9; auto ].
elim (ho_proc_exp p3 x); intros.
inversion_clear H16.
exists (nu (fun z : name => nu (fun y : name => x1 y z))); split.
apply fRES with (cons x (cons x0 empty)); intros.
inversion_clear H20; inversion_clear H21.
inversion_clear H23.
clear H25.
apply fRES with (cons x (cons x0 empty)); intros.
inversion_clear H26; inversion_clear H27.
inversion_clear H29.
clear H31.
change
  (ftrans ((fun n : name => p n y) y0) ((fun _ : name => Out n n0) y0)
     ((fun n : name => x1 n y) y0)) in |- *; apply FTR_L3 with x; 
 auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H31; auto.
inversion_clear H17; apply notin_nu; intros.
cut (notin x (nu (x1 z))); [ intro | auto ].
inversion_clear H31; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
change (ftrans (p x y) ((fun _ : name => Out n n0) y) (x1 x y)) in |- *;
 apply FTR_L3 with x0; auto.
rewrite <- H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite <- H18; assumption.
inversion_clear H16; apply notin_nu; intros.
cut (notin y (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H31; auto.
inversion_clear H19; apply notin_nu; intros.
cut (notin y (nu (fun y0 : name => x1 y0 z))); [ intro | auto ].
inversion_clear H31; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H18 in H7; cut (p2 = (fun n : name => nu (x1 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H16;
 cut
  (nu (fun n : name => nu (x1 n)) =
   nu (fun n : name => nu (fun u : name => x1 n u)));
 [ intro | apply ETA_EQ2 ].
rewrite H19; apply NU_COMM.
apply f_act_notin_Out; auto.
apply f_act_notin_Out; auto.

(* The way back: symmetric case *)

generalize H; clear H; elim a; intros.

(* TAU action case *)

inversion_clear H.
elim
 (unsat (par (nu (fun z : name => nu (fun y0 : name => p y0 z))) (nu p2)) l);
 intros.
inversion_clear H.
inversion_clear H1.
cut (ftrans (nu (fun y0 : name => p y0 x)) tau (p2 x));
 [ intro | apply H0; auto ].
inversion H1.
elim (unsat (par (nu (fun y0 : name => p y0 x)) (nu p0)) l0); intros.
inversion_clear H8.
inversion_clear H9.
cut (ftrans (p x0 x) tau (p0 x0)); [ intro | apply H7; auto ].
elim (ho_proc_exp p0 x); intros.
inversion_clear H12.
exists (nu (fun y : name => nu (fun z : name => x1 z y))); split.
apply fRES with (cons x (cons x0 empty)); intros.
inversion_clear H16.
inversion_clear H19.
clear H17 H20.
apply fRES with (cons x (cons x0 empty)); intros.
inversion_clear H20.
inversion_clear H23.
clear H21 H24.
change
  (ftrans (p y y0) ((fun _ : name => tau) y0) ((fun n : name => x1 n y) y0))
 in |- *; apply FTR_L3 with x; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H23; auto.
inversion_clear H13; apply notin_nu; intros.
cut (notin x (nu (x1 z))); [ intro | auto ].
inversion_clear H23; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
change
  (ftrans ((fun n : name => p n x) y) ((fun _ : name => tau) y) (x1 x y))
 in |- *; apply FTR_L3 with x0; auto.
rewrite <- H14; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
rewrite <- H14; assumption.
inversion_clear H12; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H23; auto.
inversion_clear H15; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => x1 z0 z))); [ intro | auto ].
inversion_clear H23; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
rewrite H14 in H5; cut (p2 = (fun n : name => nu (x1 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H12;
 cut
  (nu (fun n : name => nu (x1 n)) =
   nu (fun n : name => nu (fun u : name => x1 n u)));
 [ intro | apply ETA_EQ2 ].
rewrite H15;
 change
   (StBisim
      (nu
         (fun y : name => nu (fun z : name => (fun u v : name => x1 v u) y z)))
      (nu
         (fun n : name =>
          nu (fun u : name => (fun u' v : name => x1 v u') u n)))) 
  in |- *; apply NU_COMM.
apply f_act_notin_tau.
apply f_act_notin_tau.

(* OUT action case *)

inversion_clear H.
elim
 (unsat (par (nu (fun z : name => nu (fun y0 : name => p y0 z))) (nu p2))
    (cons n (cons n0 l))); intros.
inversion_clear H.
inversion_clear H1; inversion_clear H2.
inversion_clear H4.
cut (ftrans (nu (fun y0 : name => p y0 x)) (Out n n0) (p2 x));
 [ intro | apply H0; auto ].
inversion H4.
elim
 (unsat (par (nu (fun y0 : name => p y0 x)) (nu p0)) (cons n (cons n0 l0)));
 intros.
inversion_clear H10.
inversion_clear H11; inversion_clear H12.
inversion_clear H14.
cut (ftrans (p x0 x) (Out n n0) (p0 x0)); [ intro | apply H9; auto ].
elim (ho_proc_exp p0 x); intros.
inversion_clear H16.
exists (nu (fun y : name => nu (fun z : name => x1 z y))); split.
apply fRES with (cons x (cons x0 empty)); intros.
inversion_clear H20; inversion_clear H21.
inversion_clear H23.
clear H25; apply fRES with (cons x (cons x0 empty)); intros.
inversion_clear H26; inversion_clear H27.
inversion_clear H29.
clear H31;
 change
   (ftrans (p y y0) ((fun _ : name => Out n n0) y0)
      ((fun n : name => x1 n y) y0)) in |- *; apply FTR_L3 with x; 
 auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x (nu (fun z0 : name => p z0 z))); [ intro | auto ].
inversion_clear H31; auto.
inversion_clear H17; apply notin_nu; intros.
cut (notin x (nu (x1 z))); [ intro | auto ].
inversion_clear H31; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
change
  (ftrans ((fun n : name => p n x) y) ((fun _ : name => Out n n0) y) (x1 x y))
 in |- *; apply FTR_L3 with x0; auto.
rewrite <- H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite <- H18; assumption.
inversion_clear H16; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H31; auto.
inversion_clear H19; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => x1 z0 z))); [ intro | auto ].
inversion_clear H31; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H18 in H7; cut (p2 = (fun n : name => nu (x1 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H16;
 cut
  (nu (fun n : name => nu (x1 n)) =
   nu (fun n : name => nu (fun u : name => x1 n u)));
 [ intro | apply ETA_EQ2 ].
rewrite H19;
 change
   (StBisim
      (nu
         (fun y : name => nu (fun z : name => (fun u v : name => x1 v u) y z)))
      (nu
         (fun n : name =>
          nu (fun u : name => (fun u' v : name => x1 v u') u n)))) 
  in |- *; apply NU_COMM.
apply f_act_notin_Out; auto.
apply f_act_notin_Out; auto.

(* INPUT action case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun y0 : name => nu (fun z : name => p y0 z)))
       (nu (fun z : name => nu (p2 z)))) (cons x l)); 
 intros.
inversion_clear H.
inversion_clear H1; inversion_clear H2.
cut (btrans (nu (fun z : name => p x0 z)) (In x) (p2 x0));
 [ intro | apply H0; auto ].
inversion H2.
elim
 (unsat (par (nu (fun z : name => p x0 z)) (nu (fun z : name => nu (p3 z))))
    (cons x l0)); intros.
inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (btrans (p x0 x1) (In x) (p3 x1)); [ intro | apply H8; auto ].
elim (ho2_proc_exp p3 x0); intros.
inversion_clear H14.
exists (fun n : name => nu (fun z : name => nu (fun y : name => x2 y z n)));
 split.
change
  (btrans (nu (fun z : name => nu (fun y : name => p y z))) 
     (In x)
     (fun n : name =>
      nu
        (fun z : name =>
         (fun u v : name => nu (fun y : name => x2 y u v)) z n))) 
 in |- *; apply bRES with (cons x0 (cons x1 empty)); 
 intros.
inversion_clear H18; inversion_clear H19.
inversion_clear H21.
clear H22;
 change
   (btrans (nu (fun y0 : name => p y0 y)) (In x)
      (fun v : name => nu (fun y0 : name => (fun n : name => x2 n y) y0 v)))
  in |- *; apply bRES with (cons x (cons x0 empty)); 
 intros.
inversion_clear H23; inversion_clear H24.
inversion_clear H26.
clear H27;
 change
   (btrans ((fun n : name => p n y) y0) ((fun _ : name => In x) y0)
      ((fun n : name => x2 n y) y0)) in |- *; apply BTR_L3 with x0; 
 auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H15; apply notin_nu; intros.
cut (notin x0 (nu (fun z0 : name => nu (x2 z z0)))); [ intro | auto ].
inversion_clear H27; apply notin_nu; intros.
cut (notin x0 (nu (x2 z y))); [ intro | auto ].
inversion_clear H29; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
change (btrans (p x0 y) ((fun _ : name => In x) y) (x2 x0 y)) in |- *;
 apply BTR_L3 with x1; auto.
rewrite <- H16; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite <- H16; assumption.
inversion_clear H14; apply notin_nu; intros;
 cut (notin y (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H17; apply notin_nu; intros.
cut (notin y (nu (fun v : name => nu (fun y0 : name => x2 y0 z v))));
 [ intro | auto ].
inversion_clear H27; apply notin_nu; intros.
cut (notin y (nu (fun y0 : name => x2 y0 z z0))); [ intro | auto ].
inversion_clear H29; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H16 in H6;
 cut ((fun n y : name => nu (fun z : name => x2 n z y)) = p2);
 [ intro | apply ho_proc_ext with x0; auto ].
rewrite <- H14; intro;
 change
   (StBisim
      (nu
         (fun z : name =>
          nu (fun z0 : name => (fun u v : name => x2 u v y) z z0)))
      (nu
         (fun z : name =>
          nu (fun y0 : name => (fun u v : name => x2 u v y) y0 z)))) 
  in |- *; apply NU_COMM.
inversion_clear H15; do 3 (apply notin_nu; intros).
cut (notin x0 (nu (fun z0 : name => nu (x2 z z0)))); [ intro | auto ].
inversion_clear H19.
cut (notin x0 (nu (x2 z z1))); [ intro | auto ].
inversion_clear H19; auto.
apply b_act_notin_In; auto.
apply b_act_notin_In; auto.

(* The way back: symmetric case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun z : name => nu (fun y0 : name => p y0 z)))
       (nu (fun z : name => nu (p2 z)))) (cons x l)); 
 intros.
inversion_clear H.
inversion_clear H1; inversion_clear H2.
cut (btrans (nu (fun y0 : name => p y0 x0)) (In x) (p2 x0));
 [ intro | apply H0; auto ].
inversion H2.
elim
 (unsat
    (par (nu (fun y0 : name => p y0 x0)) (nu (fun z : name => nu (p0 z))))
    (cons x l0)); intros.
inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (btrans (p x1 x0) (In x) (p0 x1)); [ intro | apply H8; auto ].
elim (ho2_proc_exp p0 x0); intros.
inversion_clear H14;
 exists (fun n : name => nu (fun z : name => nu (fun y : name => x2 y z n)));
 split.
change
  (btrans (nu (fun z : name => nu (fun y : name => p z y))) 
     (In x)
     (fun n : name =>
      nu
        (fun z : name =>
         (fun u v : name => nu (fun y : name => x2 y u v)) z n))) 
 in |- *; apply bRES with (cons x0 (cons x1 empty)); 
 intros.
inversion_clear H18; inversion_clear H19.
inversion_clear H21.
clear H22;
 change
   (btrans (nu (fun y0 : name => p y y0)) (In x)
      (fun v : name => nu (fun y0 : name => (fun n : name => x2 n y) y0 v)))
  in |- *; apply bRES with (cons x (cons x0 empty)); 
 intros.
inversion_clear H23; inversion_clear H24.
inversion_clear H26.
clear H27;
 change
   (btrans (p y y0) ((fun _ : name => In x) y0) ((fun n : name => x2 n y) y0))
  in |- *; apply BTR_L3 with x0; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H15; apply notin_nu; intros.
cut (notin x0 (nu (fun z0 : name => nu (x2 z z0)))); [ intro | auto ].
inversion_clear H27; apply notin_nu; intros.
cut (notin x0 (nu (x2 z y))); [ intro | auto ].
inversion_clear H29; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
change
  (btrans ((fun n : name => p n x0) y) ((fun _ : name => In x) y) (x2 x0 y))
 in |- *; apply BTR_L3 with x1; auto.
rewrite <- H16; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite <- H16; assumption.
inversion_clear H14; apply notin_nu; intros;
 cut (notin y (nu (fun y0 : name => p z y0))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H17; apply notin_nu; intros.
cut (notin y (nu (fun v : name => nu (fun y0 : name => x2 y0 z v))));
 [ intro | auto ].
inversion_clear H27; apply notin_nu; intros.
cut (notin y (nu (fun y0 : name => x2 y0 z z0))); [ intro | auto ].
inversion_clear H29; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H16 in H6;
 cut (p2 = (fun n y : name => nu (fun z : name => x2 n z y)));
 [ intro | apply ho_proc_ext with x0; auto ].
rewrite H14; intro;
 change
   (StBisim
      (nu
         (fun z : name =>
          nu (fun y0 : name => (fun u v : name => x2 v u y) z y0)))
      (nu
         (fun z : name =>
          nu (fun z0 : name => (fun u v : name => x2 v u y) z0 z)))) 
  in |- *; apply NU_COMM.
inversion_clear H15; do 3 (apply notin_nu; intros).
cut (notin x0 (nu (fun z0 : name => nu (x2 z z0)))); [ intro | auto ].
inversion_clear H19.
cut (notin x0 (nu (x2 z z1))); [ intro | auto ].
inversion_clear H19; auto.
apply b_act_notin_In; auto.
apply b_act_notin_In; auto.

(* BOUND OUTPUT action case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun y0 : name => nu (fun z : name => p y0 z)))
       (nu (fun z : name => nu (p2 z)))) (cons x l)); 
 intros.
inversion_clear H.
inversion_clear H1; inversion_clear H2.
cut (btrans (nu (fun z : name => p x0 z)) (bOut x) (p2 x0));
 [ intro | apply H0; auto ].
inversion H2.
elim
 (unsat (par (nu (fun z : name => p x0 z)) (nu (fun z : name => nu (p3 z))))
    (cons x l0)); intros.
inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (btrans (p x0 x1) (bOut x) (p3 x1)); [ intro | apply H8; auto ].
elim (ho2_proc_exp p3 x0); intros.
inversion_clear H14;
 exists (fun n : name => nu (fun z : name => nu (fun y : name => x2 y z n)));
 split.
change
  (btrans (nu (fun z : name => nu (fun y : name => p y z))) 
     (bOut x)
     (fun n : name =>
      nu
        (fun z : name =>
         (fun u v : name => nu (fun y : name => x2 y u v)) z n))) 
 in |- *; apply bRES with (cons x0 (cons x1 empty)); 
 intros.
inversion_clear H18; inversion_clear H19.
inversion_clear H21.
clear H22;
 change
   (btrans (nu (fun y0 : name => p y0 y)) (bOut x)
      (fun v : name => nu (fun y0 : name => (fun n : name => x2 n y) y0 v)))
  in |- *; apply bRES with (cons x (cons x0 empty)); 
 intros.
inversion_clear H23.
inversion_clear H24.
inversion_clear H26.
clear H27;
 change
   (btrans ((fun n : name => p n y) y0) ((fun _ : name => bOut x) y0)
      ((fun n : name => x2 n y) y0)) in |- *; apply BTR_L3 with x0; 
 auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H15; apply notin_nu; intros.
cut (notin x0 (nu (fun z0 : name => nu (x2 z z0)))); [ intro | auto ].
inversion_clear H27; apply notin_nu; intros.
cut (notin x0 (nu (x2 z y))); [ intro | auto ].
inversion_clear H29; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
change (btrans (p x0 y) ((fun _ : name => bOut x) y) (x2 x0 y)) in |- *;
 apply BTR_L3 with x1; auto.
rewrite <- H16; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
rewrite <- H16; assumption.
inversion_clear H14; apply notin_nu; intros;
 cut (notin y (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H17; apply notin_nu; intros.
cut (notin y (nu (fun v : name => nu (fun y0 : name => x2 y0 z v))));
 [ intro | auto ].
inversion_clear H27; apply notin_nu; intros.
cut (notin y (nu (fun y0 : name => x2 y0 z z0))); [ intro | auto ].
inversion_clear H29; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
rewrite H16 in H6;
 cut (p2 = (fun n y : name => nu (fun z : name => x2 n z y)));
 [ intro | apply ho_proc_ext with x0; auto ].
rewrite H14; intros;
 change
   (StBisim
      (nu
         (fun z : name =>
          nu (fun z0 : name => (fun u v : name => x2 u v y) z z0)))
      (nu
         (fun z : name =>
          nu (fun y0 : name => (fun u v : name => x2 u v y) y0 z)))) 
  in |- *; apply NU_COMM.
inversion_clear H15; do 3 (apply notin_nu; intros).
cut (notin x0 (nu (fun z0 : name => nu (x2 z z0)))); [ intro | auto ].
inversion_clear H19.
cut (notin x0 (nu (x2 z z1))); [ intro | auto ].
inversion_clear H19; auto.
apply b_act_notin_bOut; auto.

elim (unsat (par (nu (fun z : name => p x0 z)) (nu (p2 x0))) (cons x l0));
 intros.
inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (ftrans (p x0 x2) (Out x x2) (p2 x0 x2)); [ intro | apply H7; auto ].
exists (fun n : name => nu (fun z : name => p2 z n)); split.
apply OPEN with (cons x (cons x0 empty)); intros.
inversion_clear H17.
inversion_clear H19.
clear H20; apply fRES with (cons x0 (cons x1 empty)); intros.
inversion_clear H21; inversion_clear H22.
inversion_clear H24.
clear H26;
 change
   (ftrans ((fun n : name => p n y) y0) ((fun _ : name => Out x y) y0)
      ((fun n : name => p2 n y) y0)) in |- *; apply FTR_L3 with x0; 
 auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H26; auto.
inversion_clear H3; apply notin_nu; intros.
cut (notin x0 (nu (p2 z))); [ intro | auto ].
inversion_clear H26; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
change (ftrans (p x0 y) (Out x y) (p2 x0 y)) in |- *; apply FTR_L3 with x2;
 auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
inversion_clear H14; apply notin_nu; intros;
 cut (notin y (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H26; auto.
inversion_clear H15; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => p2 z0 z))); [ intro | auto ].
inversion_clear H26; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
intros; apply REF.
apply b_act_notin_bOut; auto.

elim
 (unsat (par (nu (fun y0 : name => nu (fun z : name => p y0 z))) (nu p1))
    (cons x l)); intros.
inversion_clear H.
inversion_clear H1; inversion_clear H2.
cut (ftrans (nu (fun z : name => p x0 z)) (Out x x0) (p1 x0));
 [ intro | apply H0; auto ].
inversion H2.
elim
 (unsat (par (nu (fun z : name => p x0 z)) (nu p2)) (cons x (cons x0 l0)));
 intros.
inversion_clear H9.
inversion_clear H10; inversion_clear H11.
inversion_clear H13.
cut (ftrans (p x0 x1) (Out x x0) (p2 x1)); [ intro | apply H8; auto ].
elim (ho_proc_exp p2 x0); intros.
inversion_clear H15; exists (fun y : name => nu (fun z : name => x2 y z));
 split.
change
  (btrans (nu (fun z : name => nu (fun y : name => p y z))) 
     (bOut x)
     (fun y : name => nu (fun z : name => (fun u n : name => x2 n u) z y)))
 in |- *; apply bRES with (cons x0 (cons x1 empty)); 
 intros.
inversion_clear H19; inversion_clear H20.
inversion_clear H22.
clear H23; apply OPEN with (cons x0 empty); intros.
inversion_clear H25.
clear H27;
 change
   (ftrans ((fun n : name => p n y) y0) (Out x y0)
      ((fun n : name => x2 n y) y0)) in |- *; apply FTR_L3 with x0; 
 auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H16; apply notin_nu; intros.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H27; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
change (ftrans (p x0 y) ((fun _ : name => Out x x0) y) (x2 x0 y)) in |- *;
 apply FTR_L3 with x1; auto.
rewrite <- H17; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite <- H17; assumption.
inversion_clear H15; apply notin_nu; intros;
 cut (notin y (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H18; apply notin_nu; intros.
cut (notin y (nu (fun n : name => x2 n z))); [ intro | auto ].
inversion_clear H27; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H17 in H6; cut (p1 = (fun n : name => nu (x2 n)));
 [ intro | apply proc_ext with x0; auto ].
rewrite H15; intros; cut (nu (x2 y) = nu (fun n : name => x2 y n));
 [ intro | apply ETA_EQ ]; rewrite H20; apply REF.
apply f_act_notin_Out; auto.

(* The way back: symmetric case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun z : name => nu (fun y0 : name => p y0 z)))
       (nu (fun z : name => nu (p2 z)))) (cons x l)); 
 intros.
inversion_clear H.
inversion_clear H1; inversion_clear H2.
cut (btrans (nu (fun y0 : name => p y0 x0)) (bOut x) (p2 x0));
 [ intro | apply H0; auto ].
inversion H2.
elim
 (unsat
    (par (nu (fun y0 : name => p y0 x0)) (nu (fun z : name => nu (p0 z))))
    (cons x l0)); intros.
inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (btrans (p x1 x0) (bOut x) (p0 x1)); [ intro | apply H8; auto ].
elim (ho2_proc_exp p0 x0); intros.
inversion_clear H14;
 exists (fun n : name => nu (fun z : name => nu (fun y : name => x2 y z n)));
 split.
change
  (btrans (nu (fun y : name => nu (fun z : name => p y z))) 
     (bOut x)
     (fun n : name =>
      nu
        (fun z : name =>
         (fun u v : name => nu (fun y : name => x2 y u v)) z n))) 
 in |- *; apply bRES with (cons x0 (cons x1 empty)); 
 intros.
inversion_clear H18; inversion_clear H19.
inversion_clear H21.
clear H22;
 change
   (btrans (nu (fun z : name => p y z)) (bOut x)
      (fun v : name => nu (fun y0 : name => (fun n : name => x2 n y) y0 v)))
  in |- *; apply bRES with (cons x (cons x0 empty)); 
 intros.
inversion_clear H23; inversion_clear H24.
inversion_clear H26.
clear H27;
 change
   (btrans (p y y0) ((fun _ : name => bOut x) y0)
      ((fun n : name => x2 n y) y0)) in |- *; apply BTR_L3 with x0; 
 auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H15; apply notin_nu; intros.
cut (notin x0 (nu (fun z0 : name => nu (x2 z z0)))); [ intro | auto ].
inversion_clear H27; apply notin_nu; intros.
cut (notin x0 (nu (x2 z y))); [ intro | auto ].
inversion_clear H29; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
change
  (btrans ((fun n : name => p n x0) y) ((fun _ : name => bOut x) y) (x2 x0 y))
 in |- *; apply BTR_L3 with x1; auto.
rewrite <- H16; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
rewrite <- H16; assumption.
inversion_clear H14; apply notin_nu; intros;
 cut (notin y (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H17; apply notin_nu; intros.
cut (notin y (nu (fun v : name => nu (fun y0 : name => x2 y0 z v))));
 [ intro | auto ].
inversion_clear H27; apply notin_nu; intros.
cut (notin y (nu (fun y0 : name => x2 y0 z z0))); [ intro | auto ].
inversion_clear H29; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
rewrite H16 in H6;
 cut (p2 = (fun n y : name => nu (fun z : name => x2 n z y)));
 [ intro | apply ho_proc_ext with x0; auto ].
rewrite H14; intros;
 change
   (StBisim
      (nu
         (fun z : name =>
          nu (fun y0 : name => (fun u v : name => x2 v u y) z y0)))
      (nu
         (fun y0 : name =>
          nu (fun z : name => (fun u v : name => x2 v u y) z y0)))) 
  in |- *; apply NU_COMM.
inversion_clear H15; do 3 (apply notin_nu; intros).
cut (notin x0 (nu (fun z0 : name => nu (x2 z z0)))); [ intro | auto ].
inversion_clear H19; cut (notin x0 (nu (x2 z z1))); [ intro | auto ].
inversion_clear H19; auto.
apply b_act_notin_bOut; auto.

elim (unsat (par (nu (fun y0 : name => p y0 x0)) (nu (p2 x0))) (cons x l0));
 intros.
inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (ftrans (p x2 x0) (Out x x2) (p2 x0 x2)); [ intro | apply H7; auto ].
exists (fun n : name => nu (fun z : name => p2 z n)); split.
apply OPEN with (cons x (cons x0 empty)); intros.
inversion_clear H17.
inversion_clear H19.
clear H20; apply fRES with (cons x0 (cons x1 empty)); intros.
inversion_clear H21; inversion_clear H22.
inversion_clear H24.
clear H26;
 change
   (ftrans (p y y0) ((fun n : name => Out x y) y0)
      ((fun n : name => p2 n y) y0)) in |- *; apply FTR_L3 with x0; 
 auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H26; auto.
inversion_clear H3; apply notin_nu; intros.
cut (notin x0 (nu (p2 z))); [ intro | auto ].
inversion_clear H26; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
change (ftrans ((fun n : name => p n x0) y) (Out x y) (p2 x0 y)) in |- *;
 apply FTR_L3 with x2; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
inversion_clear H14; apply notin_nu; intros;
 cut (notin y (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H26; auto.
inversion_clear H15; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => p2 z0 z))); [ intro | auto ].
inversion_clear H26; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
intros; apply REF.
apply b_act_notin_bOut; auto.

elim
 (unsat (par (nu (fun z : name => nu (fun y0 : name => p y0 z))) (nu q1))
    (cons x l)); intros.
inversion_clear H.
inversion_clear H1; inversion_clear H2.
cut (ftrans (nu (fun y0 : name => p y0 x0)) (Out x x0) (q1 x0));
 [ intro | apply H0; auto ].
inversion H2.
elim
 (unsat (par (nu (fun y0 : name => p y0 x0)) (nu p2)) (cons x (cons x0 l0)));
 intros.
inversion_clear H9.
inversion_clear H10; inversion_clear H11.
inversion_clear H13.
cut (ftrans (p x1 x0) (Out x x0) (p2 x1)); [ intro | apply H8; auto ].
elim (ho_proc_exp p2 x0); intros.
inversion_clear H15; exists (fun y : name => nu (fun z : name => x2 y z));
 split.
change
  (btrans (nu (fun y : name => nu (fun z : name => p y z))) 
     (bOut x)
     (fun y : name => nu (fun z : name => (fun u n : name => x2 n u) z y)))
 in |- *; apply bRES with (cons x0 (cons x1 empty)); 
 intros.
inversion_clear H19; inversion_clear H20.
inversion_clear H22.
clear H23; apply OPEN with (cons x0 empty); intros.
inversion_clear H25.
clear H27;
 change (ftrans (p y y0) (Out x y0) ((fun n : name => x2 n y) y0)) in |- *;
 apply FTR_L3 with x0; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (nu (fun y0 : name => p y0 z))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H16; apply notin_nu; intros.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H27; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
change
  (ftrans ((fun n : name => p n x0) y) ((fun _ : name => Out x x0) y)
     (x2 x0 y)) in |- *; apply FTR_L3 with x1; auto.
rewrite <- H17; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite <- H17; assumption.
inversion_clear H15; apply notin_nu; intros;
 cut (notin y (nu (fun z0 : name => p z z0))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H18; apply notin_nu; intros.
cut (notin y (nu (fun n : name => x2 n z))); [ intro | auto ].
inversion_clear H27; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H17 in H6; cut (q1 = (fun n : name => nu (x2 n)));
 [ intro | apply proc_ext with x0; auto ].
rewrite H15; intros; cut (nu (x2 y) = nu (fun n : name => x2 y n));
 [ intro | apply ETA_EQ ]; rewrite H20; apply REF.
apply f_act_notin_Out; auto.

Qed.

Lemma NU_SUM :
 forall p q : name -> proc,
 StBisim (nu (fun y : name => sum (p y) (q y))) (sum (nu p) (nu q)).

Proof. (* This lemma depends on Lemmata FTR_L3, BTR_L3, REF. *)

intros; apply sb; do 3 try (split; intros).

(* Free actions case *)

generalize H; clear H; elim a; intros.

inversion_clear H.
elim (unsat (par (nu (fun y0 : name => sum (p y0) (q y0))) (nu p2)) l);
 intros.
inversion_clear H.
inversion_clear H1.
cut (ftrans (sum (p x) (q x)) tau (p2 x)); [ intro | apply H0; auto ].
inversion_clear H1.
exists (nu p2); split.
apply fSUM1; apply fRES with l; intros.
change (ftrans (p y) ((fun _ : name => tau) y) (p2 y)) in |- *;
 apply FTR_L3 with x; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x (sum (p z) (q z))); [ intro | auto ].
inversion_clear H9; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply REF.
exists (nu p2); split.
apply fSUM2; apply fRES with l; intros.
change (ftrans (q y) ((fun _ : name => tau) y) (p2 y)) in |- *;
 apply FTR_L3 with x; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x (sum (p z) (q z))); [ intro | auto ].
inversion_clear H9; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply REF.
apply f_act_notin_tau.

inversion_clear H.
elim
 (unsat (par (nu (fun y0 : name => sum (p y0) (q y0))) (nu p2))
    (cons n (cons n0 l))); intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H4.
cut (ftrans (sum (p x) (q x)) (Out n n0) (p2 x)); [ intro | apply H0; auto ].
inversion_clear H4.
exists (nu p2); split.
apply fSUM1; apply fRES with l; intros.
inversion_clear H9.
change (ftrans (p y) ((fun _ : name => Out n n0) y) (p2 y)) in |- *;
 apply FTR_L3 with x; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x (sum (p z) (q z))); [ intro | auto ].
inversion_clear H12; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply REF.
exists (nu p2); split.
apply fSUM2; apply fRES with l; intros.
inversion_clear H9.
change (ftrans (q y) ((fun _ : name => Out n n0) y) (p2 y)) in |- *;
 apply FTR_L3 with x; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x (sum (p z) (q z))); [ intro | auto ].
inversion_clear H12; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply REF.
apply f_act_notin_Out; auto.

(* Symmetric case *)

generalize H; clear H; elim a; intros.

inversion_clear H.
exists q1; split.
inversion_clear H0.
apply fRES with l; intros.
clear H3; apply fSUM1; apply H; auto.
inversion_clear H0; apply notin_nu; intros.
cut (notin y (sum (p z) (q z))); [ intro | auto ].
inversion_clear H4; assumption.
apply f_act_notin_tau.
apply REF.
exists q1; split.
inversion_clear H0.
apply fRES with l; intros.
clear H3; apply fSUM2; apply H; auto.
inversion_clear H0; apply notin_nu; intros.
cut (notin y (sum (p z) (q z))); [ intro | auto ].
inversion_clear H4; assumption.
apply f_act_notin_tau.
apply REF.

inversion_clear H.
exists q1; split.
inversion_clear H0.
apply fRES with l; intros.
inversion_clear H3; apply fSUM1; apply H; auto.
inversion_clear H0; apply notin_nu; intros.
cut (notin y (sum (p z) (q z))); [ intro | auto ].
inversion_clear H6; assumption.
apply f_act_notin_Out; auto.
apply REF.
exists q1; split.
inversion_clear H0.
apply fRES with l; intros.
inversion_clear H3; apply fSUM2; apply H; auto.
inversion_clear H0; apply notin_nu; intros.
cut (notin y (sum (p z) (q z))); [ intro | auto ].
inversion_clear H6; assumption.
apply f_act_notin_Out; auto.
apply REF.

(* Input actions case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun y0 : name => sum (p y0) (q y0)))
       (nu (fun z : name => nu (p2 z)))) (cons x l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (sum (p x0) (q x0)) (In x) (p2 x0)); [ intro | apply H0; auto ].
inversion_clear H2.
exists (fun u : name => nu (fun v : name => p2 v u)); split.
apply bSUM1; apply bRES with l; intros.
inversion_clear H7.
change (btrans (p y) ((fun _ : name => In x) y) (p2 y)) in |- *;
 apply BTR_L3 with x0; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (sum (p z) (q z))); [ intro | auto ].
inversion_clear H10; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
intro; apply REF.

exists (fun u : name => nu (fun v : name => p2 v u)); split.
apply bSUM2; apply bRES with l; intros.
inversion_clear H7.
change (btrans (q y) ((fun _ : name => In x) y) (p2 y)) in |- *;
 apply BTR_L3 with x0; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (sum (p z) (q z))); [ intro | auto ].
inversion_clear H10; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
intro; apply REF.
apply b_act_notin_In; auto.

(* Symmetric case *)

inversion_clear H.
exists q1; split.
inversion_clear H0.
apply bRES with l; intros.
apply bSUM1; apply H; auto.
inversion_clear H0; apply notin_nu; intros.
cut (notin y (sum (p z) (q z))); [ intro | auto ].
inversion_clear H5; assumption.
intro; apply REF.
exists q1; split.
inversion_clear H0.
apply bRES with l; intros.
apply bSUM2; apply H; auto.
inversion_clear H0; apply notin_nu; intros.
cut (notin y (sum (p z) (q z))); [ intro | auto ].
inversion_clear H5; assumption.
intro; apply REF.

(* Bound output actions case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun y0 : name => sum (p y0) (q y0)))
       (nu (fun z : name => nu (p2 z)))) (cons x l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (sum (p x0) (q x0)) (bOut x) (p2 x0)); [ intro | apply H0; auto ].
inversion_clear H2.
exists (fun u : name => nu (fun v : name => p2 v u)); split.
apply bSUM1; apply bRES with l; intros.
inversion_clear H7.
change (btrans (p y) ((fun _ : name => bOut x) y) (p2 y)) in |- *;
 apply BTR_L3 with x0; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (sum (p z) (q z))); [ intro | auto ].
inversion_clear H10; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
intros; apply REF.

exists (fun u : name => nu (fun v : name => p2 v u)); split.
apply bSUM2; apply bRES with l; intros.
inversion_clear H7.
change (btrans (q y) ((fun _ : name => bOut x) y) (p2 y)) in |- *;
 apply BTR_L3 with x0; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (sum (p z) (q z))); [ intro | auto ].
inversion_clear H10; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
intros; apply REF.
apply b_act_notin_bOut; auto.

elim
 (unsat (par (nu (fun y0 : name => sum (p y0) (q y0))) (nu p1)) (cons x l));
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (ftrans (sum (p x0) (q x0)) (Out x x0) (p1 x0));
 [ intro | apply H0; auto ].
inversion_clear H2.
exists p1; split.
apply bSUM1; apply OPEN with l; intros.
change (ftrans (p y) (Out x y) (p1 y)) in |- *; apply FTR_L3 with x0; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (sum (p z) (q z))); [ intro | auto ].
inversion_clear H10; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
intros; apply REF.

exists p1; split.
apply bSUM2; apply OPEN with l; intros.
change (ftrans (q y) (Out x y) (p1 y)) in |- *; apply FTR_L3 with x0; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (sum (p z) (q z))); [ intro | auto ].
inversion_clear H10; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
intros; apply REF.

(* Symmetric case *)

inversion_clear H.
exists q1; split.
inversion_clear H0.
apply bRES with l; intros.
apply bSUM1; apply H; auto.
inversion_clear H0; apply notin_nu; intros.
cut (notin y (sum (p z) (q z))); [ intro | auto ].
inversion_clear H5; assumption.
apply OPEN with l; intros.
apply fSUM1; apply H; auto.
inversion_clear H0; apply notin_nu; intros.
cut (notin y (sum (p z) (q z))); [ intro | auto ].
inversion_clear H5; assumption.
intros; apply REF.
exists q1; split.
inversion_clear H0.
apply bRES with l; intros.
apply bSUM2; apply H; auto.
inversion_clear H0; apply notin_nu; intros.
cut (notin y (sum (p z) (q z))); [ intro | auto ].
inversion_clear H5; assumption.
apply OPEN with l; intros.
apply fSUM2; apply H; auto.
inversion_clear H0; apply notin_nu; intros.
cut (notin y (sum (p z) (q z))); [ intro | auto ].
inversion_clear H5; assumption.
intros; apply REF.

Qed.

Lemma NU_TAU_PREF :
 forall p : name -> proc,
 StBisim (nu (fun x : name => tau_pref (p x))) (tau_pref (nu p)).

Proof. (* This lemma depends on Lemmata REF, L6_Light, NU_S. *)

intros; apply sb; do 3 try (split; intros).

(* Free actions case *)

generalize H; clear H; elim a; intros.

inversion_clear H.
elim (unsat (par (nu (fun x : name => tau_pref (p x))) (nu p2)) l); intros.
inversion_clear H.
inversion_clear H1.
cut (ftrans (tau_pref (p x)) tau (p2 x)); [ intro | apply H0; auto ].
inversion H1.
exists (nu p); split.
apply TAU.
apply NU_S; intros.
apply L6_Light with x; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x (tau_pref (p z))); [ intro | auto ].
inversion_clear H9; assumption.
rewrite H4; apply REF.
apply f_act_notin_tau.

inversion_clear H.
elim
 (unsat (par (nu (fun x : name => tau_pref (p x))) (nu p2))
    (cons n (cons n0 l))); intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H4.
cut (ftrans (tau_pref (p x)) (Out n n0) (p2 x)); [ intro | apply H0; auto ].
inversion_clear H4.
apply f_act_notin_Out; auto.

(* Symmetric case *)

inversion H.
exists (nu p); split.
apply fRES with empty; intros.
clear H5 H6.
apply TAU.
apply REF.

(* Input actions case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun x0 : name => tau_pref (p x0)))
       (nu (fun z : name => nu (p2 z)))) (cons x l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (tau_pref (p x0)) (In x) (p2 x0)); [ intro | apply H0; auto ].
inversion_clear H2.
apply b_act_notin_In; auto.

inversion_clear H.

(* Bound output actions case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun x0 : name => tau_pref (p x0)))
       (nu (fun z : name => nu (p2 z)))) (cons x l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (tau_pref (p x0)) (bOut x) (p2 x0)); [ intro | apply H0; auto ].
inversion_clear H2.
apply b_act_notin_bOut; auto.

elim (unsat (par (nu (fun x0 : name => tau_pref (p x0))) (nu p1)) (cons x l));
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (ftrans (tau_pref (p x0)) (Out x x0) (p1 x0)); [ intro | apply H0; auto ].
inversion_clear H2.

inversion_clear H.

Qed.

Lemma NU_OUT_PREF :
 forall (p : name -> proc) (x y : name),
 StBisim (nu (fun z : name => out_pref x y (p z))) (out_pref x y (nu p)).

Proof. (* This lemma depends on Lemmata REF, L6_Light, NU_S. *)

intros; apply sb; do 3 try (split; intros).

(* Free actions case *)

generalize H; clear H; elim a; intros.

inversion_clear H.
elim (unsat (par (nu (fun z : name => out_pref x y (p z))) (nu p2)) l);
 intros.
inversion_clear H.
inversion_clear H1.
cut (ftrans (out_pref x y (p x0)) tau (p2 x0)); [ intro | apply H0; auto ].
inversion_clear H1.
apply f_act_notin_tau.

inversion_clear H.
elim
 (unsat (par (nu (fun z : name => out_pref x y (p z))) (nu p2))
    (cons n (cons n0 l))); intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H4.
cut (ftrans (out_pref x y (p x0)) (Out n n0) (p2 x0));
 [ intro | apply H0; auto ].
inversion H4.
exists (nu p); split.
apply OUT.
apply NU_S; intros.
apply L6_Light with x0; auto.
inversion_clear H; apply notin_nu; intros.
cut (notin x0 (out_pref x y (p z))); [ intro | auto ].
inversion_clear H15; assumption.
rewrite H12; apply REF.
apply f_act_notin_Out; auto.

inversion_clear H.
exists (nu p); split.
apply fRES with empty; intros; apply OUT.
apply REF.

(* Input actions case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun z : name => out_pref x y (p z)))
       (nu (fun z : name => nu (p2 z)))) (cons x0 l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (out_pref x y (p x1)) (In x0) (p2 x1));
 [ intro | apply H0; auto ].
inversion_clear H2.
apply b_act_notin_In; auto.

inversion_clear H.

(* Bound output actions case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun z : name => out_pref x y (p z)))
       (nu (fun z : name => nu (p2 z)))) (cons x0 l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (out_pref x y (p x1)) (bOut x0) (p2 x1));
 [ intro | apply H0; auto ].
inversion_clear H2.
apply b_act_notin_bOut; auto.

elim
 (unsat (par (nu (fun z : name => out_pref x y (p z))) (nu p1)) (cons x0 l));
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (ftrans (out_pref x y (p x1)) (Out x0 x1) (p1 x1));
 [ intro | apply H0; auto ].
inversion H2.
absurd (y = x1); auto.
inversion_clear H.
cut (notin x1 (out_pref x y (p x0))); [ intro | auto ].
inversion_clear H; auto.

inversion_clear H.

Qed.

Lemma NU_IN_PREF :
 forall (p : name -> name -> proc) (x : name),
 StBisim (nu (fun y : name => in_pref x (p y)))
   (in_pref x (fun z : name => nu (fun y : name => p y z))).

Proof. (* This lemma depends on Lemma REF. *)

intros; apply sb; do 3 try (split; intros).

(* Free actions case *)

generalize H; clear H; elim a; intros.

inversion_clear H.
elim (unsat (par (nu (fun y0 : name => in_pref x (p y0))) (nu p2)) l); intros.
inversion_clear H.
inversion_clear H1.
cut (ftrans (in_pref x (p x0)) tau (p2 x0)); [ intro | apply H0; auto ].
inversion_clear H1.
apply f_act_notin_tau.

inversion_clear H.
elim
 (unsat (par (nu (fun y0 : name => in_pref x (p y0))) (nu p2))
    (cons n (cons n0 l))); intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H4.
cut (ftrans (in_pref x (p x0)) (Out n n0) (p2 x0));
 [ intro | apply H0; auto ].
inversion_clear H4.
apply f_act_notin_Out; auto.

inversion_clear H.

(* Input actions case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun y0 : name => in_pref x (p y0)))
       (nu (fun z : name => nu (p2 z)))) (cons x0 l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (in_pref x (p x1)) (In x0) (p2 x1)); [ intro | apply H0; auto ].
inversion H2.
exists (fun z : name => nu (fun y : name => p y z)); split.
apply IN.
cut (p = p2); [ intro | apply ho_proc_ext with x1; auto ].
intro; rewrite <- H5; apply REF.
inversion_clear H; apply notin_nu; intros.
cut (notin x1 (in_pref x (p z))); [ intro | auto ]; apply notin_nu; intros.
inversion_clear H10; auto.
apply b_act_notin_In; auto.

inversion H.
exists (fun z : name => nu (fun y : name => p y z)); split.
apply bRES with empty; intros.
apply IN.
intro; apply REF.

(* Bound output actions case *)

inversion_clear H.
elim
 (unsat
    (par (nu (fun y0 : name => in_pref x (p y0)))
       (nu (fun z : name => nu (p2 z)))) (cons x0 l)); 
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (btrans (in_pref x (p x1)) (bOut x0) (p2 x1)); [ intro | apply H0; auto ].
inversion_clear H2.
apply b_act_notin_bOut; auto.

elim
 (unsat (par (nu (fun y0 : name => in_pref x (p y0))) (nu p1)) (cons x0 l));
 intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
cut (ftrans (in_pref x (p x1)) (Out x0 x1) (p1 x1));
 [ intro | apply H0; auto ].
inversion_clear H2.

inversion_clear H.

Qed.

(* End restriction_laws1. *)

(* Section parallel. *)

Lemma ID_PAR : forall p : proc, StBisim (par p nil) p.

Proof. (* This lemma is proved from scratch: it is a coinductive proof. *)

cofix; intro; apply sb; do 3 try (split; intros).

inversion_clear H.
exists p3; split; [ assumption | apply ID_PAR ].
inversion_clear H0.
inversion_clear H1.
inversion_clear H1.
inversion_clear H1.
inversion_clear H1.
exists (par q1 nil); split; [ apply fPAR1; assumption | apply ID_PAR ].

inversion_clear H.
exists p3; split; [ assumption | intro; apply ID_PAR ].
inversion_clear H0.
exists (fun n : name => par (q1 n) nil); split;
 [ apply bPAR1; assumption | intro; apply ID_PAR ].

inversion_clear H.
exists p3; split; [ assumption | intros; apply ID_PAR ].
inversion_clear H0.
exists (fun n : name => par (q1 n) nil); split;
 [ apply bPAR1; assumption | intros; apply ID_PAR ].

Qed.

(*******************************************************************)
(* Commutativity of parallel composition is proved by means of     *)
(* internal cross adequacy, i.e., building a suitable bisimulation *)
(* and applying the Completeness lemma.                            *)
(*******************************************************************)

(* The next four definitions allow to build the
 * strong late bisimulation needed to prove the
 * commutativity of parallel composition.
 *)

Inductive BisPAR_C : proc -> proc -> Prop :=
    bispar_c : forall p q : proc, BisPAR_C (par p q) (par q p).

Inductive Op_PAR_C (R : proc -> proc -> Prop) : proc -> proc -> Prop :=
    op_par_c :
      forall p q : name -> proc,
      (forall z : name, notin z (nu p) -> notin z (nu q) -> R (p z) (q z)) ->
      Op_PAR_C R (nu p) (nu q).

Fixpoint PAR_C_fun (n : nat) : proc -> proc -> Prop :=
  match n with
  | O => BisPAR_C
  | S m => Op_PAR_C (PAR_C_fun m)
  end.

Inductive SBPAR_C (p q : proc) : Prop :=
    sbpar_c : forall n : nat, PAR_C_fun n p q -> SBPAR_C p q.

(* Next we establish a property of PAR_C_fun
 * similar to that of L6_Light for StBisim.
 *)

Lemma PAR_C_RW :
 forall (n : nat) (p q : name -> proc) (x : name),
 notin x (nu p) ->
 notin x (nu q) ->
 PAR_C_fun n (p x) (q x) ->
 forall y : name, notin y (nu p) -> notin y (nu q) -> PAR_C_fun n (p y) (q y).

Proof.

intros; elim (LEM_name x y); intro.

rewrite <- H4; assumption.

generalize p q x H H0 y H4 H2 H3 H1; clear H H0 H2 H3 H4 y H1 x p q;
 induction  n as [| n Hrecn]; intros.

(* Base Case *)

simpl in H1; inversion H1; simpl in |- *.
elim (proc_exp p0 x); elim (proc_exp q0 x); intros.
inversion_clear H5; inversion_clear H8.
rewrite H10 in H6; rewrite H11 in H6; rewrite H10 in H7; rewrite H11 in H7;
 cut (p = (fun n : name => par (x1 n) (x0 n)));
 [ intro | apply proc_ext with x; auto ].
cut (q = (fun n : name => par (x0 n) (x1 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8; rewrite H12; apply bispar_c.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H9 | inversion_clear H5 ]; auto.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H5 | inversion_clear H9 ]; auto.

(* Inductive Step *)

simpl in H1; inversion H1; simpl in |- *.
elim (ho_proc_exp p0 x); elim (ho_proc_exp q0 x); intros.
inversion_clear H8; inversion_clear H9.
rewrite H12 in H5; rewrite H11 in H6.
cut (p = (fun n : name => nu (x1 n)));
 [ intro | apply proc_ext with x; auto ].
cut (q = (fun n : name => nu (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H9; rewrite H13; apply op_par_c; intros.
elim
 (unsat
    (par (nu p)
       (par (nu q)
          (par (nu (fun n : name => nu (x0 n)))
             (nu (fun n : name => nu (x1 n))))))
    (cons x (cons y (cons z empty)))); intros.
inversion_clear H16.
inversion_clear H17; inversion_clear H18.
inversion_clear H19; inversion_clear H20.
inversion_clear H21; inversion_clear H22.
clear H24.
apply Hrecn with x2; auto.
inversion_clear H23; auto.
inversion_clear H20; auto.
change
  (PAR_C_fun n ((fun n : name => x1 n x2) y) ((fun n : name => x0 n x2) y))
 in |- *; apply Hrecn with x; auto.
inversion_clear H8; apply notin_nu; intros.
cut (notin x (nu (x1 z0))); [ intro | auto ].
inversion_clear H24; auto.
inversion_clear H10; apply notin_nu; intros.
cut (notin x (nu (x0 z0))); [ intro | auto ].
inversion_clear H24; auto.
apply proc_mono with x; inversion_clear H2.
cut (notin y (p x)); [ rewrite <- H5; intro | auto ].
inversion_clear H2; auto.
apply proc_mono with x; inversion_clear H3.
cut (notin y (q x)); [ rewrite <- H6; intro | auto ].
inversion_clear H3; auto.
rewrite <- H11; rewrite <- H12; apply H7; auto.
inversion_clear H23.
cut (notin x2 (nu (x1 x))); [ intro | auto ]; rewrite H12; assumption.
inversion_clear H20.
cut (notin x2 (nu (x0 x))); [ intro | auto ]; rewrite H11; assumption.

Qed.

(* SBPAR_C is a strong bisimulation *)

Lemma SBPAR_C_TO_SB' : Inclus SBPAR_C (Op_StBisim SBPAR_C).

Proof.

unfold Inclus in |- *; intros.
inversion_clear H.
cut (PAR_C_fun n p1 p2);
 [ generalize p1 p2; generalize n; simple induction n0; intros | assumption ].

(* Base case *)

simpl in H; inversion H.
apply op_sb; split; intros.

(* Free actions case *)

split; intros.

inversion_clear H3.

exists (par q p7); split;
 [ apply fPAR2; assumption | apply sbpar_c with 0; apply bispar_c ].

exists (par p7 p); split;
 [ apply fPAR1; assumption | apply sbpar_c with 0; apply bispar_c ].

exists (par q2 (q1 y)); split;
 [ apply COM2 with x; assumption | apply sbpar_c with 0; apply bispar_c ].

exists (par (q2 y) q1); split;
 [ apply COM1 with x; assumption | apply sbpar_c with 0; apply bispar_c ].

exists (nu (fun n : name => par (q2 n) (q1 n))); split;
 [ apply CLOSE2 with x; assumption
 | apply sbpar_c with 1; simpl in |- *; apply op_par_c; intros;
    apply bispar_c ].

exists (nu (fun n : name => par (q2 n) (q1 n))); split;
 [ apply CLOSE1 with x; assumption
 | apply sbpar_c with 1; simpl in |- *; apply op_par_c; intros;
    apply bispar_c ].

inversion_clear H3.

exists (par p p6); split;
 [ apply fPAR2; assumption | apply sbpar_c with 0; apply bispar_c ].

exists (par p6 q); split;
 [ apply fPAR1; assumption | apply sbpar_c with 0; apply bispar_c ].

exists (par q2 (q0 y)); split;
 [ apply COM2 with x; assumption | apply sbpar_c with 0; apply bispar_c ].

exists (par (q2 y) q0); split;
 [ apply COM1 with x; assumption | apply sbpar_c with 0; apply bispar_c ].

exists (nu (fun n : name => par (q2 n) (q0 n))); split;
 [ apply CLOSE2 with x; assumption
 | apply sbpar_c with 1; simpl in |- *; apply op_par_c; intros;
    apply bispar_c ].

exists (nu (fun n : name => par (q2 n) (q0 n))); split;
 [ apply CLOSE1 with x; assumption
 | apply sbpar_c with 1; simpl in |- *; apply op_par_c; intros;
    apply bispar_c ].

(* Input actions case *)

split; intros.

split; intros.

inversion_clear H3.

exists (fun n : name => par q (p7 n)); split;
 [ apply bPAR2; assumption
 | intro; apply sbpar_c with 0; simpl in |- *; apply bispar_c ].

exists (fun n : name => par (p7 n) p); split;
 [ apply bPAR1; assumption
 | intro; apply sbpar_c with 0; simpl in |- *; apply bispar_c ].

inversion_clear H3.

exists (fun n : name => par p (p6 n)); split;
 [ apply bPAR2; assumption
 | intro; apply sbpar_c with 0; simpl in |- *; apply bispar_c ].

exists (fun n : name => par (p6 n) q); split;
 [ apply bPAR1; assumption
 | intro; apply sbpar_c with 0; simpl in |- *; apply bispar_c ].

(* Bound Output actions case *)

split; intros.

inversion_clear H3.

exists (fun n : name => par q (p7 n)); split;
 [ apply bPAR2; assumption
 | intros; apply sbpar_c with 0; simpl in |- *; apply bispar_c ].

exists (fun n : name => par (p7 n) p); split;
 [ apply bPAR1; assumption
 | intros; apply sbpar_c with 0; simpl in |- *; apply bispar_c ].

inversion_clear H3.

exists (fun n : name => par p (p6 n)); split;
 [ apply bPAR2; assumption
 | intros; apply sbpar_c with 0; simpl in |- *; apply bispar_c ].

exists (fun n : name => par (p6 n) q); split;
 [ apply bPAR1; assumption
 | intros; apply sbpar_c with 0; simpl in |- *; apply bispar_c ].

(* Inductive Step *)

simpl in H1; inversion H1.
apply op_sb; split; intros.

elim a; intros; split; intros.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_C (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu p6))) l); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H10.
cut (ftrans (p x) tau (p6 x)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_C (p x) (q x)); [ intro | apply H5; auto ].
inversion_clear H12.
inversion_clear H13.
elim (H12 tau); intros.
elim (H13 (p6 x) H10); intros.
inversion_clear H16; elim (proc_exp x0 x); intros.
inversion_clear H16.
rewrite H20 in H17; rewrite H20 in H18.
exists (nu x1); split; [ apply fRES with l; intros | idtac ].
change (ftrans (q y) ((fun _ : name => tau) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
inversion_clear H18; apply sbpar_c with (S n2); simpl in |- *; apply op_par_c;
 intros.
apply PAR_C_RW with x; auto.
apply f_act_notin_tau.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_C (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu p5))) l); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H10; cut (ftrans (q x) tau (p5 x));
 [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_C (p x) (q x)); [ intro | apply H5; auto ].
inversion_clear H12.
inversion_clear H13.
elim (H12 tau); intros.
elim (H15 (p5 x) H10); intros.
inversion_clear H16; elim (proc_exp x0 x); intros.
inversion_clear H16.
rewrite H20 in H17; rewrite H20 in H18.
exists (nu x1); split; [ apply fRES with l; intros | idtac ].
change (ftrans (p y) ((fun _ : name => tau) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
inversion_clear H18.
apply sbpar_c with (S n2); simpl in |- *; apply op_par_c; intros.
apply PAR_C_RW with x; auto.
apply f_act_notin_tau.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_C (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu p6))) (cons n2 (cons n3 l))); intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (ftrans (p x) (Out n2 n3) (p6 x)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_C (p x) (q x)); [ intro | apply H5; auto ].
inversion_clear H14.
inversion_clear H15.
elim (H14 (Out n2 n3)); intros.
elim (H15 (p6 x) H11); intros.
inversion_clear H18; elim (proc_exp x0 x); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (nu x1); split; [ apply fRES with l; intros | idtac ].
inversion_clear H25;
 change (ftrans (q y) ((fun _ : name => Out n2 n3) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
inversion_clear H20.
apply sbpar_c with (S n4); simpl in |- *; apply op_par_c; intros.
apply PAR_C_RW with x; auto.
apply f_act_notin_Out; auto.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_C (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu p5))) (cons n2 (cons n3 l))); intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (ftrans (q x) (Out n2 n3) (p5 x)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_C (p x) (q x)); [ intro | apply H5; auto ].
inversion_clear H14.
inversion_clear H15.
elim (H14 (Out n2 n3)); intros.
elim (H17 (p5 x) H11); intros.
inversion_clear H18; elim (proc_exp x0 x); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (nu x1); split; [ apply fRES with l; intros | idtac ].
inversion_clear H25;
 change (ftrans (p y) ((fun _ : name => Out n2 n3) y) (x1 y)) in |- *;
 apply FTR_L3 with x; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
inversion_clear H20.
apply sbpar_c with (S n4); simpl in |- *; apply op_par_c; intros.
apply PAR_C_RW with x; auto.
apply f_act_notin_Out; auto.

split; intros.

split; intros.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_C (p x) (q x));
 [ intro | auto ].
elim
 (unsat (par (nu p) (par (nu q) (nu (fun n : name => nu (p6 n))))) (cons x l));
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (btrans (p x0) (In x) (p6 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_C (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
elim (H14 x); intros.
elim (H15 (p6 x0) H10); intros.
inversion_clear H18; elim (ho_proc_exp x1 x0); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (fun n : name => nu (fun u : name => x2 u n)); split;
 [ apply bRES with l; intros | idtac ].
inversion_clear H24;
 change (btrans (q y) ((fun _ : name => In x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
intro; elim (LEM_name x0 y); intro.

rewrite <- H18;
 elim
  (unsat
     (par (nu (fun n : name => nu (p6 n))) (nu (fun n : name => nu (x2 n))))
     (cons x0 empty)); intros.
inversion_clear H23.
inversion_clear H24; inversion_clear H25.
clear H27; cut (SBPAR_C (p6 x0 x3) (x2 x0 x3)); [ intro | auto ].
inversion_clear H25.
apply sbpar_c with (S n2); simpl in |- *; apply op_par_c; intros.
elim
 (unsat
    (par (nu (fun n : name => nu (p6 n))) (nu (fun n : name => nu (x2 n))))
    (cons x0 (cons x3 (cons z empty)))); intros.
inversion_clear H29.
inversion_clear H30; inversion_clear H31.
inversion_clear H33.
inversion_clear H34.
clear H35.
cut (PAR_C_fun n2 (p6 x4 x3) (x2 x4 x3));
 [ intro
 | change
     (PAR_C_fun n2 ((fun n : name => p6 n x3) x4)
        ((fun n : name => x2 n x3) x4)) in |- *; apply PAR_C_RW with x0; 
    auto ].
change
  (PAR_C_fun n2 ((fun n : name => p6 n x0) z) ((fun n : name => x2 n x0) z))
 in |- *; apply PAR_C_RW with x4; auto.
inversion_clear H29; apply notin_nu; intros.
cut (notin x4 (nu (p6 z0))); [ intro | auto ].
inversion_clear H36; auto.
inversion_clear H32; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H36; auto.
apply PAR_C_RW with x3; auto.
inversion_clear H23; auto.
inversion_clear H26; auto.
inversion_clear H12; auto.
inversion_clear H21; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p6 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H29; apply notin_nu; intros.
cut (notin x4 (nu (p6 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H32; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H35; auto.

cut (SBPAR_C (p6 x0 y) (x2 x0 y)); [ intro | auto ].
inversion_clear H23.
apply sbpar_c with (S n2); simpl in |- *; apply op_par_c; intros.
change
  (PAR_C_fun n2 ((fun n : name => p6 n y) z) ((fun n : name => x2 n y) z))
 in |- *; apply PAR_C_RW with x0; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p6 z0))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H27; auto.
apply b_act_notin_In; auto.

inversion_clear H5.
cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_C (p x) (q x));
 [ intro | auto ].
elim
 (unsat (par (nu p) (par (nu q) (nu (fun n : name => nu (p5 n))))) (cons x l));
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (btrans (q x0) (In x) (p5 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_C (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
elim (H14 x); intros.
elim (H17 (p5 x0) H10); intros.
inversion_clear H18; elim (ho_proc_exp x1 x0); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (fun n : name => nu (fun u : name => x2 u n)); split;
 [ apply bRES with l; intros | idtac ].
inversion_clear H24;
 change (btrans (p y) ((fun _ : name => In x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
intro; elim (LEM_name x0 y); intro.

rewrite <- H18;
 elim
  (unsat
     (par (nu (fun n : name => nu (p5 n))) (nu (fun n : name => nu (x2 n))))
     (cons x0 empty)); intros.
inversion_clear H23.
inversion_clear H24; inversion_clear H25.
clear H27; cut (SBPAR_C (x2 x0 x3) (p5 x0 x3)); [ intro | auto ].
inversion_clear H25.
apply sbpar_c with (S n2); simpl in |- *; apply op_par_c; intros.
elim
 (unsat
    (par (nu (fun n : name => nu (p5 n))) (nu (fun n : name => nu (x2 n))))
    (cons x0 (cons x3 (cons z empty)))); intros.
inversion_clear H29.
inversion_clear H30; inversion_clear H31.
inversion_clear H33.
inversion_clear H34.
clear H35; cut (PAR_C_fun n2 (x2 x4 x3) (p5 x4 x3));
 [ intro
 | change
     (PAR_C_fun n2 ((fun n : name => x2 n x3) x4)
        ((fun n : name => p5 n x3) x4)) in |- *; apply PAR_C_RW with x0; 
    auto ].
change
  (PAR_C_fun n2 ((fun n : name => x2 n x0) z) ((fun n : name => p5 n x0) z))
 in |- *; apply PAR_C_RW with x4; auto.
inversion_clear H32; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H36; auto.
inversion_clear H29; apply notin_nu; intros.
cut (notin x4 (nu (p5 z0))); [ intro | auto ].
inversion_clear H36; auto.
apply PAR_C_RW with x3; auto.
inversion_clear H26; auto.
inversion_clear H23; auto.
inversion_clear H21; auto.
inversion_clear H12; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p5 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H32; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H35; auto.
inversion_clear H29; apply notin_nu; intros.
cut (notin x4 (nu (p5 z0))); [ intro | auto ].
inversion_clear H35; auto.

cut (SBPAR_C (x2 x0 y) (p5 x0 y)); [ intro | auto ].
inversion_clear H23.
apply sbpar_c with (S n2); simpl in |- *; apply op_par_c; intros.
change
  (PAR_C_fun n2 ((fun n : name => x2 n y) z) ((fun n : name => p5 n y) z))
 in |- *; apply PAR_C_RW with x0; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H27; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p5 z0))); [ intro | auto ].
inversion_clear H27; auto.
apply b_act_notin_In; auto.

split; intros.

inversion_clear H5.

cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_C (p x) (q x));
 [ intro | auto ].
elim
 (unsat (par (nu p) (par (nu q) (nu (fun n : name => nu (p6 n))))) (cons x l));
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (btrans (p x0) (bOut x) (p6 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_C (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
elim (H16 x); intros.
elim (H15 (p6 x0) H10); intros.
inversion_clear H18; elim (ho_proc_exp x1 x0); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (fun n : name => nu (fun u : name => x2 u n)); split;
 [ apply bRES with l; intros | idtac ].
inversion_clear H24;
 change (btrans (q y) ((fun _ : name => bOut x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
intros; elim (LEM_name x0 y); intro.

rewrite <- H24;
 elim
  (unsat
     (par (nu (fun n : name => nu (p6 n))) (nu (fun n : name => nu (x2 n))))
     (cons x0 empty)); intros.
inversion_clear H25.
inversion_clear H26; inversion_clear H27.
clear H29; cut (SBPAR_C (p6 x0 x3) (x2 x0 x3)); [ intro | apply H20; auto ].
inversion_clear H27.
apply sbpar_c with (S n2); simpl in |- *; apply op_par_c; intros.
elim
 (unsat
    (par (nu (fun n : name => nu (p6 n))) (nu (fun n : name => nu (x2 n))))
    (cons x0 (cons x3 (cons z empty)))); intros.
inversion_clear H31.
inversion_clear H32; inversion_clear H33.
inversion_clear H35.
inversion_clear H36.
clear H37; cut (PAR_C_fun n2 (p6 x4 x3) (x2 x4 x3));
 [ intro
 | change
     (PAR_C_fun n2 ((fun n : name => p6 n x3) x4)
        ((fun n : name => x2 n x3) x4)) in |- *; apply PAR_C_RW with x0; 
    auto ].
change
  (PAR_C_fun n2 ((fun n : name => p6 n x0) z) ((fun n : name => x2 n x0) z))
 in |- *; apply PAR_C_RW with x4; auto.
inversion_clear H31; apply notin_nu; intros.
cut (notin x4 (nu (p6 z0))); [ intro | auto ].
inversion_clear H38; auto.
inversion_clear H34; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H38; auto.
apply PAR_C_RW with x3; auto.
inversion_clear H25; auto.
inversion_clear H28; auto.
inversion_clear H12; auto.
inversion_clear H21; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p6 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H31; apply notin_nu; intros.
cut (notin x4 (nu (p6 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H34; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H25; auto.
inversion_clear H28; auto.

cut (SBPAR_C (p6 x0 y) (x2 x0 y)); [ intro | apply H20; auto ].
inversion_clear H25.
apply sbpar_c with (S n2); simpl in |- *; apply op_par_c; intros.
change
  (PAR_C_fun n2 ((fun n : name => p6 n y) z) ((fun n : name => x2 n y) z))
 in |- *; apply PAR_C_RW with x0; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p6 z0))); [ intro | auto ].
inversion_clear H29; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H29; auto.
inversion_clear H18; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => p6 z0 z))); [ intro | auto ].
inversion_clear H26; auto.
inversion_clear H23; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => x2 z0 z))); [ intro | auto ].
inversion_clear H26; auto.
apply b_act_notin_bOut; auto.

cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_C (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu p4))) (cons x l)); intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (ftrans (p x0) (Out x x0) (p4 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_C (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
elim (H13 (Out x x0)); intros.
elim (H14 (p4 x0) H10); intros.
inversion_clear H17.
elim (proc_exp x1 x0); intros.
inversion_clear H17.
rewrite H21 in H18; rewrite H21 in H19.
exists x2; split; [ apply OPEN with l; intros | idtac ].
change (ftrans (q y) (Out x y) (x2 y)) in |- *; apply FTR_L3 with x0; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
intros; inversion_clear H19.
apply sbpar_c with n2; apply PAR_C_RW with x0; auto.

inversion_clear H5.

cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_C (p x) (q x));
 [ intro | auto ].
elim
 (unsat (par (nu p) (par (nu q) (nu (fun n : name => nu (p5 n))))) (cons x l));
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (btrans (q x0) (bOut x) (p5 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_C (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
elim (H16 x); intros.
elim (H17 (p5 x0) H10); intros.
inversion_clear H18.
elim (ho_proc_exp x1 x0); intros.
inversion_clear H18.
rewrite H22 in H19; rewrite H22 in H20.
exists (fun n : name => nu (fun u : name => x2 u n)); split;
 [ apply bRES with l; intros | idtac ].
inversion_clear H24;
 change (btrans (p y) ((fun _ : name => bOut x) y) (x2 y)) in |- *;
 apply BTR_L3 with x0; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
intros; elim (LEM_name x0 y); intro.

rewrite <- H24;
 elim
  (unsat
     (par (nu (fun n : name => nu (p5 n))) (nu (fun n : name => nu (x2 n))))
     (cons x0 empty)); intros.
inversion_clear H25.
inversion_clear H26; inversion_clear H27.
clear H29; cut (SBPAR_C (x2 x0 x3) (p5 x0 x3)); [ intro | apply H20; auto ].
inversion_clear H27.
apply sbpar_c with (S n2); simpl in |- *; apply op_par_c; intros.
elim
 (unsat
    (par (nu (fun n : name => nu (p5 n))) (nu (fun n : name => nu (x2 n))))
    (cons x0 (cons x3 (cons z empty)))); intros.
inversion_clear H31.
inversion_clear H32; inversion_clear H33.
inversion_clear H35.
inversion_clear H36.
clear H37; cut (PAR_C_fun n2 (x2 x4 x3) (p5 x4 x3));
 [ intro
 | change
     (PAR_C_fun n2 ((fun n : name => x2 n x3) x4)
        ((fun n : name => p5 n x3) x4)) in |- *; apply PAR_C_RW with x0; 
    auto ].
change
  (PAR_C_fun n2 ((fun n : name => x2 n x0) z) ((fun n : name => p5 n x0) z))
 in |- *; apply PAR_C_RW with x4; auto.
inversion_clear H34; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H38; auto.
inversion_clear H31; apply notin_nu; intros.
cut (notin x4 (nu (p5 z0))); [ intro | auto ].
inversion_clear H38; auto.
apply PAR_C_RW with x3; auto.
inversion_clear H28; auto.
inversion_clear H25; auto.
inversion_clear H21; auto.
inversion_clear H12; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p5 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H34; apply notin_nu; intros.
cut (notin x4 (nu (x2 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H31; apply notin_nu; intros.
cut (notin x4 (nu (p5 z0))); [ intro | auto ].
inversion_clear H37; auto.
inversion_clear H28; auto.
inversion_clear H25; auto.

cut (SBPAR_C (x2 x0 y) (p5 x0 y)); [ intro | apply H20; auto ].
inversion_clear H25.
apply sbpar_c with (S n2); simpl in |- *; apply op_par_c; intros.
change
  (PAR_C_fun n2 ((fun n : name => x2 n y) z) ((fun n : name => p5 n y) z))
 in |- *; apply PAR_C_RW with x0; auto.
inversion_clear H21; apply notin_nu; intros.
cut (notin x0 (nu (x2 z0))); [ intro | auto ].
inversion_clear H29; auto.
inversion_clear H12; apply notin_nu; intros.
cut (notin x0 (nu (p5 z0))); [ intro | auto ].
inversion_clear H29; auto.
inversion_clear H18; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => x2 z0 z))); [ intro | auto ].
inversion_clear H26; auto.
inversion_clear H23; apply notin_nu; intros.
cut (notin y (nu (fun z0 : name => p5 z0 z))); [ intro | auto ].
inversion_clear H26; auto.
apply b_act_notin_bOut; auto.

cut
 (forall x : name,
  notin x (nu p) -> notin x (nu q) -> Op_StBisim SBPAR_C (p x) (q x));
 [ intro | auto ].
elim (unsat (par (nu p) (par (nu q) (nu q1))) (cons x l)); intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10.
cut (ftrans (q x0) (Out x x0) (q1 x0)); [ intro | apply H6; auto ].
cut (Op_StBisim SBPAR_C (p x0) (q x0)); [ intro | apply H5; auto ].
inversion_clear H13.
inversion_clear H14.
elim (H13 (Out x x0)); intros.
elim (H16 (q1 x0) H10); intros.
inversion_clear H17.
elim (proc_exp x1 x0); intros.
inversion_clear H17.
rewrite H21 in H18; rewrite H21 in H19.
exists x2; split; [ apply OPEN with l; intros | idtac ].
change (ftrans (p y) (Out x y) (x2 y)) in |- *; apply FTR_L3 with x0; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
intros; inversion_clear H19.
apply sbpar_c with n2; apply PAR_C_RW with x0; auto.

Qed.

(* Finally, the commutativity of parallel composition
 * is proved by means of internal cross adequacy.
 *)

Lemma COMM_PAR : forall p q : proc, StBisim (par p q) (par q p).

Proof.

intros; apply Completeness; apply Co_Ind with SBPAR_C;
 [ exact SBPAR_C_TO_SB'
 | apply sbpar_c with 0; simpl in |- *; apply bispar_c; assumption ].

Qed.

(* End parallel. *)

(* Section upto. *)

(***************************************************************************)
(* In this section the technique of strong bisimulation up to equivalence  *)
(* and restriction (UpTo for short) is exploited in order to prove the     *)
(* restriction operator extrusion law and the associativity of parallel    *)
(* composition.                                                            *)
(***************************************************************************)

Definition SB_R_SB (R : proc -> proc -> Prop) (p q : proc) :=
  exists p' : proc,
    (exists q' : proc, StBisim p p' /\ R p' q' /\ StBisim q' q).

(* Definition of being a strong bisimulation
 * up to equivalence and restriction.
 *)

Definition UpTo (R : proc -> proc -> Prop) :=
  forall p q : proc,
  R p q ->
  (forall (p' q' : name -> proc) (x : name),
   notin x (nu p') ->
   notin x (nu q') ->
   p = p' x ->
   q = q' x ->
   forall y : name, notin y (nu p') -> notin y (nu q') -> R (p' y) (q' y)) /\
  (forall x y : name,
   (forall p1 : proc,
    ftrans p (Out x y) p1 ->
    exists q1 : proc, ftrans q (Out x y) q1 /\ SB_R_SB R p1 q1) /\
   (forall q1 : proc,
    ftrans q (Out x y) q1 ->
    exists p1 : proc, ftrans p (Out x y) p1 /\ SB_R_SB R p1 q1)) /\
  (forall x : name,
   (forall p1 : name -> proc,
    btrans p (In x) p1 ->
    exists q1 : name -> proc,
      btrans q (In x) q1 /\ (forall y : name, SB_R_SB R (p1 y) (q1 y))) /\
   (forall q1 : name -> proc,
    btrans q (In x) q1 ->
    exists p1 : name -> proc,
      btrans p (In x) p1 /\ (forall y : name, SB_R_SB R (p1 y) (q1 y)))) /\
  (forall x : name,
   (forall p1 : name -> proc,
    btrans p (bOut x) p1 ->
    exists q1 : name -> proc,
      btrans q (bOut x) q1 /\
      (forall y : name,
       notin y (nu p1) -> notin y (nu q1) -> SB_R_SB R (p1 y) (q1 y))) /\
   (forall q1 : name -> proc,
    btrans q (bOut x) q1 ->
    exists p1 : name -> proc,
      btrans p (bOut x) p1 /\
      (forall y : name,
       notin y (nu p1) -> notin y (nu q1) -> SB_R_SB R (p1 y) (q1 y)))) /\
  (forall p1 : proc,
   ftrans p tau p1 ->
   exists q1 : proc,
     ftrans q tau q1 /\
     (SB_R_SB R p1 q1 \/
      (exists p1' : name -> proc,
         (exists q1' : name -> proc,
            StBisim p1 (nu p1') /\
            (forall z : name,
             notin z (nu p1') -> notin z (nu q1') -> R (p1' z) (q1' z)) /\
            StBisim (nu q1') q1)))) /\
  (forall q1 : proc,
   ftrans q tau q1 ->
   exists p1 : proc,
     ftrans p tau p1 /\
     (SB_R_SB R p1 q1 \/
      (exists p1' : name -> proc,
         (exists q1' : name -> proc,
            StBisim p1 (nu p1') /\
            (forall z : name,
             notin z (nu p1') -> notin z (nu q1') -> R (p1' z) (q1' z)) /\
            StBisim (nu q1') q1)))).

Inductive Op_NU (R : proc -> proc -> Prop) : proc -> proc -> Prop :=
    op_nu :
      forall (p q : proc) (p' q' : name -> proc),
      StBisim p (nu p') ->
      StBisim (nu q') q ->
      (forall z : name, notin z (nu p') -> notin z (nu q') -> R (p' z) (q' z)) ->
      Op_NU R p q.

Fixpoint NU_fun (R : proc -> proc -> Prop) (n : nat) {struct n} :
 proc -> proc -> Prop :=
  match n with
  | O => SB_R_SB R
  | S m => Op_NU (NU_fun R m)
  end.

Inductive SBUPTO (R : proc -> proc -> Prop) (p q : proc) : Prop :=
    sbupto : forall n : nat, NU_fun R n p q -> SBUPTO R p q.

(* Strong bisimulations UpTo enjoy a property similar to that established
 * by L6_Light for StBisim.
 *)

Lemma NU_FUN_RW :
 forall R : proc -> proc -> Prop,
 UpTo R ->
 forall (n : nat) (p q : name -> proc) (x : name),
 notin x (nu p) ->
 notin x (nu q) ->
 NU_fun R n (p x) (q x) ->
 forall y : name, notin y (nu p) -> notin y (nu q) -> NU_fun R n (p y) (q y).

Proof.

intros; elim (LEM_name x y); intro.

rewrite <- H5; assumption.

generalize p q x H0 H1 y H5 H3 H4 H2; clear H0 H1 H3 H4 H5 y H2 x p q;
 induction  n as [| n Hrecn]; intros.

(* Base Case *)

simpl in H2; inversion H2; simpl in |- *; unfold SB_R_SB in |- *.
inversion_clear H6; inversion_clear H7; inversion_clear H8.
elim (proc_exp x0 x); elim (proc_exp x1 x); intros.
inversion_clear H8; inversion_clear H10.
rewrite H12 in H7; rewrite H12 in H9; rewrite H13 in H6; rewrite H13 in H7.
elim (ho_proc_exp x2 y); elim (ho_proc_exp x3 y); intros.
inversion_clear H10; inversion_clear H14.
elim
 (unsat
    (par (nu p)
       (par (nu q)
          (par (nu (fun n : name => nu (x4 n)))
             (nu (fun n : name => nu (x5 n)))))) (cons x (cons y empty)));
 intros.
inversion_clear H14; inversion_clear H18; inversion_clear H19;
 inversion_clear H20; inversion_clear H21; clear H23; 
 inversion_clear H22.
exists (x4 x6 y); exists (x5 x6 y); split; [ idtac | split ].
apply L6_Light with x; auto.
cut (notin x (nu (fun y : name => nu (x4 y))));
 [ intro; inversion_clear H22; auto
 | apply proc_mono with y; rewrite <- H16; assumption ].
change (StBisim ((fun n : name => p x) x6) ((fun n : name => x4 n x) x6))
 in |- *; apply L6_Light with y; auto.
inversion_clear H3; apply notin_nu; intros; auto.
inversion_clear H15; apply notin_nu; intros; cut (notin y (nu (x4 z)));
 [ intro | auto ]; inversion_clear H24; auto.
rewrite <- H16; assumption.
inversion_clear H14; apply notin_nu; intros; auto.
inversion_clear H21; apply notin_nu; intros; cut (notin x6 (nu (x4 z)));
 [ intro | auto ]; inversion_clear H24; auto.
inversion_clear H15; auto.
rewrite H16 in H7; rewrite H17 in H7; unfold UpTo in H;
 elim (H (x4 x6 x) (x5 x6 x)); intros; try clear H24.
apply H22 with x; auto.
cut (notin x (nu (fun n : name => nu (x4 n))));
 [ intro | apply proc_mono with y; rewrite <- H16; assumption ];
 inversion_clear H24; auto.
cut (notin x (nu (fun n : name => nu (x5 n))));
 [ intro | apply proc_mono with y; rewrite <- H17; assumption ];
 inversion_clear H24; auto.
inversion_clear H15; auto.
inversion_clear H10; auto.
unfold UpTo in H; elim (H (x4 y x) (x5 y x)); intros; auto; clear H24.
change (R ((fun n : name => x4 n x) x6) ((fun n : name => x5 n x) x6))
 in |- *; apply H22 with y; auto.
inversion_clear H15; apply notin_nu; intros; cut (notin y (nu (x4 z)));
 [ intro | auto ]; inversion_clear H25; auto.
inversion_clear H10; apply notin_nu; intros; cut (notin y (nu (x5 z)));
 [ intro | auto ]; inversion_clear H25; auto.
inversion_clear H21; apply notin_nu; intros; cut (notin x6 (nu (x4 z)));
 [ intro | auto ]; inversion_clear H25; auto.
inversion_clear H23; apply notin_nu; intros; cut (notin x6 (nu (x5 z)));
 [ intro | auto ]; inversion_clear H25; auto.
apply L6_Light with x; auto.
cut (notin x (nu (fun y : name => nu (x5 y))));
 [ intro; inversion_clear H22; auto
 | apply proc_mono with y; rewrite <- H17; assumption ].
change (StBisim ((fun n : name => x5 n x) x6) ((fun n : name => q x) x6))
 in |- *; apply L6_Light with y; auto.
inversion_clear H10; apply notin_nu; intros; cut (notin y (nu (x5 z)));
 [ intro | auto ]; inversion_clear H24; auto.
inversion_clear H4; apply notin_nu; intros; auto.
rewrite <- H17; assumption.
inversion_clear H23; apply notin_nu; intros; cut (notin x6 (nu (x5 z)));
 [ intro | auto ]; inversion_clear H24; auto.
inversion_clear H19; apply notin_nu; intros; auto.
inversion_clear H10; auto.

(* Inductive step *)

simpl in H2; inversion H2; simpl in |- *.
elim (ho_proc_exp p' x); elim (ho_proc_exp q' x); intros.
inversion_clear H11; inversion_clear H12.
rewrite H14 in H7; rewrite H15 in H6; rewrite H14 in H8; rewrite H15 in H8.
elim (ho2_proc_exp x0 y); elim (ho2_proc_exp x1 y); intros.
inversion_clear H12; inversion_clear H16.
elim
 (unsat
    (par (nu p)
       (par (nu q)
          (par (nu (fun u : name => nu (fun v : name => nu (x2 u v))))
             (nu (fun u : name => nu (fun v : name => nu (x3 u v)))))))
    (cons x (cons y empty))); intros.
inversion_clear H16; inversion_clear H20; inversion_clear H21;
 inversion_clear H22; inversion_clear H23; clear H25; 
 inversion_clear H24.
apply op_nu with (x2 x4 y) (x3 x4 y); intros.
change (StBisim (p y) ((fun n : name => nu (x2 x4 n)) y)) in |- *;
 apply L6_Light with x; auto.
cut (notin x (nu (fun y : name => nu (fun z : name => nu (x2 y z)))));
 [ intro; inversion_clear H24; apply notin_nu; intros;
    cut (notin x (nu (fun z : name => nu (x2 x4 z)))); 
    [ intro | auto ]; inversion_clear H27; auto
 | apply proc_mono with y; rewrite <- H18; assumption ].
change
  (StBisim ((fun n : name => p x) x4) ((fun n : name => nu (x2 n x)) x4))
 in |- *; apply L6_Light with y; auto.
inversion_clear H3; apply notin_nu; intros; auto.
inversion_clear H17; apply notin_nu; intros;
 cut (notin y (nu (fun n : name => nu (x2 z n)))); 
 [ intro | auto ]; inversion_clear H26; auto.
rewrite <- H18; assumption.
inversion_clear H16; apply notin_nu; intros; auto.
inversion_clear H23; apply notin_nu; intros;
 cut (notin x4 (nu (fun n : name => nu (x2 z n)))); 
 [ intro | auto ]; inversion_clear H26; auto.
inversion_clear H17; apply notin_nu; intros;
 cut (notin y (nu (fun n : name => nu (x2 x4 n)))); 
 [ intro | auto ]; inversion_clear H26; auto.

change (StBisim ((fun n : name => nu (x3 x4 n)) y) (q y)) in |- *;
 apply L6_Light with x; auto.
cut (notin x (nu (fun y : name => nu (fun z : name => nu (x3 y z)))));
 [ intro; inversion_clear H24; apply notin_nu; intros;
    cut (notin x (nu (fun z : name => nu (x3 x4 z)))); 
    [ intro | auto ]; inversion_clear H27; auto
 | apply proc_mono with y; rewrite <- H19; assumption ].
change
  (StBisim ((fun n : name => nu (x3 n x)) x4) ((fun n : name => q x) x4))
 in |- *; apply L6_Light with y; auto.
inversion_clear H12; apply notin_nu; intros;
 cut (notin y (nu (fun n : name => nu (x3 z n)))); 
 [ intro | auto ]; inversion_clear H26; auto.
inversion_clear H4; apply notin_nu; intros; auto.
rewrite <- H19; assumption.
inversion_clear H25; apply notin_nu; intros;
 cut (notin x4 (nu (fun n : name => nu (x3 z n)))); 
 [ intro | auto ]; inversion_clear H26; auto.
inversion_clear H21; apply notin_nu; intros; auto.
inversion_clear H12; apply notin_nu; intros;
 cut (notin y (nu (fun n : name => nu (x3 x4 n)))); 
 [ intro | auto ]; inversion_clear H26; auto.
elim
 (unsat
    (par (nu (fun u : name => nu (fun v : name => nu (x2 u v))))
       (nu (fun u : name => nu (fun v : name => nu (x3 u v)))))
    (cons x (cons y (cons z (cons x4 empty))))); intros.
inversion_clear H27; inversion_clear H28; inversion_clear H29;
 inversion_clear H31; inversion_clear H32; inversion_clear H33; 
 clear H34.
apply Hrecn with x5; auto.
inversion_clear H27; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => nu (x2 x4 v)))); 
 [ intro | auto ]; inversion_clear H34; cut (notin x5 (nu (x2 x4 y)));
 [ intro | auto ]; inversion_clear H34; auto.
inversion_clear H30; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => nu (x3 x4 v)))); 
 [ intro | auto ]; inversion_clear H34; cut (notin x5 (nu (x3 x4 y)));
 [ intro | auto ]; inversion_clear H34; auto.
change
  (NU_fun R n ((fun n : name => x2 x4 n x5) y)
     ((fun n : name => x3 x4 n x5) y)) in |- *; apply Hrecn with x; 
 auto.
cut (notin x (nu (fun y : name => nu (fun z : name => nu (x2 y z)))));
 [ intro; inversion_clear H33; apply notin_nu; intros;
    cut (notin x (nu (fun z : name => nu (x2 x4 z)))); 
    [ intro | auto ]; inversion_clear H35; cut (notin x (nu (x2 x4 z0)));
    [ intro | auto ]; inversion_clear H35; auto
 | apply proc_mono with y; rewrite <- H18; assumption ].
cut (notin x (nu (fun y : name => nu (fun z : name => nu (x3 y z)))));
 [ intro; inversion_clear H33; apply notin_nu; intros;
    cut (notin x (nu (fun z : name => nu (x3 x4 z)))); 
    [ intro | auto ]; inversion_clear H35; cut (notin x (nu (x3 x4 z0)));
    [ intro | auto ]; inversion_clear H35; auto
 | apply proc_mono with y; rewrite <- H19; assumption ].
inversion_clear H17; apply notin_nu; intros;
 cut (notin y (nu (fun z : name => nu (x2 x4 z)))); 
 [ intro | auto ]; inversion_clear H34; cut (notin y (nu (x2 x4 z0)));
 [ intro | auto ]; inversion_clear H34; auto.
inversion_clear H12; apply notin_nu; intros;
 cut (notin y (nu (fun z : name => nu (x3 x4 z)))); 
 [ intro | auto ]; inversion_clear H34; cut (notin y (nu (x3 x4 z0)));
 [ intro | auto ]; inversion_clear H34; auto.
change
  (NU_fun R n ((fun n : name => x2 n x x5) x4)
     ((fun n : name => x3 n x x5) x4)) in |- *; apply Hrecn with y; 
 auto.
inversion_clear H17; apply notin_nu; intros;
 cut (notin y (nu (fun z : name => nu (x2 z0 z)))); 
 [ intro | auto ]; inversion_clear H34; cut (notin y (nu (x2 z0 x)));
 [ intro | auto ]; inversion_clear H34; auto.
inversion_clear H12; apply notin_nu; intros;
 cut (notin y (nu (fun z : name => nu (x3 z0 z)))); 
 [ intro | auto ]; inversion_clear H34; cut (notin y (nu (x3 z0 x)));
 [ intro | auto ]; inversion_clear H34; auto.
inversion_clear H23; apply notin_nu; intros;
 cut (notin x4 (nu (fun z : name => nu (x2 z0 z)))); 
 [ intro | auto ]; inversion_clear H34; cut (notin x4 (nu (x2 z0 x)));
 [ intro | auto ]; inversion_clear H34; auto.
inversion_clear H25; apply notin_nu; intros;
 cut (notin x4 (nu (fun z : name => nu (x3 z0 z)))); 
 [ intro | auto ]; inversion_clear H34; cut (notin x4 (nu (x3 z0 x)));
 [ intro | auto ]; inversion_clear H34; auto.
rewrite <- H18; rewrite <- H19; apply H8; auto.
rewrite H18; inversion_clear H27;
 cut (notin x5 (nu (fun v : name => nu (x2 y v)))); 
 [ intro | auto ]; inversion_clear H27; auto.
rewrite H19; inversion_clear H30;
 cut (notin x5 (nu (fun v : name => nu (x3 y v)))); 
 [ intro | auto ]; inversion_clear H30; auto.

Qed.

(* SBUPTO is a strong late bisimulation. *)

Lemma UPTO_SB' :
 forall R : proc -> proc -> Prop,
 UpTo R -> Inclus (SBUPTO R) (Op_StBisim (SBUPTO R)).

Proof.

unfold Inclus in |- *; intros.
inversion_clear H0.
cut (NU_fun R n p1 p2);
 [ generalize p1 p2; generalize n; simple induction n0; intros | assumption ].

(* Base case *)

simpl in H0; inversion H0.
apply op_sb; split; intros.

inversion_clear H2; elim a; inversion_clear H3; inversion_clear H4; split;
 intros.

inversion_clear H2; inversion_clear H6; elim (H2 tau); intros;
 elim (H6 p4 H4); intros; inversion_clear H9.
unfold UpTo in H; elim (H x x0); intros; auto.
inversion_clear H12; inversion_clear H14; inversion_clear H15;
 inversion_clear H16.
elim (H15 x1 H10); intros.
inversion_clear H16; inversion_clear H5; inversion_clear H16.
elim (H5 tau); intros.
elim (H16 x2 H18); intros.
inversion_clear H22; exists x3; split; [ assumption | inversion_clear H19 ].

unfold SB_R_SB in H22; inversion_clear H22; inversion_clear H19;
 apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *;
 inversion_clear H22; inversion_clear H25.
exists x4; exists x5; split;
 [ apply TRANS with x1; assumption
 | split; [ assumption | apply TRANS with x2; assumption ] ].

inversion_clear H22; inversion_clear H19; inversion_clear H22;
 inversion_clear H25; apply sbupto with 1; simpl in |- *.
apply op_nu with x4 x5;
 [ apply TRANS with x1; assumption
 | apply TRANS with x2; assumption
 | intros; unfold SB_R_SB in |- *; exists (x4 z); exists (x5 z); split;
    [ apply REF | split; [ auto | apply REF ] ] ].

inversion_clear H5; inversion_clear H6; elim (H5 tau); intros;
 elim (H8 q1 H4); intros; inversion_clear H9.
unfold UpTo in H; elim (H x x0); intros; auto.
inversion_clear H12; inversion_clear H14; inversion_clear H15;
 inversion_clear H16.
elim (H17 x1 H10); intros.
inversion_clear H16; inversion_clear H2; inversion_clear H16.
elim (H2 tau); intros.
elim (H21 x2 H18); intros.
inversion_clear H22; exists x3; split; [ assumption | inversion_clear H19 ].

unfold SB_R_SB in H22; inversion_clear H22; inversion_clear H19;
 apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *;
 inversion_clear H22; inversion_clear H25.
exists x4; exists x5; split;
 [ apply TRANS with x2; assumption
 | split; [ assumption | apply TRANS with x1; assumption ] ].

inversion_clear H22; inversion_clear H19; inversion_clear H22;
 inversion_clear H25; apply sbupto with 1; simpl in |- *.
apply op_nu with x4 x5;
 [ apply TRANS with x2; assumption
 | apply TRANS with x1; assumption
 | intros; unfold SB_R_SB in |- *; exists (x4 z); exists (x5 z); split;
    [ apply REF | split; [ auto | apply REF ] ] ].

inversion_clear H2; inversion_clear H6; elim (H2 (Out n1 n2)); intros;
 elim (H6 p4 H4); intros; inversion_clear H9.
unfold UpTo in H; elim (H x x0); intros; auto.
inversion_clear H12; inversion_clear H14; inversion_clear H15;
 inversion_clear H16.
elim (H13 n1 n2); intros.
elim (H16 x1 H10); intros.
inversion_clear H19; inversion_clear H5; inversion_clear H19.
elim (H5 (Out n1 n2)); intros.
elim (H19 x2 H20); intros.
inversion_clear H24; exists x3; split;
 [ assumption
 | inversion_clear H21; inversion_clear H24; inversion_clear H21;
    inversion_clear H27 ].
apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *; exists x4;
 exists x5; split;
 [ apply TRANS with x1; assumption
 | split; [ assumption | apply TRANS with x2; assumption ] ].

inversion_clear H5; inversion_clear H6; elim (H5 (Out n1 n2)); intros;
 elim (H8 q1 H4); intros; inversion_clear H9.
unfold UpTo in H; elim (H x x0); intros; auto.
inversion_clear H12; inversion_clear H14; inversion_clear H15;
 inversion_clear H16.
elim (H13 n1 n2); intros.
elim (H18 x1 H10); intros.
inversion_clear H19; inversion_clear H2; inversion_clear H19.
elim (H2 (Out n1 n2)); intros.
elim (H23 x2 H20); intros.
inversion_clear H24; exists x3; split;
 [ assumption
 | inversion_clear H21; inversion_clear H24; inversion_clear H21;
    inversion_clear H27 ].
apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *; exists x4;
 exists x5; split;
 [ apply TRANS with x2; assumption
 | split; [ assumption | apply TRANS with x1; assumption ] ].

split; intros.

split; intros.

inversion_clear H2; inversion_clear H4; inversion_clear H5;
 inversion_clear H2; inversion_clear H5; inversion_clear H7; 
 elim (H5 x0); intros; elim (H7 p4 H3); intros; inversion_clear H10.
unfold UpTo in H; elim (H x x1); intros; auto; inversion_clear H13;
 inversion_clear H15.
elim (H13 x0); intros.
elim (H15 x2 H11); intros.
inversion_clear H18; inversion_clear H6; inversion_clear H18;
 inversion_clear H21.
elim (H18 x0); intros.
elim (H21 x3 H19); intros.
inversion_clear H24; exists x4; split;
 [ assumption
 | intro; cut (SB_R_SB R (x2 y) (x3 y)); [ intro | auto ];
    inversion_clear H24; inversion_clear H27; inversion_clear H24;
    inversion_clear H28 ].
apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *; exists x5;
 exists x6; split;
 [ apply TRANS with (x2 y); auto
 | split; [ assumption | apply TRANS with (x3 y); auto ] ].

inversion_clear H2; inversion_clear H4; inversion_clear H5;
 inversion_clear H6; inversion_clear H5; inversion_clear H7; 
 elim (H5 x0); intros; elim (H9 q1 H3); intros; inversion_clear H10.
unfold UpTo in H; elim (H x x1); intros; auto; inversion_clear H13;
 inversion_clear H15.
elim (H13 x0); intros.
elim (H17 x2 H11); intros.
inversion_clear H18; inversion_clear H2; inversion_clear H18;
 inversion_clear H21.
elim (H18 x0); intros.
elim (H23 x3 H19); intros.
inversion_clear H24; exists x4; split;
 [ assumption
 | intro; cut (SB_R_SB R (x3 y) (x2 y)); [ intro | auto ];
    inversion_clear H24; inversion_clear H27; inversion_clear H24;
    inversion_clear H28 ].
apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *; exists x5;
 exists x6; split;
 [ apply TRANS with (x3 y); auto
 | split; [ assumption | apply TRANS with (x2 y); auto ] ].

split; intros.

inversion_clear H2; inversion_clear H4; inversion_clear H5;
 inversion_clear H2; inversion_clear H5; inversion_clear H7; 
 elim (H8 x0); intros; elim (H7 p4 H3); intros; inversion_clear H10.
unfold UpTo in H; elim (H x x1); intros; auto; inversion_clear H13;
 inversion_clear H15; inversion_clear H16.
elim (H15 x0); intros.
elim (H16 x2 H11); intros.
inversion_clear H19; inversion_clear H6; inversion_clear H19;
 inversion_clear H22.
elim (H23 x0); intros.
elim (H22 x3 H20); intros.
inversion_clear H25; exists x4; split;
 [ assumption
 | intros;
    elim
     (unsat (par (nu p4) (par (nu x2) (par (nu x3) (nu x4)))) (cons y empty));
    intros; inversion_clear H29; inversion_clear H30; 
    inversion_clear H31; clear H33; inversion_clear H32; 
    inversion_clear H33; cut (SB_R_SB R (x2 x5) (x3 x5));
    [ intro; inversion_clear H33; inversion_clear H35; inversion_clear H33;
       inversion_clear H36
    | auto ] ].
elim (proc_exp x6 x5); elim (proc_exp x7 x5); intros; inversion_clear H36;
 inversion_clear H38; rewrite H41 in H35; rewrite H40 in H37.
elim (ho_proc_exp x2 y); elim (ho_proc_exp x3 y); intros; inversion_clear H38;
 inversion_clear H42.
elim (ho_proc_exp x8 y); elim (ho_proc_exp x9 y); intros; inversion_clear H42;
 inversion_clear H46.
elim
 (unsat
    (par (nu p4)
       (par (nu x4)
          (par (nu (fun n : name => nu (x10 n)))
             (par (nu (fun n : name => nu (x11 n)))
                (par (nu (fun n : name => nu (x12 n)))
                   (nu (fun n : name => nu (x13 n))))))))
    (cons y (cons x5 empty))); intros.
inversion_clear H46; inversion_clear H50; inversion_clear H51;
 inversion_clear H52; inversion_clear H53; inversion_clear H54; 
 clear H55; inversion_clear H56; inversion_clear H55.
apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *; exists (x12 x5 y);
 exists (x13 x5 y); split;
 [ apply TRANS with (x11 x5 y); apply L6_Light with x14; auto | split ].
inversion_clear H54; auto.
change
  (StBisim ((fun n : name => p4 x14) x5) ((fun n : name => x11 n x14) x5))
 in |- *; apply L6_Light with y; auto.
inversion_clear H25; apply notin_nu; intros; auto.
inversion_clear H38; apply notin_nu; intros; cut (notin y (nu (x11 z)));
 [ intro | auto ]; inversion_clear H58; auto.
rewrite <- H45; apply H12; auto.
rewrite H45; inversion_clear H54; auto.
inversion_clear H29; apply notin_nu; intros; auto.
apply proc_mono with y; rewrite <- H45; inversion_clear H31; auto.
inversion_clear H38; auto.
inversion_clear H54; auto.
inversion_clear H56; auto.
change
  (StBisim ((fun n : name => x11 n x14) x5) ((fun n : name => x12 n x14) x5))
 in |- *; apply L6_Light with y; auto.
inversion_clear H38; apply notin_nu; intros; cut (notin y (nu (x11 z)));
 [ intro | auto ]; inversion_clear H58; auto.
inversion_clear H47; apply notin_nu; intros; cut (notin y (nu (x12 z)));
 [ intro | auto ]; inversion_clear H58; auto.
rewrite <- H45; rewrite <- H48; apply L6_Light with x5; auto.
rewrite H45; inversion_clear H54; auto.
rewrite H48; inversion_clear H56; auto.
apply proc_mono with y; rewrite <- H45; inversion_clear H31; auto.
apply proc_mono with y; rewrite <- H48; inversion_clear H36; auto.
inversion_clear H38; auto.
inversion_clear H47; auto.
rewrite H40 in H33; rewrite H41 in H33; rewrite H48 in H33;
 rewrite H49 in H33.
elim (H (x12 y x5) (x13 y x5) H33); intros; clear H58.
cut (R (x12 x14 x5) (x13 x14 x5));
 [ intro
 | change
     (R ((fun n : name => x12 n x5) x14) ((fun n : name => x13 n x5) x14))
    in |- *; apply H55 with y; auto ].
elim (H (x12 x14 x5) (x13 x14 x5) H58); intros; clear H60.
cut (R (x12 x14 y) (x13 x14 y)); [ intro | apply H59 with x5; auto ].
elim (H (x12 x14 y) (x13 x14 y) H60); intros; clear H62.
cut (R (x12 x5 y) (x13 x5 y));
 [ intro; assumption
 | change (R ((fun n : name => x12 n y) x5) ((fun n : name => x13 n y) x5))
    in |- *; apply H61 with x14; auto ].
inversion_clear H56; apply notin_nu; intros; cut (notin x14 (nu (x12 z)));
 [ intro | auto ]; inversion_clear H63; auto.
inversion_clear H57; apply notin_nu; intros; cut (notin x14 (nu (x13 z)));
 [ intro | auto ]; inversion_clear H63; auto.
apply proc_mono with y; rewrite <- H48; inversion_clear H36; auto.
apply proc_mono with y; rewrite <- H49; inversion_clear H39; auto.
cut (notin x5 (nu (fun n : name => nu (x12 n))));
 [ intro; inversion_clear H60; auto
 | apply proc_mono with y; rewrite <- H48; assumption ].
cut (notin x5 (nu (fun n : name => nu (x13 n))));
 [ intro; inversion_clear H60; auto
 | apply proc_mono with y; rewrite <- H49; assumption ].
inversion_clear H47; auto.
inversion_clear H42; auto.
inversion_clear H47; apply notin_nu; intros; cut (notin y (nu (x12 z)));
 [ intro | auto ]; inversion_clear H59; auto.
inversion_clear H42; apply notin_nu; intros; cut (notin y (nu (x13 z)));
 [ intro | auto ]; inversion_clear H59; auto.
inversion_clear H56; apply notin_nu; intros; cut (notin x14 (nu (x12 z)));
 [ intro | auto ]; inversion_clear H59; auto.
inversion_clear H57; apply notin_nu; intros; cut (notin x14 (nu (x13 z)));
 [ intro | auto ]; inversion_clear H59; auto.
apply TRANS with (x10 x5 y); apply L6_Light with x14; auto.
inversion_clear H57; auto.
inversion_clear H53; auto.
change
  (StBisim ((fun n : name => x13 n x14) x5) ((fun n : name => x10 n x14) x5))
 in |- *; apply L6_Light with y; auto.
inversion_clear H42; apply notin_nu; intros; cut (notin y (nu (x13 z)));
 [ intro | auto ]; inversion_clear H58; auto.
inversion_clear H43; apply notin_nu; intros; cut (notin y (nu (x10 z)));
 [ intro | auto ]; inversion_clear H58; auto.
apply L6_Light with x5; auto.
rewrite <- H49; assumption.
rewrite <- H44; assumption.
rewrite <- H49; rewrite <- H44; assumption.
inversion_clear H57; auto.
inversion_clear H53; auto.
apply proc_mono with y; rewrite <- H49; inversion_clear H39; auto.
apply proc_mono with y; rewrite <- H44; inversion_clear H32; auto.
inversion_clear H42; auto.
inversion_clear H43; auto.
inversion_clear H53; auto.
change
  (StBisim ((fun n : name => x10 n x14) x5) ((fun n : name => x4 x14) x5))
 in |- *; apply L6_Light with y; auto.
inversion_clear H43; apply notin_nu; intros; cut (notin y (nu (x10 z)));
 [ intro | auto ]; inversion_clear H58; auto.
inversion_clear H28; apply notin_nu; intros; auto.
rewrite <- H44; apply H27; auto.
rewrite H44; inversion_clear H53; auto.
apply proc_mono with y; rewrite <- H44; inversion_clear H32; auto.
inversion_clear H34; apply notin_nu; intros; auto.
inversion_clear H43; auto.

inversion_clear H2; inversion_clear H4; inversion_clear H5;
 inversion_clear H6; inversion_clear H5; inversion_clear H7; 
 elim (H8 x0); intros; elim (H9 q1 H3); intros; inversion_clear H10.
unfold UpTo in H; elim (H x x1); intros; auto; inversion_clear H13;
 inversion_clear H15; inversion_clear H16.
elim (H15 x0); intros.
elim (H18 x2 H11); intros.
inversion_clear H19; inversion_clear H2; inversion_clear H19;
 inversion_clear H22.
elim (H23 x0); intros.
elim (H24 x3 H20); intros.
inversion_clear H25; exists x4; split;
 [ assumption
 | intros;
    elim
     (unsat (par (nu q1) (par (nu x2) (par (nu x3) (nu x4)))) (cons y empty));
    intros; inversion_clear H29; inversion_clear H30; 
    inversion_clear H31; clear H33; inversion_clear H32; 
    inversion_clear H33; cut (SB_R_SB R (x3 x5) (x2 x5));
    [ intro; inversion_clear H33; inversion_clear H35; inversion_clear H33;
       inversion_clear H36
    | auto ] ].
elim (proc_exp x6 x5); elim (proc_exp x7 x5); intros; inversion_clear H36;
 inversion_clear H38; rewrite H41 in H35; rewrite H40 in H37.
elim (ho_proc_exp x2 y); elim (ho_proc_exp x3 y); intros; inversion_clear H38;
 inversion_clear H42.
elim (ho_proc_exp x8 y); elim (ho_proc_exp x9 y); intros; inversion_clear H42;
 inversion_clear H46.
elim
 (unsat
    (par (nu q1)
       (par (nu x4)
          (par (nu (fun n : name => nu (x10 n)))
             (par (nu (fun n : name => nu (x11 n)))
                (par (nu (fun n : name => nu (x12 n)))
                   (nu (fun n : name => nu (x13 n))))))))
    (cons y (cons x5 empty))); intros.
inversion_clear H46; inversion_clear H50; inversion_clear H51;
 inversion_clear H52; inversion_clear H53; inversion_clear H54; 
 clear H55; inversion_clear H56; inversion_clear H55.
apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *; exists (x12 x5 y);
 exists (x13 x5 y); split;
 [ apply TRANS with (x10 x5 y); apply L6_Light with x14; auto | split ].
inversion_clear H53; auto.
change
  (StBisim ((fun n : name => x4 x14) x5) ((fun n : name => x10 n x14) x5))
 in |- *; apply L6_Light with y; auto.
inversion_clear H25; apply notin_nu; intros; auto.
inversion_clear H43; apply notin_nu; intros; cut (notin y (nu (x10 z)));
 [ intro | auto ]; inversion_clear H58; auto.
rewrite <- H44; apply H27; auto.
rewrite H44; inversion_clear H53; auto.
inversion_clear H34; apply notin_nu; intros; auto.
apply proc_mono with y; rewrite <- H44; inversion_clear H32; auto.
inversion_clear H43; auto.
inversion_clear H53; auto.
inversion_clear H56; auto.
change
  (StBisim ((fun n : name => x10 n x14) x5) ((fun n : name => x12 n x14) x5))
 in |- *; apply L6_Light with y; auto.
inversion_clear H43; apply notin_nu; intros; cut (notin y (nu (x10 z)));
 [ intro | auto ]; inversion_clear H58; auto.
inversion_clear H47; apply notin_nu; intros; cut (notin y (nu (x12 z)));
 [ intro | auto ]; inversion_clear H58; auto.
rewrite <- H44; rewrite <- H48; apply L6_Light with x5; auto.
rewrite H44; inversion_clear H53; auto.
rewrite H48; inversion_clear H56; auto.
apply proc_mono with y; rewrite <- H44; inversion_clear H32; auto.
apply proc_mono with y; rewrite <- H48; inversion_clear H36; auto.
inversion_clear H43; auto.
inversion_clear H47; auto.
rewrite H40 in H33; rewrite H41 in H33; rewrite H48 in H33;
 rewrite H49 in H33.
elim (H (x12 y x5) (x13 y x5) H33); intros; clear H58.
cut (R (x12 x14 x5) (x13 x14 x5));
 [ intro
 | change
     (R ((fun n : name => x12 n x5) x14) ((fun n : name => x13 n x5) x14))
    in |- *; apply H55 with y; auto ].
elim (H (x12 x14 x5) (x13 x14 x5) H58); intros; clear H60.
cut (R (x12 x14 y) (x13 x14 y)); [ intro | apply H59 with x5; auto ].
elim (H (x12 x14 y) (x13 x14 y) H60); intros; clear H62.
cut (R (x12 x5 y) (x13 x5 y));
 [ intro; assumption
 | change (R ((fun n : name => x12 n y) x5) ((fun n : name => x13 n y) x5))
    in |- *; apply H61 with x14; auto ].
inversion_clear H56; apply notin_nu; intros; cut (notin x14 (nu (x12 z)));
 [ intro | auto ]; inversion_clear H63; auto.
inversion_clear H57; apply notin_nu; intros; cut (notin x14 (nu (x13 z)));
 [ intro | auto ]; inversion_clear H63; auto.
apply proc_mono with y; rewrite <- H48; inversion_clear H36; auto.
apply proc_mono with y; rewrite <- H49; inversion_clear H39; auto.
cut (notin x5 (nu (fun n : name => nu (x12 n))));
 [ intro; inversion_clear H60; auto
 | apply proc_mono with y; rewrite <- H48; assumption ].
cut (notin x5 (nu (fun n : name => nu (x13 n))));
 [ intro; inversion_clear H60; auto
 | apply proc_mono with y; rewrite <- H49; assumption ].
inversion_clear H47; auto.
inversion_clear H42; auto.
inversion_clear H47; apply notin_nu; intros; cut (notin y (nu (x12 z)));
 [ intro | auto ]; inversion_clear H59; auto.
inversion_clear H42; apply notin_nu; intros; cut (notin y (nu (x13 z)));
 [ intro | auto ]; inversion_clear H59; auto.
inversion_clear H56; apply notin_nu; intros; cut (notin x14 (nu (x12 z)));
 [ intro | auto ]; inversion_clear H59; auto.
inversion_clear H57; apply notin_nu; intros; cut (notin x14 (nu (x13 z)));
 [ intro | auto ]; inversion_clear H59; auto.
apply TRANS with (x11 x5 y); apply L6_Light with x14; auto.
inversion_clear H57; auto.
inversion_clear H54; auto.
change
  (StBisim ((fun n : name => x13 n x14) x5) ((fun n : name => x11 n x14) x5))
 in |- *; apply L6_Light with y; auto.
inversion_clear H42; apply notin_nu; intros; cut (notin y (nu (x13 z)));
 [ intro | auto ]; inversion_clear H58; auto.
inversion_clear H38; apply notin_nu; intros; cut (notin y (nu (x11 z)));
 [ intro | auto ]; inversion_clear H58; auto.
apply L6_Light with x5; auto.
rewrite <- H49; assumption.
rewrite <- H45; assumption.
rewrite <- H49; rewrite <- H45; assumption.
inversion_clear H57; auto.
inversion_clear H54; auto.
apply proc_mono with y; rewrite <- H49; inversion_clear H39; auto.
apply proc_mono with y; rewrite <- H45; inversion_clear H31; auto.
inversion_clear H42; auto.
inversion_clear H38; auto.
inversion_clear H54; auto.
change
  (StBisim ((fun n : name => x11 n x14) x5) ((fun n : name => q1 x14) x5))
 in |- *; apply L6_Light with y; auto.
inversion_clear H38; apply notin_nu; intros; cut (notin y (nu (x11 z)));
 [ intro | auto ]; inversion_clear H58; auto.
inversion_clear H28; apply notin_nu; intros; auto.
rewrite <- H45; apply H12; auto.
rewrite H45; inversion_clear H54; auto.
apply proc_mono with y; rewrite <- H45; inversion_clear H31; auto.
inversion_clear H29; apply notin_nu; intros; auto.
inversion_clear H38; auto.

(* Inductive step *)

simpl in H2; inversion H2.
apply op_sb; split; intros.

elim a; intros; split; intros.

inversion_clear H3; inversion_clear H9.
elim (H3 tau); intros.
elim (H9 p4 H8); intros.
inversion_clear H12; inversion H13.
elim (unsat (par (nu p') (par (nu q') (nu p6))) l); intros.
inversion_clear H18; inversion_clear H19; inversion_clear H21.
cut (ftrans (p' x0) tau (p6 x0));
 [ intro; cut (NU_fun R n1 (p' x0) (q' x0)); [ intro | auto ]
 | apply H15; auto; try apply f_act_notin_tau ].
cut (Op_StBisim (SBUPTO R) (p' x0) (q' x0)); [ intro | auto ].
inversion_clear H24; inversion_clear H25.
elim (H24 tau); intros.
elim (H25 (p6 x0) H21); intros; inversion_clear H28.
elim (proc_exp x1 x0); intros; inversion_clear H28; rewrite H32 in H29;
 rewrite H32 in H30.
inversion_clear H4; inversion_clear H28.
elim (H4 tau); intros; cut (ftrans (nu q') tau (nu x2));
 [ intro
 | apply fRES with empty; intros;
    change (ftrans (q' y) ((fun _ : name => tau) y) (x2 y)) in |- *;
    apply FTR_L3 with x0; auto;
    try (unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau) ].
elim (H28 (nu x2) H35); intros; inversion_clear H36.
exists x3; split; [ assumption | inversion_clear H30 ].
apply sbupto with (S n2); simpl in |- *; apply op_nu with p6 x2;
 [ rewrite H17; assumption
 | assumption
 | intros; apply NU_FUN_RW with x0; auto ].

inversion_clear H4; inversion_clear H9.
elim (H4 tau); intros.
elim (H11 q1 H8); intros.
inversion_clear H12; inversion H13.
elim (unsat (par (nu p') (par (nu q') (nu p5))) l); intros.
inversion_clear H18; inversion_clear H19; inversion_clear H21.
cut (ftrans (q' x0) tau (p5 x0));
 [ intro; cut (NU_fun R n1 (p' x0) (q' x0)); [ intro | auto ]
 | apply H15; auto; try apply f_act_notin_tau ].
cut (Op_StBisim (SBUPTO R) (p' x0) (q' x0)); [ intro | auto ].
inversion_clear H24; inversion_clear H25.
elim (H24 tau); intros.
elim (H27 (p5 x0) H21); intros; inversion_clear H28.
elim (proc_exp x1 x0); intros; inversion_clear H28; rewrite H32 in H29;
 rewrite H32 in H30.
inversion_clear H3; inversion_clear H28.
elim (H3 tau); intros; cut (ftrans (nu p') tau (nu x2));
 [ intro
 | apply fRES with empty; intros;
    change (ftrans (p' y) ((fun _ : name => tau) y) (x2 y)) in |- *;
    apply FTR_L3 with x0; auto;
    try (unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau) ].
elim (H34 (nu x2) H35); intros; inversion_clear H36.
exists x3; split; [ assumption | inversion_clear H30 ].
apply sbupto with (S n2); simpl in |- *; apply op_nu with x2 p5;
 [ assumption
 | rewrite H17; assumption
 | intros; apply NU_FUN_RW with x0; auto ].

inversion_clear H3; inversion_clear H9.
elim (H3 (Out n2 n3)); intros.
elim (H9 p4 H8); intros.
inversion_clear H12; inversion H13.
elim (unsat (par (nu p') (par (nu q') (nu p6))) (cons n2 (cons n3 l)));
 intros.
inversion_clear H18; inversion_clear H19; inversion_clear H20;
 inversion_clear H21; inversion_clear H22.
cut (ftrans (p' x0) (Out n2 n3) (p6 x0));
 [ intro; cut (NU_fun R n1 (p' x0) (q' x0)); [ intro | auto ]
 | apply H15; auto; try (apply f_act_notin_Out; auto) ].
cut (Op_StBisim (SBUPTO R) (p' x0) (q' x0)); [ intro | auto ].
inversion_clear H26; inversion_clear H27.
elim (H26 (Out n2 n3)); intros.
elim (H27 (p6 x0) H22); intros; inversion_clear H30.
elim (proc_exp x1 x0); intros; inversion_clear H30; rewrite H34 in H31;
 rewrite H34 in H32.
inversion_clear H4; inversion_clear H30.
elim (H4 (Out n2 n3)); intros; cut (ftrans (nu q') (Out n2 n3) (nu x2));
 [ intro
 | apply fRES with empty; intros;
    change (ftrans (q' y) ((fun _ : name => Out n2 n3) y) (x2 y)) in |- *;
    apply FTR_L3 with x0; auto;
    try (unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto) ].
elim (H30 (nu x2) H37); intros; inversion_clear H38.
exists x3; split; [ assumption | inversion_clear H32 ].
apply sbupto with (S n4); simpl in |- *; apply op_nu with p6 x2;
 [ rewrite H17; assumption
 | assumption
 | intros; apply NU_FUN_RW with x0; auto ].
inversion_clear H40; auto.
inversion_clear H40; auto.

inversion_clear H4; inversion_clear H9.
elim (H4 (Out n2 n3)); intros.
elim (H11 q1 H8); intros.
inversion_clear H12; inversion H13.
elim (unsat (par (nu p') (par (nu q') (nu p5))) (cons n2 (cons n3 l)));
 intros.
inversion_clear H18; inversion_clear H19; inversion_clear H20;
 inversion_clear H21; inversion_clear H22.
cut (ftrans (q' x0) (Out n2 n3) (p5 x0));
 [ intro; cut (NU_fun R n1 (p' x0) (q' x0)); [ intro | auto ]
 | apply H15; auto; try (apply f_act_notin_Out; auto) ].
cut (Op_StBisim (SBUPTO R) (p' x0) (q' x0)); [ intro | auto ].
inversion_clear H26; inversion_clear H27.
elim (H26 (Out n2 n3)); intros.
elim (H29 (p5 x0) H22); intros; inversion_clear H30.
elim (proc_exp x1 x0); intros; inversion_clear H30; rewrite H34 in H31;
 rewrite H34 in H32.
inversion_clear H3; inversion_clear H30.
elim (H3 (Out n2 n3)); intros; cut (ftrans (nu p') (Out n2 n3) (nu x2));
 [ intro
 | apply fRES with empty; intros;
    change (ftrans (p' y) ((fun _ : name => Out n2 n3) y) (x2 y)) in |- *;
    apply FTR_L3 with x0; auto;
    try (unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto) ].
elim (H36 (nu x2) H37); intros; inversion_clear H38.
exists x3; split; [ assumption | inversion_clear H32 ].
apply sbupto with (S n4); simpl in |- *; apply op_nu with x2 p5;
 [ assumption
 | rewrite H17; assumption
 | intros; apply NU_FUN_RW with x0; auto ].
inversion_clear H40; auto.
inversion_clear H40; auto.

split; intros.

split; intros.

inversion_clear H3; inversion_clear H9; inversion_clear H10.
elim (H9 x); intros.
elim (H10 p4 H8); intros.
inversion_clear H13; inversion H14.
elim
 (unsat (par (nu p') (par (nu q') (nu (fun z : name => nu (p6 z)))))
    (cons x l)); intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21;
 inversion_clear H22.
cut (btrans (p' x1) (In x) (p6 x1));
 [ intro; cut (NU_fun R n1 (p' x1) (q' x1)); [ intro | auto ]
 | apply H16; auto; try (apply b_act_notin_In; auto) ].
cut (Op_StBisim (SBUPTO R) (p' x1) (q' x1)); [ intro | auto ].
inversion_clear H26; inversion_clear H27; inversion_clear H28.
elim (H27 x); intros.
elim (H28 (p6 x1) H22); intros; inversion_clear H31.
elim (ho_proc_exp x2 x1); intros; inversion_clear H31; rewrite H35 in H32;
 rewrite H35 in H33.
inversion_clear H4; inversion_clear H31; inversion_clear H36.
elim (H31 x); intros.
cut (btrans (nu q') (In x) (fun u : name => nu (fun v : name => x3 v u)));
 [ intro
 | apply bRES with (cons x empty); intros; inversion_clear H42;
    change (btrans (q' y) ((fun _ : name => In x) y) (x3 y)) in |- *;
    apply BTR_L3 with x1; auto;
    try (unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto) ].
elim (H36 (fun u : name => nu (fun v : name => x3 v u)) H39); intros;
 inversion_clear H40.
exists x4; split; [ assumption | idtac ].
intro; elim (LEM_name x1 y); intros.

rewrite <- H40;
 elim
  (unsat
     (par (nu (fun u : name => nu (fun v : name => p6 v u)))
        (nu (fun u : name => nu (fun v : name => x3 v u)))) 
     (cons x1 empty)); intros; inversion_clear H43; 
 inversion_clear H44; inversion_clear H45; clear H47.
elim (H33 x5); intros.
apply sbupto with (S n2); simpl in |- *;
 apply op_nu with (fun v : name => p6 v x1) (fun v : name => x3 v x1); 
 intros; auto.
cut (nu (fun v : name => p6 v x1) = x0 x1);
 [ intro; rewrite H47; auto | rewrite <- H18; trivial ].
elim
 (unsat
    (par (nu (fun u : name => nu (fun v : name => p6 v u)))
       (nu (fun u : name => nu (fun v : name => x3 v u))))
    (cons x1 (cons x5 (cons z empty)))); intros; inversion_clear H49;
 inversion_clear H50; inversion_clear H51; inversion_clear H53;
 inversion_clear H54; clear H55.
change
  (NU_fun R n2 ((fun n : name => p6 n x1) z) ((fun n : name => x3 n x1) z))
 in |- *; apply NU_FUN_RW with x6; auto.
inversion_clear H49; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => p6 v x1))); [ intro | auto ];
 inversion_clear H55; auto.
inversion_clear H52; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => x3 v x1))); [ intro | auto ];
 inversion_clear H55; auto.
apply NU_FUN_RW with x5; auto.
inversion_clear H43; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => p6 v z0))); [ intro | auto ];
 inversion_clear H55; auto.
inversion_clear H46; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => x3 v z0))); [ intro | auto ];
 inversion_clear H55; auto.
change
  (NU_fun R n2 ((fun n : name => p6 n x5) x6) ((fun n : name => x3 n x5) x6))
 in |- *; apply NU_FUN_RW with x1; auto.
inversion_clear H24; apply notin_nu; intros; cut (notin x1 (nu (p6 z0)));
 [ intro | auto ]; inversion_clear H55; auto.
inversion_clear H34; apply notin_nu; intros; cut (notin x1 (nu (x3 z0)));
 [ intro | auto ]; inversion_clear H55; auto.
inversion_clear H49; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => p6 v x5))); [ intro | auto ];
 inversion_clear H55; auto.
inversion_clear H52; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => x3 v x5))); [ intro | auto ];
 inversion_clear H55; auto.
inversion_clear H24; auto.
inversion_clear H34; auto.

elim (H33 y); intros.
apply sbupto with (S n2); simpl in |- *;
 apply op_nu with (fun v : name => p6 v y) (fun v : name => x3 v y); 
 intros; auto.
cut (nu (fun v : name => p6 v y) = x0 y);
 [ intro; rewrite H44; auto | rewrite <- H18; trivial ].
change
  (NU_fun R n2 ((fun n : name => p6 n y) z) ((fun n : name => x3 n y) z))
 in |- *; apply NU_FUN_RW with x1; auto.
inversion_clear H24; apply notin_nu; intros; cut (notin x1 (nu (p6 z0)));
 [ intro | auto ]; inversion_clear H47; auto.
inversion_clear H34; apply notin_nu; intros; cut (notin x1 (nu (x3 z0)));
 [ intro | auto ]; inversion_clear H47; auto.

inversion_clear H4; inversion_clear H9; inversion_clear H10.
elim (H9 x); intros.
elim (H12 q1 H8); intros.
inversion_clear H13; inversion H14.
elim
 (unsat (par (nu p') (par (nu q') (nu (fun z : name => nu (p5 z)))))
    (cons x l)); intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21;
 inversion_clear H22.
cut (btrans (q' x1) (In x) (p5 x1));
 [ intro; cut (NU_fun R n1 (p' x1) (q' x1)); [ intro | auto ]
 | apply H16; auto; try (apply b_act_notin_In; auto) ].
cut (Op_StBisim (SBUPTO R) (p' x1) (q' x1)); [ intro | auto ].
inversion_clear H26; inversion_clear H27; inversion_clear H28.
elim (H27 x); intros.
elim (H30 (p5 x1) H22); intros; inversion_clear H31.
elim (ho_proc_exp x2 x1); intros; inversion_clear H31; rewrite H35 in H32;
 rewrite H35 in H33.
inversion_clear H3; inversion_clear H31; inversion_clear H36.
elim (H31 x); intros.
cut (btrans (nu p') (In x) (fun u : name => nu (fun v : name => x3 v u)));
 [ intro
 | apply bRES with (cons x empty); intros; inversion_clear H42;
    change (btrans (p' y) ((fun _ : name => In x) y) (x3 y)) in |- *;
    apply BTR_L3 with x1; auto;
    try (unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto) ].
elim (H38 (fun u : name => nu (fun v : name => x3 v u)) H39); intros;
 inversion_clear H40.
exists x4; split; [ assumption | idtac ].
intro; elim (LEM_name x1 y); intros.

rewrite <- H40;
 elim
  (unsat
     (par (nu (fun u : name => nu (fun v : name => p5 v u)))
        (nu (fun u : name => nu (fun v : name => x3 v u)))) 
     (cons x1 empty)); intros; inversion_clear H43; 
 inversion_clear H44; inversion_clear H45; clear H47.
elim (H33 x5); intros.
apply sbupto with (S n2); simpl in |- *;
 apply op_nu with (fun v : name => x3 v x1) (fun v : name => p5 v x1); 
 intros; auto.
cut (nu (fun v : name => p5 v x1) = x0 x1);
 [ intro; rewrite H47; auto | rewrite <- H18; trivial ].
elim
 (unsat
    (par (nu (fun u : name => nu (fun v : name => p5 v u)))
       (nu (fun u : name => nu (fun v : name => x3 v u))))
    (cons x1 (cons x5 (cons z empty)))); intros; inversion_clear H49;
 inversion_clear H50; inversion_clear H51; inversion_clear H53;
 inversion_clear H54; clear H55.
change
  (NU_fun R n2 ((fun n : name => x3 n x1) z) ((fun n : name => p5 n x1) z))
 in |- *; apply NU_FUN_RW with x6; auto.
inversion_clear H52; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => x3 v x1))); [ intro | auto ];
 inversion_clear H55; auto.
inversion_clear H49; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => p5 v x1))); [ intro | auto ];
 inversion_clear H55; auto.
apply NU_FUN_RW with x5; auto.
inversion_clear H46; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => x3 v z0))); [ intro | auto ];
 inversion_clear H55; auto.
inversion_clear H43; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => p5 v z0))); [ intro | auto ];
 inversion_clear H55; auto.
change
  (NU_fun R n2 ((fun n : name => x3 n x5) x6) ((fun n : name => p5 n x5) x6))
 in |- *; apply NU_FUN_RW with x1; auto.
inversion_clear H34; apply notin_nu; intros; cut (notin x1 (nu (x3 z0)));
 [ intro | auto ]; inversion_clear H55; auto.
inversion_clear H24; apply notin_nu; intros; cut (notin x1 (nu (p5 z0)));
 [ intro | auto ]; inversion_clear H55; auto.
inversion_clear H52; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => x3 v x5))); [ intro | auto ];
 inversion_clear H55; auto.
inversion_clear H49; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => p5 v x5))); [ intro | auto ];
 inversion_clear H55; auto.
inversion_clear H34; auto.
inversion_clear H24; auto.

elim (H33 y); intros.
apply sbupto with (S n2); simpl in |- *;
 apply op_nu with (fun v : name => x3 v y) (fun v : name => p5 v y); 
 intros; auto.
cut (nu (fun v : name => p5 v y) = x0 y);
 [ intro; rewrite H44; auto | rewrite <- H18; trivial ].
change
  (NU_fun R n2 ((fun n : name => x3 n y) z) ((fun n : name => p5 n y) z))
 in |- *; apply NU_FUN_RW with x1; auto.
inversion_clear H34; apply notin_nu; intros; cut (notin x1 (nu (x3 z0)));
 [ intro | auto ]; inversion_clear H47; auto.
inversion_clear H24; apply notin_nu; intros; cut (notin x1 (nu (p5 z0)));
 [ intro | auto ]; inversion_clear H47; auto.

split; intros.

inversion_clear H3; inversion_clear H9; inversion_clear H10.
elim (H11 x); intros.
elim (H10 p4 H8); intros.
inversion_clear H13; inversion H14.

elim
 (unsat
    (par (nu p')
       (par (nu q') (par p0 (par p3 (nu (fun z : name => nu (p6 z)))))))
    (cons x l)); intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21;
 inversion_clear H22; inversion_clear H24; inversion_clear H25.
cut (btrans (p' x1) (bOut x) (p6 x1));
 [ intro; cut (NU_fun R n1 (p' x1) (q' x1)); [ intro | auto ]
 | apply H16; auto; try (apply b_act_notin_bOut; auto) ].
cut (Op_StBisim (SBUPTO R) (p' x1) (q' x1)); [ intro | auto ].
inversion_clear H28; inversion_clear H29; inversion_clear H30.
elim (H31 x); intros.
elim (H30 (p6 x1) H25); intros; inversion_clear H33.
elim (ho_proc_exp x2 x1); intros; inversion_clear H33; rewrite H37 in H34;
 rewrite H37 in H35.
inversion_clear H4; inversion_clear H33; inversion_clear H38.
elim (H39 x); intros.
cut (btrans (nu q') (bOut x) (fun u : name => nu (fun v : name => x3 v u)));
 [ intro
 | apply bRES with (cons x empty); intros; inversion_clear H44;
    change (btrans (q' y) ((fun _ : name => bOut x) y) (x3 y)) in |- *;
    apply BTR_L3 with x1; auto;
    try (unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto) ].
elim (H38 (fun u : name => nu (fun v : name => x3 v u)) H41); intros;
 inversion_clear H42.
exists x4; split; [ assumption | idtac ].
intros;
 elim
  (unsat
     (par (nu p4)
        (par (nu x4)
           (par (nu (fun u : name => nu (fun v : name => p6 v u)))
              (nu (fun u : name => nu (fun v : name => x3 v u))))))
     (cons x1 empty)); intros; inversion_clear H46; 
 inversion_clear H47; inversion_clear H48; clear H50; 
 inversion_clear H49; inversion_clear H50.
elim (H35 x5); intros.
apply sbupto with (S n2); apply NU_FUN_RW with x1; auto.
elim (BTR_L1 p0 p4 (bOut x) x1 H22 H8); intros; assumption.
elim (BTR_L1 p3 x4 (bOut x) x1 H24 H43); intros; assumption.
simpl in |- *;
 apply op_nu with (fun v : name => p6 v x1) (fun v : name => x3 v x1); 
 intros; auto.
cut (nu (fun v : name => p6 v x1) = x0 x1);
 [ intro; rewrite H52; apply H15; auto | rewrite <- H18; trivial ].
elim (BTR_L1 p0 p4 (bOut x) x1 H22 H8); intros; assumption.
elim (BTR_L1 (nu p') x0 (bOut x) x1 H19 H14); intros; assumption.
apply H44; auto.
inversion_clear H36; do 2 (apply notin_nu; intros);
 cut (notin x1 (nu (x3 z0))); [ intro | auto ]; inversion_clear H54; 
 auto.
elim (BTR_L1 p3 x4 (bOut x) x1 H24 H43); intros; assumption.
elim
 (unsat
    (par (nu (fun u : name => nu (fun v : name => p6 v u)))
       (nu (fun u : name => nu (fun v : name => x3 v u))))
    (cons x1 (cons x5 (cons z empty)))); intros; inversion_clear H54;
 inversion_clear H55; inversion_clear H56; inversion_clear H58;
 inversion_clear H59; clear H60.
change
  (NU_fun R n2 ((fun n : name => p6 n x1) z) ((fun n : name => x3 n x1) z))
 in |- *; apply NU_FUN_RW with x6; auto.
inversion_clear H54; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => p6 v x1))); [ intro | auto ];
 inversion_clear H60; auto.
inversion_clear H57; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => x3 v x1))); [ intro | auto ];
 inversion_clear H60; auto.
apply NU_FUN_RW with x5; auto.
inversion_clear H49; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => p6 v z0))); [ intro | auto ];
 inversion_clear H60; auto.
inversion_clear H51; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => x3 v z0))); [ intro | auto ];
 inversion_clear H60; auto.
change
  (NU_fun R n2 ((fun n : name => p6 n x5) x6) ((fun n : name => x3 n x5) x6))
 in |- *; apply NU_FUN_RW with x1; auto.
inversion_clear H26; apply notin_nu; intros; cut (notin x1 (nu (p6 z0)));
 [ intro | auto ]; inversion_clear H60; auto.
inversion_clear H36; apply notin_nu; intros; cut (notin x1 (nu (x3 z0)));
 [ intro | auto ]; inversion_clear H60; auto.
inversion_clear H54; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => p6 v x5))); [ intro | auto ];
 inversion_clear H60; auto.
inversion_clear H57; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => x3 v x5))); [ intro | auto ];
 inversion_clear H60; auto.
inversion_clear H26; auto.
inversion_clear H36; auto.
inversion_clear H49; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => p6 v z))); [ intro | auto ];
 inversion_clear H52; auto.
inversion_clear H51; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => x3 v z))); [ intro | auto ];
 inversion_clear H52; auto.

elim (unsat (par (nu p') (par (nu q') (par p0 (par p3 (nu x0))))) (cons x l));
 intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21;
 inversion_clear H22; inversion_clear H24; inversion_clear H25.
cut (ftrans (p' x2) (Out x x2) (x0 x2));
 [ intro; cut (NU_fun R n1 (p' x2) (q' x2)); [ intro | auto ]
 | apply H17; auto; try (apply f_act_notin_Out; auto) ].
cut (Op_StBisim (SBUPTO R) (p' x2) (q' x2)); [ intro | auto ].
inversion_clear H28; inversion_clear H29.
elim (H28 (Out x x2)); intros.
elim (H29 (x0 x2) H25); intros; inversion_clear H32.
elim (proc_exp x3 x2); intros; inversion_clear H32; rewrite H36 in H33;
 rewrite H36 in H34.
inversion_clear H4; inversion_clear H32; inversion_clear H37.
elim (H38 x); intros.
cut (btrans (nu q') (bOut x) x4);
 [ intro
 | apply OPEN with (cons x empty); intros; inversion_clear H43;
    apply FTR_L3 with x2; auto;
    try (unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto) ].
elim (H37 x4 H40); intros; inversion_clear H41.
exists x5; split; [ assumption | intros; inversion_clear H34 ].
generalize H45; clear H45; case n2; intros; simpl in H45; inversion_clear H45.
inversion_clear H34; inversion_clear H45; inversion_clear H46.

apply sbupto with 0; apply NU_FUN_RW with x2; auto.
elim (BTR_L1 p0 p4 (bOut x) x2 H22 H8); intros; assumption.
elim (BTR_L1 p3 x5 (bOut x) x2 H24 H42); intros; assumption.
simpl in |- *; unfold SB_R_SB in |- *; exists x6; exists x7; split;
 [ apply TRANS with (x0 x2); auto
 | split; [ assumption | apply TRANS with (x4 x2); auto ] ].
apply H15; auto; elim (BTR_L1 p0 p4 (bOut x) x2 H22 H8); intros; assumption.
apply H43; auto; elim (BTR_L1 p3 x5 (bOut x) x2 H24 H42); intros; assumption.

apply sbupto with (S n3); apply NU_FUN_RW with x2; auto.
elim (BTR_L1 p0 p4 (bOut x) x2 H22 H8); intros; assumption.
elim (BTR_L1 p3 x5 (bOut x) x2 H24 H42); intros; assumption.
simpl in |- *; apply op_nu with p'0 q'0; intros; auto.
apply TRANS with (x0 x2);
 [ apply H15; auto; elim (BTR_L1 p0 p4 (bOut x) x2 H22 H8); intros;
    assumption
 | assumption ].
apply TRANS with (x4 x2);
 [ assumption
 | apply H43; auto; elim (BTR_L1 p3 x5 (bOut x) x2 H24 H42); intros;
    assumption ].

inversion_clear H4; inversion_clear H9; inversion_clear H10.
elim (H11 x); intros.
elim (H12 q1 H8); intros.
inversion_clear H13; inversion H14.

elim
 (unsat
    (par (nu p')
       (par (nu q') (par p0 (par p3 (nu (fun z : name => nu (p5 z)))))))
    (cons x l)); intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21;
 inversion_clear H22; inversion_clear H24; inversion_clear H25.
cut (btrans (q' x1) (bOut x) (p5 x1));
 [ intro; cut (NU_fun R n1 (p' x1) (q' x1)); [ intro | auto ]
 | apply H16; auto; try (apply b_act_notin_bOut; auto) ].
cut (Op_StBisim (SBUPTO R) (p' x1) (q' x1)); [ intro | auto ].
inversion_clear H28; inversion_clear H29; inversion_clear H30.
elim (H31 x); intros.
elim (H32 (p5 x1) H25); intros; inversion_clear H33.
elim (ho_proc_exp x2 x1); intros; inversion_clear H33; rewrite H37 in H34;
 rewrite H37 in H35.
inversion_clear H3; inversion_clear H33; inversion_clear H38.
elim (H39 x); intros.
cut (btrans (nu p') (bOut x) (fun u : name => nu (fun v : name => x3 v u)));
 [ intro
 | apply bRES with (cons x empty); intros; inversion_clear H44;
    change (btrans (p' y) ((fun _ : name => bOut x) y) (x3 y)) in |- *;
    apply BTR_L3 with x1; auto;
    try (unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto) ].
elim (H40 (fun u : name => nu (fun v : name => x3 v u)) H41); intros;
 inversion_clear H42.
exists x4; split; [ assumption | idtac ].
intros;
 elim
  (unsat
     (par (nu p4)
        (par (nu x4)
           (par (nu (fun u : name => nu (fun v : name => p5 v u)))
              (nu (fun u : name => nu (fun v : name => x3 v u))))))
     (cons x1 empty)); intros; inversion_clear H46; 
 inversion_clear H47; inversion_clear H48; clear H50; 
 inversion_clear H49; inversion_clear H50.
elim (H35 x5); intros.
apply sbupto with (S n2); apply NU_FUN_RW with x1; auto.
elim (BTR_L1 p0 x4 (bOut x) x1 H22 H43); intros; assumption.
elim (BTR_L1 p3 q1 (bOut x) x1 H24 H8); intros; assumption.
simpl in |- *;
 apply op_nu with (fun v : name => x3 v x1) (fun v : name => p5 v x1); 
 intros; auto.
apply H44; auto.
elim (BTR_L1 p0 x4 (bOut x) x1 H22 H43); intros; assumption.
inversion_clear H36; do 2 (apply notin_nu; intros);
 cut (notin x1 (nu (x3 z0))); [ intro | auto ]; inversion_clear H54; 
 auto.
cut (nu (fun v : name => p5 v x1) = x0 x1);
 [ intro; rewrite H52; apply H15; auto | rewrite <- H18; trivial ].
elim (BTR_L1 (nu q') x0 (bOut x) x1 H21 H14); intros; assumption.
elim (BTR_L1 p3 q1 (bOut x) x1 H24 H8); intros; assumption.
elim
 (unsat
    (par (nu (fun u : name => nu (fun v : name => p5 v u)))
       (nu (fun u : name => nu (fun v : name => x3 v u))))
    (cons x1 (cons x5 (cons z empty)))); intros; inversion_clear H54;
 inversion_clear H55; inversion_clear H56; inversion_clear H58;
 inversion_clear H59; clear H60.
change
  (NU_fun R n2 ((fun n : name => x3 n x1) z) ((fun n : name => p5 n x1) z))
 in |- *; apply NU_FUN_RW with x6; auto.
inversion_clear H57; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => x3 v x1))); [ intro | auto ];
 inversion_clear H60; auto.
inversion_clear H54; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => p5 v x1))); [ intro | auto ];
 inversion_clear H60; auto.
apply NU_FUN_RW with x5; auto.
inversion_clear H51; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => x3 v z0))); [ intro | auto ];
 inversion_clear H60; auto.
inversion_clear H49; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => p5 v z0))); [ intro | auto ];
 inversion_clear H60; auto.
change
  (NU_fun R n2 ((fun n : name => x3 n x5) x6) ((fun n : name => p5 n x5) x6))
 in |- *; apply NU_FUN_RW with x1; auto.
inversion_clear H36; apply notin_nu; intros; cut (notin x1 (nu (x3 z0)));
 [ intro | auto ]; inversion_clear H60; auto.
inversion_clear H26; apply notin_nu; intros; cut (notin x1 (nu (p5 z0)));
 [ intro | auto ]; inversion_clear H60; auto.
inversion_clear H57; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => x3 v x5))); [ intro | auto ];
 inversion_clear H60; auto.
inversion_clear H54; apply notin_nu; intros;
 cut (notin x6 (nu (fun v : name => p5 v x5))); [ intro | auto ];
 inversion_clear H60; auto.
inversion_clear H36; auto.
inversion_clear H26; auto.
inversion_clear H51; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => x3 v z))); [ intro | auto ];
 inversion_clear H52; auto.
inversion_clear H49; apply notin_nu; intros;
 cut (notin x5 (nu (fun v : name => p5 v z))); [ intro | auto ];
 inversion_clear H52; auto.

elim (unsat (par (nu p') (par (nu q') (par p0 (par p3 (nu x0))))) (cons x l));
 intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21;
 inversion_clear H22; inversion_clear H24; inversion_clear H25.
cut (ftrans (q' x2) (Out x x2) (x0 x2));
 [ intro; cut (NU_fun R n1 (p' x2) (q' x2)); [ intro | auto ]
 | apply H17; auto; try (apply f_act_notin_Out; auto) ].
cut (Op_StBisim (SBUPTO R) (p' x2) (q' x2)); [ intro | auto ].
inversion_clear H28; inversion_clear H29.
elim (H28 (Out x x2)); intros.
elim (H31 (x0 x2) H25); intros; inversion_clear H32.
elim (proc_exp x3 x2); intros; inversion_clear H32; rewrite H36 in H33;
 rewrite H36 in H34.
inversion_clear H3; inversion_clear H32; inversion_clear H37.
elim (H38 x); intros.
cut (btrans (nu p') (bOut x) x4);
 [ intro
 | apply OPEN with (cons x empty); intros; inversion_clear H43;
    apply FTR_L3 with x2; auto;
    try (unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto) ].
elim (H39 x4 H40); intros; inversion_clear H41.
exists x5; split; [ assumption | intros; inversion_clear H34 ].
generalize H45; clear H45; case n2; intros; simpl in H45; inversion_clear H45.
inversion_clear H34; inversion_clear H45; inversion_clear H46.

apply sbupto with 0; apply NU_FUN_RW with x2; auto.
elim (BTR_L1 p0 x5 (bOut x) x2 H22 H42); intros; assumption.
elim (BTR_L1 p3 q1 (bOut x) x2 H24 H8); intros; assumption.
simpl in |- *; unfold SB_R_SB in |- *; exists x6; exists x7; split;
 [ apply TRANS with (x4 x2); auto
 | split; [ assumption | apply TRANS with (x0 x2); auto ] ].
apply H43; auto; elim (BTR_L1 p0 x5 (bOut x) x2 H22 H42); intros; assumption.
apply H15; auto; elim (BTR_L1 p3 q1 (bOut x) x2 H24 H8); intros; assumption.

apply sbupto with (S n3); apply NU_FUN_RW with x2; auto.
elim (BTR_L1 p0 x5 (bOut x) x2 H22 H42); intros; assumption.
elim (BTR_L1 p3 q1 (bOut x) x2 H24 H8); intros; assumption.
simpl in |- *; apply op_nu with p'0 q'0; intros; auto.
apply TRANS with (x4 x2);
 [ apply H43; auto; elim (BTR_L1 p0 x5 (bOut x) x2 H22 H42); intros;
    assumption
 | assumption ].
apply TRANS with (x0 x2);
 [ assumption
 | apply H15; auto; elim (BTR_L1 p3 q1 (bOut x) x2 H24 H8); intros;
    assumption ].

Qed.

(*******************************************************************)
(* Here is the definition of the strong bisimulation UpTo allowing *)
(* to prove the extrusion law of the restriction operator.         *)
(*******************************************************************)

Inductive BisNU_E : proc -> proc -> Prop :=
  | bisnu_e :
      forall (p : name -> proc) (q : proc),
      BisNU_E (nu (fun y : name => par (p y) q)) (par (nu p) q)
  | bisnu_e_ref : forall p : proc, BisNU_E p p.

Lemma NU_E_RW :
 forall (p q : name -> proc) (x : name),
 notin x (nu p) ->
 notin x (nu q) ->
 BisNU_E (p x) (q x) ->
 forall y : name, notin y (nu p) -> notin y (nu q) -> BisNU_E (p y) (q y).

Proof.

intros; elim (LEM_name x y); intro.

rewrite <- H4; assumption.

inversion H1.
elim (ho_proc_exp p0 x); elim (proc_exp q0 x); intros.
inversion_clear H5; inversion_clear H8.
rewrite H10 in H6; rewrite H10 in H7; rewrite H11 in H6; rewrite H11 in H7.
cut (p = (fun n : name => nu (fun y : name => par (x1 n y) (x0 n))));
 [ intro | apply proc_ext with x; auto ].
cut (q = (fun n : name => par (nu (x1 n)) (x0 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H8; rewrite H12; apply bisnu_e.
inversion_clear H9; inversion_clear H5; apply notin_nu; intros;
 apply notin_par; auto.
inversion_clear H9; inversion_clear H5; do 2 (apply notin_nu; intros);
 apply notin_par;
 [ cut (notin x (nu (x1 z))); [ intro; inversion_clear H13; auto | auto ]
 | auto ].

cut (p = q); [ intro | apply proc_ext with x; auto ].
rewrite H6; apply bisnu_e_ref.

Qed.

Lemma BisNU_E_FTR1 :
 forall p q : proc,
 BisNU_E p q ->
 forall x y : name,
 (forall p1 : proc,
  ftrans p (Out x y) p1 ->
  exists q1 : proc, ftrans q (Out x y) q1 /\ BisNU_E p1 q1) /\
 (forall q1 : proc,
  ftrans q (Out x y) q1 ->
  exists p1 : proc, ftrans p (Out x y) p1 /\ BisNU_E p1 q1).

Proof.

intros; inversion H; split; intros.

inversion_clear H2.
elim
 (unsat (par (nu (fun y : name => par (p0 y) q0)) (nu p3))
    (cons x (cons y l))); intros.
inversion_clear H2.
inversion_clear H4; inversion_clear H5.
inversion_clear H7.
cut (ftrans (par (p0 x0) q0) (Out x y) (p3 x0)); [ intro | apply H3; auto ].
inversion H7.
elim (proc_exp p5 x0); intros.
inversion_clear H14.
rewrite H16 in H12.
exists (par (nu x1) q0); split;
 [ apply fPAR1; apply fRES with l; intros | idtac ].
inversion_clear H19;
 change (ftrans (p0 y0) ((fun n : name => Out x y) y0) (x1 y0)) in |- *;
 apply FTR_L3 with x0; auto.
inversion_clear H2; apply notin_nu; intros.
cut (notin x0 (par (p0 z) q0)); [ intro; inversion_clear H22; auto | auto ].
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H16 in H13; cut (p3 = (fun n : name => par (x1 n) q0));
 [ intro | apply proc_ext with x0; auto ].
rewrite H14; apply bisnu_e.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H15; auto
 | inversion_clear H2; cut (notin x0 (par (p0 z) q0));
    [ intro; inversion_clear H2; assumption | auto ] ].
exists (par (nu p0) p5); split; [ apply fPAR2; assumption | idtac ].
cut (p3 = (fun n : name => par (p0 n) p5));
 [ intro | apply proc_ext with x0; auto ].
rewrite H14; apply bisnu_e.
inversion_clear H2; apply notin_nu; intros; cut (notin x0 (par (p0 z) q0));
 [ intro | auto ].
inversion_clear H15; apply notin_par;
 [ assumption
 | elim (FTR_L1 q0 p5 (Out x y) x0 H17 H12); intros; assumption ].
apply f_act_notin_Out; auto.

inversion_clear H2.
inversion H3.
elim (unsat (par (nu p0) (par q0 (nu p2))) (cons x (cons y l))); intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
inversion_clear H10; inversion_clear H11.
cut (ftrans (p0 x0) (Out x y) (p2 x0)); [ intro | apply H4; auto ].
exists (nu (fun y0 : name => par (p2 y0) q0)); split;
 [ apply fRES with l; intros | apply bisnu_e ].
change
  (ftrans ((fun n : name => par (p0 n) q0) y0) ((fun n : name => Out x y) y0)
     ((fun n : name => par (p2 n) q0) y0)) in |- *; 
 apply FTR_L3 with x0; auto.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H7; auto | assumption ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H12; auto | assumption ].
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply fPAR1; assumption.
inversion_clear H17; unfold f_act_notin_ho in |- *; intros;
 apply f_act_notin_Out; auto.
apply f_act_notin_Out; auto.
exists (nu (fun y0 : name => par (p0 y0) p3)); split;
 [ apply fRES with empty; intros; apply fPAR2; assumption | apply bisnu_e ].

exists p1; split; [ assumption | apply bisnu_e_ref ].

exists q1; split; [ assumption | apply bisnu_e_ref ].

Qed.

Lemma BisNU_E_IN :
 forall p q : proc,
 BisNU_E p q ->
 forall x : name,
 (forall p1 : name -> proc,
  btrans p (In x) p1 ->
  exists q1 : name -> proc,
    btrans q (In x) q1 /\ (forall y : name, BisNU_E (p1 y) (q1 y))) /\
 (forall q1 : name -> proc,
  btrans q (In x) q1 ->
  exists p1 : name -> proc,
    btrans p (In x) p1 /\ (forall y : name, BisNU_E (p1 y) (q1 y))).

Proof.

intros; inversion H; split; intros.

inversion H2.

elim
 (unsat
    (par (nu (fun y : name => par (p0 y) q0))
       (nu (fun z : name => nu (p3 z)))) (cons x l)); 
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
cut (btrans (par (p0 x0) q0) (In x) (p3 x0)); [ intro | apply H4; auto ].
inversion H9.
elim (ho_proc_exp p6 x0); intros.
inversion_clear H17.
rewrite H19 in H15;
 exists (fun n : name => par (nu (fun u : name => x1 u n)) q0); 
 split;
 [ change
     (btrans (par (nu p0) q0) (In x)
        (fun n : name =>
         par ((fun v : name => nu (fun u : name => x1 u v)) n) q0)) 
    in |- *; apply bPAR1; apply bRES with l; intros
 | idtac ].
inversion_clear H21;
 change (btrans (p0 y) ((fun _ : name => In x) y) (x1 y)) in |- *;
 apply BTR_L3 with x0; auto.
inversion_clear H7; apply notin_nu; intros; cut (notin x0 (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H24; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H19 in H16; cut (p3 = (fun x0 x : name => par (x1 x0 x) q0));
 [ intro | apply ho_proc_ext with x0; auto ].
intro; rewrite H17;
 change
   (BisNU_E (nu (fun z : name => par ((fun n : name => x1 n y) z) q0))
      (par (nu (fun u : name => x1 u y)) q0)) in |- *; 
 apply bisnu_e.
do 2 (apply notin_nu; intros); apply notin_par;
 [ inversion_clear H18; cut (notin x0 (nu (x1 z))); [ intro | auto ];
    inversion_clear H18; auto
 | inversion_clear H7; cut (notin x0 (par (p0 z) q0)); [ intro | auto ];
    inversion_clear H7; assumption ].

exists (fun n : name => par (nu p0) (p6 n)); split;
 [ apply bPAR2; assumption | idtac ].
intro; cut (p3 = (fun x0 x : name => par (p0 x0) (p6 x)));
 [ intro | apply ho_proc_ext with x0; auto ].
rewrite H17; apply bisnu_e.
inversion_clear H7; do 2 (apply notin_nu; intros); apply notin_par.
cut (notin x0 (par (p0 z) q0)); [ intro | auto ]; inversion_clear H19;
 assumption.
cut (notin x0 (par (p0 z) q0)); [ intro | auto ]; inversion_clear H19;
 elim (BTR_L1 q0 p6 (In x) x0 H21 H15); intros.
inversion_clear H22; auto.
apply b_act_notin_In; auto.

inversion H2.
inversion H7.
exists (fun n : name => nu (fun y : name => par (p5 y n) q0)); split;
 [ change
     (btrans (nu (fun y : name => par (p0 y) q0)) (In x)
        (fun n : name =>
         nu (fun y : name => (fun u v : name => par (p5 u v) q0) y n)))
    in |- *; apply bRES with l; intros; apply bPAR1; 
    apply H9; auto
 | idtac ].
inversion_clear H12; apply notin_nu; intros; cut (notin y (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H17; auto.
do 2 (apply notin_nu; intros); inversion_clear H13;
 cut (notin y (nu (fun v : name => par (p5 z v) q0))); 
 [ intro | auto ]; inversion_clear H13; cut (notin y (par (p5 z z0) q0));
 [ intro | auto ]; inversion_clear H13; assumption.
intro;
 change
   (BisNU_E (nu (fun y0 : name => par ((fun n : name => p5 n y) y0) q0))
      (par (nu (fun z : name => p5 z y)) q0)) in |- *; 
 apply bisnu_e.

exists (fun n : name => nu (fun y : name => par (p0 y) (p3 n))); split;
 [ change
     (btrans (nu (fun y : name => par (p0 y) q0)) (In x)
        (fun n : name =>
         nu (fun y : name => (fun u v : name => par (p0 u) (p3 v)) y n)))
    in |- *; apply bRES with empty; intros; apply bPAR2; 
    assumption
 | intro; apply bisnu_e ].

exists p1; split; [ assumption | intro; apply bisnu_e_ref ].

exists q1; split; [ assumption | intro; apply bisnu_e_ref ].

Qed.

Lemma BisNU_E_bOUT :
 forall p q : proc,
 BisNU_E p q ->
 forall x : name,
 (forall p1 : name -> proc,
  btrans p (bOut x) p1 ->
  exists q1 : name -> proc,
    btrans q (bOut x) q1 /\
    (forall y : name,
     notin y (nu p1) -> notin y (nu q1) -> BisNU_E (p1 y) (q1 y))) /\
 (forall q1 : name -> proc,
  btrans q (bOut x) q1 ->
  exists p1 : name -> proc,
    btrans p (bOut x) p1 /\
    (forall y : name,
     notin y (nu p1) -> notin y (nu q1) -> BisNU_E (p1 y) (q1 y))).

Proof.

intros; inversion H; split; intros.

inversion H2.

elim
 (unsat
    (par (nu (fun y : name => par (p0 y) q0))
       (nu (fun z : name => nu (p3 z)))) (cons x l)); 
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
cut (btrans (par (p0 x0) q0) (bOut x) (p3 x0)); [ intro | apply H4; auto ].
inversion H9.
elim (ho_proc_exp p6 x0); intros.
inversion_clear H17.
rewrite H19 in H15;
 exists (fun n : name => par (nu (fun u : name => x1 u n)) q0); 
 split;
 [ change
     (btrans (par (nu p0) q0) (bOut x)
        (fun n : name =>
         par ((fun v : name => nu (fun u : name => x1 u v)) n) q0)) 
    in |- *; apply bPAR1; apply bRES with l; intros
 | idtac ].
inversion_clear H21;
 change (btrans (p0 y) ((fun _ : name => bOut x) y) (x1 y)) in |- *;
 apply BTR_L3 with x0; auto.
inversion_clear H7; apply notin_nu; intros; cut (notin x0 (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H24; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
rewrite H19 in H16; cut (p3 = (fun x0 x : name => par (x1 x0 x) q0));
 [ intro | apply ho_proc_ext with x0; auto ].
intros; rewrite H17;
 change
   (BisNU_E (nu (fun z : name => par ((fun n : name => x1 n y) z) q0))
      (par (nu (fun u : name => x1 u y)) q0)) in |- *; 
 apply bisnu_e.
do 2 (apply notin_nu; intros); apply notin_par;
 [ inversion_clear H18; cut (notin x0 (nu (x1 z))); [ intro | auto ];
    inversion_clear H18; auto
 | inversion_clear H7; cut (notin x0 (par (p0 z) q0)); [ intro | auto ];
    inversion_clear H7; assumption ].

exists (fun n : name => par (nu p0) (p6 n)); split;
 [ apply bPAR2; assumption | idtac ].
intros; cut (p3 = (fun x0 x : name => par (p0 x0) (p6 x)));
 [ intro | apply ho_proc_ext with x0; auto ].
rewrite H19; apply bisnu_e.
inversion_clear H7; do 2 (apply notin_nu; intros); apply notin_par.
cut (notin x0 (par (p0 z) q0)); [ intro | auto ]; inversion_clear H21;
 assumption.
cut (notin x0 (par (p0 z) q0)); [ intro | auto ]; inversion_clear H21;
 elim (BTR_L1 q0 p6 (bOut x) x0 H23 H15); intros.
inversion_clear H24; auto.
apply b_act_notin_bOut; auto.

elim (unsat (par (nu (fun y : name => par (p0 y) q0)) (nu p1)) (cons x l));
 intros.
inversion_clear H7.
inversion_clear H8; inversion_clear H9.
cut (ftrans (par (p0 x1) q0) (Out x x1) (p1 x1)); [ intro | apply H5; auto ].
inversion H9.
elim (proc_exp p6 x1); intros.
inversion_clear H17; exists (fun n : name => par (x2 n) q0); split;
 [ apply bPAR1; apply OPEN with l; intros; rewrite H19 in H15;
    apply FTR_L3 with x1; auto
 | idtac ].
inversion_clear H7; apply notin_nu; intros; cut (notin x1 (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H24; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H19 in H16; cut (p1 = (fun n : name => par (x2 n) q0));
 [ intro | apply proc_ext with x1; auto ].
intros; rewrite H17; apply bisnu_e_ref.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H18; auto
 | inversion_clear H7; cut (notin x1 (par (p0 z) q0)); [ intro | auto ];
    inversion_clear H7; assumption ].

inversion_clear H7; cut (notin x1 (par (p0 x) q0)); [ intro | auto ];
 inversion_clear H7.
elim (FTR_L1 q0 p6 (Out x x1) x1 H19 H15); intros; inversion_clear H7;
 unfold not in H22; elim (H22 (refl_equal x1)).

inversion H2.
inversion H7.
exists (fun n : name => nu (fun y : name => par (p5 y n) q0)); split;
 [ change
     (btrans (nu (fun y : name => par (p0 y) q0)) (bOut x)
        (fun n : name =>
         nu (fun y : name => (fun u v : name => par (p5 u v) q0) y n)))
    in |- *; apply bRES with l; intros; apply bPAR1; 
    apply H9; auto
 | idtac ].
inversion_clear H12; apply notin_nu; intros; cut (notin y (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H17; auto.
do 2 (apply notin_nu; intros); inversion_clear H13;
 cut (notin y (nu (fun v : name => par (p5 z v) q0))); 
 [ intro | auto ]; inversion_clear H13; cut (notin y (par (p5 z z0) q0));
 [ intro | auto ]; inversion_clear H13; assumption.
intros;
 change
   (BisNU_E (nu (fun y0 : name => par ((fun n : name => p5 n y) y0) q0))
      (par (nu (fun z : name => p5 z y)) q0)) in |- *; 
 apply bisnu_e.

exists (fun n : name => par (p3 n) q0); split;
 [ apply OPEN with l; intros; apply fPAR1; apply H10; auto
 | intros; apply bisnu_e_ref ].
inversion_clear H12; apply notin_nu; intros; cut (notin y (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H17; auto.
inversion_clear H13; apply notin_nu; intros; cut (notin y (par (p3 z) q0));
 [ intro | auto ]; inversion_clear H17; auto.

exists (fun n : name => nu (fun y : name => par (p0 y) (p3 n))); split;
 [ change
     (btrans (nu (fun y : name => par (p0 y) q0)) (bOut x)
        (fun n : name =>
         nu (fun y : name => (fun u v : name => par (p0 u) (p3 v)) y n)))
    in |- *; apply bRES with empty; intros; apply bPAR2; 
    assumption
 | intros; apply bisnu_e ].

exists p1; split; [ assumption | intros; apply bisnu_e_ref ].

exists q1; split; [ assumption | intros; apply bisnu_e_ref ].

Qed.

Lemma BisNU_E_FTR2 :
 forall p q : proc,
 BisNU_E p q ->
 (forall p1 : proc,
  ftrans p tau p1 ->
  exists q1 : proc,
    ftrans q tau q1 /\
    ((exists p1' : proc,
        (exists q1' : proc,
           StBisim p1 p1' /\ BisNU_E p1' q1' /\ StBisim q1' q1)) \/
     (exists p1' : name -> proc,
        (exists q1' : name -> proc,
           StBisim p1 (nu p1') /\
           (forall z : name,
            notin z (nu p1') -> notin z (nu q1') -> BisNU_E (p1' z) (q1' z)) /\
           StBisim (nu q1') q1)))) /\
 (forall q1 : proc,
  ftrans q tau q1 ->
  exists p1 : proc,
    ftrans p tau p1 /\
    ((exists p1' : proc,
        (exists q1' : proc,
           StBisim p1 p1' /\ BisNU_E p1' q1' /\ StBisim q1' q1)) \/
     (exists p1' : name -> proc,
        (exists q1' : name -> proc,
           StBisim p1 (nu p1') /\
           (forall z : name,
            notin z (nu p1') -> notin z (nu q1') -> BisNU_E (p1' z) (q1' z)) /\
           StBisim (nu q1') q1)))).

Proof.

intros; inversion H; split; intros.

inversion H2.
elim (unsat (par (nu (fun y : name => par (p0 y) q0)) (nu p3)) l); intros.
inversion_clear H7.
inversion_clear H8.
cut (ftrans (par (p0 x) q0) tau (p3 x)); [ intro | apply H4; auto ].
inversion H8.
elim (proc_exp p6 x); intros.
inversion_clear H16.
rewrite H18 in H14; exists (par (nu x0) q0); split;
 [ apply fPAR1; apply fRES with l; intros | idtac ].
clear H21; change (ftrans (p0 y) ((fun _ : name => tau) y) (x0 y)) in |- *;
 apply FTR_L3 with x; auto.
inversion_clear H7; apply notin_nu; intros; cut (notin x (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H22; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
left; exists (nu (fun n : name => par (x0 n) q0)); exists (par (nu x0) q0);
 split; [ idtac | split; [ apply bisnu_e | apply REF ] ].
rewrite H18 in H15; cut (p3 = (fun n : name => par (x0 n) q0));
 [ intro | apply proc_ext with x; auto ].
rewrite H16; apply REF.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H17; auto
 | inversion_clear H7; cut (notin x (par (p0 z) q0)); [ intro | auto ];
    inversion_clear H7; assumption ].

exists (par (nu p0) p6); split; [ apply fPAR2; assumption | left ].
exists (nu p3); exists (par (nu p0) p6); split;
 [ apply REF | split; [ idtac | apply REF ] ].
cut (p3 = (fun n : name => par (p0 n) p6));
 [ intro | apply proc_ext with x; auto ].
rewrite H16; apply bisnu_e.
inversion_clear H7; apply notin_nu; intros; cut (notin x (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H17; apply notin_par;
 [ assumption | elim (FTR_L1 q0 p6 tau x H19 H14); intros; assumption ].

elim (ho_proc_exp q1 x); intros.
inversion_clear H16.
rewrite H18 in H14; exists (par (nu (fun n : name => x1 n y)) q2); split;
 [ change
     (ftrans (par (nu p0) q0) tau
        (par ((fun u : name => nu (fun n : name => x1 n u)) y) q2)) 
    in |- *; apply COM1 with x0; [ apply bRES with l; intros | assumption ]
 | left ].
change (btrans (p0 y0) ((fun _ : name => In x0) y0) (x1 y0)) in |- *;
 apply BTR_L3 with x; auto.
inversion_clear H7; apply notin_nu; intros; cut (notin x (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H23; assumption.
inversion_clear H7; unfold b_act_notin_ho in |- *; intros;
 apply b_act_notin_In; cut (notin x (par (p0 y1) q0)); 
 [ intro | auto ]; inversion_clear H23;
 elim (FTR_L1 q0 q2 (Out x0 y) x H25 H15); intros; 
 inversion_clear H23; auto.
inversion_clear H20; unfold b_act_notin_ho in |- *; intros;
 apply b_act_notin_In; auto.
exists (nu p3); exists (par (nu (fun n : name => x1 n y)) q2); split;
 [ apply REF | split; [ idtac | apply REF ] ].
rewrite H18 in H13; cut (p3 = (fun n : name => par (x1 n y) q2));
 [ intro | apply proc_ext with x; auto ].
rewrite H16;
 change
   (BisNU_E (nu (fun n : name => par ((fun u : name => x1 u y) n) q2))
      (par (nu (fun n : name => x1 n y)) q2)) in |- *; 
 apply bisnu_e.
apply notin_nu; intros; inversion_clear H7; cut (notin x (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H7;
 elim (FTR_L1 q0 q2 (Out x0 y) x H21 H15); intros; 
 inversion_clear H7; apply notin_par;
 [ inversion_clear H17; cut (notin x (nu (x1 z))); [ intro | auto ];
    inversion_clear H17; auto
 | assumption ].

elim (proc_exp q1 x); intros.
inversion_clear H16; elim (LEM_name x y); intro.

rewrite H18 in H14; rewrite H16 in H14;
 exists (nu (fun n : name => par (x1 n) (q2 n))); split;
 [ apply CLOSE2 with x0;
    [ apply OPEN with l; intros; apply FTR_L3 with x; auto | assumption ]
 | left ].
inversion_clear H7; apply notin_nu; intros; cut (notin x (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H24; assumption.
inversion_clear H7; unfold f_act_notin_ho in |- *; intros;
 cut (notin x (par (p0 y1) q0)); [ intro | auto ]; 
 inversion_clear H24; elim (BTR_L1 q0 q2 (In x0) x H26 H15); 
 intros; inversion_clear H24; apply f_act_notin_Out; 
 auto.
rewrite H16; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
exists (nu p3); exists (nu (fun n : name => par (x1 n) (q2 n))); split;
 [ apply REF | split; [ idtac | apply REF ] ].
rewrite <- H16 in H13; rewrite H18 in H13;
 cut (p3 = (fun n : name => par (x1 n) (q2 n)));
 [ intro | apply proc_ext with x; auto ].
rewrite H19; apply bisnu_e_ref.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H17; auto
 | inversion_clear H7; cut (notin x (par (p0 z) q0)); [ intro | auto ];
    inversion_clear H7; elim (BTR_L1 q0 q2 (In x0) x H22 H15); 
    intros; inversion_clear H23; auto ].

rewrite H18 in H14; exists (par (nu (fun n : name => x1 n)) (q2 y)); split;
 [ apply COM2 with x0; [ apply fRES with l; intros | assumption ] | left ].
change (ftrans (p0 y0) ((fun _ : name => Out x0 y) y0) (x1 y0)) in |- *;
 apply FTR_L3 with x; auto.
inversion_clear H7; apply notin_nu; intros; cut (notin x (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H24; assumption.
inversion_clear H7; unfold f_act_notin_ho in |- *; intros;
 cut (notin x (par (p0 y1) q0)); [ intro | auto ]; 
 inversion_clear H24; elim (BTR_L1 q0 q2 (In x0) x H26 H15); 
 intros; inversion_clear H24; apply f_act_notin_Out; 
 auto.
unfold f_act_notin_ho in |- *; intros; assumption.
exists (nu p3); exists (par (nu (fun n : name => x1 n)) (q2 y)); split;
 [ apply REF | split; [ idtac | apply REF ] ].
rewrite H18 in H13; cut (p3 = (fun n : name => par (x1 n) (q2 y)));
 [ intro | apply proc_ext with x; auto ].
rewrite H19;
 change
   (BisNU_E (nu (fun n : name => par ((fun u : name => x1 u) n) (q2 y)))
      (par (nu (fun n : name => x1 n)) (q2 y))) in |- *; 
 apply bisnu_e.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H17; auto
 | inversion_clear H7; cut (notin x (par (p0 z) q0)); [ intro | auto ];
    inversion_clear H7; elim (BTR_L1 q0 q2 (In x0) x H22 H15); 
    intros; inversion_clear H23; auto ].

elim (ho_proc_exp q1 x); intros.
inversion_clear H16.
rewrite H18 in H14;
 exists (nu (fun n : name => par (nu (fun u : name => x1 u n)) (q2 n)));
 split;
 [ change
     (ftrans (par (nu p0) q0) tau
        (nu
           (fun n : name =>
            par ((fun v : name => nu (fun u : name => x1 u v)) n) (q2 n))))
    in |- *; apply CLOSE1 with x0; [ apply bRES with l; intros | assumption ]
 | right ].
change (btrans (p0 y) ((fun _ : name => In x0) y) (x1 y)) in |- *;
 apply BTR_L3 with x; auto.
inversion_clear H7; apply notin_nu; intros; cut (notin x (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H23; assumption.
inversion_clear H7; unfold b_act_notin_ho in |- *; intros;
 apply b_act_notin_In; cut (notin x (par (p0 y0) q0)); 
 [ intro | auto ]; inversion_clear H23;
 elim (BTR_L1 q0 q2 (bOut x0) x H25 H15); intros; inversion_clear H23; 
 auto.
unfold b_act_notin_ho in |- *; intros; assumption.
exists (fun z : name => nu (fun n : name => par (x1 n z) (q2 z)));
 exists (fun n : name => par (nu (fun u : name => x1 u n)) (q2 n)); 
 split; [ idtac | split; [ intros | apply REF ] ].
rewrite H18 in H13;
 cut (p3 = (fun n : name => nu (fun z : name => par (x1 n z) (q2 z))));
 [ intro | apply proc_ext with x; auto ].
rewrite H16;
 change
   (StBisim
      (nu
         (fun n : name =>
          nu (fun z : name => (fun u v : name => par (x1 u v) (q2 v)) n z)))
      (nu
         (fun z : name =>
          nu (fun n : name => (fun u v : name => par (x1 u v) (q2 v)) n z))))
  in |- *; apply NU_COMM.
do 2 (apply notin_nu; intros); apply notin_par;
 [ inversion_clear H17; cut (notin x (nu (x1 z))); [ intro | auto ];
    inversion_clear H17; auto
 | inversion_clear H7; cut (notin x (par (p0 z) q0)); [ intro | auto ];
    inversion_clear H7; elim (BTR_L1 q0 q2 (bOut x0) x H22 H15); 
    intros; inversion_clear H23; auto ].
change
  (BisNU_E (nu (fun n : name => par ((fun u : name => x1 u z) n) (q2 z)))
     (par (nu (fun u : name => x1 u z)) (q2 z))) in |- *; 
 apply bisnu_e.

elim (ho_proc_exp q1 x); intros.
inversion_clear H16.
rewrite H18 in H14;
 exists (nu (fun n : name => par (nu (fun u : name => x1 u n)) (q2 n)));
 split;
 [ change
     (ftrans (par (nu p0) q0) tau
        (nu
           (fun n : name =>
            par ((fun v : name => nu (fun u : name => x1 u v)) n) (q2 n))))
    in |- *; apply CLOSE2 with x0; [ apply bRES with l; intros | assumption ]
 | right ].
change (btrans (p0 y) ((fun _ : name => bOut x0) y) (x1 y)) in |- *;
 apply BTR_L3 with x; auto.
inversion_clear H7; apply notin_nu; intros; cut (notin x (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H23; assumption.
inversion_clear H7; unfold b_act_notin_ho in |- *; intros;
 apply b_act_notin_bOut; cut (notin x (par (p0 y0) q0)); 
 [ intro | auto ]; inversion_clear H23; elim (BTR_L1 q0 q2 (In x0) x H25 H15);
 intros; inversion_clear H23; auto.
unfold b_act_notin_ho in |- *; intros; assumption.
exists (fun z : name => nu (fun n : name => par (x1 n z) (q2 z)));
 exists (fun n : name => par (nu (fun u : name => x1 u n)) (q2 n)); 
 split; [ idtac | split; [ intros | apply REF ] ].
rewrite H18 in H13;
 cut (p3 = (fun n : name => nu (fun z : name => par (x1 n z) (q2 z))));
 [ intro | apply proc_ext with x; auto ].
rewrite H16;
 change
   (StBisim
      (nu
         (fun n : name =>
          nu (fun z : name => (fun u v : name => par (x1 u v) (q2 v)) n z)))
      (nu
         (fun z : name =>
          nu (fun n : name => (fun u v : name => par (x1 u v) (q2 v)) n z))))
  in |- *; apply NU_COMM.
do 2 (apply notin_nu; intros); apply notin_par;
 [ inversion_clear H17; cut (notin x (nu (x1 z))); [ intro | auto ];
    inversion_clear H17; auto
 | inversion_clear H7; cut (notin x (par (p0 z) q0)); [ intro | auto ];
    inversion_clear H7; elim (BTR_L1 q0 q2 (In x0) x H22 H15); 
    intros; inversion_clear H23; auto ].
change
  (BisNU_E (nu (fun n : name => par ((fun u : name => x1 u z) n) (q2 z)))
     (par (nu (fun u : name => x1 u z)) (q2 z))) in |- *; 
 apply bisnu_e.

apply f_act_notin_tau.

inversion H2.

inversion H7.
exists (nu (fun y : name => par (p5 y) q0)); split;
 [ apply fRES with l; intros; apply fPAR1 | left ].
clear H15; apply H9; auto.
inversion_clear H12; apply notin_nu; intros; cut (notin y (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H16; assumption.
inversion_clear H13; apply notin_nu; intros; cut (notin y (par (p5 z) q0));
 [ intro | auto ]; inversion_clear H16; assumption.
apply f_act_notin_tau.
exists (nu (fun y : name => par (p5 y) q0)); exists (par (nu p5) q0); split;
 [ apply REF | split; [ apply bisnu_e | apply REF ] ].

exists (nu (fun y : name => par (p0 y) p3)); split;
 [ apply fRES with empty; intros; apply fPAR2; assumption | left ].
exists (nu (fun y : name => par (p0 y) p3)); exists (par (nu p0) p3); split;
 [ apply REF | split; [ apply bisnu_e | apply REF ] ].

inversion H5.
exists (nu (fun y0 : name => par (p4 y0 y) q2)); split;
 [ apply fRES with l; intros; apply COM1 with x;
    [ apply H9; auto | assumption ]
 | left ].
inversion_clear H12; apply notin_nu; intros; cut (notin y0 (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H17; assumption.
inversion_clear H13; apply notin_nu; intros; apply proc_mono with y;
 cut (notin y0 (par (p4 z y) q2)); [ intro | auto ]; 
 inversion_clear H17; assumption.
elim (unsat nil (cons y0 empty)); intros; inversion_clear H16;
 inversion_clear H18; clear H17; clear H19; inversion_clear H12;
 cut (notin y0 (par (p0 x0) q0)); [ intro | auto ]; 
 inversion_clear H12; elim (FTR_L1 q0 q2 (Out x y) y0 H19 H6); 
 intros; inversion_clear H12; apply b_act_notin_In; 
 auto.
exists (nu (fun y0 : name => par (p4 y0 y) q2));
 exists (par (nu (fun z : name => p4 z y)) q2); split;
 [ apply REF
 | split;
    [ change
        (BisNU_E (nu (fun y0 : name => par ((fun n : name => p4 n y) y0) q2))
           (par (nu (fun z : name => p4 z y)) q2)) 
       in |- *; apply bisnu_e
    | apply REF ] ].

inversion H5.
exists (nu (fun y0 : name => par (p4 y0) (q3 y))); split;
 [ apply fRES with l; intros; apply COM2 with x;
    [ apply H9; auto | assumption ]
 | left ].
inversion_clear H12; apply notin_nu; intros; cut (notin y0 (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H17; assumption.
inversion_clear H13; apply notin_nu; intros;
 cut (notin y0 (par (p4 z) (q3 y))); [ intro | auto ]; 
 inversion_clear H17; assumption.
cut (notin y0 (nu p0));
 [ intro; elim (FTR_L1 (nu p0) q2 (Out x y) y0 H16 H5); intros; assumption
 | inversion_clear H12; apply notin_nu; intros;
    cut (notin y0 (par (p0 z) q0)); [ intro | auto ]; 
    inversion_clear H17; assumption ].
exists (nu (fun y0 : name => par (p4 y0) (q3 y)));
 exists (par (nu p4) (q3 y)); split;
 [ apply REF | split; [ apply bisnu_e | apply REF ] ].

inversion H5.
exists (nu (fun y : name => nu (fun n : name => par (p4 y n) (q3 n)))); split;
 [ apply fRES with l; intros; apply CLOSE1 with x;
    [ apply H9; auto | assumption ]
 | right ].
inversion_clear H12; apply notin_nu; intros; cut (notin y (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H17; assumption.
inversion_clear H13; do 2 (apply notin_nu; intros);
 cut (notin y (nu (fun n : name => par (p4 z n) (q3 n)))); 
 [ intro | auto ]; inversion_clear H18; cut (notin y (par (p4 z z0) (q3 z0)));
 [ intro | auto ]; inversion_clear H18; assumption.
elim (unsat nil (cons y empty)); intros; inversion_clear H16;
 inversion_clear H18; clear H17; clear H19; inversion_clear H12;
 cut (notin y (par (p0 x0) q0)); [ intro | auto ]; 
 inversion_clear H12; elim (BTR_L1 q0 q3 (bOut x) y H19 H6); 
 intros; inversion_clear H12; apply b_act_notin_In; 
 auto.
exists (fun z : name => nu (fun n : name => par (p4 n z) (q3 z)));
 exists (fun n : name => par (nu (fun u : name => p4 u n)) (q3 n)); 
 split; [ idtac | split; [ intros | apply REF ] ].
change
  (StBisim
     (nu
        (fun n : name =>
         nu (fun z : name => (fun u v : name => par (p4 u v) (q3 v)) n z)))
     (nu
        (fun z : name =>
         nu (fun n : name => (fun u v : name => par (p4 u v) (q3 v)) n z))))
 in |- *; apply NU_COMM.
change
  (BisNU_E (nu (fun n : name => par ((fun u : name => p4 u z) n) (q3 z)))
     (par (nu (fun u : name => p4 u z)) (q3 z))) in |- *; 
 apply bisnu_e.

inversion H5.
exists (nu (fun y : name => nu (fun n : name => par (p4 y n) (q3 n)))); split;
 [ apply fRES with l; intros; apply CLOSE2 with x;
    [ apply H9; auto | assumption ]
 | right ].
inversion_clear H12; apply notin_nu; intros; cut (notin y (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H17; assumption.
inversion_clear H13; do 2 (apply notin_nu; intros);
 cut (notin y (nu (fun n : name => par (p4 z n) (q3 n)))); 
 [ intro | auto ]; inversion_clear H18; cut (notin y (par (p4 z z0) (q3 z0)));
 [ intro | auto ]; inversion_clear H18; assumption.
elim (unsat nil (cons y empty)); intros; inversion_clear H16;
 inversion_clear H18; clear H17; clear H19; inversion_clear H12;
 cut (notin y (par (p0 x0) q0)); [ intro | auto ]; 
 inversion_clear H12; elim (BTR_L1 q0 q3 (In x) y H19 H6); 
 intros; inversion_clear H12; apply b_act_notin_bOut; 
 auto.
exists (fun z : name => nu (fun n : name => par (p4 n z) (q3 z)));
 exists (fun n : name => par (nu (fun u : name => p4 u n)) (q3 n)); 
 split; [ idtac | split; [ intros | apply REF ] ].
change
  (StBisim
     (nu
        (fun n : name =>
         nu (fun z : name => (fun u v : name => par (p4 u v) (q3 v)) n z)))
     (nu
        (fun z : name =>
         nu (fun n : name => (fun u v : name => par (p4 u v) (q3 v)) n z))))
 in |- *; apply NU_COMM.
change
  (BisNU_E (nu (fun n : name => par ((fun u : name => p4 u z) n) (q3 z)))
     (par (nu (fun u : name => p4 u z)) (q3 z))) in |- *; 
 apply bisnu_e.

exists (nu (fun y : name => par (q2 y) (q3 y))); split;
 [ apply fRES with l; intros; apply COM2 with x;
    [ apply H10; auto | assumption ]
 | left ].
inversion_clear H12; apply notin_nu; intros; cut (notin y (par (p0 z) q0));
 [ intro | auto ]; inversion_clear H17; assumption.
inversion_clear H13; apply notin_nu; intros;
 cut (notin y (par (q2 z) (q3 z))); [ intro | auto ]; 
 inversion_clear H17; assumption.
elim (unsat nil (cons y empty)); intros; inversion_clear H16;
 inversion_clear H18; clear H17 H19; inversion_clear H12;
 cut (notin y (par (p0 x1) q0)); [ intro | auto ]; 
 inversion_clear H12; elim (BTR_L1 q0 q3 (In x) y H19 H6); 
 intros; inversion_clear H12; auto.
exists (nu (fun y : name => par (q2 y) (q3 y)));
 exists (nu (fun z : name => par (q2 z) (q3 z))); split;
 [ apply REF | split; [ apply bisnu_e_ref | apply REF ] ].

exists p1; split;
 [ assumption
 | left; exists p1; exists p1; split;
    [ apply REF | split; [ apply bisnu_e_ref | apply REF ] ] ].

exists q1; split;
 [ assumption
 | left; exists q1; exists q1; split;
    [ apply REF | split; [ apply bisnu_e_ref | apply REF ] ] ].

Qed.

(* BisNU_E is a strong bisimulation UpTo *)

Lemma BisNU_E_UPTO : UpTo BisNU_E.

Proof.

unfold UpTo in |- *; intros.

split; intros.

rewrite H2 in H; rewrite H3 in H; apply NU_E_RW with x; auto.

split; intros.

elim (BisNU_E_FTR1 p q H x y); intros; split; intros.

elim (H0 p1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | unfold SB_R_SB in |- *; exists p1; exists x0; split;
    [ apply REF | split; [ assumption | apply REF ] ] ].

elim (H1 q1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | unfold SB_R_SB in |- *; exists x0; exists q1; split;
    [ apply REF | split; [ assumption | apply REF ] ] ].

split; intros.

elim (BisNU_E_IN p q H x); intros; split; intros.

elim (H0 p1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | intro; unfold SB_R_SB in |- *; exists (p1 y); exists (x0 y); split;
    [ apply REF | split; [ auto | apply REF ] ] ].

elim (H1 q1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | intro; unfold SB_R_SB in |- *; exists (x0 y); exists (q1 y); split;
    [ apply REF | split; [ auto | apply REF ] ] ].

split; intros.

elim (BisNU_E_bOUT p q H x); intros; split; intros.

elim (H0 p1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | intros; unfold SB_R_SB in |- *; exists (p1 y); exists (x0 y); split;
    [ apply REF | split; [ auto | apply REF ] ] ].

elim (H1 q1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | intros; unfold SB_R_SB in |- *; exists (x0 y); exists (q1 y); split;
    [ apply REF | split; [ auto | apply REF ] ] ].

elim (BisNU_E_FTR2 p q H); intros; split; intros.

elim (H0 p1 H2); intros; inversion_clear H3; inversion_clear H5.
exists x; split;
 [ assumption
 | left; inversion_clear H3; inversion_clear H5; inversion_clear H3;
    inversion_clear H6; unfold SB_R_SB in |- *; exists x0; 
    exists x1; split; [ assumption | split; assumption ] ].
exists x; split;
 [ assumption
 | right; inversion_clear H3; inversion_clear H5; inversion_clear H3;
    inversion_clear H6; exists x0; exists x1; split;
    [ assumption | split; [ intros; auto | assumption ] ] ].

elim (H1 q1 H2); intros; inversion_clear H3; inversion_clear H5.
exists x; split;
 [ assumption
 | left; inversion_clear H3; inversion_clear H5; inversion_clear H3;
    inversion_clear H6; unfold SB_R_SB in |- *; exists x0; 
    exists x1; split; [ assumption | split; assumption ] ].
exists x; split;
 [ assumption
 | right; inversion_clear H3; inversion_clear H5; inversion_clear H3;
    inversion_clear H6; exists x0; exists x1; split;
    [ assumption | split; [ intros; auto | assumption ] ] ].

Qed.

Lemma NU_EXTR :
 forall (p : name -> proc) (q : proc),
 StBisim (nu (fun y : name => par (p y) q)) (par (nu p) q).

Proof.

intros; apply Completeness; apply Co_Ind with (SBUPTO BisNU_E);
 [ apply UPTO_SB'; exact BisNU_E_UPTO
 | apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *;
    exists (nu (fun y : name => par (p y) q)); exists (par (nu p) q); 
    split; [ apply REF | split; [ apply bisnu_e | apply REF ] ] ].

Qed.

(*******************************************************************)
(* Here is the definition of the strong bisimulation UpTo allowing *)
(* to prove the associativity of the parallel composition.         *)
(*******************************************************************)

Inductive BisPAR_A : proc -> proc -> Prop :=
    bispar_a :
      forall p q r : proc, BisPAR_A (par (par p q) r) (par p (par q r)).

Lemma PAR_A_RW :
 forall (p q : name -> proc) (x : name),
 notin x (nu p) ->
 notin x (nu q) ->
 BisPAR_A (p x) (q x) ->
 forall y : name, notin y (nu p) -> notin y (nu q) -> BisPAR_A (p y) (q y).

Proof.

intros; elim (LEM_name x y); intro.

rewrite <- H4; assumption.

inversion H1.
elim (proc_exp p0 x); elim (proc_exp q0 x); elim (proc_exp r x); intros.
inversion_clear H5; inversion_clear H8; inversion_clear H9.
rewrite H11 in H6; rewrite H11 in H7; rewrite H12 in H6; rewrite H12 in H7;
 rewrite H13 in H6; rewrite H13 in H7.
cut (p = (fun n : name => par (par (x2 n) (x1 n)) (x0 n)));
 [ intro | apply proc_ext with x; auto ].
cut (q = (fun n : name => par (x2 n) (par (x1 n) (x0 n))));
 [ intro | apply proc_ext with x; auto ].
rewrite H9; rewrite H14; apply bispar_a.
inversion_clear H5; inversion_clear H8; inversion_clear H10; apply notin_nu;
 intros; apply notin_par; [ auto | apply notin_par; auto ].
inversion_clear H5; inversion_clear H8; inversion_clear H10; apply notin_nu;
 intros; apply notin_par; [ apply notin_par; auto | auto ].

Qed.

Lemma BisPAR_A_FTR1 :
 forall p q : proc,
 BisPAR_A p q ->
 forall x y : name,
 (forall p1 : proc,
  ftrans p (Out x y) p1 ->
  exists q1 : proc, ftrans q (Out x y) q1 /\ BisPAR_A p1 q1) /\
 (forall q1 : proc,
  ftrans q (Out x y) q1 ->
  exists p1 : proc, ftrans p (Out x y) p1 /\ BisPAR_A p1 q1).

Proof.

intros; inversion H; split; intros.

inversion H2.

inversion H7;
 [ exists (par p7 (par q0 r)); split;
    [ apply fPAR1; assumption | apply bispar_a ]
 | exists (par p0 (par p7 r)); split;
    [ apply fPAR2; apply fPAR1; assumption | apply bispar_a ] ].

exists (par p0 (par q0 p4)); split;
 [ apply fPAR2; apply fPAR2; assumption | apply bispar_a ].

inversion H2.

exists (par (par p3 q0) r); split;
 [ apply fPAR1; apply fPAR1; assumption | apply bispar_a ].

inversion H7;
 [ exists (par (par p0 p6) r); split;
    [ apply fPAR1; apply fPAR2; assumption | apply bispar_a ]
 | exists (par (par p0 q0) p6); split;
    [ apply fPAR2; assumption | apply bispar_a ] ].

Qed.

Lemma BisPAR_A_IN :
 forall p q : proc,
 BisPAR_A p q ->
 forall x : name,
 (forall p1 : name -> proc,
  btrans p (In x) p1 ->
  exists q1 : name -> proc,
    btrans q (In x) q1 /\ (forall y : name, BisPAR_A (p1 y) (q1 y))) /\
 (forall q1 : name -> proc,
  btrans q (In x) q1 ->
  exists p1 : name -> proc,
    btrans p (In x) p1 /\ (forall y : name, BisPAR_A (p1 y) (q1 y))).

Proof.

intros; inversion H; split; intros.

inversion H2.

inversion H7;
 [ exists (fun n : name => par (p7 n) (par q0 r)); split;
    [ apply bPAR1; assumption | intro; apply bispar_a ]
 | exists (fun n : name => par p0 (par (p7 n) r)); split;
    [ change
        (btrans (par p0 (par q0 r)) (In x)
           (fun n : name => par p0 ((fun u : name => par (p7 u) r) n)))
       in |- *; apply bPAR2; apply bPAR1; assumption
    | intro; apply bispar_a ] ].

exists (fun n : name => par p0 (par q0 (p4 n))); split;
 [ change
     (btrans (par p0 (par q0 r)) (In x)
        (fun n : name => par p0 ((fun u : name => par q0 (p4 u)) n))) 
    in |- *; apply bPAR2; apply bPAR2; assumption
 | intro; apply bispar_a ].

inversion H2.

exists (fun n : name => par (par (p3 n) q0) r); split;
 [ change
     (btrans (par (par p0 q0) r) (In x)
        (fun n : name => par ((fun u : name => par (p3 u) q0) n) r)) 
    in |- *; apply bPAR1; apply bPAR1; assumption
 | intro; apply bispar_a ].

inversion H7;
 [ exists (fun n : name => par (par p0 (p6 n)) r); split;
    [ change
        (btrans (par (par p0 q0) r) (In x)
           (fun n : name => par ((fun u : name => par p0 (p6 u)) n) r))
       in |- *; apply bPAR1; apply bPAR2; assumption
    | intro; apply bispar_a ]
 | exists (fun n : name => par (par p0 q0) (p6 n)); split;
    [ apply bPAR2; assumption | intro; apply bispar_a ] ].

Qed.

Lemma BisPAR_A_bOUT :
 forall p q : proc,
 BisPAR_A p q ->
 forall x : name,
 (forall p1 : name -> proc,
  btrans p (bOut x) p1 ->
  exists q1 : name -> proc,
    btrans q (bOut x) q1 /\
    (forall y : name,
     notin y (nu p1) -> notin y (nu q1) -> BisPAR_A (p1 y) (q1 y))) /\
 (forall q1 : name -> proc,
  btrans q (bOut x) q1 ->
  exists p1 : name -> proc,
    btrans p (bOut x) p1 /\
    (forall y : name,
     notin y (nu p1) -> notin y (nu q1) -> BisPAR_A (p1 y) (q1 y))).

Proof.

intros; inversion H; split; intros.

inversion H2.

inversion H7;
 [ exists (fun n : name => par (p7 n) (par q0 r)); split;
    [ apply bPAR1; assumption | intros; apply bispar_a ]
 | exists (fun n : name => par p0 (par (p7 n) r)); split;
    [ change
        (btrans (par p0 (par q0 r)) (bOut x)
           (fun n : name => par p0 ((fun u : name => par (p7 u) r) n)))
       in |- *; apply bPAR2; apply bPAR1; assumption
    | intros; apply bispar_a ] ].

exists (fun n : name => par p0 (par q0 (p4 n))); split;
 [ change
     (btrans (par p0 (par q0 r)) (bOut x)
        (fun n : name => par p0 ((fun u : name => par q0 (p4 u)) n))) 
    in |- *; apply bPAR2; apply bPAR2; assumption
 | intros; apply bispar_a ].

inversion H2.

exists (fun n : name => par (par (p3 n) q0) r); split;
 [ change
     (btrans (par (par p0 q0) r) (bOut x)
        (fun n : name => par ((fun u : name => par (p3 u) q0) n) r)) 
    in |- *; apply bPAR1; apply bPAR1; assumption
 | intros; apply bispar_a ].

inversion H7;
 [ exists (fun n : name => par (par p0 (p6 n)) r); split;
    [ change
        (btrans (par (par p0 q0) r) (bOut x)
           (fun n : name => par ((fun u : name => par p0 (p6 u)) n) r))
       in |- *; apply bPAR1; apply bPAR2; assumption
    | intros; apply bispar_a ]
 | exists (fun n : name => par (par p0 q0) (p6 n)); split;
    [ apply bPAR2; assumption | intros; apply bispar_a ] ].

Qed.

Lemma BisPAR_A_FTR2 :
 forall p q : proc,
 BisPAR_A p q ->
 (forall p1 : proc,
  ftrans p tau p1 ->
  exists q1 : proc,
    ftrans q tau q1 /\
    ((exists p1' : proc,
        (exists q1' : proc,
           StBisim p1 p1' /\ BisPAR_A p1' q1' /\ StBisim q1' q1)) \/
     (exists p1' : name -> proc,
        (exists q1' : name -> proc,
           StBisim p1 (nu p1') /\
           (forall z : name,
            notin z (nu p1') -> notin z (nu q1') -> BisPAR_A (p1' z) (q1' z)) /\
           StBisim (nu q1') q1)))) /\
 (forall q1 : proc,
  ftrans q tau q1 ->
  exists p1 : proc,
    ftrans p tau p1 /\
    ((exists p1' : proc,
        (exists q1' : proc,
           StBisim p1 p1' /\ BisPAR_A p1' q1' /\ StBisim q1' q1)) \/
     (exists p1' : name -> proc,
        (exists q1' : name -> proc,
           StBisim p1 (nu p1') /\
           (forall z : name,
            notin z (nu p1') -> notin z (nu q1') -> BisPAR_A (p1' z) (q1' z)) /\
           StBisim (nu q1') q1)))).

Proof.

intros; inversion H; split; intros.

inversion H2.

inversion H7.
exists (par p7 (par q0 r)); split;
 [ apply fPAR1; assumption
 | left; unfold SB_R_SB in |- *; exists (par (par p7 q0) r);
    exists (par p7 (par q0 r)); split;
    [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (par p0 (par p7 r)); split;
 [ apply fPAR2; apply fPAR1; assumption
 | left; unfold SB_R_SB in |- *; exists (par (par p0 p7) r);
    exists (par p0 (par p7 r)); split;
    [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (par (q1 y) (par q2 r)); split;
 [ apply COM1 with x; [ assumption | apply fPAR1; assumption ]
 | left; unfold SB_R_SB in |- *; exists (par (par (q1 y) q2) r);
    exists (par (q1 y) (par q2 r)); split;
    [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (par q1 (par (q2 y) r)); split;
 [ change
     (ftrans (par p0 (par q0 r)) tau
        (par q1 ((fun n : name => par (q2 n) r) y))) 
    in |- *; apply COM2 with x; [ assumption | apply bPAR1; assumption ]
 | left; unfold SB_R_SB in |- *; exists (par (par q1 (q2 y)) r);
    exists (par q1 (par (q2 y) r)); split;
    [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (nu (fun n : name => par (q1 n) (par (q2 n) r))); split;
 [ change
     (ftrans (par p0 (par q0 r)) tau
        (nu (fun n : name => par (q1 n) ((fun u : name => par (q2 u) r) n))))
    in |- *; apply CLOSE1 with x; [ assumption | apply bPAR1; assumption ]
 | right; exists (fun z : name => par (par (q1 z) (q2 z)) r);
    exists (fun n : name => par (q1 n) (par (q2 n) r)); 
    split;
    [ apply SYM;
       change
         (StBisim
            (nu
               (fun z : name => par ((fun n : name => par (q1 n) (q2 n)) z) r))
            (par (nu (fun z : name => par (q1 z) (q2 z))) r)) 
        in |- *; apply NU_EXTR
    | split; [ intros; apply bispar_a | apply REF ] ] ].
exists (nu (fun n : name => par (q1 n) (par (q2 n) r))); split;
 [ change
     (ftrans (par p0 (par q0 r)) tau
        (nu (fun n : name => par (q1 n) ((fun u : name => par (q2 u) r) n))))
    in |- *; apply CLOSE2 with x; [ assumption | apply bPAR1; assumption ]
 | right; exists (fun z : name => par (par (q1 z) (q2 z)) r);
    exists (fun n : name => par (q1 n) (par (q2 n) r)); 
    split;
    [ apply SYM;
       change
         (StBisim
            (nu
               (fun z : name => par ((fun n : name => par (q1 n) (q2 n)) z) r))
            (par (nu (fun z : name => par (q1 z) (q2 z))) r)) 
        in |- *; apply NU_EXTR
    | split; [ intros; apply bispar_a | apply REF ] ] ].

exists (par p0 (par q0 p4)); split;
 [ apply fPAR2; apply fPAR2; assumption
 | left; exists (par (par p0 q0) p4); exists (par p0 (par q0 p4)); split;
    [ apply REF | split; [ apply bispar_a | apply REF ] ] ].

inversion H5.
exists (par (p6 y) (par q0 q2)); split;
 [ apply COM1 with x; [ assumption | apply fPAR2; assumption ]
 | left; exists (par (par (p6 y) q0) q2); exists (par (p6 y) (par q0 q2));
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (par p0 (par (p6 y) q2)); split;
 [ apply fPAR2; apply COM1 with x; assumption
 | left; exists (par (par p0 (p6 y)) q2); exists (par p0 (par (p6 y) q2));
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].

inversion H5.
exists (par p6 (par q0 (q2 y))); split;
 [ change
     (ftrans (par p0 (par q0 r)) tau
        (par p6 ((fun n : name => par q0 (q2 n)) y))) 
    in |- *; apply COM2 with x; [ assumption | apply bPAR2; assumption ]
 | left; exists (par (par p6 q0) (q2 y)); exists (par p6 (par q0 (q2 y)));
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (par p0 (par p6 (q2 y))); split;
 [ apply fPAR2; apply COM2 with x; assumption
 | left; exists (par (par p0 p6) (q2 y)); exists (par p0 (par p6 (q2 y)));
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].

inversion H5.
exists (nu (fun n : name => par (p6 n) (par q0 (q2 n)))); split;
 [ change
     (ftrans (par p0 (par q0 r)) tau
        (nu (fun y : name => par (p6 y) ((fun n : name => par q0 (q2 n)) y))))
    in |- *; apply CLOSE1 with x; [ assumption | apply bPAR2; assumption ]
 | right; exists (fun z : name => par (par (p6 z) q0) (q2 z));
    exists (fun n : name => par (p6 n) (par q0 (q2 n))); 
    split; [ apply REF | split; [ intros; apply bispar_a | apply REF ] ] ].
exists (par p0 (nu (fun n : name => par (p6 n) (q2 n)))); split;
 [ apply fPAR2; apply CLOSE1 with x; assumption
 | right; exists (fun z : name => par (par p0 (p6 z)) (q2 z));
    exists (fun n : name => par p0 (par (p6 n) (q2 n))); 
    split;
    [ apply REF
    | split;
       [ intros; apply bispar_a
       | apply TRANS with (par (nu (fun n : name => par (p6 n) (q2 n))) p0);
          [ apply
             TRANS with (nu (fun n : name => par (par (p6 n) (q2 n)) p0));
             [ apply NU_S; intros; apply COMM_PAR
             | change
                 (StBisim
                    (nu
                       (fun n : name =>
                        par ((fun u : name => par (p6 u) (q2 u)) n) p0))
                    (par (nu (fun n : name => par (p6 n) (q2 n))) p0))
                in |- *; apply NU_EXTR ]
          | apply COMM_PAR ] ] ] ].

inversion H5.
exists (nu (fun n : name => par (p6 n) (par q0 (q2 n)))); split;
 [ change
     (ftrans (par p0 (par q0 r)) tau
        (nu (fun y : name => par (p6 y) ((fun n : name => par q0 (q2 n)) y))))
    in |- *; apply CLOSE2 with x; [ assumption | apply bPAR2; assumption ]
 | right; exists (fun z : name => par (par (p6 z) q0) (q2 z));
    exists (fun n : name => par (p6 n) (par q0 (q2 n))); 
    split; [ apply REF | split; [ intros; apply bispar_a | apply REF ] ] ].
exists (par p0 (nu (fun n : name => par (p6 n) (q2 n)))); split;
 [ apply fPAR2; apply CLOSE2 with x; assumption
 | right; exists (fun z : name => par (par p0 (p6 z)) (q2 z));
    exists (fun n : name => par p0 (par (p6 n) (q2 n))); 
    split;
    [ apply REF
    | split;
       [ intros; apply bispar_a
       | apply TRANS with (par (nu (fun n : name => par (p6 n) (q2 n))) p0);
          [ apply
             TRANS with (nu (fun n : name => par (par (p6 n) (q2 n)) p0));
             [ apply NU_S; intros; apply COMM_PAR
             | change
                 (StBisim
                    (nu
                       (fun n : name =>
                        par ((fun u : name => par (p6 u) (q2 u)) n) p0))
                    (par (nu (fun n : name => par (p6 n) (q2 n))) p0))
                in |- *; apply NU_EXTR ]
          | apply COMM_PAR ] ] ] ].

inversion H2.

exists (par (par p3 q0) r); split;
 [ apply fPAR1; apply fPAR1; assumption
 | left; exists (par (par p3 q0) r); exists (par p3 (par q0 r)); split;
    [ apply REF | split; [ apply bispar_a | apply REF ] ] ].

inversion H7.
exists (par (par p0 p6) r); split;
 [ apply fPAR1; apply fPAR2; assumption
 | left; exists (par (par p0 p6) r); exists (par p0 (par p6 r)); split;
    [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (par (par p0 q0) p6); split;
 [ apply fPAR2; assumption
 | left; exists (par (par p0 q0) p6); exists (par p0 (par q0 p6)); split;
    [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (par (par p0 (q3 y)) q2); split;
 [ change
     (ftrans (par (par p0 q0) r) tau
        (par ((fun n : name => par p0 (q3 n)) y) q2)) 
    in |- *; apply COM1 with x; [ apply bPAR2; assumption | assumption ]
 | left; exists (par (par p0 (q3 y)) q2); exists (par p0 (par (q3 y) q2));
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (par (par p0 q2) (q3 y)); split;
 [ apply COM2 with x; [ apply fPAR2; assumption | assumption ]
 | left; exists (par (par p0 q2) (q3 y)); exists (par p0 (par q2 (q3 y)));
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (nu (fun n : name => par (par p0 (q2 n)) (q3 n))); split;
 [ change
     (ftrans (par (par p0 q0) r) tau
        (nu (fun n : name => par ((fun u : name => par p0 (q2 u)) n) (q3 n))))
    in |- *; apply CLOSE1 with x; [ apply bPAR2; assumption | assumption ]
 | right; exists (fun n : name => par (par p0 (q2 n)) (q3 n));
    exists (fun n : name => par p0 (par (q2 n) (q3 n))); 
    split;
    [ apply REF
    | split;
       [ intros; apply bispar_a
       | apply TRANS with (nu (fun n : name => par (par (q2 n) (q3 n)) p0));
          [ apply NU_S; intros; apply COMM_PAR
          | apply
             TRANS with (par (nu (fun z : name => par (q2 z) (q3 z))) p0);
             [ change
                 (StBisim
                    (nu
                       (fun n : name =>
                        par ((fun u : name => par (q2 u) (q3 u)) n) p0))
                    (par (nu (fun z : name => par (q2 z) (q3 z))) p0))
                in |- *; apply NU_EXTR
             | apply COMM_PAR ] ] ] ] ].
exists (nu (fun n : name => par (par p0 (q2 n)) (q3 n))); split;
 [ change
     (ftrans (par (par p0 q0) r) tau
        (nu (fun n : name => par ((fun u : name => par p0 (q2 u)) n) (q3 n))))
    in |- *; apply CLOSE2 with x; [ apply bPAR2; assumption | assumption ]
 | right; exists (fun n : name => par (par p0 (q2 n)) (q3 n));
    exists (fun n : name => par p0 (par (q2 n) (q3 n))); 
    split;
    [ apply REF
    | split;
       [ intros; apply bispar_a
       | apply TRANS with (nu (fun n : name => par (par (q2 n) (q3 n)) p0));
          [ apply NU_S; intros; apply COMM_PAR
          | apply
             TRANS with (par (nu (fun z : name => par (q2 z) (q3 z))) p0);
             [ change
                 (StBisim
                    (nu
                       (fun n : name =>
                        par ((fun u : name => par (q2 u) (q3 u)) n) p0))
                    (par (nu (fun z : name => par (q2 z) (q3 z))) p0))
                in |- *; apply NU_EXTR
             | apply COMM_PAR ] ] ] ] ].

inversion H6.
exists (par (par (q3 y) p5) r); split;
 [ apply fPAR1; apply COM1 with x; assumption
 | left; exists (par (par (q3 y) p5) r); exists (par (q3 y) (par p5 r));
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (par (par (q3 y) q0) p5); split;
 [ change
     (ftrans (par (par p0 q0) r) tau
        (par ((fun n : name => par (q3 n) q0) y) p5)) 
    in |- *; apply COM1 with x; [ apply bPAR1; assumption | assumption ]
 | left; exists (par (par (q3 y) q0) p5); exists (par (q3 y) (par q0 p5));
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].

inversion H6.
exists (par (par q2 (p5 y)) r); split;
 [ apply fPAR1; apply COM2 with x; assumption
 | left; exists (par (par q2 (p5 y)) r); exists (par q2 (par (p5 y) r));
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].
exists (par (par q2 q0) (p5 y)); split;
 [ apply COM2 with x; [ apply fPAR1; assumption | assumption ]
 | left; exists (par (par q2 q0) (p5 y)); exists (par q2 (par q0 (p5 y)));
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].

inversion H6.
exists (par (nu (fun n : name => par (q2 n) (p5 n))) r); split;
 [ apply fPAR1; apply CLOSE1 with x; assumption
 | right; exists (fun n : name => par (par (q2 n) (p5 n)) r);
    exists (fun z : name => par (q2 z) (par (p5 z) r)); 
    split;
    [ apply SYM;
       change
         (StBisim
            (nu
               (fun n : name => par ((fun u : name => par (q2 u) (p5 u)) n) r))
            (par (nu (fun n : name => par (q2 n) (p5 n))) r)) 
        in |- *; apply NU_EXTR
    | split; [ intros; apply bispar_a | apply REF ] ] ].
exists (nu (fun n : name => par (par (q2 n) q0) (p5 n))); split;
 [ change
     (ftrans (par (par p0 q0) r) tau
        (nu (fun n : name => par ((fun u : name => par (q2 u) q0) n) (p5 n))))
    in |- *; apply CLOSE1 with x; [ apply bPAR1; assumption | assumption ]
 | right; exists (fun n : name => par (par (q2 n) q0) (p5 n));
    exists (fun z : name => par (q2 z) (par q0 (p5 z))); 
    split; [ apply REF | split; [ intros; apply bispar_a | apply REF ] ] ].

inversion H6.
exists (par (nu (fun n : name => par (q2 n) (p5 n))) r); split;
 [ apply fPAR1; apply CLOSE2 with x; assumption
 | right; exists (fun n : name => par (par (q2 n) (p5 n)) r);
    exists (fun z : name => par (q2 z) (par (p5 z) r)); 
    split;
    [ apply SYM;
       change
         (StBisim
            (nu
               (fun n : name => par ((fun u : name => par (q2 u) (p5 u)) n) r))
            (par (nu (fun n : name => par (q2 n) (p5 n))) r)) 
        in |- *; apply NU_EXTR
    | split; [ intros; apply bispar_a | apply REF ] ] ].
exists (nu (fun n : name => par (par (q2 n) q0) (p5 n))); split;
 [ change
     (ftrans (par (par p0 q0) r) tau
        (nu (fun n : name => par ((fun u : name => par (q2 u) q0) n) (p5 n))))
    in |- *; apply CLOSE2 with x; [ apply bPAR1; assumption | assumption ]
 | right; exists (fun n : name => par (par (q2 n) q0) (p5 n));
    exists (fun z : name => par (q2 z) (par q0 (p5 z))); 
    split; [ apply REF | split; [ intros; apply bispar_a | apply REF ] ] ].

Qed.

(* BisPAR_A is a strong bisimulation UpTo *)

Lemma BisPAR_A_UPTO : UpTo BisPAR_A.

Proof.

unfold UpTo in |- *; intros.

split; intros.

rewrite H2 in H; rewrite H3 in H; apply PAR_A_RW with x; auto.

split; intros.

elim (BisPAR_A_FTR1 p q H x y); intros; split; intros.

elim (H0 p1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | unfold SB_R_SB in |- *; exists p1; exists x0; split;
    [ apply REF | split; [ assumption | apply REF ] ] ].

elim (H1 q1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | unfold SB_R_SB in |- *; exists x0; exists q1; split;
    [ apply REF | split; [ assumption | apply REF ] ] ].

split; intros.

elim (BisPAR_A_IN p q H x); intros; split; intros.

elim (H0 p1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | intro; unfold SB_R_SB in |- *; exists (p1 y); exists (x0 y); split;
    [ apply REF | split; [ auto | apply REF ] ] ].

elim (H1 q1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | intro; unfold SB_R_SB in |- *; exists (x0 y); exists (q1 y); split;
    [ apply REF | split; [ auto | apply REF ] ] ].

split; intros.

elim (BisPAR_A_bOUT p q H x); intros; split; intros.

elim (H0 p1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | intros; unfold SB_R_SB in |- *; exists (p1 y); exists (x0 y); split;
    [ apply REF | split; [ auto | apply REF ] ] ].

elim (H1 q1 H2); intros; inversion_clear H3.
exists x0; split;
 [ assumption
 | intros; unfold SB_R_SB in |- *; exists (x0 y); exists (q1 y); split;
    [ apply REF | split; [ auto | apply REF ] ] ].

elim (BisPAR_A_FTR2 p q H); intros; split; intros.

elim (H0 p1 H2); intros; inversion_clear H3; inversion_clear H5.
exists x; split;
 [ assumption
 | left; inversion_clear H3; inversion_clear H5; inversion_clear H3;
    inversion_clear H6; unfold SB_R_SB in |- *; exists x0; 
    exists x1; split; [ assumption | split; assumption ] ].
exists x; split;
 [ assumption
 | right; inversion_clear H3; inversion_clear H5; inversion_clear H3;
    inversion_clear H6; exists x0; exists x1; split;
    [ assumption | split; [ intros; auto | assumption ] ] ].

elim (H1 q1 H2); intros; inversion_clear H3; inversion_clear H5.
exists x; split;
 [ assumption
 | left; inversion_clear H3; inversion_clear H5; inversion_clear H3;
    inversion_clear H6; unfold SB_R_SB in |- *; exists x0; 
    exists x1; split; [ assumption | split; assumption ] ].
exists x; split;
 [ assumption
 | right; inversion_clear H3; inversion_clear H5; inversion_clear H3;
    inversion_clear H6; exists x0; exists x1; split;
    [ assumption | split; [ intros; auto | assumption ] ] ].

Qed.

Lemma ASS_PAR :
 forall p q r : proc, StBisim (par (par p q) r) (par p (par q r)).

Proof.

intros; apply Completeness; apply Co_Ind with (SBUPTO BisPAR_A);
 [ apply UPTO_SB'; exact BisPAR_A_UPTO
 | apply sbupto with 0; simpl in |- *; unfold SB_R_SB in |- *;
    exists (par (par p q) r); exists (par p (par q r)); 
    split; [ apply REF | split; [ apply bispar_a | apply REF ] ] ].

Qed.

(* End upto. *)

(* Section structural_congruence2. *)

Lemma PAR_S2 :
 forall p q r s : proc,
 StBisim p q -> StBisim r s -> StBisim (par p r) (par q s).

Proof. (* This lemma depends on Lemmata TRANS, PAR_S and COMM_PAR. *)

intros; apply TRANS with (par s q);
 [ apply TRANS with (par r q);
    [ apply TRANS with (par q r);
       [ apply PAR_S; assumption | apply COMM_PAR ]
    | apply PAR_S; assumption ]
 | apply COMM_PAR ].

Qed.

(* End structural_congruence2. *)

(* Section restriction_laws2. *)

Lemma NU_P : forall p : proc, StBisim (nu (fun x : name => p)) p.

Proof. (* This lemma depends on Lemmata REF, SYM, TRANS, NU_S,
        * ID_PAR, COMM_PAR, NU_EXTR, PAR_S2, NU_NIL.
        *)

intro; apply TRANS with (nu (fun _ : name => par p nil)).
apply NU_S; intros; apply SYM; apply ID_PAR.
apply TRANS with (nu (fun _ : name => par nil p)).
apply NU_S; intros; apply COMM_PAR.
apply TRANS with (par nil p).
apply TRANS with (par (nu (fun x : name => nil)) p).
change
  (StBisim (nu (fun n : name => par ((fun x : name => nil) n) p))
     (par (nu (fun x : name => nil)) p)) in |- *; apply NU_EXTR.
apply PAR_S2; [ apply NU_NIL | apply REF ].
apply TRANS with (par p nil); [ apply COMM_PAR | apply ID_PAR ].

Qed.

Lemma NU_PAR1 :
 forall (p : name -> proc) (q : proc),
 StBisim (nu (fun x : name => par (p x) q))
   (par (nu p) (nu (fun x : name => q))).

Proof. (* This lemma depends on Lemmata REF, SYM, TRANS, NU_EXTR, NU_P, PAR_S2. *)

intros; apply TRANS with (par (nu p) q);
 [ apply NU_EXTR | apply PAR_S2; [ apply REF | apply SYM; apply NU_P ] ].

Qed.

Lemma NU_PAR2 :
 forall (p : proc) (q : name -> proc),
 StBisim (nu (fun x : name => par p (q x)))
   (par (nu (fun x : name => p)) (nu q)).

Proof. (* This lemma depends on Lemmata REF, SYM, TRANS, NU_EXTR, NU_P, PAR_S2, COMM_PAR. *)

intros; apply TRANS with (nu (fun x : name => par (q x) p));
 [ apply NU_S; intros; apply COMM_PAR
 | apply TRANS with (par (nu q) p);
    [ apply NU_EXTR
    | apply TRANS with (par (nu q) (nu (fun _ : name => p)));
       [ apply PAR_S2; [ apply REF | apply SYM; apply NU_P ]
       | apply COMM_PAR ] ] ].

Qed.

(* End restriction_laws2. *)

(* Section matching_laws. *)

Lemma MATCH1 :
 forall (p : proc) (x y : name), x = y -> StBisim (match_ x y p) p.

Proof. (* This lemma depends on Lemma REF. *)

intros; apply sb; do 3 try (split; intros).

inversion_clear H0.
exists p1; split; [ assumption | apply REF ].
exists q1; split; [ rewrite H; apply fMATCH; assumption | apply REF ].

inversion_clear H0.
exists p1; split; [ assumption | intro; apply REF ].
exists q1; split; [ rewrite H; apply bMATCH; assumption | intro; apply REF ].

inversion_clear H0.
exists p1; split; [ assumption | intros; apply REF ].
exists q1; split; [ rewrite H; apply bMATCH; assumption | intros; apply REF ].

Qed.

Lemma MATCH2 :
 forall (p : proc) (x y : name), x <> y -> StBisim (match_ x y p) nil.

Proof. (* This lemma is proved from scratch. *)

intros; apply sb; do 3 try (split; intros).

inversion H0; absurd (x = y); assumption.
inversion_clear H0.

inversion H0; absurd (x = y); assumption.
inversion_clear H0.

inversion H0; absurd (x = y); assumption.
inversion_clear H0.

Qed.

Lemma MISMATCH1 :
 forall (p : proc) (x y : name), x <> y -> StBisim (mismatch x y p) p.

Proof. (* This lemma depends on Lemma REF. *)

intros; apply sb; do 3 try (split; intros).

inversion_clear H0.
exists p1; split; [ assumption | apply REF ].
exists q1; split; [ apply fMISMATCH; assumption | apply REF ].

inversion_clear H0.
exists p1; split; [ assumption | intro; apply REF ].
exists q1; split; [ apply bMISMATCH; assumption | intro; apply REF ].

inversion_clear H0.
exists p1; split; [ assumption | intros; apply REF ].
exists q1; split; [ apply bMISMATCH; assumption | intros; apply REF ].

Qed.

Lemma MISMATCH2 :
 forall (p : proc) (x y : name), x = y -> StBisim (mismatch x y p) nil.

Proof. (* This lemma is proved from scratch. *)

intros; apply sb; do 3 try (split; intros).

inversion H0; absurd (x = y); assumption.
inversion_clear H0.

inversion H0; absurd (x = y); assumption.
inversion_clear H0.

inversion H0; absurd (x = y); assumption.
inversion_clear H0.

Qed.

(* End matching_laws. *)
