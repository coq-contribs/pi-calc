(*******************************************************)
(*                                                     *)
(* Technical lemmata of the metatheory of pi-calculus  *)
(*    (Milner-Parrow-Walker's Lemmata 1, 3, 4, 6).     *)
(*                                                     *)
(*******************************************************)
(*                                                     *)
(* File   : basiclemmata.v                             *)
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

Require Export xadequacy.

Require Export hoaspack.

(*******************************************************)
(* Mutual induction principle needed in order to prove *)
(* results about LTS.                                  *)
(*******************************************************)

Scheme ftrans_btrans_ind := Minimality for ftrans
  Sort Prop
  with btrans_ftrans_ind := Minimality for btrans Sort Prop.

Section MPW_Lemma1.

Lemma FTR_L1 :
 forall (p q : proc) (a : f_act) (x : name),
 notin x p -> ftrans p a q -> f_act_notin x a /\ notin x q.

Proof.

intros.
generalize H0.
generalize H.
generalize x.
pattern p, a, q in |- *;
 apply
  ftrans_btrans_ind
   with
     (fun (p : proc) (a : b_act) (q : name -> proc) =>
      forall x : name,
      notin x p -> btrans p a q -> b_act_notin x a /\ notin x (nu q)); 
 intros; auto.

(* TAU Case *)

split; [ apply f_act_notin_tau | inversion H1; assumption ].

(* OUT Case *)

inversion H1; split; [ apply f_act_notin_Out; assumption | assumption ].

(* fSUM1 Case *)

inversion_clear H3.
elim (H2 x0 H5 H1); intros; split; assumption.

(* fSUM2 Case *)

inversion_clear H3.
elim (H2 x0 H6 H1); intros; split; assumption.

(* fPAR1 Case *)

inversion_clear H3.
elim (H2 x0 H5 H1); intros; split;
 [ assumption | apply notin_par; assumption ].

(* fPAR2 Case *)

inversion_clear H3.
elim (H2 x0 H6 H1); intros; split;
 [ assumption | apply notin_par; assumption ].

(* fMATCH Case *)

inversion_clear H3.
elim (H2 x1 H7 H1); intros; split; assumption.

(* fMISMATCH Case *)

inversion_clear H4.
elim (H3 x1 H8 H2); intros; split; assumption.

(* fBANG Case *)

inversion_clear H3.
cut (notin x0 (par p0 (bang p0)));
 [ intro | apply notin_par; [ assumption | apply notin_bang; assumption ] ].
elim (H2 x0 H3 H1); intros; split; assumption.

(* COM1 Case *)

inversion_clear H5.
elim (H2 x1 H7 H1); intros; elim (H4 x1 H8 H3); intros; split;
 [ apply f_act_notin_tau | apply notin_par ].
inversion_clear H10; inversion_clear H9; auto.
assumption.

(* COM2 Case *)

inversion_clear H5.
elim (H2 x1 H7 H1); intros; elim (H4 x1 H8 H3); intros; split;
 [ apply f_act_notin_tau | apply notin_par ].
assumption.
inversion_clear H5; inversion_clear H11; auto.

(* fRES Case *)

generalize H1 H2; elim a0; intros.
elim (unsat (par (nu p1) (nu p2)) (cons x0 l)); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
cut (ftrans (p1 x1) tau (p2 x1));
 [ intro | apply H5; auto; try apply f_act_notin_tau ].
cut (f_act_notin x1 tau); [ intro | apply f_act_notin_tau ].
cut (notin x0 (p1 x1)); [ intro | inversion H3; auto ].
elim (H6 x1 H7 H10 H11 H12 x0 H13 H9); intros.
split; [ assumption | apply proc_mono with x1; assumption ].

elim (unsat (par (nu p1) (nu p2)) (cons x0 (cons n (cons n0 l)))); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
inversion_clear H11.
inversion_clear H12.
cut (ftrans (p1 x1) (Out n n0) (p2 x1));
 [ intro | apply H5; auto; try apply f_act_notin_Out; auto ].
cut (f_act_notin x1 (Out n n0)); [ intro | apply f_act_notin_Out; auto ].
cut (notin x0 (p1 x1)); [ intro | inversion H3; auto ].
elim (H6 x1 H7 H10 H13 H14 x0 H15 H12); intros.
split; [ assumption | apply proc_mono with x1; assumption ].

(* CLOSE1 Case *)

split; [ apply f_act_notin_tau | apply notin_nu; intros ].
inversion_clear H5.
elim (H2 x1 H8 H1); intros; elim (H4 x1 H9 H3); intros.
apply notin_par; [ inversion_clear H10; auto | inversion_clear H12; auto ].

(* CLOSE2 Case *)

split; [ apply f_act_notin_tau | apply notin_nu; intros ].
inversion_clear H5.
elim (H2 x1 H8 H1); intros; elim (H4 x1 H9 H3); intros.
apply notin_par; [ inversion_clear H10; auto | inversion_clear H12; auto ].

(* IN Case *)

inversion_clear H1; split;
 [ apply b_act_notin_In; auto | apply notin_nu; intros; auto ].

(* bSUM1 Case *)

inversion_clear H3.
elim (H2 x0 H5 H1); intros; split; assumption.

(* bSUM2 Case *)

inversion_clear H3.
elim (H2 x0 H6 H1); intros; split; assumption.

(* bPAR1 Case *)

inversion_clear H3.
elim (H2 x0 H5 H1); intros; split;
 [ assumption | apply notin_nu; intros; apply notin_par; inversion H7; auto ].

(* bPAR2 Case *)

inversion_clear H3.
elim (H2 x0 H6 H1); intros; split;
 [ assumption | apply notin_nu; intros; apply notin_par; inversion H7; auto ].

(* bMATCH Case *)

inversion_clear H3.
elim (H2 x1 H7 H1); intros; split; assumption.

(* bMISMATCH Case *)

inversion_clear H4.
elim (H3 x1 H8 H2); intros; split; assumption.

(* bBANG Case *)

inversion_clear H3.
cut (notin x0 (par p0 (bang p0)));
 [ intro | apply notin_par; [ assumption | apply notin_bang; assumption ] ].
elim (H2 x0 H3 H1); intros; split; assumption.

(* bRES Case *)

generalize H1 H2; elim a0; intros.
elim
 (unsat (par (nu p1) (nu (fun n0 : name => nu (p2 n0)))) (cons x0 (cons n l)));
 intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
inversion_clear H11.
cut (btrans (p1 x1) (In n) (p2 x1));
 [ intro | apply H5; auto; try apply b_act_notin_In; auto ].
cut (b_act_notin x1 (In n)); [ intro | apply b_act_notin_In; auto ].
cut (notin x0 (p1 x1)); [ intro | inversion H3; auto ].
elim (H6 x1 H7 H10 H13 H12 x0 H14 H11); intros.
split;
 [ assumption
 | apply notin_nu; intros; apply proc_mono with x1; inversion H16; auto ].

elim
 (unsat (par (nu p1) (nu (fun n0 : name => nu (p2 n0)))) (cons x0 (cons n l)));
 intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
inversion_clear H11.
cut (btrans (p1 x1) (bOut n) (p2 x1));
 [ intro | apply H5; auto; try apply b_act_notin_bOut; auto ].
cut (b_act_notin x1 (bOut n)); [ intro | apply b_act_notin_bOut; auto ].
cut (notin x0 (p1 x1)); [ intro | inversion H3; auto ].
elim (H6 x1 H7 H10 H13 H12 x0 H14 H11); intros.
split;
 [ assumption
 | apply notin_nu; intros; apply proc_mono with x1; inversion H16; auto ].

(* OPEN Case *)

elim (unsat (par (nu p1) (nu p2)) (cons x0 (cons x1 l))); intros.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
inversion_clear H9.
cut (ftrans (p1 x2) (Out x0 x2) (p2 x2)); [ intro | apply H1; auto ].
cut (notin x1 (p1 x2)); [ intro | inversion H3; auto ].
cut (x0 <> x2); [ intro | auto ].
elim (H2 x2 H5 H8 H12 H10 x1 H11 H9); intros.
split;
 [ inversion_clear H13; apply b_act_notin_bOut; auto
 | apply proc_mono with x2; auto ].

Qed.

Lemma BTR_L1 :
 forall (p : proc) (q : name -> proc) (a : b_act) (x : name),
 notin x p -> btrans p a q -> b_act_notin x a /\ notin x (nu q).

Proof.

intros.
generalize H0.
generalize H.
generalize x.
pattern p, a, q in |- *;
 apply
  btrans_ftrans_ind
   with
     (fun (p : proc) (a : f_act) (q : proc) =>
      forall x : name,
      notin x p -> ftrans p a q -> f_act_notin x a /\ notin x q); 
 intros; auto.

(* TAU Case *)

split; [ apply f_act_notin_tau | inversion H1; assumption ].

(* OUT Case *)

inversion H1; split; [ apply f_act_notin_Out; assumption | assumption ].

(* fSUM1 Case *)

inversion_clear H3.
elim (H2 x0 H5 H1); intros; split; assumption.

(* fSUM2 Case *)

inversion_clear H3.
elim (H2 x0 H6 H1); intros; split; assumption.

(* fPAR1 Case *)

inversion_clear H3.
elim (H2 x0 H5 H1); intros; split;
 [ assumption | apply notin_par; assumption ].

(* fPAR2 Case *)

inversion_clear H3.
elim (H2 x0 H6 H1); intros; split;
 [ assumption | apply notin_par; assumption ].

(* fMATCH Case *)

inversion_clear H3.
elim (H2 x1 H7 H1); intros; split; assumption.

(* fMISMATCH Case *)

inversion_clear H4.
elim (H3 x1 H8 H2); intros; split; assumption.

(* fBANG Case *)

inversion_clear H3.
cut (notin x0 (par p0 (bang p0)));
 [ intro | apply notin_par; [ assumption | apply notin_bang; assumption ] ].
elim (H2 x0 H3 H1); intros; split; assumption.

(* COM1 Case *)

inversion_clear H5.
elim (H2 x1 H7 H1); intros; elim (H4 x1 H8 H3); intros; split;
 [ apply f_act_notin_tau | apply notin_par ].
inversion_clear H10; inversion_clear H9; auto.
assumption.

(* COM2 Case *)

inversion_clear H5.
elim (H2 x1 H7 H1); intros; elim (H4 x1 H8 H3); intros; split;
 [ apply f_act_notin_tau | apply notin_par ].
assumption.
inversion_clear H5; inversion_clear H11; auto.

(* fRES Case *)

generalize H1 H2; elim a0; intros.
elim (unsat (par (nu p1) (nu p2)) (cons x0 l)); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
cut (ftrans (p1 x1) tau (p2 x1));
 [ intro | apply H5; auto; try apply f_act_notin_tau ].
cut (f_act_notin x1 tau); [ intro | apply f_act_notin_tau ].
cut (notin x0 (p1 x1)); [ intro | inversion H3; auto ].
elim (H6 x1 H7 H10 H11 H12 x0 H13 H9); intros.
split; [ assumption | apply proc_mono with x1; assumption ].

elim (unsat (par (nu p1) (nu p2)) (cons x0 (cons n (cons n0 l)))); intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
inversion_clear H11.
inversion_clear H12.
cut (ftrans (p1 x1) (Out n n0) (p2 x1));
 [ intro | apply H5; auto; try apply f_act_notin_Out; auto ].
cut (f_act_notin x1 (Out n n0)); [ intro | apply f_act_notin_Out; auto ].
cut (notin x0 (p1 x1)); [ intro | inversion H3; auto ].
elim (H6 x1 H7 H10 H13 H14 x0 H15 H12); intros.
split; [ assumption | apply proc_mono with x1; assumption ].

(* CLOSE1 Case *)

split; [ apply f_act_notin_tau | apply notin_nu; intros ].
inversion_clear H5.
elim (H2 x1 H8 H1); intros; elim (H4 x1 H9 H3); intros.
apply notin_par; [ inversion_clear H10; auto | inversion_clear H12; auto ].

(* CLOSE2 Case *)

split; [ apply f_act_notin_tau | apply notin_nu; intros ].
inversion_clear H5.
elim (H2 x1 H8 H1); intros; elim (H4 x1 H9 H3); intros.
apply notin_par; [ inversion_clear H10; auto | inversion_clear H12; auto ].

(* IN Case *)

inversion_clear H1; split;
 [ apply b_act_notin_In; auto | apply notin_nu; intros; auto ].

(* bSUM1 Case *)

inversion_clear H3.
elim (H2 x0 H5 H1); intros; split; assumption.

(* bSUM2 Case *)

inversion_clear H3.
elim (H2 x0 H6 H1); intros; split; assumption.

(* bPAR1 Case *)

inversion_clear H3.
elim (H2 x0 H5 H1); intros; split;
 [ assumption | apply notin_nu; intros; apply notin_par; inversion H7; auto ].

(* bPAR2 Case *)

inversion_clear H3.
elim (H2 x0 H6 H1); intros; split;
 [ assumption | apply notin_nu; intros; apply notin_par; inversion H7; auto ].

(* bMATCH Case *)

inversion_clear H3.
elim (H2 x1 H7 H1); intros; split; assumption.

(* bMISMATCH Case *)

inversion_clear H4.
elim (H3 x1 H8 H2); intros; split; assumption.

(* bBANG Case *)

inversion_clear H3.
cut (notin x0 (par p0 (bang p0)));
 [ intro | apply notin_par; [ assumption | apply notin_bang; assumption ] ].
elim (H2 x0 H3 H1); intros; split; assumption.

(* bRES Case *)

generalize H1 H2; elim a0; intros.
elim
 (unsat (par (nu p1) (nu (fun n0 : name => nu (p2 n0)))) (cons x0 (cons n l)));
 intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
inversion_clear H11.
cut (btrans (p1 x1) (In n) (p2 x1));
 [ intro | apply H5; auto; try apply b_act_notin_In; auto ].
cut (b_act_notin x1 (In n)); [ intro | apply b_act_notin_In; auto ].
cut (notin x0 (p1 x1)); [ intro | inversion H3; auto ].
elim (H6 x1 H7 H10 H13 H12 x0 H14 H11); intros.
split;
 [ assumption
 | apply notin_nu; intros; apply proc_mono with x1; inversion H16; auto ].

elim
 (unsat (par (nu p1) (nu (fun n0 : name => nu (p2 n0)))) (cons x0 (cons n l)));
 intros.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
inversion_clear H11.
cut (btrans (p1 x1) (bOut n) (p2 x1));
 [ intro | apply H5; auto; try apply b_act_notin_bOut; auto ].
cut (b_act_notin x1 (bOut n)); [ intro | apply b_act_notin_bOut; auto ].
cut (notin x0 (p1 x1)); [ intro | inversion H3; auto ].
elim (H6 x1 H7 H10 H13 H12 x0 H14 H11); intros.
split;
 [ assumption
 | apply notin_nu; intros; apply proc_mono with x1; inversion H16; auto ].

(* OPEN Case *)

elim (unsat (par (nu p1) (nu p2)) (cons x0 (cons x1 l))); intros.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
inversion_clear H9.
cut (ftrans (p1 x2) (Out x0 x2) (p2 x2)); [ intro | apply H1; auto ].
cut (notin x1 (p1 x2)); [ intro | inversion H3; auto ].
cut (x0 <> x2); [ intro | auto ].
elim (H2 x2 H5 H8 H12 H10 x1 H11 H9); intros.
split;
 [ inversion_clear H13; apply b_act_notin_bOut; auto
 | apply proc_mono with x2; auto ].

Qed.

Lemma Aux1 :
 forall (p q : proc) (a : f_act) (x : name),
 f_act_isin x a -> ftrans p a q -> isin x p.

Proof.

intros.
apply isin_to_notin.
unfold not in |- *; intro.
absurd (x = x).
elim (FTR_L1 p q a x H1 H0); intros.
apply Sep_f_act with a; assumption.
trivial.

Qed.

Lemma Aux2 :
 forall (p : proc) (a : b_act) (q : name -> proc) (x : name),
 b_act_isin x a -> btrans p a q -> isin x p.

Proof.

intros.
apply isin_to_notin.
unfold not in |- *; intro.
absurd (x = x).
elim (BTR_L1 p q a x H1 H0); intros.
apply Sep_b_act with a; assumption.
trivial.

Qed.

End MPW_Lemma1.

Section MPW_Lemma3.

(*************************************************)
(* Lemmata 3 and 4 are the same in our encoding. *)
(*************************************************)

Lemma L3 :
 forall (p q : proc) (a : f_act) (p' q' : name -> proc) 
   (a' : name -> f_act) (x : name),
 notin x (nu p') ->
 notin x (nu q') ->
 f_act_notin_ho x a' ->
 p = p' x ->
 q = q' x ->
 a = a' x ->
 ftrans p a q ->
 forall y : name,
 notin y (nu p') ->
 notin y (nu q') -> f_act_notin_ho y a' -> ftrans (p' y) (a' y) (q' y).

Proof.

do 14 intro.
generalize H5.
generalize H4.
generalize H3.
generalize H2.
generalize H1.
generalize H0.
generalize H.
generalize x.
generalize a'.
generalize q'.
generalize p'.
pattern p, a, q in |- *;
 apply
  ftrans_btrans_ind
   with
     (fun (p : proc) (a : b_act) (q : name -> proc) =>
      forall (p' : name -> proc) (q' : name -> name -> proc)
        (a' : name -> b_act) (x : name),
      notin x (nu p') ->
      notin x (nu (fun z : name => nu (q' z))) ->
      b_act_notin_ho x a' ->
      p = p' x ->
      q = q' x ->
      a = a' x ->
      btrans p a q ->
      forall y : name,
      notin y (nu p') ->
      notin y (nu (fun z : name => nu (q' z))) ->
      b_act_notin_ho y a' -> btrans (p' y) (a' y) (q' y)); 
 intros; auto.

(* TAU Case *)

rewrite H10 in H9.
cut (tau_pref (q'0 y) = p'0 y);
 [ intro
 | change ((fun n : name => tau_pref (q'0 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H16.
cut (tau = a'0 y);
 [ intro
 | change ((fun _ : name => tau) y = a'0 y) in |- *;
    apply f_act_sub_congr with x0; auto ].
rewrite <- H17.
apply TAU.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_tau; inversion H7; auto.

(* OUT Case *)

elim (LEM_name x0 x1); elim (LEM_name x1 y); intros.

(* Subcase x0=x1=y *)

rewrite <- H16 in H9; rewrite H17 in H9.
rewrite <- H16 in H11; rewrite H17 in H11.
rewrite H10 in H9.
cut (out_pref y0 y0 (q'0 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => out_pref n n (q'0 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H18.
cut (Out y0 y0 = a'0 y0);
 [ intro
 | change ((fun n : name => Out n n) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H19.
apply OUT.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply notin_nu; intros; apply notin_out; inversion H7; auto.

(* Subcase x0=x1 /\ ~x1=y *)

rewrite H17 in H9.
rewrite H17 in H11.
rewrite H10 in H9.
cut (out_pref y0 y (q'0 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => out_pref n y (q'0 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H18.
cut (Out y0 y = a'0 y0);
 [ intro
 | change ((fun n : name => Out n y) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H19.
apply OUT.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply notin_nu; intros; apply notin_out; inversion H7; auto.

(* Subcase ~x0=x1 /\ x1=y *)

rewrite <- H16 in H9.
rewrite <- H16 in H11.
rewrite H10 in H9.
cut (out_pref x0 y0 (q'0 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => out_pref x0 n (q'0 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H18.
cut (Out x0 y0 = a'0 y0);
 [ intro
 | change ((fun n : name => Out x0 n) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H19.
apply OUT.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply notin_nu; intros; apply notin_out; inversion H7; auto.

(* Subcase ~x0=x1 /\ ~x1=y *)

rewrite H10 in H9.
cut (out_pref x0 y (q'0 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => out_pref x0 y (q'0 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H18.
cut (Out x0 y = a'0 y0);
 [ intro
 | change ((fun _ : name => Out x0 y) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H19.
apply OUT.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply notin_nu; intros; apply notin_out; inversion H7; auto.

(* fSUM1 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H23 in H11; rewrite H22 in H11.
cut (sum (x2 y) (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => sum (x2 n) (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
apply fSUM1.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_sum;
 [ inversion_clear H19; auto | inversion_clear H21; auto ].

(* fSUM2 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H23 in H11; rewrite H22 in H11.
cut (sum (x2 y) (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => sum (x2 n) (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
apply fSUM2.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_sum;
 [ inversion_clear H19; auto | inversion_clear H21; auto ].

(* fPAR1 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); elim (proc_exp p0 x0); intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21.
rewrite H23 in H12; rewrite H24 in H11; rewrite H24 in H12;
 rewrite H25 in H11.
cut (par (x1 y) (x2 y) = q'0 y);
 [ intro
 | change ((fun n : name => par (x1 n) (x2 n)) y = q'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H21.
cut (par (x3 y) (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H26.
apply fPAR1.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply proc_mono with x0.
inversion_clear H16.
cut (notin y (q'0 x0)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto | inversion_clear H19; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H22; auto | inversion_clear H19; auto ].

(* fPAR2 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); elim (proc_exp p0 x0); intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21.
rewrite H23 in H12; rewrite H24 in H11; rewrite H25 in H11;
 rewrite H25 in H12.
cut (par (x3 y) (x1 y) = q'0 y);
 [ intro
 | change ((fun n : name => par (x3 n) (x1 n)) y = q'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H21.
cut (par (x3 y) (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H26.
apply fPAR2.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply proc_mono with x0.
inversion_clear H16.
cut (notin y (q'0 x0)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto | inversion_clear H19; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto | inversion_clear H22; auto ].

(* fMATCH Case *)

elim (LEM_name x0 x1); elim (LEM_name x1 y); intros.

(* Subcase x0=x1=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H20.
rewrite H22 in H11.
rewrite H19 in H11.
cut (match_ y y (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => match_ n n (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H20.
apply fMATCH.
apply H7 with x1; auto.
apply proc_mono with x1.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_match; inversion H21; auto.

(* Subcase ~x0=x1 /\ x1=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H20.
rewrite H22 in H11.
cut (match_ x0 x0 (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => match_ x0 x0 (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H20.
apply fMATCH.
apply H7 with x1; auto.
apply proc_mono with x1.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_match; inversion H21; auto.

(* fMISMATCH Case *)

elim (LEM_name x1 y0); intros.

(* Subcase x1=y0 *)

rewrite <- H19; rewrite <- H12; rewrite <- H13; rewrite <- H14; assumption.

(* Subcase ~x1=y0 *)

elim (LEM_name x0 x1); elim (LEM_name y x1); intros.

(* Subsubcase x0=x1=y *)

absurd (x0 = y); [ assumption | rewrite H20; rewrite H21; trivial ].

(* Subsubcase x0=x1 /\ ~x1=y *)

rewrite H21 in H12.
elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch y0 y (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch n y (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply fMISMATCH.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H12; apply isin_mismatch3.
inversion_clear H16; auto.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* Subsubcase ~x0=x1 /\ x1=y *)

rewrite H20 in H12.
elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch x0 y0 (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch x0 n (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply fMISMATCH.
apply Sep_proc with (p'0 x1).
rewrite <- H12; apply isin_mismatch2.
inversion_clear H16; auto.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* Subsubcase ~x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch x0 y (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch x0 y (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply fMISMATCH.
inversion H15; assumption.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* fBANG Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p0 x0); intros.
inversion_clear H19.
rewrite H21 in H11.
cut (bang (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => bang (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H19; apply fBANG.
change
  (ftrans ((fun n : name => par (x1 n) (bang (x1 n))) y) (a'0 y) (q'0 y))
 in |- *; apply H7 with x0; auto.
apply notin_nu; intros; inversion_clear H20; apply notin_par;
 [ auto | apply notin_bang; auto ].
rewrite H21; trivial.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15; inversion H15; apply notin_par; assumption.
apply notin_nu; intros; apply notin_bang; inversion_clear H20; auto.

(* COM1 Case *)

elim (LEM_name x1 y0); intros.

(* Subcase x1=y0 *)

rewrite <- H20; rewrite <- H13; rewrite <- H14; rewrite <- H15; assumption.

(* Subcase ~x1=y0 *)

elim (proc_exp p1 x1); elim (proc_exp p2 x1); elim (ho_proc_exp q1 x1);
 elim (proc_exp q2 x1); intros.
inversion_clear H21; inversion_clear H22; inversion_clear H23;
 inversion_clear H24.
rewrite H26 in H14; rewrite H27 in H14; rewrite H28 in H13;
 rewrite H29 in H13.
elim (LEM_name x0 x1); elim (LEM_name x1 y); intros.

rewrite <- H24 in H14.
cut (par (x3 y0 y0) (x2 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n n) (x2 n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM1 with y0.
change (btrans (x5 y0) ((fun n : name => In n) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
change (ftrans (x4 y0) ((fun n : name => Out n n) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite <- H24; rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; auto ].

cut (par (x3 y0 y) (x2 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n y) (x2 n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM1 with y0.
change (btrans (x5 y0) ((fun n : name => In n) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with y.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
change (ftrans (x4 y0) ((fun n : name => Out n y) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out2 | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; auto ].

rewrite <- H24 in H14.
cut (par (x3 y0 y0) (x2 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n n) (x2 n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM1 with x0.
change (btrans (x5 y0) ((fun n : name => In x0) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17; cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17; inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
change (ftrans (x4 y0) ((fun n : name => Out x0 n) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; auto ].

cut (par (x3 y0 y) (x2 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n y) (x2 n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM1 with x0.
change (btrans (x5 y0) ((fun n : name => In x0) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17; cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17; inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with y.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
change (ftrans (x4 y0) ((fun n : name => Out x0 y) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out2 | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; auto ].

(* COM2 Case *)

elim (LEM_name x1 y0); intros.

(* Subcase x1=y0 *)

rewrite <- H20; rewrite <- H13; rewrite <- H14; rewrite <- H15; assumption.

(* Subcase ~x1=y0 *)

elim (proc_exp p1 x1); elim (proc_exp p2 x1); elim (proc_exp q1 x1);
 elim (ho_proc_exp q2 x1); intros.
inversion_clear H21; inversion_clear H22; inversion_clear H23;
 inversion_clear H24.
rewrite H26 in H14; rewrite H27 in H14; rewrite H28 in H13;
 rewrite H29 in H13.
elim (LEM_name x0 x1); elim (LEM_name x1 y); intros.

rewrite <- H24 in H14.
cut (par (x3 y0) (x2 y0 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM2 with y0.
change (ftrans (x5 y0) ((fun n : name => Out n n) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite <- H24; rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
change (btrans (x4 y0) ((fun n : name => In n) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

cut (par (x3 y0) (x2 y0 y) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n y)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM2 with y0.

change (ftrans (x5 y0) ((fun n : name => Out n y) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out2 | auto ].
inversion_clear H17; auto.
change (btrans (x4 y0) ((fun n : name => In n) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with y.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

rewrite <- H24 in H14.
cut (par (x3 y0) (x2 y0 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM2 with x0.
change (ftrans (x5 y0) ((fun n : name => Out x0 n) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
change (btrans (x4 y0) ((fun n : name => In x0) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17; cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17; inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

cut (par (x3 y0) (x2 y0 y) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n y)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM2 with x0.
change (ftrans (x5 y0) ((fun n : name => Out x0 y) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out2 | auto ].
inversion_clear H17; auto.
change (btrans (x4 y0) ((fun n : name => In x0) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17; cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17; inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with y.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

(* fRES Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (ho_proc_exp p1 x0); elim (ho_proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H22 in H12; rewrite H23 in H11.
cut (nu (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => nu (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
cut (nu (x1 y) = q'0 y);
 [ intro
 | change ((fun n : name => nu (x1 n)) y = q'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H24.
apply fRES with (cons x0 (cons y l)); intros.
inversion_clear H27.
inversion_clear H30.
change
  (ftrans ((fun n : name => x2 n y0) y) (a'0 y) ((fun n : name => x1 n y0) y))
 in |- *.
apply H7 with y0 x0; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H30; auto.
cut (notin y0 (nu (fun n : name => nu (x1 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H30; auto.
rewrite H13; cut (f_act_notin_ho y0 a'0);
 [ intro | apply f_act_mono with y; assumption ].
unfold f_act_notin_ho in H30; auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H19; auto.
apply notin_nu; intros.
inversion_clear H21.
cut (notin x0 (nu (x1 z))); [ intro | auto ].
inversion_clear H21; auto.
rewrite H23; trivial.
rewrite H22; trivial.
apply H6; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; auto ].
inversion_clear H30.
cut (notin y0 (nu (x2 x0))); [ intro | auto ].
rewrite H23; assumption.
cut (notin y0 (nu (fun n : name => nu (x1 n))));
 [ intro | apply proc_mono with y; auto ].
inversion_clear H30.
cut (notin y0 (nu (x1 x0))); [ intro | auto ].
rewrite H22; assumption.
rewrite H13; cut (f_act_notin_ho y0 a'0);
 [ intro | apply f_act_mono with y; assumption ].
unfold f_act_notin_ho in H30; auto.
cut (notin y (p'0 x0)); [ intro | inversion_clear H15; auto ].
cut (notin y (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with x0; rewrite <- H11 in H30; auto ].
apply notin_nu; intros.
inversion_clear H32.
cut (notin y (nu (x2 z))); [ intro | auto ].
inversion_clear H32; auto.
cut (notin y (q'0 x0)); [ intro | inversion_clear H16; auto ].
cut (notin y (nu (fun n : name => nu (x1 n))));
 [ intro | apply proc_mono with x0; rewrite <- H12 in H30; auto ].
apply notin_nu; intros.
inversion_clear H32.
cut (notin y (nu (x1 z))); [ intro | auto ].
inversion_clear H32; auto.

(* CLOSE1 Case *)

elim (LEM_name x1 y); intros.

(* Subcase x1=y *)

rewrite <- H20; rewrite <- H13; rewrite <- H14; rewrite <- H15; assumption.

(* Subcase ~x1=y *)

elim (proc_exp p1 x1); elim (proc_exp p2 x1); elim (ho_proc_exp q1 x1);
 elim (ho_proc_exp q2 x1); intros.
inversion_clear H21; inversion_clear H22; inversion_clear H23;
 inversion_clear H24.
rewrite H26 in H14; rewrite H27 in H14; rewrite H28 in H13;
 rewrite H29 in H13.
elim (LEM_name x0 x1); intros.
cut (nu (fun z : name => par (x3 y z) (x2 y z)) = q'0 y);
 [ intro
 | change
     ((fun n : name => nu (fun z : name => par (x3 n z) (x2 n z))) y = q'0 y)
    in |- *; apply proc_sub_congr with x1; auto ].
cut (par (x5 y) (x4 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y);
 [ intro
 | change ((fun n : name => tau) y = a'0 y) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H30; rewrite <- H31; rewrite <- H32.
apply CLOSE1 with y.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; apply proc_mono with x1; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

cut (nu (fun z : name => par (x3 y z) (x2 y z)) = q'0 y);
 [ intro
 | change
     ((fun n : name => nu (fun z : name => par (x3 n z) (x2 n z))) y = q'0 y)
    in |- *; apply proc_sub_congr with x1; auto ].
cut (par (x5 y) (x4 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y);
 [ intro
 | change ((fun n : name => tau) y = a'0 y) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H30; rewrite <- H31; rewrite <- H32.
apply CLOSE1 with x0.
change (btrans (x5 y) ((fun n : name => In x0) y) (x3 y)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux2 with (bOut x0) q2; [ apply b_act_isin_bOut | auto ].
inversion_clear H17; auto.
change (btrans (x4 y) ((fun n : name => bOut x0) y) (x2 y)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; apply proc_mono with x1; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
cut (x0 <> y); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux2 with (bOut x0) q2; [ apply b_act_isin_bOut | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

(* CLOSE2 Case *)

elim (LEM_name x1 y); intros.

(* Subcase x1=y *)

rewrite <- H20; rewrite <- H13; rewrite <- H14; rewrite <- H15; assumption.

(* Subcase ~x1=y *)

elim (proc_exp p1 x1); elim (proc_exp p2 x1); elim (ho_proc_exp q1 x1);
 elim (ho_proc_exp q2 x1); intros.
inversion_clear H21; inversion_clear H22; inversion_clear H23;
 inversion_clear H24.
rewrite H26 in H14; rewrite H27 in H14; rewrite H28 in H13;
 rewrite H29 in H13.
elim (LEM_name x0 x1); intros.
cut (nu (fun z : name => par (x3 y z) (x2 y z)) = q'0 y);
 [ intro
 | change
     ((fun n : name => nu (fun z : name => par (x3 n z) (x2 n z))) y = q'0 y)
    in |- *; apply proc_sub_congr with x1; auto ].
cut (par (x5 y) (x4 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y);
 [ intro
 | change ((fun n : name => tau) y = a'0 y) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H30; rewrite <- H31; rewrite <- H32.
apply CLOSE2 with y.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; apply proc_mono with x1; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

cut (nu (fun z : name => par (x3 y z) (x2 y z)) = q'0 y);
 [ intro
 | change
     ((fun n : name => nu (fun z : name => par (x3 n z) (x2 n z))) y = q'0 y)
    in |- *; apply proc_sub_congr with x1; auto ].
cut (par (x5 y) (x4 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y);
 [ intro
 | change ((fun n : name => tau) y = a'0 y) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H30; rewrite <- H31; rewrite <- H32.
apply CLOSE2 with x0.
change (btrans (x5 y) ((fun n : name => bOut x0) y) (x3 y)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
cut (x0 <> y); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux2 with (In x0) q2; [ apply b_act_isin_In | auto ].
inversion_clear H17; auto.
change (btrans (x4 y) ((fun n : name => In x0) y) (x2 y)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; apply proc_mono with x1; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux2 with (In x0) q2; [ apply b_act_isin_In | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

(* IN Case *)

elim (LEM_name x1 y); intros.

(* Subcase x1=y *)

rewrite <- H16; rewrite <- H9; rewrite <- H10; rewrite <- H11; assumption.

(* Subcase ~x1=y *)

elim (ho_proc_exp p0 x1); intros.
inversion_clear H17.
rewrite H19 in H9; rewrite H19 in H10.
elim (LEM_name x0 x1); intros.
rewrite H17 in H9.
rewrite H17 in H11.
cut (in_pref y (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => in_pref n (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (x2 y = q'0 y); [ intro | apply ho_proc_sub_congr with x1; auto ].
cut (In y = a'0 y); [ intro | apply b_act_sub_congr with x1; auto ].
rewrite <- H20; rewrite <- H21; rewrite <- H22; apply IN.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply notin_nu; intros; apply notin_in; intros; auto.
inversion_clear H18.
cut (notin x1 (nu (x2 z))); [ intro | auto ].
inversion_clear H18; auto.

cut (in_pref x0 (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => in_pref x0 (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (x2 y = q'0 y); [ intro | apply ho_proc_sub_congr with x1; auto ].
cut (In x0 = a'0 y);
 [ intro
 | change ((fun n : name => In x0) y = a'0 y) in |- *;
    apply b_act_sub_congr with x1; auto ].
rewrite <- H20; rewrite <- H21; rewrite <- H22; apply IN.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply notin_nu; intros; apply notin_in; intros; auto.
inversion_clear H18.
cut (notin x1 (nu (x2 z))); [ intro | auto ].
inversion_clear H18; auto.

(* bSUM1 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H23 in H11; rewrite H22 in H11.
cut (sum (x2 y) (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => sum (x2 n) (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
apply bSUM1.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_sum;
 [ inversion_clear H19; auto | inversion_clear H21; auto ].

(* bSUM2 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H23 in H11; rewrite H22 in H11.
cut (sum (x2 y) (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => sum (x2 n) (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
apply bSUM2.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_sum;
 [ inversion_clear H19; auto | inversion_clear H21; auto ].

(* bPAR1 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); elim (ho_proc_exp p0 x0);
 intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21.
rewrite H23 in H12; rewrite H24 in H11; rewrite H24 in H12;
 rewrite H25 in H11.
cut ((fun x : name => par (x1 y x) (x2 y)) = q'0 y);
 [ intro
 | change ((fun n x : name => par (x1 n x) (x2 n)) y = q'0 y) in |- *;
    apply ho_proc_sub_congr with x0; auto ].
rewrite <- H21.
cut (par (x3 y) (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H26.
apply bPAR1.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply proc_mono with x0.
inversion_clear H16.
cut (notin y (nu (q'0 x0))); [ intro | auto ].
rewrite <- H12 in H16.
apply proc_mono with x0; inversion_clear H16;
 cut (notin y (par (x1 x0 x0) (x2 x0))); [ intro | auto ];
 inversion_clear H16; auto.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto | inversion_clear H19; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H22; cut (notin x0 (nu (x1 z))); [ intro | auto ];
    inversion_clear H22; auto
 | inversion_clear H19; auto ].

(* bPAR2 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); elim (ho_proc_exp p0 x0);
 intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21.
rewrite H23 in H12; rewrite H24 in H11; rewrite H25 in H11;
 rewrite H25 in H12.
cut ((fun x : name => par (x3 y) (x1 y x)) = q'0 y);
 [ intro
 | change ((fun n x : name => par (x3 n) (x1 n x)) y = q'0 y) in |- *;
    apply ho_proc_sub_congr with x0; auto ].
rewrite <- H21.
cut (par (x3 y) (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H26.
apply bPAR2.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply proc_mono with x0.
inversion_clear H16.
cut (notin y (nu (q'0 x0))); [ intro | auto ].
rewrite <- H12 in H16.
apply proc_mono with x0; inversion_clear H16;
 cut (notin y (par (x3 x0) (x1 x0 x0))); [ intro | auto ];
 inversion_clear H16; auto.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto | inversion_clear H19; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto
 | inversion_clear H22; cut (notin x0 (nu (x1 z))); [ intro | auto ];
    inversion_clear H22; auto ].

(* bMATCH Case *)

elim (LEM_name x0 x1); elim (LEM_name x1 y); intros.

(* Subcase x0=x1=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H20.
rewrite H22 in H11.
rewrite H19 in H11.
cut (match_ y y (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => match_ n n (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H20.
apply bMATCH.
apply H7 with x1; auto.
apply proc_mono with x1.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_match; inversion H21; auto.

(* Subcase ~x0=x1 /\ x1=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H20.
rewrite H22 in H11.
cut (match_ x0 x0 (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => match_ x0 x0 (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H20.
apply bMATCH.
apply H7 with x1; auto.
apply proc_mono with x1.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_match; inversion H21; auto.

(* bMISMATCH Case *)

elim (LEM_name x1 y0); intros.

(* Subcase x1=y0 *)

rewrite <- H19; rewrite <- H12; rewrite <- H13; rewrite <- H14; assumption.

(* Subcase ~x1=y0 *)

elim (LEM_name x0 x1); elim (LEM_name y x1); intros.

(* Subsubcase x0=x1=y *)

absurd (x0 = y); [ assumption | rewrite H20; rewrite H21; trivial ].

(* Subsubcase x0=x1 /\ ~x1=y *)

rewrite H21 in H12.
elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch y0 y (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch n y (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply bMISMATCH.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H12; apply isin_mismatch3.
inversion_clear H16; auto.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* Subsubcase ~x0=x1 /\ x1=y *)

rewrite H20 in H12.
elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch x0 y0 (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch x0 n (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply bMISMATCH.
apply Sep_proc with (p'0 x1).
rewrite <- H12; apply isin_mismatch2.
inversion_clear H16; auto.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* Subsubcase ~x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch x0 y (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch x0 y (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply bMISMATCH.
inversion H15; assumption.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* bBANG Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p0 x0); intros.
inversion_clear H19.
rewrite H21 in H11.
cut (bang (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => bang (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H19; apply bBANG.
change
  (btrans ((fun n : name => par (x1 n) (bang (x1 n))) y) (a'0 y) (q'0 y))
 in |- *; apply H7 with x0; auto.
apply notin_nu; intros; inversion_clear H20; apply notin_par;
 [ auto | apply notin_bang; auto ].
rewrite H21; trivial.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15; inversion H15; apply notin_par; assumption.
apply notin_nu; intros; apply notin_bang; inversion_clear H20; auto.

(* bRES Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (ho_proc_exp p1 x0); elim (ho2_proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H22 in H12; rewrite H23 in H11.
cut (nu (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => nu (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
cut ((fun v : name => nu (fun z : name => x1 y z v)) = q'0 y);
 [ intro
 | change ((fun n v : name => nu (fun z : name => x1 n z v)) y = q'0 y)
    in |- *; apply ho_proc_sub_congr with x0; auto ].
rewrite <- H24.
apply bRES with (cons x0 (cons y l)); intros.
inversion_clear H28.
inversion_clear H30.
change
  (btrans ((fun n : name => x2 n y0) y) (a'0 y) ((fun n : name => x1 n y0) y))
 in |- *.
apply H7 with y0 x0; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H30; auto.
cut (notin y0 (nu (fun y : name => nu (fun z : name => nu (x1 y z)))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H30; auto.
rewrite H13; cut (b_act_notin_ho y0 a'0);
 [ intro | apply b_act_mono with y; assumption ].
unfold f_act_notin_ho in H30; auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H19; auto.
apply notin_nu; intros.
inversion_clear H21.
cut (notin x0 (nu (fun z0 : name => nu (x1 z z0)))); [ intro | auto ].
inversion_clear H21.
cut (notin x0 (nu (x1 z y0))); [ intro | auto ]; assumption.
rewrite H23; trivial.
rewrite H22; trivial.
apply H6; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; auto ].
inversion_clear H30.
cut (notin y0 (nu (x2 x0))); [ intro | auto ].
rewrite H23; assumption.
cut (notin y0 (nu (fun y : name => nu (fun z : name => nu (x1 y z)))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H30; auto.
rewrite H13; cut (b_act_notin_ho y0 a'0);
 [ intro | apply b_act_mono with y; assumption ].
unfold b_act_notin_ho in H30; auto.
cut (notin y (p'0 x0)); [ intro | inversion_clear H15; auto ].
cut (notin y (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with x0; rewrite <- H11 in H30; auto ].
apply notin_nu; intros.
inversion_clear H32.
cut (notin y (nu (x2 z))); [ intro | auto ].
inversion_clear H32; auto.
cut (notin y (nu (q'0 x0))); [ intro | inversion_clear H16; auto ].
rewrite <- H12 in H30; inversion_clear H30.
cut (notin y (nu (fun z0 : name => x1 x0 z0 y0))); [ intro | auto ].
inversion_clear H30.
apply proc_mono with x0; apply proc_mono with y0; auto.
do 3 (apply notin_nu; intros).
inversion_clear H21.
cut (notin x0 (nu (fun z0 : name => nu (x1 z z0)))); [ intro | auto ].
inversion_clear H21.
cut (notin x0 (nu (x1 z z1))); [ intro | auto ].
inversion_clear H21; auto.

(* OPEN Case *)

elim (LEM_name x1 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (ho_proc_exp p1 x1); elim (ho_proc_exp p2 x1); intros.
inversion_clear H19; inversion_clear H20.
rewrite H23 in H11; rewrite H22 in H12.
cut (nu (x3 y) = p'0 y);
 [ intro
 | change ((fun n : name => nu (x3 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H20.
cut (x2 y = q'0 y);
 [ intro
 | change ((fun n : name => x2 n) y = q'0 y) in |- *;
    apply ho_proc_sub_congr with x1; auto ].
rewrite <- H24.
elim (LEM_name x0 x1); intros.
rewrite H25 in H13.
cut (bOut y = a'0 y); [ intro | apply b_act_sub_congr with x1; auto ].
rewrite <- H26.
apply OPEN with (cons x1 (cons y l)); intros.
inversion_clear H30.
inversion_clear H32.
change
  (ftrans ((fun n : name => x3 n y0) y) ((fun n : name => Out n y0) y)
     ((fun n : name => x2 n y0) y)) in |- *; apply H7 with y0 x1; 
 auto.
cut (notin y0 (nu (fun n : name => nu (x3 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H32; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H32; auto.
rewrite H25; auto.
apply notin_nu; intros; inversion_clear H19.
cut (notin x1 (nu (x3 z))); [ intro | auto ].
inversion_clear H19; auto.
apply notin_nu; intros; inversion_clear H21.
cut (notin x1 (nu (x2 z))); [ intro | auto ].
inversion_clear H21; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H23; trivial.
rewrite H22; trivial.
rewrite H25; trivial.
apply H6; auto.
cut (notin y0 (nu (fun n : name => nu (x3 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H32; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H32; auto.
rewrite H25; auto.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
apply proc_mono with x1; inversion_clear H15; auto.
inversion_clear H16.
cut (notin y (nu (q'0 x1))); [ intro | auto ].
rewrite <- H12 in H16.
apply proc_mono with x1; inversion_clear H16; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.

cut (bOut x0 = a'0 y);
 [ intro
 | change ((fun n : name => bOut x0) y = a'0 y) in |- *;
    apply b_act_sub_congr with x1; auto ].
rewrite <- H26.
apply OPEN with (cons x1 (cons y l)); intros.
inversion_clear H30.
inversion_clear H32.
change
  (ftrans ((fun n : name => x3 n y0) y) ((fun n : name => Out x0 y0) y)
     ((fun n : name => x2 n y0) y)) in |- *; apply H7 with y0 x1; 
 auto.
cut (notin y0 (nu (fun n : name => nu (x3 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H32; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H32; auto.
apply notin_nu; intros; inversion_clear H19.
cut (notin x1 (nu (x3 z))); [ intro | auto ].
inversion_clear H19; auto.
apply notin_nu; intros; inversion_clear H21.
cut (notin x1 (nu (x2 z))); [ intro | auto ].
inversion_clear H21; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H23; trivial.
rewrite H22; trivial.
apply H6; auto.
cut (notin y0 (nu (fun n : name => nu (x3 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H32; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H32; auto.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
apply proc_mono with x1; inversion_clear H15; auto.
inversion_clear H16.
cut (notin y (nu (q'0 x1))); [ intro | auto ].
rewrite <- H12 in H16.
apply proc_mono with x1; inversion_clear H16; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (x0 <> y); [ intro; auto | apply Sep_proc with (nu p1) ].
apply Aux2 with (bOut x0) p2; [ apply b_act_isin_bOut | auto ].
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15; rewrite <- H23 in H15; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.

Qed.

Lemma L3bis :
 forall (p : proc) (a : b_act) (q p' : name -> proc) 
   (a' : name -> b_act) (q' : name -> name -> proc) 
   (x : name),
 notin x (nu p') ->
 notin x (nu (fun n : name => nu (q' n))) ->
 b_act_notin_ho x a' ->
 p = p' x ->
 q = q' x ->
 a = a' x ->
 btrans p a q ->
 forall y : name,
 notin y (nu p') ->
 notin y (nu (fun n : name => nu (q' n))) ->
 b_act_notin_ho y a' -> btrans (p' y) (a' y) (q' y).

Proof.

do 14 intro.
generalize H5.
generalize H4.
generalize H3.
generalize H2.
generalize H1.
generalize H0.
generalize H.
generalize x.
generalize a'.
generalize q'.
generalize p'.
pattern p, a, q in |- *;
 apply
  btrans_ftrans_ind
   with
     (fun (p : proc) (a : f_act) (q : proc) =>
      forall (p' q' : name -> proc) (a' : name -> f_act) (x : name),
      notin x (nu p') ->
      notin x (nu q') ->
      f_act_notin_ho x a' ->
      p = p' x ->
      q = q' x ->
      a = a' x ->
      ftrans p a q ->
      forall y : name,
      notin y (nu p') ->
      notin y (nu q') -> f_act_notin_ho y a' -> ftrans (p' y) (a' y) (q' y));
 intros; auto.

(* TAU Case *)

rewrite H10 in H9.
cut (tau_pref (q'0 y) = p'0 y);
 [ intro
 | change ((fun n : name => tau_pref (q'0 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H16.
cut (tau = a'0 y);
 [ intro
 | change ((fun n : name => tau) y = a'0 y) in |- *;
    apply f_act_sub_congr with x0; auto ].
rewrite <- H17.
apply TAU.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_tau; inversion H7; auto.

(* OUT Case *)

elim (LEM_name x0 x1); elim (LEM_name x1 y); intros.

(* Subcase x0=x1=y *)

rewrite <- H16 in H9; rewrite H17 in H9.
rewrite <- H16 in H11; rewrite H17 in H11.
rewrite H10 in H9.
cut (out_pref y0 y0 (q'0 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => out_pref n n (q'0 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H18.
cut (Out y0 y0 = a'0 y0);
 [ intro
 | change ((fun n : name => Out n n) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H19.
apply OUT.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply notin_nu; intros; apply notin_out; inversion H7; auto.

(* Subcase x0=x1 /\ ~x1=y *)

rewrite H17 in H9.
rewrite H17 in H11.
rewrite H10 in H9.
cut (out_pref y0 y (q'0 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => out_pref n y (q'0 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H18.
cut (Out y0 y = a'0 y0);
 [ intro
 | change ((fun n : name => Out n y) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H19.
apply OUT.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply notin_nu; intros; apply notin_out; inversion H7; auto.

(* Subcase ~x0=x1 /\ x1=y *)

rewrite <- H16 in H9.
rewrite <- H16 in H11.
rewrite H10 in H9.
cut (out_pref x0 y0 (q'0 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => out_pref x0 n (q'0 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H18.
cut (Out x0 y0 = a'0 y0);
 [ intro
 | change ((fun n : name => Out x0 n) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H19.
apply OUT.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply notin_nu; intros; apply notin_out; inversion H7; auto.

(* Subcase ~x0=x1 /\ ~x1=y *)

rewrite H10 in H9.
cut (out_pref x0 y (q'0 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => out_pref x0 y (q'0 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H18.
cut (Out x0 y = a'0 y0);
 [ intro
 | change ((fun n : name => Out x0 y) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H19.
apply OUT.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply notin_nu; intros; apply notin_out; inversion H7; auto.

(* fSUM1 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H23 in H11; rewrite H22 in H11.
cut (sum (x2 y) (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => sum (x2 n) (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
apply fSUM1.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_sum;
 [ inversion_clear H19; auto | inversion_clear H21; auto ].

(* fSUM2 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H23 in H11; rewrite H22 in H11.
cut (sum (x2 y) (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => sum (x2 n) (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
apply fSUM2.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_sum;
 [ inversion_clear H19; auto | inversion_clear H21; auto ].

(* fPAR1 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); elim (proc_exp p0 x0); intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21.
rewrite H23 in H12; rewrite H24 in H11; rewrite H24 in H12;
 rewrite H25 in H11.
cut (par (x1 y) (x2 y) = q'0 y);
 [ intro
 | change ((fun n : name => par (x1 n) (x2 n)) y = q'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H21.
cut (par (x3 y) (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H26.
apply fPAR1.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply proc_mono with x0.
inversion_clear H16.
cut (notin y (q'0 x0)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto | inversion_clear H19; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H22; auto | inversion_clear H19; auto ].

(* fPAR2 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); elim (proc_exp p0 x0); intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21.
rewrite H23 in H12; rewrite H24 in H11; rewrite H25 in H11;
 rewrite H25 in H12.
cut (par (x3 y) (x1 y) = q'0 y);
 [ intro
 | change ((fun n : name => par (x3 n) (x1 n)) y = q'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H21.
cut (par (x3 y) (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H26.
apply fPAR2.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply proc_mono with x0.
inversion_clear H16.
cut (notin y (q'0 x0)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto | inversion_clear H19; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto | inversion_clear H22; auto ].

(* fMATCH Case *)

elim (LEM_name x0 x1); elim (LEM_name x1 y); intros.

(* Subcase x0=x1=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H20.
rewrite H22 in H11.
rewrite H19 in H11.
cut (match_ y y (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => match_ n n (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H20.
apply fMATCH.
apply H7 with x1; auto.
apply proc_mono with x1.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_match; inversion H21; auto.

(* Subcase ~x0=x1 /\ x1=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H20.
rewrite H22 in H11.
cut (match_ x0 x0 (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => match_ x0 x0 (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H20.
apply fMATCH.
apply H7 with x1; auto.
apply proc_mono with x1.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_match; inversion H21; auto.

(* fMISMATCH Case *)

elim (LEM_name x1 y0); intros.

(* Subcase x1=y0 *)

rewrite <- H19; rewrite <- H12; rewrite <- H13; rewrite <- H14; assumption.

(* Subcase ~x1=y0 *)

elim (LEM_name x0 x1); elim (LEM_name y x1); intros.

(* Subsubcase x0=x1=y *)

absurd (x0 = y); [ assumption | rewrite H20; rewrite H21; trivial ].

(* Subsubcase x0=x1 /\ ~x1=y *)

rewrite H21 in H12.
elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch y0 y (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch n y (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply fMISMATCH.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H12; apply isin_mismatch3.
inversion_clear H16; auto.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* Subsubcase ~x0=x1 /\ x1=y *)

rewrite H20 in H12.
elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch x0 y0 (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch x0 n (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply fMISMATCH.
apply Sep_proc with (p'0 x1).
rewrite <- H12; apply isin_mismatch2.
inversion_clear H16; auto.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* Subsubcase ~x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch x0 y (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch x0 y (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply fMISMATCH.
inversion H15; assumption.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* fBANG Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p0 x0); intros.
inversion_clear H19.
rewrite H21 in H11.
cut (bang (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => bang (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H19; apply fBANG.
change
  (ftrans ((fun n : name => par (x1 n) (bang (x1 n))) y) (a'0 y) (q'0 y))
 in |- *; apply H7 with x0; auto.
apply notin_nu; intros; inversion_clear H20; apply notin_par;
 [ auto | apply notin_bang; auto ].
rewrite H21; trivial.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15; inversion H15; apply notin_par; assumption.
apply notin_nu; intros; apply notin_bang; inversion_clear H20; auto.

(* COM1 Case *)

elim (LEM_name x1 y0); intros.

(* Subcase x1=y0 *)

rewrite <- H20; rewrite <- H13; rewrite <- H14; rewrite <- H15; assumption.

(* Subcase ~x1=y0 *)

elim (proc_exp p1 x1); elim (proc_exp p2 x1); elim (ho_proc_exp q1 x1);
 elim (proc_exp q2 x1); intros.
inversion_clear H21; inversion_clear H22; inversion_clear H23;
 inversion_clear H24.
rewrite H26 in H14; rewrite H27 in H14; rewrite H28 in H13;
 rewrite H29 in H13.
elim (LEM_name x0 x1); elim (LEM_name x1 y); intros.

rewrite <- H24 in H14.
cut (par (x3 y0 y0) (x2 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n n) (x2 n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM1 with y0.
change (btrans (x5 y0) ((fun n : name => In n) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
change (ftrans (x4 y0) ((fun n : name => Out n n) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite <- H24; rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; auto ].

cut (par (x3 y0 y) (x2 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n y) (x2 n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM1 with y0.
change (btrans (x5 y0) ((fun n : name => In n) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with y.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
change (ftrans (x4 y0) ((fun n : name => Out n y) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out2 | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; auto ].

rewrite <- H24 in H14.
cut (par (x3 y0 y0) (x2 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n n) (x2 n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM1 with x0.
change (btrans (x5 y0) ((fun n : name => In x0) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17; cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17; inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
change (ftrans (x4 y0) ((fun n : name => Out x0 n) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; auto ].

cut (par (x3 y0 y) (x2 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n y) (x2 n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM1 with x0.
change (btrans (x5 y0) ((fun n : name => In x0) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17; cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17; inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with y.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
change (ftrans (x4 y0) ((fun n : name => Out x0 y) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux1 with q2 (Out x0 y); [ apply f_act_isin_Out2 | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; auto ].

(* COM2 Case *)

elim (LEM_name x1 y0); intros.

(* Subcase x1=y0 *)

rewrite <- H20; rewrite <- H13; rewrite <- H14; rewrite <- H15; assumption.

(* Subcase ~x1=y0 *)

elim (proc_exp p1 x1); elim (proc_exp p2 x1); elim (proc_exp q1 x1);
 elim (ho_proc_exp q2 x1); intros.
inversion_clear H21; inversion_clear H22; inversion_clear H23;
 inversion_clear H24.
rewrite H26 in H14; rewrite H27 in H14; rewrite H28 in H13;
 rewrite H29 in H13.
elim (LEM_name x0 x1); elim (LEM_name x1 y); intros.

rewrite <- H24 in H14.
cut (par (x3 y0) (x2 y0 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM2 with y0.
change (ftrans (x5 y0) ((fun n : name => Out n n) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite <- H24; rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
change (btrans (x4 y0) ((fun n : name => In n) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

cut (par (x3 y0) (x2 y0 y) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n y)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM2 with y0.

change (ftrans (x5 y0) ((fun n : name => Out n y) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out2 | auto ].
inversion_clear H17; auto.
change (btrans (x4 y0) ((fun n : name => In n) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H30; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with y.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

rewrite <- H24 in H14.
cut (par (x3 y0) (x2 y0 y0) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n n)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM2 with x0.
change (ftrans (x5 y0) ((fun n : name => Out x0 n) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
change (btrans (x4 y0) ((fun n : name => In x0) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17; cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17; inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

cut (par (x3 y0) (x2 y0 y) = q'0 y0);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n y)) y0 = q'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (par (x5 y0) (x4 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y0);
 [ intro
 | change ((fun n : name => tau) y0 = a'0 y0) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H31; rewrite <- H32; rewrite <- H33.
apply COM2 with x0.
change (ftrans (x5 y0) ((fun n : name => Out x0 y) y0) (x3 y0)) in |- *.
apply H7 with x1; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18; assumption.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out2 | auto ].
inversion_clear H17; auto.
change (btrans (x4 y0) ((fun n : name => In x0) y0) (x2 y0)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17; cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17; inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y0 (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with y.
inversion_clear H18; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par1.
rewrite <- H29.
apply Aux1 with q1 (Out x0 y); [ apply f_act_isin_Out1 | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

(* fRES Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (ho_proc_exp p1 x0); elim (ho_proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H22 in H12; rewrite H23 in H11.
cut (nu (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => nu (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
cut (nu (x1 y) = q'0 y);
 [ intro
 | change ((fun n : name => nu (x1 n)) y = q'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H24.
apply fRES with (cons x0 (cons y l)); intros.
inversion_clear H27.
inversion_clear H30.
change
  (ftrans ((fun n : name => x2 n y0) y) (a'0 y) ((fun n : name => x1 n y0) y))
 in |- *.
apply H7 with y0 x0; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H30; auto.
cut (notin y0 (nu (fun n : name => nu (x1 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H30; auto.
rewrite H13; cut (f_act_notin_ho y0 a'0);
 [ intro | apply f_act_mono with y; assumption ].
unfold f_act_notin_ho in H30; auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H19; auto.
apply notin_nu; intros.
inversion_clear H21.
cut (notin x0 (nu (x1 z))); [ intro | auto ].
inversion_clear H21; auto.
rewrite H23; trivial.
rewrite H22; trivial.
apply H6; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; auto ].
inversion_clear H30.
cut (notin y0 (nu (x2 x0))); [ intro | auto ].
rewrite H23; assumption.
cut (notin y0 (nu (fun n : name => nu (x1 n))));
 [ intro | apply proc_mono with y; auto ].
inversion_clear H30.
cut (notin y0 (nu (x1 x0))); [ intro | auto ].
rewrite H22; assumption.
rewrite H13; cut (f_act_notin_ho y0 a'0);
 [ intro | apply f_act_mono with y; assumption ].
unfold f_act_notin_ho in H30; auto.
cut (notin y (p'0 x0)); [ intro | inversion_clear H15; auto ].
cut (notin y (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with x0; rewrite <- H11 in H30; auto ].
apply notin_nu; intros.
inversion_clear H32.
cut (notin y (nu (x2 z))); [ intro | auto ].
inversion_clear H32; auto.
cut (notin y (q'0 x0)); [ intro | inversion_clear H16; auto ].
cut (notin y (nu (fun n : name => nu (x1 n))));
 [ intro | apply proc_mono with x0; rewrite <- H12 in H30; auto ].
apply notin_nu; intros.
inversion_clear H32.
cut (notin y (nu (x1 z))); [ intro | auto ].
inversion_clear H32; auto.

(* CLOSE1 Case *)

elim (LEM_name x1 y); intros.

(* Subcase x1=y *)

rewrite <- H20; rewrite <- H13; rewrite <- H14; rewrite <- H15; assumption.

(* Subcase ~x1=y *)

elim (proc_exp p1 x1); elim (proc_exp p2 x1); elim (ho_proc_exp q1 x1);
 elim (ho_proc_exp q2 x1); intros.
inversion_clear H21; inversion_clear H22; inversion_clear H23;
 inversion_clear H24.
rewrite H26 in H14; rewrite H27 in H14; rewrite H28 in H13;
 rewrite H29 in H13.
elim (LEM_name x0 x1); intros.
cut (nu (fun z : name => par (x3 y z) (x2 y z)) = q'0 y);
 [ intro
 | change
     ((fun n : name => nu (fun z : name => par (x3 n z) (x2 n z))) y = q'0 y)
    in |- *; apply proc_sub_congr with x1; auto ].
cut (par (x5 y) (x4 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y);
 [ intro
 | change ((fun n : name => tau) y = a'0 y) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H30; rewrite <- H31; rewrite <- H32.
apply CLOSE1 with y.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; apply proc_mono with x1; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

cut (nu (fun z : name => par (x3 y z) (x2 y z)) = q'0 y);
 [ intro
 | change
     ((fun n : name => nu (fun z : name => par (x3 n z) (x2 n z))) y = q'0 y)
    in |- *; apply proc_sub_congr with x1; auto ].
cut (par (x5 y) (x4 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y);
 [ intro
 | change ((fun n : name => tau) y = a'0 y) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H30; rewrite <- H31; rewrite <- H32.
apply CLOSE1 with x0.
change (btrans (x5 y) ((fun n : name => In x0) y) (x3 y)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux2 with (bOut x0) q2; [ apply b_act_isin_bOut | auto ].
inversion_clear H17; auto.
change (btrans (x4 y) ((fun n : name => bOut x0) y) (x2 y)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; apply proc_mono with x1; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
cut (x0 <> y); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux2 with (bOut x0) q2; [ apply b_act_isin_bOut | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

(* CLOSE2 Case *)

elim (LEM_name x1 y); intros.

(* Subcase x1=y *)

rewrite <- H20; rewrite <- H13; rewrite <- H14; rewrite <- H15; assumption.

(* Subcase ~x1=y *)

elim (proc_exp p1 x1); elim (proc_exp p2 x1); elim (ho_proc_exp q1 x1);
 elim (ho_proc_exp q2 x1); intros.
inversion_clear H21; inversion_clear H22; inversion_clear H23;
 inversion_clear H24.
rewrite H26 in H14; rewrite H27 in H14; rewrite H28 in H13;
 rewrite H29 in H13.
elim (LEM_name x0 x1); intros.
cut (nu (fun z : name => par (x3 y z) (x2 y z)) = q'0 y);
 [ intro
 | change
     ((fun n : name => nu (fun z : name => par (x3 n z) (x2 n z))) y = q'0 y)
    in |- *; apply proc_sub_congr with x1; auto ].
cut (par (x5 y) (x4 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y);
 [ intro
 | change ((fun n : name => tau) y = a'0 y) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H30; rewrite <- H31; rewrite <- H32.
apply CLOSE2 with y.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; apply proc_mono with x1; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
rewrite H24; trivial.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

cut (nu (fun z : name => par (x3 y z) (x2 y z)) = q'0 y);
 [ intro
 | change
     ((fun n : name => nu (fun z : name => par (x3 n z) (x2 n z))) y = q'0 y)
    in |- *; apply proc_sub_congr with x1; auto ].
cut (par (x5 y) (x4 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x5 n) (x4 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (tau = a'0 y);
 [ intro
 | change ((fun n : name => tau) y = a'0 y) in |- *;
    apply f_act_sub_congr with x1; auto ].
rewrite <- H30; rewrite <- H31; rewrite <- H32.
apply CLOSE2 with x0.
change (btrans (x5 y) ((fun n : name => bOut x0) y) (x3 y)) in |- *.
apply H7 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.
cut (x0 <> y); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux2 with (In x0) q2; [ apply b_act_isin_In | auto ].
inversion_clear H17; auto.
change (btrans (x4 y) ((fun n : name => In x0) y) (x2 y)) in |- *.
apply H9 with x1; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply proc_mono with x1.
inversion_clear H17.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H13 in H17.
inversion_clear H17; assumption.
apply proc_mono with x1.
inversion_clear H18.
cut (notin y (q'0 x1)); [ intro | auto ].
rewrite <- H14 in H18.
inversion_clear H18.
cut (notin y (par (x3 x1 x1) (x2 x1 x1))); [ intro | auto ].
inversion_clear H18; apply proc_mono with x1; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
cut (x0 <> y); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H13.
apply isin_par2.
rewrite <- H28.
apply Aux2 with (In x0) q2; [ apply b_act_isin_In | auto ].
inversion_clear H17; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_tau.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H23; auto | inversion_clear H22; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H21; cut (notin x1 (nu (x3 z))); [ intro | auto ];
    inversion_clear H21; auto
 | inversion_clear H25; cut (notin x1 (nu (x2 z))); [ intro | auto ];
    inversion_clear H25; auto ].

(* IN Case *)

elim (LEM_name x1 y); intros.

(* Subcase x1=y *)

rewrite <- H16; rewrite <- H9; rewrite <- H10; rewrite <- H11; assumption.

(* Subcase ~x1=y *)

elim (ho_proc_exp p0 x1); intros.
inversion_clear H17.
rewrite H19 in H9; rewrite H19 in H10.
elim (LEM_name x0 x1); intros.
rewrite H17 in H9.
rewrite H17 in H11.
cut (in_pref y (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => in_pref n (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (x2 y = q'0 y); [ intro | apply ho_proc_sub_congr with x1; auto ].
cut (In y = a'0 y); [ intro | apply b_act_sub_congr with x1; auto ].
rewrite <- H20; rewrite <- H21; rewrite <- H22; apply IN.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply notin_nu; intros; apply notin_in; intros; auto.
inversion_clear H18.
cut (notin x1 (nu (x2 z))); [ intro | auto ].
inversion_clear H18; auto.

cut (in_pref x0 (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => in_pref x0 (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
cut (x2 y = q'0 y); [ intro | apply ho_proc_sub_congr with x1; auto ].
cut (In x0 = a'0 y);
 [ intro
 | change ((fun n : name => In x0) y = a'0 y) in |- *;
    apply b_act_sub_congr with x1; auto ].
rewrite <- H20; rewrite <- H21; rewrite <- H22; apply IN.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; auto.
apply notin_nu; intros; apply notin_in; intros; auto.
inversion_clear H18.
cut (notin x1 (nu (x2 z))); [ intro | auto ].
inversion_clear H18; auto.

(* bSUM1 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H23 in H11; rewrite H22 in H11.
cut (sum (x2 y) (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => sum (x2 n) (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
apply bSUM1.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_sum;
 [ inversion_clear H19; auto | inversion_clear H21; auto ].

(* bSUM2 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H23 in H11; rewrite H22 in H11.
cut (sum (x2 y) (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => sum (x2 n) (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
apply bSUM2.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_sum;
 [ inversion_clear H19; auto | inversion_clear H21; auto ].

(* bPAR1 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); elim (ho_proc_exp p0 x0);
 intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21.
rewrite H23 in H12; rewrite H24 in H11; rewrite H24 in H12;
 rewrite H25 in H11.
cut ((fun x : name => par (x1 y x) (x2 y)) = q'0 y);
 [ intro
 | change ((fun n x : name => par (x1 n x) (x2 n)) y = q'0 y) in |- *;
    apply ho_proc_sub_congr with x0; auto ].
rewrite <- H21.
cut (par (x3 y) (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H26.
apply bPAR1.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply proc_mono with x0.
inversion_clear H16.
cut (notin y (nu (q'0 x0))); [ intro | auto ].
rewrite <- H12 in H16.
apply proc_mono with x0; inversion_clear H16;
 cut (notin y (par (x1 x0 x0) (x2 x0))); [ intro | auto ];
 inversion_clear H16; auto.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto | inversion_clear H19; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H22; cut (notin x0 (nu (x1 z))); [ intro | auto ];
    inversion_clear H22; auto
 | inversion_clear H19; auto ].

(* bPAR2 Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p1 x0); elim (proc_exp p2 x0); elim (ho_proc_exp p0 x0);
 intros.
inversion_clear H19; inversion_clear H20; inversion_clear H21.
rewrite H23 in H12; rewrite H24 in H11; rewrite H25 in H11;
 rewrite H25 in H12.
cut ((fun x : name => par (x3 y) (x1 y x)) = q'0 y);
 [ intro
 | change ((fun n x : name => par (x3 n) (x1 n x)) y = q'0 y) in |- *;
    apply ho_proc_sub_congr with x0; auto ].
rewrite <- H21.
cut (par (x3 y) (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => par (x3 n) (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H26.
apply bPAR2.
apply H7 with x0; auto.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply proc_mono with x0.
inversion_clear H16.
cut (notin y (nu (q'0 x0))); [ intro | auto ].
rewrite <- H12 in H16.
apply proc_mono with x0; inversion_clear H16;
 cut (notin y (par (x3 x0) (x1 x0 x0))); [ intro | auto ];
 inversion_clear H16; auto.
apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto | inversion_clear H19; auto ].
apply notin_nu; intros; apply notin_nu; intros; apply notin_par;
 [ inversion_clear H20; auto
 | inversion_clear H22; cut (notin x0 (nu (x1 z))); [ intro | auto ];
    inversion_clear H22; auto ].

(* bMATCH Case *)

elim (LEM_name x0 x1); elim (LEM_name x1 y); intros.

(* Subcase x0=x1=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H20.
rewrite H22 in H11.
rewrite H19 in H11.
cut (match_ y y (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => match_ n n (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H20.
apply bMATCH.
apply H7 with x1; auto.
apply proc_mono with x1.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_match; inversion H21; auto.

(* Subcase ~x0=x1 /\ x1=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H20.
rewrite H22 in H11.
cut (match_ x0 x0 (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => match_ x0 x0 (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H20.
apply bMATCH.
apply H7 with x1; auto.
apply proc_mono with x1.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
inversion_clear H15; assumption.
apply notin_nu; intros; apply notin_match; inversion H21; auto.

(* bMISMATCH Case *)

elim (LEM_name x1 y0); intros.

(* Subcase x1=y0 *)

rewrite <- H19; rewrite <- H12; rewrite <- H13; rewrite <- H14; assumption.

(* Subcase ~x1=y0 *)

elim (LEM_name x0 x1); elim (LEM_name y x1); intros.

(* Subsubcase x0=x1=y *)

absurd (x0 = y); [ assumption | rewrite H20; rewrite H21; trivial ].

(* Subsubcase x0=x1 /\ ~x1=y *)

rewrite H21 in H12.
elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch y0 y (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch n y (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply bMISMATCH.
cut (y <> y0); [ intro; auto | apply Sep_proc with (p'0 x1) ].
rewrite <- H12; apply isin_mismatch3.
inversion_clear H16; auto.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* Subsubcase ~x0=x1 /\ x1=y *)

rewrite H20 in H12.
elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch x0 y0 (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch x0 n (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply bMISMATCH.
apply Sep_proc with (p'0 x1).
rewrite <- H12; apply isin_mismatch2.
inversion_clear H16; auto.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* Subsubcase ~x0=x1 /\ ~x1=y *)

elim (proc_exp p0 x1); intros.
inversion_clear H22.
rewrite H24 in H12.
cut (mismatch x0 y (x2 y0) = p'0 y0);
 [ intro
 | change ((fun n : name => mismatch x0 y (x2 n)) y0 = p'0 y0) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H22.
apply bMISMATCH.
inversion H15; assumption.
apply H8 with x1; auto.
apply proc_mono with x1.
inversion_clear H16.
cut (notin y0 (p'0 x1)); [ intro | auto ].
rewrite <- H12 in H16.
inversion_clear H16; assumption.
apply notin_nu; intros; apply notin_mismatch; inversion H23; auto.

(* bBANG Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (proc_exp p0 x0); intros.
inversion_clear H19.
rewrite H21 in H11.
cut (bang (x1 y) = p'0 y);
 [ intro
 | change ((fun n : name => bang (x1 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H19; apply bBANG.
change
  (btrans ((fun n : name => par (x1 n) (bang (x1 n))) y) (a'0 y) (q'0 y))
 in |- *; apply H7 with x0; auto.
apply notin_nu; intros; inversion_clear H20; apply notin_par;
 [ auto | apply notin_bang; auto ].
rewrite H21; trivial.
apply proc_mono with x0.
inversion_clear H15.
cut (notin y (p'0 x0)); [ intro | auto ].
rewrite <- H11 in H15; inversion H15; apply notin_par; assumption.
apply notin_nu; intros; apply notin_bang; inversion_clear H20; auto.

(* bRES Case *)

elim (LEM_name x0 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (ho_proc_exp p1 x0); elim (ho2_proc_exp p2 x0); intros.
inversion_clear H19; inversion_clear H20.
rewrite H22 in H12; rewrite H23 in H11.
cut (nu (x2 y) = p'0 y);
 [ intro
 | change ((fun n : name => nu (x2 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x0; auto ].
rewrite <- H20.
cut ((fun v : name => nu (fun z : name => x1 y z v)) = q'0 y);
 [ intro
 | change ((fun n v : name => nu (fun z : name => x1 n z v)) y = q'0 y)
    in |- *; apply ho_proc_sub_congr with x0; auto ].
rewrite <- H24.
apply bRES with (cons x0 (cons y l)); intros.
inversion_clear H28.
inversion_clear H30.
change
  (btrans ((fun n : name => x2 n y0) y) (a'0 y) ((fun n : name => x1 n y0) y))
 in |- *.
apply H7 with y0 x0; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H30; auto.
cut (notin y0 (nu (fun y : name => nu (fun z : name => nu (x1 y z)))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H30; auto.
rewrite H13; cut (b_act_notin_ho y0 a'0);
 [ intro | apply b_act_mono with y; assumption ].
unfold f_act_notin_ho in H30; auto.
apply notin_nu; intros.
inversion_clear H19.
cut (notin x0 (nu (x2 z))); [ intro | auto ].
inversion_clear H19; auto.
apply notin_nu; intros.
inversion_clear H21.
cut (notin x0 (nu (fun z0 : name => nu (x1 z z0)))); [ intro | auto ].
inversion_clear H21.
cut (notin x0 (nu (x1 z y0))); [ intro | auto ]; assumption.
rewrite H23; trivial.
rewrite H22; trivial.
apply H6; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; auto ].
inversion_clear H30.
cut (notin y0 (nu (x2 x0))); [ intro | auto ].
rewrite H23; assumption.
cut (notin y0 (nu (fun y : name => nu (fun z : name => nu (x1 y z)))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H30; auto.
rewrite H13; cut (b_act_notin_ho y0 a'0);
 [ intro | apply b_act_mono with y; assumption ].
unfold b_act_notin_ho in H30; auto.
cut (notin y (p'0 x0)); [ intro | inversion_clear H15; auto ].
cut (notin y (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with x0; rewrite <- H11 in H30; auto ].
apply notin_nu; intros.
inversion_clear H32.
cut (notin y (nu (x2 z))); [ intro | auto ].
inversion_clear H32; auto.
cut (notin y (nu (q'0 x0))); [ intro | inversion_clear H16; auto ].
rewrite <- H12 in H30; inversion_clear H30.
cut (notin y (nu (fun z0 : name => x1 x0 z0 y0))); [ intro | auto ].
inversion_clear H30.
apply proc_mono with x0; apply proc_mono with y0; auto.
do 3 (apply notin_nu; intros).
inversion_clear H21.
cut (notin x0 (nu (fun z0 : name => nu (x1 z z0)))); [ intro | auto ].
inversion_clear H21.
cut (notin x0 (nu (x1 z z1))); [ intro | auto ].
inversion_clear H21; auto.

(* OPEN Case *)

elim (LEM_name x1 y); intros.

(* Subcase x0=y *)

rewrite <- H18; rewrite <- H11; rewrite <- H12; rewrite <- H13; assumption.

(* Subcase ~x0=y *)

elim (ho_proc_exp p1 x1); elim (ho_proc_exp p2 x1); intros.
inversion_clear H19; inversion_clear H20.
rewrite H23 in H11; rewrite H22 in H12.
cut (nu (x3 y) = p'0 y);
 [ intro
 | change ((fun n : name => nu (x3 n)) y = p'0 y) in |- *;
    apply proc_sub_congr with x1; auto ].
rewrite <- H20.
cut (x2 y = q'0 y);
 [ intro
 | change ((fun n : name => x2 n) y = q'0 y) in |- *;
    apply ho_proc_sub_congr with x1; auto ].
rewrite <- H24.
elim (LEM_name x0 x1); intros.
rewrite H25 in H13.
cut (bOut y = a'0 y); [ intro | apply b_act_sub_congr with x1; auto ].
rewrite <- H26.
apply OPEN with (cons x1 (cons y l)); intros.
inversion_clear H30.
inversion_clear H32.
change
  (ftrans ((fun n : name => x3 n y0) y) ((fun n : name => Out n y0) y)
     ((fun n : name => x2 n y0) y)) in |- *; apply H7 with y0 x1; 
 auto.
cut (notin y0 (nu (fun n : name => nu (x3 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H32; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H32; auto.
rewrite H25; auto.
apply notin_nu; intros; inversion_clear H19.
cut (notin x1 (nu (x3 z))); [ intro | auto ].
inversion_clear H19; auto.
apply notin_nu; intros; inversion_clear H21.
cut (notin x1 (nu (x2 z))); [ intro | auto ].
inversion_clear H21; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H23; trivial.
rewrite H22; trivial.
rewrite H25; trivial.
apply H6; auto.
cut (notin y0 (nu (fun n : name => nu (x3 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H32; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H32; auto.
rewrite H25; auto.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
apply proc_mono with x1; inversion_clear H15; auto.
inversion_clear H16.
cut (notin y (nu (q'0 x1))); [ intro | auto ].
rewrite <- H12 in H16.
apply proc_mono with x1; inversion_clear H16; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.

cut (bOut x0 = a'0 y);
 [ intro
 | change ((fun n : name => bOut x0) y = a'0 y) in |- *;
    apply b_act_sub_congr with x1; auto ].
rewrite <- H26.
apply OPEN with (cons x1 (cons y l)); intros.
inversion_clear H30.
inversion_clear H32.
change
  (ftrans ((fun n : name => x3 n y0) y) ((fun n : name => Out x0 y0) y)
     ((fun n : name => x2 n y0) y)) in |- *; apply H7 with y0 x1; 
 auto.
cut (notin y0 (nu (fun n : name => nu (x3 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H32; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H32; auto.
apply notin_nu; intros; inversion_clear H19.
cut (notin x1 (nu (x3 z))); [ intro | auto ].
inversion_clear H19; auto.
apply notin_nu; intros; inversion_clear H21.
cut (notin x1 (nu (x2 z))); [ intro | auto ].
inversion_clear H21; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
rewrite H23; trivial.
rewrite H22; trivial.
apply H6; auto.
cut (notin y0 (nu (fun n : name => nu (x3 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H23; inversion_clear H32; auto.
cut (notin y0 (nu (fun n : name => nu (x2 n))));
 [ intro | apply proc_mono with y; assumption ].
rewrite H22; inversion_clear H32; auto.
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15.
apply proc_mono with x1; inversion_clear H15; auto.
inversion_clear H16.
cut (notin y (nu (q'0 x1))); [ intro | auto ].
rewrite <- H12 in H16.
apply proc_mono with x1; inversion_clear H16; auto.
unfold f_act_notin_ho in |- *; intros; apply f_act_notin_Out; auto.
cut (x0 <> y); [ intro; auto | apply Sep_proc with (nu p1) ].
apply Aux2 with (bOut x0) p2; [ apply b_act_isin_bOut | auto ].
inversion_clear H15.
cut (notin y (p'0 x1)); [ intro | auto ].
rewrite <- H11 in H15; rewrite <- H23 in H15; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; auto.

Qed.

Lemma FTR_L3 :
 forall (p q : name -> proc) (a : name -> f_act) (x : name),
 notin x (nu p) ->
 notin x (nu q) ->
 f_act_notin_ho x a ->
 ftrans (p x) (a x) (q x) ->
 forall y : name,
 notin y (nu p) ->
 notin y (nu q) -> f_act_notin_ho y a -> ftrans (p y) (a y) (q y).

Proof.

intros; apply L3 with (p x) (q x) (a x) x; auto.

Qed.

Lemma BTR_L3 :
 forall (p : name -> proc) (q : name -> name -> proc) 
   (a : name -> b_act) (x : name),
 notin x (nu p) ->
 notin x (nu (fun z : name => nu (q z))) ->
 b_act_notin_ho x a ->
 btrans (p x) (a x) (q x) ->
 forall y : name,
 notin y (nu p) ->
 notin y (nu (fun z : name => nu (q z))) ->
 b_act_notin_ho y a -> btrans (p y) (a y) (q y).

Proof.

intros; apply L3bis with (p x) (a x) (q x) x; auto.

Qed.

End MPW_Lemma3.

Section MPW_Lemma6.

(***************************************************************)
(* Since a coinductive proof of Lemma 6 is not straightforward *)
(* (indeed all the attempts made using the Cofix tactic lead   *)
(* to guardedness problems), we will prove it by means of      *)
(* the GFP encoding approach and the Cross Adequacy result.    *)
(***************************************************************)

Inductive Op_S (R : proc -> proc -> Prop) : proc -> proc -> Prop :=
    op_s :
      forall (p q : name -> proc) (z : name),
      notin z (nu p) ->
      notin z (nu q) ->
      R (p z) (q z) ->
      forall w : name,
      w <> z -> notin w (nu p) -> notin w (nu q) -> Op_S R (p w) (q w).

Fixpoint Bfun (n : nat) : proc -> proc -> Prop :=
  match n with
  | O => StBisim
  | S m => Op_S (Bfun m)
  end.

Inductive BL6 (p q : proc) : Prop :=
    bl6 : forall n : nat, Bfun n p q -> BL6 p q.

Lemma BisimL6 : Inclus BL6 (Op_StBisim BL6).

Proof.

unfold Inclus in |- *; intros.
inversion_clear H.
cut (Bfun n p1 p2);
 [ generalize p1 p2; generalize n; simple induction n0; intros | assumption ].

(* Base Case *)

cut (StBisim p0 p3); [ intro | auto ].
apply op_sb; split; intros; split; intros.

inversion_clear H1.
inversion_clear H3.
elim (H1 a); intros.
elim (H3 p4 H2); intros.
exists x; split; try tauto.
inversion_clear H6.
cut (Bfun 0 p4 x); [ intro | auto ].
apply bl6 with 0; auto.

inversion_clear H1.
inversion_clear H3.
elim (H1 a); intros.
elim (H5 q1 H2); intros.
exists x; split; try tauto.
inversion_clear H6.
cut (Bfun 0 x q1); [ intro | auto ].
apply bl6 with 0; auto.

split; intros.

inversion_clear H1.
inversion_clear H3.
inversion_clear H4.
elim (H3 x); intros.
elim (H4 p4 H2); intros.
exists x0; split; try tauto.
inversion_clear H7.
intro.
cut (StBisim (p4 y) (x0 y)); [ intro | auto ].
cut (Bfun 0 (p4 y) (x0 y)); [ intro | auto ].
apply bl6 with 0; auto.

inversion_clear H1.
inversion_clear H3.
inversion_clear H4.
elim (H3 x); intros.
elim (H6 q1 H2); intros.
exists x0; split; try tauto.
inversion_clear H7.
intro.
cut (StBisim (x0 y) (q1 y)); [ intro | auto ].
cut (Bfun 0 (x0 y) (q1 y)); [ intro | auto ].
apply bl6 with 0; auto.

split; intros.

inversion_clear H1.
inversion_clear H3.
inversion_clear H4.
elim (H5 x); intros.
elim (H4 p4 H2); intros.
exists x0; split; try tauto.
inversion_clear H7.
intros.
cut (StBisim (p4 y) (x0 y)); [ intro | auto ].
cut (Bfun 0 (p4 y) (x0 y)); [ intro | auto ].
apply bl6 with 0; auto.

inversion_clear H1.
inversion_clear H3.
inversion_clear H4.
elim (H5 x); intros.
elim (H6 q1 H2); intros.
exists x0; split; try tauto.
inversion_clear H7.
intros.
cut (StBisim (x0 y) (q1 y)); [ intro | auto ].
cut (Bfun 0 (x0 y) (q1 y)); [ intro | auto ].
apply bl6 with 0; auto.

(* Inductive Step *)

simpl in H1.
inversion H1.
cut (Op_StBisim BL6 (p z) (q z)); [ intro | auto ].
inversion_clear H10.
apply op_sb; split; intros; split; intros.

elim (proc_exp p4 w); intros.
inversion_clear H12.
rewrite H14 in H10.
rewrite H14.
elim (f_act_exp a w); intros.
inversion_clear H12.
rewrite H16 in H10.
rewrite H16.
cut (ftrans (p z) (x0 z) (x z)); [ intro | idtac ].
inversion_clear H11.
elim (H17 (x0 z)); intros.
elim (H11 (x z) H12); intros.
elim (proc_exp x1 z); intros.
inversion_clear H21.
rewrite H23 in H20.
inversion_clear H20.
cut (ftrans (q w) (x0 w) (x2 w)); [ intro | idtac ].
exists (x2 w); split; auto.
inversion_clear H24.
apply bl6 with (S n2).
simpl in |- *.
apply op_s with z; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (FTR_L1 (p w) (x w) (x0 w) z H24 H10); intros; auto.
apply proc_mono with w; auto.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (FTR_L1 (q z) (x2 z) (x0 z) w H24 H21); intros; auto.
apply proc_mono with z; auto.
apply FTR_L3 with z; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (FTR_L1 (p w) (x w) (x0 w) z H20 H10); intros; auto.
apply f_act_mono with w; auto.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (FTR_L1 (q z) (x2 z) (x0 z) w H20 H21); intros; auto.
apply proc_mono with z; auto.
apply FTR_L3 with w; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (FTR_L1 (p w) (x w) (x0 w) z H12 H10); intros; auto.
apply proc_mono with w; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (FTR_L1 (p w) (x w) (x0 w) z H12 H10); intros; auto.
apply f_act_mono with w; auto.

elim (proc_exp q1 w); intros.
inversion_clear H12.
rewrite H14 in H10.
rewrite H14.
elim (f_act_exp a w); intros.
inversion_clear H12.
rewrite H16 in H10.
rewrite H16.
cut (ftrans (q z) (x0 z) (x z)); [ intro | idtac ].
inversion_clear H11.
elim (H17 (x0 z)); intros.
elim (H19 (x z) H12); intros.
elim (proc_exp x1 z); intros.
inversion_clear H21.
rewrite H23 in H20.
inversion_clear H20.
cut (ftrans (p w) (x0 w) (x2 w)); [ intro | idtac ].
exists (x2 w); split; auto.
inversion_clear H24.
apply bl6 with (S n2).
simpl in |- *.
apply op_s with z; auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (FTR_L1 (q w) (x w) (x0 w) z H24 H10); intros; auto.
apply proc_mono with w; auto.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (FTR_L1 (p z) (x2 z) (x0 z) w H24 H21); intros; auto.
apply proc_mono with z; auto.
apply FTR_L3 with z; auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (FTR_L1 (q w) (x w) (x0 w) z H20 H10); intros; auto.
apply f_act_mono with w; auto.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (FTR_L1 (p z) (x2 z) (x0 z) w H20 H21); intros; auto.
apply proc_mono with z; auto.
apply FTR_L3 with w; auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (FTR_L1 (q w) (x w) (x0 w) z H12 H10); intros; auto.
apply proc_mono with w; auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (FTR_L1 (q w) (x w) (x0 w) z H12 H10); intros; auto.
apply f_act_mono with w; auto.

(* Input-actions *)

split; intros.
elim (LEM_name w x); intros.

(* Case: w=x *)

rewrite <- H12 in H10.
rewrite <- H12.
elim (ho_proc_exp p4 w); intros.
inversion_clear H13.
rewrite H15 in H10.
cut (btrans (p z) (In z) (x0 z)); [ intro | idtac ].
inversion_clear H11.
inversion_clear H17.
elim (H11 z); intros.
elim (H17 (x0 z) H13); intros.
inversion_clear H20.
elim (ho_proc_exp x1 z); intros.
inversion_clear H20.
rewrite H24 in H21.
rewrite H24 in H22.
cut (btrans (q w) (In w) (x2 w)); [ intro | idtac ].
exists (x2 w); split.
assumption.
rewrite H15.
intro.
elim (LEM_name y w); elim (LEM_name y z); intros.

(* Subcase (y=w/\y=z) *)

cut (w = z); [ intro | rewrite <- H25; rewrite <- H26; trivial ].
rewrite H27; auto.

(* Subcase (y=w/\~y=z) *)

rewrite H26.
cut (BL6 (x0 z z) (x2 z z)); [ intro | auto ].
inversion_clear H27.
apply bl6 with (S n2).
simpl in |- *.
change
  (Op_S (Bfun n2) ((fun n : name => x0 n n) w) ((fun n : name => x2 n n) w))
 in |- *.
apply op_s with z; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In w) z H27 H10); intros.
apply proc_mono with w.
inversion_clear H30; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (In z) w H27 H21); intros.
apply proc_mono with z.
inversion_clear H30; auto.

(* Subcase (~y=w/\y=z) *)

rewrite H25.
elim
 (unsat
    (par (nu (fun y : name => nu (x0 y))) (nu (fun y : name => nu (x2 y))))
    (cons w (cons z empty))); intros.
inversion_clear H27.
inversion_clear H28.
inversion_clear H29.
inversion_clear H31.
clear H32.
cut (BL6 (x0 z x3) (x2 z x3)); [ intro | auto ].
inversion_clear H31.
apply bl6 with (S (S n2)).
simpl in |- *.
apply op_s with x3; auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 w))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 w))); [ intro | auto ].
inversion_clear H30.
auto.
change
  (Op_S (Bfun n2) ((fun n : name => x0 n x3) w) ((fun n : name => x2 n x3) w))
 in |- *.
apply op_s with z; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In w) z H31 H10); intros.
apply proc_mono with w.
inversion_clear H34; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (In z) w H31 H21); intros.
apply proc_mono with z.
inversion_clear H34; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In w) z H31 H10); intros.
apply proc_mono with w.
inversion_clear H34; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 w))); [ intro | auto ].
inversion_clear H23.
auto.

(* Subcase (~y=w/\~y=z) *)

cut (BL6 (x0 z y) (x2 z y)); [ intro | auto ].
inversion_clear H27.
apply bl6 with (S n2).
simpl in |- *.
change
  (Op_S (Bfun n2) ((fun n : name => x0 n y) w) ((fun n : name => x2 n y) w))
 in |- *.
apply op_s with z; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In w) z H27 H10); intros.
apply proc_mono with w.
inversion_clear H30; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (In z) w H27 H21); intros.
apply proc_mono with z.
inversion_clear H30; auto.

apply BTR_L3 with z; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (In z) w H20 H21); intros.
apply proc_mono with z.
auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.

apply BTR_L3 with w; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In w) z H13 H10); intros.
apply proc_mono with w.
auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.

(* Case ~w=x *)

elim (ho_proc_exp p4 w); intros.
inversion_clear H13.
rewrite H15 in H10.
cut (btrans (p z) (In x) (x0 z)); [ intro | idtac ].
inversion_clear H11.
inversion_clear H17.
elim (H11 x); intros.
elim (H17 (x0 z) H13); intros.
inversion_clear H20.
elim (ho_proc_exp x1 z); intros.
inversion_clear H20.
rewrite H24 in H21.
rewrite H24 in H22.
cut (btrans (q w) (In x) (x2 w)); [ intro | idtac ].
exists (x2 w); split.
assumption.
rewrite H15.
intro.
elim (LEM_name y w); elim (LEM_name y z); intros.

(* Subcase (y=w/\y=z) *)

cut (w = z); [ intro | rewrite <- H25; rewrite <- H26; trivial ].
rewrite H27; auto.

(* Subcase (y=w/\~y=z) *)

rewrite H26.
cut (BL6 (x0 z z) (x2 z z)); [ intro | auto ].
inversion_clear H27.
apply bl6 with (S n2).
simpl in |- *.
change
  (Op_S (Bfun n2) ((fun n : name => x0 n n) w) ((fun n : name => x2 n n) w))
 in |- *.
apply op_s with z; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In x) z H27 H10); intros.
apply proc_mono with w.
inversion_clear H30; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (In x) w H27 H21); intros.
apply proc_mono with z.
inversion_clear H30; auto.

(* Subcase (~y=w/\y=z) *)

rewrite H25.
elim
 (unsat
    (par (nu (fun y : name => nu (x0 y))) (nu (fun y : name => nu (x2 y))))
    (cons w (cons z empty))); intros.
inversion_clear H27.
inversion_clear H28.
inversion_clear H29.
inversion_clear H31.
clear H32.
cut (BL6 (x0 z x3) (x2 z x3)); [ intro | auto ].
inversion_clear H31.
apply bl6 with (S (S n2)).
simpl in |- *.
apply op_s with x3; auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 w))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 w))); [ intro | auto ].
inversion_clear H30.
auto.
change
  (Op_S (Bfun n2) ((fun n : name => x0 n x3) w) ((fun n : name => x2 n x3) w))
 in |- *.
apply op_s with z; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In x) z H31 H10); intros.
apply proc_mono with w.
inversion_clear H34; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (In x) w H31 H21); intros.
apply proc_mono with z.
inversion_clear H34; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In x) z H31 H10); intros.
apply proc_mono with w.
inversion_clear H34; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 w))); [ intro | auto ].
inversion_clear H23.
auto.

(* Subcase (~y=w/\~y=z) *)

cut (BL6 (x0 z y) (x2 z y)); [ intro | auto ].
inversion_clear H27.
apply bl6 with (S n2).
simpl in |- *.
change
  (Op_S (Bfun n2) ((fun n : name => x0 n y) w) ((fun n : name => x2 n y) w))
 in |- *.
apply op_s with z; auto.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In x) z H27 H10); intros.
apply proc_mono with w.
inversion_clear H30; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (In x) w H27 H21); intros.
apply proc_mono with z.
inversion_clear H30; auto.

cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In x) z H20 H10); intros.
change (btrans (q w) ((fun n : name => In x) w) (x2 w)) in |- *.
apply BTR_L3 with z; auto.
unfold b_act_notin_ho in |- *; intros; assumption.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (In x) w H27 H21); intros.
apply proc_mono with z; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.

cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (In x) z H13 H10); intros.
change (btrans (p z) ((fun n : name => In x) z) (x0 z)) in |- *.
apply BTR_L3 with w; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.
apply proc_mono with w; assumption.
unfold b_act_notin_ho in |- *; intros; assumption.

(* The way back (symmetric case) *)

elim (LEM_name w x); intros.

(* Case: w=x *)

rewrite <- H12 in H10.
rewrite <- H12.
elim (ho_proc_exp q1 w); intros.
inversion_clear H13.
rewrite H15 in H10.
cut (btrans (q z) (In z) (x0 z)); [ intro | idtac ].
inversion_clear H11.
inversion_clear H17.
elim (H11 z); intros.
elim (H19 (x0 z) H13); intros.
inversion_clear H20.
elim (ho_proc_exp x1 z); intros.
inversion_clear H20.
rewrite H24 in H21.
rewrite H24 in H22.
cut (btrans (p w) (In w) (x2 w)); [ intro | idtac ].
exists (x2 w); split.
assumption.
rewrite H15.
intro.
elim (LEM_name y w); elim (LEM_name y z); intros.

(* Subcase (y=w/\y=z) *)

cut (w = z); [ intro | rewrite <- H25; rewrite <- H26; trivial ].
rewrite H27; auto.

(* Subcase (y=w/\~y=z) *)

rewrite H26.
cut (BL6 (x2 z z) (x0 z z)); [ intro | auto ].
inversion_clear H27.
apply bl6 with (S n2).
simpl in |- *.
change
  (Op_S (Bfun n2) ((fun n : name => x2 n n) w) ((fun n : name => x0 n n) w))
 in |- *.
apply op_s with z; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In w) z H27 H10); intros.
apply proc_mono with w.
inversion_clear H30; auto.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (In z) w H27 H21); intros.
apply proc_mono with z.
inversion_clear H30; auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.

(* Subcase (~y=w/\y=z) *)

rewrite H25.
elim
 (unsat
    (par (nu (fun y : name => nu (x0 y))) (nu (fun y : name => nu (x2 y))))
    (cons w (cons z empty))); intros.
inversion_clear H27.
inversion_clear H28.
inversion_clear H29.
inversion_clear H31.
clear H32.
cut (BL6 (x2 z x3) (x0 z x3)); [ intro | auto ].
inversion_clear H31.
apply bl6 with (S (S n2)).
simpl in |- *.
apply op_s with x3; auto.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 w))); [ intro | auto ].
inversion_clear H30.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 w))); [ intro | auto ].
inversion_clear H27.
auto.
change
  (Op_S (Bfun n2) ((fun n : name => x2 n x3) w) ((fun n : name => x0 n x3) w))
 in |- *.
apply op_s with z; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In w) z H31 H10); intros.
apply proc_mono with w.
inversion_clear H34; auto.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (In z) w H31 H21); intros.
apply proc_mono with z.
inversion_clear H34; auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 w))); [ intro | auto ].
inversion_clear H23.
auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In w) z H31 H10); intros.
apply proc_mono with w.
inversion_clear H34; auto.

(* Subcase (~y=w/\~y=z) *)

cut (BL6 (x2 z y) (x0 z y)); [ intro | auto ].
inversion_clear H27.
apply bl6 with (S n2).
simpl in |- *.
change
  (Op_S (Bfun n2) ((fun n : name => x2 n y) w) ((fun n : name => x0 n y) w))
 in |- *.
apply op_s with z; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In w) z H27 H10); intros.
apply proc_mono with w.
inversion_clear H30; auto.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (In z) w H27 H21); intros.
apply proc_mono with z.
inversion_clear H30; auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.

apply BTR_L3 with z; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (In z) w H20 H21); intros.
apply proc_mono with z.
auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.

apply BTR_L3 with w; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In w) z H13 H10); intros.
apply proc_mono with w.
auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.

(* Case ~w=x *)

elim (ho_proc_exp q1 w); intros.
inversion_clear H13.
rewrite H15 in H10.
cut (btrans (q z) (In x) (x0 z)); [ intro | idtac ].
inversion_clear H11.
inversion_clear H17.
elim (H11 x); intros.
elim (H19 (x0 z) H13); intros.
inversion_clear H20.
elim (ho_proc_exp x1 z); intros.
inversion_clear H20.
rewrite H24 in H21.
rewrite H24 in H22.
cut (btrans (p w) (In x) (x2 w)); [ intro | idtac ].
exists (x2 w); split.
assumption.
rewrite H15.
intro.
elim (LEM_name y w); elim (LEM_name y z); intros.

(* Subcase (y=w/\y=z) *)

cut (w = z); [ intro | rewrite <- H25; rewrite <- H26; trivial ].
rewrite H27; auto.

(* Subcase (y=w/\~y=z) *)

rewrite H26.
cut (BL6 (x2 z z) (x0 z z)); [ intro | auto ].
inversion_clear H27.
apply bl6 with (S n2).
simpl in |- *.
change
  (Op_S (Bfun n2) ((fun n : name => x2 n n) w) ((fun n : name => x0 n n) w))
 in |- *.
apply op_s with z; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In x) z H27 H10); intros.
apply proc_mono with w.
inversion_clear H30; auto.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (In x) w H27 H21); intros.
apply proc_mono with z.
inversion_clear H30; auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.

(* Subcase (~y=w/\y=z) *)

rewrite H25.
elim
 (unsat
    (par (nu (fun y : name => nu (x0 y))) (nu (fun y : name => nu (x2 y))))
    (cons w (cons z empty))); intros.
inversion_clear H27.
inversion_clear H28.
inversion_clear H29.
inversion_clear H31.
clear H32.
cut (BL6 (x2 z x3) (x0 z x3)); [ intro | auto ].
inversion_clear H31.
apply bl6 with (S (S n2)).
simpl in |- *.
apply op_s with x3; auto.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 w))); [ intro | auto ].
inversion_clear H30.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 w))); [ intro | auto ].
inversion_clear H27.
auto.
change
  (Op_S (Bfun n2) ((fun n : name => x2 n x3) w) ((fun n : name => x0 n x3) w))
 in |- *.
apply op_s with z; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In x) z H31 H10); intros.
apply proc_mono with w.
inversion_clear H34; auto.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (In x) w H31 H21); intros.
apply proc_mono with z.
inversion_clear H34; auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 w))); [ intro | auto ].
inversion_clear H23.
auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In x) z H31 H10); intros.
apply proc_mono with w.
inversion_clear H34; auto.

(* Subcase (~y=w/\~y=z) *)

cut (BL6 (x2 z y) (x0 z y)); [ intro | auto ].
inversion_clear H27.
apply bl6 with (S n2).
simpl in |- *.
change
  (Op_S (Bfun n2) ((fun n : name => x2 n y) w) ((fun n : name => x0 n y) w))
 in |- *.
apply op_s with z; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In x) z H27 H10); intros.
apply proc_mono with w.
inversion_clear H30; auto.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (In x) w H27 H21); intros.
apply proc_mono with z.
inversion_clear H30; auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.

cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In x) z H20 H10); intros.
change (btrans (p w) ((fun n : name => In x) w) (x2 w)) in |- *.
apply BTR_L3 with z; auto.
unfold b_act_notin_ho in |- *; intros; assumption.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (In x) w H27 H21); intros.
apply proc_mono with z; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.

cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (In x) z H13 H10); intros.
change (btrans (q z) ((fun n : name => In x) z) (x0 z)) in |- *.
apply BTR_L3 with w; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_In; assumption.
apply proc_mono with w; assumption.
unfold b_act_notin_ho in |- *; intros; assumption.

(* Bound-output actions *)

split; intros.
elim (LEM_name w x); intros.

(* Case w=x *)

rewrite <- H12 in H10.
rewrite <- H12.
elim (ho_proc_exp p4 w); intros.
inversion_clear H13.
rewrite H15 in H10.
cut (btrans (p z) (bOut z) (x0 z)); [ intro | idtac ].
inversion_clear H11.
inversion_clear H17.
elim (H18 z); intros.
elim (H17 (x0 z) H13); intros.
inversion_clear H20.
elim (ho_proc_exp x1 z); intros.
inversion_clear H20.
rewrite H24 in H21.
rewrite H24 in H22.
cut (btrans (q w) (bOut w) (x2 w)); [ intro | idtac ].
exists (x2 w); split.
assumption.
rewrite H15.
intros.
elim
 (unsat
    (par (nu (fun n : name => nu (x0 n))) (nu (fun n : name => nu (x2 n))))
    (cons y (cons z (cons w empty)))); intros.
inversion_clear H27.
inversion_clear H28.
inversion_clear H29.
inversion_clear H31.
inversion_clear H32.
clear H33.
cut (BL6 (x0 z x3) (x2 z x3)); [ intro | apply H22; auto ].
inversion_clear H32.
apply bl6 with (S (S n2)).
simpl in |- *.
apply op_s with x3; intros.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 w))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 w))); [ intro | auto ].
inversion_clear H30.
auto.
change
  (Op_S (Bfun n2) ((fun n : name => x0 n x3) w) ((fun n : name => x2 n x3) w))
 in |- *.
apply op_s with z; intros.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (bOut w) z H32 H10); intros.
apply proc_mono with w.
inversion_clear H35; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
assumption.
auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (bOut z) w H32 H21); intros.
apply proc_mono with z.
inversion_clear H35; auto.
auto.
auto.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 z))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 z))); [ intro | auto ].
inversion_clear H30.
auto.

cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (bOut w) z H20 H10); intros.
apply BTR_L3 with z; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (bOut z) w H27 H21); intros.
apply proc_mono with z; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.

cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (bOut w) z H13 H10); intros.
apply BTR_L3 with w; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.
apply proc_mono with w; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.

(* Case ~w=x *)

elim (ho_proc_exp p4 w); intros.
inversion_clear H13.
rewrite H15 in H10.
cut (btrans (p z) (bOut x) (x0 z)); [ intro | idtac ].
inversion_clear H11.
inversion_clear H17.
elim (H18 x); intros.
elim (H17 (x0 z) H13); intros.
inversion_clear H20.
elim (ho_proc_exp x1 z); intros.
inversion_clear H20.
rewrite H24 in H21.
rewrite H24 in H22.
cut (btrans (q w) (bOut x) (x2 w)); [ intro | idtac ].
exists (x2 w); split.
assumption.
rewrite H15.
intros.
elim
 (unsat
    (par (nu (fun n : name => nu (x0 n))) (nu (fun n : name => nu (x2 n))))
    (cons y (cons z (cons w empty)))); intros.
inversion_clear H27.
inversion_clear H28.
inversion_clear H29.
inversion_clear H31.
inversion_clear H32.
clear H33.
cut (BL6 (x0 z x3) (x2 z x3)); [ intro | apply H22; auto ].
inversion_clear H32.
apply bl6 with (S (S n2)).
simpl in |- *.
apply op_s with x3; intros.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 w))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 w))); [ intro | auto ].
inversion_clear H30.
auto.
change
  (Op_S (Bfun n2) ((fun n : name => x0 n x3) w) ((fun n : name => x2 n x3) w))
 in |- *.
apply op_s with z; intros.
cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (bOut x) z H32 H10); intros.
apply proc_mono with w.
inversion_clear H35; auto.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
assumption.
auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (bOut x) w H32 H21); intros.
apply proc_mono with z.
inversion_clear H35; auto.
auto.
auto.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 z))); [ intro | auto ].
inversion_clear H27.
auto.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 z))); [ intro | auto ].
inversion_clear H30.
auto.

cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (bOut x) z H20 H10); intros.
change (btrans (q w) ((fun n : name => bOut x) w) (x2 w)) in |- *.
apply BTR_L3 with z; auto.
unfold b_act_notin_ho in |- *; intros; assumption.
cut (notin w (q z)); [ intro | inversion H7; auto ].
elim (BTR_L1 (q z) (x2 z) (bOut x) w H27 H21); intros.
apply proc_mono with z; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.

cut (notin z (p w)); [ intro | inversion H2; auto ].
elim (BTR_L1 (p w) (x0 w) (bOut x) z H13 H10); intros.
change (btrans (p z) ((fun n : name => bOut x) z) (x0 z)) in |- *.
apply BTR_L3 with w; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.
apply proc_mono with w; assumption.
unfold b_act_notin_ho in |- *; intros; assumption.

(* The symmetric case. *)

elim (LEM_name w x); intros.

(* Case w=x *)

rewrite <- H12 in H10.
rewrite <- H12.
elim (ho_proc_exp q1 w); intros.
inversion_clear H13.
rewrite H15 in H10.
cut (btrans (q z) (bOut z) (x0 z)); [ intro | idtac ].
inversion_clear H11.
inversion_clear H17.
elim (H18 z); intros.
elim (H19 (x0 z) H13); intros.
inversion_clear H20.
elim (ho_proc_exp x1 z); intros.
inversion_clear H20.
rewrite H24 in H21.
rewrite H24 in H22.
cut (btrans (p w) (bOut w) (x2 w)); [ intro | idtac ].
exists (x2 w); split.
assumption.
rewrite H15.
intros.
elim
 (unsat
    (par (nu (fun n : name => nu (x0 n))) (nu (fun n : name => nu (x2 n))))
    (cons y (cons z (cons w empty)))); intros.
inversion_clear H27.
inversion_clear H28.
inversion_clear H29.
inversion_clear H31.
inversion_clear H32.
clear H33.
cut (BL6 (x2 z x3) (x0 z x3)); [ intro | apply H22; auto ].
inversion_clear H32.
apply bl6 with (S (S n2)).
simpl in |- *.
apply op_s with x3; intros.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 w))); [ intro | auto ].
inversion_clear H30.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 w))); [ intro | auto ].
inversion_clear H27.
auto.
change
  (Op_S (Bfun n2) ((fun n : name => x2 n x3) w) ((fun n : name => x0 n x3) w))
 in |- *.
apply op_s with z; intros.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (bOut w) z H32 H10); intros.
apply proc_mono with w.
inversion_clear H35; auto.
assumption.
auto.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (bOut z) w H32 H21); intros.
apply proc_mono with z.
inversion_clear H35; auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
auto.
auto.
auto.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 z))); [ intro | auto ].
inversion_clear H30.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 z))); [ intro | auto ].
inversion_clear H27.
auto.

cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (bOut w) z H20 H10); intros.
apply BTR_L3 with z; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (bOut z) w H27 H21); intros.
apply proc_mono with z; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.

cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (bOut w) z H13 H10); intros.
apply BTR_L3 with w; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.
apply proc_mono with w; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.

(* Case ~w=x *)

elim (ho_proc_exp q1 w); intros.
inversion_clear H13.
rewrite H15 in H10.
cut (btrans (q z) (bOut x) (x0 z)); [ intro | idtac ].
inversion_clear H11.
inversion_clear H17.
elim (H18 x); intros.
elim (H19 (x0 z) H13); intros.
inversion_clear H20.
elim (ho_proc_exp x1 z); intros.
inversion_clear H20.
rewrite H24 in H21.
rewrite H24 in H22.
cut (btrans (p w) (bOut x) (x2 w)); [ intro | idtac ].
exists (x2 w); split.
assumption.
rewrite H15.
intros.
elim
 (unsat
    (par (nu (fun n : name => nu (x0 n))) (nu (fun n : name => nu (x2 n))))
    (cons y (cons z (cons w empty)))); intros.
inversion_clear H27.
inversion_clear H28.
inversion_clear H29.
inversion_clear H31.
inversion_clear H32.
clear H33.
cut (BL6 (x2 z x3) (x0 z x3)); [ intro | apply H22; auto ].
inversion_clear H32.
apply bl6 with (S (S n2)).
simpl in |- *.
apply op_s with x3; intros.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 w))); [ intro | auto ].
inversion_clear H30.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 w))); [ intro | auto ].
inversion_clear H27.
auto.
change
  (Op_S (Bfun n2) ((fun n : name => x2 n x3) w) ((fun n : name => x0 n x3) w))
 in |- *.
apply op_s with z; intros.
apply notin_nu; intros.
inversion_clear H23.
cut (notin z (nu (x2 z0))); [ intro | auto ].
inversion_clear H23.
auto.
cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (bOut x) z H32 H10); intros.
apply proc_mono with w.
inversion_clear H35; auto.
assumption.
auto.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (bOut x) w H32 H21); intros.
apply proc_mono with z.
inversion_clear H35; auto.
apply notin_nu; intros.
inversion_clear H14.
cut (notin w (nu (x0 z0))); [ intro | auto ].
inversion_clear H14.
auto.
auto.
auto.
auto.
apply notin_nu; intros.
inversion_clear H30.
cut (notin x3 (nu (x2 z))); [ intro | auto ].
inversion_clear H30.
auto.
apply notin_nu; intros.
inversion_clear H27.
cut (notin x3 (nu (x0 z))); [ intro | auto ].
inversion_clear H27.
auto.

cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (bOut x) z H20 H10); intros.
change (btrans (p w) ((fun n : name => bOut x) w) (x2 w)) in |- *.
apply BTR_L3 with z; auto.
unfold b_act_notin_ho in |- *; intros; assumption.
cut (notin w (p z)); [ intro | inversion H6; auto ].
elim (BTR_L1 (p z) (x2 z) (bOut x) w H27 H21); intros.
apply proc_mono with z; assumption.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.

cut (notin z (q w)); [ intro | inversion H3; auto ].
elim (BTR_L1 (q w) (x0 w) (bOut x) z H13 H10); intros.
change (btrans (q z) ((fun n : name => bOut x) z) (x0 z)) in |- *.
apply BTR_L3 with w; auto.
unfold b_act_notin_ho in |- *; intros; apply b_act_notin_bOut; assumption.
apply proc_mono with w; assumption.
unfold b_act_notin_ho in |- *; intros; assumption.

Qed.

(****************************)
(* Now, the "real" Lemma 6. *)
(****************************)

Lemma L6 :
 forall (p q : name -> proc) (z : name),
 notin z (nu p) ->
 notin z (nu q) ->
 StBisim (p z) (q z) ->
 forall w : name,
 w <> z -> notin w (nu p) -> notin w (nu q) -> StBisim (p w) (q w).

Proof.

intros.
apply Completeness.
apply Co_Ind with BL6.
exact BisimL6.
cut (BL6 (p z) (q z)); [ intro | apply bl6 with 0; auto ].
inversion_clear H5.
apply bl6 with (S n).
simpl in |- *.
apply op_s with z; auto.

Qed.

(*****************************************************)
(* A lighter version of the same lemma, often useful *)
(* in proving algebraic laws.                        *)
(*****************************************************)

Lemma L6_Light :
 forall (p q : name -> proc) (z : name),
 notin z (nu p) ->
 notin z (nu q) ->
 StBisim (p z) (q z) ->
 forall w : name, notin w (nu p) -> notin w (nu q) -> StBisim (p w) (q w).

Proof.

intros.
elim (LEM_name w z); intros.
rewrite H4; auto.
apply L6 with z; auto.

Qed.

End MPW_Lemma6.