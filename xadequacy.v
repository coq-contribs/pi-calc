(*******************************************************)
(*                                                     *)
(*  Proof of cross adequacy between the two encodings  *)
(*            of Strong Late Bisimilarity.             *)
(*                                                     *)
(*******************************************************)
(*                                                     *)
(* File   : xadequacy.v                                *)
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

Section picalc_xadeq.

(*****************************************************************)
(* Monotonicity of the operator of the Strong Late Bisimilarity. *)
(*****************************************************************)

Lemma Op_StBisim_monotone :
 forall R1 R2 : proc -> proc -> Prop,
 Inclus R1 R2 -> Inclus (Op_StBisim R1) (Op_StBisim R2).

Proof.

unfold Inclus in |- *.
intros.
inversion H0.
apply op_sb.
split.

intro.
cut
 ((forall p0 : proc,
   ftrans p1 a p0 -> exists q1 : proc, ftrans p2 a q1 /\ R1 p0 q1) /\
  (forall q1 : proc,
   ftrans p2 a q1 -> exists p0 : proc, ftrans p1 a p0 /\ R1 p0 q1)).
intro. elim H2. intros. clear H2. split. intros.
cut (exists q1 : proc, ftrans p2 a q1 /\ R1 p0 q1).
intro.
elim H5. intros. clear H5.
exists x.
split. tauto. elim H6.
intros. clear H6.
auto. auto. intros.
cut (exists p0 : proc, ftrans p1 a p0 /\ R1 p0 q1).
intro.
elim H5. intros. clear H5.
exists x.
split. tauto. elim H6.
intros. clear H6.
auto. auto. elim H1. intros. auto.

split.

intro.
cut
 ((forall p0 : name -> proc,
   btrans p1 (In x) p0 ->
   exists q1 : name -> proc,
     btrans p2 (In x) q1 /\ (forall y : name, R1 (p0 y) (q1 y))) /\
  (forall q1 : name -> proc,
   btrans p2 (In x) q1 ->
   exists p0 : name -> proc,
     btrans p1 (In x) p0 /\ (forall y : name, R1 (p0 y) (q1 y)))).
intro. elim H2. intros. clear H2. split. intros. 
cut
 (exists q1 : name -> proc,
    btrans p2 (In x) q1 /\ (forall y : name, R1 (p0 y) (q1 y))). 
intro. 
elim H5. intros. clear H5. 
exists x0. 
split. tauto. elim H6. 
intros. clear H6. 
auto. auto. intros. 
cut
 (exists p0 : name -> proc,
    btrans p1 (In x) p0 /\ (forall y : name, R1 (p0 y) (q1 y))). 
intro. 
elim H5. intros. clear H5. 
exists x0. 
split. tauto. elim H6. 
intros. clear H6. 
auto. auto. elim H1. intros. elim H3. intros. auto. 

intro. 
cut
 ((forall p0 : name -> proc,
   btrans p1 (bOut x) p0 ->
   exists q1 : name -> proc,
     btrans p2 (bOut x) q1 /\
     (forall y : name, notin y (nu p0) -> notin y (nu q1) -> R1 (p0 y) (q1 y))) /\
  (forall q1 : name -> proc,
   btrans p2 (bOut x) q1 ->
   exists p0 : name -> proc,
     btrans p1 (bOut x) p0 /\
     (forall y : name, notin y (nu p0) -> notin y (nu q1) -> R1 (p0 y) (q1 y)))). 
intros. elim H2. intros. clear H2. split. intros. 
cut
 (exists q1 : name -> proc,
    btrans p2 (bOut x) q1 /\
    (forall y : name, notin y (nu p0) -> notin y (nu q1) -> R1 (p0 y) (q1 y))). 
intro. 
elim H5. intros. clear H5. 
exists x0. 
split. tauto. elim H6. 
intros. clear H6. 
auto. auto. intros. 
cut
 (exists p0 : name -> proc,
    btrans p1 (bOut x) p0 /\
    (forall y : name, notin y (nu p0) -> notin y (nu q1) -> R1 (p0 y) (q1 y))). 
intro. 
elim H5. intros. clear H5. 
exists x0. 
split. tauto. elim H6. 
intros. clear H6. 
auto. auto. elim H1. intros. elim H3. intros. auto. 

Qed. 

(****************************)
(* Internal Cross Adequacy.  *)
(****************************)

Lemma Soundness : forall p1 p2 : proc, StBisim p1 p2 -> StBisim' p1 p2. 

Proof. 

intros. 
apply Co_Ind with StBisim. 
unfold Inclus in |- *. 
intros. 
inversion H0. 
apply op_sb. 
auto. auto. 

Qed. 

Lemma Completeness : forall p1 p2 : proc, StBisim' p1 p2 -> StBisim p1 p2. 

Proof. 

intros. elim H. unfold Inclus in |- *. do 2 intro.  generalize p1 p2. 
cofix. intros. case (H0 p0 p3 H1). intros. 

apply sb. split. intro. 
cut
 ((forall p1 : proc,
   ftrans p0 a p1 -> exists q1 : proc, ftrans p3 a q1 /\ R p1 q1) /\
  (forall q1 : proc,
   ftrans p3 a q1 -> exists p1 : proc, ftrans p0 a p1 /\ R p1 q1)). 
intro. elim H3. intros. clear H3. split. intros. cut (exists q1 : proc, ftrans p3 a q1 /\ R p4 q1). 
intro. elim H6. intros. clear H6. exists x. split. tauto. apply Completeness. tauto. auto. intros. 
cut (exists p1 : proc, ftrans p0 a p1 /\ R p1 q1). intro. elim H6. intros. clear H6. exists x. split. tauto. 
apply Completeness. tauto. auto. elim H2. intros. auto. 

split. 
intro. 
cut
 ((forall p1 : name -> proc,
   btrans p0 (In x) p1 ->
   exists q1 : name -> proc,
     btrans p3 (In x) q1 /\ (forall y : name, R (p1 y) (q1 y))) /\
  (forall q1 : name -> proc,
   btrans p3 (In x) q1 ->
   exists p1 : name -> proc,
     btrans p0 (In x) p1 /\ (forall y : name, R (p1 y) (q1 y)))). 
intro. elim H3. intros. clear H3. split. intros. 
cut
 (exists q1 : name -> proc,
    btrans p3 (In x) q1 /\ (forall y : name, R (p4 y) (q1 y))). 
intro. elim H6. intros. clear H6. exists x0. split. tauto. intro. apply Completeness. elim H7. intros. auto. 
auto. intros. 
cut
 (exists p1 : name -> proc,
    btrans p0 (In x) p1 /\ (forall y : name, R (p1 y) (q1 y))). 
intro. elim H6. intros. clear H6. exists x0. split. tauto. intro. apply Completeness. elim H7. intros. auto. 
auto. elim H2. intros. elim H4. intros. auto. 

intro. 
cut
 ((forall p1 : name -> proc,
   btrans p0 (bOut x) p1 ->
   exists q1 : name -> proc,
     btrans p3 (bOut x) q1 /\
     (forall y : name, notin y (nu p1) -> notin y (nu q1) -> R (p1 y) (q1 y))) /\
  (forall q1 : name -> proc,
   btrans p3 (bOut x) q1 ->
   exists p1 : name -> proc,
     btrans p0 (bOut x) p1 /\
     (forall y : name, notin y (nu p1) -> notin y (nu q1) -> R (p1 y) (q1 y)))). 
intro. elim H3. intros. clear H3. split. intros. 
cut
 (exists q1 : name -> proc,
    btrans p3 (bOut x) q1 /\
    (forall y : name, notin y (nu p4) -> notin y (nu q1) -> R (p4 y) (q1 y))). 
intro. elim H6. intros. clear H6. exists x0. split. tauto. intros. apply Completeness. elim H7. intros. auto. 
auto. intros. 
cut
 (exists p1 : name -> proc,
    btrans p0 (bOut x) p1 /\
    (forall y : name, notin y (nu p1) -> notin y (nu q1) -> R (p1 y) (q1 y))). 
intro. elim H6. intros. clear H6. exists x0. split. tauto. intros. apply Completeness. elim H7. intros. auto. 
auto. elim H2. intros. elim H4. intros. auto. 

Qed. 

End picalc_xadeq. 
