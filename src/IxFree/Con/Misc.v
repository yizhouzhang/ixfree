Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Con.Arrow.
Require Import IxFree.Con.Conj.
Require Import IxFree.Con.Disj.
Require Import IxFree.Con.Iff.
Require Import IxFree.Con.Forall.
Require Import IxFree.Con.Exists.
Require Import IxFree.Con.Later.
Require Import IxFree.Con.Tactics.

Lemma I_iff_symmetric {n : nat} {P Q : IProp} :
(n ⊨ Q ⇔ P) → (n ⊨ P ⇔ Q).
Proof.
intro H ; idestruct H as H1 H2 ; isplit ; iintro H ; [ iapply H2 | iapply H1 ] ; apply H.
Qed.

Lemma I_iff_transitive {n : nat} {P Q R : IProp} :
(n ⊨ P ⇔ Q) → (n ⊨ Q ⇔ R) → (n ⊨ P ⇔ R).
Proof.
intros H1 H2 ; idestruct H1 as H11 H12 ; idestruct H2 as H21 H22.
isplit.
+ iintro H ; iapply H21 ; iapply H11 ; apply H.
+ iintro H ; iapply H12 ; iapply H22 ; apply H.
Qed.