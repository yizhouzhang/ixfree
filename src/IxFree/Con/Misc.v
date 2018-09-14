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