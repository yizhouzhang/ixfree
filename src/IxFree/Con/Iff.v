Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Con.Arrow IxFree.Con.Conj.

Definition I_iff (P Q : IProp) := (P ⇒ Q) ∧ᵢ (Q ⇒ P).

Notation "A ⇔ B" := (I_iff A B) (at level 95).

Lemma I_iff_intro_M {n : nat} {P Q : IProp} :
  (∀ k, k ≤ n → ((k ⊨ P) <-> (k ⊨ Q))) → (n ⊨ P ⇔ Q).
Proof.
intro H; apply I_conj_intro; apply I_arrow_intro; apply H.
Qed.

Lemma I_iff_elim_M {n : nat} {P Q : IProp} :
  (n ⊨ P ⇔ Q) → ((n ⊨ P) <-> (n ⊨ Q)).
Proof.
intro H; split; intro H'.
+ apply I_conj_elim1 in H; apply (I_arrow_elim H H').
+ apply I_conj_elim2 in H; apply (I_arrow_elim H H').
Qed.
