Require Import Utf8.
Require Import List.

Definition monotone (P : nat → Prop) := ∀ n, P (S n) → P n.

Module Type IProp_S.

Parameter IProp : Type.

Parameter mk_IProp : ∀ P : nat → Prop, monotone P → IProp.

Parameter I_valid_at : nat -> IProp -> Prop.

Section I_valid.
Variable P : nat → Prop.
Variable H : monotone P.
Variable n : nat.

Parameter I_valid_intro : P n → I_valid_at n (mk_IProp P H).
Parameter I_valid_elim  : I_valid_at n (mk_IProp P H) → P n.
End I_valid.

Parameter I_valid_monotone_S : ∀ (P : IProp) (n : nat),
  I_valid_at (S n) P → I_valid_at n P.

End IProp_S.

Module IProp : IProp_S.

Definition IProp := { P : nat → Prop | monotone P }.

Definition mk_IProp (P : nat → Prop) (H : monotone P) :=
  exist _ P H.

Definition I_valid_at (n : nat) (P : IProp) : Prop :=
  proj1_sig P n.

Section I_valid.
Variable P : nat → Prop.
Variable H : monotone P.
Variable n : nat.

Lemma I_valid_intro : P n → I_valid_at n (mk_IProp P H).
Proof. auto. Qed.
Lemma I_valid_elim  : I_valid_at n (mk_IProp P H) → P n.
Proof. auto. Qed.
End I_valid.

Lemma I_valid_monotone_S (P : IProp) (n : nat) :
  I_valid_at (S n) P → I_valid_at n P.
Proof.
destruct P as [ P H ]; apply H.
Qed.

End IProp.

Include IProp.

Fixpoint IRel (l : list Type) : Type :=
  match l with
  | nil    => IProp
  | A :: l => A → IRel l
  end.

Definition IRel_x {A : Type} (P : A → list Type) : Type :=
  ∀ x : A, IRel (P x).

Definition I_valid (P : IProp) := ∀ n, I_valid_at n P.

Notation "n ⊨ P" := (I_valid_at n P) (at level 98, no associativity).
Notation "⊨ P" := (I_valid P) (at level 98, no associativity).

Lemma I_valid_monotone (P : IProp) (n m : nat) :
  n ≤ m → (m ⊨ P) → (n ⊨ P).
Proof.
induction 1; trivial.
intro; apply IHle; apply I_valid_monotone_S; assumption.
Qed.

(* ========================================================================= *)
(* Embeding Prop *)

Definition I_Prop (P : Prop) : IProp := mk_IProp (λ _, P) (λ _ H, H).

Notation "( P )ᵢ" := (I_Prop P).

Lemma I_Prop_intro (P : Prop) n : P → (n ⊨ (P)ᵢ).
Proof.
intro H; apply I_valid_intro; assumption.
Qed.

Lemma I_Prop_elim (P : Prop) n : (n ⊨ (P)ᵢ) → P.
Proof.
intro H; apply I_valid_elim in H; apply H.
Qed.
