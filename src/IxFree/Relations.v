Require Import Utf8.
Require Import List.
Require Import IxFree.Base.
Require Import IxFree.Connectives.

Fixpoint I_rel_equiv (l : list Type) : IRel l → IRel l → IProp :=
  match l return IRel l → IRel l → IProp with
  | nil    => λ R₁ R₂, R₁ ⇔ R₂
  | A :: l => λ R₁ R₂, ∀ᵢ x, I_rel_equiv l (R₁ x) (R₂ x)
  end.

Notation "R ≈ᵢ S" := (I_rel_equiv _ R S) (at level 70).

Fixpoint subrel (l : list Type) : IRel l → IRel l → Prop :=
  match l return IRel l → IRel l → Prop with
  | nil    => λ R₁ R₂, ∀ n, (n ⊨ R₁) → (n ⊨ R₂)
  | A :: l => λ R₁ R₂, ∀ x, subrel l (R₁ x) (R₂ x)
  end.

Notation "R ≾ᵣ S" := (subrel _ R S) (at level 70).


Definition I_rel_x_equiv {A : Type} (P : A → list Type) (R₁ R₂ : IRel_x P) : IProp :=
  ∀ᵢ x, I_rel_equiv (P x) (R₁ x) (R₂ x).

Definition subrel_x {A : Type} (P : A → list Type) (R₁ R₂ : IRel_x P) : Prop :=
  ∀ x, subrel (P x) (R₁ x) (R₂ x).


Definition I_rel_xx_equiv {A B : Type} (P : A → B → list Type) (R₁ R₂ : IRel_xx P) : IProp :=
  ∀ᵢ x y, I_rel_equiv (P x y) (R₁ x y) (R₂ x y).

Definition subrel_xx {A B : Type} (P : A → B → list Type) (R₁ R₂ : IRel_xx P) : Prop :=
  ∀ x y, subrel (P x y) (R₁ x y) (R₂ x y).