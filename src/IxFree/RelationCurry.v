Require Import Utf8.
Require Import List.
Require Import IxFree.Base IxFree.Relations IxFree.Connectives.
Require Import IxFree.UnaryFixpoint IxFree.BinaryFixpoint IxFree.TernaryFixpoint.

Fixpoint Prod (l : list Type) : Type :=
  match l with
  | nil    => unit
  | A :: l => (A * Prod l)%type
  end.

Fixpoint IRel_curry (l : list Type) : IRel_1 (Prod l) → IRel l :=
  match l return IRel_1 (Prod l) → IRel l with
  | nil    => λ R, R tt
  | A :: l => λ R x, IRel_curry l (λ y, R (x, y))
  end.

Fixpoint IRel_uncurry (l : list Type) : IRel l → IRel_1 (Prod l) :=
  match l return IRel l → IRel_1 (Prod l) with
  | nil    => λ R _, R
  | A :: l => λ R p, IRel_uncurry l (R (fst p)) (snd p)
  end.

Lemma IRel_uncurry_equiv (l : list Type) (R₁ R₂ : IRel l) :
  ⊨ R₁ ≈ᵢ R₂ ⇒ 
    I_rel_equiv (Prod l :: nil) (IRel_uncurry l R₁) (IRel_uncurry l R₂).
Proof.
induction l; intro n; simpl.
+ iintro; iintro; auto.
+ iintro H; iintro p; destruct p as [ x y ]; simpl.
  specialize (IHl (R₁ x) (R₂ x) n); ispecialize IHl.
  iapply H.
  iapply IHl.
Qed.

Lemma IRel_curry_equiv (l : list Type) (R₁ R₂ : IRel_1 (Prod l)) :
  ⊨ I_rel_equiv (Prod l :: nil) R₁ R₂ ⇒ IRel_curry l R₁ ≈ᵢ IRel_curry l R₂.
Proof.
induction l; intro n; simpl.
+ iintro H; iapply H.
+ iintro H; iintro x.
  specialize (IHl (λ y, R₁ (x, y)) (λ y, R₂ (x, y)) n).
  iapply IHl; simpl; iintro y; iapply H.
Qed.

Lemma IRel_uncurry_subrel (l : list Type) (R₁ R₂ : IRel l) :
  subrel (Prod l :: nil) (IRel_uncurry l R₁) (IRel_uncurry l R₂) → R₁ ≾ᵣ R₂.
Proof.
induction l; simpl.
+ intro H; apply H; constructor.
+ intros H x; apply IHl; simpl.
  intro y; apply (H (x, y)).
Qed.

Lemma IRel_uncurry_curry_id (l : list Type) (R : IRel_1 (Prod l)) :
  ∀ n x, (n ⊨ IRel_uncurry l (IRel_curry l R) x) <-> (n ⊨ R x).
Proof.
induction l; intros n x; simpl.
+ destruct x; split; auto.
+ destruct x as [ x y ]; simpl.
  apply (IHl (λ z, R (x, z))).
Qed.



Definition Prod_x {A : Type} (P : A → list Type) : A → Type :=
  λ x, Prod (P x).

Definition IRel_x_curry {A : Type} (P : A → list Type) : IRel_2 (Prod_x P) → IRel_x P :=
  λ R x, IRel_curry _ (R x).

Definition IRel_x_uncurry {A : Type} (P : A → list Type) : IRel_x P → IRel_2 (Prod_x P) :=
  λ R x y, IRel_uncurry _ (R x) y.

Lemma IRel_x_uncurry_equiv {A : Type} (P : A → list Type) (R₁ R₂ : IRel_x P) :
  ⊨ I_rel_x_equiv _ R₁ R₂ ⇒
    I_rel_x_equiv (λ x, Prod (P x) :: nil) (IRel_x_uncurry P R₁) (IRel_x_uncurry _ R₂).
Proof.
  intro n.
  iintro H.
  iintro x ; iintro y.
  unfold IRel_x_uncurry.
  specialize (IRel_uncurry_equiv (P x) (R₁ x) (R₂ x) n) as H'.
  iespecialize H.
  iapply (I_arrow_elim H' H).
Qed.

Lemma IRel_x_curry_equiv {A : Type} (P : A → list Type) (R₁ R₂ : IRel_2 (Prod_x P)) :
  ⊨ I_rel_x_equiv (λ x, Prod (P x) :: nil) R₁ R₂ ⇒ 
    I_rel_x_equiv _ (IRel_x_curry _ R₁) (IRel_x_curry _ R₂).
Proof.
  intro n.
  iintro H.
  iintro x.
  unfold IRel_x_curry.
  specialize (IRel_curry_equiv (P x) (R₁ x) (R₂ x) n) as H'.
  specialize (I_forall_elim H x) as H'' ; clear H ; rename H'' into H.
  apply (I_arrow_elim H' H).
Qed.

Lemma IRel_x_uncurry_subrel {A : Type} (P : A → list Type) (R₁ R₂ : IRel_x P) :
  subrel_x (λ x, Prod (P x) :: nil) (IRel_x_uncurry _ R₁) (IRel_x_uncurry _ R₂) →
  subrel_x _ R₁ R₂.
Proof.
  intro H.
  intro x.
  apply IRel_uncurry_subrel.
  apply H.
Qed.

Lemma IRel_x_uncurry_curry_id {A : Type} (P : A → list Type) (R : IRel_2 (Prod_x P)) :
  ∀ n x y, (n ⊨ IRel_x_uncurry _ (IRel_x_curry _ R) x y) ↔ (n ⊨ R x y).
Proof.
  intros n x.
  apply IRel_uncurry_curry_id.
Qed.



Definition Prod_xx {A B : Type} (P : A → B → list Type) : A → B → Type :=
  λ x, Prod_x (P x).

Definition IRel_xx_curry {A B : Type} (P : A → B → list Type) : IRel_3 (Prod_xx P) → IRel_xx P :=
  λ R x, IRel_x_curry _ (R x).

Definition IRel_xx_uncurry {A B : Type} (P : A → B → list Type) : IRel_xx P → IRel_3 (Prod_xx P) :=
  λ R x y, IRel_x_uncurry _ (R x) y.

Lemma IRel_xx_uncurry_equiv {A B : Type} (P : A → B → list Type) (R₁ R₂ : IRel_xx P) :
  ⊨ I_rel_xx_equiv _ R₁ R₂ ⇒
    I_rel_xx_equiv (λ x y, Prod (P x y) :: nil) (IRel_xx_uncurry _ R₁) (IRel_xx_uncurry _ R₂).
Proof.
  intro n.
  iintro H.
  iintro x ; iintro y.
  unfold IRel_xx_uncurry.
  specialize (IRel_x_uncurry_equiv (P x) (R₁ x) (R₂ x) n) as H'.
  specialize (I_forall_elim H x) as H'' ; clear H ; rename H'' into H.
  iapply (I_arrow_elim H' H).
Qed.

Lemma IRel_xx_curry_equiv {A B : Type} (P : A → B → list Type) (R₁ R₂ : IRel_3 (Prod_xx P)) :
  ⊨ I_rel_xx_equiv (λ x y, Prod (P x y) :: nil) R₁ R₂ ⇒ 
    I_rel_xx_equiv _ (IRel_xx_curry _ R₁) (IRel_xx_curry _ R₂).
Proof.
  intro n.
  iintro H.
  iintro x.
  unfold IRel_xx_curry.
  specialize (IRel_x_curry_equiv (P x) (R₁ x) (R₂ x) n) as H'.
  specialize (I_forall_elim H x) as H'' ; clear H ; rename H'' into H.
  apply (I_arrow_elim H' H).
Qed.

Lemma IRel_xx_uncurry_subrel {A B : Type} (P : A → B → list Type) (R₁ R₂ : IRel_xx P) :
  subrel_xx (λ x y, Prod (P x y) :: nil) (IRel_xx_uncurry _ R₁) (IRel_xx_uncurry _ R₂) →
  subrel_xx _ R₁ R₂.
Proof.
  intro H.
  intros x.
  apply IRel_x_uncurry_subrel.
  unfold subrel_x.
  apply H.
Qed.

Lemma IRel_xx_uncurry_curry_id {A B : Type} (P : A → B → list Type) (R : IRel_3 (Prod_xx P)) :
  ∀ n x y z, (n ⊨ IRel_xx_uncurry _ (IRel_xx_curry _ R) x y z) ↔ (n ⊨ R x y z).
Proof.
  intros n x.
  apply IRel_x_uncurry_curry_id.
Qed.