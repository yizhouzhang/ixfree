Require Import Utf8.
Require Import List.
Require Import IxFree.Base IxFree.Relations IxFree.Connectives.
Require Import IxFree.UnaryFixpoint.

Fixpoint Prod (l : list Type) : Type :=
  match l with
  | nil    => unit
  | A :: l => (A * Prod l)%type
  end.

Fixpoint IRel_curry (l : list Type) : IRel1 (Prod l) → IRel l :=
  match l return IRel1 (Prod l) → IRel l with
  | nil    => λ R, R tt
  | A :: l => λ R x, IRel_curry l (λ y, R (x, y))
  end.

Fixpoint IRel_uncurry (l : list Type) : IRel l → IRel1 (Prod l) :=
  match l return IRel l → IRel1 (Prod l) with
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

Lemma IRel_curry_equiv (l : list Type) (R₁ R₂ : IRel1 (Prod l)) :
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

Lemma IRel_uncurry_curry_id (l : list Type) (R : IRel1 (Prod l)) :
  ∀ n x, (n ⊨ IRel_uncurry l (IRel_curry l R) x) <-> (n ⊨ R x).
Proof.
induction l; intros n x; simpl.
+ destruct x; split; auto.
+ destruct x as [ x y ]; simpl.
  apply (IHl (λ z, R (x, z))).
Qed.