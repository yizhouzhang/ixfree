Require Import Utf8.
Require Import IxFree.Base IxFree.UnaryFixpoint.

Require Import Arith.
Require Import Omega.

Definition IRel_2 {A : Type} (P : A → Type) := ∀ x, IRel_1 (P x).
Definition True_2 {A : Type} {P : A → Type} : IRel_2 P := λ _, True_1.

Program Definition contractive_2 {A : Type} {P : A → Type} (f : IRel_2 P → IRel_2 P) :=
  ∀ (n : nat) (R₁ R₂ : IRel_2 P),
  (∀ k, k < n → ∀ x y, (k ⊨ R₁ x y) <-> (k ⊨ R₂ x y)) →
  ∀ x y, (n ⊨ f R₁ x y) <-> (n ⊨ f R₂ x y).

Fixpoint pow_IRel_2 {A : Type} {P : A → Type}
    (f : IRel_2 P → IRel_2 P) (n : nat) (R₀ : IRel_2 P) :=
  match n with
  | 0   => R₀
  | S n => f (pow_IRel_2 f n R₀)
  end.

Lemma pow_IRel_2_limit {A : Type} {P : A → Type} (f : IRel_2 P → IRel_2 P) :
  contractive_2 f → ∀ k n m : nat, k ≤ n → k ≤ m → ∀ x y,
  ((k ⊨ f (pow_IRel_2 f n True_2) x y) <->
   (k ⊨ f (pow_IRel_2 f m True_2) x y)).
Proof.
  intro Hcon.
  apply (well_founded_ind lt_wf (λ k, ∀ n m, k ≤ n → k ≤ m → ∀ x y, (_ : Prop))).
  intros k HI n m H₁ H₂ x y ; destruct k.
  + apply Hcon ; intros ; omega.
  + apply Hcon ; intros l Hl.
    destruct n ; [ exfalso ; omega | ].
    destruct m ; [ exfalso ; omega | ].
    apply HI ; omega.
Qed.

Definition I_fix_2_func {A : Type} {P : A → Type} (f : IRel_2 P → IRel_2 P) :
    ∀ x, P x → nat → Prop :=
  λ x y n, n ⊨ f (pow_IRel_2 f n True_2) x y.

Lemma I_fix_2_func_monotone {A : Type} {P : A → Type} (f : IRel_2 P → IRel_2 P) :
  contractive_2 f → ∀ x y, monotone (I_fix_2_func f x y).
Proof.
  intros Hcon x y n ; induction n.
  + unfold I_fix_2_func ; simpl.
    intro H₁; apply (Hcon 0 True_2 (f True_2)).
    - intros k H; inversion H.
    - apply I_valid_monotone_S; assumption.
  + unfold I_fix_2_func.
    intro H₁; apply (Hcon (S n) 
        (pow_IRel_2 f (S n) True_2) (pow_IRel_2 f (S (S n)) True_2)).
    - intros; apply pow_IRel_2_limit; trivial; omega.
    - apply I_valid_monotone_S; assumption.
Qed.

Definition I_fix_2 {A : Type} {P : A → Type} (f : IRel_2 P → IRel_2 P) (p : contractive_2 f) : 
  IRel_2 P :=
  λ x y, mk_IProp (I_fix_2_func f x y) (I_fix_2_func_monotone f p x y).

Lemma I_fix_2_is_fixpoint {A : Type} {P : A → Type}
  (f : IRel_2 P → IRel_2 P) (p : contractive_2 f) :
  ∀ x y n, (n ⊨ I_fix_2 f p x y) <-> (n ⊨ f (I_fix_2 f p) x y).
Proof.
  intros x y n; apply iff_trans with (B := (n ⊨ f (pow_IRel_2 f n True_2) x y)).
  { split; intro H; [ apply I_valid_elim in H | apply I_valid_intro ]; auto. }
  apply p; intros k Hle x' y'.
  destruct n; [ omega | ]; simpl.
  apply iff_trans with (B := (k ⊨ f (pow_IRel_2 f k True_2) x' y')).
  { apply pow_IRel_2_limit; trivial; omega. }
  split; intro H; [ apply I_valid_intro | apply I_valid_elim in H ]; auto.
Qed.

Lemma I_fix_2_unroll {A : Type} {P : A → Type}
  (f : IRel_2 P → IRel_2 P) (p : contractive_2 f) :
  ∀ x y n, (n ⊨ I_fix_2 f p x y) → (n ⊨ f (I_fix_2 f p) x y).
Proof.
apply I_fix_2_is_fixpoint.
Qed.

Lemma I_fix_2_roll {A : Type} {P : A → Type}
  (f : IRel_2 P → IRel_2 P) (p : contractive_2 f) :
  ∀ x y n, (n ⊨ f (I_fix_2 f p) x y) → (n ⊨ I_fix_2 f p x y).
Proof.
apply I_fix_2_is_fixpoint.
Qed.
