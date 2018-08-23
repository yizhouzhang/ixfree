Require Import Utf8.
Require Import IxFree.Base.

Require Import Arith.
Require Import Omega.

Definition IRel_1 (A : Type) := A → IProp.
Definition True_1 {A : Type} : IRel_1 A := λ _, (True)ᵢ.

Definition contractive_1 {A : Type} (f : IRel_1 A → IRel_1 A) :=
  ∀ (n : nat) (R₁ R₂ : A → IProp),
  (∀ k, k < n → ∀ x : A, (k ⊨ R₁ x) <-> (k ⊨ R₂ x)) →
  ∀ x : A, (n ⊨ f R₁ x) <-> (n ⊨ f R₂ x).

Fixpoint pow_IRel_1 {A : Type} 
    (f : IRel_1 A → IRel_1 A) (n : nat) (R₀ : IRel_1 A) :=
  match n with
  | 0   => R₀
  | S n => f (pow_IRel_1 f n R₀)
  end.

Lemma pow_IRel_1_limit {A : Type} (f : IRel_1 A → IRel_1 A) :
  contractive_1 f → ∀ k n m : nat, k ≤ n → k ≤ m → ∀ x,
  ((k ⊨ f (pow_IRel_1 f n True_1) x) <-> 
   (k ⊨ f (pow_IRel_1 f m True_1) x)).
Proof.
intro Hcon; 
apply (well_founded_ind lt_wf (λ k, ∀ n m, k ≤ n → k ≤ m → ∀ x, (_ : Prop))).
intros k HI n m H₁ H₂ x; destruct k.
+ apply Hcon; intros; omega.
+ apply Hcon; intros l Hl.
  destruct n; [ exfalso; omega | ].
  destruct m; [ exfalso; omega | ].
  apply HI; omega.
Qed.

Definition I_fix_1_func {A : Type} (f : IRel_1 A → IRel_1 A) : A → nat → Prop :=
  λ x n, n ⊨ f (pow_IRel_1 f n True_1) x.
Lemma I_fix_func_monotone {A : Type} (f : IRel_1 A → IRel_1 A) :
  contractive_1 f → ∀ x, monotone (I_fix_1_func f x).
Proof.
intros Hcon x n; induction n.
+ unfold I_fix_1_func; simpl.
  intro H₁; apply (Hcon 0 True_1 (f True_1)).
  - intros k H; inversion H.
  - apply I_valid_monotone_S; assumption.
+ unfold I_fix_1_func.
  intro H₁; apply (Hcon (S n) 
      (pow_IRel_1 f (S n) True_1) (pow_IRel_1 f (S (S n)) True_1)).
  - intros; apply pow_IRel_1_limit; trivial; omega.
  - apply I_valid_monotone_S; assumption.
Qed.

Definition I_fix_1 {A : Type} (f : IRel_1 A → IRel_1 A) (p : contractive_1 f) : 
  IRel_1 A :=
  λ x, mk_IProp (I_fix_1_func f x) (I_fix_func_monotone f p x).

Lemma I_fix_1_is_fixpoint {A : Type} 
  (f : IRel_1 A → IRel_1 A) (p : contractive_1 f) :
  ∀ x n, (n ⊨ I_fix_1 f p x) <-> (n ⊨ f (I_fix_1 f p) x).
Proof.
intros x n; apply iff_trans with (B := (n ⊨ f (pow_IRel_1 f n True_1) x)).
  split; intro H; [ apply I_valid_elim in H | apply I_valid_intro ]; auto.
apply p; intros k Hle y.
destruct n; [ omega | ]; simpl.
apply iff_trans with (B := (k ⊨ f (pow_IRel_1 f k True_1) y)).
  apply pow_IRel_1_limit; trivial; omega.
split; intro H; [ apply I_valid_intro | apply I_valid_elim in H ]; auto.
Qed.

Lemma I_fix_1_unroll {A : Type}
  (f : IRel_1 A → IRel_1 A) (p : contractive_1 f) :
  ∀ x n, (n ⊨ I_fix_1 f p x) → (n ⊨ f (I_fix_1 f p) x).
Proof.
apply I_fix_1_is_fixpoint.
Qed.

Lemma I_fix_1_roll {A : Type}
  (f : IRel_1 A → IRel_1 A) (p : contractive_1 f) :
  ∀ x n, (n ⊨ f (I_fix_1 f p) x) → (n ⊨ I_fix_1 f p x).
Proof.
apply I_fix_1_is_fixpoint.
Qed.
