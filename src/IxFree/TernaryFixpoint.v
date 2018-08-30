Require Import Utf8.
Require Import IxFree.Base IxFree.BinaryFixpoint.

Require Import Arith.
Require Import Omega.

Definition IRel_3 {A B : Type} (P : A → B → Type) := ∀ x, IRel_2 (P x).
Definition True_3 {A B : Type} {P : A → B → Type} : IRel_3 P := λ _, True_2.

Program Definition contractive_3 {A B : Type} {P : A → B → Type} (f : IRel_3 P → IRel_3 P) :=
  ∀ (n : nat) (R₁ R₂ : IRel_3 P),
  (∀ k, k < n → ∀ x y z, (k ⊨ R₁ x y z) <-> (k ⊨ R₂ x y z)) →
  ∀ x y z, (n ⊨ f R₁ x y z) <-> (n ⊨ f R₂ x y z).

Fixpoint pow_IRel_3 {A B : Type} {P : A → B → Type}
    (f : IRel_3 P → IRel_3 P) (n : nat) (R₀ : IRel_3 P) :=
  match n with
  | 0   => R₀
  | S n => f (pow_IRel_3 f n R₀)
  end.

Lemma pow_IRel_3_limit {A B : Type} {P : A → B → Type} (f : IRel_3 P → IRel_3 P) :
  contractive_3 f → ∀ k n m : nat, k ≤ n → k ≤ m → ∀ x y z,
  ((k ⊨ f (pow_IRel_3 f n True_3) x y z) <->
   (k ⊨ f (pow_IRel_3 f m True_3) x y z)).
Proof.
  intro Hcon.
  apply (well_founded_ind lt_wf (λ k, ∀ n m, k ≤ n → k ≤ m → ∀ x y z, (_ : Prop))).
  intros k HI n m H₁ H₂ x y z ; destruct k.
  + apply Hcon ; intros ; omega.
  + apply Hcon ; intros l Hl.
    destruct n ; [ exfalso ; omega | ].
    destruct m ; [ exfalso ; omega | ].
    apply HI ; omega.
Qed.

Definition I_fix_3_func {A B : Type} {P : A → B → Type} (f : IRel_3 P → IRel_3 P) :
    ∀ x y, P x y → nat → Prop :=
  λ x y z n, n ⊨ f (pow_IRel_3 f n True_3) x y z.

Lemma I_fix_3_func_monotone {A B : Type} {P : A → B → Type} (f : IRel_3 P → IRel_3 P) :
  contractive_3 f → ∀ x y z, monotone (I_fix_3_func f x y z).
Proof.
  intros Hcon x y z n ; induction n.
  + unfold I_fix_3_func ; simpl.
    intro H₁; apply (Hcon 0 True_3 (f True_3)).
    - intros k H; inversion H.
    - apply I_valid_monotone_S; assumption.
  + unfold I_fix_3_func.
    intro H₁; apply (Hcon (S n) 
        (pow_IRel_3 f (S n) True_3) (pow_IRel_3 f (S (S n)) True_3)).
    - intros; apply pow_IRel_3_limit; trivial; omega.
    - apply I_valid_monotone_S; assumption.
Qed.

Definition I_fix_3 {A B : Type} {P : A → B → Type} (f : IRel_3 P → IRel_3 P) (p : contractive_3 f) : 
  IRel_3 P :=
  λ x y z, mk_IProp (I_fix_3_func f x y z) (I_fix_3_func_monotone f p x y z).

Lemma I_fix_3_is_fixpoint {A B : Type} {P : A → B → Type}
  (f : IRel_3 P → IRel_3 P) (p : contractive_3 f) :
  ∀ x y z n, (n ⊨ I_fix_3 f p x y z) <-> (n ⊨ f (I_fix_3 f p) x y z).
Proof.
  intros x y z n; apply iff_trans with (B := (n ⊨ f (pow_IRel_3 f n True_3) x y z)).
  { split; intro H; [ apply I_valid_elim in H | apply I_valid_intro ]; auto. }
  apply p; intros k Hle x' y' z'.
  destruct n; [ omega | ]; simpl.
  apply iff_trans with (B := (k ⊨ f (pow_IRel_3 f k True_3) x' y' z')).
  { apply pow_IRel_3_limit; trivial; omega. }
  split; intro H; [ apply I_valid_intro | apply I_valid_elim in H ]; auto.
Qed.

Lemma I_fix_3_unroll {A B : Type} {P : A → B → Type}
  (f : IRel_3 P → IRel_3 P) (p : contractive_3 f) :
  ∀ x y z n, (n ⊨ I_fix_3 f p x y z) → (n ⊨ f (I_fix_3 f p) x y z).
Proof.
apply I_fix_3_is_fixpoint.
Qed.

Lemma I_fix_3_roll {A B : Type} {P : A → B → Type}
  (f : IRel_3 P → IRel_3 P) (p : contractive_3 f) :
  ∀ x y z n, (n ⊨ f (I_fix_3 f p) x y z) → (n ⊨ I_fix_3 f p x y z).
Proof.
apply I_fix_3_is_fixpoint.
Qed.