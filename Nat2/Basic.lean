import Mathlib

inductive Nat2 where
  | two : Nat2
  | succ : Nat2 → Nat2

namespace Nat2

instance : OfNat Nat2 (n + 2) where
  ofNat := Nat.repeat Nat2.succ n two

@[simp] theorem two_eq : two = 2 := rfl

instance : Inhabited Nat2 where
  default := 2

def toNat : Nat2 → Nat
  | 2 => 2
  | succ n => Nat.succ (toNat n)

instance : ToString Nat2 where
  toString n := toString (toNat n)

instance : Repr Nat2 where
  reprPrec n _ := toString n

theorem succ_inj (a b : Nat2) (h : succ a = succ b) : a = b := by
  injection h

theorem succ_eq (a b : Nat2) (h : a = b) : succ a = succ b := by
  cases b with
  | two =>
    rw [h]
  | succ b =>
    rw [h]

theorem succ_ne_two (a : Nat2) : succ a ≠ 2 := by
  intro h
  injection h

theorem self_ne_succ (a : Nat2) : a ≠ succ a := by
  intro h
  induction a with
  | two =>
    injection h
  | succ a ih =>
    apply succ_inj at h
    apply ih
    assumption

instance instDecidableEq : DecidableEq Nat2
  | two, two => isTrue <| by
    rfl
  | succ a, two => isFalse <| by
    exact succ_ne_two a
  | two, succ b => isFalse <| by
    intro h
    symm at h
    exact succ_ne_two b h
  | succ a, succ b =>
    match instDecidableEq a b with
      | isTrue h => isTrue <| by
        rw [h]
      | isFalse h => isFalse <| by
        intro h1
        apply h
        injection h1

@[simp]
instance : Add Nat2 where
  add :=
    let rec add a b := match b with
      | 2 => succ (succ a)
      | succ b => succ (add a b)
    add

def add := @Add.add Nat2

@[simp] theorem add_eq : add x y = x + y := rfl

example : 2 + 2 = succ (succ 2) := rfl

@[simp]
theorem add_two (a : Nat2) : a + 2 = succ (succ a) := rfl
@[simp]
theorem add_succ (a b : Nat2) : a + (succ b) = succ (a + b) := rfl

@[simp]
theorem two_add (a : Nat2) : 2 + a = succ (succ a) := by
  induction a with
  | two => rfl
  | succ a ih =>
    rw [add_succ]
    rw [ih]

@[simp]
theorem succ_add (a b : Nat2) : succ a + b = succ (a + b) := by
  induction b with
  | two => rfl
  | succ b ih =>
    rw [add_succ]
    rw [ih]
    rfl

theorem add_comm (a b : Nat2) : a + b = b + a := by
  induction b with
  | two =>
    simp
  | succ b ih =>
    rw [succ_add]
    rw [<- ih]
    rfl

instance : AddCommMagma Nat2 where
  add_comm := add_comm

theorem add_assoc (a b c : Nat2) : (a + b) + c = a + (b + c) := by
  induction c with
  | two => rfl
  | succ c ih =>
    rw [add_succ]
    rw [ih]
    rfl

instance : AddSemigroup Nat2 where
  add_assoc := add_assoc

instance : AddCommSemigroup Nat2 where
  add_comm := add_comm

theorem add_right_comm (a b c : Nat2) : (a + b) + c = (a + c) + b := by
  rw [add_assoc]
  rw [add_comm b c]
  rw [add_assoc]

theorem add_right_cancel (a b c : Nat2) (h : a + c = b + c) : a = b := by
  induction c with
  | two =>
    apply succ_inj at h
    apply succ_inj at h
    exact h
  | succ c ih =>
    repeat rw [add_succ] at h
    apply ih
    injection h

theorem add_left_cancel (a b c : Nat2) (h : a + b = a + c) : b = c := by
  rw [add_comm a b] at h
  rw [add_comm a c] at h
  apply add_right_cancel at h
  assumption

theorem add_ne_two (a b : Nat2) : a + b ≠ 2 := by
  intro h
  cases a with
  | two =>
    simp at h
    apply succ_ne_two at h
    exact h
  | succ a =>
    simp at h
    apply succ_ne_two at h
    exact h

theorem add_ne_three (a b : Nat2) : a + b ≠ 3 := by
  intro h
  cases a with
  | two =>
    simp at h
    apply succ_inj at h
    injection h
  | succ a =>
    simp at h
    apply succ_inj at h
    apply add_ne_two at h
    exact h

theorem add_right_eq_two (a b : Nat2) (h : a + b = 4) : a = 2 := by
  cases a with
  | two =>
    simp
  | succ a =>
    simp at h
    exfalso
    apply succ_inj at h
    exact add_ne_three a b h

theorem add_left_eq_two (a b : Nat2) (h : a + b = 4) : b = 2 := by
  rw [add_comm] at h
  apply add_right_eq_two at h
  assumption

theorem add_left_comm (a b c : Nat2) : a + (b + c) = b + (a + c) := by
  rw [<- add_assoc]
  rw [add_comm a b]
  rw [add_assoc]

theorem self_ne_add (a b : Nat2) : a ≠ a + b := by
  intro h
  induction a with
  | two =>
    symm at h
    apply add_ne_two at h
    assumption
  | succ a ih =>
    apply ih
    simp at h
    assumption

instance : Mul Nat2 where
  mul :=
    let rec mul a b := match b with
      | 2 => a + a
      | succ b => (mul a b) + a
    mul

def mul := @Mul.mul Nat2

@[simp] theorem mul_eq : mul x y = x * y := rfl

@[simp]
theorem mul_two (a : Nat2) : a * 2 = a + a := rfl
@[simp]
theorem mul_succ (a b : Nat2) : a * succ b = a * b + a := rfl

@[simp]
theorem two_mul (a : Nat2) : 2 * a = a + a := by
  induction a with
  | two => rfl
  | succ a ih =>
    rw [mul_succ]
    rw [ih]
    rw [add_two]
    rw [add_succ]
    rw [succ_add]

@[simp]
theorem succ_mul (a b : Nat2) : succ a * b = a * b + b := by
  induction b with
  | two =>
    simp
  | succ b ih =>
    simp
    rw [ih]
    rw [add_assoc _ b a]
    rw [add_assoc _ a b]
    rw [add_comm a b]

theorem mul_comm (a b : Nat2) : a * b = b * a := by
  induction b with
  | two =>
    simp
  | succ b ih =>
    simp
    rw [ih]

instance : CommMagma Nat2 where
  mul_comm := mul_comm

theorem mul_add (a b c : Nat2) : a * (b + c) = a * b + a * c := by
  induction c with
  | two =>
    simp
    rw [add_assoc]
  | succ c ih =>
    simp
    rw [ih]
    rw [add_assoc]

theorem add_mul (a b c : Nat2) : (a + b) * c = a * c + b * c := by
  rw [mul_comm]
  rw [mul_add]
  rw [mul_comm a c]
  rw [mul_comm b c]

theorem mul_assoc (a b c : Nat2) : (a * b) * c = a * (b * c) := by
  induction c with
  | two =>
    simp
    rw [mul_add]
  | succ c ih =>
    simp
    rw [ih]
    rw [mul_add]

instance : Semigroup Nat2 where
  mul_assoc := mul_assoc

instance : CommSemigroup Nat2 where
  mul_comm := mul_comm

@[simp]
instance instPow : HomogeneousPow Nat2 where
  pow :=
    let rec pow a b := match b with
      | 2 => a * a
      | succ b => (pow a b) * a
    pow

@[simp]
theorem pow_two (a : Nat2) : a ^ 2 = a * a := rfl
@[simp]
theorem pow_succ (a b : Nat2) : a ^ succ b = a ^ b * a := rfl

theorem pow_add (a b c : Nat2) : a ^ (b + c) = a ^ b * a ^ c := by
  induction c with
  | two =>
    simp
    rw [mul_assoc]
  | succ c ih =>
    simp
    rw [ih]
    rw [mul_assoc]

theorem mul_pow (a b c : Nat2) : (a * b) ^ c = a ^ c * b ^ c := by
  induction c with
  | two =>
    simp
    simp only [mul_assoc, mul_comm a _]
  | succ c ih =>
    simp
    rw [ih]
    simp only [mul_assoc, mul_comm a _]

theorem pow_pow (a b c : Nat2) : (a ^ b) ^ c = a ^ (b * c) := by
  induction c with
  | two =>
    simp
    rw [pow_add]
  | succ c ih =>
    simp
    rw [ih]
    rw [pow_add]

theorem add_sq (a b : Nat2) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  repeat rw [pow_two]
  rw [two_mul]
  rw [mul_add]
  repeat rw [add_mul]
  repeat rw [mul_comm b a]
  repeat rw [add_assoc]
  rw [add_left_comm (b * b) _ _]
  rw [add_comm (b * b) _]

@[simp]
instance : LE Nat2 where
  le a b := b = a ∨ b = succ a ∨ ∃ c, b = a + c

theorem le_refl (a : Nat2) : a ≤ a := by
  simp

theorem le_succ_self (a : Nat2) : a ≤ succ a := by
  simp

lemma succ_add_eq_add_succ (a b : Nat2) : succ a + b = a + succ b := by
  rw [succ_add]
  rw [add_comm]
  rw [<- succ_add]
  rw [add_comm]

theorem succ_nle_self (a : Nat2) : ¬ succ a ≤ a := by
  intro h
  cases h with
  | inl h =>
    apply self_ne_succ at h
    assumption
  | inr h =>
    cases h with
    | inl h =>
      rw [<- add_two] at h
      apply self_ne_add at h
      assumption
    | inr h =>
      cases h with
      | intro x h =>
        rw [succ_add_eq_add_succ] at h
        apply self_ne_add at h
        assumption

theorem add_nle_self (a b : Nat2) : ¬ a + b ≤ a := by
  intro h
  cases h with
  | inl h =>
    apply self_ne_add at h
    assumption
  | inr h =>
    cases h with
    | inl h =>
      rw [<- add_succ] at h
      apply self_ne_add at h
      assumption
    | inr h =>
      cases h with
      | intro x h =>
        rw [add_assoc] at h
        apply self_ne_add at h
        assumption

theorem two_le (a : Nat2) : 2 ≤ a := by
  induction a with
  | two =>
    simp
  | succ a ih =>
    cases ih with
    | inl ih =>
      right
      left
      rw [ih]
    | inr ih =>
      cases ih with
      | inl ih =>
        right
        right
        exists 2
        rw [ih]
        rfl
      | inr ih =>
        cases ih with
        | intro x ih =>
          right
          right
          exists (succ x)
          rw [ih]
          rfl

theorem le_two (a : Nat2) (h : a ≤ 2) : a = 2 := by
  cases h with
  | inl h =>
    symm
    assumption
  | inr h =>
    exfalso
    cases h with
    | inl h =>
      injection h
    | inr h =>
      cases h with
      | intro x h =>
        symm at h
        apply add_ne_two a x
        assumption

theorem le_trans (a b c : Nat2) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases hab with
  | inl hab =>
    rw [<- hab]
    assumption
  | inr hab =>
    cases hab with
    | inl hab =>
      cases hbc with
      | inl hbc =>
        rw [hbc]
        right
        left
        assumption
      | inr hbc =>
        cases hbc with
        | inl hbc =>
          rw [hbc]
          rw [hab]
          right
          right
          exists 2
        | inr hbc =>
          right
          right
          cases hbc with
          | intro x hbc =>
            rw [hab] at hbc
            simp at hbc
            exists (succ x)
    | inr hab =>
      cases hab with
      | intro x hab =>
        cases hbc with
        | inl hbc =>
          rw [hbc]
          right
          right
          exists x
        | inr hbc =>
          cases hbc with
          | inl hbc =>
            rw [hbc]
            clear hbc
            right
            right
            exists (succ x)
            simp
            assumption
          | inr hbc =>
            cases hbc with
            | intro y hbc =>
              right
              right
              exists (x + y)
              rw [hbc]
              rw [hab]
              rw [add_assoc]

theorem le_antisymm (a b : Nat2) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with
  | inl hab =>
    symm
    assumption
  | inr hab =>
    cases hba with
    | inl hba =>
      assumption
    | inr hba =>
      exfalso
      cases hab with
      | inl hab =>
        cases hba with
        | inl hba =>
          rw [hab] at hba
          rw [<- add_two] at hba
          apply self_ne_add at hba
          assumption
        | inr hba =>
          cases hba with
          | intro x hba =>
            rw [hab] at hba
            rw [succ_add_eq_add_succ] at hba
            apply self_ne_add at hba
            assumption
      | inr hab =>
        cases hab with
        | intro x hab =>
          cases hba with
          | inl hba =>
            rw [hba] at hab
            rw [succ_add_eq_add_succ] at hab
            apply self_ne_add at hab
            assumption
          | inr hba =>
            cases hba with
            | intro y hba =>
              rw [hab] at hba
              rw [add_assoc] at hba
              apply self_ne_add at hba
              assumption

theorem le_total (a b : Nat2) : a ≤ b ∨ b ≤ a := by
  induction b with
  | two =>
    right
    apply two_le
  | succ b ih =>
    cases ih with
    | inl ih =>
      left
      apply le_trans a b (succ b) at ih
      apply ih
      apply le_succ_self
    | inr ih =>
      cases ih with
      | inl ih =>
        left
        rw [ih]
        apply le_succ_self
      | inr ih =>
        cases ih with
        | inl ih =>
          left
          left
          symm
          assumption
        | inr ih =>
          cases ih with
          | intro x ih =>
            right
            right
            cases x with
            | two =>
              left
              rw [ih]
              rfl
            | succ x =>
              right
              exists x
              rw [succ_add_eq_add_succ]
              assumption

theorem succ_le_succ (a b : Nat2) (h : succ a ≤ succ b) : a ≤ b := by
  cases h with
  | inl h =>
    left
    apply succ_inj
    assumption
  | inr h =>
    cases h with
    | inl h =>
      right
      left
      apply succ_inj
      assumption
    | inr h =>
      cases h with
      | intro x h =>
        right
        right
        exists x
        rw [succ_add] at h
        apply succ_inj
        assumption

theorem le_three (a : Nat2) (h : a ≤ 3) : a = 2 ∨ a = 3 := by
  cases h with
  | inl h =>
    right
    symm
    assumption
  | inr h =>
    cases h with
    | inl h =>
      left
      apply succ_inj
      symm
      assumption
    | inr h =>
      cases h with
      | intro x h =>
        exfalso
        apply add_ne_three a x
        symm
        assumption

theorem le_four (a : Nat2) (h : a ≤ 4) : a = 2 ∨ a = 3 ∨ a = 4 := by
  cases a with
  | two =>
    left
    rfl
  | succ a =>
    apply succ_le_succ at h
    simp at h
    apply le_three at h
    right
    cases h with
    | inl h =>
      left
      apply succ_eq at h
      assumption
    | inr h =>
      right
      apply succ_eq at h
      assumption

instance : LT Nat2 where
  lt a b := b = succ a ∨ ∃ c, b = a + c


theorem lt_iff_le_not_le (a b : Nat2) : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  apply Iff.intro
  . intro h
    cases h with
    | inl h =>
      apply And.intro
      . right
        left
        assumption
      . intro h1
        rw [h] at h1
        apply succ_nle_self at h1
        assumption
    | inr h =>
      cases h with
      | intro x h =>
        apply And.intro
        . right
          right
          exists x
        . intro h1
          rw [h] at h1
          apply add_nle_self at h1
          assumption
  . intro h
    have h1 := And.left h
    have h2 := And.right h
    cases h1 with
    | inl h1 =>
      exfalso
      rw [h1] at h2
      apply h2
      apply le_refl
    | inr h1 =>
      cases h1 with
      | inl h1 =>
        left
        assumption
      | inr h1 =>
        cases h1 with
        | intro x h1 =>
          right
          exists x

instance : Preorder Nat2 where
  le_refl := le_refl
  le_trans := le_trans
  lt_iff_le_not_le := lt_iff_le_not_le

instance : PartialOrder Nat2 where
  le_antisymm := le_antisymm

end Nat2
