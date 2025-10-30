import MyLean.MyNat.p9_WellOrder

set_option linter.unusedVariables false

namespace MyNat

def divAux : MyNat → MyNat → MyNat → MyNat
  | acc, m, n =>
    if nz : n = zero then
      zero
    else if mz : m = zero then
      acc.pred
    else if mn : m = n then
      acc.succ
    else
      divAux acc.succ (m.sub n) n
termination_by _ m => m

decreasing_by
  clear mn
  cases m with
  | zero =>
    contradiction
  | succ m =>
    clear mz
    have sizeOf_succ (a : MyNat) :
    sizeOf a < sizeOf a.succ := by
      rw [succ.sizeOf_spec, Nat.add_comm]
      exact Nat.lt_add_one (n := sizeOf a)
    have : ∀ a b : MyNat, sizeOf (b.sub a) ≤ sizeOf b := by
      intro a
      induction a with
      | zero =>
        intro b; rw [sub_zero]
        exact Nat.le_refl (n := sizeOf b)
      | succ a ih =>
        intro b
        cases b with
        | zero =>
          rw [zero_sub]
          apply Nat.le_refl
        | succ b =>
          rw [sub]
          specialize ih b
          apply Nat.le_of_lt
          apply Nat.lt_of_le_of_lt ih
          exact sizeOf_succ b
    cases n with
    | zero => contradiction
    | succ n =>
      clear nz
      rw [sub]
      apply Nat.lt_of_le_of_lt (m := sizeOf m)
      · exact this n m
      rw [succ.sizeOf_spec, Nat.add_comm]
      exact Nat.lt_add_one (n := sizeOf m)

def div (m n : MyNat) := divAux zero m n

theorem dvd_zero {n : MyNat} :
n.dvd zero := by
  use zero
  rw [mul_zero]

theorem zero_dvd {n : MyNat} :
zero.dvd n ↔ n = zero := by
  constructor
  · intro h
    contrapose h
    intro h2
    rw [ne, ne_zero_eq_succ] at h
    rw [h] at h2
    rcases h2 with ⟨c, hc⟩
    rw [zero_mul] at hc
    exact zero_ne_succ hc
  intro h
  rw [h]
  use zero
  rw [zero_mul]

theorem dvd_one {n : MyNat} :
n.dvd one ↔ n = one := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    rw [mul_eq_one] at h
    exact h.1
  intro h
  use one
  rw [h, mul_one]

theorem div_zero (n : MyNat) : n.div zero = zero := by
  rw [div, divAux]
  simp only [↓reduceDIte]

theorem zero_div (n : MyNat) : zero.div n = zero := by
  rw [div, divAux]
  cases n with
  | zero =>
    simp only [↓reduceDIte]
  | succ n =>
    rw [pred]
    simp only [reduceCtorEq, ↓reduceDIte]

theorem div_self (a : MyNat) (az : a ≠ zero) :
a.div a = one := by
  rw [div, divAux]
  cases a with
  | zero => contradiction
  | succ a =>
    clear az
    simp only [reduceCtorEq, ↓reduceDIte]
    rw [one]

theorem divAux_gt (acc m n : MyNat) (mn : m.lt n)
(mz : m ≠ zero) : divAux acc m n = acc := by
  have nz := ne_zero_of_lt (m := m) (n := n) mn
  rw [lt_iff_le_and_ne] at mn
  rcases mn with ⟨mn1, mn2⟩
  rw [← sub_eq_zero_iff_le] at mn1
  rw [divAux]
  simp only [nz, ↓reduceDIte, mz, mn2, mn1]
  rw [divAux]
  simp? [nz, pred]

theorem div_gt (m n : MyNat) (mn : m.lt n) :
m.div n = zero := by
  have nz := ne_zero_of_lt (m := m) (n := n) mn
  rw [div]
  cases m with
  | zero =>
    rw [divAux]
    simp only [nz, ↓reduceDIte, pred]
  | succ m =>
    apply divAux_gt
    · exact mn
    exact succ_ne_zero

theorem divAux_reduce1 (m n : MyNat) (nz : n ≠ zero) :
∀ acc : MyNat, divAux acc.succ.succ m n =
(divAux acc.succ m n).succ := by
  set P : MyNat → Prop := fun x =>
    ∀ acc : MyNat, acc.succ.succ.divAux x n =
    (acc.succ.divAux x n).succ with P_def
  have ih : ∀ a, (∀ b, b.lt a → P b) → P a := by
    intro a hb
    rw [P_def]
    simp only
    rcases (lt_trichotomy (m := a) (n := n)) with h | h | h
    · intro acc
      cases a with
      | zero =>
        rw [divAux]
        nth_rewrite 2 [divAux]
        simp only [nz, ↓reduceDIte, pred]
      | succ a =>
        have h1 := succ_ne_zero (a := a)
        have h2 := divAux_gt acc.succ.succ a.succ n h h1
        rw [h2]
        have h3 := divAux_gt acc.succ a.succ n h h1
        rw [h3]
    · rw [h]
      intro acc
      rw [divAux]
      nth_rewrite 2 [divAux]
      simp only [nz, ↓reduceDIte]
    intro acc
    cases a with
    | zero =>
      rw [divAux]
      nth_rewrite 2 [divAux]
      simp only [nz, ↓reduceDIte, pred]
    | succ a =>
      specialize hb (a.succ.sub n)
      have h1 : (a.succ.sub n).lt a.succ := by
        rw [lt_iff_succ_le, succ_le_succ] at h
        rw [ne_zero_eq_succ] at nz
        rw [nz, succ_sub_succ]
        apply lt_of_le_of_lt (b := a)
        · exact self_sub_le_self (m := a) (n := n.pred)
        exact lt_succ_self
      have h2 := hb h1
      rw [P_def] at h2
      specialize h2 acc.succ
      rw [divAux]
      simp? [nz]
      have h3 : a.succ ≠ n := by
        rw [lt_iff_le_and_ne] at h
        symm; exact h.2
      simp only [h3, ↓reduceIte]
      rw [h2, succ_inj]
      symm
      rw [divAux]
      simp only [nz, ↓reduceDIte, reduceCtorEq, h3]
  have := strong_induction (P := P) ih
  rw [P_def] at this
  exact this m

theorem divAux_reduce2 (m n acc : MyNat)
(mz : m ≠ zero) (nz : n ≠ zero) :
divAux acc.succ m n = (divAux acc m n).succ := by
  rw [divAux]
  nth_rewrite 2 [divAux]
  simp only [nz, ↓reduceDIte, mz, dite_eq_ite]
  by_cases mn : m = n
  · simp only [mn, ↓reduceIte]
  simp only [mn, ↓reduceIte]
  exact divAux_reduce1 (m.sub n) n nz acc

theorem add_div_right_eq_div_succ
(n : MyNat) (nz : n ≠ zero) :
∀ m : MyNat, (m.add n).div n = (m.div n).succ := by
  set P : MyNat → Prop :=
    fun x => (x.add n).div n = (x.div n).succ with P_def
  have ih : ∀ m, (∀ k, k.lt m → P k) → P m := by
    intro m hk
    rw [P_def]
    simp only
    have h1 : m.add n ≠ zero := by
      intro h
      rw [add_eq_zero] at h
      exact nz h.2
    rw [div, divAux]
    simp? [nz, h1]
    cases m with
    | zero =>
      rw [zero_add]
      simp only [↓reduceIte]
      rw [succ_inj, zero_div]
    | succ m =>
      have h2 : m.succ.add n ≠ n := by
        intro h2
        rw [add_eq_right] at h2
        exact succ_ne_zero h2
      simp only [h2, ↓reduceIte]
      rw [add_sub_cancel_right]
      apply divAux_reduce2
      exact succ_ne_zero
      exact nz
  have := strong_induction (P := P) ih
  intro m
  specialize this m
  rw [P_def] at this
  exact this

theorem div_one (a : MyNat) : a.div one = a := by
  induction a with
  | zero =>
    apply div_gt; use zero; rw [zero_add, one]
  | succ a ih =>
    rw [← add_one, add_div_right_eq_div_succ]
    · rw [ih, add_one]
    rw [one]
    exact succ_ne_zero

theorem mul_div_right_cancel (a b : MyNat) (az : a ≠ zero) :
(a.mul b).div a = b := by
  cases a with
  | zero => contradiction
  | succ a =>
    induction b with
    | zero =>
      rw [mul_zero, zero_div]
    | succ b ih =>
      rw [mul_succ, add_div_right_eq_div_succ]
      · rw [ih]
      exact succ_ne_zero

end MyNat
