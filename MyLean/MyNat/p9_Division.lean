import MyLean.MyNat.p8_Powers

namespace MyNat

theorem div_zero {n : MyNat} :
n.dvd zero := by
  use zero
  rw [mul_zero]

theorem zero_div {n : MyNat} :
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

theorem div_one {n : MyNat} :
n.dvd one ↔ n = one := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    rw [mul_eq_one] at h
    exact h.1
  intro h
  use one
  rw [h, mul_one]

theorem floor_div {m n : MyNat} (mz : m ≠ zero) :
∃ c : MyNat, (m.mul c).le n ∧ n.lt (m.mul c.succ) := by
  have mz1 := mz
  have mz2 := mz
  clear mz
  rw [ne_zero_eq_succ] at mz2
  induction n with
  | zero =>
    use zero
    constructor
    · rw [mul_zero]
      exact zero_le
    rw [mul_succ, mul_zero, zero_add, lt_iff_succ_le, mz2,
        succ_le_succ]
    exact zero_le
  | succ n ih =>
    rcases ih with ⟨c, eq1, eq2⟩
    rcases eq1 with ⟨d, eq1⟩
    by_cases eq4 : d = m.pred
    · rw [eq4] at eq1
      use c.succ
      constructor
      · rw [mul_succ]
        nth_rewrite 2 [mz2]
        rw [add_succ, eq1]
        exact le_self
      rw [mul_succ]
      nth_rewrite 2 [mz2]
      rw [add_succ, succ_lt_succ, lt_iff_succ_le, mul_succ,
          add_assoc, add_comm (a := m), ← add_assoc]
      nth_rewrite 3 [mz2]
      rw [add_succ, succ_le_succ, eq1]
      use m.pred
    use c
    constructor
    · use d.succ
      rw [add_succ, eq1]
    rw [mul_succ]
    nth_rewrite 2 [mz2]
    rw [add_succ, succ_lt_succ]
    rw [lt_iff_not_ge]
    contrapose! eq4
    rw [ge, eq1, add_le_add_left_cancel] at eq4
    rw [eq1, mul_succ, add_lt_add_left_cancel,
        lt_iff_succ_le] at eq2
    rw [← succ_le_succ, ← mz2] at eq4
    have eq5 := le_antisymm eq4 eq2
    rw [eq5, pred]

end MyNat
