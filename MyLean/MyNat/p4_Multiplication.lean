import MyLean.MyNat.p3_Subtraction

namespace MyNat

theorem mul_zero {a : MyNat} : a.mul zero = zero := by
  rw [mul, iterate]

theorem mul_succ {a b : MyNat} :
a.mul b.succ = (a.mul b).add a := by
  rw [mul, iterate_out, ← mul]

theorem zero_mul {a : MyNat} : zero.mul a = zero := by
  induction a with
  | zero =>
    exact mul_zero
  | succ a ih =>
  rw [mul_succ, ih, add_zero]

theorem succ_mul {a b : MyNat} :
a.succ.mul b = (a.mul b).add b := by
  induction b with
  | zero =>
    rw [mul_zero, mul_zero, add_zero]
  | succ b ih =>
    rw [mul_succ, ih, mul_succ, add_succ, add_succ,
      add_assoc, add_comm (a := b), ← add_assoc]

theorem mul_one {a : MyNat} : a.mul one = a := by
  rw [one, mul_succ, mul_zero, zero_add]

theorem one_mul {a : MyNat} : one.mul a = a := by
  rw [one, succ_mul, zero_mul, zero_add]

theorem mul_comm {a b : MyNat} : a.mul b = b.mul a := by
  induction b with
  | zero =>
    rw [mul_zero, zero_mul]
  | succ b ih =>
    rw [mul_succ, ih, succ_mul]

theorem add_mul {a b c : MyNat} :
(a.add b).mul c = (a.mul c).add (b.mul c) := by
  induction c with
  | zero =>
    simp only [mul_zero, add_zero]
  | succ c ih =>
    rw [mul_succ, ih]
    simp only [mul_succ, add_comm, ← add_assoc]

theorem mul_add (a b c : MyNat) :
a.mul (b.add c) = (a.mul b).add (a.mul c) := by
  rw [mul_comm, add_mul]
  simp only [mul_comm]

theorem mul_assoc {a b c : MyNat} :
(a.mul b).mul c = a.mul (b.mul c) := by
  induction c with
  | zero =>
    rw [mul_zero, mul_zero, mul_zero]
  | succ c ih =>
    rw [mul_succ, ih, mul_succ, mul_add]

theorem mul_eq_zero {m n : MyNat} :
m.mul n = zero ↔ m = zero ∨ n = zero := by
  constructor
  · intro h
    by_cases nz : n = zero
    · right
      exact nz
    rw [ne, ne_zero_eq_succ] at nz
    left
    rw [nz, mul_succ] at h
    rw [add_eq_zero] at h
    exact h.2
  intro h
  rcases h with h | h
  · rw [h, zero_mul]
  rw [h, mul_zero]

theorem mul_eq_one_aux {m n : MyNat} :
m.mul n = one → m = one := by
  intro eq1
  by_cases eq2 : n = zero
  · rw [eq2, mul_zero, one] at eq1
    have := zero_ne_succ eq1
    contradiction
  by_cases eq3 : m = zero
  · rw [eq3, zero_mul, one] at eq1
    have := zero_ne_succ eq1
    contradiction
  rw [ne, ne_zero_eq_succ] at eq2
  rw [ne, ne_zero_eq_succ] at eq3
  rw [eq2, eq3, one, mul_succ, succ_mul, add_succ, succ_inj,
      add_eq_zero] at eq1
  rw [eq1.2] at eq3
  rw [eq3, one]

theorem mul_eq_one {m n : MyNat} :
m.mul n = one ↔ m = one ∧ n = one := by
  constructor
  · intro h
    have := mul_eq_one_aux h
    constructor
    · exact this
    rw [this, one_mul] at h
    exact h
  intro h
  rw [h.1, h.2, mul_one]

theorem mul_pred {m n : MyNat} :
m.mul n.pred = (m.mul n).sub m := by
  by_cases eq1 : n = zero
  · rw [eq1, pred, mul_zero, zero_sub]
  rw [ne, ne_zero_eq_succ] at eq1
  nth_rewrite 2 [eq1]
  rw [mul_succ, add_sub_cancel_right]

theorem mul_sub {a b c : MyNat} :
a.mul (b.sub c) = (a.mul b).sub (a.mul c) := by
  induction c with
  | zero =>
    rw [sub_zero, mul_zero, sub_zero]
  | succ c ih =>
  rw [sub_succ, mul_pred, ih, mul_succ, sub_sub_eq_sub_add]

theorem sub_mul {a b c : MyNat} :
(a.sub b).mul c = (a.mul c).sub (b.mul c) := by
  rw [mul_comm, mul_sub, mul_comm, mul_comm (a := c)]

end MyNat
