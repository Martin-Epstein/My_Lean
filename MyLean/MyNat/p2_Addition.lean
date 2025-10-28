import MyLean.MyNat.p1_Successor

namespace MyNat

theorem add_zero {a : MyNat} :
a.add zero = a := by
  rw [add, iterate]

theorem succ_add_of_add_succ {a b : MyNat} :
a.add b.succ = a.succ.add b := by
  rw [add, iterate, ← add]

theorem add_succ (a b : MyNat) :
a.add b.succ = (a.add b).succ := by
  rw [add, iterate_out, add]

theorem succ_add (a b : MyNat) :
a.succ.add b = (a.add b).succ := by
  rw [← succ_add_of_add_succ, add_succ]

theorem zero_add {a : MyNat} : zero.add a = a := by
  induction a with
  | zero =>
    rw [add_zero]
  | succ a ih =>
    rw [add_succ, ih]

theorem add_comm {a b : MyNat} :
a.add b = b.add a := by
  induction b with
  | zero =>
    rw [add_zero, zero_add]
  | succ b ih =>
    rw [add_succ, ih, succ_add]

theorem iterate_add (f : MyNat → MyNat) (m n k : MyNat) :
iterate f m (iterate f n k) = iterate f (add n m) k := by
  induction m with
  | zero =>
    rw [add_zero, iterate]
  | succ m ih =>
    rw [iterate_out, add_succ, iterate_out]
    rw [← ih]

theorem add_assoc {a b c : MyNat} :
(a.add b).add c = a.add (b.add c) := by
  rw [add, add, add, iterate_add]

theorem add_left_cancel {a b c : MyNat} :
a.add b = a.add c ↔ b = c := by
  constructor
  · intro h
    induction a with
    | zero =>
      rw [zero_add, zero_add] at h
      exact h
    | succ a ih =>
      rw [succ_add, succ_add, succ_inj] at h
      exact ih h
  intro h
  rw [h]

theorem add_right_cancel {a b c : MyNat} :
a.add c = b.add c ↔ a = b := by
  constructor
  · intro h
    rw [add_comm, add_comm (a := b), add_left_cancel] at h
    exact h
  intro h
  rw [h]

theorem add_one {a : MyNat} :
a.add one = a.succ := by
  rw [one, add_succ, add_zero]

theorem one_add {n : MyNat} :
one.add n = n.succ := by
  rw [add_comm]; exact add_one

theorem add_eq_zero {m n : MyNat} :
m.add n = zero ↔ m = zero ∧ n = zero := by
  constructor
  · intro h
    induction n with
    | zero =>
      rw [add_zero] at h; exact ⟨h, rfl⟩
    | succ n ih =>
      rw [add_succ] at h
      apply succ_ne_zero at h
      contradiction
  intro h
  rcases h with ⟨h1, h2⟩
  rw [h1, h2, add_zero]

theorem zero_eq_add {m n : MyNat} :
zero = m.add n ↔ m = zero ∧ n = zero := by
  constructor
  · intro h
    symm at h
    exact add_eq_zero.1 h
  intro h
  rw [h.1, h.2, add_zero]

theorem add_eq_left {m n : MyNat} :
m.add n = m ↔ n = zero := by
  constructor
  · intro eq1
    nth_rewrite 2 [← add_zero (a := m)] at eq1
    rw [add_left_cancel] at eq1
    exact eq1
  intro eq1
  rw [eq1, add_zero]

theorem add_eq_right {m n : MyNat} :
m.add n = n ↔ m = zero := by
  rw [add_comm]
  exact add_eq_left

theorem one_add_one : one.add one = two := by
  rw [add_one, ← two]

end MyNat
