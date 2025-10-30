import MyLean.MyNat.p2_Addition

namespace MyNat

theorem ne_zero_eq_succ {a : MyNat} :
a ≠ zero ↔ a = a.pred.succ := by
  cases a
  case zero =>
    tauto
  case succ a =>
    tauto

theorem pred_eq_zero {a : MyNat} :
a.pred = zero ↔ a = zero ∨ a = one := by
  constructor
  · intro h
    cases a
    case zero => left; rfl
    case succ a => right; rw [pred] at h; rw [one, h]
  intro h
  rcases h with h | h
  · rw [h, pred]
  rw [h, one, pred]

theorem zero_sub (a : MyNat) : zero.sub a = zero := by
  rw [sub]

theorem sub_zero {a : MyNat} :
a.sub zero = a := by
  cases a with
  | zero => rw [sub]
  | succ a => rw [sub]

theorem succ_sub_succ {a b : MyNat} :
a.succ.sub b.succ = a.sub b := by rw [sub]

theorem sub_succ (a b : MyNat) :
a.sub b.succ = (a.sub b).pred := by
  induction a generalizing b with
  | zero =>
    rw [zero_sub, zero_sub, pred]
  | succ a ih =>
    rw [succ_sub_succ]
    cases b with
    | zero =>
      rw [sub_zero, sub_zero, pred]
    | succ b =>
      rw [succ_sub_succ]
      exact ih b

theorem sub_self {a : MyNat} :
a.sub a = zero := by
  induction a with
  | zero =>
    rw [sub_zero]
  | succ a ih =>
    rw [succ_sub_succ, ih]

theorem add_sub_cancel_right {a b : MyNat} :
(a.add b).sub b = a := by
  induction b with
  | zero =>
    rw [sub_zero, add_zero]
  | succ b ih =>
    rw [add_succ, succ_sub_succ]
    exact ih

theorem add_sub_cancel_left {a b : MyNat} :
(a.add b).sub a = b := by
  rw [add_comm]
  exact add_sub_cancel_right

theorem sub_eq_one (a b : MyNat) :
a.sub b = one ↔ a = b.succ := by
  induction a generalizing b with
  | zero =>
    rw [zero_sub, one]
    tauto
  | succ a ih =>
    by_cases bz : b = zero
    · rw [bz, one, sub_zero]
    rw [ne, ne_zero_eq_succ] at bz
    constructor
    · intro h
      rw [bz, succ_sub_succ, ih b.pred] at h
      rw [← bz] at h
      rw [h]
    intro h
    rw [succ_inj] at h
    rw [h, ← add_one, add_sub_cancel_left]

theorem succ_sub_self {a : MyNat} : a.succ.sub a = one := by
  rw [sub_eq_one]

theorem sub_eq_zero_of_sub_ne_zero {a b : MyNat}
(h : a.sub b ≠ zero) : b.sub a = zero := by
  induction a with
  | zero =>
    rw [zero_sub] at h; contradiction
  | succ a ih =>
    by_cases eq1 : a = b
    · rw [eq1, sub_succ, sub_self, pred]
    rw [sub_succ]
    have eq2 : a.sub b ≠ zero := by
      contrapose! h
      have bz : b ≠ zero := by
        intro bz
        rw [bz, sub_zero] at h
        rw [h, bz] at eq1
        contradiction
      rw [ne_zero_eq_succ] at bz
      rw [bz, succ_sub_succ]
      rw [bz, sub_succ, pred_eq_zero] at h
      rcases h with h | h
      · exact h
      rw [sub_eq_one] at h
      rw [← bz] at h
      contradiction
    apply ih at eq2
    rw [eq2, pred]

theorem pred_sub {m n : MyNat} :
m.pred.sub n = (m.sub n).pred := by
  by_cases mz : m = zero
  · rw [mz, pred, zero_sub, pred]
  rw [ne, ne_zero_eq_succ] at mz
  rw [← sub_succ]
  nth_rewrite 2 [mz]
  rw [succ_sub_succ]

theorem sub_sub_eq_sub_add {a b c : MyNat} :
(a.sub b).sub c = a.sub (b.add c) := by
  induction c with
  | zero =>
    rw [sub_zero, add_zero]
  | succ c ih =>
    rw [sub_succ, ih, add_succ, sub_succ]

theorem add_imp_sub_left {a b c : MyNat}
(h : a.add b = c) : b = c.sub a := by
  rw [← h, add_sub_cancel_left]

theorem add_imp_sub_right {a b c : MyNat}
(h : a.add b = c) : a = c.sub b := by
  rw [← h, add_sub_cancel_right]

theorem add_sub {a b : MyNat} :
(a.add (b.sub a) = a) ∨ (a.add (b.sub a) = b) := by
  by_cases eq1 : b.sub a = zero
  · left
    rw [eq1, add_zero]
  right
  induction a with
  | zero =>
    rw [zero_add, sub_zero]
  | succ a ih =>
    have eq2 : ¬b.sub a = zero := by
      contrapose! eq1
      rw [sub_succ, eq1, pred]
    apply ih at eq2
    rw [sub_succ, ← succ_add_of_add_succ]
    have : b.sub a ≠ zero := by
      contrapose! eq1
      rw [sub_succ, eq1, pred]
    rw [ne_zero_eq_succ] at this
    rw [← this]
    exact eq2

end MyNat
