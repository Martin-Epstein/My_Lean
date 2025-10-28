import MyLean.MyNat.p4_Multiplication

namespace MyNat

theorem le_self {n : MyNat} : n.le n := by
  use zero
  rw [add_zero]

theorem le_self_add (m n : MyNat) :
m.le (m.add n) := by
  use n

theorem le_add_self (m n : MyNat) :
m.le (n.add m) := by
  use n
  rw [add_comm]

theorem add_imp_lt {m n c : MyNat} :
c ≠ zero → m.add c = n → m.lt n := by
  intro h1 h2
  rw [ne_zero_eq_succ] at h1
  use c.pred
  rw [← h1]
  symm
  exact h2

theorem lt_iff_succ_le {m n : MyNat} :
m.lt n ↔ m.succ.le n := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    use c
    rw [succ_add, ← add_succ]
    exact h
  intro h
  rcases h with ⟨c, hc⟩
  use c
  rw [add_succ, ← succ_add]
  exact hc

theorem lt_imp_le {m n : MyNat} :
m.lt n → m.le n := by
  intro eq1
  rw [lt] at eq1
  rcases eq1 with ⟨c, eq1⟩
  use c.succ

theorem lt_succ_self {n : MyNat} :
n.lt n.succ := by
  use zero
  rw [add_succ, add_zero]

theorem le_succ {n : MyNat} : n.le n.succ := by
  exact lt_imp_le (lt_succ_self (n := n))

theorem zero_le {a : MyNat} : zero.le a := by
  use a
  rw [zero_add]

theorem le_zero {a : MyNat} : a.le zero ↔ a = zero := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    symm at h
    rw [add_eq_zero] at h
    exact h.1
  intro h
  rw [h]
  exact zero_le

theorem succ_le_succ {a b : MyNat} :
a.succ.le b.succ ↔ a.le b := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    use c
    rw [succ_add, succ_inj] at h
    exact h
  intro h
  rcases h with ⟨c, h⟩
  use c
  rw [h, succ_add]

theorem le_one {n : MyNat} :
n.le one ↔ n = zero ∨ n = one := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    cases c
    · rw [add_zero] at h
      right
      symm; exact h
    case succ c =>
      rw [add_succ, one, succ_inj, zero_eq_add] at h
      left
      exact h.1
  intro h
  rcases h with h | h
  · use one
    rw [h, zero_add]
  rw [h]
  exact le_self

theorem lt_one {n : MyNat} :
n.lt one ↔ n = zero := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    rw [one, add_succ, succ_inj, zero_eq_add] at h
    exact h.1
  intro h
  rw [h]
  use zero
  rw [zero_add, ← one]

theorem one_le {n : MyNat} :
one.le n ↔ n ≠ zero := by
  constructor
  · intro h h'
    rw [h', le_zero] at h
    exact one_ne_zero h
  intro h
  rw [ne_zero_eq_succ] at h
  rw [one, h, succ_le_succ]
  exact zero_le

theorem not_succ_le_self {n : MyNat} : ¬ n.succ.le n := by
  intro h
  rcases h with ⟨c, h⟩
  symm at h
  rw [succ_add, ← add_succ, add_eq_left] at h
  exact succ_ne_zero h

theorem le_antisymm {a b : MyNat} (ab : a.le b) (ba : b.le a) :
a = b := by
  rcases ab with ⟨c, ab⟩
  rcases ba with ⟨d, ba⟩
  rw [ba, add_assoc] at ab
  nth_rewrite 2 [← add_zero (a := b)] at ab
  symm at ab
  rw [add_zero, add_eq_left, add_eq_zero] at ab
  rw [ab.1, add_zero] at ba
  rw [ba]

theorem le_of_succ_le {a b : MyNat} (h : a.succ.le b) : a.le b := by
  rcases h with ⟨c, h⟩
  use c.succ
  rw [add_succ]
  rw [succ_add] at h
  exact h

theorem le_trans {a b c : MyNat} (hab : a.le b) (hbc : b.le c) :
a.le c := by
  rcases hab with ⟨m, hab⟩
  rcases hbc with ⟨n, hbc⟩
  use m.add n
  rw [← add_assoc, ← hab]
  exact hbc

theorem not_lt_self {n : MyNat} : ¬ n.lt n := by
  intro h
  rcases h with ⟨c, h⟩
  symm at h
  rw [add_eq_left] at h
  exact succ_ne_zero h

theorem succ_lt_succ {m n : MyNat} :
m.succ.lt n.succ ↔ m.lt n := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    rw [add_succ, succ_inj, succ_add, ← add_succ] at h
    use c
  intro h
  rcases h with ⟨c, h⟩
  use c
  rw [succ_add, h]

theorem le_iff_lt_or_eq {m n : MyNat} :
m.le n ↔ m.lt n ∨ m = n := by
  constructor
  · intro eq1
    rcases eq1 with ⟨c, eq1⟩
    cases c
    case zero =>
      rw [add_zero] at eq1
      right; symm; exact eq1
    case succ c =>
      left; use c
  intro eq1
  rcases eq1 with eq1 | eq1
  · exact lt_imp_le eq1
  rw [eq1]; exact le_self

theorem lt_of_le_of_lt {a b c : MyNat}
(eq1 : a.le b) (eq2 : b.lt c) :
a.lt c := by
  rcases eq1 with ⟨m, eq1⟩
  rcases eq2 with ⟨n, eq2⟩
  use m.add n
  rw [← add_succ, ← add_assoc, ← eq1]
  exact eq2

theorem lt_of_lt_of_le {a b c : MyNat}
(eq1 : a.lt b) (eq2 : b.le c) :
a.lt c := by
  rcases eq1 with ⟨m, eq1⟩
  rcases eq2 with ⟨n, eq2⟩
  use m.add n
  rw [← succ_add, ← add_assoc, ← eq1]
  exact eq2

theorem le_or_gt {m n : MyNat} : m.le n ∨ m.gt n := by
  induction n with
  | zero =>
    cases m
    case zero =>
      left; exact le_self
    case succ m =>
      right
      use m
      rw [zero_add]
  | succ n ih =>
    rcases ih with ⟨c, ih⟩ | ⟨c, ih⟩
    · left
      use c.succ
      rw [add_succ, ih]
    cases c
    case zero =>
      left
      rw [add_succ, add_zero] at ih
      rw [ih]; exact le_self
    case succ c =>
      right
      rw [ih, gt, add_succ, succ_lt_succ]
      use c

theorem le_iff_not_gt {m n : MyNat} : m.le n ↔ ¬m.gt n := by
  constructor
  · intro eq1 eq2
    rw [gt] at eq2
    have eq3 := lt_of_le_of_lt eq1 eq2
    exact not_lt_self eq3
  intro eq1
  have eq2 := le_or_gt (m := m) (n := n)
  rcases eq2 with eq2 | eq2
  · exact eq2
  contradiction

theorem lt_iff_not_ge {m n : MyNat} : m.lt n ↔ ¬ m.ge n := by
  have eq1 := le_iff_not_gt (m := m.succ) (n := n)
  rw [lt_iff_succ_le, ge]
  rw [gt, lt_iff_succ_le, succ_le_succ] at eq1
  exact eq1

theorem lt_or_ge {m n : MyNat} : m.lt n ∨ m.ge n := by
  have eq1 := le_or_gt (m := m.succ) (n := n)
  rw [lt_iff_not_ge]
  tauto

theorem lt_trichotomy {m n : MyNat} :
m.lt n ∨ m = n ∨ (n.lt m) := by
  rcases le_or_gt (m := m) (n := n) with eq1 | eq1
  · rw [le_iff_lt_or_eq] at eq1
    rw [← or_assoc]; left
    exact eq1
  rw [gt] at eq1
  right; right; exact eq1

theorem lt_trans {a b c : MyNat} (eq1 : a.lt b) (eq2 : b.lt c) :
a.lt c := by
  rcases eq1 with ⟨m, eq1⟩
  rcases eq2 with ⟨n, eq2⟩
  use m.succ.add n
  rw [add_succ, ← add_assoc, ← eq1, ← add_succ, eq2]

theorem lt_imp_not_lt {m n : MyNat} :
m.lt n → ¬ n.lt m := by
  intro h1 h2
  exact not_lt_self (lt_trans h1 h2)

theorem lt_iff_le_and_ne {m n : MyNat} :
m.lt n ↔ m.le n ∧ m ≠ n := by
  constructor
  · intro eq1
    constructor
    · exact lt_imp_le eq1
    intro eq2
    rw [eq2] at eq1
    exact not_lt_self eq1
  intro h
  rcases h with ⟨⟨c, h1⟩, h2⟩
  cases c
  case zero =>
    rw [add_zero] at h1
    symm at h1
    contradiction
  case succ c =>
    use c

theorem zero_lt_succ {n : MyNat} : zero.lt n.succ := by
  use n
  rw [zero_add]

theorem zero_lt_one : zero.lt one := by
  use zero
  rw [zero_add, ← one]

theorem one_lt_two : one.lt two := by
  use zero
  rw [← one]
  exact one_add_one

theorem zero_lt_two : zero.lt two := by
  exact lt_trans zero_lt_one one_lt_two

theorem sub_eq_zero_iff_le {a b : MyNat} :
a.sub b = zero ↔ a.le b := by
  constructor
  · intro eq1
    have eq2 := lt_trichotomy (m := a) (n := b)
    rcases eq2 with eq2 | eq2 | eq2
    · exact lt_imp_le eq2
    · rw [eq2]
      exact le_self
    rcases eq2 with ⟨c, eq2⟩
    rw [eq2, add_sub_cancel_left] at eq1
    have eq3 := succ_ne_zero (a := c)
    contradiction
  intro eq1
  rcases eq1 with ⟨c, eq1⟩
  rw [eq1, ← sub_sub_eq_sub_add, sub_self, zero_sub]

theorem succ_sub {a b : MyNat} :
a.le b ↔ b.succ.sub a = (b.sub a).succ := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    rw [h, ← add_succ, add_sub_cancel_left,
        add_sub_cancel_left]
  intro h
  rcases le_or_gt (m := a) (n := b) with h2 | h2
  · exact h2
  rw [gt] at h2
  rw [lt_iff_succ_le, ← sub_eq_zero_iff_le] at h2
  rw [h2] at h
  exfalso; exact zero_ne_succ h

theorem add_le_add_right_cancel {a b c : MyNat} :
(a.add c).le (b.add c) ↔ a.le b := by
  induction c with
  | zero =>
    rw [add_zero, add_zero]
  | succ c ih =>
    rw [add_succ, add_succ, succ_le_succ]
    exact ih

theorem add_le_add_left_cancel {a b c : MyNat} :
(a.add b).le (a.add c) ↔ b.le c := by
  rw [add_comm, add_comm (b := c), add_le_add_right_cancel]

theorem add_lt_add_right_cancel {a b c : MyNat} :
(a.add c).lt (b.add c) ↔ a.lt b := by
  constructor
  · intro h
    rcases h with ⟨d, h⟩
    use d
    rw [add_assoc, add_comm (a := c), ← add_assoc,
        add_right_cancel] at h
    exact h
  intro h
  rcases h with ⟨d, h⟩
  use d
  rw [h, add_succ, add_succ, succ_add, add_assoc,
      add_comm (a := d), add_assoc]

theorem add_lt_add_left_cancel {a b c : MyNat} :
(a.add b).lt (a.add c) ↔ b.lt c := by
  rw [add_comm, add_comm (a := a)]
  exact add_lt_add_right_cancel

theorem le_mul {m n : MyNat} :
m.le (m.mul n.succ) := by
  rw [mul_succ]
  nth_rewrite 1 [← zero_add (a := m)]
  rw [add_le_add_right_cancel]
  exact zero_le

theorem le_iff_lt_succ {m n : MyNat} :
m.le n ↔ m.lt n.succ := by
  rw [lt_iff_succ_le, succ_le_succ]

theorem add_sub_le_right {a b c : MyNat} (h : c.le b) :
(a.add b).sub c = a.add (b.sub c) := by
  induction c with
  | zero =>
    rw [sub_zero, sub_zero]
  | succ c ih =>
    have h2 := h
    rcases h with ⟨d, h⟩
    rw [succ_add, ← add_succ] at h
    have eq1 : c.le b := by
      use d.succ
    have eq2 := ih eq1
    rw [sub_succ, eq2, sub_succ]
    have eq3 : b.sub c ≠ zero := by
      rw [le_iff_lt_succ, succ_lt_succ, lt] at h2
      rcases h2 with ⟨h2, h3⟩
      contrapose! h3
      rw [h, add_sub_cancel_left] at h3
      have := succ_ne_zero (a := d)
      contradiction
    rw [ne_zero_eq_succ] at eq3
    rw [eq3, add_succ, pred, pred]

theorem add_le_add {a b c d : MyNat} :
a.le c → b.le d → (a.add b).le (c.add d) := by
  intro ac bd
  rcases ac with ⟨m, ac⟩
  rcases bd with ⟨n, bd⟩
  use m.add n
  rw [add_comm (a := m), add_assoc, ← add_assoc (a := b), ← bd,
      add_comm (a := d), ← add_assoc, ← ac]

theorem mul_le_mul {a b c d : MyNat} :
a.le c → b.le d → (a.mul b).le (c.mul d) := by
  intro ac bd
  rcases ac with ⟨m, ac⟩
  rcases bd with ⟨n, bd⟩
  rw [ac, bd, mul_add, add_mul, add_mul, add_assoc]
  use (m.mul b).add ((a.mul n).add (m.mul n))

theorem mul_lt_mul {a b c d : MyNat} :
a ≠ zero → b ≠ zero → a.le c →
b.lt d → (a.mul b).lt (c.mul d) := by
  intro az bz ac bd
  rcases ac with ⟨m, hm⟩
  rcases bd with ⟨n ,hn⟩
  set N : MyNat := n.succ
  rw [hn, hm, add_mul, mul_add, add_assoc]
  nth_rewrite 1 [← add_zero (a := a.mul b)]
  rw [add_lt_add_left_cancel, lt_iff_le_and_ne]
  constructor
  · exact zero_le
  intro h
  symm at h
  rw [add_eq_zero] at h
  rcases h with ⟨h1, _⟩
  rw [mul_eq_zero] at h1
  rcases h1 with h | h
  · exact az h
  exact succ_ne_zero h

theorem sub_ne_zero_iff_gt {m n : MyNat} :
m.sub n ≠ zero ↔ m.gt n := by
  constructor
  · intro eq1
    rw [gt]
    use ((m.sub n).pred)
    rw [ne_zero_eq_succ] at eq1
    rw [← eq1]
    rcases add_sub (a := n) (b := m) with eq2 | eq2
    · cases n
      case zero =>
        rw [zero_add, sub_zero] at eq2
        rw [eq2, zero_add, sub_zero]
      case succ n =>
        rw [sub_succ, succ_add, succ_inj, add_eq_left] at eq2
        rw [sub_succ, eq2, pred] at eq1
        exfalso
        exact zero_ne_succ eq1
    exact eq2.symm
  intro eq1 eq2
  rcases eq1 with ⟨c, eq1⟩
  rw [eq1, add_sub_cancel_left] at eq2
  exact succ_ne_zero eq2

theorem mul_right_increasing {m n : MyNat}
(hm : m ≠ zero) (hn : two.le n) :
m.lt (m.mul n) := by
  cases m
  case zero => contradiction
  case succ m =>
  clear hm
  rcases hn with ⟨c, hc⟩
  use m.add (m.succ.mul c)
  rw [succ_mul, hc, succ_add, succ_mul, add_succ, mul_add,
      two, succ_add, one_add, mul_succ, mul_one, add_succ, add_succ,
      succ_inj, succ_inj, add_assoc, add_assoc]

theorem mul_left_increasing {m n : MyNat}
(hm : two.le m) (hn : n ≠ zero) :
n.lt (m.mul n) := by
  have := mul_right_increasing (m := n) (n := m) hn hm
  rw [mul_comm]
  exact this

theorem mul_le_mul_left_cancel (a b c : MyNat) :
(a.succ.mul b).le (a.succ.mul c) ↔ b.le c := by
  constructor
  · intro h1
    rw [succ_mul, succ_mul] at h1
    rw [le_iff_not_gt]
    intro h2
    rw [gt] at h2
    rcases h2 with ⟨d, h2⟩
    rw [h2, add_comm (a := c), ← add_assoc,
        add_le_add_right_cancel, mul_add,
        add_assoc, add_comm (a := a.mul c),
        ← add_assoc] at h1
    nth_rewrite 2 [← zero_add (a := a.mul c)] at h1
    rw [add_le_add_right_cancel, le_zero, add_succ] at h1
    exact succ_ne_zero h1
  intro h
  set a' := a.succ
  rcases h with ⟨d, h⟩
  rw [h, mul_add]
  apply le_self_add

end MyNat
