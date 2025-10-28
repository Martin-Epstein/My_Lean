import MyLean.MyNat.p0_Definitions

namespace MyNat

theorem ne {a b : MyNat} :  ¬a = b ↔ a ≠ b := by
  rw [ne_eq]

theorem zero_ne_succ {a : MyNat} : zero ≠ a.succ := nofun

theorem succ_ne_zero {a : MyNat} : a.succ ≠ zero := nofun

theorem succ_inj {a b : MyNat} :
a.succ = b.succ ↔ a = b := by
  constructor
  · intro h
    exact succ.inj h
  intro h
  rw [h]

theorem self_ne_succ {a : MyNat} : a ≠ a.succ := by nofun

theorem succ_ne_self {n : MyNat} : n.succ ≠ n := by
  symm; exact self_ne_succ

theorem zero_ne_one : zero ≠ one := by
  rw [one]; exact zero_ne_succ

theorem one_ne_zero : one ≠ zero := by
  symm; exact zero_ne_one

theorem zero_ne_two : zero ≠ two := by
  rw [two]; exact zero_ne_succ

theorem two_ne_zero : two ≠ zero := by
  symm; exact zero_ne_two

theorem one_ne_two : one ≠ two := by
  rw [one, two]
  intro h
  rw [succ_inj] at h
  exact zero_ne_one h

theorem two_ne_one : two ≠ one := by
  symm; exact one_ne_two

theorem iterate_out (f : MyNat → MyNat) (n k : MyNat) :
iterate f n.succ k = f (iterate f n k) := by
/-This theorem states that applying f n+1 times is the
same as applying f n times, then applying f once more.
This is the reverse of the definition whereby applying
f n+1 times is the same as applying f once, and then
applying f n times more.
-/
  induction n generalizing k with
  | zero =>
    simp only [iterate]
  | succ n ih =>
    specialize ih (f k)
    rw [iterate, ih, iterate]

end MyNat
