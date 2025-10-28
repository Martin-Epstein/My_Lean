import MyLean.MyNat.p5_Ordering

namespace MyNat

theorem inc_local_to_global {f : MyNat → MyNat} :
increasing_local f ↔ increasing f := by
  constructor
  · intro h m n hmn
    rcases hmn with ⟨c, hmn⟩
    induction c generalizing n with
    | zero =>
      rw [add_succ] at hmn
      rw [hmn]
      exact h m
    | succ c hc =>
      cases n
      case zero =>
        rw [add_succ] at hmn
        exfalso; exact zero_ne_succ hmn
      case succ n =>
      rw [add_succ, succ_inj] at hmn
      have h2 := hc n hmn
      exact lt_trans h2 (h n)
  intro h n
  exact h n n.succ lt_succ_self

theorem nd_local_to_global {f : MyNat → MyNat} :
nondecreasing_local f ↔ nondecreasing f := by
  constructor
  · intro h1 m n h2
    rcases h2 with ⟨c, h2⟩
    rw [h2]; clear h2
    induction c with
    | zero =>
      rw [add_zero]
      exact le_self
    | succ c h2 =>
    rw [add_succ]
    exact le_trans h2 (h1 (m.add c))
  intro h m
  exact h m m.succ (lt_imp_le (lt_succ_self))

theorem inc_imp_nd {f : MyNat → MyNat} :
increasing f → nondecreasing f := by
  rw [← inc_local_to_global, ← nd_local_to_global]
  intro h1 n
  apply lt_imp_le
  exact h1 n

theorem inc_preserves_order {f : MyNat → MyNat} {m n : MyNat}
(h : increasing f) : (f m).lt (f n) ↔ m.lt n := by
  constructor
  · intro eq1
    rcases lt_or_ge (m := m) (n := n) with eq2 | eq2
    · exact eq2
    rw [ge] at eq2
    have eq3 := inc_imp_nd h
    have eq4 := eq3 n m eq2
    rw [le_iff_not_gt, gt] at eq4
    contradiction
  exact h m n

theorem increasing_inj {f : MyNat → MyNat} {m n : MyNat}
(h : increasing f) : f m = f n ↔ m = n := by
  constructor
  · intro eq1
    rcases lt_trichotomy (m := m) (n := n) with eq2 | eq2 | eq2
    · have eq3 := h m n eq2
      rw [lt_iff_le_and_ne] at eq3
      exfalso; exact eq3.2 eq1
    · exact eq2
    have eq3 := h n m eq2
    rw [lt_iff_le_and_ne] at eq3
    symm at eq1
    exfalso; exact eq3.2 eq1
  intro eq2
  rw [eq2]

theorem inc_of_inc_comp_inc {f g : MyNat → MyNat} :
increasing f → increasing g → increasing (fun x => f ( g x)) := by
  intro hf hg m n hmn
  simp
  exact hf (g m) (g n) (hg m n hmn)

theorem nd_of_nd_comp_nd {f g : MyNat → MyNat} :
nondecreasing f → nondecreasing g →
nondecreasing (fun x => f (g x)) := by
  intro hf hg m n hmn
  simp
  exact hf (g m) (g n) (hg m n hmn)

end MyNat
