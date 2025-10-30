import MyLean.MyNat.p8_Powers

namespace MyNat

theorem induction_from {P : MyNat → Prop} {n : MyNat} :
(P n) → (∀ m, n.le m → P m → P m.succ) → (∀ m, n.le m → P m) := by
  intro hp hm
  have : ∀ c, P (n.add c) := by
    intro c
    induction c with
    | zero =>
      rw [add_zero]; exact hp
    | succ c ih =>
      have eq1 : n.le (n.add c) := by
        use c
      have eq2 := hm (n.add c) eq1 ih
      rw [add_succ]; exact eq2
  intro m hmn
  rcases hmn with ⟨c, hc⟩
  rw [hc]
  exact this c

theorem zero_is_min {P : MyNat → Prop} :
P zero ↔ min P zero := by
  constructor
  · intro h
    constructor
    · exact h
    intro n hn
    exact zero_le
  intro h
  rcases h with ⟨h, _⟩
  exact h

lemma well_order_aux {P : MyNat → Prop} :
(∀ m : MyNat, ¬ min P m) → (∀ m n : MyNat, n.le m → ¬ P n) := by
  intro h1 m n h2
  induction m generalizing n with
  | zero =>
    rw [le_zero] at h2
    rw [h2]
    have h3 := h1 zero
    contrapose! h3
    rw [zero_is_min (P := P)] at h3
    exact h3
  | succ m ih =>
    have h3 := h1 n
    contrapose! h3
    constructor
    · exact h3
    intro k hk1
    rw [le_iff_not_gt]
    intro hk2
    rw [gt] at hk2
    have hk3 := lt_of_lt_of_le hk2 h2
    rw [lt_iff_succ_le, succ_le_succ] at hk3
    exact ih k hk3 hk1

theorem well_order {P : MyNat → Prop} :
satisfiable P ↔ ∃ m, min P m := by
  constructor
  · intro h
    contrapose h
    push_neg at h
    rw [satisfiable]
    push_neg
    have h2 := well_order_aux h
    intro m
    exact h2 m m le_self
  intro h
  rcases h with ⟨m, ⟨h1, _⟩⟩
  use m

theorem lt_min (P : MyNat → Prop) (m k : MyNat)
(km : k.lt m) (hm : min P m) : ¬ P k := by
  rw [lt_iff_not_ge, ge] at km
  rw [min] at hm
  rcases hm with ⟨h1, h2⟩
  specialize h2 k
  tauto

theorem strong_induction (P : MyNat → Prop) :
(∀ m : MyNat, (∀ k : MyNat, k.lt m → P k) → P m) →
∀ m : MyNat, P m := by
  by_contra h
  push_neg at h
  rcases h with ⟨h1, h2⟩
  rw [← satisfiable, well_order] at h2
  rcases h2 with ⟨m, h2⟩
  specialize h1 m
  have : ∀ (k : MyNat), k.lt m → P k := by
    intro k hk
    have := lt_min (P := fun x => ¬P x)
      (m := m) (k := k) (km := hk) (hm := h2)
    exact not_not.1 this
  apply h1 at this
  exact h2.1 this

end MyNat
