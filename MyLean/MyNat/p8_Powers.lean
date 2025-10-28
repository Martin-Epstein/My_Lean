import MyLean.MyNat.p7_Summation

namespace MyNat

theorem pow_zero {n : MyNat} :
n.pow zero = one := by
  rw [pow, iterate]

theorem pow_succ {m n : MyNat} :
m.pow n.succ = (m.pow n).mul m := by
  rw [pow, iterate_out, ← pow]

theorem pow_succ_left {m n : MyNat} :
m.pow n.succ = m.mul (m.pow n) := by
  rw [pow_succ, mul_comm]

theorem zero_pow {n : MyNat} :
zero.pow n.succ = zero := by
  rw [pow_succ, mul_zero]

theorem one_pow {n : MyNat} :
one.pow n = one := by
  induction n with
  | zero =>
    rw [pow_zero]
  | succ n ih =>
    rw [pow_succ, mul_one, ih]

theorem pow_one {n : MyNat} :
n.pow one = n := by
  rw [one, pow_succ, pow_zero, one_mul]

theorem pow_two {n : MyNat} :
n.pow two = n.mul n := by
  rw [two, pow_succ, pow_one]

theorem pow_eq_zero {m n : MyNat} :
m.pow n = zero → m = zero := by
  intro h
  cases m with
  | zero =>
    rfl
  | succ m =>
    induction n with
    | zero =>
      rw [pow_zero, one] at h; tauto
    | succ n ih =>
      rw [pow_succ, mul_eq_zero] at h
      rcases h with h | h
      · apply ih at h; exact h
      exact h

theorem pow_eq_one {m n : MyNat} (eq1 : two.le m) :
m.pow n = one ↔ n = zero := by
  constructor
  · intro eq2
    by_cases eq3 : n = zero
    · exact eq3
    rw [ne, ne_zero_eq_succ] at eq3
    rw [eq3, pow_succ, mul_eq_one] at eq2
    rw [eq2.2, two, one, succ_le_succ, le_zero] at eq1
    have eq4 := succ_ne_zero (a := zero)
    contradiction
  intro eq2
  rw [eq2, pow_zero]

theorem one_le_pow {m n : MyNat} (eq1 : m ≠ zero) :
one.le (m.pow n) := by
  rw [le_iff_not_gt]
  contrapose! eq1
  rw [gt, lt_one] at eq1
  exact pow_eq_zero eq1

theorem pow_add {a b c : MyNat} :
a.pow (b.add c) = (a.pow b).mul (a.pow c) := by
  induction c with
  | zero =>
    rw [add_zero, pow_zero, mul_one]
  | succ c ih =>
    rw [add_succ, pow_succ, ih, pow_succ, mul_assoc]

theorem tri_add_tri {n : MyNat} :
(tri n).add (tri n.pred) = n.pow two := by
  cases n
  · case zero =>
    rw [pred, two, zero_pow, tri_zero, add_zero]
  case succ n =>
  rw [pred, tri, sum_extract_first, id, zero_add,
      sum_reverse, tri, add_sum]
  set f := fun x ↦ (id (n.succ.sub x).pred.succ).add (id x) with f_def
  set g := fun (x : MyNat) ↦ n.succ with g_def
  have : ∀ m, m.lt n.succ → f m = g m := by
    intro m h
    rw [f_def, g_def]
    dsimp
    rcases h with ⟨c, h⟩
    rw [h, add_sub_cancel_left, pred, add_comm]
  apply sum_eq_sum at this
  rw [this, g_def, sum_const_eq_mul, pow_two]

theorem pow_right_increasing {a b c : MyNat}
(ha : two.le a) (hbc : b.lt c) : (a.pow b).lt (a.pow c) := by
  set f : MyNat → MyNat := fun x => a.pow x with f_def
  have f_inc : increasing_local f := by
    intro x
    rw [f_def]; simp
    rw [pow_succ]
    have : a.pow x ≠ zero := by
      intro h
      have := pow_eq_zero h
      rw [this, le_zero] at ha
      exact two_ne_zero ha
    exact mul_right_increasing (m := a.pow x) (n := a) this ha
  rw [inc_local_to_global] at f_inc
  have := f_inc b c hbc
  rw [f_def] at this
  simp at this
  exact this

theorem prod_zero (f : MyNat → MyNat) : prod f zero = one := by
  rw [prod, prod.prodAux]

theorem prod_aux (f : MyNat → MyNat) (m n : MyNat) :
prod.prodAux f m n = mul (prod f m) n := by
  induction m generalizing n with
  | zero =>
    rw [prod.prodAux, prod_zero, one_mul]
  | succ m ih =>
    rw [prod.prodAux]
    have := ih (n.mul (f m))
    rw [this]; symm; rw [prod, prod.prodAux, one_mul]
    specialize ih (f m)
    rw [ih, mul_assoc, mul_comm (a := n)]

theorem prod_succ (f : MyNat → MyNat) (n : MyNat) :
prod f n.succ = mul (prod f n) (f n) := by
  rw [prod, prod.prodAux, one_mul, prod_aux]

theorem pow_as_prod {m n : MyNat} :
m.pow n = prod (fun _ => m) n := by
  induction n with
  | zero =>
    rw [pow_zero, prod_zero]
  | succ n ih =>
    rw [pow_succ, prod_succ, ih]

theorem pow_left_increasing_aux {f : MyNat → MyNat} {c : MyNat}
(f_def : f = fun x => x.pow c.succ) :
increasing_local f := by
  induction c generalizing f with
  | zero =>
    intro n
    rw [f_def]; simp
    rw [← one, pow_one, pow_one]
    exact lt_succ_self
  | succ c hc =>
  intro n
  rw [f_def]; simp
  rw [pow_succ]
  nth_rewrite 2 [pow_succ]
  set g : MyNat → MyNat := fun x => x.pow c.succ with g_def
  have hg := hc g_def
  have eq1 := hg n
  rw [g_def] at eq1
  simp at eq1
  by_cases nz : n = zero
  · rw [nz, mul_zero, ← one, one_pow, mul_one]
    exact zero_lt_one
  apply mul_lt_mul
  · intro h
    exact nz (pow_eq_zero h)
  · exact nz
  · exact lt_imp_le eq1
  exact lt_succ_self

theorem pow_left_increasing {a b c : MyNat}
(cz : c ≠ zero) : (a.pow c).lt (b.pow c) ↔ a.lt b := by
  rw [ne_zero_eq_succ] at cz
  set d : MyNat := c.pred with d_def
  set f : MyNat → MyNat := fun x => x.pow d.succ with f_def
  have f_inc := pow_left_increasing_aux f_def
  rw [inc_local_to_global] at f_inc
  have eq := inc_preserves_order (f := f) (m := a) (n := b) f_inc
  rw [f_def] at eq; simp at eq
  rw [cz]; exact eq

theorem mul_pow {a b c : MyNat} :
(a.mul b).pow c = (a.pow c).mul (b.pow c) := by
  induction c with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero, mul_one]
  | succ c ih =>
    rw [pow_succ, ih, pow_succ, pow_succ, mul_assoc,
        mul_assoc, ← mul_assoc (a := a) (b := b.pow c),
        mul_comm (a := a) (b := b.pow c), mul_assoc]

theorem pow_sub_pow {a b c : MyNat} :
(a.pow c).sub (b.pow c) = (a.sub b).mul
(sum (fun x => (a.pow x).mul (b.pow (c.pred.sub x))) c) := by
  cases c
  case zero =>
    rw [pow_zero, pow_zero, sub_self, sum_zero, mul_zero]
  case succ c =>
  rw [pred]
  rcases lt_or_ge (m := a) (n := b) with h | h
  · have h2 := pow_left_increasing
               (a := a) (b := b) (c := c.succ) succ_ne_zero
    have h3 := h2.2 h
    apply lt_imp_le at h3
    rw [← sub_eq_zero_iff_le] at h3
    have h4 := lt_imp_le h
    rw [← sub_eq_zero_iff_le] at h4
    rw [h3, h4, zero_mul]
  rw [ge] at h
  set f : MyNat → MyNat :=
    fun x => (a.pow x).mul (b.pow (c.succ.sub x)) with f_def
  have eq1 : a.pow c.succ = f (c.succ) := by
    rw [f_def]; simp
    rw [sub_self, pow_zero, mul_one]
  have eq2 : b.pow c.succ = f zero := by
    rw [f_def]; simp
    rw [pow_zero, one_mul, sub_zero]
  have f_nd : nondecreasing_local f := by
    intro n
    rw [f_def]; simp
    rcases le_or_gt (m := n) (n := c) with eq3 | eq3
    · rcases eq3 with ⟨d, eq3⟩
      symm at eq3
      have eq4 := add_imp_sub_left eq3
      rw [succ_sub_succ]
      have eq5 : c.succ.sub n = d.succ := by
        rw [← eq3, ← add_succ, add_sub_cancel_left]
      rw [← eq4, eq5]
      rw [pow_succ, pow_succ]
      cases n
      case zero =>
        rw [pow_zero, one_mul, one_mul, mul_comm]
        apply mul_le_mul
        · exact h
        exact le_self
      case succ n =>
      rw [pow_succ, mul_assoc, mul_assoc, mul_assoc,
          mul_comm (a := a) (b := b.pow d),
          ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      apply mul_le_mul
      · exact le_self
      exact h
    rw [gt, lt_iff_succ_le, ← sub_eq_zero_iff_le] at eq3
    rw [sub_succ, eq3, pred, pow_zero, mul_one, mul_one, pow_succ]
    have nz : n ≠ zero := by
      intro eq4
      rw [eq4, sub_zero] at eq3
      exact succ_ne_zero eq3
    cases a
    case zero =>
      rw [ne_zero_eq_succ] at nz
      rw [mul_zero, nz, pow_succ, mul_zero]
      exact le_self
    case succ a =>
    set A : MyNat := a.succ with A_def
    nth_rewrite 1 [← mul_one (a := A.pow n)]
    apply mul_le_mul
    · exact le_self
    rw [A_def, one, succ_le_succ]
    exact zero_le
  rw [nd_local_to_global] at f_nd
  have tele := telescope (f := f) (n := c.succ) f_nd
  set g : MyNat → MyNat := fun x => (f x.succ).sub (f x) with g_def
  set G : MyNat → MyNat := fun x =>
    (a.sub b).mul ((a.pow x).mul (b.pow (c.sub x))) with G_def
  have eq3 : ∀ x, x.lt c.succ →
  g x = G x := by
    intro x eq3
    rw [← le_iff_lt_succ] at eq3
    rw [G_def]; simp
    rw [sub_mul, ← mul_assoc, ← pow_succ_left, ← mul_assoc,
        mul_comm (b := a.pow x), mul_assoc, ← pow_succ_left]
    rw [g_def, f_def]; simp
    rw [succ_sub_succ]
    rw [succ_sub.1 eq3]
  have eq4 := sum_eq_sum eq3
  rw [eq4, G_def, ← num_mul_sum] at tele
  have fc : f c.succ = a.pow c.succ := by
    rw [f_def]; simp
    rw [sub_self, pow_zero, mul_one]
  have f0 : f zero = b.pow c.succ := by
    rw [f_def]; simp
    rw [pow_zero, one_mul, sub_zero]
  rw [← f0, ← fc]
  exact tele

theorem sq_sub_sq {m n : MyNat} :
(m.pow two).sub (n.pow two) = (m.sub n).mul (m.add n) := by
  rw [pow_sub_pow (a := m) (b := n) (c := two)]
  rw [two, sum_succ, pred, sub_self, pow_zero, mul_one, pow_one]
  nth_rewrite 2 [one]
  rw [sum_succ, sub_zero, pow_one, pow_zero, one_mul, sum_zero,
      zero_add, add_comm]

theorem sum_cb_eq_tri_sq {n : MyNat} :
sum (fun x => x.succ.pow three) n = n.tri.pow two := by
  have eq1 : ∀ x : MyNat,
  x.pow three = (x.tri.pow two).sub ((x.pred.tri).pow two) := by
    intro x
    calc
      x.pow three = x.mul (x.pow two) := by
        rw [three, pow_succ_left]
      _ = (x.tri.sub x.pred.tri).mul (x.tri.add x.pred.tri) := by
        rw [tri_sub_tri, tri_add_tri]
      _ = (x.tri.pow two).sub ((x.pred.tri).pow two) := by
        symm
        exact sq_sub_sq (m := x.tri) (n := x.pred.tri)
  set sq : MyNat → MyNat := fun x => x.pow two with sq_def
  have sq_inc : increasing sq := by
    intro a b h
    rw [sq_def]; simp
    rw [pow_left_increasing (a := a) (b := b) (c := two)
      two_ne_zero]
    exact h
  set f : MyNat → MyNat := fun x => sq (tri x) with f_def
  have f_inc := inc_of_inc_comp_inc sq_inc tri_inc
  rw [← f_def] at f_inc
  have f_nd := inc_imp_nd (f := f) f_inc
  have tele := telescope (f := f) (n := n) f_nd
  have fn : f n = n.tri.pow two := by
    rw [f_def]
  have f0 : f zero = zero := by
    rw [f_def]; dsimp
    rw [tri_zero, sq_def]; dsimp
    rw [two, zero_pow]
  rw [fn, f0, sub_zero] at tele
  set g : MyNat → MyNat := fun x => (f x.succ).sub (f x) with g_def
  have hg : g = fun x : MyNat => x.succ.pow three := by
    ext x
    rw [g_def, f_def, sq_def]; simp; symm
    have := eq1 x.succ
    rw [pred] at this
    exact this
  rw [hg] at tele
  symm
  exact tele

end MyNat
