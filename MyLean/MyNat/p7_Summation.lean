import MyLean.MyNat.p6_IncreasingFunctions

namespace MyNat

theorem sum_zero (f : MyNat → MyNat) : sum f zero = zero := by
  rw [sum, sum.sumAux]

theorem sum_aux (f : MyNat → MyNat) (n a b : MyNat) :
sum.sumAux f n (a.add b) = (sum.sumAux f n a).add b := by
  induction n generalizing b with
  | zero =>
    simp only [sum.sumAux]
  | succ n ih =>
    simp only [sum.sumAux]
    rw [add_assoc]
    have eq1 := ih (b.add (f n))
    rw [eq1]
    specialize ih (f n)
    rw [ih]
    rw [add_assoc, add_comm (a := b)]

theorem sum_succ (f : MyNat → MyNat) (n : MyNat) :
sum f n.succ = (sum f n).add (f n) := by
  rw [sum, sum.sumAux, sum_aux, sum]

theorem sum_extract_first {n : MyNat} {f : MyNat → MyNat} :
sum f n.succ = add (f zero) (sum (fun x => f (x.succ)) n) := by
  induction n with
  | zero =>
    rw [sum_succ, sum_zero, zero_add, sum_zero, add_zero]
  | succ n ih =>
    rw [sum_succ, ih, add_assoc, sum_succ]

theorem sum_le_n {f g : MyNat → MyNat} {n : MyNat} :
  (∀ m : MyNat, (m.lt n → f m = g m)) → sum f n = sum g n := by
    induction n with
    | zero =>
      intro hm
      rw [sum_zero, sum_zero]
    | succ n ih =>
      intro hm
      rw [sum_succ, sum_succ]
      have eq1 := hm n
      have eq2 := lt_succ_self (n := n)
      rw [eq1 eq2, add_right_cancel]
      apply ih
      intro m eq3
      have eq4 := hm m
      exact eq4 (lt_trans eq3 eq2)

theorem sum_reverse_aux1 {f : MyNat → MyNat} {n : MyNat} :
sum (fun x => f (n.sub x).pred.succ) n =
sum (fun x => f (n.succ.sub x).pred) n := by
  set F1 : MyNat → MyNat := fun x => f (n.sub x).pred.succ with F1_def
  set F2 : MyNat → MyNat := fun x => f (n.succ.sub x).pred with F2_def
  have eq1 : ∀ m : MyNat, (m.lt n → F1 m = F2 m) := by
    intro m hm
    rw [F1_def, F2_def]
    simp
    have : (n.sub m).pred.succ = (n.succ.sub m).pred := by
      rcases hm with ⟨c, hm⟩
      rw [hm, add_sub_cancel_left,
          pred, ← add_succ, add_sub_cancel_left, pred]
    rw [this]
  exact sum_le_n eq1

theorem sum_reverse_aux2 {n : MyNat} :
∀ f : MyNat → MyNat, sum f n = sum (fun x => f ((n.sub x).pred)) n := by
  induction n with
  | zero =>
    intro f
    rw [sum_zero, sum_zero]
  | succ n ih =>
    intro f
    rw [sum_extract_first, sum_succ]
    have eq1 : f (n.succ.sub n).pred = f zero := by
      rw [← sub_succ, succ_sub_succ, sub_self]
    rw [eq1, add_comm, add_right_cancel]
    rw [ih]
    exact sum_reverse_aux1

theorem sum_reverse {f : MyNat → MyNat} {n : MyNat} :
sum f n = sum (fun x => f ((n.sub x).pred)) n := by
  exact sum_reverse_aux2 f

theorem sq_eq_sum_odd {n : MyNat} :
sum (fun x => (x.add x).add one) n = n.mul n := by
  induction n with
  | zero =>
    rw [sum_zero, mul_zero]
  | succ n ih =>
    rw [sum_succ, ih, add_one, add_succ,
        mul_succ, succ_mul, add_succ, add_assoc]

theorem add_sum {f g : MyNat → MyNat} {n : MyNat} :
(sum f n).add (sum g n) = sum (fun x => (f x).add (g x) ) n := by
  induction n with
  | zero =>
    simp only [sum_zero, add_zero]
  | succ n ih =>
    rw [sum_succ, sum_succ, sum_succ, add_assoc,
        ← add_assoc (a := f n), add_comm (a := f n),
        ← add_assoc, ← add_assoc, ih, ← add_assoc]

theorem num_mul_sum {f : MyNat → MyNat} {m n : MyNat} :
m.mul (sum f n) = sum (fun x => (m.mul (f x))) n := by
  induction n with
  | zero =>
    rw [sum_zero, sum_zero, mul_zero]
  | succ n ih =>
    rw [sum_succ, sum_succ, mul_add, ih]

theorem sum_const_eq_mul {m n : MyNat} :
sum (fun _ => m) n = m.mul n := by
  induction n with
  | zero =>
    rw [sum_zero, mul_zero]
  | succ n ih =>
    rw [sum_succ, ih, mul_succ]

theorem sum_one {n : MyNat} :
sum (fun _ => one) n = n := by
  have := sum_const_eq_mul (m := one) (n := n)
  rw [one_mul] at this
  exact this

theorem fun_eq_sum_sub_sum {f : MyNat → MyNat} {n : MyNat} :
f n = (sum f n.succ).sub (sum f n) := by
  rw [sum_succ, add_sub_cancel_left]

theorem telescope {f : MyNat → MyNat} {n : MyNat}
(h : nondecreasing f) :
 (f n).sub (f zero) = sum (fun x => (f x.succ).sub (f x)) n := by
  induction n with
  | zero =>
    rw [sum_zero, sub_self]
  | succ n ih =>
    rw [sum_succ, ← ih]
    clear ih
    have h' := nd_local_to_global.2 h
    rcases h zero n zero_le with ⟨c, hc⟩
    symm at hc
    rw [← add_imp_sub_left hc]
    rcases h' n with ⟨d, hd⟩
    symm at hd
    rw [← add_imp_sub_left hd]
    rw [← hc, add_assoc] at hd
    rw [add_imp_sub_left hd]

theorem tri_succ (n : MyNat) :
tri n.succ = n.tri.add n.succ := by
  rw [tri, sum_succ, id, ← tri]

theorem tri_zero : tri zero = zero := by
  rw [tri, sum_succ, sum_zero, id, add_zero]

theorem tri_one : tri one = one := by
  rw [one, tri_succ, tri_zero, zero_add]

theorem tri_two : tri two = three := by
  rw [two, tri_succ, tri_one, add_succ, one_add_one, three]

theorem tri_sub_tri {n : MyNat} :
(tri n).sub (tri n.pred) = n := by
  cases n
  case zero =>
    rw [pred, sub_self]
  case succ n =>
  rw [pred, tri_succ, add_sub_cancel_left]

theorem sum_le {f g : MyNat → MyNat} {n : MyNat}
(h : ∀ m : MyNat, m.lt n → (g m).le (f m)) :
(sum g n).le (sum f n) := by
  have eq1 : ∀ (m : MyNat), m.lt n → f m = ((g m).add ((f m).sub (g m))) := by
    intro m eq1
    specialize h m
    apply h at eq1
    rcases eq1 with ⟨c, eq1⟩
    nth_rewrite 2 [eq1]
    rw [add_sub_cancel_left, eq1]
  apply sum_le_n at eq1
  rw [← add_sum] at eq1
  use sum (fun m => (f m).sub (g m)) n

theorem sum_sub_sum {f g : MyNat → MyNat} {n : MyNat} :
(∀ m : MyNat, m.lt n → (g m).le (f m)) → (sum f n).sub (sum g n) =
sum (fun x => (f x).sub (g x)) n := by
  intro h
  have eq1 : ∀ (m : MyNat), m.lt n → f m = ((g m).add ((f m).sub (g m))) := by
    intro m eq1
    specialize h m
    apply h at eq1
    rcases eq1 with ⟨c, eq1⟩
    nth_rewrite 2 [eq1]
    rw [add_sub_cancel_left, eq1]
  apply sum_le_n at eq1
  rw [← add_sum] at eq1
  rw [eq1, add_sub_cancel_left]

theorem sum_eq_sum {f g : MyNat → MyNat} {n : MyNat} :
(∀ x, x.lt n → f x = g x) → sum f n = sum g n := by
  induction n with
  | zero =>
    intro _
    rw [sum_zero, sum_zero]
  | succ n ih =>
    intro h
    have eq1 : ∀ (x : MyNat), x.lt n → f x = g x := by
      intro x hx
      have := lt_trans hx lt_succ_self
      exact h x this
    rw [sum_succ, sum_succ]
    rw [ih eq1]
    rw [h n (lt_succ_self (n := n))]

theorem tri_inc : increasing tri := by
  rw [← inc_local_to_global]
  intro n
  rw [tri_succ]
  use n

end MyNat
