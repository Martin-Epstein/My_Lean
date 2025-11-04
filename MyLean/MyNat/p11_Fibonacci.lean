import MyLean.MyNat.p10_Division

namespace MyNat

def Fib : MyNat → MyNat
| zero => zero
| succ zero => succ zero
| succ (succ n) => (Fib n).add (Fib n.succ)

def Fib' (n : MyNat) :=
  let rec aux : MyNat → MyNat → MyNat → MyNat
    | zero, _, b => b
    | succ n , a , b => aux n b (a.add b)
  aux n one zero

theorem Fib_aux (n a b c d : MyNat) :
(Fib'.aux n a b).add (Fib'.aux n c d) =
Fib'.aux n (a.add c) (b.add d) := by
  induction n generalizing a b c d with
  | zero =>
    simp only [Fib'.aux]
  | succ n ih =>
    simp only [Fib'.aux]
    rw [ih b (a.add b) d (c.add d), add_assoc,
        ← add_assoc (a := b), add_comm (a := b) (b := c),
        add_assoc, add_assoc]

theorem Fib_eq (n : MyNat) : Fib n = Fib' n := by
  apply strong_induction (P := fun x => x.Fib = x.Fib')
  intro n ih
  cases n with
  | zero =>
    rw [Fib, Fib', Fib'.aux]
  | succ n =>
    cases n with
    | zero =>
      rw [Fib, Fib', Fib'.aux, add_zero, Fib'.aux, one]
    | succ n =>
      have j1 : n.succ.lt n.succ.succ := by
        apply lt_succ_self
      have h1 := ih n.succ j1
      have j2 : n.lt n.succ.succ := by
        apply lt_trans (b := n.succ)
        · apply lt_succ_self
        exact j1
      have h2 := ih n j2; clear j1; clear j2
      rw [Fib, Fib', Fib'.aux, Fib'.aux, add_zero, zero_add,
          h1, h2, Fib', Fib', Fib'.aux, add_zero]
      have := Fib_aux (n := n) (a := one) (b := zero)
            (c := zero) (d := one)
      rw [this, add_zero, zero_add]

end MyNat
