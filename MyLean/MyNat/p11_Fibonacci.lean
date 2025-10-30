import MyLean.MyNat.p10_Division

namespace MyNat

def Fib (n : MyNat) :=
  let rec FibAux : MyNat → (MyNat × MyNat) → (MyNat × MyNat)
    | zero, (a, b) => (a, b)
    | succ n, (a, b) => FibAux n (b, a.add b)
  (FibAux n (one, zero)).2

end MyNat
