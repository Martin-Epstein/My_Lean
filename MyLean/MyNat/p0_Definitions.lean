import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Set

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

--------------
-- Definitions

def to_N (n : MyNat) :=
-- Convert MyNat to the equivalent natural number
-- e.g. to_N (succ succ zero) = 2
  let rec to_NAux : MyNat → ℕ → (MyNat × ℕ)
    | zero, n => (zero, n)
    | succ m, n => to_NAux m (n + 1)
  (to_NAux n 0).2

protected def toString [ToString Nat] (t : MyNat) : String :=
  toString (to_N t)

instance [ToString Nat] : ToString MyNat where
  toString := MyNat.toString

def one : MyNat := succ zero

def two : MyNat := succ one

def three : MyNat := succ two

def iterate : (MyNat → MyNat) → MyNat → MyNat → MyNat
-- iterate f m n applies f m times to n
-- e.g. iterate f 3 n = f (f (f n))
  | _, zero, n => n
  | f, succ m, n => iterate f m (f n)

def add (m n : MyNat) := iterate succ n m

def sum (f : MyNat → MyNat) (n : MyNat) :=
-- sum values of f from f 0 to f (n - 1)
-- e.g. sum f 3 = f 0 + f 1 + f 2
  let rec sumAux : MyNat → MyNat → MyNat
    | zero, acc => acc
    | succ n, acc => sumAux n (add acc (f n))
  sumAux n zero

def mul (m n : MyNat) := iterate (fun x => add x m) n zero

def prod (f : MyNat → MyNat) (n : MyNat) :=
  let rec prodAux : MyNat → MyNat → MyNat
    | zero, acc => acc
    | succ n, acc => prodAux n (mul acc (f n))
  prodAux n one

def pred : MyNat → MyNat
  | zero => zero
  | succ x => x

def sub : MyNat → MyNat → MyNat
  | m, n => iterate pred n m

def le (x y : MyNat) : Prop := ∃ z, y = x.add z

def lt (x y : MyNat) : Prop := ∃ z : MyNat, y = x.add z.succ

def ge (x y : MyNat) : Prop := y.le x

def gt (x y : MyNat) : Prop := y.lt x

def tri : MyNat → MyNat
  | n => sum id n.succ

def fact : MyNat → MyNat
  | n => prod (fun x => x.succ) n

def pow : MyNat → MyNat → MyNat
  | m, n => iterate (fun x => x.mul m) n one

def dvd (a b : MyNat) : Prop := ∃ c, a.mul c = b

def increasing_local (f : MyNat → MyNat) :
Prop := ∀ n, (f n).lt (f n.succ)

def increasing (f : MyNat → MyNat) :
Prop := ∀ m n, m.lt n → (f m).lt (f n)

def nondecreasing_local (f : MyNat → MyNat) :
Prop := ∀ n, (f n).le (f n.succ)

def nondecreasing (f : MyNat → MyNat) :
Prop := ∀ m n, m.le n → (f m).le (f n)

def min (P : MyNat → Prop) (m : MyNat) : Prop :=
P m ∧ ∀ n, P n → m.le n

def satisfiable (P : MyNat → Prop) : Prop :=
∃ m, P m

end MyNat
