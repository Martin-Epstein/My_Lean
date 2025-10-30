import Mathlib.Tactic.Tauto
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Use
import Mathlib.Tactic.ApplyAt

inductive Stack (α : Type*) where
  | empty  : Stack α
  | push : α → Stack α → Stack α

namespace Stack

protected def toString {α : Type*} [ToString α] (t : Stack α) : String :=
  match t with
  | empty => ""
  | push a as => toString a ++ " " ++ Stack.toString as

instance {α : Type*} [ToString α] : ToString (Stack α) where
  toString := Stack.toString

def pop {α : Type*} : Stack α → Option (α × Stack α)
  | empty => none
  | push a s => some (a, s)

def rev_append {α : Type*} : Stack α → Stack α → Stack α
| empty, s2 => s2
| push a s1, s2 => rev_append s1 (push a s2)

def reverse {α : Type*} (s : Stack α) :=
  rev_append s empty

def append {α : Type*} (s1 s2 : Stack α) :=
  rev_append (reverse s1) s2

def nonempty_eq_push {α : Type*} (s : Stack α) :
s ≠ (empty : Stack α) → ∃ (a : α) (t : Stack α), s = push a t := by
  intro h1
  cases h2 : s with
  | empty =>
    tauto
  | push a as =>
    use a, as

theorem reverse_pushAux {α : Type*} (as : Stack α) :
∀ (b : α) (bs : Stack α), rev_append as (push b bs) ≠ empty := by
  induction as with
  | empty =>
    intro b bs
    rw [rev_append]
    tauto
  | push a as ih =>
    intro b bs
    rw [rev_append]
    specialize ih a (push b bs)
    exact ih

theorem reverse_push {α : Type*} (a : α) (as : Stack α) :
∃ (b : α) (bs : Stack α), reverse (push a as) = push b bs := by
  have : (push a as).reverse ≠ empty := by
    apply reverse_pushAux
  apply nonempty_eq_push at this
  rcases this with ⟨b, bs, this⟩
  use b, bs

def list_to_stack {α : Type*} : List α → Stack α
  | []      => empty
  | a :: as => push a (list_to_stack as)

def combine {α : Type*} : Stack α → Stack α → Stack α
  | empty, t    => t
  | push a s, t => push a (combine s t)

end Stack

structure Queue (α : Type*) where
  front : Stack α
  back : Stack α

namespace Queue

protected def toString {α : Type*} [ToString α] (t : Queue α) : String :=
  "[ " ++ toString t.front ++ "] [ " ++ toString t.back ++ "]"

instance {α : Type*} [ToString α] : ToString (Queue α) where
  toString := Queue.toString

end Queue

open Stack

def enqueue {α : Type*} (a : α) (q : Queue α) : Queue α where
  front := q.front
  back  := push a q.back

def dequeue {α : Type*} (q : Queue α) : ((Option α) × Queue α) :=
  match q.front with
  | push a as =>
    (some a, {front := as
            , back  := q.back})
  | empty =>
    match reverse q.back with
    | push b bs =>
      (some b, {front := bs
              , back  := empty})
    | empty =>
      (none, {front := empty
            , back  := empty})

def Fib (n : ℕ) :=
  let rec FibAux : ℕ → (ℕ × ℕ) → (ℕ × ℕ)
    | 0, (a, b) => (a, b)
    | n + 1, (a, b) => FibAux n (b, a + b)
  (FibAux n (1, 0)).2

def hi := list_to_stack [1, 6, 2, 3, 8]
def bye := list_to_stack [4, 4, 5, 1, 3]

def q1 : Queue ℕ := {front := hi
                   , back  := bye}
def q2 := (dequeue q1).2
def q3 := (dequeue q2).2
def q4 := (dequeue q3).2
def q5 := (dequeue q4).2
def q6 := (dequeue q5).2
def q7 := (dequeue q6).2

#eval hi
#eval bye
#eval reverse bye
#eval combine hi bye
#eval append hi bye
#eval q5
#eval q6
#eval q7
