import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation

inductive Queue (α : Type*) where
  | empty : Queue α
  | mk : α → List α → List α → Queue α

namespace Queue

protected def toString {α : Type*} [ToString α] (t : Queue α) : String :=
  match t with
  | empty => "queue [] []"
  | mk a front back => "queue " ++ toString (a :: front) ++ " " ++ toString back

instance {α : Type*} [ToString α] : ToString (Queue α) where
  toString := Queue.toString

def enqueue {α : Type*} : Queue α → α → Queue α
  | empty, a              => mk a [] []
  | mk head front back, a => mk head front (a :: back)

def last {α : Type*} : α → List α → α
  | a, [] => a
  | _, (b :: bs) => last b bs

def dequeue {α : Type*} : Queue α → Option (α × Queue α)
  | empty             => none
  | mk a [] [] => some (a, empty)
  | mk a (b :: bs) back => some (a, mk b bs back)
  | mk a [] (b :: bs) =>
      let rev := (b :: bs).reverse
      match rev with
      | [] => none
      | c :: cs => some (a, mk c cs [])

end Queue

open Queue

#eval (Queue.empty : Queue Nat)

def blah {α : Type*} : Option (α × Queue α) → Option (α × Queue α)
  | none => none
  | some (_, aq) => dequeue aq

def q0 := mk 2 [3, 5, 6] [3, 2, 1]
def q1 := dequeue q0
def q2 := blah q1
def q3 := blah q2
def q4 := blah q3
def q5 := blah q4

#eval q0
#eval q1
#eval q2
#eval q3
#eval q4
#eval q5
