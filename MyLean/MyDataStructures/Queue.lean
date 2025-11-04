import MyLean.MyDataStructures.Stack
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation

structure Queue (α : Type*) where
  front : Stack α
  back : Stack α

namespace Queue

protected def toString {α : Type*} [ToString α] (t : Queue α) : String :=
  "[ " ++ toString t.front ++ "] [ " ++ toString t.back ++ "]"

instance {α : Type*} [ToString α] : ToString (Queue α) where
  toString := Queue.toString

def enqueue {α : Type*} (a : α) (q : Queue α) : Queue α where
  front := q.front
  back  := Stack.push a q.back

def dequeue {α : Type*} (q : Queue α) : ((Option α) × Queue α) :=
  match q.front with
  | Stack.push a as =>
    (some a, {front := as
            , back  := q.back})
  | Stack.empty =>
    match Stack.rev_tr q.back with
    | Stack.push b bs =>
      (some b, {front := bs
              , back  := Stack.empty})
    | Stack.empty =>
      (none, {front := Stack.empty
            , back  := Stack.empty})

def empty {α : Type*} : Queue α where
  front := Stack.empty
  back  := Stack.empty

end Queue
