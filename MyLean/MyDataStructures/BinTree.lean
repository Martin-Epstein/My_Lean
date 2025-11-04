import MyLean.MyDataStructures.Queue
import Mathlib.Tactic.Tauto
import Mathlib.Data.Prod.Basic

set_option linter.unusedVariables false

inductive BinTree (α : Type*) where
  | empty : BinTree α
  | node  : α → BinTree α → BinTree α → BinTree α

namespace BinTree

protected def toString {α : Type*} [ToString α] (t : BinTree α) : String :=
  match t with
  | empty => ""
  | node a left right => toString a ++ " ( " ++
    BinTree.toString left ++
    " ) ( " ++ BinTree.toString right ++ " )"

instance {α : Type*} [ToString α] : ToString (BinTree α) where
  toString := BinTree.toString

def size {α : Type*} : BinTree α → ℕ
  | empty      => 0
  | node _ left right => 1 + size left + size right

-- Size including empty children
def size' {α : Type*} : BinTree α → ℕ
  | empty => 1
  | node _ left right =>
    1 + size' left + size' right

-- SBS = Size of BinTree Stack
def SBS {α : Type*} : Stack (BinTree α) → ℕ
  | Stack.empty => 0
  | Stack.push q qs =>
    size q + SBS qs

def SBS' {α : Type*} : Stack (BinTree α) → ℕ
  | Stack.empty => 0
  | Stack.push q qs =>
    size' q + SBS' qs

-- SBQ = Size of BinTree Queue
def SBQ {α : Type*} (q : Queue (BinTree α)) :=
  SBS (q.front) + SBS (q.back)

def SBQ' {α : Type*} (q : Queue (BinTree α)) :=
  SBS' (q.front) + SBS' (q.back)

def height {α : Type*} : BinTree α → ℕ
  | empty      => 0
  | node _ left right =>
    1 + max (height left) (height right)

def Bi_to_List_df {α : Type*} : BinTree α → List α
  | empty => []
  | node a left right =>
    Bi_to_List_df left ++ a :: Bi_to_List_df right

theorem size_of_app
{α : Type*} (s1 s2 : Stack (BinTree α)) :
SBS (s1.app s2) = SBS s1 + SBS s2 := by
  induction s1 with
  | empty =>
    rw [SBS, Nat.zero_add, Stack.app]
  | push b q1 h =>
  rw [Stack.app, SBS, h, SBS,
      Nat.add_assoc]

theorem size_of_app'
{α : Type*} (s1 s2 : Stack (BinTree α)) :
SBS' (s1.app s2) = SBS' s1 + SBS' s2 := by
  induction s1 with
  | empty =>
    rw [SBS', Nat.zero_add, Stack.app]
  | push b q1 h =>
    rw [Stack.app, SBS', h, SBS', Nat.add_assoc]

theorem size_of_ptb {α : Type*}
(a : BinTree α) (s : Stack (BinTree α)) :
SBS (Stack.ptb a s) = SBS s + size a := by
  induction s with
  | empty =>
    rw [Stack.ptb, SBS, SBS, SBS, Nat.add_zero, Nat.zero_add]
  | push b s ih =>
    rw [Stack.ptb, SBS, SBS, ih]; omega

theorem size_of_ptb' {α : Type*}
(a : BinTree α) (s : Stack (BinTree α)) :
SBS' (Stack.ptb a s) = SBS' s + size' a := by
  induction s with
  | empty =>
    rw [Stack.ptb, SBS', SBS', SBS',
        Nat.add_zero, Nat.zero_add]
  | push b s ih =>
    rw [Stack.ptb, SBS', SBS', ih]; omega

theorem size_of_rev {α : Type*} (q : Stack (BinTree α)) :
SBS q.rev_tr = SBS q := by
  rw [Stack.rev_eq]
  induction q with
  | empty =>
    rw [Stack.rev, SBS]
  | push a as ih =>
    rw [SBS, ← ih, Stack.rev, size_of_ptb, Nat.add_comm]

theorem size_of_rev' {α : Type*} (q : Stack (BinTree α)) :
SBS' q.rev_tr = SBS' q := by
  rw [Stack.rev_eq]
  induction q with
  | empty =>
    rw [Stack.rev, SBS']
  | push a as ih =>
    rw [SBS', ← ih, Stack.rev, size_of_ptb', Nat.add_comm]

theorem size_ne_zero' {α : Type*} (b : BinTree α) :
size' b ≠ 0 := by
  cases b with
  | empty =>
    rw [size']; tauto
  | node a l r =>
    rw [size']
    simp only [ne_eq, Nat.add_eq_zero, Nat.succ_ne_self,
               false_and, not_false_eq_true]

theorem SBS_eq_zero_iff_empty' {α : Type*}
(s : Stack (BinTree α)) :
SBS' s = 0 ↔ s = Stack.empty := by
  constructor
  · intro h
    cases s with
    | empty => rfl
    | push a s =>
      rw [SBS', Nat.add_eq_zero] at h
      rcases h with ⟨h, -⟩
      have h2 := size_ne_zero' a
      contradiction
  intro h
  rw [h, SBS']

def breadthFirstAux {α : Type*} (acc : List α)
(q : Queue (BinTree α)) :=
  match h : Queue.dequeue q with
  | (none, _) => acc
  | (some a, p) => match a with
    | empty => breadthFirstAux acc p
    | node a l r => breadthFirstAux
        (a :: acc) (Queue.enqueue r (Queue.enqueue l p))
termination_by SBQ' q

decreasing_by
  · cases q with
    | mk front back =>
      cases front with
      | empty =>
        cases back with
        | empty =>
          rw [SBQ', SBQ', SBS', Nat.add_zero]
          rw [Queue.dequeue] at h
          dsimp at h
          rw [Stack.rev_tr, Stack.app_rev] at h
          dsimp at h
          rw [Prod.mk_inj] at h; tauto
        | push b back =>
          nth_rewrite 2 [SBQ']
          rw [SBS', SBS', Nat.zero_add]
          rw [Queue.dequeue] at h
          dsimp at h
          rw [Stack.rev_eq, Stack.rev] at h
          have := Stack.exists_push_of_ptb
            (a := b) (s := back.rev)
          rcases this with ⟨c, s, h2⟩
          rw [← h2] at h
          dsimp at h
          rw [Prod.mk_inj] at h
          rcases h with ⟨h3, h4⟩
          rw [Option.some_inj] at h3
          rw [← h4, SBQ', SBS', Nat.add_zero]
          dsimp
          apply Nat.lt_of_lt_of_le (m := size' c + SBS' s)
          · rw [Nat.lt_add_left_iff_pos]
            have h5 := size_ne_zero' c
            omega
          have h5 : SBS' (Stack.push c s) =
            SBS' (Stack.ptb b back.rev) := by rw [h2]
          rw [SBS', size_of_ptb', ← Stack.rev_eq,
              size_of_rev'] at h5
          rw [h5, Nat.add_comm]
          apply Nat.le_refl
      | push b front =>
        rw [Queue.dequeue] at h
        dsimp at h
        rw [Prod.mk_inj] at h
        rcases h with ⟨h1, h2⟩; clear h
        rw [Option.some_inj] at h1
        rw [h1, ← h2]; simp only [SBQ', SBS']
        rw [size']
        omega
  rw [Queue.enqueue, Queue.enqueue, SBQ', SBQ']
  dsimp
  rw [SBS', SBS']
  cases q with
  | mk front back =>
    cases front with
    | empty =>
      cases back with
      | empty =>
        rw [Queue.dequeue] at h
        dsimp at h
        rw [Stack.rev_tr, Stack.app_rev] at h
        dsimp at h
        rw [Prod.mk_inj] at h
        tauto
      | push c back =>
        rw [Queue.dequeue] at h
        dsimp at h
        rw [Stack.rev_eq, Stack.rev] at h
        have h2 := Stack.exists_push_of_ptb (a := c) back.rev
        rcases h2 with ⟨b, s, h2⟩
        rw [← h2] at h
        dsimp at h
        rw [Prod.mk_inj, Option.some_inj] at h
        rcases h with ⟨h3, h4⟩; clear h
        rw [← h4]
        dsimp
        rw [SBS', Nat.add_zero, Nat.zero_add, SBS']
        have h5 : SBS' (Stack.push b s) =
          SBS' (Stack.ptb c back.rev) := by rw [h2]
        rw [SBS', size_of_ptb', ← Stack.rev_eq,
            size_of_rev', h3, size'] at h5
        rw [Nat.add_comm (n := c.size'), ← h5]
        omega
    | push b front =>
      dsimp
      rw [Queue.dequeue] at h
      dsimp at h
      rw [Prod.mk_inj, Option.some_inj] at h
      rcases h with ⟨h1, h2⟩; clear h
      rw [← h2, h1]
      dsimp
      rw [SBS', size']
      omega

def Bi_to_List_bf {α : Type*} : BinTree α → List α
  | b => List.reverse (breadthFirstAux
      [] (Queue.enqueue b Queue.empty))

end BinTree
