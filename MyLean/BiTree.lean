import MyLean.Queue
import Mathlib.Tactic.Tauto
import Mathlib.Data.Prod.Basic

set_option linter.unusedVariables false

inductive BiTree (α : Type*) where
  | empty : BiTree α
  | node  : α → BiTree α → BiTree α → BiTree α

namespace BiTree

open Queue

protected def toString {α : Type*} [ToString α] (t : BiTree α) : String :=
  match t with
  | empty => ""
  | node a left right => toString a ++ " ( " ++
    BiTree.toString left ++
    " ) ( " ++ BiTree.toString right ++ " )"

instance {α : Type*} [ToString α] : ToString (BiTree α) where
  toString := BiTree.toString

def size {α : Type*} : BiTree α → ℕ
  | empty      => 0
  | node _ left right => 1 + size left + size right

def height {α : Type*} : BiTree α → ℕ
  | empty      => 0
  | node _ left right => 1 + max (height left) (height right)

def Bi_to_List_df {α : Type*} : BiTree α → List α
  | empty => []
  | node a left right => Bi_to_List_df left ++ a :: Bi_to_List_df right

def size_with_empty {α : Type*} : BiTree α → ℕ
  | empty => 1
  | node _ left right => 1 + size_with_empty left + size_with_empty right

def List_BiTree_size {α : Type*} : List (BiTree α) → ℕ
  | [] => 0
  | q :: qs => size_with_empty q + List_BiTree_size qs

def Queue_BiTree_size {α : Type*} : Queue (BiTree α) → ℕ
  | Queue.empty           => 0
  | mk q front back => size_with_empty q +
                        List_BiTree_size front +
                        List_BiTree_size back

theorem LBs_dist {α : Type*} (q1 q2 : List (BiTree α)) :
List_BiTree_size (q1.append q2) = List_BiTree_size q1 + List_BiTree_size q2 := by
  induction q1 with
  | nil =>
    rw [List_BiTree_size, Nat.zero_add, List.append]
  | cons b q1 h =>
  rw [List.append, List_BiTree_size, h, List_BiTree_size, Nat.add_assoc]

theorem LBs_reverse {α : Type*} (q : List (BiTree α)) :
List_BiTree_size q = List_BiTree_size q.reverse := by
  induction q with
  | nil =>
    rw [List.reverse, List.reverseAux]
  | cons a as ih =>
  rw [List_BiTree_size, ih, List.reverse_cons, ← List.append_eq, LBs_dist,
      List_BiTree_size, List_BiTree_size, Nat.add_zero, Nat.add_comm]

def breadthFirstAux {α : Type*} : Queue (BiTree α) → List α → List α
  | q, out =>
    match h : dequeue q with
    | none => out.reverse
    | some (BiTree.empty, q') =>
        breadthFirstAux q' out
    | some (node a l r, q') =>
        breadthFirstAux (enqueue (enqueue q' l) r) (a :: out)
termination_by q _ => Queue_BiTree_size q

decreasing_by
  cases q with
  | empty =>
    rw [dequeue] at h
    tauto
  | mk a front back =>
    cases front with
    | nil =>
      cases back with
      | nil =>
        rw [dequeue] at h
        cases h
        rw [Queue_BiTree_size, Queue_BiTree_size,
            size_with_empty]
        omega
      | cons b bs =>
        rw [dequeue] at h
        cases hrev : (b :: bs).reverse with
        | nil =>
          rw [List.reverse_eq_nil_iff] at hrev
          tauto
        | cons c cs =>
          rw [Queue_BiTree_size, List_BiTree_size,
              Nat.add_zero, LBs_reverse, hrev, List_BiTree_size]
          rw [hrev, Option.some_inj, Prod.mk_inj] at h
          rcases h with ⟨h1, h2⟩
          rw [h1, size_with_empty, ← h2, Queue_BiTree_size,
              List_BiTree_size, Nat.add_zero]
          omega
    | cons b bs =>
      rw [dequeue, Option.some_inj, Prod.mk_inj] at h
      rcases h with ⟨h1, h2⟩
      rw [h1, ← h2, Queue_BiTree_size, Queue_BiTree_size,
          size_with_empty, List_BiTree_size]
      omega
  cases q with
  | empty =>
    rw [dequeue] at h
    tauto
  | mk b front back =>
    rw [Queue_BiTree_size]
    cases front with
    | nil =>
      cases back with
      | nil =>
        rw [dequeue, Option.some_inj, Prod.mk_inj] at h
        rcases h with ⟨h1, h2⟩
        rw [h1, ← h2, enqueue, enqueue, Queue_BiTree_size]
        simp only [List_BiTree_size, Nat.add_zero, size_with_empty]
        omega
      | cons c cs =>
        rw [List_BiTree_size, Nat.add_zero]
        rw [dequeue] at h
        cases hrev : (c :: cs).reverse with
        | nil =>
          rw [List.reverse_eq_nil_iff] at hrev
          tauto
        | cons d ds =>
          rw [hrev, Option.some_inj, Prod.mk_inj] at h
          rcases h with ⟨h1, h2⟩
          rw [LBs_reverse, hrev, h1, ← h2,
              enqueue, enqueue, Queue_BiTree_size]
          simp only [List_BiTree_size]
          rw [Nat.add_zero, size_with_empty]
          omega
    | cons c cs =>
      rw [dequeue, Option.some_inj, Prod.mk_inj] at h
      rcases h with ⟨h1, h2⟩
      rw [h1, ← h2, enqueue, enqueue, Queue_BiTree_size, size_with_empty]
      simp only [List_BiTree_size]
      omega

def Bi_to_List_bf {α : Type*} : BiTree α → List α
  | b => breadthFirstAux (Queue.mk b [] []) []

end BiTree

open BiTree

#eval Queue.mk 3 [1, 3, 5] [5, 2, 2]

def mytree1 := BiTree.node 2 (node 3 empty empty) (node 5 empty empty)
def mytree2 := node 6 (node 8 empty mytree1) (node 7 empty mytree1)

def empty_q := (Queue.empty : Queue (BiTree ℕ))

def myqueue1 := Queue.enqueue empty_q mytree1
def myqueue2 := Queue.enqueue myqueue1 mytree2

#eval mytree1
#eval mytree2

#eval size mytree1
#eval size mytree2
#eval size_with_empty mytree1
#eval size_with_empty mytree2

#eval Bi_to_List_df mytree2
#eval Bi_to_List_bf mytree2
