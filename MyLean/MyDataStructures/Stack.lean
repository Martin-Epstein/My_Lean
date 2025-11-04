import Mathlib.Tactic.Tauto
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Use
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose

inductive Stack (α : Type*) where
  | empty : Stack α
  | push  : α → Stack α → Stack α

namespace Stack

-- Definitions

protected def toString {α : Type*} [ToString α] (t : Stack α) : String :=
  match t with
  | empty     => ""
  | push a as => toString a ++ " " ++ Stack.toString as

instance {α : Type*} [ToString α] : ToString (Stack α) where
  toString := Stack.toString


def pop {α : Type*} : Stack α → (Option α) × Stack α
  | empty    => (none, empty)
  | push a s => (some a, s)


def app {α : Type*} : Stack α → Stack α → Stack α
| empty, t    => t
| push a s, t => push a (app s t)

-- ptb = push to bottom
def ptb {α : Type*} : α → Stack α → Stack α
| a, empty    => push a empty
| a, push b s => push b (ptb a s)

def rev {α : Type*} : Stack α → Stack α
| empty    => empty
| push a s => ptb a (rev s)

def size {α : Type*} : Stack α → ℕ
| empty    => 0
| push _ s => size s + 1

def ind {α : Type*} : ℕ → Stack α → Option α
-- ind n s = the nth entry of the Stack s, or none
| _    , empty    => none
| 0    , push a _ => some a
| n + 1, push _ s => ind n s

def app_rev {α : Type*} : Stack α → Stack α → Stack α
| empty, t    => t
| push a s, t => app_rev s (push a t)

def list_to_stack {α : Type*} : List α → Stack α
| []      => empty
| a :: as => push a (list_to_stack as)

/- Functions defined below are tail-recursive variants
of functions defined above-/

def rev_tr {α : Type*} (s : Stack α) := app_rev s empty

def app_tr {α : Type*} (s1 s2 : Stack α) :=
  app_rev (rev_tr s1) s2

def size_tr {α : Type*} (s : Stack α) :=
  let rec aux : ℕ → Stack α → ℕ
    | acc, empty    => acc
    | acc, push _ s => aux (acc + 1) s
  aux 0 s

----------------------------------------
-- Equality with tail-recursive variants

theorem app_ptb_left {α : Type*} (a : α) (s t : Stack α) :
(ptb a s).app t = s.app (push a t) := by
  induction s with
  | empty =>
    rw [ptb, app, app, app]
  | push b s ih =>
    rw [ptb, app, ih, app]

theorem app_ptb_right {α : Type*} (a : α) (s t : Stack α) :
s.app (ptb a t) = ptb a (s.app t) := by
  induction s with
  | empty =>
    rw [app, app]
  | push b s ih =>
    rw [app, app, ptb, ih]

theorem app_rev_ptb_left {α : Type*}
(a : α) (s t : Stack α) :
app_rev (ptb a s) t = push a (app_rev s t) := by
  induction s generalizing t with
  | empty =>
    rw [ptb, app_rev, app_rev, app_rev]
  | push b s ih =>
    rw [ptb, app_rev, app_rev]
    exact ih (push b t)

theorem app_rev_ptb_right {α : Type*}
(a : α) (s t : Stack α) :
app_rev s (ptb a t) = ptb a (app_rev s t) := by
  induction s generalizing t with
  | empty =>
    rw [app_rev, app_rev]
  | push b s ih =>
    rw [app_rev, app_rev, ← ptb]
    exact ih (push b t)

theorem app_rev_eq {α : Type*} (s t : Stack α) :
s.app_rev t = s.rev.app t := by
  induction s generalizing t with
  | empty =>
    rw [app_rev, rev, app]
  | push b s ih =>
    rw [app_rev, rev, app_ptb_left]
    exact ih (push b t)

theorem app_empty {α : Type*} (s : Stack α) :
s.app empty = s := by
  induction s with
  | empty =>
    rw [app]
  | push a s ih =>
    rw [app, ih]

theorem rev_eq {α : Type*} (s : Stack α) :
s.rev_tr = s.rev := by
  have := app_rev_eq s empty
  rw [app_empty, ← rev_tr] at this
  exact this

theorem rev_ptb {α : Type*} (a : α) (s : Stack α) :
(ptb a s).rev = push a s.rev := by
  rw [← rev_eq, rev_tr, app_rev_ptb_left, ← rev_tr, rev_eq]

theorem rev_rev {α : Type*} (s : Stack α) :
s.rev.rev = s := by
  induction s with
  | empty =>
    rw [rev, rev]
  | push a s ih =>
    rw [rev, rev_ptb, ih]

theorem app_eq {α : Type*} (s t : Stack α) :
s.app_tr t = s.app t := by
  rw [app_tr, app_rev_eq, rev_eq, rev_rev]

----------------------
-- Theorems about size

theorem size_aux_succ {α : Type*} (n : ℕ) (s : Stack α) :
size_tr.aux (n + 1) s = size_tr.aux n s + 1 := by
  induction s generalizing n with
  | empty =>
    rw [size_tr.aux, size_tr.aux]
  | push a s ih =>
    rw [size_tr.aux, size_tr.aux]
    exact ih (n + 1)

theorem size_eq {α : Type*} (s : Stack α) :
s.size_tr = s.size := by
  induction s with
  | empty =>
    rw [size_tr, size_tr.aux, size]
  | push a s ih =>
    rw [size_tr, size_tr.aux, size_aux_succ, ← size_tr,
        size, ih]

theorem size_of_single {α : Type*} (a : α) :
size (push a empty) = 1 := by
  rw [size, size, Nat.zero_add]

theorem size_eq_zero_iff_empty {α : Type*} (s : Stack α) :
size s = 0 ↔ s = empty := by
  cases s with
  | empty =>
    rw [size]
    simp only
  | push a s =>
    rw [size]
    simp only [Nat.add_eq_zero, Nat.succ_ne_self,
               and_false, reduceCtorEq]

theorem size_of_ptb {α : Type*} (a : α) (s : Stack α) :
size (ptb a s) = size s + 1 := by
  induction s with
  | empty =>
    rw [ptb, size_of_single, size, Nat.zero_add]
  | push b s ih =>
    rw [ptb, size, size, ih]

theorem size_of_rev {α : Type*} (s : Stack α) :
size s.rev = size s := by
  induction s with
  | empty =>
    rw [rev]
  | push a s ih =>
    rw [rev, size_of_ptb, size, ih]

theorem size_of_app {α : Type*} (s t : Stack α) :
size (s.app t) = size s + size t := by
  induction s with
  | empty =>
    rw [app, size, Nat.zero_add]
  | push a s ih =>
    rw [app, size, size, ih, Nat.add_right_comm]

theorem size_of_app_rev {α : Type*} (s t : Stack α) :
size (s.app_rev t) = size s + size t := by
  induction s generalizing t with
  | empty =>
    rw [app_rev, size, Nat.zero_add]
  | push a s ih =>
    rw [app_rev, size]
    specialize ih (push a t)
    rw [ih, size]; omega

theorem size_ne_zero_iff_exists_push {α : Type*}
(s : Stack α) : s.size ≠ 0 ↔
∃ (a : α) (t : Stack α), s = push a t := by
  constructor
  · intro h
    rw [ne_eq, size_eq_zero_iff_empty] at h
    cases s with
    | empty => contradiction
    | push b s =>
      use b; use s
  intro h
  rcases h with ⟨a, t, h⟩
  rw [h, size]; omega

theorem size_ne_zero_iff_exists_ptb {α : Type*}
(s : Stack α) : s.size ≠ 0 ↔
∃ (a : α) (t : Stack α), s = ptb a t := by
  induction s with
  | empty =>
    rw [size]
    constructor
    · tauto
    intro h
    rcases h with ⟨a, t, h⟩
    have : size (empty : Stack α) = size (ptb a t) := by rw [h]
    rw [size, size_of_ptb] at this
    omega
  | push b s ih =>
    rw [size]
    constructor
    · intro h; clear h
      cases s with
      | empty =>
        use b
        use empty
        rw [ptb]
      | push a s =>
        rcases ih with ⟨h, -⟩
        rw [size] at h
        have h2 : s.size + 1 ≠ 0 := by omega
        apply h at h2
        rcases h2 with ⟨c, t, h⟩
        rw [h, ← ptb]
        use c
        use push b t
    omega

theorem exists_push_of_ptb {α : Type*} (a : α) (s : Stack α) :
∃ (b : α) (t : Stack α), push b t = ptb a s := by
  have h1 : size (ptb a s) ≠ 0 := by
    rw [size_of_ptb]; omega
  rw [size_ne_zero_iff_exists_push] at h1
  rcases h1 with ⟨b, t, h1⟩
  use b
  use t
  rw [h1]

--------------------------
-- Theorems about indexing

theorem eq_of_ind_eq {α : Type*} (s t : Stack α)
(h : ∀ n : ℕ, ind n s = ind n t) : s = t := by
  induction s generalizing t with
  | empty =>
    specialize h 0
    rw [ind] at h
    cases t with
    | empty => rfl
    | push b t =>
      rw [ind] at h
      tauto
  | push a s ih =>
    cases t with
    | empty =>
      specialize h 0
      simp only [ind] at h
      tauto
    | push b t =>
      have h2 := h 0
      simp only [ind, Option.some.injEq] at h2
      rw [h2]
      specialize ih t
      have h3 : ∀ (n : ℕ), ind n s = ind n t := by
        intro n
        specialize h (n + 1)
        rw [ind, ind] at h
        exact h
      apply ih at h3
      rw [h3]

theorem ind_of_sizeAux {α : Type*} (n : ℕ) (s : Stack α)
(sn : size s = n) :
ind n s = none := by
  induction n generalizing s with
  | zero =>
    rw [size_eq_zero_iff_empty] at sn
    rw [sn, ind]
  | succ n ih =>
    cases s with
    | empty =>
      symm at sn
      rw [size, Nat.add_eq_zero] at sn
      tauto
    | push a s =>
      rw [size] at sn
      apply Nat.add_right_cancel at sn
      rw [ind]
      exact ih s sn

theorem ind_of_size {α : Type*} (s : Stack α) :
ind (size s) s = none := by
  have := ind_of_sizeAux (n := size s) (s := s)
  tauto

theorem ind_of_lt_size {α : Type*} (n : ℕ) (s : Stack α)
(sn : n < size s) : ind n s ≠ none := by
  induction s generalizing n with
  | empty =>
    rw [size] at sn; tauto
  | push a s ih =>
    rw [size] at sn
    cases n with
    | zero =>
      rw [ind]; tauto
    | succ n =>
      simp only [Nat.add_lt_add_iff_right] at sn
      rw [ind]
      exact ih n sn

theorem ind_succ_none_of_ind_none {α : Type*}
(n : ℕ) (s : Stack α) (h : ind n s = none) :
ind (n + 1) s = none := by
  induction n generalizing s with
  | zero =>
    cases s with
    | empty =>
      rw [ind]
    | push a s =>
      rw [ind] at h; tauto
  | succ n ih =>
    cases s with
    | empty => rw [ind]
    | push a s =>
      rw [ind]
      rw [ind] at h
      exact ih s h

theorem ind_of_gt_size {α : Type*} (n : ℕ) (s : Stack α)
(sn : size s < n) : ind n s = none := by
  have h1 : ∀ c : ℕ, ind (size s + c) s = none := by
    intro c
    induction c generalizing s with
    | zero =>
      rw [Nat.add_zero]
      apply ind_of_size
    | succ c ih =>
      rw [← Nat.add_assoc]
      apply ind_succ_none_of_ind_none
      exact ih s sn
  apply Nat.exists_eq_add_of_lt at sn
  rcases sn with ⟨k, sn⟩
  rw [sn, Nat.add_assoc]
  exact h1 (k + 1)

theorem ind_size_of_ptb {α : Type*} (a : α) (s : Stack α) :
ind (size s) (ptb a s) = a := by
  induction s with
  | empty =>
    rw [size, ptb, ind]
  | push b s ih =>
    rw [size, ptb, ind, ih]

theorem ind_lt_size_of_ptb {α : Type*}
(n : ℕ) (a : α) (s : Stack α) (sn : n < size s) :
ind n (ptb a s) = ind n s := by
  induction s generalizing n with
  | empty =>
    rw [size] at sn; tauto
  | push b s ih =>
    rw [ptb]
    rw [size] at sn
    cases n with
    | zero =>
      rw [ind, ind]
    | succ n =>
      rw [ind, ind]
      rw [Nat.add_lt_add_iff_right] at sn
      exact ih n sn

theorem ind_of_rev {α : Type*} (s : Stack α) (n : ℕ)
(sn : n < size s) : ind n s =
ind (size s - 1 - n) s.rev := by
  induction n generalizing s with
  | zero =>
    cases s with
    | empty =>
      rw [size] at sn; tauto
    | push a s =>
      rw [rev, Nat.sub_zero, ind, size, Nat.add_sub_cancel,
          ← size_of_rev, ind_size_of_ptb]
  | succ n ih =>
    cases s with
    | empty =>
      rw [size] at sn; tauto
    | push b s =>
      rw [size, Nat.add_lt_add_iff_right] at sn
      have h1 := ih s sn
      rw [ind, size, Nat.add_sub_cancel, h1, rev,
          Nat.sub_sub, Nat.add_comm]
      cases s with
      | empty =>
        rw [size] at sn; tauto
      | push c s =>
        have h2 : (push c s).size - (n + 1) < (push c s).rev.size := by
          rw [size_of_rev, size]
          omega
        have h3 := ind_lt_size_of_ptb
          (n := (push c s).size - (n + 1))
          (a := b) (s := (push c s).rev) h2
        rw [h3]

theorem ind_app_left {α : Type*} (n : ℕ) (s t : Stack α)
(sn : n < s.size) : ind n (s.app t) = ind n s := by
  induction s generalizing n with
  | empty =>
    rw [size] at sn; tauto
  | push a s ih =>
    rw [size] at sn
    rw [app]
    cases n with
    | zero =>
      rw [ind, ind]
    | succ n =>
      rw [ind, ind]
      simp only [Nat.add_lt_add_iff_right] at sn
      exact ih n sn

theorem ind_of_rev' {α : Type*} (n : ℕ) (s : Stack α)
(h : n < s.size) :
ind n s.rev = ind (s.size - 1 - n) s := by
  rw [← size_of_rev] at h
  have h2 := ind_of_rev (n := n) (s := s.rev) h
  rw [rev_rev, size_of_rev] at h2
  exact h2

theorem ind_size_left_of_app {α : Type*} (a : α)
(s t : Stack α) : ind s.size (s.app (push a t)) = a := by
  induction s with
  | empty =>
    rw [size, app, ind]
  | push b s ih =>
    rw [size, app, ind]
    exact ih

theorem app_rev_exists {α : Type*} (s t : Stack α) :
∃ r : Stack α, s.app_rev t = r.app t := by
  induction s generalizing t with
  | empty =>
    use empty
    rw [app_rev, app]
  | push a s ih =>
    rw [app_rev]
    specialize ih (push a t)
    rcases ih with ⟨q, ih⟩
    rw [ih]
    use ptb a q
    rw [app_ptb_left]

theorem ind_eq_size_of_app_rev {α : Type*}
(a : α) (s t : Stack α) :
ind s.size ((push a s).app_rev t) = a := by
  rw [app_rev]
  have h1 := app_rev_exists (s := s) (t := push a t)
  rcases h1 with ⟨r, h1⟩
  have h2 : s.size = r.size := by
    have h2 : size (s.app_rev (push a t)) =
    size (r.app (push a t)) := by
      rw [h1]
    rw [size_of_app_rev, size_of_app,
        Nat.add_right_cancel_iff] at h2
    exact h2
  rw [h1, h2, ind_size_left_of_app]

theorem size_of_app_eq_app_rev {α : Type*}
(r s t : Stack α) (h : r.app t = s.app_rev t) :
size r = size s := by
  have h1 :size (r.app t) = size (s.app_rev t) := by
    rw [h]
  rw [size_of_app, size_of_app_rev,
      Nat.add_right_cancel_iff] at h1
  exact h1

end Stack
