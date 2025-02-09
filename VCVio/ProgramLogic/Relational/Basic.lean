
/-!
# Relational program logic

This is a formalization of the paper
[The next 700 relational program logics](https://dl.acm.org/doi/pdf/10.1145/3371072).

We follow the paper as well as the Coq formalization in [SSProve](https://github.com/ssprove/ssprove).
-/

universe u v

namespace Monad

/-- Two monadic actions `ma : m α` and `mb : m β` are commutative if the following holds:
```
(do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b))
```
-/
class IsCommutativeAt (m : Type u → Type v) [Monad m] {α β : Type u} (ma : m α) (mb : m β) where
  bind_comm : (do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b))

/-- A monad is commutative if any two monadic actions `ma : m α` and `mb : m β` can be applied
  in any order. In other words, the following holds:
```
(do let a ← ma; let b ← mb; f (a, b)) = (do let b ← mb; let a ← ma; f (a, b))
```
-/
class IsCommutative (m : Type u → Type v) [Monad m] where
  bind_comm_comp {α β} (ma : m α) (mb : m β) : IsCommutativeAt m ma mb

export Monad.IsCommutative (bind_comm_comp)

attribute [simp] bind_comm_comp

-- TODO: add supporting lemmas

-- @[simp] theorem bind_comm_comp' {m} [Monad m] [IsCommutative m] {α β γ}
--     (ma : m α) (mb : m β) (f : α × β → m γ) :
--       (do let a ← ma; let b ← mb; f (a, b)) = (do let b ← mb; let a ← ma; f (a, b)) :=
--   bind_comm_comp ma mb (fun a b => f (a, b))

-- @[simp] theorem bind_comm {m} [Monad m] [IsCommutative m] {α β}
--     (ma : m α) (mb : m β) :
--       (do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b)) :=
--   bind_comm_comp' ma mb pure

-- @[simp] theorem pure_comm {m} [Monad m] [Monad.IsCommutative m] {α β}

end Monad

namespace Relational



end Relational
