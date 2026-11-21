import ContinuationTut.Core

/-!
# 3. Lean の Monad に登録
-/

namespace ContinuationTut

instance {R : Type r} : Monad (Cont R) where
  pure := Cont.pure
  bind := Cont.bind

namespace MonadDemo

def arithmetic : Cont Nat Nat := do
  let a ← pure 3
  let b ← pure (a + 1)
  return b * 2

def arithmeticExplicit : Cont Nat Nat :=
  .bind (.pure 3) fun a ↦
    .bind (.pure (a + 1)) fun b ↦
      .pure (b * 2)

theorem do_is_bind : arithmetic = arithmeticExplicit := by
  rfl

def withLocalLet : Cont Nat Nat := do
  let a ← pure 3
  let b := a + 1
  pure <| b * 2

#eval Cont.finish arithmetic -- 8
#eval Cont.run arithmetic (fun n ↦ n + 100) -- 108
#guard Cont.finish arithmetic == 8
#guard Cont.run arithmetic (fun n ↦ n + 100) == 108
#guard Cont.finish withLocalLet == 8


end MonadDemo


end ContinuationTut
