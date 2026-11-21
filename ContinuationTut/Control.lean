import ContinuationTut.Monad

/-!
# 4. 継続を複数回使う

-/

namespace ContinuationTut
namespace Control

/-- 残りの計算を使わず答えのみを返す -/
def abort {R A : Type} (answer : R) : Cont R A :=
  fun _k ↦ answer

def stopped : Cont Nat Nat := do
  let x ← abort 99
  pure (x + 1000)

#eval Cont.finish stopped -- 99
#guard Cont.finish stopped == 99

/-- 継続を2回使用し、それぞれの答えのリストを連結する -/
def choose {R A : Type} (a b : A) : Cont (List R) A :=
  fun k ↦ k a ++ k b

def combinations : Cont (List Nat) Nat := do
  let x ← choose 1 2
  let y ← choose 10 20
  pure (x + y)

#eval Cont.run combinations (fun n ↦ [n])
#guard Cont.run combinations (fun n ↦ [n]) == [11, 21, 12, 22]

def callCC {R A B : Type}
  (f : (A → Cont R B) → Cont R A) : Cont R A :=
  fun k ↦
    f (fun a ↦ fun _localRest ↦ k a) k

def checked (n : Nat) : Cont Nat Nat := do
  let x ← callCC (B := Nat) fun exit ↦ do
    if n == 0 then
      let _ ← exit 99
      pure 0
    else
      pure (n + 1)
  pure (x * 2)

#eval Cont.finish (checked 0)
#eval Cont.finish (checked 3)
#guard Cont.finish (checked 0) == 198
#guard Cont.finish (checked 3) == 8


end Control
end ContinuationTut
