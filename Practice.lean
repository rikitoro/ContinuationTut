import ContinuationTut

namespace Practice
open ContinuationTut

-- 演習1 : 二乗をCPS化する
def squareCPS {R : Type} (n : Nat) (k : Nat → R) : R :=
  k (n^2)

#guard squareCPS 5 fun n ↦ n + 1 == 26
#guard squareCPS 5 fun n ↦ s!"square={n}" == "square=25"


-- 演習2：型だけを手掛かりに pure と bind を作る。
def myPure {R A : Type} (a : A) : Cont R A := sorry
def myBind {R A B : Type} (m : Cont R A) (f : A → Cont R B) : Cont R B := sorry
-- #guard Cont.finish (myBind (myPure 3) (fun n => myPure (n + 1))) == 4

-- 演習3：myPure と myBind だけで map を作る。
def myMap {R A B : Type} (f : A → B) (m : Cont R A) : Cont R B := sorry
example {R A : Type} (m : Cont R A) : myMap id m = m := by
  sorry

-- 演習4：継続を3回使う計算を作る。
def chooseThree {A R : Type} (a b c : A) : Cont (List R) A := sorry
-- #guard Cont.run (chooseThree 1 2 3) (fun n => [n * 10]) == [10, 20, 30]

-- 演習5：「すべての人が誰かを愛する」を作る。
open Quantifiers
def everySubjectSomeObject : Cont Bool Bool := sorry
-- #guard Cont.reset everySubjectSomeObject == true

end Practice
