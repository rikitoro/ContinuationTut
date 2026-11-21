/-!
# 2. 継続モナドのコアを自作

-/

namespace ContinuationTut

universe r u v w

def Cont (R : Type r) (A : Type u) : Type (max r u) := (A → R) → R

namespace Cont

variable {R : Type r} {A : Type u} {B : Type v} {C : Type w}

/-- 関数適用 -/
def run (m : Cont R A) (k : A → R) : R := m k

/-- 値 a を受け取った継続へ渡す -/
def pure (a : A) : Cont R A := fun k ↦ k a

--
def first (next : Nat → Nat) : Nat :=
  next 3

def second (a : Nat) (next : Nat → Nat) : Nat :=
  next (a + 1)

def combined (finish : Nat → Nat) : Nat :=
  first (fun a ↦ second a finish)

#eval combined (fun b ↦ b * 2) -- 8
--

/-- m の結果 a を f に渡し、最後の継続 k を引き継ぐ -/
def bind (m : Cont R A) (f : A → Cont R B) : Cont R B :=
  fun k ↦
    let afterM := fun a ↦ f a k
    m afterM


/-- 通常の関数を継続付き計算の上で使う -/
def map (f : A → B) (m : Cont R A) : Cont R B :=
  fun k ↦
    m fun a ↦ k (f a)

def finish (m : Cont R R) : R := run m id

end Cont


def four : Cont Nat Nat := Cont.pure 4
def fourAsText : Cont String Nat := Cont.pure 4

#eval Cont.run four <| fun n ↦ n * 10 -- 40
#eval Cont.run fourAsText <| fun n ↦ s!"n = {n}" -- "n = 4"



end ContinuationTut
