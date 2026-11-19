/-!
# 1. 普通の関数から継続渡し

-/
namespace ContinuationTut.CPS

def addOne (n : Nat) : Nat := n + 1
def double (n : Nat) : Nat := n * 2

def direct (n : Nat) : Nat := double (addOne n) + 10

def addOneCPS {R : Type} (n : Nat) (k : Nat → R) : R :=
  k (n + 1)

def doubleCPS {R : Type} (n : Nat) (k : Nat → R) : R :=
  k (n * 2)

def pipelineCPS {R : Type} (n : Nat) (k : Nat → R) : R :=
  addOneCPS n fun a ↦
  doubleCPS a fun b ↦
  k (b + 10)

#eval direct 3 -- 18
#eval addOneCPS 3 fun x ↦ x * 2 -- 9
#eval addOneCPS 3 fun x ↦ s!"value = {x}" -- "value = 4"
#eval pipelineCPS 3 id -- 18
#eval pipelineCPS 3 fun n ↦ n == 18 -- true

#guard direct 3 == 18
#guard pipelineCPS 3 id == 18
#guard pipelineCPS 3 fun n ↦ n == 18

theorem cps_matches_direct (n : Nat) :
  pipelineCPS n id = direct n := by
  rfl

end ContinuationTut.CPS
