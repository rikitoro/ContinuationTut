import ContinuationTut.Laws
/-!
# 6. 量化詞を継続として読む
-/

namespace ContinuationTut.Quantifiers

inductive Person where
  | anna
  | bruno
  deriving Repr, DecidableEq, BEq

def people : List Person := [.anna, .bruno]

-- 各人は自分自身だけを愛する世界
def loves (subject object : Person) : Bool := subject == object

def someone : Cont Bool Person := fun k ↦ people.any k
def everyone : Cont Bool Person := fun k ↦ people.all k

-- ∃ subject, ∀ object, loves subject object
def surface : Cont Bool Bool := do
  let subject ← someone
  let object ← everyone
  pure (loves subject object)


-- ∀ object, ∃ subject, loves subject object
def inverse : Cont Bool Bool := do
  let object ← everyone
  let subject ← someone
  pure (loves subject object)

#eval Cont.reset surface
#guard Cont.reset surface == false
#eval Cont.reset inverse
#guard Cont.reset inverse == true


#eval Cont.reset surface
end ContinuationTut.Quantifiers
