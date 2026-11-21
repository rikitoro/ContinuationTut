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




end ContinuationTut.Quantifiers
