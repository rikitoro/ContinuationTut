/-!
# 2. 継続モナドのコアを自作

-/

namespace ContinuationTut

universe r u v w

def Cont (R : Type r) (A : Type u) : Type (max r u) := (A → R) → R



end ContinuationTut
