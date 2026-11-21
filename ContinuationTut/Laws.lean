import ContinuationTut.Monad

/-!
# 5. モナド則
-/


namespace ContinuationTut.Cont

universe r u v w
variable {R : Type r} {A : Type u} {B : Type v} {C : Type w}

theorem pure_bind (a : A) (f : A → Cont R B) :
  bind (pure a) f = f a := by
  rfl

theorem bind_pure (m : Cont R A) : bind m pure = m := by
  rfl

theorem bind_assoc (m : Cont R A)
  (f : A → Cont R B) (g : B → Cont R C) :
  bind (bind m f) g = bind m (fun a ↦ bind (f a) g) := by
  rfl

theorem map_eq_bind (f : A → B) (m : Cont R A) :
  map f m = bind m (fun a ↦ pure (f a)) := by
  rfl


/-- μ -/
def join (mm : Cont R (Cont R A)) : Cont R A :=
  fun k ↦
    mm <| fun m ↦ m k

/-- 関数側の計算、引数側の計算の順に合成 -/
def ap (mf : Cont R (A → B)) (ma : Cont R A) : Cont R B :=
  bind mf fun f ↦
  bind ma fun a ↦
  pure (f a)

/-- 二項演算の持ち上げ -/
def lift2 (op : A → B → C) (ma : Cont R A) (mb : Cont R B) : Cont R C :=
  bind ma fun a ↦
  bind mb fun b ↦
  pure $ op a b

def reset (m : Cont R R) : R := finish m

theorem join_pure (m : Cont R A) : join (pure m) = m := by
  rfl

theorem join_map_pure (m : Cont R A) :
  join (map pure m) = m := by
  rfl

theorem join_assoc (mmm : Cont R (Cont R (Cont R A))) :
  join (map join mmm) = join (join mmm) := by
  rfl


end ContinuationTut.Cont
