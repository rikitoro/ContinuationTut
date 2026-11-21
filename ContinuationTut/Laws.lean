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

end ContinuationTut.Cont
