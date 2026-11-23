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

theorem surface_expansion :
  Cont.reset surface = people.any fun x ↦ people.all fun y ↦ loves x y := by
  rfl

theorem inverse_expansion :
  Cont.reset inverse = people.all fun y ↦ people.any fun x ↦ loves x y := by
  rfl

example : Cont.reset surface ≠ Cont.reset inverse := by
  decide

/- Prop 版 -/

def someoneP  : Cont Prop Person := fun k ↦ ∃ x, k x
def everyoneP : Cont Prop Person := fun k ↦ ∀ x, k x

def surfaceP : Prop := Cont.reset <| do
  let subject ← someoneP
  let object ← everyoneP
  pure (subject = object)

def inverseP : Prop := Cont.reset <| do
  let object ← everyoneP
  let subject ← someoneP
  pure (subject = object)

theorem surfaceP_expansion : surfaceP = (∃ x : Person, ∀ y : Person, x = y) := by
  rfl

theorem inverseP_expansion : inverseP = (∀ y : Person, ∃ x : Person, x = y) := by
  rfl

theorem inveseP_true : inverseP := by
  change ∀ y : Person, ∃ x, x = y
  intro y
  apply Exists.intro y
  rfl

theorem surface_false : ¬ surfaceP := by
  change ¬ (∃ x : Person, ∀ y, x = y)
  intro h
  obtain ⟨x, hx⟩ := h
  have ha := hx .anna
  have hb := hx .bruno
  rw [hb] at ha
  cases ha




end ContinuationTut.Quantifiers
