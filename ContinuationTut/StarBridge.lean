import ContinuationTut.Quantifiers

/-!
# 7. *-CCGへの接続
-/

namespace ContinuationTut.StarBridge

open Quantifiers

theorem two_layer_order {R A B C : Type} (op : A → B→ C)
  (left : Cont R A) (right : Cont R B) :
  Cont.join (.lift2 (.lift2 op) (.pure left) (.map .pure right)) =
  .bind right fun b ↦ .bind left fun a ↦ .pure (op a b) := by
  rfl

abbrev M (A : Type) := Cont Bool A

def forward {A B : Type} (f : A → B) (a : A) : B := f a
def backward {A B : Type} (a : A) (f : A → B) : B := f a

-- someone loves everyone の語順に合わせ動詞はまず目的語を受け取る
def verb : Person → Person → Bool :=
  fun object subject ↦ loves subject object

-- 第 1 層: loves と everyone を結び、その後 someone を結ぶ
def verb1 : M (Person → Person → Bool) := .pure verb
def vp1 : M (Person → Bool) := .lift2 forward verb1 everyone
def sentence1 : M Bool := .lift2 backward someone vp1

#eval Cont.reset sentence1
#guard Cont.reset sentence1 == false

theorem same_as_surface : Cont.reset sentence1 = Cont.reset surface := by
  rfl

-- 同じ M A → M (M A) という型でも継続の配置が異なる二つの操作
def unitOutside {A : Type} (m : M A) : M (M A) := .pure m
def unitInside {A : Type} (m : M A) : M (M A) :=
  .map (fun a ↦ .pure a) m

-- β 簡約で両者の違いを確認
theorem unitOutside_expansion {A : Type} (m : M A) :
  unitOutside m = (fun outer ↦ outer m) := by rfl

theorem unitInside_expansion {A : Type} (m : M A) :
  unitInside m = (fun outer ↦ m (fun a ↦ outer (.pure a))) := by
  rfl

-- 単独で join するとどちらも元に戻る
example {A : Type} (m : M A) : .join (unitOutside m) = m := by rfl
example {A : Type} (m : M A) : .join (unitInside m) = m := by rfl

-- ∃ と動詞はもとの層に残し、∀ は外側の層へ置く
def subject2 : M (M Person) := unitOutside someone
def verb2 : M (M (Person → Person → Bool)) := unitOutside verb1
def object2 : M (M Person) := unitInside everyone

-- lift2 をさらに lift2 することで、R** の意味計算を作る
def vp2 : M (M (Person → Bool)) :=
  .lift2 (.lift2 forward) verb2 object2

def sentence2 : M (M Bool) :=
  .lift2 (.lift2 backward) subject2 vp2

def inverseByLayers : Bool := Cont.reset $ .join sentence2

#eval Cont.reset sentence1 -- false
#eval inverseByLayers -- true
#guard inverseByLayers == true

theorem same_as_inverse : inverseByLayers = Cont.reset inverse := by
  rfl

-- 対照実験 : 全員を unitOutside で包むだけでは作用域は反転しない
def object2Outside : M (M Person) := unitOutside everyone

def surfaceByLayers : Bool := Cont.reset $ .join $
  .lift2 (.lift2 backward) subject2 (.lift2 (.lift2 forward) verb2 object2Outside)

#eval surfaceByLayers
#guard surfaceByLayers == false


end ContinuationTut.StarBridge
