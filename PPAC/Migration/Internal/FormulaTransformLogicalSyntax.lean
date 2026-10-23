import PPAC.Migration.Internal.FormulaTransformAtomSyntax

/-! 公式程序逻辑步骤：原节点重建、严格子码及实际历史读取／双表提升。 -/
namespace PPAC.Migration.Internal.FormulaTransformLogicalSyntax
open Source SourceAlgebra SourceLogic SyntaxLogicalSyntax FormulaTransformHistorySyntax

def check {m} (advance : Bool) (w h x r s a b c d q : Fin m) : Formula m :=
  if advance then advanced w h x r s a b c d q else read w h x r s a b c d q

theorem check_rename {m k} (advance : Bool) (w h x r s a b c d q : Fin m) (ρ : Fin m → Fin k) :
    (check advance w h x r s a b c d q).rename ρ = check advance (ρ w) (ρ h) (ρ x) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  cases advance <;> simp only [check, Bool.false_eq_true, ↓reduceIte, read_rename, advanced_rename]

def singleData {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q x X : Fin m) : Formula m :=
  (singleCode tag w x n).conj ((Formula.mem x n).conj ((singleCode tag w X q).conj (check advance w h x r s a b c d X)))

def singleBody {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q : Fin m) : Formula (m+2) :=
  singleData tag advance w.castSucc.castSucc h.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def single {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q : Fin m) : Formula m := .ex (.ex (singleBody tag advance w h r s a b c d n q))

theorem singleData_rename {m k} (tag : Nat) (advance : Bool) (w h r s a b c d n q x X : Fin m) (ρ : Fin m → Fin k) :
    (singleData tag advance w h r s a b c d n q x X).rename ρ = singleData tag advance (ρ w) (ρ h) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) (ρ x) (ρ X) := by
  simp only [singleData, Formula.rename, singleCode_rename, check_rename]

theorem single_rename {m k} (tag : Nat) (advance : Bool) (w h r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (single tag advance w h r s a b c d n q).rename ρ = single tag advance (ρ w) (ρ h) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [single, singleBody, Formula.rename, singleData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_single {m} {Γ : Context m} (tag : Nat) (advance : Bool) (w h r s a b c d n q x X : Fin m)
    (hd : Derives Γ (singleData tag advance w h r s a b c d n q x X)) : Derives Γ (single tag advance w h r s a b c d n q) := by
  apply Derives.exI x
  apply Derives.exI X
  simpa only [singleBody, Formula.instantiate, Formula.rename, singleData_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

def binaryData {m} (kind : Fin 4) (w h r s a b c d n q x y X Y : Fin m) : Formula m :=
  (binaryCode kind w x y n).conj ((Formula.mem x n).conj ((Formula.mem y n).conj ((binaryCode kind w X Y q).conj ((read w h x r s a b c d X).conj (read w h y r s a b c d Y)))))

def binaryBody {m} (kind : Fin 4) (w h r s a b c d n q : Fin m) : Formula (m+4) :=
  binaryData kind w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))

def binary {m} (kind : Fin 4) (w h r s a b c d n q : Fin m) : Formula m := .ex (.ex (.ex (.ex (binaryBody kind w h r s a b c d n q))))

theorem binaryData_rename {m k} (kind : Fin 4) (w h r s a b c d n q x y X Y : Fin m) (ρ : Fin m → Fin k) :
    (binaryData kind w h r s a b c d n q x y X Y).rename ρ = binaryData kind (ρ w) (ρ h) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [binaryData, Formula.rename, binaryCode_rename, read_rename]

theorem binary_rename {m k} (kind : Fin 4) (w h r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (binary kind w h r s a b c d n q).rename ρ = binary kind (ρ w) (ρ h) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [binary, binaryBody, Formula.rename, binaryData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_binary {m} {Γ : Context m} (kind : Fin 4) (w h r s a b c d n q x y X Y : Fin m)
    (hd : Derives Γ (binaryData kind w h r s a b c d n q x y X Y)) : Derives Γ (binary kind w h r s a b c d n q) := by
  apply Derives.exI x
  apply Derives.exI y
  apply Derives.exI X
  apply Derives.exI Y
  simpa only [binaryBody, Formula.instantiate, Formula.rename, binaryData_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

end PPAC.Migration.Internal.FormulaTransformLogicalSyntax
