import PPAC.Migration.Internal.FormulaCodeTreeValidity

/-! 无预设Constructor前提的完整根类型数据；子式检查使用真实图和值及正确内部作用域。 -/
namespace PPAC.Migration.Internal.FormulaCodeTypedDataSyntax
open Source SourceAlgebra SourceLogic SyntaxTermSyntax SyntaxNumeralSyntax FormulaCodeGraphTyping FormulaCodeAllowedAritySyntax
open StructuralTreeValiditySyntax (nodeData nodeData_rename)
open FormulaCodeShapeSyntax (uniqueShape uniqueShape_rename)

def rootCheck {m} (tag : Nat) (w g b f : Fin m) : Formula m := match tag with
  | 0 | 1 => contexts w b f
  | 2 => memberCheck w g b f
  | 3 => equalCheck w g b f
  | 4 => singleCheck false w g b f
  | 5 | 6 | 7 | 8 => binaryCheck w g b f
  | 9 | 10 => singleCheck true w g b f
  | _ => .bot

def cases {m} : Nat → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Formula m
  | 0, _, _, _, _, _, _ => .bot
  | k+1, w, t, l, g, b, f => (cases k w t l g b f).disj
      ((numeral k t).conj ((numeral (expectedArity k) l).conj (rootCheck k w g b f)))

def typedData {m} (w n b f t p l g : Fin m) : Formula m :=
  (nodeData w n t p l g).conj ((contexts w b f).conj (cases 11 w t l g b f))

def dataBody {m} (w n b f : Fin m) : Formula (m+4) :=
  typedData w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    b.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3))

def typedFiber {m} (w n b f : Fin m) : Formula m := .ex (.ex (.ex (.ex
  ((dataBody w n b f).conj (uniqueShape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3)))))))

theorem rootCheck_rename {m n} (tag : Nat) (w g b f : Fin m) (r : Fin m → Fin n) :
    (rootCheck tag w g b f).rename r = rootCheck tag (r w) (r g) (r b) (r f) := by
  match tag with
  | 0 | 1 => exact contexts_rename w b f r
  | 2 => exact memberCheck_rename w g b f r
  | 3 => exact equalCheck_rename w g b f r
  | 4 => exact singleCheck_rename false w g b f r
  | 5 | 6 | 7 | 8 => exact binaryCheck_rename w g b f r
  | 9 | 10 => exact singleCheck_rename true w g b f r
  | _+11 => rfl

theorem cases_rename {m n} (k : Nat) (w t l g b f : Fin m) (r : Fin m → Fin n) :
    (cases k w t l g b f).rename r = cases k (r w) (r t) (r l) (r g) (r b) (r f) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [cases, Formula.rename, numeral_rename, rootCheck_rename, ih]

theorem typedData_rename {m n} (w x b f t p l g : Fin m) (r : Fin m → Fin n) :
    (typedData w x b f t p l g).rename r = typedData (r w) (r x) (r b) (r f) (r t) (r p) (r l) (r g) := by
  simp only [typedData, Formula.rename, nodeData_rename, contexts_rename, cases_rename]

theorem typedFiber_rename {m n} (w x b f : Fin m) (r : Fin m → Fin n) :
    (typedFiber w x b f).rename r = typedFiber (r w) (r x) (r b) (r f) := by
  simp only [typedFiber, dataBody, Formula.rename, typedData_rename, uniqueShape_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_cases {m} {Γ : Context m} (k tag : Nat) (hk : tag < k) (w t l g b f : Fin m)
    (ht : Derives Γ (numeral tag t)) (hl : Derives Γ (numeral (expectedArity tag) l))
    (hc : Derives Γ (rootCheck tag w g b f)) : Derives Γ (cases k w t l g b f) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : tag = k
    · subst tag; exact .disjR (.conjI ht (.conjI hl hc))
    · exact .disjL (ih (by omega))

theorem intro_fiber {m} {Γ : Context m} (w n b f t p l g : Fin m)
    (hd : Derives Γ (typedData w n b f t p l g)) (hu : Derives Γ (uniqueShape w n t p l g)) :
    Derives Γ (typedFiber w n b f) := by
  apply Derives.exI t
  apply Derives.exI p
  apply Derives.exI l
  apply Derives.exI g
  simp only [dataBody, Formula.instantiate, Formula.rename, typedData_rename, uniqueShape_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hd hu
end PPAC.Migration.Internal.FormulaCodeTypedDataSyntax
