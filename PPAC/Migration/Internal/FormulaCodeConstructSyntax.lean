import PPAC.Migration.Internal.ObjectFormulaCode

/-! 原精确构造及完整FormulaCode的实际码纤维；所有码见证均为对象存在量词。 -/
namespace PPAC.Migration.Internal.FormulaCodeConstructSyntax
open Source SourceAlgebra SourceLogic SyntaxNodeSyntax FormulaCodeSyntax

def typedAt {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n b f : Fin m) : Formula m :=
  (constructor k tag w xs n).conj (formulaCode w n b f)

def typedExists {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (b f : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj
    (typedAt k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m) b.castSucc f.castSucc))

def typedFiber {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (b f : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj
    (typedAt k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m) b.castSucc f.castSucc)).conj
      (.all ((constructor k tag w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def law {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (b f : Fin m) : Formula m := .all
  ((constructor k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).imp
    (formulaCode w.castSucc (Fin.last m) b.castSucc f.castSucc))

theorem typedAt_rename {m l} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n b f : Fin m) (s : Fin m → Fin l) :
    (typedAt k tag w xs n b f).rename s = typedAt k tag (s w) (fun i => s (xs i)) (s n) (s b) (s f) := by
  simp only [typedAt, Formula.rename, constructor_rename, formulaCode_rename]

theorem typedExists_rename {m l} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (b f : Fin m) (s : Fin m → Fin l) :
    (typedExists k tag w xs b f).rename s = typedExists k tag (s w) (fun i => s (xs i)) (s b) (s f) := by
  simp only [typedExists, Formula.rename, typedAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem typedFiber_rename {m l} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (b f : Fin m) (s : Fin m → Fin l) :
    (typedFiber k tag w xs b f).rename s = typedFiber k tag (s w) (fun i => s (xs i)) (s b) (s f) := by
  simp only [typedFiber, Formula.rename, typedAt_rename, constructor_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem law_rename {m l} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (b f : Fin m) (s : Fin m → Fin l) :
    (law k tag w xs b f).rename s = law k tag (s w) (fun i => s (xs i)) (s b) (s f) := by
  simp only [law, Formula.rename, constructor_rename, formulaCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem law_at {m} {Γ : Context m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (b f n : Fin m)
    (hl : Derives Γ (law k tag w xs b f)) (hc : Derives Γ (constructor k tag w xs n)) :
    Derives Γ (formulaCode w n b f) := by
  have hh := Derives.allE n hl
  simp only [Formula.instantiate, Formula.rename, constructor_rename, formulaCode_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] at hh
  exact .impE hh hc

theorem law_of_known {m} {Γ : Context m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (b f : Fin m) (p : Formula m)
    (hp : Derives Γ p)
    (hi : Derives (Context.add (constructor k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m))
      (Context.image Formula.raise Γ))
      ((formulaCode w.castSucc (Fin.last m) b.castSucc f.castSucc).iff p.raise)) :
    Derives Γ (law k tag w xs b f) := by
  apply Derives.allI
  apply Derives.impI
  exact .impE (.conjR hi) (under hp _)
end PPAC.Migration.Internal.FormulaCodeConstructSyntax
