import PPAC.Migration.Internal.FormulaTransformHistorySyntax

/-! 公式程序原子步骤：重建原节点并调用独立受检项程序，不调用旧项替换判断。 -/
namespace PPAC.Migration.Internal.FormulaTransformAtomSyntax
open Source SourceAlgebra SourceLogic SyntaxAtomSyntax TermTransformProgramSyntax

def nullary {m} (truth : Bool) (w a b c d n q : Fin m) : Formula m :=
  (SyntaxAtomSyntax.nullary truth w a b n).conj (SyntaxAtomSyntax.nullary truth w c d q)

theorem nullary_rename {m k} (truth : Bool) (w a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (nullary truth w a b c d n q).rename ρ = nullary truth (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [nullary, Formula.rename, SyntaxAtomSyntax.nullary_rename]

def membershipData {m} (w r s a b c d n q z x y X Y : Fin m) : Formula m :=
  (zeroScalar w z).conj ((memberCode w z x y n).conj ((memberCode w z X Y q).conj ((checked w r s a b c d x X).conj (checked w r s a b c d y Y))))

def membershipBody {m} (w r s a b c d n q : Fin m) : Formula (m+5) :=
  membershipData w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4))

def membership {m} (w r s a b c d n q : Fin m) : Formula m := .ex (.ex (.ex (.ex (.ex (membershipBody w r s a b c d n q)))))

theorem membershipData_rename {m k} (w r s a b c d n q z x y X Y : Fin m) (ρ : Fin m → Fin k) :
    (membershipData w r s a b c d n q z x y X Y).rename ρ = membershipData (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) (ρ z) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [membershipData, Formula.rename, zeroScalar_rename, memberCode_rename, checked_rename]

theorem membership_rename {m k} (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (membership w r s a b c d n q).rename ρ = membership (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [membership, membershipBody, Formula.rename, membershipData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_membership {m} {Γ : Context m} (w r s a b c d n q z x y X Y : Fin m)
    (hd : Derives Γ (membershipData w r s a b c d n q z x y X Y)) : Derives Γ (membership w r s a b c d n q) := by
  apply Derives.exI z
  apply Derives.exI x
  apply Derives.exI y
  apply Derives.exI X
  apply Derives.exI Y
  simpa only [membershipBody, Formula.instantiate, Formula.rename, membershipData_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

def equalityData {m} (w r s a b c d n q x y X Y : Fin m) : Formula m :=
  (equalCode w x y n).conj ((equalCode w X Y q).conj ((checked w r s a b c d x X).conj (checked w r s a b c d y Y)))

def equalityBody {m} (w r s a b c d n q : Fin m) : Formula (m+4) :=
  equalityData w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))

def equality {m} (w r s a b c d n q : Fin m) : Formula m := .ex (.ex (.ex (.ex (equalityBody w r s a b c d n q))))

theorem equalityData_rename {m k} (w r s a b c d n q x y X Y : Fin m) (ρ : Fin m → Fin k) :
    (equalityData w r s a b c d n q x y X Y).rename ρ = equalityData (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [equalityData, Formula.rename, equalCode_rename, checked_rename]

theorem equality_rename {m k} (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (equality w r s a b c d n q).rename ρ = equality (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [equality, equalityBody, Formula.rename, equalityData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_equality {m} {Γ : Context m} (w r s a b c d n q x y X Y : Fin m)
    (hd : Derives Γ (equalityData w r s a b c d n q x y X Y)) : Derives Γ (equality w r s a b c d n q) := by
  apply Derives.exI x
  apply Derives.exI y
  apply Derives.exI X
  apply Derives.exI Y
  simpa only [equalityBody, Formula.instantiate, Formula.rename, equalityData_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

end PPAC.Migration.Internal.FormulaTransformAtomSyntax
