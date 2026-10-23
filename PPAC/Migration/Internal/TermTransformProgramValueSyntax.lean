import PPAC.Migration.Internal.TermTransformProgramCorrectness

/-! 受检程序的实际结果及比较全部内部候选的唯一纤维。 -/
namespace PPAC.Migration.Internal.TermTransformProgramValueSyntax
open Source SourceAlgebra SourceLogic TermTransformProgramSyntax

def uniqueOutput {m} (w R S a b c d n q : Fin m) : Formula m := .all
  ((checked w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def value {m} (w R S a b c d n q : Fin m) : Formula m :=
  (checked w R S a b c d n q).conj ((SyntaxTermSyntax.term w c d q).conj
    ((Formula.mem q w).conj (uniqueOutput w R S a b c d n q)))

def fiber {m} (w R S a b c d n : Fin m) : Formula m := .ex
  (value w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))

theorem uniqueOutput_rename {m k} (w R S a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w R S a b c d n q).rename ρ = uniqueOutput (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, checked_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m k} (w R S a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (value w R S a b c d n q).rename ρ = value (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [value, Formula.rename, checked_rename, SyntaxTermSyntax.term_rename, uniqueOutput_rename]

theorem fiber_rename {m k} (w R S a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w R S a b c d n).rename ρ = fiber (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [fiber, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} (w R S a b c d n q : Fin m) (hq : Derives Γ (value w R S a b c d n q)) :
    Derives Γ (fiber w R S a b c d n) := by
  apply Derives.exI q
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

end PPAC.Migration.Internal.TermTransformProgramValueSyntax
