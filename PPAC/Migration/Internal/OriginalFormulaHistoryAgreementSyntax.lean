import PPAC.Migration.Internal.OriginalAtomicProgram

/-! 严格子码且有类型的内部公式上，真实原运行与实际历史read的归纳比较公式。 -/
namespace PPAC.Migration.Internal.OriginalFormulaHistoryAgreementSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def agreement {m} (w mode depth parameter h R S a b c d n : Fin m) : Formula m := .all (.all
  (((Formula.mem (Fin.last m).castSucc n.castSucc.castSucc).conj
    (FormulaCodeSyntax.formulaCode w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc b.castSucc.castSucc)).imp
      ((OriginalTransformRowSyntax.run 3 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
        (FormulaTransformHistorySyntax.read w.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))))))

theorem agreement_rename {m j} (w mode depth parameter h R S a b c d n : Fin m) (ρ : Fin m → Fin j) :
    (agreement w mode depth parameter h R S a b c d n).rename ρ = agreement (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ h) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [agreement, Formula.rename, Formula.iff, FormulaCodeSyntax.formulaCode_rename, OriginalTransformRowSyntax.run_rename, FormulaTransformHistorySyntax.read_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem agreement_at {m} {Γ : Context m} (w mode depth parameter h R S a b c d n x X : Fin m)
    (ha : Derives Γ (agreement w mode depth parameter h R S a b c d n))
    (hx : Derives Γ (.mem x n)) (ht : Derives Γ (FormulaCodeSyntax.formulaCode w x a b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter x X).iff (FormulaTransformHistorySyntax.read w h x R S a b c d X)) := by
  have hi := Derives.allE X (Derives.allE x ha)
  have he : Derives Γ (((Formula.mem x n).conj (FormulaCodeSyntax.formulaCode w x a b)).imp ((OriginalTransformRowSyntax.run 3 w mode depth parameter x X).iff (FormulaTransformHistorySyntax.read w h x R S a b c d X))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, Formula.iff, FormulaCodeSyntax.formulaCode_rename, OriginalTransformRowSyntax.run_rename, FormulaTransformHistorySyntax.read_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hi
  exact .impE he (.conjI hx ht)

end PPAC.Migration.Internal.OriginalFormulaHistoryAgreementSyntax
