import PPAC.Migration.Internal.OriginalTransformExprQuery

/-! 原axiomTest接口的对象一元测试公式；这里不宣称已构造ZF/U的专用测试。 -/
namespace PPAC.Migration.Internal.AxiomTestSyntax
open Source SourceAlgebra SourceLogic

def holds {m} (test : Formula 1) (row : Fin m) : Formula m := test.rename (fun _ => row)

theorem holds_rename {m l} (test : Formula 1) (row : Fin m) (ρ : Fin m → Fin l) :
    (holds test row).rename ρ = holds test (ρ row) := by
  simp only [holds, rename_comp]

end PPAC.Migration.Internal.AxiomTestSyntax
