import PPAC.Migration.Internal.ProjectCompilerUniqueMatrixHead

/-! Each finite mode is exactly one actual program case, before harmless witness padding. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueActualSyntax
open Source SourceAlgebra SourceLogic ProjectCompilerCaseSyntax ProjectCompilerRecursiveSyntax ProjectCompilerUniqueMatrixSyntax

def actualCase {m} (mode : Mode) (w b z n q : Fin m) : Formula m :=
  match mode with
  | .falseCase => constant false w n q
  | .trueCase => constant true w n q
  | .memberCase => atomicCase 0 w b z n q
  | .equalCase => atomicCase 1 w b z n q
  | .subsetCase => atomicCase 2 w b z n q
  | .negCase => singleCase 4 false codeMatrix (parameters w) w b n q
  | .conjCase => binaryCase 0 codeMatrix (parameters w) w b n q
  | .disjCase => binaryCase 1 codeMatrix (parameters w) w b n q
  | .impCase => binaryCase 2 codeMatrix (parameters w) w b n q
  | .iffCase => binaryCase 3 codeMatrix (parameters w) w b n q
  | .forallCase => singleCase 9 true codeMatrix (parameters w) w b n q
  | .existsCase => singleCase 10 true codeMatrix (parameters w) w b n q

theorem actualCase_rename {m j} (mode : Mode) (w b z n q : Fin m) (σ : Fin m → Fin j) :
    (actualCase mode w b z n q).rename σ = actualCase mode (σ w) (σ b) (σ z) (σ n) (σ q) := by
  cases mode <;> simp only [actualCase, constant_rename, atomicCase_rename, singleCase_rename, binaryCase_rename, parameters_map]

end PPAC.Migration.Internal.ProjectCompilerUniqueActualSyntax
