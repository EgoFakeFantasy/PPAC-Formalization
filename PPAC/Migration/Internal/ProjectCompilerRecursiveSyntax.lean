import PPAC.Migration.Internal.ProjectCompilerQuerySyntax

/-! The direct compiler recursive equation uses actual child Compiled relations. -/
namespace PPAC.Migration.Internal.ProjectCompilerRecursiveSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax

def codeMatrix : Formula (1+3) := ProjectCompilerCodeSyntax.compiled (0 : Fin 1).castSucc.castSucc.castSucc
  (Fin.last 1).castSucc.castSucc (Fin.last 2).castSucc (Fin.last 3)

def parameters {m} (w : Fin m) : Fin 1 → Fin m := fun _ => w

def casesAt {m} (w b z n q : Fin m) : Formula m :=
  ProjectCompilerCaseSyntax.cases codeMatrix (parameters w) w b z n q

def body {m} (w n b q : Fin m) : Formula (m+1) :=
  (empty (Fin.last m)).conj (casesAt w.castSucc b.castSucc (Fin.last m) n.castSucc q.castSucc)

def criterion {m} (w n b q : Fin m) : Formula m :=
  (Formula.mem n w).conj ((SyntaxTermSyntax.contexts w b q).conj (.ex (body w n b q)))

theorem codeMatrix_at {m} (ρ : Fin 1 → Fin m) (x b q : Fin m) :
    ProjectCompilerCaseSyntax.relation codeMatrix ρ x b q = ProjectCompilerCodeSyntax.compiled (ρ 0) x b q := by
  simp only [ProjectCompilerCaseSyntax.relation, codeMatrix, ProjectCompilerCodeSyntax.compiled_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem parameters_map {m l} (w : Fin m) (ρ : Fin m → Fin l) : (fun i => ρ (parameters w i)) = parameters (ρ w) := rfl

theorem casesAt_rename {m l} (w b z n q : Fin m) (ρ : Fin m → Fin l) :
    (casesAt w b z n q).rename ρ = casesAt (ρ w) (ρ b) (ρ z) (ρ n) (ρ q) := by
  simp only [casesAt, ProjectCompilerCaseSyntax.cases_rename, parameters_map]

theorem criterion_rename {m l} (w n b q : Fin m) (ρ : Fin m → Fin l) :
    (criterion w n b q).rename ρ = criterion (ρ w) (ρ n) (ρ b) (ρ q) := by
  simp only [criterion, body, Formula.rename, SyntaxTermSyntax.contexts_rename, empty_rename, casesAt_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.ProjectCompilerRecursiveSyntax
