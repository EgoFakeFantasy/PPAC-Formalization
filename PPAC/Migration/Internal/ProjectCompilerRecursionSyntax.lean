import PPAC.Migration.Internal.ProjectCompilerStateMembership

/-! Actual compiler set recursion or guarded output relation; output correctness and functionality remain unproved. -/
namespace PPAC.Migration.Internal.ProjectCompilerRecursionSyntax
open Source SourceAlgebra SourceLogic SyntaxAtomSyntax ProjectCompilerStateSyntax SyntaxContextCarrierSyntax

def matrix : Formula (2+3) :=
  state (0 : Fin 2).castSucc.castSucc.castSucc (1 : Fin 2).castSucc.castSucc.castSucc
    (Fin.last 2).castSucc.castSucc (Fin.last 3).castSucc (Fin.last 4)
def recursors {m} (w c : Fin m) : Formula m := OrdinalRecursionExistenceSyntax.allUnique matrix (two w c)
def graph {m} (w c f d : Fin m) : Formula m := OrdinalRecursionSyntax.recursor matrix (two w c) f d
def graphExists {m} (w c d : Fin m) : Formula m := .ex
  (graph w.castSucc c.castSucc (Fin.last m) d.castSucc)
def actualBody {m} (w : Fin m) : Formula (m+3) :=
  (tower w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).conj
    (recursors w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc)
def actualRecursors {m} (w : Fin m) : Formula m := .ex (.ex (.ex (actualBody w)))

theorem matrix_operator {m} (ρ : Fin 2 → Fin m) (n h v : Fin m) :
    OrdinalRecursionSyntax.operator matrix ρ n h v = state (ρ 0) (ρ 1) n h v := by
  simp only [OrdinalRecursionSyntax.operator, matrix, state_rename, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem recursors_rename {m k} (w c : Fin m) (r : Fin m → Fin k) :
    (recursors w c).rename r = recursors (r w) (r c) := by
  simp only [recursors, OrdinalRecursionExistenceSyntax.allUnique_rename, two_map]

theorem graph_rename {m k} (w c f d : Fin m) (r : Fin m → Fin k) :
    (graph w c f d).rename r = graph (r w) (r c) (r f) (r d) := by
  simp only [graph, OrdinalRecursionSyntax.recursor_rename, two_map]

theorem graphExists_rename {m k} (w c d : Fin m) (r : Fin m → Fin k) :
    (graphExists w c d).rename r = graphExists (r w) (r c) (r d) := by
  simp only [graphExists, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem actualRecursors_rename {m k} (w : Fin m) (r : Fin m → Fin k) :
    (actualRecursors w).rename r = actualRecursors (r w) := by
  simp only [actualRecursors, actualBody, Formula.rename, tower_rename, recursors_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
end PPAC.Migration.Internal.ProjectCompilerRecursionSyntax
