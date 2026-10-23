import PPAC.Migration.Internal.SyntaxMixedFormulaOperatorMembership

/-! 完整混合替换状态集合值算子及原序数递归接口；固定参数只有内部ω。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic SyntaxMixedFormulaOperatorSyntax

def one {m} (w : Fin m) : Fin 1 → Fin m := fun _ => w

theorem one_map {m k} (w : Fin m) (ρ : Fin m → Fin k) : (fun i => ρ (one w i)) = one (ρ w) := rfl

def matrix : Formula (1+3) := value (0 : Fin 1).castSucc.castSucc.castSucc
  (Fin.last 1).castSucc.castSucc (Fin.last 2).castSucc (Fin.last 3)

def recursors {m} (w : Fin m) : Formula m := OrdinalRecursionExistenceSyntax.allUnique matrix (one w)

def graph {m} (w f d : Fin m) : Formula m := OrdinalRecursionSyntax.recursor matrix (one w) f d

def graphExists {m} (w d : Fin m) : Formula m := .ex (graph w.castSucc (Fin.last m) d.castSucc)

def actualRecursors {m} (w : Fin m) : Formula m := .ex
  ((PowerSetSyntax.powerOf (Fin.last m) w.castSucc).conj (recursors w.castSucc))

def existsSystem : Source.Sentence := .ex ((OmegaSyntax.omega (Fin.last 0)).conj (actualRecursors (Fin.last 0)))

theorem matrix_operator {m} (ρ : Fin 1 → Fin m) (n h v : Fin m) :
    OrdinalRecursionSyntax.operator matrix ρ n h v = value (ρ 0) n h v := by
  simp only [OrdinalRecursionSyntax.operator, matrix, value_rename, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem recursors_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) :
    (recursors w).rename ρ = recursors (ρ w) := by
  simp only [recursors, OrdinalRecursionExistenceSyntax.allUnique_rename, one_map]

theorem graph_rename {m k} (w f d : Fin m) (ρ : Fin m → Fin k) :
    (graph w f d).rename ρ = graph (ρ w) (ρ f) (ρ d) := by
  simp only [graph, OrdinalRecursionSyntax.recursor_rename, one_map]

theorem graphExists_rename {m k} (w d : Fin m) (ρ : Fin m → Fin k) :
    (graphExists w d).rename ρ = graphExists (ρ w) (ρ d) := by
  simp only [graphExists, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem actualRecursors_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) :
    (actualRecursors w).rename ρ = actualRecursors (ρ w) := by
  simp only [actualRecursors, Formula.rename, PowerSetSyntax.powerOf_rename, recursors_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
end PPAC.Migration.Internal.SyntaxMixedFormulaRecursionSyntax
