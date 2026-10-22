import PPAC.Migration.Internal.ObjectSyntaxRenameFields

/-! 实际恒等完整图及原自然映射码的纯对象合同；不抽取宿主identity函数。 -/
namespace PPAC.Migration.Internal.SyntaxIdentityMapSyntax
open Source SourceAlgebra SourceLogic SyntaxRenameTermIdentity SyntaxIndexMapSyntax SyntaxMapCodeSyntax

def matrix : Formula 2 := .equal 0 1

def graph {m} (a r : Fin m) : Formula m := RelationGraphSyntax.functionGraph matrix (Fin.elim0 : Fin 0 → Fin m) a r

def identityMap {m} (w a r : Fin m) : Formula m := (indexMap w r a a).conj (diagonal r)

def identityCode {m} (w a R : Fin m) : Formula m := .ex
  ((encoded w.castSucc (Fin.last m) a.castSucc a.castSucc R.castSucc).conj (diagonal (Fin.last m)))

def existsMap {m} (w a : Fin m) : Formula m := .ex (identityMap w.castSucc a.castSucc (Fin.last m))

def existsCode {m} (w a : Fin m) : Formula m := .ex (identityCode w.castSucc a.castSucc (Fin.last m))

theorem matrix_rel {m} (ρ : Fin 0 → Fin m) (x y : Fin m) : ReplacementPredicates.rel matrix ρ x y = Formula.equal x y := by
  have h0 : Fin.lastCases y (Fin.lastCases x ρ) (0 : Fin 2) = x := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 0).castSucc = x
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h1 : Fin.lastCases y (Fin.lastCases x ρ) (1 : Fin 2) = y := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 1) = y
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, Formula.rename, h0, h1]

theorem graph_rename {m k} (a r : Fin m) (ρ : Fin m → Fin k) : (graph a r).rename ρ = graph (ρ a) (ρ r) := by
  simp only [graph, RelationGraphSyntax.functionGraph_rename, SyntaxAtomSyntax.zero_map]

theorem identityMap_rename {m k} (w a r : Fin m) (ρ : Fin m → Fin k) :
    (identityMap w a r).rename ρ = identityMap (ρ w) (ρ a) (ρ r) := by
  simp only [identityMap, Formula.rename, indexMap_rename, diagonal_rename]

theorem identityCode_rename {m k} (w a R : Fin m) (ρ : Fin m → Fin k) :
    (identityCode w a R).rename ρ = identityCode (ρ w) (ρ a) (ρ R) := by
  simp only [identityCode, Formula.rename, encoded_rename, diagonal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsMap_rename {m k} (w a : Fin m) (ρ : Fin m → Fin k) : (existsMap w a).rename ρ = existsMap (ρ w) (ρ a) := by
  simp only [existsMap, Formula.rename, identityMap_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsCode_rename {m k} (w a : Fin m) (ρ : Fin m → Fin k) : (existsCode w a).rename ρ = existsCode (ρ w) (ρ a) := by
  simp only [existsCode, Formula.rename, identityCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_code {m} {Γ : Context m} (w a r R : Fin m)
    (he : Derives Γ (encoded w r a a R)) (hd : Derives Γ (diagonal r)) : Derives Γ (identityCode w a R) := by
  apply Derives.exI r
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, Formula.rename, encoded_rename, diagonal_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.conjI he hd)
end PPAC.Migration.Internal.SyntaxIdentityMapSyntax
