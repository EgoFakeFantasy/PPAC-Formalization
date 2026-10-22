import PPAC.Migration.Internal.SyntaxIdentityCode

/-! 原 free 头槽弱化的实际位移图/自然码合同；全部索引和范围为对象变量。 -/
namespace PPAC.Migration.Internal.SyntaxFreeShiftSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxIndexMapSyntax SyntaxMapCodeSyntax

def matrix : Formula 2 := successor 1 0

def law {m} (b r : Fin m) : Formula m :=
  RelationGraphSyntax.edgeLaw matrix (Fin.elim0 : Fin 0 → Fin m) b r

def graph {m} (b r : Fin m) : Formula m :=
  RelationGraphSyntax.functionGraph matrix (Fin.elim0 : Fin 0 → Fin m) b r

def shiftMap {m} (w b B r : Fin m) : Formula m :=
  (successor B b).conj ((indexMap w r b B).conj (law b r))

def shiftCode {m} (w b B S : Fin m) : Formula m := .ex
  ((encoded w.castSucc (Fin.last m) b.castSucc B.castSucc S.castSucc).conj
    (shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m)))

def existsMap {m} (w b B : Fin m) : Formula m := .ex
  (shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m))

def existsCode {m} (w b B : Fin m) : Formula m := .ex
  (shiftCode w.castSucc b.castSucc B.castSucc (Fin.last m))

def mapFiber {m} (w b B : Fin m) : Formula m := .ex
  ((shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m)).conj (.all
    ((shiftMap w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def codeFiber {m} (w b B : Fin m) : Formula m := .ex
  ((shiftCode w.castSucc b.castSucc B.castSucc (Fin.last m)).conj (.all
    ((shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def actualState {m} (w b : Fin m) : Formula m := .ex
  ((successor (Fin.last m) b.castSucc).conj (codeFiber w.castSucc b.castSucc (Fin.last m)))

theorem matrix_rel {m} (ρ : Fin 0 → Fin m) (i j : Fin m) :
    ReplacementPredicates.rel matrix ρ i j = successor j i := by
  have h0 : Fin.lastCases j (Fin.lastCases i ρ) (0 : Fin 2) = i := by
    change Fin.lastCases j (Fin.lastCases i ρ) (Fin.last 0).castSucc = i
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h1 : Fin.lastCases j (Fin.lastCases i ρ) (1 : Fin 2) = j := by
    change Fin.lastCases j (Fin.lastCases i ρ) (Fin.last 1) = j
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, successor_rename, h0, h1]

theorem law_rename {m k} (b r : Fin m) (ρ : Fin m → Fin k) :
    (law b r).rename ρ = law (ρ b) (ρ r) := by
  simp only [law, RelationGraphSyntax.edgeLaw_rename, SyntaxAtomSyntax.zero_map]

theorem graph_rename {m k} (b r : Fin m) (ρ : Fin m → Fin k) :
    (graph b r).rename ρ = graph (ρ b) (ρ r) := by
  simp only [graph, RelationGraphSyntax.functionGraph_rename, SyntaxAtomSyntax.zero_map]

theorem shiftMap_rename {m k} (w b B r : Fin m) (ρ : Fin m → Fin k) :
    (shiftMap w b B r).rename ρ = shiftMap (ρ w) (ρ b) (ρ B) (ρ r) := by
  simp only [shiftMap, Formula.rename, successor_rename, indexMap_rename, law_rename]

theorem shiftCode_rename {m k} (w b B S : Fin m) (ρ : Fin m → Fin k) :
    (shiftCode w b B S).rename ρ = shiftCode (ρ w) (ρ b) (ρ B) (ρ S) := by
  simp only [shiftCode, Formula.rename, encoded_rename, shiftMap_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsMap_rename {m k} (w b B : Fin m) (ρ : Fin m → Fin k) :
    (existsMap w b B).rename ρ = existsMap (ρ w) (ρ b) (ρ B) := by
  simp only [existsMap, Formula.rename, shiftMap_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsCode_rename {m k} (w b B : Fin m) (ρ : Fin m → Fin k) :
    (existsCode w b B).rename ρ = existsCode (ρ w) (ρ b) (ρ B) := by
  simp only [existsCode, Formula.rename, shiftCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem mapFiber_rename {m k} (w b B : Fin m) (ρ : Fin m → Fin k) :
    (mapFiber w b B).rename ρ = mapFiber (ρ w) (ρ b) (ρ B) := by
  simp only [mapFiber, Formula.rename, shiftMap_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem codeFiber_rename {m k} (w b B : Fin m) (ρ : Fin m → Fin k) :
    (codeFiber w b B).rename ρ = codeFiber (ρ w) (ρ b) (ρ B) := by
  simp only [codeFiber, Formula.rename, shiftCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem actualState_rename {m k} (w b : Fin m) (ρ : Fin m → Fin k) :
    (actualState w b).rename ρ = actualState (ρ w) (ρ b) := by
  simp only [actualState, Formula.rename, successor_rename, codeFiber_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_code {m} {Γ : Context m} (w b B r S : Fin m)
    (he : Derives Γ (encoded w r b B S)) (hm : Derives Γ (shiftMap w b B r)) :
    Derives Γ (shiftCode w b B S) := by
  apply Derives.exI r
  simpa only [Formula.instantiate, Formula.rename, encoded_rename, shiftMap_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI he hm
end PPAC.Migration.Internal.SyntaxFreeShiftSyntax
