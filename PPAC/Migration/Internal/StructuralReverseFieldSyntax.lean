import PPAC.Migration.Internal.StructuralReverseIndexExistence
import PPAC.Migration.Internal.StructuralListCodeInduction

/-! Reverse fields use the actual source field at the unique internal mirror index. -/
namespace PPAC.Migration.Internal.StructuralReverseFieldSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax StructuralReverseIndexSyntax
open StructuralListFieldSyntax (field field_rename)
open SyntaxRenameQuerySyntax (of_eq)

def value {m} (w n l i y : Fin m) : Formula m := .ex
  ((mirror w.castSucc l.castSucc i.castSucc (Fin.last m)).conj (field w.castSucc n.castSucc (Fin.last m) y.castSucc))

def existsValue {m} (w n l i : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (value w.castSucc n.castSucc l.castSucc i.castSucc (Fin.last m)))

def valueFiber {m} (w n l i : Fin m) : Formula m := .ex
  ((value w.castSucc n.castSucc l.castSucc i.castSucc (Fin.last m)).conj (.all
    ((value w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def matrix : Formula 5 := value 0 1 2 3 4

def edgeLaw {m} (w n l g : Fin m) : Formula m := .all (.all
  ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc l.castSucc.castSucc).conj (value w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def graph {m} (w n l g : Fin m) : Formula m := (functionOn g l).conj (edgeLaw w n l g)

def existsGraph {m} (w n l : Fin m) : Formula m := .ex (graph w.castSucc n.castSucc l.castSucc (Fin.last m))

theorem value_rename {m k} (w n l i y : Fin m) (ρ : Fin m → Fin k) :
    (value w n l i y).rename ρ = value (ρ w) (ρ n) (ρ l) (ρ i) (ρ y) := by
  simp only [value,Formula.rename,mirror_rename,field_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem existsValue_rename {m k} (w n l i : Fin m) (ρ : Fin m → Fin k) :
    (existsValue w n l i).rename ρ = existsValue (ρ w) (ρ n) (ρ l) (ρ i) := by
  simp only [existsValue,Formula.rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem valueFiber_rename {m k} (w n l i : Fin m) (ρ : Fin m → Fin k) :
    (valueFiber w n l i).rename ρ = valueFiber (ρ w) (ρ n) (ρ l) (ρ i) := by
  simp only [valueFiber,Formula.rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem edgeLaw_rename {m k} (w n l g : Fin m) (ρ : Fin m → Fin k) :
    (edgeLaw w n l g).rename ρ = edgeLaw (ρ w) (ρ n) (ρ l) (ρ g) := by
  simp only [edgeLaw,Formula.rename,Formula.iff,edge_rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem graph_rename {m k} (w n l g : Fin m) (ρ : Fin m → Fin k) :
    (graph w n l g).rename ρ = graph (ρ w) (ρ n) (ρ l) (ρ g) := by
  simp only [graph,Formula.rename,functionOn_rename,edgeLaw_rename]

theorem existsGraph_rename {m k} (w n l : Fin m) (ρ : Fin m → Fin k) :
    (existsGraph w n l).rename ρ = existsGraph (ρ w) (ρ n) (ρ l) := by
  simp only [existsGraph,Formula.rename,graph_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_rel {m} (ρ : Fin 3 → Fin m) (i y : Fin m) :
    ReplacementPredicates.rel matrix ρ i y = value (ρ 0) (ρ 1) (ρ 2) i y := by
  have h0 : Fin.lastCases y (Fin.lastCases i ρ) (0 : Fin 5) = ρ 0 := by
    change Fin.lastCases y (Fin.lastCases i ρ) (0 : Fin 3).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases y (Fin.lastCases i ρ) (1 : Fin 5) = ρ 1 := by
    change Fin.lastCases y (Fin.lastCases i ρ) (1 : Fin 3).castSucc.castSucc = ρ 1
    simp only [Fin.lastCases_castSucc]
  have h2 : Fin.lastCases y (Fin.lastCases i ρ) (2 : Fin 5) = ρ 2 := by
    change Fin.lastCases y (Fin.lastCases i ρ) (2 : Fin 3).castSucc.castSucc = ρ 2
    simp only [Fin.lastCases_castSucc]
  have h3 : Fin.lastCases y (Fin.lastCases i ρ) (3 : Fin 5) = i := by
    change Fin.lastCases y (Fin.lastCases i ρ) (Fin.last 3).castSucc = i
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
  have h4 : Fin.lastCases y (Fin.lastCases i ρ) (4 : Fin 5) = y := by
    change Fin.lastCases y (Fin.lastCases i ρ) (Fin.last 4) = y
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel,Source.SetLanguage.relation,matrix,value_rename,h0,h1,h2,h3,h4]

theorem matrix_fiber {m} (ρ : Fin 3 → Fin m) (i : Fin m) :
    ReplacementPredicates.fiber matrix ρ i = valueFiber (ρ 0) (ρ 1) (ρ 2) i := by
  simp only [ReplacementPredicates.fiber,ReplacementPredicates.unique,matrix_rel,ReplacementPredicates.paramsUp,valueFiber]

theorem matrix_graph {m} (ρ : Fin 3 → Fin m) (g : Fin m) :
    RelationGraphSyntax.functionGraph matrix ρ (ρ 2) g = graph (ρ 0) (ρ 1) (ρ 2) g := by
  simp only [RelationGraphSyntax.functionGraph,RelationGraphSyntax.edgeLaw,matrix_rel,ReplacementPredicates.paramsUp,graph,edgeLaw]

theorem intro_value {m} {Γ : Context m} (w n l i j y : Fin m) (hm : Derives Γ (mirror w l i j))
    (hf : Derives Γ (field w n j y)) : Derives Γ (value w n l i y) := by
  apply Derives.exI j
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,mirror_rename,field_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hm hf)

theorem law_at {m} {Γ : Context m} (w n l g i y : Fin m) (hg : Derives Γ (graph w n l g)) :
    Derives Γ ((edge g i y).iff ((Formula.mem i l).conj (value w n l i y))) := by
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,Formula.iff,edge_rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE y (Derives.allE i (.conjR hg)))

end PPAC.Migration.Internal.StructuralReverseFieldSyntax
