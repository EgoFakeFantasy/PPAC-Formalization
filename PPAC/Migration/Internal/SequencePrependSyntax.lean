import PPAC.Migration.Internal.ObjectPacketReaderInit

/-! Exact prepend graph values: new zero head and every actual old index shifted to its successor. -/
namespace PPAC.Migration.Internal.SequencePrependSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax
open StructuralListFieldSyntax (field field_rename)
open SyntaxRenameQuerySyntax (of_eq)

def shift {m} (f d i y : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) d.castSucc).conj ((successor i.castSucc (Fin.last m)).conj (edge f.castSucc (Fin.last m) y.castSucc)))

def value {m} (f d n i y : Fin m) : Formula m :=
  ((empty i).conj (.equal y n)).disj (shift f d i y)

def existsValue {m} (f d n i : Fin m) : Formula m := .ex (value f.castSucc d.castSucc n.castSucc i.castSucc (Fin.last m))

def valueFiber {m} (f d n i : Fin m) : Formula m := .ex
  ((value f.castSucc d.castSucc n.castSucc i.castSucc (Fin.last m)).conj (.all
    ((value f.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def matrix : Formula 5 := value 0 1 2 3 4

def edgeLaw {m} (f d n e g : Fin m) : Formula m := .all (.all
  ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc e.castSucc.castSucc).conj (value f.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def graph {m} (f d n e g : Fin m) : Formula m := (functionOn g e).conj (edgeLaw f d n e g)

def existsGraph {m} (f d n e : Fin m) : Formula m := .ex (graph f.castSucc d.castSucc n.castSucc e.castSucc (Fin.last m))

theorem shift_rename {m k} (f d i y : Fin m) (ρ : Fin m → Fin k) :
    (shift f d i y).rename ρ = shift (ρ f) (ρ d) (ρ i) (ρ y) := by
  simp only [shift,Formula.rename,successor_rename,edge_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem value_rename {m k} (f d n i y : Fin m) (ρ : Fin m → Fin k) :
    (value f d n i y).rename ρ = value (ρ f) (ρ d) (ρ n) (ρ i) (ρ y) := by
  simp only [value,Formula.rename,empty_rename,shift_rename]

theorem existsValue_rename {m k} (f d n i : Fin m) (ρ : Fin m → Fin k) :
    (existsValue f d n i).rename ρ = existsValue (ρ f) (ρ d) (ρ n) (ρ i) := by
  simp only [existsValue,Formula.rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem valueFiber_rename {m k} (f d n i : Fin m) (ρ : Fin m → Fin k) :
    (valueFiber f d n i).rename ρ = valueFiber (ρ f) (ρ d) (ρ n) (ρ i) := by
  simp only [valueFiber,Formula.rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem edgeLaw_rename {m k} (f d n e g : Fin m) (ρ : Fin m → Fin k) :
    (edgeLaw f d n e g).rename ρ = edgeLaw (ρ f) (ρ d) (ρ n) (ρ e) (ρ g) := by
  simp only [edgeLaw,Formula.rename,Formula.iff,edge_rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem graph_rename {m k} (f d n e g : Fin m) (ρ : Fin m → Fin k) :
    (graph f d n e g).rename ρ = graph (ρ f) (ρ d) (ρ n) (ρ e) (ρ g) := by
  simp only [graph,Formula.rename,functionOn_rename,edgeLaw_rename]

theorem existsGraph_rename {m k} (f d n e : Fin m) (ρ : Fin m → Fin k) :
    (existsGraph f d n e).rename ρ = existsGraph (ρ f) (ρ d) (ρ n) (ρ e) := by
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

theorem matrix_graph {m} (ρ : Fin 3 → Fin m) (e g : Fin m) :
    RelationGraphSyntax.functionGraph matrix ρ e g = graph (ρ 0) (ρ 1) (ρ 2) e g := by
  simp only [RelationGraphSyntax.functionGraph,RelationGraphSyntax.edgeLaw,matrix_rel,ReplacementPredicates.paramsUp,graph,edgeLaw]

theorem intro_shift {m} {Γ : Context m} (f d i j y : Fin m) (hj : Derives Γ (.mem j d))
    (hs : Derives Γ (successor i j)) (he : Derives Γ (edge f j y)) : Derives Γ (shift f d i y) := by
  apply Derives.exI j
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,successor_rename,edge_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hj (.conjI hs he))

theorem law_at {m} {Γ : Context m} (f d n e g i y : Fin m) (hg : Derives Γ (graph f d n e g)) :
    Derives Γ ((edge g i y).iff ((Formula.mem i e).conj (value f d n i y))) := by
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,Formula.iff,edge_rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE y (Derives.allE i (.conjR hg)))

end PPAC.Migration.Internal.SequencePrependSyntax
