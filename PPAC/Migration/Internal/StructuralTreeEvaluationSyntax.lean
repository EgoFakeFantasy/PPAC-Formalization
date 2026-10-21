import PPAC.Migration.Internal.ObjectStructuralTreeOperator

/-! 树求值保留实际后继域、完整原递归图和索引真边；全部见证在对象层。 -/
namespace PPAC.Migration.Internal.StructuralTreeEvaluationSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax
open StructuralTreeOperatorSyntax (matrix params3_map)
open NaturalAdditionTransport (params3)

def graph {m} (w z e f d : Fin m) : Formula m := OrdinalRecursionSyntax.recursor matrix (params3 w z e) f d

def graphExists {m} (w z e d : Fin m) : Formula m := .ex (graph w.castSucc z.castSucc e.castSucc (Fin.last m) d.castSucc)

def data {m} (w z e s f n y : Fin m) : Formula m := (successor s n).conj ((graph w z e f s).conj (edge f n y))

def evaluation {m} (w z e n y : Fin m) : Formula m := .ex (.ex
  (data w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc y.castSucc.castSucc))

def existsValue {m} (w z e n : Fin m) : Formula m := .ex (evaluation w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m))

def uniqueValue {m} (w z e n y : Fin m) : Formula m := .all
  ((evaluation w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) y.castSucc))

def fiber {m} (w z e n : Fin m) : Formula m := .ex
  ((evaluation w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m)).conj (uniqueValue w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m)))

theorem graph_rename {m k} (w z e f d : Fin m) (s : Fin m → Fin k) : (graph w z e f d).rename s = graph (s w) (s z) (s e) (s f) (s d) := by
  simp only [graph, OrdinalRecursionSyntax.recursor_rename, params3_map]

theorem graphExists_rename {m k} (w z e d : Fin m) (s : Fin m → Fin k) : (graphExists w z e d).rename s = graphExists (s w) (s z) (s e) (s d) := by
  simp only [graphExists, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem data_rename {m k} (w z e d f n y : Fin m) (s : Fin m → Fin k) : (data w z e d f n y).rename s = data (s w) (s z) (s e) (s d) (s f) (s n) (s y) := by
  simp only [data, Formula.rename, successor_rename, graph_rename, edge_rename]

theorem evaluation_rename {m k} (w z e n y : Fin m) (s : Fin m → Fin k) : (evaluation w z e n y).rename s = evaluation (s w) (s z) (s e) (s n) (s y) := by
  simp only [evaluation, Formula.rename, data_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsValue_rename {m k} (w z e n : Fin m) (s : Fin m → Fin k) : (existsValue w z e n).rename s = existsValue (s w) (s z) (s e) (s n) := by
  simp only [existsValue, Formula.rename, evaluation_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueValue_rename {m k} (w z e n y : Fin m) (s : Fin m → Fin k) : (uniqueValue w z e n y).rename s = uniqueValue (s w) (s z) (s e) (s n) (s y) := by
  simp only [uniqueValue, Formula.rename, evaluation_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w z e n : Fin m) (s : Fin m → Fin k) : (fiber w z e n).rename s = fiber (s w) (s z) (s e) (s n) := by
  simp only [fiber, Formula.rename, evaluation_rename, uniqueValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_value {m} {Γ : Context m} (w z e s f n y : Fin m) (hs : Derives Γ (successor s n))
    (hf : Derives Γ (graph w z e f s)) (hy : Derives Γ (edge f n y)) : Derives Γ (evaluation w z e n y) := by
  apply Derives.exI s
  apply Derives.exI f
  simp only [Formula.instantiate, data_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs (.conjI hf hy)

abbrev witnesses {m} (w z e n y : Fin m) : Formula (m+2) :=
  data w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc y.castSucc.castSucc

theorem eliminate_value {m} {Γ : Context m} (w z e n y : Fin m) (q : Formula m) (hy : Derives Γ (evaluation w z e n y))
    (hc : Derives (Context.add (witnesses w z e n y) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (witnesses w z e n y))) at hy
  apply Derives.exE hy
  apply Derives.exE (p := witnesses w z e n y) (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨t, ht, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨t, Or.inr ht, he⟩

theorem intro_exists {m} {Γ : Context m} (w z e n y : Fin m) (hy : Derives Γ (evaluation w z e n y)) : Derives Γ (existsValue w z e n) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy

theorem output_subst {m} {Γ : Context m} (w z e n y u : Fin m) (he : Derives Γ (.equal y u))
    (hy : Derives Γ (evaluation w z e n y)) : Derives Γ (evaluation w z e n u) := by
  have hi : Derives Γ ((evaluation w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (evaluation w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.StructuralTreeEvaluationSyntax
