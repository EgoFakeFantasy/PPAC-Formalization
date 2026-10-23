import PPAC.Migration.Internal.FormulaTransformRecursionSyntax

/-! 独立编译公式程序的实际内部递归／求值接口；没有外部语法树或标准性前提。 -/
namespace PPAC.Migration.Internal.FormulaTransformEvaluationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax
open FormulaTransformRecursionSyntax
open FormulaTransformRecursionSyntax (one one_map)

def data {m} (w s f n y : Fin m) : Formula m := (successor s n).conj ((graph w f s).conj (edge f n y))

def evaluation {m} (w n y : Fin m) : Formula m := .ex (.ex
  (data w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc y.castSucc.castSucc))

def existsValue {m} (w n : Fin m) : Formula m := .ex (evaluation w.castSucc n.castSucc (Fin.last m))

def uniqueValue {m} (w n y : Fin m) : Formula m := .all
  ((evaluation w.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) y.castSucc))

def fiber {m} (w n : Fin m) : Formula m := .ex
  ((evaluation w.castSucc n.castSucc (Fin.last m)).conj (uniqueValue w.castSucc n.castSucc (Fin.last m)))

theorem data_rename {m k} (w d f n y : Fin m) (s : Fin m → Fin k) : (data w d f n y).rename s = data (s w) (s d) (s f) (s n) (s y) := by
  simp only [data, Formula.rename, successor_rename, graph_rename, edge_rename]

theorem evaluation_rename {m k} (w n y : Fin m) (s : Fin m → Fin k) : (evaluation w n y).rename s = evaluation (s w) (s n) (s y) := by
  simp only [evaluation, Formula.rename, data_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsValue_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (existsValue w n).rename s = existsValue (s w) (s n) := by
  simp only [existsValue, Formula.rename, evaluation_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueValue_rename {m k} (w n y : Fin m) (s : Fin m → Fin k) : (uniqueValue w n y).rename s = uniqueValue (s w) (s n) (s y) := by
  simp only [uniqueValue, Formula.rename, evaluation_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (fiber w n).rename s = fiber (s w) (s n) := by
  simp only [fiber, Formula.rename, evaluation_rename, uniqueValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_value {m} {Γ : Context m} (w s f n y : Fin m) (hs : Derives Γ (successor s n))
    (hf : Derives Γ (graph w f s)) (hy : Derives Γ (edge f n y)) : Derives Γ (evaluation w n y) := by
  apply Derives.exI s
  apply Derives.exI f
  simp only [Formula.instantiate, data_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs (.conjI hf hy)

abbrev witnesses {m} (w n y : Fin m) : Formula (m+2) :=
  data w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc y.castSucc.castSucc

theorem eliminate_value {m} {Γ : Context m} (w n y : Fin m) (q : Formula m) (hy : Derives Γ (evaluation w n y))
    (hc : Derives (Context.add (witnesses w n y) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (witnesses w n y))) at hy
  apply Derives.exE hy
  apply Derives.exE (p := witnesses w n y) (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨t, ht, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨t, Or.inr ht, he⟩

theorem intro_exists {m} {Γ : Context m} (w n y : Fin m) (hy : Derives Γ (evaluation w n y)) : Derives Γ (existsValue w n) := by
  apply Derives.exI y
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (hy)

theorem output_subst {m} {Γ : Context m} (w n y u : Fin m) (he : Derives Γ (.equal y u))
    (hy : Derives Γ (evaluation w n y)) : Derives Γ (evaluation w n u) := by
  have hi : Derives Γ ((evaluation w.castSucc n.castSucc (Fin.last m)).instantiate y) := by
    exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (hy)
  have ho := Derives.eqSubst (evaluation w.castSucc n.castSucc (Fin.last m)) he hi
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (ho)
end PPAC.Migration.Internal.FormulaTransformEvaluationSyntax
