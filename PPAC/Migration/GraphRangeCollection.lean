import PPAC.Migration.GraphRangeSyntax

/-! 一个原Replacement实例实际取得完整函数图的精确输出集合。 -/
namespace PPAC.Migration.GraphRangeCollection
open Source SourceAlgebra SourceLogic GraphSyntax GraphRangeSyntax

theorem total_values {m} {Γ : Context m} (f a : Fin m) (hf : Derives Γ (functionOn f a)) :
    Derives Γ (ReplacementPredicates.total matrix (fun _ => f) a) := by
  simpa only [ReplacementPredicates.total, matrix_fiber, ReplacementPredicates.paramsUp, totalOn] using Derives.conjR hf

theorem exists_range {m} {Γ : Context m} (f a : Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0))
    (hf : Derives Γ (functionOn f a)) : Derives Γ (rangeExists f a) := by
  have hi := Derives.impE (IterationValueCollection.replacement_instance matrix (fun _ => f) a hr) (total_values f a hf)
  simpa only [ReplacementPredicates.imageExists, matrix_range, rangeExists] using hi
end PPAC.Migration.GraphRangeCollection
