import PPAC.Migration.TaggedFamilyContext

/-! 原Replacement实际收集全部唯一标签行，保留精确族成员描述。 -/
namespace PPAC.Migration.TaggedFamilyCollection
open Source SourceAlgebra SourceLogic TaggedFamilySyntax

theorem total_rows {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (a : Fin m) :
    Derives Γ (ReplacementPredicates.total matrix Fin.elim0 a) := by
  simp only [ReplacementPredicates.total, matrix_fiber]
  apply Derives.allI
  have hA' := TaggedFamilyContext.rename hA Fin.castSucc
  apply Derives.impI
  have hAX := TaggedFamilyContext.add hA' (Formula.mem (Fin.last m) a.castSucc)
  exact TaggedRowExistence.fiber (Fin.last m) hAX.pairing hAX.extensionality hAX.pairReplacement

theorem exists_family {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (a : Fin m) : Derives Γ (familyExists a) := by
  have hi := Derives.impE (IterationValueCollection.replacement_instance matrix Fin.elim0 a hA.familyReplacement) (total_rows hA a)
  simpa only [ReplacementPredicates.imageExists, matrix_range, familyExists] using hi
end PPAC.Migration.TaggedFamilyCollection
