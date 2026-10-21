import PPAC.Migration.ObjectPowerUnion

/-! 幂集像并算子实际满足总单值性后，实例化全对象超限递归；无残留算子前提。 -/
namespace PPAC.Migration.HierarchyRecursion
open Source SourceAlgebra SourceLogic OrdinalRecursionExistenceSyntax

def existenceSentence : Source.Sentence := holds PowerUnionSyntax.matrix (id : Fin 0 → Fin 0)

def uniquenessSentence : Source.Sentence := allUnique PowerUnionSyntax.matrix (id : Fin 0 → Fin 0)

theorem source_existence : Derives (Source.SetLanguage.ZF.at 0) existenceSentence := by
  have hi := ObjectTransfiniteRecursion.source_existence PowerUnionSyntax.matrix
  change Derives (Source.SetLanguage.ZF.at 0) ((OrdinalRecursionTotal.total PowerUnionSyntax.matrix (id : Fin 0 → Fin 0)).imp
    ((OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix (id : Fin 0 → Fin 0)).imp existenceSentence)) at hi
  exact .impE (.impE hi ObjectPowerUnion.source_ZF_total) ObjectPowerUnion.source_ZF_deterministic

theorem source_uniqueness : Derives (Source.SetLanguage.ZF.at 0) uniquenessSentence := by
  have hi := ObjectTransfiniteRecursion.source_uniqueness PowerUnionSyntax.matrix
  change Derives (Source.SetLanguage.ZF.at 0) ((OrdinalRecursionTotal.total PowerUnionSyntax.matrix (id : Fin 0 → Fin 0)).imp
    ((OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix (id : Fin 0 → Fin 0)).imp uniquenessSentence)) at hi
  exact .impE (.impE hi ObjectPowerUnion.source_ZF_total) ObjectPowerUnion.source_ZF_deterministic

theorem existence_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence existenceSentence) := TheoryTransport.sentence source_existence

theorem uniqueness_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence uniquenessSentence) := TheoryTransport.sentence source_uniqueness

theorem native_existence : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  ZFReplay.replay existence_kernel_certificate

theorem native_uniqueness : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence uniquenessSentence) :=
  ZFReplay.replay uniqueness_kernel_certificate
end PPAC.Migration.HierarchyRecursion
