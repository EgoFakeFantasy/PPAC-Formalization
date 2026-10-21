import PPAC.Migration.ObjectTransfiniteRecursion

/-! 无总性/单值性残留前提的实际实例：Φ(x,h,y)为y=x，全部内部原序数上有唯一递归图。 -/
namespace PPAC.Migration.ObjectTransfiniteRecursionIdentity
open Source SourceLogic GraphSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionTotal OrdinalRecursionDeterminism OrdinalRecursionExistenceSyntax

def matrix : Formula 3 := .equal 2 0

def sentence : Source.Sentence := allUnique matrix (id : Fin 0 → Fin 0)

theorem source_total : Derives (Source.SetLanguage.ZF.at 0) (total matrix (id : Fin 0 → Fin 0)) := by
  change Derives (Source.SetLanguage.ZF.at 0) (.all (.all
    (((ordinal (0 : Fin 2)).conj (functionOn 1 0)).imp (.ex (.equal (Fin.last 2) (0 : Fin 2).castSucc)))))
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.exI (0 : Fin 2)
  exact .eqRefl 0

theorem source_deterministic : Derives (Source.SetLanguage.ZF.at 0) (deterministic matrix (id : Fin 0 → Fin 0)) := by
  change Derives (Source.SetLanguage.ZF.at 0) (.all (.all
    (((ordinal (0 : Fin 2)).conj (functionOn 1 0)).imp (.all (.all
      ((Formula.equal (2 : Fin 4) 0).imp ((Formula.equal 3 0).imp (.equal 2 3))))))))
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  exact eq_trans (.hyp (Or.inr (Or.inl rfl))) (eq_symm (.hyp (Or.inl rfl)))

theorem source_proof : Derives (Source.SetLanguage.ZF.at 0) sentence := by
  have hi := ObjectTransfiniteRecursion.source_uniqueness matrix
  change Derives (Source.SetLanguage.ZF.at 0) ((total matrix (id : Fin 0 → Fin 0)).imp
    ((deterministic matrix (id : Fin 0 → Fin 0)).imp sentence)) at hi
  exact .impE (.impE hi source_total) source_deterministic

theorem kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence sentence) := TheoryTransport.sentence source_proof

theorem native_proof : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ZFReplay.replay kernel_certificate
end PPAC.Migration.ObjectTransfiniteRecursionIdentity
