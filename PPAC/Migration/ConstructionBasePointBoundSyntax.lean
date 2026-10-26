/- Native closed certificate: existing full Base margin plus the probe PointBound
on the same constructed arithmetic and height/cost graphs. -/
import PPAC.Migration.ConstructionBasePointBound

namespace PPAC.Migration.ConstructionBasePointBoundSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1 (.imp (Project.Formula.isOmega (.bound 0))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionBaseMonoid.graph (10 : Fin 11) (9 : Fin 11)) (.conj (ConstructionBaseWeights.digits (10 : Fin
    11) (8 : Fin 11) (7 : Fin 11) (6 : Fin 11)) (.conj (ConstructionFractionOrder.carrier (10 : Fin 11) (5 :
    Fin 11)) (.conj (cutCarrier (10 : Fin 11) (5 : Fin 11) (4 : Fin 11)) (.conj (ConstructionCutWeights.graph
    true (10 : Fin 11) (8 : Fin 11) (7 : Fin 11) (8 : Fin 11) (5 : Fin 11) (3 : Fin 11)) (.conj
    (ConstructionCutWeights.graph false (10 : Fin 11) (8 : Fin 11) (7 : Fin 11) (6 : Fin 11) (5 : Fin 11) (2 :
    Fin 11)) (.conj (ConstructionCutWeights.rangeCuts (4 : Fin 11) (3 : Fin 11)) (.conj
    (ConstructionCutWeights.rangeCuts (4 : Fin 11) (2 : Fin 11)) (.conj (ConstructionFractionOrder.coordinates
    (10 : Fin 11) (1 : Fin 11) (8 : Fin 11) (8 : Fin 11)) (.conj (principal (10 : Fin 11) (5 : Fin 11) (1 :
    Fin 11) (0 : Fin 11)) (.conj (.mem (.bound (0 : Fin 11)) (.bound (4 : Fin 11))) (.conj
    (ConstructionCutWeights.rangeBound (0 : Fin 11) (3 : Fin 11)) (.conj (ConstructionCutWeights.rangeBound (0
    : Fin 11) (2 : Fin 11)) (.conj (ConstructionBaseHeightGap.marginLaw (10 : Fin 11) (5 : Fin 11) (3 : Fin
    11) (2 : Fin 11)) (ConstructionProbeCostBoundsSyntax.pointBound (10 : Fin 11) (10 : Fin 11) (9 : Fin 11)
    (3 : Fin 11) (2 : Fin 11)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionBaseMonoid.graph_freeClosed,
      ConstructionBaseWeights.digits_freeClosed,ConstructionFractionOrder.carrier_freeClosed,
      cutCarrier_freeClosed,ConstructionCutWeights.graph_freeClosed,ConstructionCutWeights.rangeCuts_freeClosed,
      ConstructionFractionOrder.coordinates_freeClosed,principal_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,
      ConstructionBaseHeightGap.marginLaw_freeClosed,ConstructionProbeCostBoundsSyntax.pointBound_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound]
  intro hw
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionBaseMonoid.graph_semantics hM,ConstructionBaseWeights.digits_semantics,
    ConstructionFractionOrder.carrier_semantics hM,cutCarrier_semantics hM,
    ConstructionCutWeights.graph_semantics hM,ConstructionCutWeights.rangeCuts_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,principal_semantics hM,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionCutWeights.rangeBound_semantics hM,
    ConstructionBaseHeightGap.marginLaw_semantics hM,ConstructionProbeCostBoundsSyntax.pointBound_semantics hM]
  exact ConstructionBasePointBound.exists_base hM hw

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionBasePointBoundSyntax
