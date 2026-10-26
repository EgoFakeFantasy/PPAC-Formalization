/- Original-kernel native-ZF certificates for the Base margin adapters. -/
import PPAC.Migration.ConstructionBaseUniformMargin
import PPAC.Migration.ConstructionProbeIntervalsSyntax

namespace PPAC.Migration.ConstructionBaseUniformMarginSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionBaseUniformMargin
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def data {m : Nat} (w mul zero one two three Q R H C unitCode unit : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionBaseMonoid.graph w mul) (.conj (Project.Formula.isEmpty (.bound zero)) (.conj
  (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid w mul zero)) (.conj (ProjectSyntax.encode
  id (ForcingDiagramPoset.conical w mul zero)) (.conj (.neg (Project.Formula.extensionalEq (.bound one)
  (.bound zero))) (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.joinsFormula w mul)) (.conj
  (ConstructionBaseWeights.digits w one two three) (.conj (ConstructionFractionOrder.carrier w Q) (.conj
  (ConstructionRealCuts.cutCarrier w Q R) (.conj (ConstructionCutWeights.graph true w one two one Q H)
  (.conj (ConstructionCutWeights.graph false w one two three Q C) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo H w R)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo C w R))
  (.conj (ConstructionFractionOrder.coordinates w unitCode one one) (.conj (ConstructionRealCuts.principal
  w Q unitCode unit) (.conj (.mem (.bound unit) (.bound R)) (.conj (ConstructionCutWeights.rangeBound unit
  H) (.conj (ConstructionCutWeights.rangeBound unit C) (.conj
  (ConstructionProbeLetterFloorSyntax.heightOrder w mul R H) (.conj
  (ConstructionProbeCostBoundsSyntax.pointBound w w mul H C) (.conj (ConstructionBaseHeightGap.marginLaw w
  Q H C) (ConstructionProbeIntervalsSyntax.uniformMargins w Q w mul H C))))))))))))))))))))))

theorem data_freeClosed {m : Nat} (w mul zero one two three Q R H C unitCode unit : Fin m) : (data w mul zero one two three Q R H C unitCode unit).FreeClosed := by
  simp -implicitDefEqProofs
  [data,Definitional.Formula.FreeClosed,ConstructionBaseMonoid.graph_freeClosed,ProjectSyntax.freeClosed,ConstructionBaseWeights.digits_freeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionCutWeights.graph_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,ConstructionRealCuts.principal_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,ConstructionProbeLetterFloorSyntax.heightOrder_freeClosed,ConstructionProbeCostBoundsSyntax.pointBound_freeClosed,ConstructionBaseHeightGap.marginLaw_freeClosed,ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w mul zero one two three Q R H C unitCode unit : Fin m) :
    Project.Formula.satisfies env (data w mul zero one two three Q R H C unitCode unit) ↔
  Data hM (env.bound w) (env.bound mul) (env.bound zero) (env.bound one) (env.bound two) (env.bound three)
  (env.bound Q) (env.bound R) (env.bound H) (env.bound C) (env.bound unitCode) (env.bound unit) := by
  simp only [data,Data,Project.Formula.satisfies_conj_iff,ConstructionBaseMonoid.graph_semantics
  hM,Project.Formula.satisfies_isEmpty_iff,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality
  hM),ForcingDiagramPoset.leftCancelMonoid_semantics,ForcingDiagramPoset.conical_semantics,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq
  (ModelTransfer.extensionality
  hM),ConstructionBaseMonoid.joinsFormula_semantics,ConstructionBaseWeights.digits_semantics,ConstructionFractionOrder.carrier_semantics
  hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionCutWeights.graph_semantics
  hM,ForcingSupportSize.mapsTo_semantics (M := M),ConstructionFractionOrder.coordinates_semantics
  hM,ConstructionRealCuts.principal_semantics
  hM,Project.Formula.satisfies_mem_iff,ConstructionCutWeights.rangeBound_semantics
  hM,ConstructionProbeLetterFloorSyntax.heightOrder_semantics
  hM,ConstructionProbeCostBoundsSyntax.pointBound_semantics
  hM,ConstructionBaseHeightGap.marginLaw_semantics
  hM,ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,Project.Term.eval_bound]
  rfl

def bridgeSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 5
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 5))) (.imp (ConstructionFractionOrder.carrier (0 : Fin
    5) (1 : Fin 5)) (.imp (ConstructionPrincipalAddition.principalAdd (0 : Fin 5) (1 : Fin 5) (2 : Fin 5)
    (3 : Fin 5) (4 : Fin 5)) (ConstructionCutAddition.sumCut (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (3 : Fin
    5) (4 : Fin 5)))))
  freeClosed := by
    simp -implicitDefEqProofs
    [Definitional.Formula.FreeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionPrincipalAddition.principalAdd_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem bridge_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence bridgeSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) bridgeSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only
  [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,ConstructionFractionOrder.carrier_semantics
  hM,ConstructionPrincipalAddition.principalAdd_semantics hM,ConstructionCutAddition.sumCut_semantics
  hM,Project.Term.eval_bound]
  exact ConstructionPrincipalSumBridge.principal_sum hM

theorem bridge_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence bridgeSentence) := ModelTransfer.derives (fun _ hM => bridge_models hM)

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 1))) (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (data (0 : Fin
    1).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin (1+11)) (9 : Fin (1+11)) (8 : Fin
    (1+11)) (7 : Fin (1+11)) (6 : Fin (1+11)) (5 : Fin (1+11)) (4 : Fin (1+11)) (3 : Fin (1+11)) (2 : Fin
    (1+11)) (1 : Fin (1+11)) (0 : Fin (1+11)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,data_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only
  [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_exists_iff,data_semantics
  hM,Project.Term.eval_bound]
  exact exists_base hM

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionBaseUniformMarginSyntax
