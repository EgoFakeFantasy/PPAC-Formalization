/- Native original-kernel certificate for copies_uniform_margin:337 and
its actual missed-cost supremum, consumed by copiesHeightCost.margin:359.
All internal/nonstandard lengths; no internal choice or maximum oracle.
Same-parent full copiesHeightCost assembly and final Con remain open. -/
import PPAC.Migration.ConstructionMergerUniformMargin
import PPAC.Migration.ConstructionMergerCoordinateMarginSyntax
import PPAC.Migration.ConstructionWordArithmeticSyntax

namespace PPAC.Migration.ConstructionMergerUniformMarginSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 32
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 3)) (.imp
    (.mem (.bound 3) (.bound 0)) (.imp (ConstructionFractionOrder.carrier (0 : Fin 32) (1 : Fin 32))
    (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 32) (1 : Fin 32) (2 : Fin 32)) (.imp
    (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph (2 : Fin 32) (6 : Fin 32))) (.imp
    (ConstructionCutArithmeticSyntax.graph (0 : Fin 32) (1 : Fin 32) (2 : Fin 32) (4 : Fin 32))
    (.imp (ConstructionWordArithmeticSyntax.graph (0 : Fin 32) (1 : Fin 32) (2 : Fin 32) (5 : Fin
    32)) (.imp (.mem (.bound 7) (.bound 0)) (.imp (.existsE (.mem (.bound 0) (.bound 8))) (.imp
    (.mem (.bound 22) (.bound 0)) (.imp (Project.Formula.isOrdinalOne (.bound 22)) (.imp
    (ConstructionFractionOrder.coordinates (0 : Fin 32) (23 : Fin 32) (22 : Fin 32) (22 : Fin 32))
    (.imp (ConstructionRealCuts.principal (0 : Fin 32) (1 : Fin 32) (23 : Fin 32) (20 : Fin 32))
    (.imp (Project.Formula.isSuccessor (.bound 24) (.bound 22)) (.imp (.mem (.bound 24) (.bound 0))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (10 : Fin 32) (11 : Fin 32)
    (12 : Fin 32))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (10 : Fin 32) (11 :
    Fin 32) (12 : Fin 32))) (.imp (ConstructionProbeLetters.representatives (7 : Fin 32) (10 : Fin
    32) (14 : Fin 32)) (.imp (ConstructionMergerCopies.copies (7 : Fin 32) (10 : Fin 32) (11 : Fin
    32) (13 : Fin 32) (14 : Fin 32) (15 : Fin 32)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (16 : Fin 32) (14 : Fin 32) (15 : Fin 32))) (.imp
    (ConstructionMergerCopies.projectionGraph (7 : Fin 32) (10 : Fin 32) (11 : Fin 32) (13 : Fin 32)
    (14 : Fin 32) (16 : Fin 32)) (.imp (ConstructionMergerCopies.equalityLaw (7 : Fin 32) (10 : Fin
    32) (11 : Fin 32) (13 : Fin 32) (16 : Fin 32)) (.imp (ConstructionMergerAction.copyLaw (10 : Fin
    32) (11 : Fin 32) (16 : Fin 32) (17 : Fin 32)) (.imp (ConstructionProbeLetters.representatives
    (7 : Fin 32) (15 : Fin 32) (21 : Fin 32)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (8 : Fin 32) (21 : Fin 32) (2 : Fin 32))) (.imp (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (9 : Fin 32) (21 : Fin 32) (2 : Fin 32))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (18 : Fin 32) (10 : Fin 32) (2 : Fin 32)))
    (.imp (ConstructionCutWeights.rangeBound (20 : Fin 32) (18 : Fin 32)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (19 : Fin 32) (10 : Fin 32) (2 : Fin 32)))
    (.imp (ConstructionProbeGateCap.bounds (20 : Fin 32) (19 : Fin 32)) (.imp
    (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 32) (1 : Fin 32) (10 : Fin 32) (11 :
    Fin 32) (18 : Fin 32) (19 : Fin 32)) (.imp (ConstructionMergerCoordinates.graph (7 : Fin 32) (15
    : Fin 32) (16 : Fin 32) (18 : Fin 32) (3 : Fin 32) (8 : Fin 32)) (.imp
    (ConstructionMergerCoordinates.graph (7 : Fin 32) (15 : Fin 32) (16 : Fin 32) (19 : Fin 32) (20
    : Fin 32) (9 : Fin 32)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (18 : Fin 32)
    (12 : Fin 32) (25 : Fin 32))) (.imp (ConstructionCutDivision.value (0 : Fin 32) (1 : Fin 32) (24
    : Fin 32) (25 : Fin 32) (26 : Fin 32)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    (31 : Fin 32) (15 : Fin 32) (2 : Fin 32))) (.imp (.forallE (.forallE (.iff (ProjectSyntax.encode
    id (Source.SetLanguage.edge (33 : Fin 34) (1 : Fin 34) (0 : Fin 34))) (.conj (.mem (.bound 1)
    (.bound 17)) (ConstructionMergerFiniteWeights.costValue (2 : Fin 34) (3 : Fin 34) (9 : Fin 34)
    (4 : Fin 34) (7 : Fin 34) (8 : Fin 34) (22 : Fin 34) (28 : Fin 34) (11 : Fin 34) (1 : Fin 34) (0
    : Fin 34)))))) (.imp (.mem (.bound 27) (.bound 15)) (.imp (.mem (.bound 28) (.bound 15)) (.imp
    (ConstructionMergerFiniteWeights.heightValue (0 : Fin 32) (1 : Fin 32) (7 : Fin 32) (2 : Fin 32)
    (4 : Fin 32) (6 : Fin 32) (3 : Fin 32) (8 : Fin 32) (27 : Fin 32) (29 : Fin 32)) (.imp
    (ConstructionMergerFiniteWeights.heightValue (0 : Fin 32) (1 : Fin 32) (7 : Fin 32) (2 : Fin 32)
    (4 : Fin 32) (6 : Fin 32) (3 : Fin 32) (8 : Fin 32) (28 : Fin 32) (30 : Fin 32)) (.imp
    (ConstructionMergerCopyCones.reaches (10 : Fin 32) (17 : Fin 32) (27 : Fin 32) (28 : Fin 32))
    (.imp (.neg (Project.Formula.extensionalEq (.bound 27) (.bound 28))) (.existsE (.existsE (.conj
    (ConstructionRealCuts.cut (2 : Fin 34) (3 : Fin 34) (1 : Fin 34)) (.conj (.existsE (.conj
    (.forallE (.iff (.mem (.bound 0) (.bound 1)) (ConstructionMergerUniformMargin.costMember (14 :
    Fin 36) (19 : Fin 36) (21 : Fin 36) (35 : Fin 36) (31 : Fin 36) (32 : Fin 36) (0 : Fin 36))))
    (ConstructionRealCuts.supremum (0 : Fin 35) (2 : Fin 35)))) (.conj
    (ConstructionCutAddition.sumCut (2 : Fin 34) (3 : Fin 34) (31 : Fin 34) (1 : Fin 34) (0 : Fin
    34)) (.conj (.conj (Project.Formula.subset (.bound 0) (.bound 32)) (.neg (Project.Formula.subset
    (.bound 32) (.bound 0)))) (.forallE (.forallE (.imp (.mem (.bound 1) (.bound 19)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (35 : Fin 36) (1 : Fin 36) (0 : Fin 36)))
    (.imp (ConstructionMergerCopyCones.reaches (14 : Fin 36) (21 : Fin 36) (1 : Fin 36) (32 : Fin
    36)) (.imp (.neg (ConstructionMergerCopyCones.reaches (14 : Fin 36) (21 : Fin 36) (1 : Fin 36)
    (31 : Fin 36))) (Project.Formula.subset (.bound 0) (.bound
    3))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isSuccessor,Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionRealCuts.cut_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
      ConstructionCutArithmeticSyntax.graph_freeClosed,ConstructionWordArithmeticSyntax.graph_freeClosed,
      ConstructionCutWeights.rangeBound_freeClosed,ConstructionProbeGateCap.bounds_freeClosed,
      ConstructionMergerCopies.copies_freeClosed,ConstructionMergerCopies.projectionGraph_freeClosed,
      ConstructionMergerCopies.equalityLaw_freeClosed,ConstructionMergerAction.copyLaw_freeClosed,
      ConstructionMergerCoordinates.graph_freeClosed,
      ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,
      ConstructionMergerCopyCones.reaches_freeClosed,ConstructionMergerFiniteWeights.heightValue_freeClosed,
      ConstructionMergerFiniteWeights.costValue_freeClosed,ConstructionCutDivision.value_freeClosed,
      ConstructionCutAddition.sumCut_freeClosed,ConstructionRealCuts.supremum_freeClosed,
      ConstructionMergerUniformMargin.costMember_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_isSuccessor_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionRealCuts.cut_semantics hM,ConstructionProbeLetters.representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    KuratowskiZF.source_edge,
    ConstructionCutArithmeticSyntax.graph_semantics hM,ConstructionWordArithmeticSyntax.graph_semantics hM,
    ConstructionCutWeights.rangeBound_semantics hM,ConstructionProbeGateCap.bounds_semantics hM,
    ConstructionMergerCopies.copies_semantics hM,ConstructionMergerCopies.projectionGraph_semantics hM,
    ConstructionMergerCopies.equalityLaw_semantics hM,ConstructionMergerAction.copyLaw_semantics hM,
    ConstructionMergerCoordinates.graph_semantics hM,
    ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,ConstructionMergerCopyCones.reaches_semantics hM,
    ConstructionMergerFiniteWeights.heightValue_semantics hM,ConstructionMergerFiniteWeights.costValue_semantics hM,
    ConstructionCutDivision.value_semantics hM,ConstructionCutAddition.sumCut_semantics hM,
    ConstructionMergerUniformMargin.costMember_semantics hM,ConstructionRealCuts.supremum_semantics]
  intro hw hz hzw hQ hR hId hAdd hMul hn hnp ho hone hu hunit htwo htwow hm hc hC hL hp hProj hEq
    hCopy hJ hCH hCC hHeight hHB hCost hCB hUniform hGraph hCoordC hEdge hCap hNC hNCGraph hzL htL
    ha hb hReach hne
  change ∃ bd total, ConstructionRealCuts.Cut hM (bound 0) (bound 1) bd ∧
    ConstructionMergerUniformMargin.Cap (bound 10) (bound 15) (bound 17) (bound 31) (bound 27) (bound 28) bd ∧
    ConstructionCutAddition.SumCut hM (bound 0) (bound 1) (bound 29) bd total ∧
    ConstructionProbeIntervals.Strict total (bound 30) ∧
    ConstructionMergerUniformMargin.MissedBound (bound 10) (bound 15) (bound 17) (bound 31) (bound 27) (bound 28) bd
  have hACut : ConstructionRealCuts.Cut hM (bound 0) (bound 1) (bound 29) := by
    obtain ⟨sum,hSum,hDiv⟩ := ha
    exact ConstructionCutDivision.value_cut hw hQ hn hnp
      ((hR sum).mp (ConstructionMergerFiniteWeights.coordinateEval_range hM hSum)) hDiv
  apply ConstructionMergerUniformMargin.canonical_uniform hM hw hQ hR hNC hACut
  exact ConstructionMergerUniformMargin.copies_uniform_margin hM hw hz hzw hQ hR hId hAdd hMul hn
    hnp ho hone hu hunit htwo htwow hm hc hC hL hp hProj hEq hCopy hJ hCH hCC hHeight hHB hCost hCB
    hUniform hGraph hCoordC hEdge hCap hNCGraph hzL htL ha hb hReach hne

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerUniformMarginSyntax
