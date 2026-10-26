/- Original-kernel pure-member certificate for COMPLETE source Word HeightCost.
Constructs actual height/cap/cost graphs, all strict uniform margins on internal
words, graph uniqueness and common old/new missed-cost suprema. -/
import PPAC.Migration.ConstructionProbeHeightCost
import PPAC.Migration.ConstructionProbeNewOldMarginSyntax
import PPAC.Migration.ConstructionProbeOldCostSupremumSyntax

namespace PPAC.Migration.ConstructionProbeHeightCostSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Inputs: w D S zero mul A b W Q R Emb H C V e G unitW unit E I
Off F B K one u four. NO new height/cap/cost graph or new margin is assumed. -/
def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 27
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 27))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin 27)))
    (.imp (.mem (.bound (3 : Fin 27)) (.bound (0 : Fin 27))) (.imp (ConstructionFractionOrder.carrier (0 : Fin
    27) (8 : Fin 27)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 27) (8 : Fin 27) (9 : Fin 27)) (.imp
    (ConstructionFractionOrder.coordinates (0 : Fin 27) (25 : Fin 27) (24 : Fin 27) (24 : Fin 27)) (.imp
    (Project.Formula.isOrdinalOne (.bound (24 : Fin 27))) (.imp (ConstructionRealCuts.principal (0 : Fin 27) (8
    : Fin 27) (25 : Fin 27) (17 : Fin 27)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid
    (1 : Fin 27) (4 : Fin 27) (14 : Fin 27))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 :
    Fin 27) (4 : Fin 27) (14 : Fin 27))) (.imp (ConstructionProbeAlphabet.alphabet (1 : Fin 27) (4 : Fin 27) (14
    : Fin 27) (2 : Fin 27) (19 : Fin 27) (5 : Fin 27) (18 : Fin 27)) (.imp (.mem (.bound (6 : Fin 27)) (.bound
    (1 : Fin 27))) (.imp (.neg (Project.Formula.extensionalEq (.bound (6 : Fin 27)) (.bound (14 : Fin 27))))
    (.imp (ConstructionProbeWord.wordCarrier (0 : Fin 27) (1 : Fin 27) (2 : Fin 27) (4 : Fin 27) (5 : Fin 27) (6
    : Fin 27) (7 : Fin 27)) (.imp (ConstructionProbeWordMonoidSyntax.multiplicationGraph (0 : Fin 27) (1 : Fin
    27) (2 : Fin 27) (3 : Fin 27) (4 : Fin 27) (5 : Fin 27) (6 : Fin 27) (7 : Fin 27) (18 : Fin 27) (15 : Fin
    27)) (.imp (ConstructionProbeRaw.old (3 : Fin 27) (1 : Fin 27) (14 : Fin 27) (16 : Fin 27)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 27) (1 : Fin 27) (7 : Fin 27))) (.imp
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (3 : Fin 27) (1 : Fin 27) (10 : Fin 27)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 27) (1 : Fin 27) (9 : Fin 27))) (.imp
    (ConstructionCutWeights.rangeBound (17 : Fin 27) (11 : Fin 27)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (12 : Fin 27) (1 : Fin 27) (9 : Fin 27))) (.imp (ConstructionProbeGateCap.bounds
    (17 : Fin 27) (12 : Fin 27)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (20 : Fin 27) (2 :
    Fin 27) (9 : Fin 27))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 27) (2 : Fin 27)
    (9 : Fin 27))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (22 : Fin 27) (2 : Fin 27) (9 : Fin
    27))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (21 : Fin 27) (2 : Fin 27) (9 : Fin 27)))
    (.imp (ConstructionProbeLetterFloorSyntax.floorLaws (1 : Fin 27) (2 : Fin 27) (5 : Fin 27) (23 : Fin 27) (11
    : Fin 27) (21 : Fin 27)) (.imp (ConstructionProbeCostBoundsSyntax.costBounds (0 : Fin 27) (8 : Fin 27) (1 :
    Fin 27) (4 : Fin 27) (2 : Fin 27) (5 : Fin 27) (23 : Fin 27) (11 : Fin 27) (12 : Fin 27) (21 : Fin 27))
    (.imp (ConstructionProbeHeightIntervalsSyntax.laws (0 : Fin 27) (8 : Fin 27) (26 : Fin 27) (1 : Fin 27) (4 :
    Fin 27) (2 : Fin 27) (5 : Fin 27) (23 : Fin 27) (18 : Fin 27) (11 : Fin 27) (12 : Fin 27) (21 : Fin 27) (20
    : Fin 27) (13 : Fin 27) (22 : Fin 27)) (.imp (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 27)
    (8 : Fin 27) (1 : Fin 27) (4 : Fin 27) (11 : Fin 27) (12 : Fin 27)) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 27) (4 : Fin 27)) (.imp
    (ConstructionProbeConservativeSyntax.conservative (1 : Fin 27) (7 : Fin 27) (4 : Fin 27) (15 : Fin 27) (10 :
    Fin 27)) (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (2 : Fin
    30) (10 : Fin 30) (12 : Fin 30))) (.conj (ConstructionProbeHeightFoldSyntax.laws (3 : Fin 30) (4 : Fin 30)
    (5 : Fin 30) (6 : Fin 30) (10 : Fin 30) (11 : Fin 30) (14 : Fin 30) (23 : Fin 30) (16 : Fin 30) (2 : Fin
    30)) (.conj (ConstructionCutWeights.rangeBound (20 : Fin 30) (2 : Fin 30)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (1 : Fin 30) (10 : Fin 30) (12 : Fin 30))) (.conj (ConstructionProbeGateCap.graph
    (4 : Fin 30) (10 : Fin 30) (7 : Fin 30) (18 : Fin 30) (13 : Fin 30) (15 : Fin 30) (20 : Fin 30) (1 : Fin
    30)) (.conj (ConstructionProbeGateCap.bounds (20 : Fin 30) (1 : Fin 30)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 30) (10 : Fin 30) (12 : Fin 30))) (.conj
    (ConstructionProbeCostFoldSyntax.laws (3 : Fin 30) (4 : Fin 30) (5 : Fin 30) (6 : Fin 30) (10 : Fin 30) (11
    : Fin 30) (15 : Fin 30) (16 : Fin 30) (1 : Fin 30) (0 : Fin 30)) (.conj (ConstructionProbeGateCap.bounds (20
    : Fin 30) (0 : Fin 30)) (.conj (ConstructionProbeIntervalsSyntax.uniformMargins (3 : Fin 30) (11 : Fin 30)
    (10 : Fin 30) (18 : Fin 30) (2 : Fin 30) (0 : Fin 30)) (.conj (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (6 : Fin 34) (3 : Fin 34) (1 : Fin 34))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (6 : Fin 34) (2 : Fin 34) (0 : Fin 34))) (.imp
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (14 : Fin 34) (22 : Fin 34) (3 : Fin 34) (2 : Fin
    34))) (.imp (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (14 : Fin 34) (22 : Fin 34) (2 :
    Fin 34) (3 : Fin 34)))) (.existsE (.existsE (.conj (ConstructionRealCuts.cut (9 : Fin 36) (17 : Fin 36) (1 :
    Fin 36)) (.conj (ConstructionProbeCostSupremum.cap (16 : Fin 36) (24 : Fin 36) (6 : Fin 36) (5 : Fin 36) (4
    : Fin 36) (1 : Fin 36)) (.conj (ConstructionCutAddition.sumCut (9 : Fin 36) (17 : Fin 36) (3 : Fin 36) (1 :
    Fin 36) (0 : Fin 36)) (.conj (.conj (Project.Formula.subset (.bound (0 : Fin 36)) (.bound (2 : Fin 36)))
    (.neg (Project.Formula.subset (.bound (2 : Fin 36)) (.bound (0 : Fin 36)))))
    (ConstructionProbeIntervalsSyntax.missedBound (16 : Fin 36) (24 : Fin 36) (6 : Fin 36) (5 : Fin 36) (4 : Fin
    36) (1 : Fin 36)))))))))))))))) (.conj (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    (0 : Fin 31) (11 : Fin 31) (13 : Fin 31))) (.imp (ConstructionProbeHeightFoldSyntax.laws (4 : Fin 31) (5 :
    Fin 31) (6 : Fin 31) (7 : Fin 31) (11 : Fin 31) (12 : Fin 31) (15 : Fin 31) (24 : Fin 31) (17 : Fin 31) (0 :
    Fin 31)) (Project.Formula.extensionalEq (.bound (0 : Fin 31)) (.bound (3 : Fin 31)))))) (.conj (.forallE
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 31) (11 : Fin 31) (13 : Fin 31))) (.imp
    (ConstructionProbeCostFoldSyntax.laws (4 : Fin 31) (5 : Fin 31) (6 : Fin 31) (7 : Fin 31) (11 : Fin 31) (12
    : Fin 31) (16 : Fin 31) (17 : Fin 31) (2 : Fin 31) (0 : Fin 31)) (Project.Formula.extensionalEq (.bound (0 :
    Fin 31)) (.bound (1 : Fin 31)))))) (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (17 : Fin 34) (3 : Fin 34) (1 : Fin 34))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (17 : Fin 34) (2 : Fin 34) (0 : Fin 34))) (.existsE (.existsE (.existsE (.conj
    (ConstructionProbeCostSupremum.family (11 : Fin 37) (14 : Fin 37) (22 : Fin 37) (6 : Fin 37) (5 : Fin 37) (2
    : Fin 37)) (.conj (ConstructionProbeCostSupremum.family (17 : Fin 37) (25 : Fin 37) (7 : Fin 37) (4 : Fin
    37) (3 : Fin 37) (1 : Fin 37)) (.conj (ConstructionRealCuts.cut (10 : Fin 37) (18 : Fin 37) (0 : Fin 37))
    (.conj (ConstructionProbeCostSupremum.cap (11 : Fin 37) (14 : Fin 37) (22 : Fin 37) (6 : Fin 37) (5 : Fin
    37) (0 : Fin 37)) (.conj (ConstructionProbeCostSupremum.cap (17 : Fin 37) (25 : Fin 37) (7 : Fin 37) (4 :
    Fin 37) (3 : Fin 37) (0 : Fin 37)) (.forallE (.forallE (.imp (ConstructionProbeCostSupremum.cap (13 : Fin
    39) (16 : Fin 39) (24 : Fin 39) (8 : Fin 39) (7 : Fin 39) (1 : Fin 39)) (.imp
    (ConstructionProbeCostSupremum.cap (19 : Fin 39) (27 : Fin 39) (9 : Fin 39) (6 : Fin 39) (5 : Fin 39) (0 :
    Fin 39)) (Project.Formula.extensionalEq (.bound (1 : Fin 39)) (.bound (0 : Fin
    39)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionFractionOrder.coordinates_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionProbeAlphabet.alphabet_freeClosed,ConstructionProbeWord.wordCarrier_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,ConstructionProbeRaw.old_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,
      ConstructionProbeGateCap.bounds_freeClosed,ConstructionProbeLetterFloorSyntax.floorLaws_freeClosed,
      ConstructionProbeCostBoundsSyntax.costBounds_freeClosed,ConstructionProbeHeightIntervalsSyntax.laws_freeClosed,
      ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeHeightFoldSyntax.laws_freeClosed,ConstructionProbeGateCap.graph_freeClosed,
      ConstructionProbeCostFoldSyntax.laws_freeClosed,ConstructionProbeCostSupremum.family_freeClosed,
      ConstructionProbeCostSupremum.cap_freeClosed,ConstructionRealCuts.cut_freeClosed,
      ConstructionCutAddition.sumCut_freeClosed,ConstructionProbeIntervalsSyntax.missedBound_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,Project.Formula.satisfies_isOrdinalOne_iff,
    ConstructionRealCuts.principal_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeAlphabet.alphabet_semantics hM,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionProbeWord.wordCarrier_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,ConstructionProbeRaw.old_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    ConstructionCutWeights.rangeBound_semantics hM,ConstructionProbeGateCap.bounds_semantics hM,
    ConstructionProbeLetterFloorSyntax.floorLaws_semantics hM,ConstructionProbeCostBoundsSyntax.costBounds_semantics hM,
    ConstructionProbeHeightIntervalsSyntax.laws_semantics hM,ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionProbeHeightFoldSyntax.laws_semantics hM,ConstructionProbeGateCap.graph_semantics hM,
    ConstructionProbeCostFoldSyntax.laws_semantics hM,Project.Formula.satisfies_forall_iff,
    KuratowskiZF.source_edge,ConstructionProbeCostSupremum.family_semantics hM,
    ConstructionProbeCostSupremum.cap_semantics hM,ConstructionRealCuts.cut_semantics hM,
    ConstructionCutAddition.sumCut_semantics hM,Project.Formula.satisfies_subset_iff,
    ConstructionProbeIntervalsSyntax.missedBound_semantics hM,ConstructionBaseMonoid.divides_semantics (M := M)]
  exact ConstructionProbeHeightCost.exists_heightCost hM

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeHeightCostSyntax
