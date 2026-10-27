/- Original-kernel certificate for the SAME actual weighted successor and old
inclusion, including the old distinguished nonunit, exact weights and suprema.
This composes existing producers; path/alphabet/interval premises stay explicit. -/
import PPAC.Migration.ConstructionProbeSuccessor
import PPAC.Migration.ConstructionProbeHeightCostSyntax
import PPAC.Migration.ConstructionProbeMappedPathSyntax
import PPAC.Migration.ConstructionProbeNewOldMarginSyntax
import PPAC.Migration.ConstructionProbeOldCostSupremumSyntax

namespace PPAC.Migration.ConstructionProbeSuccessorSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 30
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 30))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin
    30))) (.imp (.mem (.bound (3 : Fin 30)) (.bound (0 : Fin 30))) (.imp (ConstructionFractionOrder.carrier
    (0 : Fin 30) (7 : Fin 30)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 30) (7 : Fin 30) (8 : Fin
    30)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 30) (21 : Fin 30) (20 : Fin 30) (20 : Fin
    30)) (.imp (Project.Formula.isOrdinalOne (.bound (20 : Fin 30))) (.imp (ConstructionRealCuts.principal
    (0 : Fin 30) (7 : Fin 30) (21 : Fin 30) (13 : Fin 30)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 30) (4 : Fin 30) (12 : Fin 30))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 30) (4 : Fin 30) (12 : Fin 30))) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 30) (4 : Fin 30) (12 : Fin 30) (2 : Fin 30) (15 : Fin 30)
    (5 : Fin 30) (14 : Fin 30)) (.imp (.mem (.bound (6 : Fin 30)) (.bound (1 : Fin 30))) (.imp (.neg
    (Project.Formula.extensionalEq (.bound (6 : Fin 30)) (.bound (12 : Fin 30)))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (9 : Fin 30) (1 : Fin 30) (8 : Fin 30))) (.imp
    (ConstructionCutWeights.rangeBound (13 : Fin 30) (9 : Fin 30)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (10 : Fin 30) (1 : Fin 30) (8 : Fin 30))) (.imp
    (ConstructionProbeGateCap.bounds (13 : Fin 30) (10 : Fin 30)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (16 : Fin 30) (2 : Fin 30) (8 : Fin 30))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (11 : Fin 30) (2 : Fin 30) (8 : Fin 30))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (18 : Fin 30) (2 : Fin 30) (8 : Fin 30))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (17 : Fin 30) (2 : Fin 30) (8 : Fin 30))) (.imp
    (ConstructionProbeLetterFloorSyntax.floorLaws (1 : Fin 30) (2 : Fin 30) (5 : Fin 30) (19 : Fin 30) (9 :
    Fin 30) (17 : Fin 30)) (.imp (ConstructionProbeCostBoundsSyntax.costBounds (0 : Fin 30) (7 : Fin 30) (1
    : Fin 30) (4 : Fin 30) (2 : Fin 30) (5 : Fin 30) (19 : Fin 30) (9 : Fin 30) (10 : Fin 30) (17 : Fin 30))
    (.imp (ConstructionProbeHeightIntervalsSyntax.laws (0 : Fin 30) (7 : Fin 30) (22 : Fin 30) (1 : Fin 30)
    (4 : Fin 30) (2 : Fin 30) (5 : Fin 30) (19 : Fin 30) (14 : Fin 30) (9 : Fin 30) (10 : Fin 30) (17 : Fin
    30) (16 : Fin 30) (11 : Fin 30) (18 : Fin 30)) (.imp (ConstructionProbeIntervalsSyntax.uniformMargins (0
    : Fin 30) (7 : Fin 30) (1 : Fin 30) (4 : Fin 30) (9 : Fin 30) (10 : Fin 30)) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 30) (4 : Fin 30)) (.imp
    (ConstructionProbeCones.coneLaws (0 : Fin 30) (1 : Fin 30) (4 : Fin 30) (12 : Fin 30) (3 : Fin 30) (23 :
    Fin 30) (24 : Fin 30) (2 : Fin 30) (25 : Fin 30) (5 : Fin 30)) (.imp (.mem (.bound (26 : Fin 30))
    (.bound (1 : Fin 30))) (.imp (.neg (Project.Formula.extensionalEq (.bound (26 : Fin 30)) (.bound (12 :
    Fin 30)))) (.imp (ConstructionProbePath.path (0 : Fin 30) (1 : Fin 30) (4 : Fin 30) (12 : Fin 30) (3 :
    Fin 30) (27 : Fin 30) (23 : Fin 30)) (.imp (ConstructionProbeLetters.representatives (0 : Fin 30) (1 :
    Fin 30) (28 : Fin 30)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (25 : Fin 30) (28 : Fin
    30) (2 : Fin 30))) (.imp (ConstructionProbePath.terminalTable (0 : Fin 30) (1 : Fin 30) (4 : Fin 30) (23
    : Fin 30) (27 : Fin 30) (29 : Fin 30)) (.imp (ConstructionProbeTarget.targetLaws (4 : Fin 30) (25 : Fin
    30) (29 : Fin 30) (5 : Fin 30) (19 : Fin 30)) (.imp (ConstructionProbeAlphabet.exitGraph (4 : Fin 30)
    (19 : Fin 30) (26 : Fin 30) (14 : Fin 30)) (.imp (ConstructionProbeLetters.letters (0 : Fin 30) (1 : Fin
    30) (4 : Fin 30) (24 : Fin 30) (28 : Fin 30) (2 : Fin 30)) (.imp
    (ConstructionProbeLetters.projectionGraph (0 : Fin 30) (1 : Fin 30) (4 : Fin 30) (24 : Fin 30) (28 : Fin
    30) (25 : Fin 30)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionProbeWord.wordCarrier (12 : Fin 42) (13 :
    Fin 42) (14 : Fin 42) (16 : Fin 42) (17 : Fin 42) (18 : Fin 42) (11 : Fin 42)) (.conj
    (ConstructionProbeRaw.old (15 : Fin 42) (13 : Fin 42) (24 : Fin 42) (10 : Fin 42)) (.conj
    (ConstructionProbeLetters.representatives (11 : Fin 42) (11 : Fin 42) (9 : Fin 42)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (8 : Fin 42) (9 : Fin 42) (11 : Fin 42))) (.conj
    (ConstructionProbeWordMonoidSyntax.multiplicationGraph (12 : Fin 42) (13 : Fin 42) (14 : Fin 42) (15 :
    Fin 42) (16 : Fin 42) (17 : Fin 42) (18 : Fin 42) (11 : Fin 42) (26 : Fin 42) (8 : Fin 42)) (.conj
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (11 : Fin 42) (8 : Fin 42) (10 : Fin
    42))) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical (11 : Fin 42) (8 : Fin 42) (10 : Fin
    42))) (.conj (ConstructionProbeSharedIntersections.conditionalJoins (11 : Fin 42) (8 : Fin 42)) (.conj
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (15 : Fin 42) (13 : Fin 42) (7 : Fin 42)) (.conj
    (ConstructionProbeConservativeSyntax.conservative (13 : Fin 42) (11 : Fin 42) (16 : Fin 42) (8 : Fin 42)
    (7 : Fin 42)) (.conj (ConstructionProbeOldEmbeddingSyntax.embeddingLaws (12 : Fin 42) (13 : Fin 42) (14
    : Fin 42) (15 : Fin 42) (16 : Fin 42) (17 : Fin 42) (11 : Fin 42) (8 : Fin 42) (24 : Fin 42) (10 : Fin
    42) (7 : Fin 42)) (.conj (ConstructionPersistentProfiles.hasOldGates (13 : Fin 42) (11 : Fin 42) (16 :
    Fin 42) (8 : Fin 42) (7 : Fin 42)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (7 : Fin 42)
    (38 : Fin 42) (6 : Fin 42))) (.conj (.mem (.bound (6 : Fin 42)) (.bound (11 : Fin 42))) (.conj (.neg
    (Project.Formula.extensionalEq (.bound (6 : Fin 42)) (.bound (10 : Fin 42)))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 : Fin 42) (14 : Fin 42) (11 : Fin 42))) (.conj
    (ConstructionProbeGeneratorSyntax.generatorGraph (12 : Fin 42) (13 : Fin 42) (14 : Fin 42) (10 : Fin 42)
    (5 : Fin 42)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (4 : Fin 42) (12 : Fin 42) (11
    : Fin 42))) (.conj (ConstructionProbeIndexedGeneratorsSyntax.probeGraph (12 : Fin 42) (37 : Fin 42) (24
    : Fin 42) (5 : Fin 42) (4 : Fin 42)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (4 : Fin
    42) (15 : Fin 42) (3 : Fin 42))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (7 : Fin 42)
    (39 : Fin 42) (2 : Fin 42))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (7 : Fin 42) (18 :
    Fin 42) (1 : Fin 42))) (.conj (ConstructionProbeMappedPathSyntax.nodeMap (35 : Fin 42) (7 : Fin 42) (0 :
    Fin 42)) (.conj (ConstructionPersistentProfiles.probeProfile (12 : Fin 42) (11 : Fin 42) (8 : Fin 42) (2
    : Fin 42) (1 : Fin 42) (6 : Fin 42) (3 : Fin 42) (0 : Fin 42)) (.conj (.forallE (.neg
    (ProjectSyntax.encode id (Source.SetLanguage.edge (8 : Fin 43) (0 : Fin 43) (4 : Fin 43))))) (.conj
    (.forallE (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound (13 : Fin
    43)) (.bound (0 : Fin 43))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (14 : Fin 43) (0 :
    Fin 43))) (ProjectSyntax.encode id (ForcingSupportSize.small (12 : Fin 43) (0 : Fin 43)))))) (.conj
    (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionPersistentProfiles.probeProfile (17
    : Fin 47) (18 : Fin 47) (21 : Fin 47) (4 : Fin 47) (3 : Fin 47) (2 : Fin 47) (1 : Fin 47) (0 : Fin 47))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionProbeMappedPathSyntax.nodeMap (5 :
    Fin 52) (17 : Fin 52) (4 : Fin 52)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (17 : Fin
    52) (9 : Fin 52) (3 : Fin 52))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (17 : Fin 52)
    (8 : Fin 52) (2 : Fin 52))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (17 : Fin 52) (7 :
    Fin 52) (1 : Fin 52))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (17 : Fin 52) (6 : Fin
    52) (0 : Fin 52))) (ConstructionPersistentProfiles.probeProfile (22 : Fin 52) (21 : Fin 52) (18 : Fin
    52) (3 : Fin 52) (2 : Fin 52) (1 : Fin 52) (0 : Fin 52) (4 : Fin 52)))))))))))))))))) (.existsE
    (.existsE (.existsE (.conj (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (2 : Fin 45) (14 :
    Fin 45) (23 : Fin 45))) (.conj (ConstructionProbeHeightFoldSyntax.laws (15 : Fin 45) (16 : Fin 45) (17 :
    Fin 45) (18 : Fin 45) (14 : Fin 45) (22 : Fin 45) (24 : Fin 45) (31 : Fin 45) (26 : Fin 45) (2 : Fin
    45)) (.conj (ConstructionCutWeights.rangeBound (28 : Fin 45) (2 : Fin 45)) (.conj (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (1 : Fin 45) (14 : Fin 45) (23 : Fin 45))) (.conj
    (ConstructionProbeGateCap.graph (16 : Fin 45) (14 : Fin 45) (19 : Fin 45) (11 : Fin 45) (10 : Fin 45)
    (25 : Fin 45) (28 : Fin 45) (1 : Fin 45)) (.conj (ConstructionProbeGateCap.bounds (28 : Fin 45) (1 : Fin
    45)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 45) (14 : Fin 45) (23 : Fin
    45))) (.conj (ConstructionProbeCostFoldSyntax.laws (15 : Fin 45) (16 : Fin 45) (17 : Fin 45) (18 : Fin
    45) (14 : Fin 45) (22 : Fin 45) (25 : Fin 45) (26 : Fin 45) (1 : Fin 45) (0 : Fin 45)) (.conj
    (ConstructionProbeGateCap.bounds (28 : Fin 45) (0 : Fin 45)) (.conj
    (ConstructionProbeIntervalsSyntax.uniformMargins (15 : Fin 45) (22 : Fin 45) (14 : Fin 45) (11 : Fin 45)
    (2 : Fin 45) (0 : Fin 45)) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (6 : Fin 49) (3 : Fin 49) (1 : Fin 49))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (6 : Fin 49) (2 : Fin 49) (0 : Fin 49))) (.imp (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides (18 : Fin 49) (15 : Fin 49) (3 : Fin 49) (2 : Fin 49))) (.imp (.neg
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (18 : Fin 49) (15 : Fin 49) (2 : Fin 49) (3 :
    Fin 49)))) (.existsE (.existsE (.conj (ConstructionRealCuts.cut (21 : Fin 51) (28 : Fin 51) (1 : Fin
    51)) (.conj (ConstructionProbeCostSupremum.cap (20 : Fin 51) (17 : Fin 51) (6 : Fin 51) (5 : Fin 51) (4
    : Fin 51) (1 : Fin 51)) (.conj (ConstructionCutAddition.sumCut (21 : Fin 51) (28 : Fin 51) (3 : Fin 51)
    (1 : Fin 51) (0 : Fin 51)) (.conj (.conj (Project.Formula.subset (.bound (0 : Fin 51)) (.bound (2 : Fin
    51))) (.neg (Project.Formula.subset (.bound (2 : Fin 51)) (.bound (0 : Fin 51)))))
    (ConstructionProbeIntervalsSyntax.missedBound (20 : Fin 51) (17 : Fin 51) (6 : Fin 51) (5 : Fin 51) (4 :
    Fin 51) (1 : Fin 51)))))))))))))))) (.conj (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 46) (15 : Fin 46) (24 : Fin 46))) (.imp
    (ConstructionProbeHeightFoldSyntax.laws (16 : Fin 46) (17 : Fin 46) (18 : Fin 46) (19 : Fin 46) (15 :
    Fin 46) (23 : Fin 46) (25 : Fin 46) (32 : Fin 46) (27 : Fin 46) (0 : Fin 46))
    (Project.Formula.extensionalEq (.bound (0 : Fin 46)) (.bound (3 : Fin 46)))))) (.conj (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 46) (15 : Fin 46) (24 : Fin 46))) (.imp
    (ConstructionProbeCostFoldSyntax.laws (16 : Fin 46) (17 : Fin 46) (18 : Fin 46) (19 : Fin 46) (15 : Fin
    46) (23 : Fin 46) (26 : Fin 46) (27 : Fin 46) (2 : Fin 46) (0 : Fin 46)) (Project.Formula.extensionalEq
    (.bound (0 : Fin 46)) (.bound (1 : Fin 46)))))) (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 49) (3 : Fin 49) (1 : Fin 49))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 49) (2 : Fin 49) (0 : Fin 49))) (.existsE
    (.existsE (.existsE (.conj (ConstructionProbeCostSupremum.family (23 : Fin 52) (26 : Fin 52) (32 : Fin
    52) (6 : Fin 52) (5 : Fin 52) (2 : Fin 52)) (.conj (ConstructionProbeCostSupremum.family (21 : Fin 52)
    (18 : Fin 52) (7 : Fin 52) (4 : Fin 52) (3 : Fin 52) (1 : Fin 52)) (.conj (ConstructionRealCuts.cut (22
    : Fin 52) (29 : Fin 52) (0 : Fin 52)) (.conj (ConstructionProbeCostSupremum.cap (23 : Fin 52) (26 : Fin
    52) (32 : Fin 52) (6 : Fin 52) (5 : Fin 52) (0 : Fin 52)) (.conj (ConstructionProbeCostSupremum.cap (21
    : Fin 52) (18 : Fin 52) (7 : Fin 52) (4 : Fin 52) (3 : Fin 52) (0 : Fin 52)) (.forallE (.forallE (.imp
    (ConstructionProbeCostSupremum.cap (25 : Fin 54) (28 : Fin 54) (34 : Fin 54) (8 : Fin 54) (7 : Fin 54)
    (1 : Fin 54)) (.imp (ConstructionProbeCostSupremum.cap (23 : Fin 54) (20 : Fin 54) (9 : Fin 54) (6 : Fin
    54) (5 : Fin 54) (0 : Fin 54)) (Project.Formula.extensionalEq (.bound (1 : Fin 54)) (.bound (0 : Fin
    54)))))))))))))))))))))))))))))))))) (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (13 : Fin 48) (2 : Fin 48) (1 : Fin 48))) (.conj (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge (5 : Fin 48) (1 : Fin 48) (0 : Fin 48))) (ProjectSyntax.encode id
    (Source.SetLanguage.edge (27 : Fin 48) (2 : Fin 48) (0 : Fin 48)))) (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge (3 : Fin 48) (1 : Fin 48) (0 : Fin 48))) (ProjectSyntax.encode id
    (Source.SetLanguage.edge (28 : Fin 48) (2 : Fin 48) (0 : Fin
    48)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
      ConstructionCutAddition.sumCut_freeClosed,ConstructionProbeIntervalsSyntax.missedBound_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.embeddingLaws_freeClosed,
      ConstructionPersistentProfiles.hasOldGates_freeClosed,
      ConstructionProbeCones.coneLaws_freeClosed,
      ConstructionProbePath.path_freeClosed,
      ConstructionProbePath.terminalTable_freeClosed,
      ConstructionProbeTarget.targetLaws_freeClosed,
      ConstructionProbeAlphabet.exitGraph_freeClosed,
      ConstructionProbeLetters.letters_freeClosed,
      ConstructionProbeLetters.projectionGraph_freeClosed,
      ConstructionProbeGeneratorSyntax.generatorGraph_freeClosed,
      ConstructionProbeIndexedGeneratorsSyntax.probeGraph_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
      ConstructionPersistentProfiles.probeProfile_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
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
    ConstructionProbeIntervalsSyntax.missedBound_semantics hM,ConstructionBaseMonoid.divides_semantics (M := M),
    ConstructionProbeLetters.representatives_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.embeddingLaws_semantics hM,
    ConstructionPersistentProfiles.hasOldGates_semantics hM,
    ConstructionProbeCones.coneLaws_semantics hM,
    ConstructionProbePath.path_semantics hM,
    ConstructionProbePath.terminalTable_semantics hM,
    ConstructionProbeTarget.targetLaws_semantics hM,
    ConstructionProbeAlphabet.exitGraph_semantics hM,
    ConstructionProbeLetters.letters_semantics hM,
    ConstructionProbeLetters.projectionGraph_semantics hM,
    ConstructionProbeGeneratorSyntax.generatorGraph_semantics hM,
    ConstructionProbeIndexedGeneratorsSyntax.probeGraph_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    ConstructionPersistentProfiles.probeProfile_semantics hM,
    ForcingSupportSize.small_semantics (M := M)]
  exact ConstructionProbeSuccessor.exists_probe_successor hM



theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeSuccessorSyntax
