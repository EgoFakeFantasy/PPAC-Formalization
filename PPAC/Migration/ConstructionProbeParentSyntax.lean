/- Pure nativeZF sentence for original ProbeData: all alphabet/letter/floor/
interval data and the SAME weighted successor/inclusion/probe are constructed
from the old weighted monoid, distinguished nonunit and actual request Path. -/
import PPAC.Migration.ConstructionProbeParent
import PPAC.Migration.ConstructionProbeSuccessor
import PPAC.Migration.ConstructionProbeHeightCostSyntax
import PPAC.Migration.ConstructionProbeMappedPathSyntax
import PPAC.Migration.ConstructionProbeNewOldMarginSyntax
import PPAC.Migration.ConstructionProbeOldCostSupremumSyntax

namespace PPAC.Migration.ConstructionProbeParentSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 16
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 16))) (.imp (Project.Formula.isEmpty (.bound (2 : Fin
    16))) (.imp (.mem (.bound (2 : Fin 16)) (.bound (0 : Fin 16))) (.imp (ConstructionFractionOrder.carrier
    (0 : Fin 16) (5 : Fin 16)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 16) (5 : Fin 16) (6 : Fin
    16)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 16) (12 : Fin 16) (11 : Fin 16) (11 : Fin
    16)) (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 16))) (.imp (ConstructionRealCuts.principal
    (0 : Fin 16) (5 : Fin 16) (12 : Fin 16) (10 : Fin 16)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 16) (3 : Fin 16) (9 : Fin 16))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 16) (3 : Fin 16) (9 : Fin 16))) (.imp
    (.mem (.bound (4 : Fin 16)) (.bound (1 : Fin 16))) (.imp (.neg (Project.Formula.extensionalEq (.bound (4
    : Fin 16)) (.bound (9 : Fin 16)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin
    16) (1 : Fin 16) (6 : Fin 16))) (.imp (ConstructionCutWeights.rangeBound (10 : Fin 16) (7 : Fin 16))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (8 : Fin 16) (1 : Fin 16) (6 : Fin 16))) (.imp
    (ConstructionProbeGateCap.bounds (10 : Fin 16) (8 : Fin 16)) (.imp
    (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 16) (5 : Fin 16) (1 : Fin 16) (3 : Fin 16) (7
    : Fin 16) (8 : Fin 16)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 16) (3 :
    Fin 16)) (.imp (.mem (.bound (14 : Fin 16)) (.bound (1 : Fin 16))) (.imp (.neg
    (Project.Formula.extensionalEq (.bound (14 : Fin 16)) (.bound (9 : Fin 16)))) (.imp
    (ConstructionProbePath.path (0 : Fin 16) (1 : Fin 16) (3 : Fin 16) (9 : Fin 16) (2 : Fin 16) (15 : Fin
    16) (13 : Fin 16)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (ConstructionProbeWord.wordCarrier (18 : Fin 34) (19 : Fin 34) (17 : Fin 34) (21 : Fin 34) (16 :
    Fin 34) (22 : Fin 34) (11 : Fin 34)) (.conj (ConstructionProbeRaw.old (20 : Fin 34) (19 : Fin 34) (27 :
    Fin 34) (10 : Fin 34)) (.conj (ConstructionProbeLetters.representatives (11 : Fin 34) (11 : Fin 34) (9 :
    Fin 34)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (8 : Fin 34) (9 : Fin 34) (11 : Fin
    34))) (.conj (ConstructionProbeWordMonoidSyntax.multiplicationGraph (18 : Fin 34) (19 : Fin 34) (17 :
    Fin 34) (20 : Fin 34) (21 : Fin 34) (16 : Fin 34) (22 : Fin 34) (11 : Fin 34) (15 : Fin 34) (8 : Fin
    34)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (11 : Fin 34) (8 : Fin 34)
    (10 : Fin 34))) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical (11 : Fin 34) (8 : Fin 34)
    (10 : Fin 34))) (.conj (ConstructionProbeSharedIntersections.conditionalJoins (11 : Fin 34) (8 : Fin
    34)) (.conj (ConstructionProbeOldEmbeddingSyntax.oldGraph (20 : Fin 34) (19 : Fin 34) (7 : Fin 34))
    (.conj (ConstructionProbeConservativeSyntax.conservative (19 : Fin 34) (11 : Fin 34) (21 : Fin 34) (8 :
    Fin 34) (7 : Fin 34)) (.conj (ConstructionProbeOldEmbeddingSyntax.embeddingLaws (18 : Fin 34) (19 : Fin
    34) (17 : Fin 34) (20 : Fin 34) (21 : Fin 34) (16 : Fin 34) (11 : Fin 34) (8 : Fin 34) (27 : Fin 34) (10
    : Fin 34) (7 : Fin 34)) (.conj (ConstructionPersistentProfiles.hasOldGates (19 : Fin 34) (11 : Fin 34)
    (21 : Fin 34) (8 : Fin 34) (7 : Fin 34)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (7 :
    Fin 34) (32 : Fin 34) (6 : Fin 34))) (.conj (.mem (.bound (6 : Fin 34)) (.bound (11 : Fin 34))) (.conj
    (.neg (Project.Formula.extensionalEq (.bound (6 : Fin 34)) (.bound (10 : Fin 34)))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 : Fin 34) (17 : Fin 34) (11 : Fin 34))) (.conj
    (ConstructionProbeGeneratorSyntax.generatorGraph (18 : Fin 34) (19 : Fin 34) (17 : Fin 34) (10 : Fin 34)
    (5 : Fin 34)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (4 : Fin 34) (18 : Fin 34) (11
    : Fin 34))) (.conj (ConstructionProbeIndexedGeneratorsSyntax.probeGraph (18 : Fin 34) (12 : Fin 34) (27
    : Fin 34) (5 : Fin 34) (4 : Fin 34)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (4 : Fin
    34) (20 : Fin 34) (3 : Fin 34))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (7 : Fin 34)
    (33 : Fin 34) (2 : Fin 34))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (7 : Fin 34) (22 :
    Fin 34) (1 : Fin 34))) (.conj (ConstructionProbeMappedPathSyntax.nodeMap (31 : Fin 34) (7 : Fin 34) (0 :
    Fin 34)) (.conj (ConstructionPersistentProfiles.probeProfile (18 : Fin 34) (11 : Fin 34) (8 : Fin 34) (2
    : Fin 34) (1 : Fin 34) (6 : Fin 34) (3 : Fin 34) (0 : Fin 34)) (.conj (.forallE (.neg
    (ProjectSyntax.encode id (Source.SetLanguage.edge (8 : Fin 35) (0 : Fin 35) (4 : Fin 35))))) (.conj
    (.forallE (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound (19 : Fin
    35)) (.bound (0 : Fin 35))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (20 : Fin 35) (0 :
    Fin 35))) (ProjectSyntax.encode id (ForcingSupportSize.small (12 : Fin 35) (0 : Fin 35)))))) (.conj
    (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionPersistentProfiles.probeProfile (23
    : Fin 39) (24 : Fin 39) (26 : Fin 39) (4 : Fin 39) (3 : Fin 39) (2 : Fin 39) (1 : Fin 39) (0 : Fin 39))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionProbeMappedPathSyntax.nodeMap (5 :
    Fin 44) (17 : Fin 44) (4 : Fin 44)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (17 : Fin
    44) (9 : Fin 44) (3 : Fin 44))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (17 : Fin 44)
    (8 : Fin 44) (2 : Fin 44))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (17 : Fin 44) (7 :
    Fin 44) (1 : Fin 44))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (17 : Fin 44) (6 : Fin
    44) (0 : Fin 44))) (ConstructionPersistentProfiles.probeProfile (28 : Fin 44) (21 : Fin 44) (18 : Fin
    44) (3 : Fin 44) (2 : Fin 44) (1 : Fin 44) (0 : Fin 44) (4 : Fin 44)))))))))))))))))) (.existsE
    (.existsE (.existsE (.conj (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (2 : Fin 37) (14 :
    Fin 37) (27 : Fin 37))) (.conj (ConstructionProbeHeightFoldSyntax.laws (21 : Fin 37) (22 : Fin 37) (20 :
    Fin 37) (23 : Fin 37) (14 : Fin 37) (26 : Fin 37) (28 : Fin 37) (17 : Fin 37) (16 : Fin 37) (2 : Fin
    37)) (.conj (ConstructionCutWeights.rangeBound (31 : Fin 37) (2 : Fin 37)) (.conj (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (1 : Fin 37) (14 : Fin 37) (27 : Fin 37))) (.conj
    (ConstructionProbeGateCap.graph (22 : Fin 37) (14 : Fin 37) (24 : Fin 37) (11 : Fin 37) (10 : Fin 37)
    (29 : Fin 37) (31 : Fin 37) (1 : Fin 37)) (.conj (ConstructionProbeGateCap.bounds (31 : Fin 37) (1 : Fin
    37)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 37) (14 : Fin 37) (27 : Fin
    37))) (.conj (ConstructionProbeCostFoldSyntax.laws (21 : Fin 37) (22 : Fin 37) (20 : Fin 37) (23 : Fin
    37) (14 : Fin 37) (26 : Fin 37) (29 : Fin 37) (16 : Fin 37) (1 : Fin 37) (0 : Fin 37)) (.conj
    (ConstructionProbeGateCap.bounds (31 : Fin 37) (0 : Fin 37)) (.conj
    (ConstructionProbeIntervalsSyntax.uniformMargins (21 : Fin 37) (26 : Fin 37) (14 : Fin 37) (11 : Fin 37)
    (2 : Fin 37) (0 : Fin 37)) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (6 : Fin 41) (3 : Fin 41) (1 : Fin 41))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (6 : Fin 41) (2 : Fin 41) (0 : Fin 41))) (.imp (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides (18 : Fin 41) (15 : Fin 41) (3 : Fin 41) (2 : Fin 41))) (.imp (.neg
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (18 : Fin 41) (15 : Fin 41) (2 : Fin 41) (3 :
    Fin 41)))) (.existsE (.existsE (.conj (ConstructionRealCuts.cut (27 : Fin 43) (32 : Fin 43) (1 : Fin
    43)) (.conj (ConstructionProbeCostSupremum.cap (20 : Fin 43) (17 : Fin 43) (6 : Fin 43) (5 : Fin 43) (4
    : Fin 43) (1 : Fin 43)) (.conj (ConstructionCutAddition.sumCut (27 : Fin 43) (32 : Fin 43) (3 : Fin 43)
    (1 : Fin 43) (0 : Fin 43)) (.conj (.conj (Project.Formula.subset (.bound (0 : Fin 43)) (.bound (2 : Fin
    43))) (.neg (Project.Formula.subset (.bound (2 : Fin 43)) (.bound (0 : Fin 43)))))
    (ConstructionProbeIntervalsSyntax.missedBound (20 : Fin 43) (17 : Fin 43) (6 : Fin 43) (5 : Fin 43) (4 :
    Fin 43) (1 : Fin 43)))))))))))))))) (.conj (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 38) (15 : Fin 38) (28 : Fin 38))) (.imp
    (ConstructionProbeHeightFoldSyntax.laws (22 : Fin 38) (23 : Fin 38) (21 : Fin 38) (24 : Fin 38) (15 :
    Fin 38) (27 : Fin 38) (29 : Fin 38) (18 : Fin 38) (17 : Fin 38) (0 : Fin 38))
    (Project.Formula.extensionalEq (.bound (0 : Fin 38)) (.bound (3 : Fin 38)))))) (.conj (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 38) (15 : Fin 38) (28 : Fin 38))) (.imp
    (ConstructionProbeCostFoldSyntax.laws (22 : Fin 38) (23 : Fin 38) (21 : Fin 38) (24 : Fin 38) (15 : Fin
    38) (27 : Fin 38) (30 : Fin 38) (17 : Fin 38) (2 : Fin 38) (0 : Fin 38)) (Project.Formula.extensionalEq
    (.bound (0 : Fin 38)) (.bound (1 : Fin 38)))))) (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 41) (3 : Fin 41) (1 : Fin 41))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 41) (2 : Fin 41) (0 : Fin 41))) (.existsE
    (.existsE (.existsE (.conj (ConstructionProbeCostSupremum.family (29 : Fin 44) (31 : Fin 44) (36 : Fin
    44) (6 : Fin 44) (5 : Fin 44) (2 : Fin 44)) (.conj (ConstructionProbeCostSupremum.family (21 : Fin 44)
    (18 : Fin 44) (7 : Fin 44) (4 : Fin 44) (3 : Fin 44) (1 : Fin 44)) (.conj (ConstructionRealCuts.cut (28
    : Fin 44) (33 : Fin 44) (0 : Fin 44)) (.conj (ConstructionProbeCostSupremum.cap (29 : Fin 44) (31 : Fin
    44) (36 : Fin 44) (6 : Fin 44) (5 : Fin 44) (0 : Fin 44)) (.conj (ConstructionProbeCostSupremum.cap (21
    : Fin 44) (18 : Fin 44) (7 : Fin 44) (4 : Fin 44) (3 : Fin 44) (0 : Fin 44)) (.forallE (.forallE (.imp
    (ConstructionProbeCostSupremum.cap (31 : Fin 46) (33 : Fin 46) (38 : Fin 46) (8 : Fin 46) (7 : Fin 46)
    (1 : Fin 46)) (.imp (ConstructionProbeCostSupremum.cap (23 : Fin 46) (20 : Fin 46) (9 : Fin 46) (6 : Fin
    46) (5 : Fin 46) (0 : Fin 46)) (Project.Formula.extensionalEq (.bound (1 : Fin 46)) (.bound (0 : Fin
    46)))))))))))))))))))))))))))))))))) (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (13 : Fin 40) (2 : Fin 40) (1 : Fin 40))) (.conj (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge (5 : Fin 40) (1 : Fin 40) (0 : Fin 40))) (ProjectSyntax.encode id
    (Source.SetLanguage.edge (31 : Fin 40) (2 : Fin 40) (0 : Fin 40)))) (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge (3 : Fin 40) (1 : Fin 40) (0 : Fin 40))) (ProjectSyntax.encode id
    (Source.SetLanguage.edge (32 : Fin 40) (2 : Fin 40) (0 : Fin
    40)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionFractionOrder.coordinates_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,ConstructionProbeRaw.old_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,
      ConstructionProbeGateCap.bounds_freeClosed,
      
      ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeHeightFoldSyntax.laws_freeClosed,ConstructionProbeGateCap.graph_freeClosed,
      ConstructionProbeCostFoldSyntax.laws_freeClosed,ConstructionProbeCostSupremum.family_freeClosed,
      ConstructionProbeCostSupremum.cap_freeClosed,ConstructionRealCuts.cut_freeClosed,
      ConstructionCutAddition.sumCut_freeClosed,ConstructionProbeIntervalsSyntax.missedBound_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.embeddingLaws_freeClosed,
      ConstructionPersistentProfiles.hasOldGates_freeClosed,
      
      ConstructionProbePath.path_freeClosed,
      
      
      
      
      
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
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionProbeWord.wordCarrier_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,ConstructionProbeRaw.old_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    ConstructionCutWeights.rangeBound_semantics hM,ConstructionProbeGateCap.bounds_semantics hM,
    
    ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,
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
    
    ConstructionProbePath.path_semantics hM,
    
    
    
    
    
    ConstructionProbeGeneratorSyntax.generatorGraph_semantics hM,
    ConstructionProbeIndexedGeneratorsSyntax.probeGraph_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    ConstructionPersistentProfiles.probeProfile_semantics hM,
    ForcingSupportSize.small_semantics (M := M)]
  exact ConstructionProbeParent.exists_probe hM




theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeParentSyntax
