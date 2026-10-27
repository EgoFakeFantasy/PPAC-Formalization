/- Pinned MonoidBase.MergerData.extension/inclusion/cardinal_le.
Pure forall15 original-kernel certificate constructs SAME 41 actual outputs,
complete weighted successor/inclusion, all old profiles/roots, marked nonunit,
and cardinal bound for EVERY internal infinite mu as a conditional OUTPUT.
Consumes accepted copies/Word producers; no extra well-orderability premise,
new Object/Hom framework, scalar backend, Choice, parser, Sat or proof kernel.
Placement/Hull/final saturated monoid and final internal Con remain open. -/
import PPAC.Migration.ConstructionMergerParent
import PPAC.Migration.ConstructionMergerCoordinateSyntax
import PPAC.Migration.ConstructionCutArithmeticSyntax
import PPAC.Migration.ConstructionWordArithmeticSyntax

namespace PPAC.Migration.ConstructionMergerParentSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 15
    (.imp (ConstructionFractionOrder.carrier (0 : Fin 15) (7 : Fin 15)) (.imp (.mem (.bound 1)     (.bound
    0)) (.imp (.existsE (.mem (.bound 0) (.bound 2))) (.imp (ConstructionFractionOrder.coordinates (0 :
    Fin 15) (13 : Fin 15) (12 : Fin 15) (12 : Fin 15)) (.imp (Project.Formula.isOrdinalOne (.bound 12))
    (.imp (ConstructionRealCuts.principal (0 : Fin 15) (7 : Fin 15) (13 : Fin 15) (11 : Fin 15)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 15) (7 : Fin 15) (8 : Fin 15)) (.imp (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (9 :     Fin 15) (2 : Fin 15) (8 : Fin 15))) (.imp
    (ConstructionCutWeights.rangeBound (11 : Fin 15) (9 :     Fin 15)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (10 : Fin 15) (2 : Fin 15) (8     : Fin 15))) (.imp
    (ConstructionProbeGateCap.bounds (11 : Fin 15) (10 : Fin 15)) (.imp
    (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 15) (7 : Fin 15) (2 : Fin 15) (3 : Fin 15)
    (9 : Fin 15) (10 : Fin 15)) (.imp (Project.Formula.isOmega (.bound (0 : Fin 15))) (.imp
    (Project.Formula.isEmpty (.bound (6 : Fin 15))) (.imp (.mem (.bound (6 : Fin 15)) (.bound (0 :
    Fin 15))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 15) (3 :
    Fin 15) (4 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (2 : Fin 15)
    (3 : Fin 15) (4 : Fin 15))) (.imp (ConstructionProbeSharedIntersections.conditionalJoins (2 :     Fin
    15) (3 : Fin 15)) (.imp (ConstructionMergerRelations.prescription (1 : Fin 15) (2 : Fin 15)     (5 :
    Fin 15)) (.imp (ConstructionMergerRelations.valid (1 : Fin 15) (2 : Fin 15) (3 : Fin 15) (5     : Fin
    15)) (.imp (.mem (.bound (14 : Fin 15)) (.bound (2 : Fin 15))) (.imp (.neg
    (Project.Formula.extensionalEq (.bound (14 : Fin 15)) (.bound (4 : Fin 15)))) (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE     (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.conj
    (ConstructionProbeLetters.representatives (17 : Fin 31) (18 : Fin 31) (15 : Fin 31)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 31) (15 : Fin 31) (14 : Fin 31)))
    (.conj (ConstructionMergerCopies.copies (17 : Fin 31) (18 : Fin 31) (19 : Fin 31) (21 : Fin 31)
    (15 : Fin 31) (14 : Fin 31)) (.conj (ConstructionMergerCopies.projectionGraph (17 : Fin 31) (18     :
    Fin 31) (19 : Fin 31) (21 : Fin 31) (15 : Fin 31) (13 : Fin 31)) (.conj
    (ConstructionMergerCopies.equalityLaw (17 : Fin 31) (18 : Fin 31) (19 : Fin 31) (21 : Fin 31)     (13
    : Fin 31)) (.conj (ConstructionProbeLetters.representatives (14 : Fin 31) (18 : Fin 31) (12     : Fin
    31)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 31) (12 : Fin 31) (14 : Fin
    31))) (.conj (ConstructionMergerAction.actionTable (18 : Fin 31) (19 : Fin 31) (13     : Fin 31) (11
    : Fin 31)) (.conj (ConstructionMergerAction.rightFreeAction (19 : Fin 31) (20 :     Fin 31) (14 : Fin
    31) (11 : Fin 31)) (.conj (ConstructionMergerAction.copyLaw (18 : Fin 31) (19     : Fin 31) (13 : Fin
    31) (11 : Fin 31)) (.conj (ConstructionProbeRaw.carrier (16 : Fin 31) (18 :     Fin 31) (14 : Fin 31)
    (10 : Fin 31)) (.conj (ConstructionProbeLetters.representatives (10 : Fin 31) (18 : Fin 31) (9 : Fin
    31)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (8 :     Fin 31) (9 : Fin 31) (10 :
    Fin 31))) (.conj (ConstructionMergerWordAction.actionTable (16 : Fin 31) (18 : Fin 31) (14 : Fin 31)
    (22 : Fin 31) (19 : Fin 31) (11 : Fin 31) (8 : Fin 31)) (.conj
    (ConstructionMergerAction.rightFreeAction (19 : Fin 31) (20 : Fin 31) (10 : Fin 31) (8 : Fin 31))
    (.conj (ConstructionProbeLetters.representatives (10 : Fin 31) (10 : Fin 31) (7 : Fin 31))     (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 31) (7 : Fin 31) (10 : Fin 31)))
    (ConstructionMergerWordProduct.laws (16 : Fin 31) (18 : Fin 31) (14 : Fin 31) (22 : Fin 31) (8 : Fin
    31) (6 : Fin 31))))))))))))))))))) (.conj (ConstructionProbeRaw.old (22 : Fin 31)     (18 : Fin 31)
    (20 : Fin 31) (5 : Fin 31)) (.conj (ProjectSyntax.encode id     (ForcingDiagramPoset.leftCancelMonoid
    (10 : Fin 31) (6 : Fin 31) (5 : Fin 31))) (.conj     (ProjectSyntax.encode id
    (ForcingDiagramPoset.conical (10 : Fin 31) (6 : Fin 31) (5 : Fin 31)))     (.conj
    (ConstructionMergerCopyCones.hasConeJoins (18 : Fin 31) (14 : Fin 31) (11 : Fin 31))     (.conj
    (ConstructionProbeSharedIntersections.conditionalJoins (10 : Fin 31) (6 : Fin 31)) (.conj
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (22 : Fin 31) (18 : Fin 31) (4 : Fin 31)) (.conj
    (ConstructionProbeConservativeSyntax.conservative (18 : Fin 31) (10 : Fin 31) (19 : Fin 31) (6 :
    Fin 31) (4 : Fin 31)) (.conj (ConstructionProbeLiftHomSyntax.preservesProducts (19 : Fin 31) (6     :
    Fin 31) (4 : Fin 31)) (.conj (ConstructionPersistentProfiles.hasOldGates (18 : Fin 31) (10 :     Fin
    31) (19 : Fin 31) (6 : Fin 31) (4 : Fin 31)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge (4 : Fin 31) (20 : Fin 31) (5 : Fin 31))) (.conj (.forallE (.forallE
    (.forallE (.forallE (.forallE (.imp (ConstructionPersistentProfiles.probeProfile (21 : Fin 36)
    (23 : Fin 36) (24 : Fin 36) (4 : Fin 36) (3 : Fin 36) (2 : Fin 36) (1 : Fin 36) (0 : Fin 36))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap (5 : Fin 41) (14 : Fin 41) (4 : Fin 41)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 41) (9 : Fin 41) (3 : Fin 41)))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 41) (8 : Fin 41) (2 : Fin 41)))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 41) (7 : Fin 41) (1 :     Fin
    41))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 41) (6 : Fin 41) (0     :
    Fin 41))) (ConstructionPersistentProfiles.probeProfile (26 : Fin 41) (20 : Fin 41) (16 : Fin 41) (3 :
    Fin 41) (2 : Fin 41) (1 : Fin 41) (0 : Fin 41) (4 : Fin 41)))))))))))))))))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (3 : Fin 31) (17 : Fin 31) (10 : Fin 31)))
    (.conj (ConstructionMergerRoots.rootGraph (16 : Fin 31) (18 : Fin 31) (14 : Fin 31) (20 : Fin 31) (13
    : Fin 31) (5 : Fin 31) (3 : Fin 31)) (.conj (ConstructionMergerRoots.rootLaws (16 : Fin 31) (18 : Fin
    31) (14 : Fin 31) (17 : Fin 31) (19 : Fin 31) (21 : Fin 31) (13 : Fin 31) (5 : Fin 31) (6 : Fin 31)
    (4 : Fin 31) (3 : Fin 31)) (.conj (ConstructionProbeLetters.representatives (17     : Fin 31) (14 :
    Fin 31) (2 : Fin 31)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo     (1 : Fin 31) (2
    : Fin 31) (24 : Fin 31))) (.conj (ProjectSyntax.encode id     (Source.SetLanguage.mapsTo (0 : Fin 31)
    (2 : Fin 31) (24 : Fin 31))) (.conj     (ConstructionMergerCoordinates.graph (17 : Fin 31) (14 : Fin
    31) (13 : Fin 31) (25 : Fin 31) (22     : Fin 31) (1 : Fin 31)) (.conj
    (ConstructionMergerCoordinates.graph (17 : Fin 31) (14 : Fin 31)     (13 : Fin 31) (26 : Fin 31) (27
    : Fin 31) (0 : Fin 31)) (.conj     (ConstructionMergerCoordinateLaws.laws (17 : Fin 31) (18 : Fin 31)
    (14 : Fin 31) (11 : Fin 31)     (13 : Fin 31) (25 : Fin 31) (26 : Fin 31) (22 : Fin 31) (27 : Fin 31)
    (1 : Fin 31) (0 : Fin 31))     (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE     (.existsE (.conj (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (35
    : Fin 41) (30 :     Fin 41) (9 : Fin 41))) (.conj (ConstructionProbeLetters.representatives (34 : Fin
    41) (34 : Fin 41) (8 : Fin 41)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin
    41) (8 :     Fin 41) (34 : Fin 41))) (.conj (ConstructionCutArithmeticSyntax.graph (26 : Fin 41) (33
    : Fin 41) (34 : Fin 41) (7 : Fin 41)) (.conj (ConstructionProbeLetters.representatives (34 : Fin 41)
    (34 : Fin 41) (6 : Fin 41)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 : Fin 41)
    (6 : Fin 41) (34 : Fin 41))) (.conj (ConstructionWordArithmeticSyntax.graph (26 : Fin 41)     (33 :
    Fin 41) (34 : Fin 41) (5 : Fin 41)) (.conj (ProjectSyntax.encode id     (Source.SetLanguage.mapsTo (4
    : Fin 41) (34 : Fin 41) (34 : Fin 41))) (.conj     (ProjectSyntax.encode id
    (ForcingConditionGraphs.identityGraph (34 : Fin 41) (4 : Fin 41)))     (.conj
    (Project.Formula.isSuccessor (.bound 3) (.bound 38)) (.conj (.mem (.bound 3) (.bound 26))     (.conj
    (.mem (.bound 2) (.bound 34)) (.conj (ConstructionCutDivision.value (26 : Fin 41) (33 :     Fin 41)
    (3 : Fin 41) (9 : Fin 41) (2 : Fin 41)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (1 : Fin 41) (24 : Fin 41) (34 : Fin 41))) (.conj (.forallE (.forallE
    (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (3 : Fin 43) (1 : Fin 43) (0 : Fin 43)))
    (.conj (.mem (.bound 1) (.bound 26)) (ConstructionMergerFiniteWeights.heightValue (28 : Fin 43)
    (35 : Fin 43) (29 : Fin 43) (36 : Fin 43) (9 : Fin 43) (6 : Fin 43) (34 : Fin 43) (13 : Fin 43)
    (1 : Fin 43) (0 : Fin 43)))))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 :
    Fin 41) (24 : Fin 41) (34 : Fin 41))) (.conj (.forallE (.forallE (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge (2 : Fin 43) (1 : Fin 43) (0 : Fin 43))) (.conj (.mem (.bound 1)     (.bound
    26)) (ConstructionMergerFiniteWeights.costValue (28 : Fin 43) (35 : Fin 43) (29 : Fin 43) (36 : Fin
    43) (7 : Fin 43) (6 : Fin 43) (39 : Fin 43) (4 : Fin 43) (12 : Fin 43) (1 : Fin 43) (0 : Fin 43))))))
    (.conj (.forallE (.imp (.mem (.bound 0) (.bound 35)) (ProjectSyntax.encode     id
    (ForcingDiagramOrder.product (6 : Fin 42) (0 : Fin 42) (38 : Fin 42) (0 : Fin 42)))))     (.forallE
    (.imp (.mem (.bound 0) (.bound 35)) (ProjectSyntax.encode id     (ForcingDiagramOrder.product (8 :
    Fin 42) (33 : Fin 42) (0 : Fin 42) (0 : Fin 42))))))))))))))))))))))) (.conj
    (ConstructionMergerHeightCost.copiesHeightCost (26 : Fin 41) (33 : Fin 41) (34 : Fin 41) (28 : Fin
    41) (24 : Fin 41) (21 : Fin 41) (37 : Fin 41) (1 : Fin 41) (0 : Fin 41)) (.conj (.forallE (.imp
    (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound (27 : Fin 42)) (.bound
    (0 : Fin 42))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (29 : Fin 42) (0 : Fin 42)))
    (ProjectSyntax.encode id (ForcingSupportSize.small (21 : Fin 42) (0 : Fin 42)))))) (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.conj (.conj (.conj (.conj (ConstructionBaseWeights.digits (40 : Fin
    55) (52 : Fin 55) (13 : Fin 55) (12 : Fin 55)) (.conj (Project.Formula.isSuccessor (.bound (11 : Fin
    55)) (.bound (12 : Fin 55))) (.conj (.mem (.bound (11 : Fin 55)) (.bound (40 : Fin 55))) (.conj
    (Project.Formula.isSuccessor (.bound (10 : Fin 55)) (.bound (11 : Fin 55))) (.conj
    (Project.Formula.isSuccessor (.bound (9 : Fin 55)) (.bound (10 : Fin 55))) (.conj
    (Project.Formula.isSuccessor (.bound (8 : Fin 55)) (.bound (9 : Fin 55))) (.conj
    (Project.Formula.isSuccessor (.bound (7 : Fin 55)) (.bound (8 : Fin 55))) (.conj (.mem (.bound (7 :
    Fin 55)) (.bound (40 : Fin 55))) (.conj (ConstructionCutDivision.value (40 : Fin 55) (47 : Fin 55)
    (11 : Fin 55) (51 : Fin 55) (6 : Fin 55)) (.conj (ConstructionCutDivision.value (40 : Fin 55) (47 :
    Fin 55) (7 : Fin 55) (51 : Fin 55) (5 : Fin 55)) (.conj (.mem (.bound (6 : Fin 55)) (.bound (48 : Fin
    55))) (.conj (.mem (.bound (5 : Fin 55)) (.bound (48 : Fin 55))) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (4 : Fin 55) (38 : Fin 55) (48 : Fin 55))) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (3 : Fin 55) (38 : Fin 55) (48 : Fin 55))) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (2 : Fin 55) (38 : Fin 55) (48 : Fin 55))) (.conj
    (ConstructionMergerWordParameters.graph 0 (40 : Fin 55) (47 : Fin 55) (11 : Fin 55) (51 : Fin 55) (6
    : Fin 55) (5 : Fin 55) (38 : Fin 55) (15 : Fin 55) (14 : Fin 55) (4 : Fin 55)) (.conj
    (ConstructionMergerWordParameters.graph 1 (40 : Fin 55) (47 : Fin 55) (11 : Fin 55) (51 : Fin 55) (6
    : Fin 55) (5 : Fin 55) (38 : Fin 55) (15 : Fin 55) (14 : Fin 55) (3 : Fin 55)) (.conj
    (ConstructionMergerWordParameters.graph 2 (40 : Fin 55) (47 : Fin 55) (11 : Fin 55) (51 : Fin 55) (6
    : Fin 55) (5 : Fin 55) (38 : Fin 55) (15 : Fin 55) (14 : Fin 55) (2 : Fin 55)) (.conj (.forallE
    (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (8 : Fin 59) (3
    : Fin 59) (2 : Fin 59))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (7 : Fin 59) (3 :
    Fin 59) (1 : Fin 59))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (6 : Fin 59) (3 : Fin
    59) (0 : Fin 59))) (ConstructionMergerWordParameters.recipe (44 : Fin 59) (51 : Fin 59) (15 : Fin 59)
    (55 : Fin 59) (10 : Fin 59) (9 : Fin 59) (19 : Fin 59) (18 : Fin 59) (3 : Fin 59) (2 : Fin 59) (1 :
    Fin 59) (0 : Fin 59))))))))) (.conj (ConstructionCutWeights.rangeBound (51 : Fin 55) (4 : Fin 55))
    (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 57) (1 :
    Fin 57) (0 : Fin 57))) (.existsE (.mem (.bound (0 : Fin 58)) (.bound (1 : Fin 58)))))))
    (ConstructionProbeGateCap.bounds (5 : Fin 55) (2 : Fin 55))))))))))))))))))))))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 55) (34 : Fin 55) (48 : Fin 55))) (.conj
    (ConstructionProbeHeightFoldSyntax.laws (40 : Fin 55) (42 : Fin 55) (38 : Fin 55) (46 : Fin 55) (34 :
    Fin 55) (47 : Fin 55) (49 : Fin 55) (4 : Fin 55) (3 : Fin 55) (1 : Fin 55)) (.conj
    (ConstructionMergerWordHeights.literalLaws (40 : Fin 55) (47 : Fin 55) (42 : Fin 55) (38 : Fin 55)
    (46 : Fin 55) (51 : Fin 55) (49 : Fin 55) (4 : Fin 55) (1 : Fin 55)) (.conj
    (ConstructionCutWeights.rangeBound (51 : Fin 55) (1 : Fin 55)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 55) (34 : Fin 55) (48 : Fin 55))) (.conj (.forallE (.forallE
    (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (2 : Fin 57) (1 : Fin 57) (0 : Fin 57)))
    (.conj (.mem (.bound (1 : Fin 57)) (.bound (36 : Fin 57))) (ConstructionMergerWordCosts.value (42 :
    Fin 57) (49 : Fin 57) (44 : Fin 57) (40 : Fin 57) (48 : Fin 57) (53 : Fin 57) (3 : Fin 57) (52 : Fin
    57) (4 : Fin 57) (1 : Fin 57) (0 : Fin 57)))))) (.conj (ConstructionProbeGateCap.bounds (51 : Fin 55)
    (0 : Fin 55)) (.conj (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.old (49 : Fin 58) (45
    : Fin 58) (2 : Fin 58) (1 : Fin 58)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (3 : Fin
    58) (1 : Fin 58) (0 : Fin 58))) (ProjectSyntax.encode id (Source.SetLanguage.edge (53 : Fin 58) (2 :
    Fin 58) (0 : Fin 58)))))))) (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.cons
    (44 : Fin 59) (46 : Fin 59) (42 : Fin 59) (3 : Fin 59) (2 : Fin 59) (1 : Fin 59)) (.iff
    (ProjectSyntax.encode id (Source.SetLanguage.edge (4 : Fin 59) (1 : Fin 59) (0 : Fin 59))) (.existsE
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (8 : Fin 62) (5 : Fin
    62) (2 : Fin 62))) (.conj (ConstructionCutDifference.value (47 : Fin 62) (54 : Fin 62) (2 : Fin 62)
    (58 : Fin 62) (1 : Fin 62)) (.conj (ConstructionCutAddition.sumCut (47 : Fin 62) (54 : Fin 62) (2 :
    Fin 62) (1 : Fin 62) (58 : Fin 62)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (9 : Fin
    62) (6 : Fin 62) (0 : Fin 62))) (ConstructionCutProduct.value (47 : Fin 62) (54 : Fin 62) (1 : Fin
    62) (0 : Fin 62) (3 : Fin 62)))))))))))))))))))))))) (.conj
    (ConstructionProbeIntervalsSyntax.uniformMargins (40 : Fin 55) (47 : Fin 55) (34 : Fin 55) (30 : Fin
    55) (1 : Fin 55) (0 : Fin 55)) (.conj (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 59) (3 : Fin 59) (1 : Fin 59))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 59) (2 : Fin 59) (0 : Fin 59))) (.imp
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (38 : Fin 59) (34 : Fin 59) (3 : Fin 59) (2
    : Fin 59))) (.imp (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (38 : Fin 59) (34 :
    Fin 59) (2 : Fin 59) (3 : Fin 59)))) (.existsE (.existsE (.conj (ConstructionRealCuts.cut (46 : Fin
    61) (53 : Fin 61) (1 : Fin 61)) (.conj (ConstructionProbeCostSupremum.cap (40 : Fin 61) (36 : Fin 61)
    (6 : Fin 61) (5 : Fin 61) (4 : Fin 61) (1 : Fin 61)) (.conj (ConstructionCutAddition.sumCut (46 : Fin
    61) (53 : Fin 61) (3 : Fin 61) (1 : Fin 61) (0 : Fin 61)) (.conj (.conj (Project.Formula.subset
    (.bound (0 : Fin 61)) (.bound (2 : Fin 61))) (.neg (Project.Formula.subset (.bound (2 : Fin 61))
    (.bound (0 : Fin 61))))) (ConstructionProbeIntervalsSyntax.missedBound (40 : Fin 61) (36 : Fin 61) (6
    : Fin 61) (5 : Fin 61) (4 : Fin 61) (1 : Fin 61)))))))))))))))) (.forallE (.forallE (.forallE
    (.forallE (.imp (ConstructionProbeRaw.old (50 : Fin 59) (46 : Fin 59) (3 : Fin 59) (1 : Fin 59))
    (.imp (ConstructionProbeRaw.old (50 : Fin 59) (46 : Fin 59) (2 : Fin 59) (0 : Fin 59)) (.conj
    (.forallE (.iff (ConstructionProbeCostSupremum.costMember (39 : Fin 60) (35 : Fin 60) (5 : Fin 60) (2
    : Fin 60) (1 : Fin 60) (0 : Fin 60)) (ConstructionProbeCostSupremum.costMember (47 : Fin 60) (48 :
    Fin 60) (55 : Fin 60) (4 : Fin 60) (3 : Fin 60) (0 : Fin 60)))) (.conj (.forallE (.iff
    (ConstructionProbeCostSupremum.cap (39 : Fin 60) (35 : Fin 60) (5 : Fin 60) (2 : Fin 60) (1 : Fin 60)
    (0 : Fin 60)) (ConstructionProbeCostSupremum.cap (47 : Fin 60) (48 : Fin 60) (55 : Fin 60) (4 : Fin
    60) (3 : Fin 60) (0 : Fin 60)))) (.existsE (.conj (ConstructionRealCuts.cut (45 : Fin 60) (52 : Fin
    60) (0 : Fin 60)) (.conj (ConstructionProbeCostSupremum.cap (47 : Fin 60) (48 : Fin 60) (55 : Fin 60)
    (4 : Fin 60) (3 : Fin 60) (0 : Fin 60)) (.conj (ConstructionProbeCostSupremum.cap (39 : Fin 60) (35 :
    Fin 60) (5 : Fin 60) (2 : Fin 60) (1 : Fin 60) (0 : Fin 60)) (.forallE (.forallE (.imp
    (ConstructionProbeCostSupremum.cap (49 : Fin 62) (50 : Fin 62) (57 : Fin 62) (6 : Fin 62) (5 : Fin
    62) (1 : Fin 62)) (.imp (ConstructionProbeCostSupremum.cap (41 : Fin 62) (37 : Fin 62) (7 : Fin 62)
    (4 : Fin 62) (3 : Fin 62) (0 : Fin 62)) (Project.Formula.extensionalEq (.bound (1 : Fin 62)) (.bound
    (0 : Fin 62)))))))))))))))))))))) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
    (29 : Fin 56) (55 : Fin 56) (0 : Fin 56))) (.conj (.mem (.bound (0 : Fin 56)) (.bound (35 : Fin 56)))
    (.conj (.neg (Project.Formula.extensionalEq (.bound (0 : Fin 56)) (.bound (30 : Fin 56)))) (.conj
    (ConstructionProbeRaw.old (47 : Fin 56) (43 : Fin 56) (55 : Fin 56) (0 : Fin 56)) (.forallE (.forallE
    (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (32 : Fin 59) (2 : Fin 59) (1 : Fin
    59))) (.conj (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 59) (1 : Fin 59) (0 :
    Fin 59))) (ProjectSyntax.encode id (Source.SetLanguage.edge (53 : Fin 59) (2 : Fin 59) (0 : Fin
    59)))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (4 : Fin 59) (1 : Fin 59) (0 : Fin
    59))) (ProjectSyntax.encode id (Source.SetLanguage.edge (54 : Fin 59) (2 : Fin 59) (0 : Fin 59)))))))
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      ConstructionMergerRelations.prescription_freeClosed,
      ConstructionMergerRelations.valid_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,
      ConstructionMergerCopies.copies_freeClosed,
      ConstructionMergerCopies.projectionGraph_freeClosed,
      ConstructionMergerCopies.equalityLaw_freeClosed,
      ConstructionMergerAction.actionTable_freeClosed,
      ConstructionMergerAction.rightFreeAction_freeClosed,
      ConstructionMergerAction.copyLaw_freeClosed,
      ConstructionProbeRaw.carrier_freeClosed,
      ConstructionMergerWordAction.actionTable_freeClosed,
      ConstructionMergerWordProduct.laws_freeClosed,
      ConstructionProbeRaw.old_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionMergerCopyCones.hasConeJoins_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,
      ConstructionPersistentProfiles.hasOldGates_freeClosed,
      ConstructionPersistentProfiles.probeProfile_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
      ConstructionMergerRoots.rootGraph_freeClosed,
      ConstructionMergerRoots.rootLaws_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionCutWeights.rangeBound_freeClosed,
      ConstructionProbeGateCap.bounds_freeClosed,
      ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,
      ConstructionMergerCoordinates.graph_freeClosed,
      ConstructionMergerCoordinateLaws.laws_freeClosed,
      Project.Formula.isOrdinalOne,
      Project.Formula.isSuccessor,
      ConstructionFractionOrder.carrier_freeClosed,
      ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.principal_freeClosed,
      ConstructionCutArithmeticSyntax.graph_freeClosed,
      ConstructionWordArithmeticSyntax.graph_freeClosed,
      ConstructionCutDivision.value_freeClosed,
      ConstructionMergerFiniteWeights.heightValue_freeClosed,
      ConstructionMergerFiniteWeights.costValue_freeClosed,
      ConstructionMergerHeightCost.copiesHeightCost_freeClosed,
      ConstructionProbeRaw.cons_freeClosed,
      ConstructionBaseWeights.digits_freeClosed,
      ConstructionCutDifference.value_freeClosed,
      ConstructionCutAddition.sumCut_freeClosed,
      ConstructionCutProduct.value_freeClosed,
      ConstructionMergerWordParameters.graph_freeClosed,
      ConstructionMergerWordParameters.recipe_freeClosed,
      ConstructionMergerWordHeights.literalLaws_freeClosed,
      ConstructionMergerWordCosts.value_freeClosed,
      ConstructionProbeHeightFoldSyntax.laws_freeClosed,
      ConstructionProbeCostSupremum.cap_freeClosed,
      ConstructionProbeCostSupremum.costMember_freeClosed,
      ConstructionProbeIntervalsSyntax.missedBound_freeClosed,
      ConstructionRealCuts.cut_freeClosed,
      Project.Formula.extensionalEq]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeRaw.old_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbeLetters.representatives_semantics hM,
    ConstructionMergerRelations.prescription_semantics hM,
    ConstructionMergerRelations.valid_semantics hM,
    ConstructionMergerCopies.copies_semantics hM,
    ConstructionMergerCopies.projectionGraph_semantics hM,
    ConstructionMergerCopies.equalityLaw_semantics hM,
    ConstructionMergerAction.actionTable_semantics hM,
    ConstructionMergerAction.rightFreeAction_semantics hM,
    ConstructionMergerAction.copyLaw_semantics hM,
    ConstructionProbeRaw.carrier_semantics hM,
    ConstructionMergerWordAction.actionTable_semantics hM,
    ConstructionMergerWordProduct.laws_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionMergerCopyCones.hasConeJoins_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,
    ConstructionPersistentProfiles.hasOldGates_semantics hM,
    ConstructionPersistentProfiles.probeProfile_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    KuratowskiZF.source_edge,
    ConstructionMergerRoots.rootGraph_semantics hM,
    ConstructionMergerRoots.rootLaws_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionCutWeights.rangeBound_semantics hM,
    ConstructionProbeGateCap.bounds_semantics hM,
    ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,
    ConstructionMergerCoordinates.graph_semantics hM,
    ConstructionMergerCoordinateLaws.laws_semantics hM,
    Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Formula.satisfies_isSuccessor_iff,
    ConstructionFractionOrder.carrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,
    ConstructionRealCuts.principal_semantics hM,
    ConstructionCutArithmeticSyntax.graph_semantics hM,
    ConstructionWordArithmeticSyntax.graph_semantics hM,
    ConstructionCutDivision.value_semantics hM,
    ForcingConditionGraphs.identityGraph_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),
    ConstructionMergerFiniteWeights.heightValue_semantics hM,
    ConstructionMergerFiniteWeights.costValue_semantics hM,
    ConstructionMergerHeightCost.copiesHeightCost_semantics hM,
    Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionProbeRaw.cons_semantics hM,
    ConstructionBaseWeights.digits_semantics,
    ConstructionCutDifference.value_semantics hM,
    ConstructionCutAddition.sumCut_semantics hM,
    ConstructionCutProduct.value_semantics hM,
    ConstructionMergerWordParameters.graph_semantics hM,
    ConstructionMergerWordParameters.recipe_semantics hM,
    ConstructionMergerWordHeights.literalLaws_semantics hM,
    ConstructionMergerWordCosts.value_semantics hM,
    ConstructionProbeHeightFoldSyntax.laws_semantics hM,
    ConstructionProbeCostSupremum.cap_semantics hM,
    ConstructionProbeCostSupremum.costMember_semantics hM,
    ConstructionProbeIntervalsSyntax.missedBound_semantics hM,
    ConstructionRealCuts.cut_semantics hM,
    ConstructionBaseMonoid.divides_semantics (M := M),
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M)]
  intro hQ hn hnp hu hone hunit hR hHeight hHB hCost hCB hUniform hw hz hzw hm hc hJoins hP hValid hmark hmarkNe
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,hRootLaws,J,CH,CC,hJ,hCH,hCC,hCoordH,hCoordC,hCoordLaws,
    unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,hWeights,hHeightCost,hCard,hWord⟩ :=
    ConstructionMergerParent.exists_system hM hw hz hzw hm hc hJoins hP hValid hQ hn hnp hu hone hunit hR hHeight hHB hCost hCB hUniform hmark hmarkNe
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,O,F,J,CH,CC,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,hO,hCons,hPres,hGates,hEdge,hProfiles,hF,hRoots,hRootLaws,hJ,hCH,hCC,hCoordH,hCoordC,hCoordLaws,
    unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,hWeights,hHeightCost,hCard,hWord⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerParentSyntax
