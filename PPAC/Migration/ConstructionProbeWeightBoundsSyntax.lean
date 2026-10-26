/- Actual bounded source weight graphs and cost_le_scale; not full HeightCost. -/
import PPAC.Migration.ConstructionProbeWeightBounds

namespace PPAC.Migration.ConstructionProbeWeightBoundsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 25
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 25))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin 25)))
(.imp (.mem (.bound (3 : Fin 25)) (.bound (0 : Fin 25))) (.imp (ConstructionFractionOrder.carrier (0 : Fin 25)
(8 : Fin 25)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 25) (8 : Fin 25) (9 : Fin 25)) (.imp
(ConstructionFractionOrder.coordinates (0 : Fin 25) (22 : Fin 25) (21 : Fin 25) (21 : Fin 25)) (.imp
(Project.Formula.isOrdinalOne (.bound (21 : Fin 25))) (.imp (ConstructionRealCuts.principal (0 : Fin 25) (8 :
Fin 25) (22 : Fin 25) (23 : Fin 25)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 :
Fin 25) (4 : Fin 25) (19 : Fin 25))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 25) (4
: Fin 25) (19 : Fin 25))) (.imp (ConstructionProbeWord.wordCarrier (0 : Fin 25) (1 : Fin 25) (2 : Fin 25) (4 :
Fin 25) (5 : Fin 25) (6 : Fin 25) (7 : Fin 25)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 :
Fin 25) (1 : Fin 25) (7 : Fin 25))) (.imp (ConstructionProbeOldEmbeddingSyntax.oldGraph (3 : Fin 25) (1 : Fin
25) (10 : Fin 25)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 25) (1 : Fin 25) (9 : Fin
25))) (.imp (ConstructionCutWeights.rangeBound (23 : Fin 25) (11 : Fin 25)) (.imp (ProjectSyntax.encode id
(Source.SetLanguage.mapsTo (12 : Fin 25) (1 : Fin 25) (9 : Fin 25))) (.imp (ConstructionProbeGateCap.bounds (23
: Fin 25) (12 : Fin 25)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 25) (2 : Fin 25) (9
: Fin 25))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 : Fin 25) (2 : Fin 25) (9 : Fin 25)))
(.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (15 : Fin 25) (2 : Fin 25) (9 : Fin 25))) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (16 : Fin 25) (2 : Fin 25) (9 : Fin 25))) (.imp
(ConstructionProbeHeightIntervalsSyntax.laws (0 : Fin 25) (8 : Fin 25) (24 : Fin 25) (1 : Fin 25) (4 : Fin 25)
(2 : Fin 25) (5 : Fin 25) (17 : Fin 25) (18 : Fin 25) (11 : Fin 25) (12 : Fin 25) (16 : Fin 25) (13 : Fin 25)
(14 : Fin 25) (15 : Fin 25)) (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id
(Source.SetLanguage.mapsTo (2 : Fin 28) (10 : Fin 28) (12 : Fin 28))) (.conj
(ConstructionProbeHeightFoldSyntax.laws (3 : Fin 28) (4 : Fin 28) (5 : Fin 28) (6 : Fin 28) (10 : Fin 28) (11 :
Fin 28) (14 : Fin 28) (16 : Fin 28) (17 : Fin 28) (2 : Fin 28)) (.conj (ConstructionCutWeights.rangeBound (26 :
Fin 28) (2 : Fin 28)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 28) (10 : Fin 28) (12
: Fin 28))) (.conj (ConstructionProbeGateCap.graph (4 : Fin 28) (10 : Fin 28) (7 : Fin 28) (23 : Fin 28) (13 :
Fin 28) (15 : Fin 28) (26 : Fin 28) (1 : Fin 28)) (.conj (ConstructionProbeGateCap.bounds (26 : Fin 28) (1 : Fin
28)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 28) (10 : Fin 28) (12 : Fin 28)))
(.conj (ConstructionProbeCostFoldSyntax.laws (3 : Fin 28) (4 : Fin 28) (5 : Fin 28) (6 : Fin 28) (10 : Fin 28)
(11 : Fin 28) (15 : Fin 28) (17 : Fin 28) (1 : Fin 28) (0 : Fin 28)) (.conj (ConstructionProbeGateCap.bounds (26
: Fin 28) (0 : Fin 28)) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
(ConstructionProbeRaw.cons (8 : Fin 33) (9 : Fin 33) (10 : Fin 33) (4 : Fin 33) (3 : Fin 33) (2 : Fin 33)) (.imp
(.mem (.bound (2 : Fin 33)) (.bound (15 : Fin 33))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (5 :
Fin 33) (2 : Fin 33) (1 : Fin 33))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (22 : Fin 33) (4 :
Fin 33) (0 : Fin 33))) (Project.Formula.subset (.bound (1 : Fin 33)) (.bound (0 : Fin 33)))))))))))) (.conj
(.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 29) (11 : Fin 29) (13 : Fin 29)))
(.imp (ConstructionProbeHeightFoldSyntax.laws (4 : Fin 29) (5 : Fin 29) (6 : Fin 29) (7 : Fin 29) (11 : Fin 29)
(12 : Fin 29) (15 : Fin 29) (17 : Fin 29) (18 : Fin 29) (0 : Fin 29)) (Project.Formula.extensionalEq (.bound (0
: Fin 29)) (.bound (3 : Fin 29)))))) (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 :
Fin 29) (11 : Fin 29) (13 : Fin 29))) (.imp (ConstructionProbeCostFoldSyntax.laws (4 : Fin 29) (5 : Fin 29) (6 :
Fin 29) (7 : Fin 29) (11 : Fin 29) (12 : Fin 29) (16 : Fin 29) (18 : Fin 29) (2 : Fin 29) (0 : Fin 29))
(Project.Formula.extensionalEq (.bound (0 : Fin 29)) (.bound (1 : Fin
29))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinalOne,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,
      ConstructionCutWeights.rangeBound_freeClosed,ConstructionProbeGateCap.bounds_freeClosed,
      ConstructionProbeHeightIntervalsSyntax.laws_freeClosed,ConstructionProbeHeightFoldSyntax.laws_freeClosed,
      ConstructionProbeGateCap.graph_freeClosed,ConstructionProbeCostFoldSyntax.laws_freeClosed,ConstructionProbeRaw.cons_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Term.eval_bound,ConstructionRealCuts.principal_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics,ForcingDiagramPoset.conical_semantics,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeWord.wordCarrier_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,ConstructionCutWeights.rangeBound_semantics hM,
    ConstructionProbeGateCap.bounds_semantics hM,ConstructionProbeHeightIntervalsSyntax.laws_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionProbeHeightFoldSyntax.laws_semantics hM,ConstructionProbeGateCap.graph_semantics hM,
    ConstructionProbeCostFoldSyntax.laws_semantics hM,Project.Formula.satisfies_forall_iff,
    ConstructionProbeRaw.cons_semantics hM,KuratowskiZF.source_edge,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact ConstructionProbeWeightBounds.exists_bounded_weights hM

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeWeightBoundsSyntax
