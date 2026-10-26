/- Native source cost_le_gate's least-old-profile bound and cost_old_factor.
Consumes the already proved actual old embedding and old-gate records. -/
import PPAC.Migration.ConstructionProbeOldCostFactors
import PPAC.Migration.ConstructionProbeCostFoldSyntax

namespace PPAC.Migration.ConstructionProbeOldCostFactorsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 19
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 19))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin 19)))
(.imp (.mem (.bound (3 : Fin 19)) (.bound (0 : Fin 19))) (.imp (ConstructionProbeWord.wordCarrier (0 : Fin 19)
(1 : Fin 19) (2 : Fin 19) (4 : Fin 19) (5 : Fin 19) (6 : Fin 19) (7 : Fin 19)) (.imp (ProjectSyntax.encode id
(ForcingDiagramPoset.leftCancelMonoid (1 : Fin 19) (4 : Fin 19) (15 : Fin 19))) (.imp (ProjectSyntax.encode id
(ForcingDiagramPoset.conical (1 : Fin 19) (4 : Fin 19) (15 : Fin 19))) (.imp (ProjectSyntax.encode id
(Source.SetLanguage.mapsTo (10 : Fin 19) (1 : Fin 19) (7 : Fin 19))) (.imp
(ConstructionProbeOldEmbeddingSyntax.oldGraph (3 : Fin 19) (1 : Fin 19) (10 : Fin 19)) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 19) (1 : Fin 19) (9 : Fin 19))) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 19) (7 : Fin 19) (9 : Fin 19))) (.imp
(ConstructionProbeGateCap.graph (1 : Fin 19) (7 : Fin 19) (4 : Fin 19) (16 : Fin 19) (10 : Fin 19) (11 : Fin 19)
(18 : Fin 19) (13 : Fin 19)) (.imp (ConstructionProbeCostFoldSyntax.laws (0 : Fin 19) (1 : Fin 19) (2 : Fin 19)
(3 : Fin 19) (7 : Fin 19) (8 : Fin 19) (11 : Fin 19) (12 : Fin 19) (13 : Fin 19) (14 : Fin 19)) (.imp
(ConstructionProbeOldEmbeddingSyntax.embeddingLaws (0 : Fin 19) (1 : Fin 19) (2 : Fin 19) (3 : Fin 19) (4 : Fin
19) (5 : Fin 19) (7 : Fin 19) (16 : Fin 19) (15 : Fin 19) (17 : Fin 19) (10 : Fin 19)) (.imp
(ConstructionPersistentProfiles.hasOldGates (1 : Fin 19) (7 : Fin 19) (4 : Fin 19) (16 : Fin 19) (10 : Fin 19))
(.conj (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin 23)) (.bound (11 : Fin 23))) (.imp
(ConstructionProbeGateCap.oldMinimum (5 : Fin 23) (11 : Fin 23) (8 : Fin 23) (20 : Fin 23) (14 : Fin 23) (3 :
Fin 23) (2 : Fin 23)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (15 : Fin 23) (2 : Fin 23) (0 :
Fin 23))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (18 : Fin 23) (3 : Fin 23) (1 : Fin 23)))
(Project.Formula.subset (.bound (1 : Fin 23)) (.bound (0 : Fin 23))))))))))) (.forallE (.forallE (.forallE
(.forallE (.imp (.mem (.bound (3 : Fin 23)) (.bound (11 : Fin 23))) (.imp (ProjectSyntax.encode id
(Source.SetLanguage.edge (14 : Fin 23) (2 : Fin 23) (1 : Fin 23))) (.imp (ProjectSyntax.encode id
(ConstructionBaseMonoid.divides (11 : Fin 23) (20 : Fin 23) (3 : Fin 23) (1 : Fin 23))) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.edge (18 : Fin 23) (3 : Fin 23) (0 : Fin 23))) (.existsE (.existsE
(.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (17 : Fin 26) (2 : Fin 26) (1 : Fin 26)))
(.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (18 : Fin 26) (2 : Fin 26) (0 : Fin 26))) (.conj
(ConstructionProbeGateCap.oldMinimum (8 : Fin 26) (14 : Fin 26) (11 : Fin 26) (23 : Fin 26) (17 : Fin 26) (6 :
Fin 26) (2 : Fin 26)) (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (14 : Fin 26) (23 : Fin
26) (6 : Fin 26) (1 : Fin 26))) (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (8 : Fin 26) (11
: Fin 26) (2 : Fin 26) (5 : Fin 26))) (Project.Formula.subset (.bound (3 : Fin 26)) (.bound (0 : Fin
26))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,
      ConstructionProbeGateCap.graph_freeClosed,ConstructionProbeGateCap.oldMinimum_freeClosed,
      ConstructionProbeCostFoldSyntax.laws_freeClosed,ConstructionProbeOldEmbeddingSyntax.embeddingLaws_freeClosed,
      ConstructionPersistentProfiles.hasOldGates_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionProbeWord.wordCarrier_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics,ForcingDiagramPoset.conical_semantics,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    ConstructionProbeGateCap.graph_semantics hM,ConstructionProbeCostFoldSyntax.laws_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.embeddingLaws_semantics hM,ConstructionPersistentProfiles.hasOldGates_semantics hM,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,KuratowskiZF.source_edge,
    ConstructionProbeGateCap.oldMinimum_semantics hM,ConstructionBaseMonoid.divides_semantics (M := M),
    Project.Formula.satisfies_subset_iff]
  intro hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hL hEmbed hGates
  have hDiv := ConstructionProbeOldCostFactors.reflection_of_embedding hEmbed
  exact ⟨fun _ _ _ _ hq hmin hcg hqc =>
    ConstructionProbeOldCostFactors.cost_le_minimum hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hL hDiv hq hmin hcg hqc,
    fun _ _ _ _ hq hy hqy hqc =>
    ConstructionProbeOldCostFactors.cost_old_factor hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hL hDiv hGates hq hy hqy hqc⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeOldCostFactorsSyntax
