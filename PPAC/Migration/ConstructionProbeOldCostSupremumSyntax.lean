/- Pure nativeZF original-kernel certificate for source old_cost_supremum.
Constructs the actual old/new missed-cost families and their common unique
cut supremum, including empty families and unordered old endpoints. -/
import PPAC.Migration.ConstructionProbeOldCostSupremum
import PPAC.Migration.ConstructionProbeCostMarginsSyntax

namespace PPAC.Migration.ConstructionProbeOldCostSupremumSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Inputs: w D S zero mul A b W Q R Emb C V Cap LC e G unitW unit E I.
No height, comparison, supplied family, supplied supremum or b!=e is assumed. -/
def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 21
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 21))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin 21)))
    (.imp (.mem (.bound (3 : Fin 21)) (.bound (0 : Fin 21))) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 21)
    (8 : Fin 21) (9 : Fin 21)) (.imp (.mem (.bound (18 : Fin 21)) (.bound (9 : Fin 21))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 21) (4 : Fin 21) (15 : Fin 21)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 21) (4 : Fin 21) (15 : Fin 21))) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 21) (4 : Fin 21) (15 : Fin 21) (2 : Fin 21) (20 : Fin 21) (5 :
    Fin 21) (19 : Fin 21)) (.imp (.mem (.bound (6 : Fin 21)) (.bound (1 : Fin 21))) (.imp
    (ConstructionProbeWord.wordCarrier (0 : Fin 21) (1 : Fin 21) (2 : Fin 21) (4 : Fin 21) (5 : Fin 21) (6 : Fin
    21) (7 : Fin 21)) (.imp (ConstructionProbeWordMonoidSyntax.multiplicationGraph (0 : Fin 21) (1 : Fin 21) (2
    : Fin 21) (3 : Fin 21) (4 : Fin 21) (5 : Fin 21) (6 : Fin 21) (7 : Fin 21) (19 : Fin 21) (16 : Fin 21))
    (.imp (ConstructionProbeRaw.old (3 : Fin 21) (1 : Fin 21) (15 : Fin 21) (17 : Fin 21)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 21) (1 : Fin 21) (7 : Fin 21))) (.imp
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (3 : Fin 21) (1 : Fin 21) (10 : Fin 21)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 21) (1 : Fin 21) (9 : Fin 21))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 : Fin 21) (7 : Fin 21) (9 : Fin 21))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 21) (7 : Fin 21) (9 : Fin 21))) (.imp
    (ConstructionProbeGateCap.graph (1 : Fin 21) (7 : Fin 21) (4 : Fin 21) (16 : Fin 21) (10 : Fin 21) (11 : Fin
    21) (18 : Fin 21) (13 : Fin 21)) (.imp (ConstructionProbeCostFoldSyntax.laws (0 : Fin 21) (1 : Fin 21) (2 :
    Fin 21) (3 : Fin 21) (7 : Fin 21) (8 : Fin 21) (11 : Fin 21) (12 : Fin 21) (13 : Fin 21) (14 : Fin 21))
    (.imp (ConstructionProbeGateCap.bounds (18 : Fin 21) (11 : Fin 21)) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 21) (4 : Fin 21)) (.imp
    (ConstructionProbeConservativeSyntax.conservative (1 : Fin 21) (7 : Fin 21) (4 : Fin 21) (16 : Fin 21) (10 :
    Fin 21)) (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (14
    : Fin 25) (3 : Fin 25) (1 : Fin 25))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 25)
    (2 : Fin 25) (0 : Fin 25))) (.existsE (.existsE (.existsE (.conj (ConstructionProbeCostSupremum.family (8 :
    Fin 28) (11 : Fin 28) (18 : Fin 28) (6 : Fin 28) (5 : Fin 28) (2 : Fin 28)) (.conj
    (ConstructionProbeCostSupremum.family (14 : Fin 28) (23 : Fin 28) (21 : Fin 28) (4 : Fin 28) (3 : Fin 28) (1
    : Fin 28)) (.conj (ConstructionRealCuts.cut (7 : Fin 28) (15 : Fin 28) (0 : Fin 28)) (.conj
    (ConstructionProbeCostSupremum.cap (8 : Fin 28) (11 : Fin 28) (18 : Fin 28) (6 : Fin 28) (5 : Fin 28) (0 :
    Fin 28)) (.conj (ConstructionProbeCostSupremum.cap (14 : Fin 28) (23 : Fin 28) (21 : Fin 28) (4 : Fin 28) (3
    : Fin 28) (0 : Fin 28)) (.forallE (.forallE (.imp (ConstructionProbeCostSupremum.cap (10 : Fin 30) (13 : Fin
    30) (20 : Fin 30) (8 : Fin 30) (7 : Fin 30) (1 : Fin 30)) (.imp (ConstructionProbeCostSupremum.cap (16 : Fin
    30) (25 : Fin 30) (23 : Fin 30) (6 : Fin 30) (5 : Fin 30) (0 : Fin 30)) (Project.Formula.extensionalEq
    (.bound (1 : Fin 30)) (.bound (0 : Fin 30)))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.extensionalEq,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionProbeAlphabet.alphabet_freeClosed,ConstructionProbeWord.wordCarrier_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,ConstructionProbeRaw.old_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,ConstructionProbeGateCap.graph_freeClosed,
      ConstructionProbeCostFoldSyntax.laws_freeClosed,ConstructionProbeGateCap.bounds_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeCostSupremum.family_freeClosed,ConstructionProbeCostSupremum.cap_freeClosed,
      ConstructionRealCuts.cut_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionRealCuts.cutCarrier_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeAlphabet.alphabet_semantics hM,ConstructionProbeWord.wordCarrier_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,ConstructionProbeRaw.old_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    ConstructionProbeGateCap.graph_semantics hM,ConstructionProbeCostFoldSyntax.laws_semantics hM,
    ConstructionProbeGateCap.bounds_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,Project.Formula.satisfies_forall_iff,
    KuratowskiZF.source_edge,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionProbeCostSupremum.family_semantics hM,ConstructionProbeCostSupremum.cap_semantics hM,
    ConstructionRealCuts.cut_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  intro hw hz hzw hR hUnit hm hCon hAlpha hb hW hMult hWordUnit hEmb hOld hC hLC hCap hCapG hL hCB hJoins hConservative
  have hEmbed := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hm hAlpha hW hb hWordUnit hMult hOld
  have hDiv := ConstructionProbeOldCostFactors.reflection_of_embedding hEmbed
  have hGates := ConstructionPersistentProfiles.probe_has_old_gates hM hw hz hzw hm hAlpha hW hb hMult hWordUnit hOld hJoins hConservative
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hWordUnit hMult
  intro x y ox oy hxo hyo
  exact ConstructionProbeOldCostSupremum.exists_common_cap hM hw hz hzw hR hUnit hW hm hmW hCon hEmb hOld hC hLC hCap hCapG hL hCB hDiv hGates hxo hyo

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeOldCostSupremumSyntax
