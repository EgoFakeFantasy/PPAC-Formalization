/- Pure-member original-kernel certificate for source new-to-old strict margin.
The native proof constructs the literal max bound, including the zero old
remainder, and invokes existing generator/old-factor/Word producers. -/
import PPAC.Migration.ConstructionProbeNewOldMargin
import PPAC.Migration.ConstructionProbeOldNewMarginSyntax

namespace PPAC.Migration.ConstructionProbeNewOldMarginSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Same thirty actual data graphs as the old-new certificate. Only this
source theorem needs b!=e, matching ProbeMargins.uniform_margin_new_old. -/
def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 30
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 30))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin 30)))
    (.imp (.mem (.bound (3 : Fin 30)) (.bound (0 : Fin 30))) (.imp (ConstructionFractionOrder.carrier (0 : Fin
    30) (8 : Fin 30)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 30) (8 : Fin 30) (9 : Fin 30)) (.imp
    (ConstructionFractionOrder.coordinates (0 : Fin 30) (28 : Fin 30) (27 : Fin 30) (27 : Fin 30)) (.imp
    (Project.Formula.isOrdinalOne (.bound (27 : Fin 30))) (.imp (ConstructionRealCuts.principal (0 : Fin 30) (8
    : Fin 30) (28 : Fin 30) (19 : Fin 30)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid
    (1 : Fin 30) (4 : Fin 30) (16 : Fin 30))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 :
    Fin 30) (4 : Fin 30) (16 : Fin 30))) (.imp (ConstructionProbeAlphabet.alphabet (1 : Fin 30) (4 : Fin 30) (16
    : Fin 30) (2 : Fin 30) (21 : Fin 30) (5 : Fin 30) (20 : Fin 30)) (.imp (.mem (.bound (6 : Fin 30)) (.bound
    (1 : Fin 30))) (.imp (.neg (Project.Formula.extensionalEq (.bound (6 : Fin 30)) (.bound (16 : Fin 30))))
    (.imp (ConstructionProbeWord.wordCarrier (0 : Fin 30) (1 : Fin 30) (2 : Fin 30) (4 : Fin 30) (5 : Fin 30) (6
    : Fin 30) (7 : Fin 30)) (.imp (ConstructionProbeWordMonoidSyntax.multiplicationGraph (0 : Fin 30) (1 : Fin
    30) (2 : Fin 30) (3 : Fin 30) (4 : Fin 30) (5 : Fin 30) (6 : Fin 30) (7 : Fin 30) (20 : Fin 30) (17 : Fin
    30)) (.imp (ConstructionProbeRaw.old (3 : Fin 30) (1 : Fin 30) (16 : Fin 30) (18 : Fin 30)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 30) (1 : Fin 30) (7 : Fin 30))) (.imp
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (3 : Fin 30) (1 : Fin 30) (10 : Fin 30)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 30) (1 : Fin 30) (9 : Fin 30))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 30) (1 : Fin 30) (9 : Fin 30))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (25 : Fin 30) (2 : Fin 30) (9 : Fin 30))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (23 : Fin 30) (7 : Fin 30) (9 : Fin 30))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 : Fin 30) (7 : Fin 30) (9 : Fin 30))) (.imp
    (ConstructionCutWeights.rangeBound (19 : Fin 30) (23 : Fin 30)) (.imp
    (ConstructionProbeHeightIntervalsSyntax.laws (0 : Fin 30) (8 : Fin 30) (29 : Fin 30) (1 : Fin 30) (4 : Fin
    30) (2 : Fin 30) (5 : Fin 30) (26 : Fin 30) (20 : Fin 30) (11 : Fin 30) (12 : Fin 30) (24 : Fin 30) (22 :
    Fin 30) (13 : Fin 30) (25 : Fin 30)) (.imp (ConstructionProbeHeightFoldSyntax.laws (0 : Fin 30) (1 : Fin 30)
    (2 : Fin 30) (3 : Fin 30) (7 : Fin 30) (8 : Fin 30) (11 : Fin 30) (22 : Fin 30) (13 : Fin 30) (23 : Fin 30))
    (.imp (ConstructionProbeGateCap.graph (1 : Fin 30) (7 : Fin 30) (4 : Fin 30) (17 : Fin 30) (10 : Fin 30) (12
    : Fin 30) (19 : Fin 30) (14 : Fin 30)) (.imp (ConstructionProbeCostFoldSyntax.laws (0 : Fin 30) (1 : Fin 30)
    (2 : Fin 30) (3 : Fin 30) (7 : Fin 30) (8 : Fin 30) (12 : Fin 30) (13 : Fin 30) (14 : Fin 30) (15 : Fin 30))
    (.imp (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 30) (8 : Fin 30) (1 : Fin 30) (4 : Fin 30)
    (11 : Fin 30) (12 : Fin 30)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 30) (4 :
    Fin 30)) (.imp (ConstructionProbeConservativeSyntax.conservative (1 : Fin 30) (7 : Fin 30) (4 : Fin 30) (17
    : Fin 30) (10 : Fin 30)) (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (5
    : Fin 36)) (.bound (13 : Fin 36))) (.imp (ConstructionProbeGatesSyntax.headSome (6 : Fin 36) (7 : Fin 36) (8
    : Fin 36) (5 : Fin 36) (4 : Fin 36)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (16 : Fin 36)
    (3 : Fin 36) (2 : Fin 36))) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (13 : Fin 36) (23
    : Fin 36) (5 : Fin 36) (2 : Fin 36))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (29 : Fin 36)
    (5 : Fin 36) (1 : Fin 36))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (29 : Fin 36) (2 : Fin
    36) (0 : Fin 36))) (ConstructionProbeIntervalsSyntax.uniformAt (6 : Fin 36) (14 : Fin 36) (13 : Fin 36) (23
    : Fin 36) (21 : Fin 36) (5 : Fin 36) (2 : Fin 36) (1 : Fin 36) (0 : Fin
    36)))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionFractionOrder.coordinates_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionProbeAlphabet.alphabet_freeClosed,ConstructionProbeWord.wordCarrier_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,ConstructionProbeRaw.old_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,
      ConstructionProbeHeightIntervalsSyntax.laws_freeClosed,ConstructionProbeHeightFoldSyntax.laws_freeClosed,
      ConstructionProbeGateCap.graph_freeClosed,ConstructionProbeCostFoldSyntax.laws_freeClosed,
      ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeGatesSyntax.headSome_freeClosed,ConstructionProbeIntervalsSyntax.uniformAt_freeClosed]

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
    ConstructionCutWeights.rangeBound_semantics hM,
    ConstructionProbeHeightIntervalsSyntax.laws_semantics hM,ConstructionProbeHeightFoldSyntax.laws_semantics hM,
    ConstructionProbeGateCap.graph_semantics hM,ConstructionProbeCostFoldSyntax.laws_semantics hM,
    ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,Project.Formula.satisfies_forall_iff,
    ConstructionProbeGatesSyntax.headSome_semantics hM,KuratowskiZF.source_edge,
    ConstructionBaseMonoid.divides_semantics (M := M),ConstructionProbeIntervalsSyntax.uniformAt_semantics hM]
  intro hw hz hzw hQ hR hu hone hunit hm hCon hAlpha hb hne hW hMult hWordUnit hEmb hOld hH hC hB hHL hCap hHB hI hHeight hCapG hLC hUniform hJoins hConservative
  intro z s y oy hx hy hzW hHead hyo hzy hxh hyh
  exact ConstructionProbeNewOldMargin.uniform_margin_new_old hM hw hz hzw hQ hR hu hone hunit hm hCon hAlpha hb hne hW hMult hWordUnit hEmb hOld hH hC hB hHL hCap hHB hI hHeight hCapG hLC hUniform hJoins hConservative hzW hHead hyo hzy hxh hyh

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeNewOldMarginSyntax
