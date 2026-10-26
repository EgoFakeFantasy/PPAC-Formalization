/- Pure-member original-kernel certificate for the source literal Gate cost,
outside-block old factor and old-old strict margin. Existing producers discharge
ExitGates, HasOldGates, EmbeddingLaws and the actual Word monoid in this proof. -/
import PPAC.Migration.ConstructionProbeCostMargins
import PPAC.Migration.ConstructionProbeCostFoldSyntax
import PPAC.Migration.ConstructionProbeHeightFoldSyntax
import PPAC.Migration.ConstructionProbeIntervalsSyntax
import PPAC.Migration.ConstructionProbeGatesSyntax

namespace PPAC.Migration.ConstructionProbeCostMarginsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Inputs in order: w D S zero mul A b W Q R Emb H C V Cap LC e G
unitW unit E I Off HL. All source gates/factors/margins range internally. -/
def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 24
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 24))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin 24)))
    (.imp (.mem (.bound (3 : Fin 24)) (.bound (0 : Fin 24))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 24) (4 : Fin 24) (16 : Fin 24))) (.imp (ProjectSyntax.encode
    id (ForcingDiagramPoset.conical (1 : Fin 24) (4 : Fin 24) (16 : Fin 24))) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 24) (4 : Fin 24) (16 : Fin 24) (2 : Fin 24) (21 : Fin 24) (5 :
    Fin 24) (20 : Fin 24)) (.imp (.mem (.bound (6 : Fin 24)) (.bound (1 : Fin 24))) (.imp
    (ConstructionProbeWord.wordCarrier (0 : Fin 24) (1 : Fin 24) (2 : Fin 24) (4 : Fin 24) (5 : Fin 24) (6 : Fin
    24) (7 : Fin 24)) (.imp (ConstructionProbeWordMonoidSyntax.multiplicationGraph (0 : Fin 24) (1 : Fin 24) (2
    : Fin 24) (3 : Fin 24) (4 : Fin 24) (5 : Fin 24) (6 : Fin 24) (7 : Fin 24) (20 : Fin 24) (17 : Fin 24))
    (.imp (ConstructionProbeRaw.old (3 : Fin 24) (1 : Fin 24) (16 : Fin 24) (18 : Fin 24)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 24) (1 : Fin 24) (7 : Fin 24))) (.imp
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (3 : Fin 24) (1 : Fin 24) (10 : Fin 24)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 24) (1 : Fin 24) (9 : Fin 24))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 : Fin 24) (7 : Fin 24) (9 : Fin 24))) (.imp
    (ConstructionProbeGateCap.graph (1 : Fin 24) (7 : Fin 24) (4 : Fin 24) (17 : Fin 24) (10 : Fin 24) (12 : Fin
    24) (19 : Fin 24) (14 : Fin 24)) (.imp (ConstructionProbeCostFoldSyntax.laws (0 : Fin 24) (1 : Fin 24) (2 :
    Fin 24) (3 : Fin 24) (7 : Fin 24) (8 : Fin 24) (12 : Fin 24) (13 : Fin 24) (14 : Fin 24) (15 : Fin 24))
    (.imp (ConstructionProbeHeightFoldSyntax.laws (0 : Fin 24) (1 : Fin 24) (2 : Fin 24) (3 : Fin 24) (7 : Fin
    24) (8 : Fin 24) (11 : Fin 24) (22 : Fin 24) (13 : Fin 24) (23 : Fin 24)) (.imp
    (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 24) (8 : Fin 24) (1 : Fin 24) (4 : Fin 24) (11 :
    Fin 24) (12 : Fin 24)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 24) (4 : Fin
    24)) (.imp (ConstructionProbeConservativeSyntax.conservative (1 : Fin 24) (7 : Fin 24) (4 : Fin 24) (17 :
    Fin 24) (10 : Fin 24)) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (4 : Fin
    29)) (.bound (12 : Fin 29))) (.imp (.mem (.bound (2 : Fin 29)) (.bound (6 : Fin 29))) (.imp
    (ConstructionProbeGatesSyntax.headSome (5 : Fin 29) (6 : Fin 29) (7 : Fin 29) (4 : Fin 29) (3 : Fin 29))
    (.imp (ConstructionProbeGatesSyntax.gate (5 : Fin 29) (6 : Fin 29) (7 : Fin 29) (8 : Fin 29) (9 : Fin 29)
    (10 : Fin 29) (12 : Fin 29) (22 : Fin 29) (4 : Fin 29) (3 : Fin 29) (2 : Fin 29)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (17 : Fin 29) (2 : Fin 29) (0 : Fin 29))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (20 : Fin 29) (4 : Fin 29) (1 : Fin 29)))
    (Project.Formula.subset (.bound (1 : Fin 29)) (.bound (0 : Fin 29)))))))))))))) (.conj (.forallE (.forallE
    (.forallE (.forallE (.imp (.mem (.bound (3 : Fin 28)) (.bound (11 : Fin 28))) (.imp (.mem (.bound (2 : Fin
    28)) (.bound (11 : Fin 28))) (.imp (.neg (ConstructionProbeGatesSyntax.headSome (4 : Fin 28) (5 : Fin 28) (6
    : Fin 28) (3 : Fin 28) (1 : Fin 28))) (.imp (ConstructionProbeGatesSyntax.headSome (4 : Fin 28) (5 : Fin 28)
    (6 : Fin 28) (2 : Fin 28) (1 : Fin 28)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (11 :
    Fin 28) (21 : Fin 28) (3 : Fin 28) (2 : Fin 28))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    (19 : Fin 28) (3 : Fin 28) (0 : Fin 28))) (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge (17 : Fin 31) (2 : Fin 31) (1 : Fin 31))) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge (19 : Fin 31) (2 : Fin 31) (0 : Fin 31))) (.conj (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides (14 : Fin 31) (24 : Fin 31) (6 : Fin 31) (1 : Fin 31))) (.conj
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (14 : Fin 31) (24 : Fin 31) (1 : Fin 31) (5 : Fin
    31))) (Project.Formula.subset (.bound (3 : Fin 31)) (.bound (0 : Fin 31)))))))))))))))))))) (.forallE
    (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    (16 : Fin 30) (5 : Fin 30) (3 : Fin 30))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (16 : Fin
    30) (4 : Fin 30) (2 : Fin 30))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (29 : Fin 30) (3 :
    Fin 30) (1 : Fin 30))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (29 : Fin 30) (2 : Fin 30) (0
    : Fin 30))) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (7 : Fin 30) (10 : Fin 30) (5 :
    Fin 30) (4 : Fin 30))) (.imp (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (7 : Fin 30) (10
    : Fin 30) (4 : Fin 30) (5 : Fin 30)))) (ConstructionProbeIntervalsSyntax.uniformAt (6 : Fin 30) (14 : Fin
    30) (13 : Fin 30) (23 : Fin 30) (21 : Fin 30) (3 : Fin 30) (2 : Fin 30) (1 : Fin 30) (0 : Fin
    30))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeAlphabet.alphabet_freeClosed,ConstructionProbeWord.wordCarrier_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,ConstructionProbeRaw.old_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,ConstructionProbeGateCap.graph_freeClosed,
      ConstructionProbeCostFoldSyntax.laws_freeClosed,ConstructionProbeHeightFoldSyntax.laws_freeClosed,
      ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeGatesSyntax.headSome_freeClosed,ConstructionProbeGatesSyntax.gate_freeClosed,
      ConstructionProbeIntervalsSyntax.uniformAt_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeAlphabet.alphabet_semantics hM,ConstructionProbeWord.wordCarrier_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,ConstructionProbeRaw.old_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    ConstructionProbeGateCap.graph_semantics hM,ConstructionProbeCostFoldSyntax.laws_semantics hM,
    ConstructionProbeHeightFoldSyntax.laws_semantics hM,ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,
    ConstructionProbeGatesSyntax.headSome_semantics hM,ConstructionProbeGatesSyntax.gate_semantics hM,
    KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M := M),
    Project.Formula.satisfies_subset_iff,ConstructionProbeIntervalsSyntax.uniformAt_semantics hM]
  intro hw hz hzw hm hCon hAlpha hb hW hMult hUnit hEmb hOld hC hCap hCapG hCost hHeight hUniform hJoins hConservative
  have hEmbed := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hm hAlpha hW hb hUnit hMult hOld
  have hDiv := ConstructionProbeOldCostFactors.reflection_of_embedding hEmbed
  have hExit := ConstructionProbeConditionalJoins.gate_existence hM hw hz hzw hm hAlpha hW hb hMult hUnit hOld hJoins hConservative
  have hGates := ConstructionPersistentProfiles.probe_has_old_gates hM hw hz hzw hm hAlpha hW hb hMult hUnit hOld hJoins hConservative
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hMult
  refine ⟨?_,?_,?_⟩
  · intro q s g c cg hq hg _ hGate hcg hqc
    exact ConstructionProbeCostMargins.cost_le_gate hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hCost hDiv hq hg hGate hcg hqc
  · intro q z s c hq hzW hqHead hzHead hqz hqc
    exact ConstructionProbeCostMargins.cost_other_block_factor hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hCost hEmbed hExit hq hzW hqHead hzHead hqz hqc
  · intro x y ox oy hx hy hxo hyo hxh hyh hxy hNot
    exact ConstructionProbeCostMargins.uniform_margin_old hM hw hz hzw hW hm hmW hCon hEmb hOld hC hCap hCapG hCost hHeight hDiv hGates hUniform hxo hyo hxh hyh hxy hNot

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeCostMarginsSyntax
