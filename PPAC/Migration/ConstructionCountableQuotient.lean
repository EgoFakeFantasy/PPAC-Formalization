/- Complete pinned ConcreteQuotients.Chain.countable_quotient_of_cells:174-198.
Actual original cell tower -> ONE countable reordered base -> all stabilizer
alignments -> the full tail-coset quotient and an internal injection into omega.
Original ground Choice is supplied by the EXISTING internal L interpretation. -/
import PPAC.Migration.ConstructionGermCosets

namespace PPAC.Migration.ConstructionCountableQuotient
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionComponentCofinal (Chain)
open ForcingSupportSize (Small Injection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF
      labels q root vertices chain : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : ConstructionCellRestriction.Stages V GV e S)
    (hT : ConstructionFirstAppearance.Timeline hM V I R bottom S)
    (hIndex : ConstructionFirstAppearance.Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hData : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hGraph : ConstructionFlatStages.Graph history outerF kappa V zero traces I S)
    (hD : PureKuratowski.PairMember M bottom D S) (hDc : Small D w)
    (hX : ConstructionComponentCarrier.Carrier V labels GV q vertices)
    (hC : Chain w V labels GV q zero root vertices chain) (hq : Injection V labels q) :
    ∃ H Q pr, ConstructionGermCosets.Result w V labels GV q root chain H Q pr := by
  obtain ⟨base,_,hCount,hAligned⟩ := ConstructionCountableAlignments.construction hM hChoice
    hw hz hzw hv hc hJ hStages hT hIndex hCells hNew hData hGraph hD hDc hX hC hq
  exact ConstructionGermCosets.construction hM hw hzw hC hCount hAligned

def constructionSentence {m : Nat} (w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionCellRestriction.stages V GV e S) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV e I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV e I R S cells) (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R) (.imp (ConstructionFlatStages.graph history outerF kappa V zero traces I S) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S bottom D)) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small D w)) (.imp (ConstructionComponentCarrier.carrier V labels GV q vertices) (.imp (ConstructionComponentCofinal.chain w V labels GV q zero root vertices chain) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q V labels)) (.existsE (.existsE (.existsE (ConstructionGermCosets.resultFormula w.succ.succ.succ V.succ.succ.succ labels.succ.succ.succ GV.succ.succ.succ q.succ.succ.succ root.succ.succ.succ chain.succ.succ.succ 2 1 0))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionGermCosets.resultFormula_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionCellRestriction.stages_freeClosed,
      ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,
      ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,
      ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.graph_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed]

theorem construction_models {m : Nat} (w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ConstructionGermCosets.resultFormula_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionCellRestriction.stages_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,
    ConstructionFirstAppearance.indexGraph_semantics hM,ConstructionStepCellSelection.graph_semantics hM,
    ConstructionStepCellSelection.atNew_semantics hM,ConstructionBlockIndex.data_semantics hM,
    ConstructionFlatStages.graph_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,ConstructionComponentCofinal.chain_semantics hM]
  exact construction hM hChoice

theorem construction_kernel_certificate {m : Nat} (w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain)).mp (construction_models w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain hL hChoice)



end PPAC.Migration.ConstructionCountableQuotient
