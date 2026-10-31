/- Pinned CellReorder.countable_reordering:346-355.
Reuse the existing countable conservative dependency hull on s union the
original bottom, then the SAME actual reordered tower. Countability uses the
existing constructible ZFC ground; the final certificate is in nativeZF for
its L-relative sentence, not an extra Choice axiom in nativeZF. -/
import PPAC.Migration.ConstructionReordered

namespace PPAC.Migration.ConstructionCountableReordering
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionCellRestriction (Stages)
open ConstructionFirstAppearance (Timeline Index)
open ConstructionRealCuts (Subset)
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Result (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero V GV e I R bottom S s retained futures muls : M.Carrier .set) : Prop :=
  ConstructionReordered.Result hM w zero V GV e I R bottom zero S retained futures muls ∧
    Small retained w ∧ Subset s retained ∧ PureKuratowski.PairMember M bottom retained futures

/-- Original countable_reordering, with actual dependency graph and retained
carrier constructed here. The original bottom is included before taking hull. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w zero one V GV e I R bottom S index cells D s kappa traces Indices A r history outerF : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : Stages V GV e S) (hT : Timeline hM V I R bottom S)
    (hIndex : Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hData : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hGraph : ConstructionFlatStages.Graph history outerF kappa V zero traces I S)
    (hD : PureKuratowski.PairMember M bottom D S) (hDc : Small D w)
    (hs : Subset s V) (hsc : Small s w) :
    ∃ retained futures muls, Result hM w zero V GV e I R bottom S s retained futures muls := by
  let P := KuratowskiZF.interpretation hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨seed,hSeed⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) s D
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF P w
  have hwc : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal P w w :=
    ⟨ExistingCardinalBounds.omega_cardinal_l P hZF hw,id,hId.1⟩
  have hSeedSmall := ExistingCardinalBounds.infinite_union_two_l P hZF hw hwc
    ((ForcingSupportSize.native_small hM s w).mp hsc)
    ((ForcingSupportSize.native_small hM D w).mp hDc) hSeed
  have hSeedV : Subset seed V := by
    intro x hx
    rcases (hSeed x).mp hx with hx | hx
    · exact hs x hx
    · exact (hStages bottom D hD).1 x hx
  obtain ⟨deps,hGlobal,hDeps⟩ := ConstructionGlobalDependencies.assembly hM hT hIndex hCells hNew
  obtain ⟨retained,B,G,inc,hCount,hSub,hRet,_,_,_,_,_,_,_,_,_,hClosed⟩ :=
    ConstructionCountableConservativeHull.exists_countable_conservative hM hChoice hw hv hc hJ
      hDeps hSeedV ((ForcingSupportSize.native_small hM seed w).mpr hSeedSmall)
  obtain ⟨futures,muls,hResult⟩ := ConstructionReordered.actual hM hw hz hzw hv hc hJ hStages
    hRet hT hIndex hCells hNew hGlobal hClosed hData hGraph
  refine ⟨retained,futures,muls,hResult,hCount,?_,?_⟩
  · exact fun x hx => hSub x ((hSeed x).mpr (Or.inl hx))
  · exact hResult.2.2.2.2.2.2 D hD (fun x hx => hSub x ((hSeed x).mpr (Or.inr hx)))

def resultFormula {m : Nat} (w zero V GV e I R bottom S s retained futures muls : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionReordered.resultFormula w zero V GV e I R bottom zero S retained futures muls) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small retained w)) (.conj (Project.Formula.subset (.bound s) (.bound retained)) (ProjectSyntax.encode id (Source.SetLanguage.edge futures bottom retained)))))

theorem resultFormula_freeClosed {m : Nat} (w zero V GV e I R bottom S s retained futures muls : Fin m) :
    (resultFormula w zero V GV e I R bottom S s retained futures muls).FreeClosed := by
  simp -implicitDefEqProofs [resultFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.subset,ConstructionReordered.resultFormula_freeClosed]

theorem resultFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero V GV e I R bottom S s retained futures muls : Fin m) :
    Project.Formula.satisfies env (resultFormula w zero V GV e I R bottom S s retained futures muls) ↔ Result hM (env.bound w) (env.bound zero) (env.bound V) (env.bound GV) (env.bound e) (env.bound I) (env.bound R) (env.bound bottom) (env.bound S) (env.bound s) (env.bound retained) (env.bound futures) (env.bound muls) := by
  simp only [resultFormula,Result,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    ConstructionReordered.resultFormula_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.small_semantics (M := M)]
  rfl

/-- The pinned countable_reordering sentence; source ground Choice is
provided only by the already established constructible interpretation. -/
def constructionSentence {m : Nat} (w zero one V GV e I R bottom S index cells D s kappa traces Indices A r history outerF : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionCellRestriction.stages V GV e S) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV e I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV e I R S cells) (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R) (.imp (ConstructionFlatStages.graph history outerF kappa V zero traces I S) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S bottom D)) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small D w)) (.imp (Project.Formula.subset (.bound s) (.bound V)) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small s w)) (.existsE (.existsE (.existsE (resultFormula w.succ.succ.succ zero.succ.succ.succ V.succ.succ.succ GV.succ.succ.succ e.succ.succ.succ I.succ.succ.succ R.succ.succ.succ bottom.succ.succ.succ S.succ.succ.succ s.succ.succ.succ 2 1 0)))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.subset,resultFormula_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionCellRestriction.stages_freeClosed,
      ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,
      ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,
      ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.graph_freeClosed]

theorem construction_models {m : Nat} (w zero one V GV e I R bottom S index cells D s kappa traces Indices A r history outerF : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w zero one V GV e I R bottom S index cells D s kappa traces Indices A r history outerF)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w zero one V GV e I R bottom S index cells D s kappa traces Indices A r history outerF)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_subset_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),resultFormula_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionCellRestriction.stages_semantics hM,
    ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,
    ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,
    ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.graph_semantics hM]
  exact construction hM hChoice

theorem construction_kernel_certificate {m : Nat} (w zero one V GV e I R bottom S index cells D s kappa traces Indices A r history outerF : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w zero one V GV e I R bottom S index cells D s kappa traces Indices A r history outerF))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w zero one V GV e I R bottom S index cells D s kappa traces Indices A r history outerF)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w zero one V GV e I R bottom S index cells D s kappa traces Indices A r history outerF)).mp (construction_models w zero one V GV e I R bottom S index cells D s kappa traces Indices A r history outerF hL hChoice)


end PPAC.Migration.ConstructionCountableReordering
