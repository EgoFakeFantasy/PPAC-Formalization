/- Pinned CellTowers.dependencies/dependencies_countable/dependencies_at.
Use the SAME first-appearance index, selected cell family and local coefficient
rows. This is a global internal set function on the original terminal monoid. -/
import PPAC.Migration.ConstructionStepCellSelection

namespace PPAC.Migration.ConstructionGlobalDependencies
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFirstAppearance (At NewAt Timeline Index)
open ConstructionTowerHistory (Row)
open ForcingConditionGraphs (FunctionOn function_unique)
open ForcingWithTopCarrier (Empty)
open ConstructionCountableConservativeHull (Dependencies)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (zero I R bottom S index cells x Y : M.Carrier .set) : Prop :=
  (At S bottom x ∧ Empty (M := M) Y) ∨
    ∃ i cell deps, PureKuratowski.PairMember M x i index ∧ NewAt I R S i x ∧
      PureKuratowski.PairMember M i cell cells ∧ ConstructionStepCell.DependencyField zero cell deps ∧
      PureKuratowski.PairMember M x Y deps

def Graph (zero V I R bottom S index cells deps : M.Carrier .set) : Prop :=
  FunctionOn V deps ∧ ∀ x Y, PureKuratowski.PairMember M x Y deps ↔
    (Project.FirstOrderSemantics.reduct M).mem x V ∧ Value zero I R bottom S index cells x Y

def value {m : Nat} (zero I R bottom S index cells x Y : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (ConstructionFirstAppearance.atStage S bottom x) (Project.Formula.isEmpty (.bound Y))) (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge index.succ.succ.succ x.succ.succ.succ 2)) (.conj (ConstructionFirstAppearance.newAt I.succ.succ.succ R.succ.succ.succ S.succ.succ.succ 2 x.succ.succ.succ) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge cells.succ.succ.succ 2 1)) (.conj (ConstructionStepCell.dependencyField zero.succ.succ.succ 1 0) (ProjectSyntax.encode id (Source.SetLanguage.edge 0 x.succ.succ.succ Y.succ.succ.succ))))))))))

theorem value_freeClosed {m : Nat} (zero I R bottom S index cells x Y : Fin m) :
    (value zero I R bottom S index cells x Y).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ConstructionFirstAppearance.atStage_freeClosed,ConstructionFirstAppearance.newAt_freeClosed,ConstructionStepCell.dependencyField_freeClosed,ProjectSyntax.freeClosed,Project.Formula.isEmpty]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero I R bottom S index cells x Y : Fin m) :
    Project.Formula.satisfies env (value zero I R bottom S index cells x Y) ↔ Value (env.bound zero) (env.bound I) (env.bound R) (env.bound bottom) (env.bound S) (env.bound index) (env.bound cells) (env.bound x) (env.bound Y) := by
  simp only [value,Value,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isEmpty_iff,ConstructionFirstAppearance.atStage_semantics hM,ConstructionFirstAppearance.newAt_semantics hM,ConstructionStepCell.dependencyField_semantics hM]
  rfl

def graph {m : Nat} (zero V I R bottom S index cells deps : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn deps V)) (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge deps.succ.succ 1 0)) (.conj (.mem (.bound 1) (.bound V.succ.succ)) (value zero.succ.succ I.succ.succ R.succ.succ bottom.succ.succ S.succ.succ index.succ.succ cells.succ.succ 1 0))))))

theorem graph_freeClosed {m : Nat} (zero V I R bottom S index cells deps : Fin m) :
    (graph zero V I R bottom S index cells deps).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero V I R bottom S index cells deps : Fin m) :
    Project.Formula.satisfies env (graph zero V I R bottom S index cells deps) ↔ Graph (env.bound zero) (env.bound V) (env.bound I) (env.bound R) (env.bound bottom) (env.bound S) (env.bound index) (env.bound cells) (env.bound deps) := by
  simp only [graph,Graph,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,ForcingConditionGraphs.functionOn_semantics (M := M),value_semantics hM]
  rfl

/-- The exact local row at any first-appearance stage; no new coefficient choice. -/
theorem value_at (hM : FirstOrder.Theory.Models M nativeZF)
    {zero V I R bottom S index cells i cell deps x Y : M.Carrier .set}
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : FunctionOn I cells) (hi : NewAt I R S i x)
    (hCell : PureKuratowski.PairMember M i cell cells)
    (hField : ConstructionStepCell.DependencyField zero cell deps) :
    Value zero I R bottom S index cells x Y ↔ PureKuratowski.PairMember M x Y deps := by
  constructor
  · rintro (⟨hb,_⟩ | ⟨j,c,d,_,hj,hc,hf,hY⟩)
    · exact (ConstructionFirstAppearance.newAt_not_bottom hM hT hi hb).elim
    · have he := ConstructionFirstAppearance.newAt_unique hM hT hj hi
      subst j
      have hec := function_unique hCells hc hCell
      subst c
      have hed := ConstructionStepCell.dependencyField_unique hf hField
      subst d
      exact hY
  · exact fun hY => Or.inr ⟨i,cell,deps,ConstructionFirstAppearance.index_at hM hT hIndex hi,hi,hCell,hField,hY⟩

theorem value_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV unitV I R bottom S index cells x : M.Carrier .set}
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV unitV I R S cells)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x V) :
    ∃ Y, Value zero I R bottom S index cells x Y := by
  classical
  by_cases hb : At S bottom x
  · obtain ⟨Y,hY⟩ := ForcingWithTopCarrier.exists_empty hM
    exact ⟨Y,Or.inl ⟨hb,hY⟩⟩
  · obtain ⟨i,hi⟩ := ConstructionFirstAppearance.exists_newAt hM hT hx hb
    obtain ⟨cell,j,D,T,deps,hCell,_,_,_,_,_,hField,hDeps,hxT,_⟩ := hNew i x hi
    obtain ⟨Y,hY,_⟩ := hDeps.1.2 x hxT
    exact ⟨Y,Or.inr ⟨i,cell,deps,ConstructionFirstAppearance.index_at hM hT hIndex hi,hi,hCell,hField,hY⟩⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV unitV I R bottom S index cells x Y Z : M.Carrier .set}
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : FunctionOn I cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV unitV I R S cells)
    (hy : Value zero I R bottom S index cells x Y)
    (hz : Value zero I R bottom S index cells x Z) : Y = Z := by
  rcases hy with ⟨hb,he⟩ | ⟨i,cell,deps,hix,hi,hCell,hField,hY⟩
  · rcases hz with ⟨_,he'⟩ | ⟨i,_,_,_,hi,_⟩
    · exact (ModelTransfer.extensionality hM).eq_of_same_members Y Z
        (fun z => ⟨fun h => (he z h).elim,fun h => (he' z h).elim⟩)
    · exact (ConstructionFirstAppearance.newAt_not_bottom hM hT hi hb).elim
  · obtain ⟨c,j,D,T,d,hc,_,_,_,_,_,hf,hd,_,_⟩ := hNew i x hi
    have hy' := (value_at hM hT hIndex hCells hi hc hf).mp
      (Or.inr ⟨i,cell,deps,hix,hi,hCell,hField,hY⟩)
    have hz' := (value_at hM hT hIndex hCells hi hc hf).mp hz
    exact function_unique hd.1 hy' hz'

theorem value_small (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV unitV I R bottom S index cells x Y : M.Carrier .set}
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : FunctionOn I cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV unitV I R S cells)
    (hy : Value zero I R bottom S index cells x Y) :
    (Project.FirstOrderSemantics.reduct M).MemberSubset Y V ∧ ForcingSupportSize.Small Y w := by
  rcases hy with ⟨_,he⟩ | ⟨i,cell,deps,hix,hi,hCell,hField,hY⟩
  · exact ⟨fun z hz => (he z hz).elim,ForcingSupportSize.small_empty hM w he⟩
  · obtain ⟨c,j,D,T,d,hc,_,_,hTj,_,_,hf,hd,_,_⟩ := hNew i x hi
    have hY' := (value_at hM hT hIndex hCells hi hc hf).mp
      (Or.inr ⟨i,cell,deps,hix,hi,hCell,hField,hY⟩)
    have hSmall := hd.2 x Y hY'
    exact ⟨fun z hz => hT.2.2.2.2.1 j z ⟨T,hTj,hSmall.1 z hz⟩,hSmall.2⟩

/-- Separation/Replacement produces the global function, including empty bottom rows. -/
theorem assembly (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV unitV I R bottom S index cells : M.Carrier .set}
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV unitV I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV unitV I R S cells) :
    ∃ deps, Graph zero V I R bottom S index cells deps ∧ Dependencies w V deps := by
  let schema : Project.BinarySchema 7 := {
    body := value 2 3 4 5 6 7 8 1 0
    freeClosed := value_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases zero (Fin.cases I (Fin.cases R (Fin.cases bottom
      (Fin.cases S (Fin.cases index (fun _ => cells))))))
    free := fun _ => zero }
  have he x Y : schema.denote env x Y ↔ Value zero I R bottom S index cells x Y :=
    value_semantics hM ((env.push x).push Y) 2 3 4 5 6 7 8 1 0
  have ht : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x V → ∃ Y, schema.denote env x Y := by
    intro x hx
    obtain ⟨Y,hY⟩ := value_total hM hT hIndex hNew hx
    exact ⟨Y,(he x Y).mpr hY⟩
  have hu : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x V → ∀ Y Z,
      schema.denote env x Y → schema.denote env x Z → Y = Z :=
    fun _ _ _ _ hy hz => value_unique hM hT hIndex hCells.1 hNew ((he _ _).mp hy) ((he _ _).mp hz)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema env V ht hu
  obtain ⟨deps,hDeps,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF
    (KuratowskiZF.interpretation hM) schema env ht hu
    (fun x Y hx hY => (hA Y).mpr ⟨x,hx,hY⟩)
  have hg : Graph zero V I R bottom S index cells deps :=
    ⟨((ForcingSupportSize.native_mapsTo hM V A deps).mpr hDeps).1,
      fun x Y => (hGraph x Y).trans (and_congr_right fun _ => he x Y)⟩
  exact ⟨deps,hg,hg.1,fun x Y hY => value_small hM hT hIndex hCells.1 hNew ((hg.2 x Y).mp hY).2⟩

/-- Source dependencies_at: equality with the row of the SAME selected local graph. -/
theorem dependencies_at (hM : FirstOrder.Theory.Models M nativeZF)
    {zero V I R bottom S index cells deps i cell localDeps x Y : M.Carrier .set}
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : FunctionOn I cells) (hg : Graph zero V I R bottom S index cells deps)
    (hi : NewAt I R S i x) (hc : PureKuratowski.PairMember M i cell cells)
    (hf : ConstructionStepCell.DependencyField zero cell localDeps) :
    PureKuratowski.PairMember M x Y deps ↔ PureKuratowski.PairMember M x Y localDeps := by
  rw [hg.2 x Y]
  have hx : (Project.FirstOrderSemantics.reduct M).mem x V := by
    obtain ⟨_,j,_,hj,_⟩ := hi
    exact hT.2.2.2.2.1 j x hj
  exact ⟨fun h => (value_at hM hT hIndex hCells hi hc hf).mp h.2,
    fun h => ⟨hx,(value_at hM hT hIndex hCells hi hc hf).mpr h⟩⟩

theorem dependencies_bottom (hM : FirstOrder.Theory.Models M nativeZF)
    {zero V I R bottom S index cells deps x Y : M.Carrier .set}
    (hT : Timeline hM V I R bottom S) (hg : Graph zero V I R bottom S index cells deps)
    (hx : At S bottom x) : PureKuratowski.PairMember M x Y deps ↔ Empty (M := M) Y := by
  constructor
  · intro hy
    rcases ((hg.2 x Y).mp hy).2 with ⟨_,h⟩ | ⟨i,_,_,_,hi,_⟩
    · exact h
    · exact (ConstructionFirstAppearance.newAt_not_bottom hM hT hi hx).elim
  · intro hy
    exact (hg.2 x Y).mpr ⟨hT.2.2.2.2.1 bottom x hx,Or.inl ⟨hx,hy⟩⟩

def assemblySentence {m : Nat} (w zero one V GV unitV I R bottom S index cells : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV unitV I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV unitV I R S cells) (.existsE (.conj (graph zero.succ V.succ I.succ R.succ bottom.succ S.succ index.succ cells.succ 0) (ConstructionCountableConservativeHull.dependencies w.succ V.succ 0)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,graph_freeClosed,ConstructionCountableConservativeHull.dependencies_freeClosed]

theorem assembly_models {m : Nat} (w zero one V GV unitV I R bottom S index cells : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (assemblySentence w zero one V GV unitV I R bottom S index cells)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (assemblySentence w zero one V GV unitV I R bottom S index cells)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,graph_semantics hM,ConstructionCountableConservativeHull.dependencies_semantics hM]
  exact assembly hM

theorem assembly_kernel_certificate {m : Nat} (w zero one V GV unitV I R bottom S index cells : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (assemblySentence w zero one V GV unitV I R bottom S index cells)) :=
  ModelTransfer.derives (fun _ hM => assembly_models w zero one V GV unitV I R bottom S index cells hM)

def atSentence {m : Nat} (zero V I R bottom S index cells deps i cell localDeps x Y : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn cells I)) (.imp (graph zero V I R bottom S index cells deps) (.imp (ConstructionFirstAppearance.newAt I R S i x) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge cells i cell)) (.imp (ConstructionStepCell.dependencyField zero cell localDeps) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge deps x Y)) (ProjectSyntax.encode id (Source.SetLanguage.edge localDeps x Y))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,ProjectSyntax.freeClosed,graph_freeClosed,ConstructionFirstAppearance.newAt_freeClosed,ConstructionStepCell.dependencyField_freeClosed]

theorem at_models {m : Nat} (zero V I R bottom S index cells deps i cell localDeps x Y : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (atSentence zero V I R bottom S index cells deps i cell localDeps x Y)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (atSentence zero V I R bottom S index cells deps i cell localDeps x Y)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics (M := M),ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,graph_semantics hM,ConstructionFirstAppearance.newAt_semantics hM,ConstructionStepCell.dependencyField_semantics hM]
  exact dependencies_at hM

theorem at_kernel_certificate {m : Nat} (zero V I R bottom S index cells deps i cell localDeps x Y : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (atSentence zero V I R bottom S index cells deps i cell localDeps x Y)) :=
  ModelTransfer.derives (fun _ hM => at_models zero V I R bottom S index cells deps i cell localDeps x Y hM)

def bottomSentence {m : Nat} (zero V I R bottom S index cells deps x Y : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (graph zero V I R bottom S index cells deps) (.imp (ConstructionFirstAppearance.atStage S bottom x) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge deps x Y)) (Project.Formula.isEmpty (.bound Y))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionFirstAppearance.timeline_freeClosed,graph_freeClosed,ConstructionFirstAppearance.atStage_freeClosed,ProjectSyntax.freeClosed,Project.Formula.isEmpty]

theorem bottom_models {m : Nat} (zero V I R bottom S index cells deps x Y : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (bottomSentence zero V I R bottom S index cells deps x Y)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (bottomSentence zero V I R bottom S index cells deps x Y)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_isEmpty_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionFirstAppearance.timeline_semantics hM,graph_semantics hM,ConstructionFirstAppearance.atStage_semantics hM]
  exact dependencies_bottom hM

theorem bottom_kernel_certificate {m : Nat} (zero V I R bottom S index cells deps x Y : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (bottomSentence zero V I R bottom S index cells deps x Y)) :=
  ModelTransfer.derives (fun _ hM => bottom_models zero V I R bottom S index cells deps x Y hM)

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q values top D mul e mark H C zero one u K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV : M.Carrier .set}
    (hctx : ConstructionSaturationIterationCases.Context hM w Q values top D mul e mark H C zero one u K mu B)
    (hrec : ConstructionSaturationIteration.Recursive hM w Q values top D mul e mark H C zero one K mu B B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa) :
    ∃ traces Indices A r I R S ODomains OE OImages bottom cells index deps,
      ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces ∧
      ConstructionBlockIndex.Data hM kappa traces Indices A r I R ∧
      ConstructionFlatStages.Result history outerF kappa V zero traces I S ∧
      ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages ∧
      ConstructionFlatOuter.Bottoms kappa zero S OImages ∧ ConstructionFlatOuter.Covers V I R S ∧
      Timeline hM V I R bottom S ∧
      ConstructionFlatAttachments.Steps hM w Q values top zero one traces V mulV unitV I R S ∧
      ConstructionStepCellSelection.Graph hM w zero one V mulV unitV I R S cells ∧ ConstructionStepCellSelection.AtNew hM w zero one V mulV unitV I R S cells ∧
      Index V I R bottom S index ∧ Graph zero V I R bottom S index cells deps ∧ Dependencies w V deps := by
  obtain ⟨traces,Indices,A,r,I,R,S,ODomains,OE,OImages,bottom,cells,ht,hd,hS,ho,hb,hcovers,hTimeline,hSteps,hCells,hNew⟩ :=
    ConstructionStepCellSelection.construction hM hOrder hChoice hctx hrec hindex hf hr
  obtain ⟨index,hIndex⟩ := ConstructionFirstAppearance.exists_index hM hTimeline
  obtain ⟨deps,hDeps,hCount⟩ := assembly hM hTimeline hIndex hCells hNew
  exact ⟨traces,Indices,A,r,I,R,S,ODomains,OE,OImages,bottom,cells,index,deps,
    ht,hd,hS,ho,hb,hcovers,hTimeline,hSteps,hCells,hNew,hIndex,hDeps,hCount⟩

def constructionSentence {m : Nat} (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionSaturationIterationCases.context w Q values top D mul e mark H C zero one u K mu B) (.imp (ConstructionSaturationIteration.recursive w Q values top D mul e mark H C zero one K mu B B history) (.imp (ConstructionSaturationIndex.data w mu kappa B) (.imp (ConstructionTowerTransitions.matrix B history zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionBlockTraces.family w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ values.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13) (.conj (ConstructionBlockIndex.data kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13 12 11 10 9 8) (.conj (ConstructionFlatStages.result history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13 9 7) (.conj (ConstructionBlockContinuity.outerData B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ terminalLegs.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 4) (.conj (ConstructionFlatOuter.bottoms kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 4) (.conj (ConstructionFlatOuter.covers V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 7) (.conj (ConstructionFirstAppearance.timeline V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 3 7) (.conj (ConstructionFlatAttachments.steps w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ values.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13 V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mulV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 7) (.conj (ConstructionStepCellSelection.graph w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mulV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 7 2) (.conj (ConstructionStepCellSelection.atNew w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mulV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 7 2) (.conj (ConstructionFirstAppearance.indexGraph V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 3 7 1) (.conj (graph zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 3 7 1 2 0) (ConstructionCountableConservativeHull.dependencies w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 0))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.result_freeClosed,ConstructionBlockContinuity.outerData_freeClosed,ConstructionFlatOuter.bottoms_freeClosed,ConstructionFlatOuter.covers_freeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFlatAttachments.steps_freeClosed,ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,graph_freeClosed,ConstructionCountableConservativeHull.dependencies_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {m : Nat}
    (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : (Project.fo_sentence (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.result_semantics hM,ConstructionBlockContinuity.outerData_semantics hM,ConstructionFlatOuter.bottoms_semantics hM,ConstructionFlatOuter.covers_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,ConstructionFlatAttachments.steps_semantics hM,ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,graph_semantics hM,ConstructionCountableConservativeHull.dependencies_semantics hM]
  exact construction hM hOrder hChoice

theorem construction_kernel_certificate {m : Nat} (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)

end PPAC.Migration.ConstructionGlobalDependencies
