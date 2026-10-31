/- Pinned CellCuts.selected_dependencies/selected_word. Read the SAME selected
cell and coefficient graphs through global dependencies_at. Consumer:
restrict_selected, including its single retained-base intersection. -/
import PPAC.Migration.ConstructionGlobalDependencies

namespace PPAC.Migration.ConstructionSelectedCellWords
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFirstAppearance (Cover NewAt Timeline Index)
open ConstructionCountableConservativeHull (DependenciesClosed)
open ConstructionCellGeneration (ClosureMember)
open ConstructionRealCuts (Subset)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn function_input function_unique)
open ConstructionRoundSelection (Pack)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Every genuinely new element of the fixed pair of stage images is NewAt i. -/
theorem new_at {I R S i j D T x : M.Carrier .set}
    (hS : FunctionOn I S) (hij : Cover I R i j)
    (hD : PureKuratowski.PairMember M i D S) (hT : PureKuratowski.PairMember M j T S)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x T)
    (hnot : ¬ (Project.FirstOrderSemantics.reduct M).mem x D) : NewAt I R S i x := by
  refine ⟨hij.1,j,hij,⟨T,hT,hx⟩,?_⟩
  rintro ⟨D',hD',hx'⟩
  exact hnot ((function_unique hS hD' hD) ▸ hx')

/-- Global Closed implies local Closed for the SAME selected dependency graph.
Old rows are empty by the existing exact row formula. -/
theorem local_closed (hM : FirstOrder.Theory.Models M nativeZF)
    {zero V I R bottom S index cells deps retained i j D T cell n generators parameters supports localDeps : M.Carrier .set}
    (hTimeline : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : FunctionOn I cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : DependenciesClosed deps retained)
    (hij : Cover I R i j) (hD : PureKuratowski.PairMember M i D S)
    (hT : PureKuratowski.PairMember M j T S) (hc : PureKuratowski.PairMember M i cell cells)
    (hField : ConstructionStepCell.DependencyField zero cell localDeps)
    (hLocal : ConstructionAttachmentDependencies.Graph D n generators parameters T supports localDeps) :
    DependenciesClosed localDeps retained := by
  intro x Y hx hY z hz
  classical
  by_cases hxD : (Project.FirstOrderSemantics.reduct M).mem x D
  · exact ((((hLocal.2 x Y).mp hY).2 z).mp hz).1 hxD |>.elim
  · have hNew := new_at hTimeline.2.1 hij hD hT (function_input hLocal.1 hY) hxD
    have hGlobalY := (ConstructionGlobalDependencies.dependencies_at hM hTimeline hIndex hCells hGlobal hNew hc hField).mpr hY
    exact hClosed x Y hx hGlobalY z hz

/-- Reuse the existing local selected_word proof. One fixed cut works for
ALL retained new words; no coefficient or cell is reselected per word. -/
theorem retained_result (hM : FirstOrder.Theory.Models M nativeZF)
    {w D n W V GV unitV O P F T parameters old generators supports localDeps retained x : M.Carrier .set}
    (hResult : ConstructionCellParameters.Result w D n W V GV unitV O P F T parameters old generators supports localDeps)
    (hClosed : DependenciesClosed localDeps retained)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x retained)
    (hxT : (Project.FirstOrderSemantics.reduct M).mem x T)
    (hxD : ¬ (Project.FirstOrderSemantics.reduct M).mem x D) :
    Subset parameters retained ∧ MapsTo n retained generators ∧ ∃ cut,
      (∀ z, (Project.FirstOrderSemantics.reduct M).mem z cut ↔
        (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z D) ∧
      ∀ y, (Project.FirstOrderSemantics.reduct M).mem y retained →
        (Project.FirstOrderSemantics.reduct M).mem y T → ¬ (Project.FirstOrderSemantics.reduct M).mem y D →
        ClosureMember n V GV unitV old generators cut y := by
  have hId := hResult.1.2.2.2.2.1
  have hGen := hResult.1.2.2.2.2.2.2.1
  have hSupports := hResult.2.2.2.2.1
  have hLocal := hResult.2.2.2.2.2.1
  obtain ⟨hp,hg,cut,hcut,hword⟩ := ConstructionAttachmentDependencies.selected_word hM
    hSupports hLocal hId hGen hClosed hxT hx hxD
  refine ⟨hp,hg,cut,hcut,?_⟩
  intro y hy hyT hyD
  obtain ⟨_,_,cut',hcut',hword'⟩ := ConstructionAttachmentDependencies.selected_word hM
    hSupports hLocal hId hGen hClosed hyT hy hyD
  have he : cut' = cut := (ModelTransfer.extensionality hM).eq_of_same_members cut' cut
    (fun z => (hcut' z).trans (hcut z).symm)
  exact he ▸ hword'

/-- The literal chosen record is retained, so its parameters, generators,
supports and localDeps can be identified when unpacking either presentation. -/
def Retained (w zero V GV unitV D T cell retained cut : M.Carrier .set) : Prop :=
  ∃ n W O P F parameters old generators supports localDeps tag presentation,
    Pack tag presentation parameters old generators supports localDeps zero zero cell ∧
    ConstructionCellParameters.Result w D n W V GV unitV O P F T parameters old generators supports localDeps ∧
    Subset parameters retained ∧ MapsTo n retained generators ∧
    (∀ z, (Project.FirstOrderSemantics.reduct M).mem z cut ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z D) ∧
    ∀ y, (Project.FirstOrderSemantics.reduct M).mem y retained →
      (Project.FirstOrderSemantics.reduct M).mem y T → ¬ (Project.FirstOrderSemantics.reduct M).mem y D →
      ClosureMember n V GV unitV old generators cut y

theorem from_cell (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV unitV I R bottom S index cells deps retained i j D T cell x : M.Carrier .set}
    (hTimeline : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : FunctionOn I cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : DependenciesClosed deps retained)
    (hij : Cover I R i j) (hD : PureKuratowski.PairMember M i D S)
    (hT : PureKuratowski.PairMember M j T S) (hc : PureKuratowski.PairMember M i cell cells)
    (hData : ConstructionStepCell.Data hM w zero one V GV unitV D T cell)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x retained)
    (hxT : (Project.FirstOrderSemantics.reduct M).mem x T)
    (hxD : ¬ (Project.FirstOrderSemantics.reduct M).mem x D) :
    ∃ cut, Retained w zero V GV unitV D T cell retained cut := by
  rcases hData with h | h
  · obtain ⟨mul,a,b,d,node,factor,terminal,target,L,C,projection,N,act,E,W,unit,G,K,P,O,F,
      p0,p1,presentation,parameters,old,generators,supports,localDeps,
      _,_,_,_,_,_,_,_,_,_,_,_,hResult,hPack,_,_,_,_,_,_⟩ := h
    have hField : ConstructionStepCell.DependencyField zero cell localDeps :=
      ⟨zero,presentation,parameters,old,generators,supports,hPack⟩
    have hLocal := local_closed hM hTimeline hIndex hCells hGlobal hClosed hij hD hT hc hField hResult.2.2.2.2.2.1
    obtain ⟨hp,hg,cut,hcut,hwords⟩ := retained_result hM hResult hLocal hx hxT hxD
    exact ⟨cut,w,W,O,P,F,parameters,old,generators,supports,localDeps,zero,presentation,hPack,hResult,hp,hg,hcut,hwords⟩
  · obtain ⟨mul,n,P,C,L,projection,A,W,B,T',G,unit,O,roots,F,p0,presentation,parameters,old,generators,supports,localDeps,
      _,_,_,_,_,_,_,_,_,_,_,_,_,hResult,hPack,_,_,_,_⟩ := h
    have hField : ConstructionStepCell.DependencyField zero cell localDeps :=
      ⟨one,presentation,parameters,old,generators,supports,hPack⟩
    have hLocal := local_closed hM hTimeline hIndex hCells hGlobal hClosed hij hD hT hc hField hResult.2.2.2.2.2.1
    obtain ⟨hp,hg,cut,hcut,hwords⟩ := retained_result hM hResult hLocal hx hxT hxD
    exact ⟨cut,n,W,O,roots,F,parameters,old,generators,supports,localDeps,one,presentation,hPack,hResult,hp,hg,hcut,hwords⟩

/-- Actual source selected_dependencies and selected_word, for every internal
selected stage and retained word, with the full chosen cell still available. -/
theorem selected (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV unitV I R bottom S index cells deps retained i x : M.Carrier .set}
    (hTimeline : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV unitV I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV unitV I R S cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : DependenciesClosed deps retained)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x retained) (hi : NewAt I R S i x) :
    ∃ cell j D T cut, PureKuratowski.PairMember M i cell cells ∧ Cover I R i j ∧
      PureKuratowski.PairMember M i D S ∧ PureKuratowski.PairMember M j T S ∧
      ConstructionStepCell.Data hM w zero one V GV unitV D T cell ∧
      Retained w zero V GV unitV D T cell retained cut := by
  obtain ⟨cell,j,D,T,localDeps,hc,hij,hD,hT,_,hData,_,_,hxT,hxD⟩ := hNew i x hi
  obtain ⟨cut,hcut⟩ := from_cell hM hTimeline hIndex hCells.1 hGlobal hClosed hij hD hT hc hData hx hxT hxD
  exact ⟨cell,j,D,T,cut,hc,hij,hD,hT,hData,hcut⟩

/-- Unpacking either full presentation must read the fixed retained fields.
The generator domain can use its original presentation index: only the SAME
generator graph matters, so no equality of externally chosen witnesses is assumed. -/
theorem read_retained {w zero V GV unitV D T cell retained cut
    tag presentation parameters old generators supports localDeps n : M.Carrier .set}
    (h : Retained w zero V GV unitV D T cell retained cut)
    (hp : Pack tag presentation parameters old generators supports localDeps zero zero cell)
    (hGen : MapsTo n V generators) :
    Subset parameters retained ∧ MapsTo n retained generators ∧
      (∀ z, (Project.FirstOrderSemantics.reduct M).mem z cut ↔
        (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z D) ∧
      ∀ y, (Project.FirstOrderSemantics.reduct M).mem y retained →
        (Project.FirstOrderSemantics.reduct M).mem y T → ¬ (Project.FirstOrderSemantics.reduct M).mem y D →
        ClosureMember n V GV unitV old generators cut y := by
  obtain ⟨n',W,O,P,F,parameters',old',generators',supports',localDeps',tag',presentation',hp',_,hParams,hGens,hCut,hWords⟩ := h
  obtain ⟨_,_,epa,eo,eg,_,_,_,_⟩ := ConstructionRoundSelection.pack_injective hp hp'
  subst parameters' old' generators'
  refine ⟨hParams,⟨hGen.1,hGens.2⟩,hCut,?_⟩
  intro y hy hyT hyD
  have hWord := hWords y hy hyT hyD
  exact ⟨hWord.1,fun Q hQ hOld hGenerators => hWord.2 Q hQ hOld ⟨hGens.1,hGenerators.2⟩⟩

/-- The exact old-stage intersection supplies the range witnesses required
by the EXISTING Probe.exists_preimage theorem. -/
theorem probe_covered {D retained cut parameters a b d node inc : M.Carrier .set}
    (hParams : ConstructionCellParameters.ProbeParameters a b d node parameters)
    (hpD : Subset parameters D) (hpS : Subset parameters retained)
    (hCut : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z cut ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z D)
    (hId : ForcingConditionGraphs.IdentityGraph cut inc) :
    ConstructionCellPreimage.ProbeCovered inc a b d node := by
  have hRange z (hz : (Project.FirstOrderSemantics.reduct M).mem z parameters) :
      ∃ x, PureKuratowski.PairMember M x z inc :=
    ⟨z,(hId z z).mpr ⟨(hCut z).mpr ⟨hpS z hz,hpD z hz⟩,rfl⟩⟩
  exact ⟨hRange a ((hParams a).mpr (Or.inl rfl)),
    hRange b ((hParams b).mpr (Or.inr (Or.inl rfl))),
    hRange d ((hParams d).mpr (Or.inr (Or.inr (Or.inl rfl)))),
    fun i y hiy => hRange y ((hParams y).mpr (Or.inr (Or.inr (Or.inr ⟨i,hiy⟩))))⟩

/-- The SAME stored Merger parameter set covers every original start coordinate. -/
theorem merger_covered {D retained cut parameters P inc : M.Carrier .set}
    (hParams : ConstructionCellParameters.MergerParameters P parameters)
    (hpD : Subset parameters D) (hpS : Subset parameters retained)
    (hCut : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z cut ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z D)
    (hId : ForcingConditionGraphs.IdentityGraph cut inc) :
    ConstructionCellPreimage.MergerCovered P inc := by
  intro i j a b hStart
  have hRange z (hz : (Project.FirstOrderSemantics.reduct M).mem z parameters) :
      ∃ x, PureKuratowski.PairMember M x z inc :=
    ⟨z,(hId z z).mpr ⟨(hCut z).mpr ⟨hpS z hz,hpD z hz⟩,rfl⟩⟩
  exact ⟨hRange a ((hParams a).mpr ⟨i,j,a,b,hStart,Or.inl rfl⟩),
    hRange b ((hParams b).mpr ⟨i,j,a,b,hStart,Or.inr rfl⟩)⟩

def retainedFormula {m : Nat} (w zero V GV unitV D T cell retained cut : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRoundSelection.pack 1 0 6 5 4 3 2 zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ cell.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (ConstructionCellParameters.result w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 7 T.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 4 3 2) (.conj (Project.Formula.subset (.bound 6) (.bound retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 4 11 retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ConstructionAttachmentCoefficients.intersection cut.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.forallE (.imp (.mem (.bound 0) (.bound retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound 0) (.bound T.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.neg (.mem (.bound 0) (.bound D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))) (ConstructionCellGeneration.closureMember 12 V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 cut.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 0))))))))))))))))))))))

theorem retainedFormula_freeClosed {m : Nat} (w zero V GV unitV D T cell retained cut : Fin m) :
    (retainedFormula w zero V GV unitV D T cell retained cut).FreeClosed := by
  simp -implicitDefEqProofs [retainedFormula,Definitional.Formula.FreeClosed,Project.Formula.subset,ProjectSyntax.freeClosed,
    ConstructionRoundSelection.pack_freeClosed,ConstructionCellParameters.result_freeClosed,
    ConstructionAttachmentCoefficients.intersection_freeClosed,ConstructionCellGeneration.closureMember_freeClosed]

theorem retainedFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero V GV unitV D T cell retained cut : Fin m) :
    Project.Formula.satisfies env (retainedFormula w zero V GV unitV D T cell retained cut) ↔ Retained (env.bound w) (env.bound zero) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound D) (env.bound T) (env.bound cell) (env.bound retained) (env.bound cut) := by
  simp only [retainedFormula,Retained,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionRoundSelection.pack_semantics hM,ConstructionCellParameters.result_semantics hM,
    ConstructionAttachmentCoefficients.intersection_semantics (M := M),ConstructionCellGeneration.closureMember_semantics hM]
  rfl

def selectedSentence {m : Nat} (w zero one V GV unitV I R bottom S index cells deps retained i x : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV unitV I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV unitV I R S cells) (.imp (ConstructionGlobalDependencies.graph zero V I R bottom S index cells deps) (.imp (ConstructionCountableConservativeHull.dependenciesClosed deps retained) (.imp (.mem (.bound x) (.bound retained)) (.imp (ConstructionFirstAppearance.newAt I R S i x) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge cells.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ 4)) (.conj (ConstructionFirstAppearance.cover I.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ 3) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ.succ 3 1)) (.conj (ConstructionStepCell.data w.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ 2 1 4) (retainedFormula w.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ 2 1 4 retained.succ.succ.succ.succ.succ 0)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,
      ConstructionFirstAppearance.newAt_freeClosed,ConstructionFirstAppearance.cover_freeClosed,
      ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,
      ConstructionGlobalDependencies.graph_freeClosed,ConstructionCountableConservativeHull.dependenciesClosed_freeClosed,
      ConstructionStepCell.data_freeClosed,retainedFormula_freeClosed]

theorem selected_models {m : Nat} (w zero one V GV unitV I R bottom S index cells deps retained i x : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (selectedSentence w zero one V GV unitV I R bottom S index cells deps retained i x)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (selectedSentence w zero one V GV unitV I R bottom S index cells deps retained i x)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,
    ConstructionFirstAppearance.newAt_semantics hM,ConstructionFirstAppearance.cover_semantics hM,
    ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,
    ConstructionGlobalDependencies.graph_semantics hM,ConstructionCountableConservativeHull.dependenciesClosed_semantics hM,
    ConstructionStepCell.data_semantics hM,retainedFormula_semantics hM]
  exact selected hM

theorem selected_kernel_certificate {m : Nat} (w zero one V GV unitV I R bottom S index cells deps retained i x : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (selectedSentence w zero one V GV unitV I R bottom S index cells deps retained i x)) :=
  ModelTransfer.derives (fun _ hM => selected_models w zero one V GV unitV I R bottom S index cells deps retained i x hM)

end PPAC.Migration.ConstructionSelectedCellWords
