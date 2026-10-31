/- Pinned CellReorder.future/future_eq/future_square/future_mono and
reordered's terminal/continuous fields. The SAME exact ordinary supremum
family is constructed with existing native unique-function APIs.
Consumer: reordered's selected/omitted cell steps and countable reordering. -/
import PPAC.Migration.ConstructionFutureInduction

namespace PPAC.Migration.ConstructionFutureTower
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionSelectedCellRestriction (Base)
open ConstructionUnionPushout (Square)
open ConstructionConservativeHull (Closure)
open ConstructionCellRestriction (Stages)
open ConstructionFutureFamily (CutAt Suprema Products)
open ConstructionFirstAppearance (Timeline Cover At Index)
open ConstructionIntermediate (Sup)
open ConstructionRealCuts (Subset)
open ForcingConditionGraphs (function_unique function_input)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem sup_comm {V GV e A B F : M.Carrier .set} (h : Sup V GV e A B F) : Sup V GV e B A F :=
  ⟨h.1,h.2.2.1,h.2.1,fun D hD hBD hAD => h.2.2.2 D hD hAD hBD⟩

/-- Read the supremum at the SAME original stage, with no witness choice. -/
theorem sup_at {I V GV e retained S futures i D F : M.Carrier .set}
    (hS : ForcingConditionGraphs.FunctionOn I S) (hF : Suprema I V GV e retained S futures)
    (hiD : PureKuratowski.PairMember M i D S) (hiF : PureKuratowski.PairMember M i F futures) :
    Sup V GV e retained D F := by
  obtain ⟨D',hiD',hSup⟩ := ((hF.2 i F).mp hiF).2
  exact (function_unique hS hiD' hiD) ▸ hSup

/-- Exact source future_square, specializing full future_cut at the top.
The supplied ordinary supremum gains its conservative Base and Square. -/
theorem future_square (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom top S index cells deps retained i
      A D F PA PD PR GA GD GR ia idD ir : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : Stages V GV e S) (hRet : Closure V GV e retained)
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : ConstructionCountableConservativeHull.DependenciesClosed deps retained)
    (htop : (Project.FirstOrderSemantics.reduct M).mem top I)
    (hTop : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → i = top ∨ PureKuratowski.PairMember M i top R)
    (hTerminal : PureKuratowski.PairMember M top V S)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i I)
    (hiD : PureKuratowski.PairMember M i D S) (hiA : CutAt retained S i A)
    (hA : Base V GV e A PA GA ia) (hD : Base V GV e D PD GD idD)
    (hRetBase : Base V GV e retained PR GR ir) (hF : Sup V GV e retained D F) :
    ∃ PF GF iF, Base V GV e F PF GF iF ∧ Square A retained D F GA GR GD GF e ia ir idD := by
  have hCutTop : CutAt retained S top retained := ⟨V,hTerminal,fun x =>
    ⟨fun hx => ⟨hx,hRet.1 x hx⟩,fun hx => hx.1⟩⟩
  obtain ⟨F',PR',GR',ir',PF,GF,iF,hRetBase',hBaseF,hSupF,hSquare⟩ :=
    ConstructionFutureInduction.future_cut hM hw hz hzw hv hc hJ hStages hRet hT hIndex hCells hNew hGlobal
      hClosed hA hD hi hiD hiA htop (hTop i hi) hCutTop
  have heF := ConstructionFutureFamily.sup_unique hM hSupF (sup_comm hF)
  subst F'
  obtain ⟨heG,hei⟩ := ConstructionFutureSelected.base_graphs_unique hM hRetBase' hRetBase
  subst GR' ir'
  exact ⟨PF,GF,iF,hBaseF,hSquare⟩

/-- Terminal and bottom values are exact carriers, not further hulls. -/
theorem terminal (hM : FirstOrder.Theory.Models M nativeZF)
    {I V GV e retained S futures top : M.Carrier .set}
    (hS : ForcingConditionGraphs.FunctionOn I S) (hF : Suprema I V GV e retained S futures)
    (htop : (Project.FirstOrderSemantics.reduct M).mem top I)
    (hTerminal : PureKuratowski.PairMember M top V S) : PureKuratowski.PairMember M top V futures := by
  obtain ⟨F,htF,_⟩ := hF.1.2 top htop
  have hs := sup_at hS hF hTerminal htF
  have he : F = V := (ModelTransfer.extensionality hM).eq_of_same_members F V
    (fun x => ⟨hs.1.1 x,hs.2.2.1 x⟩)
  exact he ▸ htF

theorem bottom (hM : FirstOrder.Theory.Models M nativeZF)
    {I V GV e retained S futures b D : M.Carrier .set}
    (hS : ForcingConditionGraphs.FunctionOn I S) (hF : Suprema I V GV e retained S futures)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b I)
    (hRet : Closure V GV e retained) (hbD : PureKuratowski.PairMember M b D S)
    (hD : Subset D retained) : PureKuratowski.PairMember M b retained futures := by
  obtain ⟨F,hbF,_⟩ := hF.1.2 b hb
  have hs := sup_at hS hF hbD hbF
  have hFR := hs.2.2.2 retained ⟨hRet.1,hRet.2.1,hRet.2.2.1⟩ (fun _ h => h) hD
  have he : F = retained := (ModelTransfer.extensionality hM).eq_of_same_members F retained
    (fun x => ⟨hFR x,hs.2.1 x⟩)
  exact he ▸ hbF

/-- The source's directed union of earlier futures is the actual value at
an internal limit. Existing interval/restriction/union constructors suffice. -/
theorem timeline (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e I R bottom S retained futures : M.Carrier .set}
    (hT : Timeline hM V I R bottom S) (hF : Suprema I V GV e retained S futures)
    (hSourceStages : Stages V GV e S) (hStages : Stages V GV e futures) : Timeline hM V I R bottom futures := by
  have hMono := ConstructionFutureFamily.suprema_mono hF (ConstructionFutureLimit.timeline_mono hM hT)
  refine ⟨hT.1,hF.1,hT.2.2.1,hT.2.2.2.1,?_,?_,?_,?_⟩
  · rintro i x ⟨F,hiF,hx⟩
    exact (hStages i F hiF).1 x hx
  · intro i j x hij hix
    rcases hij with rfl | hij
    · exact hix
    · obtain ⟨F,hiF,hx⟩ := hix
      have hi := function_input hF.1 hiF
      have hj : (Project.FirstOrderSemantics.reduct M).mem j I := by
        obtain ⟨D,hiD,_⟩ := hT.2.1.2 i hi
        obtain ⟨E,hjE,_⟩ := hT.2.2.2.2.2.1 i j e (Or.inr hij) ⟨D,hiD,(hSourceStages i D hiD).2.1⟩
        exact function_input hT.2.1 hjE
      obtain ⟨G,hjG,_⟩ := hF.1.2 j hj
      exact ⟨G,hjG,hMono i j F G hi hj hij hiF hjG x hx⟩
  · intro x hx
    obtain ⟨i,hi,D,hiD,hxD⟩ := hT.2.2.2.2.2.2.1 x hx
    obtain ⟨F,hiF,_⟩ := hF.1.2 i hi
    exact ⟨i,hi,F,hiF,(sup_at hT.2.1 hF hiD hiF).2.2.1 x hxD⟩
  · intro b hb hnb hLimit x hx
    obtain ⟨B,hbB,hxB⟩ := hx
    obtain ⟨D,hbD,_⟩ := hT.2.1.2 b hb
    have hSupB := sup_at hT.2.1 hF hbD hbB
    have hbotb : PureKuratowski.PairMember M bottom b R := by
      rcases hT.2.2.2.1 b hb with he | hr
      · exact (hnb he.symm).elim
      · exact hr
    obtain ⟨K,hK⟩ := ConstructionFutureLimit.exists_interval hM I R bottom b
    obtain ⟨E,hE⟩ := ConstructionFutureLimit.exists_order hM K R
    have hKI : Subset K I := fun i hi => ((hK i).mp hi).1
    have hBotK := (hK bottom).mpr ⟨hT.2.2.1,Or.inl rfl,hbotb⟩
    obtain ⟨f,hf⟩ := ConstructionFutureLimit.restrict_family hM hF.1 hKI
    have hfMono := ConstructionFutureLimit.restrict_mono hKI hE hF.1 hMono hf
    have hfStages : Stages V GV e f := fun i F hiF => hStages i F ((hf.2 i F).mp hiF).2
    obtain ⟨U,hU⟩ := ConstructionSubobjectUnion.exists_union hM hf.1
    have hUClosed := ConstructionSubobjectUnion.closed (ConstructionFutureLimit.index_laws hM hT hK hE)
      ⟨bottom,hBotK⟩ hf.1 hfMono hfStages hU
    have hRU : Subset retained U := by
      obtain ⟨F,hbotF,_⟩ := hf.1.2 bottom hBotK
      obtain ⟨D0,hbotD,_⟩ := hT.2.1.2 bottom hT.2.2.1
      have hSup0 := sup_at hT.2.1 hF hbotD ((hf.2 bottom F).mp hbotF).2
      exact fun z hz => (hU z).mpr ⟨bottom,F,hBotK,hbotF,hSup0.2.1 z hz⟩
    have hDU : Subset D U := by
      intro z hz
      obtain ⟨i,hi,hib,hiz⟩ := hT.2.2.2.2.2.2.2 b hb hnb hLimit z ⟨D,hbD,hz⟩
      have hiK := (hK i).mpr ⟨hi,hT.2.2.2.1 i hi,hib⟩
      obtain ⟨F,hiF,_⟩ := hf.1.2 i hiK
      obtain ⟨Di,hiDi,hzDi⟩ := hiz
      exact (hU z).mpr ⟨i,F,hiK,hiF,(sup_at hT.2.1 hF hiDi ((hf.2 i F).mp hiF).2).2.2.1 z hzDi⟩
    have hxU := hSupB.2.2.2 U ⟨hUClosed.1,hUClosed.2.1,hUClosed.2.2.1⟩ hRU hDU x hxB
    obtain ⟨i,F,hi,hiF,hxF⟩ := (hU x).mp hxU
    exact ⟨i,hKI i hi,((hK i).mp hi).2.2,F,((hf.2 i F).mp hiF).2,hxF⟩

/-- Build the one actual future carrier/multiplication family and its entire
Timeline. No caller supplies conservative futures or future continuity. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom top S index cells deps retained : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : Stages V GV e S) (hRet : Closure V GV e retained)
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : ConstructionCountableConservativeHull.DependenciesClosed deps retained)
    (htop : (Project.FirstOrderSemantics.reduct M).mem top I)
    (hTop : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → i = top ∨ PureKuratowski.PairMember M i top R)
    (hTerminal : PureKuratowski.PairMember M top V S)
    : ∃ futures muls, Suprema I V GV e retained S futures ∧ Products I GV futures muls ∧
      Stages V GV e futures ∧ Timeline hM V I R bottom futures ∧
      PureKuratowski.PairMember M top V futures := by
  obtain ⟨PR,GR,ir,hRetBase⟩ := ConstructionFutureFamily.base_of_closed hM hv hc hJ hRet
  obtain ⟨futures,hF⟩ := ConstructionFutureFamily.exists_suprema hM hv hc hJ hRetBase hT.2.1 hStages
  have hFutureStages : Stages V GV e futures := by
    intro i F hiF
    obtain ⟨hi,D,hiD,hSupF⟩ := (hF.2 i F).mp hiF
    obtain ⟨A,hiA⟩ := ConstructionFutureFamily.cut_exists hM hT.2.1 hi
    obtain ⟨PA,GA,ia,hA⟩ := ConstructionFutureFamily.base_of_closed hM hv hc hJ
      (ConstructionFutureFamily.cut_closed hStages hRet hiA)
    obtain ⟨PD,GD,idD,hD⟩ := ConstructionFutureFamily.base_of_closed hM hv hc hJ (hStages i D hiD)
    obtain ⟨_,_,_,hBaseF,_⟩ := future_square hM hw hz hzw hv hc hJ hStages hRet hT hIndex hCells hNew hGlobal
      hClosed htop hTop hTerminal hi hiD hiA hA hD hRetBase hSupF
    exact hBaseF.1
  obtain ⟨muls,hmuls⟩ := ConstructionFutureFamily.exists_products hM hv hF.1
    (ConstructionFutureFamily.suprema_submonoids hF)
  exact ⟨futures,muls,hF,hmuls,hFutureStages,timeline hM hT hF hStages hFutureStages,terminal hM hT.2.1 hF htop hTerminal⟩

end PPAC.Migration.ConstructionFutureTower
