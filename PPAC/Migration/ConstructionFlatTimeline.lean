/- Pinned BlockTower.flatten.mono/continuous, consumed in the original
FirstAppearance.Timeline. All stages belong to the SAME actual S and final V.
Reuse actual block/outer range laws, cut classification and strict coverage. -/
import PPAC.Migration.ConstructionFlatOuter

namespace PPAC.Migration.ConstructionFlatTimeline
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionBlockCuts (Cut)
open ConstructionBlockBoundary (Realized)
open ConstructionFirstAppearance (At Timeline)
open ConstructionTowerTransitions (Before)
open ConstructionTowerHistory (Row)
open ConstructionRoundSelection (Pack)
open ForcingConditionGraphs (function_unique function_input)
open ForcingWithTopCarrier (Empty)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem ends_at (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top zero one K mu history outerF kappa traces i code
      J Schedule last inner F Steps Events Roots L : M.Carrier .set}
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hcode : PureKuratowski.PairMember M i code traces)
    (hp : Pack J Schedule last inner F Steps Events Roots L code) :
    (Project.FirstOrderSemantics.reduct M).IsOrdinal J ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf J last ∧ Empty (M := M) zero ∧
      (Project.FirstOrderSemantics.reduct M).mem zero J := by
  obtain ⟨J',last',hends,hJ,hs,hz,hzJ⟩ := ConstructionBlockCuts.actual_ends hM ht (function_input ht.1 hcode)
  obtain ⟨Schedule',inner',F',Steps',Events',Roots',L',code',hcode',hp'⟩ := hends
  have ec := function_unique ht.1 hcode' hcode
  subst code'
  have eqs := ConstructionRoundSelection.pack_injective hp' hp
  have eJ := eqs.1
  have el := eqs.2.2.1
  subst J' last'
  exact ⟨hJ,hs,hz,hzJ⟩

theorem inner_mono {code W after V J Domains E F L Out Images j k x : M.Carrier .set}
    (hd : ConstructionActualBlocks.Data code W after V J Domains E F L Out Images)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k J) (hjk : Before j k)
    (hx : At Images j x) : At Images k x := by
  obtain ⟨Schedule,last,inner,Steps,Events,Roots,_,_,hE,_,_,hr,_,_⟩ := hd
  obtain ⟨A,hA,hx⟩ := hx
  obtain ⟨B,hB,_⟩ := hr.2.2.2.2.1.1.2 k hk
  exact ⟨B,hB,hr.2.2.2.2.2.2 j k A B hj hk ((hE.2 j k).mpr ⟨hj,hk,hjk⟩) hA hB x hx⟩

theorem outer_mono {B history F terminalLegs V Domains E Images i j x : M.Carrier .set}
    (ho : ConstructionBlockContinuity.OuterData B history F terminalLegs V Domains E Images)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i B)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j B) (hij : Before i j)
    (hx : At Images i x) : At Images j x := by
  obtain ⟨A,hA,hx⟩ := hx
  obtain ⟨D,hD,_⟩ := ho.2.2.2.2.1.1.2 j hj
  exact ⟨D,hD,ho.2.2.2.2.2.2.1 i j A D hi hj ((ho.2.1.2 i j).mpr ⟨hi,hj,hij⟩) hA hD x hx⟩

/-- Source successor <= later ordinal, using native ordinal trichotomy. -/
theorem successor_before (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa i next k : M.Carrier .set}
    (hkappa : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i kappa)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k kappa)
    (hik : (Project.FirstOrderSemantics.reduct M).mem i k)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf next i) : Before next k := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hKP := ZF.modelsKP hZF
  have hn := KP.successor_isOrdinal hKP (hkappa.mem hi) hs
  rcases Structure.IsOrdinal.trichotomy hZF.1 hn (hkappa.mem hk)
      (KP.difference_exists_d hKP) (KP.intersection_exists_d hKP next k) with he | hnk | hkn
  · exact Or.inr (hZF.1.eq_of_same_members next k he)
  · exact Or.inl hnk
  · rcases (hs k).mp hkn with hki | he
    · exact (KP.mem_irrefl_d hKP k ((hkappa.mem hk).transitive i hik k hki)).elim
    · have eq := hZF.1.eq_of_same_members k i he
      subst k
      exact (KP.mem_irrefl_d hKP i hik).elim

/-- Source blockStage_top into the actual next outer range. -/
theorem top_to_outer (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C B history zero P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV ODomains OE OImages
      i code next N W fromBase after J Domains E F L Out Images Schedule last inner Steps Events Roots x : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages)
    (hb : Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images)
    (hp : Pack J Schedule last inner F Steps Events Roots L code)
    (hx : At Images last x) : At OImages next x := by
  obtain ⟨Schedule',last',inner',Steps',Events',Roots',hp',_,_,_,_,_,_,htop⟩ := hb.2.2.2.2.2.1
  have el := (ConstructionRoundSelection.pack_injective hp hp').2.2.1
  subst last'
  obtain ⟨A,hA,hx⟩ := hx
  have hn := ((hf.2.2 next kappa after).mp hb.2.2.2.2.1).1
  obtain ⟨AO,hAO,_⟩ := ho.2.2.2.2.1.1.2 next hn
  have eq := ConstructionBlockStages.range_unique hM (htop A hA)
    (ConstructionFlatOuter.outer_range hM hv hB hf hr ho hb.2.2.1 hb.2.2.2.2.1 hAO)
  subst AO
  exact ⟨A,hAO,hx⟩

/-- The actual Trace in Family has the SAME successor carrier as Realized. -/
theorem realized_continuous (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history outerF kappa traces
      V i code next N W fromBase after J Domains E F L Out Images : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hcode : PureKuratowski.PairMember M i code traces)
    (hb : Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images) :
    ConstructionBlockContinuity.Continuous J Images := by
  obtain ⟨next',raw,Requests,N',mulN,eN,markN,HN,CN,L0,f,W',G,unitW,markW,HW,CW,NewOut,baseW,O,
    hs,_,hrj,_,_,_,_,_,htrace⟩ := ((ht.2 i code).mp hcode).2.1
  have en : next' = next := (ModelTransfer.extensionality hM).eq_of_same_members next' next
    (fun x => (hs x).trans (hb.1 x).symm)
  subst next'
  have ew : W' = W := ConstructionTowerHistory.field_unique 0 hv.1.1
    (ConstructionTowerValidity.row_field 0 hrj) hb.2.2.1
  subst W'
  exact ConstructionBlockContinuity.trace_continuous hM htrace hb.2.2.2.2.2.1

theorem monotone (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hg : ConstructionFlatStages.Graph history outerF kappa V zero traces I S)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages) :
    ∀ c d x, c = d ∨ PureKuratowski.PairMember M c d R → At S c x → At S d x := by
  intro c d x hcd hx
  rcases hcd with rfl | hcd
  · exact hx
  have hdCopy := hd
  obtain ⟨_,_,_,_,_,_,_,hR⟩ := hdCopy
  obtain ⟨hcI,hdI,_⟩ := (hR c d).mp hcd
  obtain ⟨imageD,himageD,_⟩ := hg.1.2 d hdI
  rcases ((hg.2 d imageD).mp himageD).2 with ⟨_,rfl⟩ | ⟨k,l,hcutD,hvalueD⟩
  · obtain ⟨imageC,himageC,hx⟩ := hx
    exact ⟨imageD,himageD,ConstructionFlatStages.graph_bounded hg c imageC himageC x hx⟩
  · obtain ⟨i,Jindex,j,hi,_,_,hcutC⟩ := ConstructionBlockCuts.source_cut hM hd hcd
    obtain ⟨_,hk,_,_⟩ := (ConstructionBlockCuts.cut_mem hM hd hcutD).mp hdI
    obtain ⟨imageC,himageC,hx⟩ := hx
    obtain ⟨code,next,N,W,fromBase,after,J,Domains,E,F,L,Out,Images,hcode,hb,himage⟩ :=
      (ConstructionFlatStages.graph_cut hg hcutC hcI).mp himageC
    obtain ⟨codeD,nextD,ND,WD,fromD,afterD,JD,DomainsD,ED,FD,LD,OutD,ImagesD,hcodeD,hbD,himageD'⟩ := hvalueD
    have hbData := hb.2.2.2.2.2.1
    have hbDataD := hbD.2.2.2.2.2.1
    obtain ⟨Schedule,last,inner,Steps,Events,Roots,hpack,_,hE,_,_,hresult,_,_⟩ := hbData
    obtain ⟨ScheduleD,lastD,innerD,StepsD,EventsD,RootsD,hpackD,_,_,_,_,hresultD,_,_⟩ := hbDataD
    have hj := function_input hresult.2.2.2.2.1.1 himage
    have hl := function_input hresultD.2.2.2.2.1.1 himageD'
    have hJ := ConstructionFlatOuter.realized_index hM hd hi hcode hb
    have hJD := ConstructionFlatOuter.realized_index hM hd hk hcodeD hbD
    rcases (ConstructionBlockCuts.cut_lt hM hd hcutC hcutD hcI hdI).mp hcd with hik | ⟨eik,hjl⟩
    · have hB := hindex.2.2.2.1
      obtain ⟨_,hSucc,_,_⟩ := ends_at hM ht hcode hpack
      have hlast := inner_mono hb.2.2.2.2.2.1 hj hSucc.predecessor_mem
        (ConstructionActualBlocks.before_last hM hSucc hj) ⟨imageC,himage,hx⟩
      have hnAt := top_to_outer hM hv hB hf hr ho hb hpack hlast
      have hnB := ((hf.2.2 next kappa after).mp hb.2.2.2.2.1).1
      have hkB := (hB k).mpr (Or.inl hk)
      have hnk := successor_before hM hindex.1.1 hi hk hik hb.1
      have hkAt := outer_mono ho hnB hkB hnk hnAt
      obtain ⟨hJDord,_,hzero,hzeroJD⟩ := ends_at hM ht hcodeD hpackD
      have hzAt := (ConstructionFlatOuter.base_at hM hv hB hf hr ho hbD hzeroJD).mpr hkAt
      have hzl : Before zero l := by
        classical
        by_cases he : l = zero
        · exact Or.inr he.symm
        · exact Or.inl (Structure.IsOrdinal.empty_mem_of_nonempty
            (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) (hJDord.mem hl)
            (ConstructionTowerIterationCases.nonzero_nonempty hM hzero he) hzero)
      exact (ConstructionFlatStages.realized_at hM ht.1 hf.2.1 hg hcutD hdI hcodeD hbD hl).mpr
        (inner_mono hbD.2.2.2.2.2.1 hzeroJD hl hzl hzAt)
    · subst k
      have eqJ := function_unique hd.1.1 hJD hJ
      have hlJ := eqJ ▸ hl
      exact (ConstructionFlatStages.realized_at hM ht.1 hf.2.1 hg hcutD hdI hcode hb hlJ).mpr
        (inner_mono hb.2.2.2.2.2.1 hj hlJ (Or.inl hjl) ⟨imageC,himage,hx⟩)

theorem continuous (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages bottom : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hg : ConstructionFlatStages.Graph history outerF kappa V zero traces I S)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages)
    (hbottom : ConstructionCutLimits.Bottom zero I R bottom)
    (hb : ConstructionFlatOuter.Bottoms kappa zero S OImages)
    (hcovers : ConstructionFlatOuter.Covers V I R S) :
    ∀ c, (Project.FirstOrderSemantics.reduct M).mem c I → c ≠ bottom →
      (¬ ∃ b, ConstructionFirstAppearance.Cover I R b c) → ∀ x, At S c x →
        ∃ b, (Project.FirstOrderSemantics.reduct M).mem b I ∧ PureKuratowski.PairMember M b c R ∧ At S b x := by
  intro c hcI hne hno x hx
  have hall := ConstructionBlockCuts.all_successors hM hindex.1.1 ht hd
  rcases ConstructionCutLimits.classify hM hindex.1.1 hd hall hbottom ⟨hcI,hne,hno⟩ with he | ⟨i,J,j,hi,hJ,hj,hcut,hcases⟩
  · obtain ⟨image,himage,hx⟩ := hx
    exact hcovers c he x (ConstructionFlatStages.graph_bounded hg c image himage x hx)
  · rcases hcases with hlimit | ⟨rfl,hlimit⟩
    · obtain ⟨code,hcode,_⟩ := ht.1.2 i hi
      obtain ⟨next,N,W,fromBase,after,J',Domains,E,F,L,Out,Images,hreal⟩ :=
        ConstructionBlockBoundary.family_realized hM hv hindex.2.2.2.1 hf hr ht i code hcode
      have hJ' := ConstructionFlatOuter.realized_index hM hd hi hcode hreal
      have eJ := function_unique hd.1.1 hJ hJ'
      subst J'
      have hxj := (ConstructionFlatStages.realized_at hM ht.1 hf.2.1 hg hcut hcI hcode hreal hj).mp hx
      obtain ⟨k,hkj,hxk⟩ := realized_continuous hM hv ht hcode hreal j hj hlimit x hxj
      have hkJ := (hd.2.1.2 i J hJ).transitive j hj k hkj
      obtain ⟨b,hbI,hcutB⟩ := ConstructionBlockCuts.exists_cut hM hd hJ hkJ
      exact ⟨b,hbI,(ConstructionBlockCuts.cut_lt hM hd hcutB hcut hbI hcI).mpr (Or.inr ⟨rfl,hkj⟩),
        (ConstructionFlatStages.realized_at hM ht.1 hf.2.1 hg hcutB hbI hcode hreal hkJ).mpr hxk⟩
    · have hxi := (hb i c hi hcut x).mp hx
      have hiB := (hindex.2.2.2.1 i).mpr (Or.inl hi)
      obtain ⟨k,hki,hxk⟩ := ho.2.2.2.2.2.2.2 i hiB hlimit x hxi
      have hk := hindex.1.1.transitive i hi k hki
      obtain ⟨Jk,last,hends,_,_,_,hzJk⟩ := ConstructionBlockCuts.actual_ends hM ht hk
      have hJk := ConstructionBlockCuts.ends_index hM hd hk hends
      obtain ⟨b,hbI,hcutB⟩ := ConstructionBlockCuts.exists_cut hM hd hJk hzJk
      exact ⟨b,hbI,(ConstructionBlockCuts.cut_lt hM hd hcutB hcut hbI hcI).mpr (Or.inl hki),
        (hb k b hk hcutB x).mpr hxk⟩

/-- All clauses of the EXISTING Timeline hold for the SAME actual graph. -/
theorem assembly (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hS : ConstructionFlatStages.Result history outerF kappa V zero traces I S)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages) :
    ∃ bottom, Timeline hM V I R bottom S := by
  obtain ⟨bottom,hbottom,_,_⟩ := ConstructionCutLimits.construction hM hindex.1.1 ht hd ⟨w,hindex.2.2.1⟩
  obtain ⟨hb,hcovers⟩ := ConstructionFlatOuter.assembly hM hv hindex hf hr ht hd hS.1 ho
  refine ⟨bottom,hd.2.2.2.2.2.2.1,hS.1.1,hbottom.2.1,hbottom.2.2,?_,
    monotone hM hv hindex hf hr ht hd hS.1 ho,hS.2.2.2,?_⟩
  · rintro c x ⟨image,himage,hx⟩
    exact hS.2.1 c image himage x hx
  · exact continuous hM hv hindex hf hr ht hd hS.1 ho hbottom hb hcovers

/-- Actual recursive caller. Preserve every earlier graph and return the
full Timeline, without assuming monotonicity, continuity, a bottom or coverage. -/
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
    ∃ traces Indices A r I R S ODomains OE OImages bottom,
      ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces ∧
      ConstructionBlockIndex.Data hM kappa traces Indices A r I R ∧
      ConstructionFlatStages.Result history outerF kappa V zero traces I S ∧
      ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages ∧
      ConstructionFlatOuter.Bottoms kappa zero S OImages ∧ ConstructionFlatOuter.Covers V I R S ∧
      Timeline hM V I R bottom S := by
  obtain ⟨traces,Indices,A,r,I,R,S,ODomains,OE,OImages,ht,hd,hS,ho,hb,hcovers⟩ :=
    ConstructionFlatOuter.construction hM hOrder hChoice hctx hrec hindex hf hr
  have hv := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice hctx hrec (fun _ h => h)).1
  obtain ⟨bottom,hTimeline⟩ := assembly hM hv hindex hf hr ht hd hS ho
  exact ⟨traces,Indices,A,r,I,R,S,ODomains,OE,OImages,bottom,ht,hd,hS,ho,hb,hcovers,hTimeline⟩

def assemblySentence {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionTowerValidity.valid w Q values top D mul e mark H C B history) (.imp
    (ConstructionSaturationIndex.data w mu kappa B) (.imp (ConstructionTowerTransitions.matrix B history
    zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V mulV unitV markV HV CV terminalLegs
    baseV kappa) (.imp (ConstructionBlockTraces.family w Q values top zero one K mu history outerF kappa
    traces) (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R) (.imp
    (ConstructionFlatStages.result history outerF kappa V zero traces I S) (.imp
    (ConstructionBlockContinuity.outerData B history outerF terminalLegs V ODomains OE OImages) (.existsE
    (ConstructionFirstAppearance.timeline V.succ I.succ R.succ 0 S.succ))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerValidity.valid_freeClosed,ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.result_freeClosed,ConstructionBlockContinuity.outerData_freeClosed,ConstructionFirstAppearance.timeline_freeClosed]

theorem assembly_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : Fin m) : (Project.fo_sentence (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,ConstructionTowerValidity.valid_semantics hM,ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.result_semantics hM,ConstructionBlockContinuity.outerData_semantics hM,ConstructionFirstAppearance.timeline_semantics hM]
  exact assembly hM

theorem assembly_kernel_certificate {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages)) := by
  apply ModelTransfer.derives
  intro M hM
  exact assembly_models hM w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages

def constructionSentence {m : Nat} (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionSaturationIterationCases.context w Q values top D mul e mark H C zero one u K mu B)
    (.imp (ConstructionSaturationIteration.recursive w Q values top D mul e mark H C zero one K mu B B
    history) (.imp (ConstructionSaturationIndex.data w mu kappa B) (.imp
    (ConstructionTowerTransitions.matrix B history zero P outerF) (.imp (ConstructionTowerHistory.row
    history kappa V mulV unitV markV HV CV terminalLegs baseV kappa) (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionBlockTraces.family w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    values.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10) (.conj (ConstructionBlockIndex.data
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 9 8 7 6 5) (.conj
    (ConstructionFlatStages.result history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 6 4) (.conj
    (ConstructionBlockContinuity.outerData B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    terminalLegs.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 2 1) (.conj (ConstructionFlatOuter.bottoms
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 4 1) (.conj (ConstructionFlatOuter.covers
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 4) (ConstructionFirstAppearance.timeline
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 0 4)))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.result_freeClosed,ConstructionBlockContinuity.outerData_freeClosed,ConstructionFlatOuter.bottoms_freeClosed,ConstructionFlatOuter.covers_freeClosed,ConstructionFirstAppearance.timeline_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {m : Nat}
    (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : (Project.fo_sentence (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.result_semantics hM,ConstructionBlockContinuity.outerData_semantics hM,ConstructionFlatOuter.bottoms_semantics hM,ConstructionFlatOuter.covers_semantics hM,ConstructionFirstAppearance.timeline_semantics hM]
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

end PPAC.Migration.ConstructionFlatTimeline
