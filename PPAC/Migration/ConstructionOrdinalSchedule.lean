/- Pinned CompleteRounds.ScheduleIndex / schedule / place, transported
along the SAME actual internal order collapse to its native ordinal.
Actual consumer: MonoidTowers.ConstructionIteration via existing internal
ordinal recursion. Reuse native inverse/composition functions, not a new
function/category/recursor backend. No request or position is discarded. -/
import PPAC.Migration.ConstructionScheduleOrderSyntax

namespace PPAC.Migration.ConstructionOrdinalSchedule
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ConstructionProbeMappedPath (NodeMap)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Data (hM : FirstOrder.Theory.Models M nativeZF)
    (Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last : M.Carrier .set) : Prop :=
  ConstructionScheduleOrder.OrderedData hM Requests K A I top base Schedule Place r R ordinal ∧
    (Project.FirstOrderSemantics.reduct M).IsWellOrderCollapseFunction (KuratowskiZF.interpretation hM) collapse R I I ∧
    (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) collapse I ordinal ∧
    (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) inverse ordinal I ∧
    (∀ j i, PureKuratowski.PairMember M j i inverse ↔ PureKuratowski.PairMember M i j collapse) ∧
    (∀ i j a b, PureKuratowski.PairMember M i a collapse → PureKuratowski.PairMember M j b collapse →
      (PureKuratowski.PairMember M i j R ↔ (Project.FirstOrderSemantics.reduct M).mem a b)) ∧
    MapsTo ordinal Requests ordSchedule ∧ NodeMap inverse Schedule ordSchedule ∧
    Injection A ordinal ordPlace ∧ NodeMap Place collapse ordPlace ∧
    (Project.FirstOrderSemantics.reduct M).mem last ordinal ∧ PureKuratowski.PairMember M top last collapse ∧
    (Project.FirstOrderSemantics.reduct M).IsOrdinal last ∧
    (∀ a, (Project.FirstOrderSemantics.reduct M).mem a ordinal ↔
      (Project.FirstOrderSemantics.reduct M).mem a last ∨ a = last) ∧
    PureKuratowski.PairMember M last base ordSchedule ∧
    (∀ q k, (Project.FirstOrderSemantics.reduct M).mem q Requests → (Project.FirstOrderSemantics.reduct M).mem k K →
      ∃ j, (Project.FirstOrderSemantics.reduct M).mem j last ∧ Product ordPlace q k j ∧
        PureKuratowski.PairMember M j q ordSchedule) ∧
    (∀ q k l j, Product ordPlace q k j → Product ordPlace q l j → k = l) ∧
    (∀ i j q, PureKuratowski.PairMember M i j collapse →
      (PureKuratowski.PairMember M j q ordSchedule ↔ PureKuratowski.PairMember M i q Schedule)) ∧
    ∀ q k i j, Product Place q k i → PureKuratowski.PairMember M i j collapse → Product ordPlace q k j

/-- Consume the accepted actual order type; construct its actual collapse,
inverse, ordinal Schedule, ordinal Place and last stage. No supplied graphs. -/
theorem transport (hM : FirstOrder.Theory.Models M nativeZF)
    {Requests K A I top base Schedule Place r R ordinal : M.Carrier .set}
    (hd : ConstructionScheduleOrder.OrderedData hM Requests K A I top base Schedule Place r R ordinal) :
    ∃ collapse inverse ordSchedule ordPlace last,
      Data hM Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last := by
  let N := Project.FirstOrderSemantics.reduct M
  let J := KuratowskiZF.interpretation hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hd' := hd
  rcases hd' with ⟨hBase,_,hOrder,_,hBefore,_,hAt,hType,hOrdinal,_⟩
  have hBase' := hBase
  rcases hBase' with ⟨_,_,_,hTopI,hSch,_,hPlace,_,hAtTop,_,_,hKInj,_⟩
  obtain ⟨collapse,hCollapse,hRange⟩ := hType
  have hCollapseMap : N.IsSetFunctionFromTo J collapse I ordinal :=
    ⟨hCollapse.1,hCollapse.2.1,fun i hi => by
      obtain ⟨a,ha⟩ := (hCollapse.2.1 i).mp hi
      exact ⟨a,(hRange a).mpr ⟨i,ha⟩,ha⟩⟩
  have hCollapseBij : N.IsSetBijectionFromTo J collapse I ordinal :=
    ⟨⟨hCollapseMap,hCollapse.isSetInjective hZF J hOrder⟩,fun a ha => by
      obtain ⟨i,hi⟩ := (hRange a).mp ha
      exact ⟨i,hCollapseMap.input_mem_of_pairMember hi,hi⟩⟩
  have hIso (i j a b) (hi : PureKuratowski.PairMember M i a collapse)
      (hj : PureKuratowski.PairMember M j b collapse) :
      PureKuratowski.PairMember M i j R ↔ N.mem a b :=
    hCollapse.relation_iff_mem hZF J hOrder hi hj
  obtain ⟨inverse,hInverse,hInv⟩ := ZF.exists_inverseBijectionWithPairs hZF J hCollapseBij
  obtain ⟨ordSchedule,hOrdSch,hSchPairs⟩ := ZF.exists_compositionFunction hZF J hInverse.1.1
    ((ForcingSupportSize.native_mapsTo hM I Requests Schedule).mp hSch)
  have hSchGraph : NodeMap inverse Schedule ordSchedule := by
    intro j q
    change N.PairMember J j q ordSchedule ↔ ∃ i, N.PairMember J j i inverse ∧ N.PairMember J i q Schedule
    rw [hSchPairs j q]
    exact ⟨And.right,fun h => ⟨by obtain ⟨i,hi,_⟩ := h; exact hInverse.1.1.input_mem_of_pairMember hi,h⟩⟩
  obtain ⟨ordPlace,hOrdPlace,hPlacePairs⟩ := ZF.exists_compositionFunction hZF J
    ((ForcingSupportSize.native_mapsTo hM A I Place).mp hPlace.1) hCollapseMap
  have hPlaceGraph : NodeMap Place collapse ordPlace := by
    intro p j
    change N.PairMember J p j ordPlace ↔ ∃ i, N.PairMember J p i Place ∧ N.PairMember J i j collapse
    rw [hPlacePairs p j]
    exact ⟨And.right,fun h => ⟨by obtain ⟨i,hi,_⟩ := h; exact ForcingConditionGraphs.function_input hPlace.1.1 hi,h⟩⟩
  have hOrdPlaceInj : Injection A ordinal ordPlace := by
    refine ⟨(ForcingSupportSize.native_mapsTo hM A ordinal ordPlace).mpr hOrdPlace,?_⟩
    intro p q j hp hq
    obtain ⟨i,hpi,hij⟩ := (hPlaceGraph p j).mp hp
    obtain ⟨i',hqi',hi'j⟩ := (hPlaceGraph q j).mp hq
    have eq := hCollapseBij.1.2 i i' j hij hi'j
    subst i'
    exact hPlace.2 p q i hpi hqi'
  have hValue (i j q) (hi : PureKuratowski.PairMember M i j collapse) :
      PureKuratowski.PairMember M j q ordSchedule ↔ PureKuratowski.PairMember M i q Schedule := by
    rw [hSchGraph j q]
    constructor
    · rintro ⟨i',hi',hq⟩
      have eq := hInverse.1.1.1.2 j i' i hi' ((hInv j i).mpr hi)
      exact eq ▸ hq
    · exact fun hq => ⟨i,(hInv j i).mpr hi,hq⟩
  have hPosition (q k i j) (hpi : Product Place q k i) (hij : PureKuratowski.PairMember M i j collapse) :
      Product ordPlace q k j := by
    obtain ⟨p,hp,hpi⟩ := hpi
    exact ⟨p,hp,(hPlaceGraph p j).mpr ⟨i,hpi,hij⟩⟩
  obtain ⟨last,hLast,hTop⟩ := hCollapseMap.2.2 top hTopI
  have hSuccessor (a) : N.mem a ordinal ↔ N.mem a last ∨ a = last := by
    constructor
    · intro ha
      obtain ⟨i,hi,hca⟩ := hCollapseBij.2 a ha
      by_cases eq : i = top
      · subst i
        exact Or.inr (hCollapseMap.1.2 top a last hca hTop)
      · exact Or.inl ((hIso i top a last hca hTop).mp (hBefore i hi eq))
    · rintro (ha | rfl)
      · exact hOrdinal.transitive last hLast a ha
      · exact hLast
  refine ⟨collapse,inverse,ordSchedule,ordPlace,last,hd,hCollapse,hCollapseBij,hInverse,hInv,hIso,
    (ForcingSupportSize.native_mapsTo hM ordinal Requests ordSchedule).mpr hOrdSch,hSchGraph,
    hOrdPlaceInj,hPlaceGraph,hLast,hTop,hOrdinal.mem hLast,hSuccessor,
    (hValue top last base hTop).mpr hAtTop,?_,?_,hValue,hPosition⟩
  · intro q k hq hk
    obtain ⟨i,hi,hpi,hq',hlt⟩ := hAt q k hq hk
    obtain ⟨j,_,hij⟩ := hCollapseMap.2.2 i hi
    exact ⟨j,(hIso i top j last hij hTop).mp hlt,hPosition q k i j hpi hij,(hValue i j q hij).mpr hq'⟩
  · intro q k l j hk hl
    obtain ⟨p,hp,hpj⟩ := hk
    obtain ⟨p',hp',hp'j⟩ := hl
    have eq := hOrdPlaceInj.2 p p' j hpj hp'j
    subst p'
    exact (PureKuratowski.code_injective hp hp').2

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    (hc : ConstructionDirectedCardinality.Choice (M := M)) {Requests K base : M.Carrier .set}
    (hbase : (Project.FirstOrderSemantics.reduct M).mem base Requests)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K) :
    ∃ A I top Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last,
      Data hM Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last := by
  obtain ⟨A,I,top,Schedule,Place,r,R,ordinal,hd⟩ := ConstructionScheduleOrder.exists_system hM hc hbase hK
  obtain ⟨collapse,inverse,ordSchedule,ordPlace,last,hData⟩ := transport hM hd
  exact ⟨A,I,top,Schedule,Place,r,R,ordinal,collapse,inverse,ordSchedule,ordPlace,last,hData⟩

/-- Original monoid parent inputs produce ALL requests and the ACTUAL ordinal
schedule. No Request set, default, index, collapse, or schedule supplied. -/
theorem exists_all (hM : FirstOrder.Theory.Models M nativeZF)
    (hc : ConstructionDirectedCardinality.Choice (M := M))
    {w D mul e mark zero one K : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D) (hne : mark ≠ e)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K) :
    ∃ Requests node base A I top Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last,
      ConstructionRequestCarrier.Carrier w D mul e zero one Requests ∧ MapsTo w D node ∧
      ConstructionRequestCarrier.ConstantNode w e node ∧ ConstructionProbePath.Path w D mul e zero e node ∧
      ConstructionRequestSchedule.ProbeCode zero e mark node base ∧
      (Project.FirstOrderSemantics.reduct M).mem base Requests ∧ zero ≠ one ∧
      Data hM Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last ∧
      ConstructionRequestSchedule.Requests ordSchedule w D mul e zero one ∧
      (∀ N mulN eN f q qN, (Project.FirstOrderSemantics.reduct M).mem q Requests →
        ConstructionRequestSchedule.Transport w D mul e zero one N mulN eN f q qN →
        ConstructionRequestCarrier.Element w N mulN eN zero one qN) ∧
      ∀ other, ConstructionRequestCarrier.Carrier w D mul e zero one other → other = Requests := by
  obtain ⟨Requests,node,base,hR,hNode,hConst,hPath,hCode,hbase,h01,hLegacy,hTransport,hUnique⟩ :=
    ConstructionRequestCarrier.exists_system hM hw hz hzw hone hm hmark hne
  obtain ⟨A,I,top,Schedule,Place,r,R,ordinal,collapse,inverse,ordSchedule,ordPlace,last,hData⟩ :=
    exists_system hM hc hbase hK
  have hData' := hData
  rcases hData' with ⟨_,_,_,_,_,_,hMaps,_⟩
  exact ⟨Requests,node,base,A,I,top,Schedule,Place,r,R,ordinal,collapse,inverse,ordSchedule,ordPlace,last,
    hR,hNode,hConst,hPath,hCode,hbase,h01,hData,
    fun i q hq => hLegacy q (hMaps.2 i q hq),hTransport,hUnique⟩

end PPAC.Migration.ConstructionOrdinalSchedule
