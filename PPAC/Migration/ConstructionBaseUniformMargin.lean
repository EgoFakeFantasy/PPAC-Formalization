/- Reuse the completed source Base margin on actual mapped weight graphs.
Only representation/derivation adapters are added: PrincipalAdd -> SumCut,
ordinal natural order -> original monoid Divides, and retained MapsTo. -/
import PPAC.Migration.ConstructionPrincipalSumBridge
import PPAC.Migration.ConstructionProbeLetterIntervals

namespace PPAC.Migration.ConstructionBaseUniformMargin
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionRealCuts
open ConstructionBaseWeights (Digits)
open ConstructionBaseMonoid (AdditionGraph Divides)
open ConstructionProbeLetterIntervals (UniformMargins)
open ConstructionProbeLetterFloor (HeightOrder)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The source full supremum margin already proved for Base supplies the
current probe UniformMargins input on the very same height/cost graphs. -/
theorem base_uniform (hM : FirstOrder.Theory.Models M nativeZF)
    {w mul one two three Q R H C : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R) (hMul : AdditionGraph hM w mul)
    (hH : ConstructionCutWeights.Graph hM true w one two one Q H)
    (hC : ConstructionCutWeights.Graph hM false w one two three Q C) (hHM : MapsTo w R H) :
    UniformMargins hM w Q w mul H C := by
  intro x y hx hy hxh hyh hxy hNot
  have hxw := ((hH x hx).mp hxh).1
  have hyw := ((hH y hy).mp hyh).1
  have hxyNat : (Project.FirstOrderSemantics.reduct M).mem x y := by
    rcases (ConstructionBaseMonoid.le_iff hM hw hMul hxw hyw).mp hxy with he | hxyNat
    · subst y
      exact (hNot hxy).elim
    · exact hxyNat
  obtain ⟨cx,hxc⟩ := ConstructionBasePointBound.cost_value_exists hM hw hd hC hxw
  obtain ⟨gap,family,s,hGap,hAdd,hFamily,_,hS,hu,_,hSGap,hNotGapS⟩ :=
    ConstructionBaseHeightGap.source_margin hM hw hd hQ hH hC hxh hyh hxc hxyNat
  have hActual := ConstructionPrincipalSumBridge.principal_sum hM hw hQ hAdd
  obtain ⟨q,hq,hPrincipal⟩ := hGap
  have hGapCut := principal_cut hM hw hQ hq hPrincipal
  have hHX := (hR hx).mp (hHM.2 x hx hxh)
  obtain ⟨sum,_,hSum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hHX hS
  have hStrict := (ConstructionCutDifference.sum_strict_iff hM hw hQ hS hGapCut hHX
    (ConstructionCutArithmetic.sum_comm hM hw hSum) (ConstructionCutArithmetic.sum_comm hM hw hActual)).mpr ⟨hSGap,hNotGapS⟩
  refine ⟨s,sum,hS,hSum,hStrict,?_⟩
  intro d cd hdw hdc hdy hdx
  have hdyNat := (ConstructionBaseMonoid.le_iff hM hw hMul hdw hyw).mp hdy
  have hdxNat : ¬ NatLe d x := fun h => hdx ((ConstructionBaseMonoid.le_iff hM hw hMul hdw hxw).mpr h)
  exact hu cd ((hFamily cd).mpr ⟨d,hdc,hdyNat,hdxNat⟩)

/-- The old height-order input is also discharged using existing bounds and
height_mono; it is not an additional assumption of the new Base constructor. -/
theorem base_height_order (hM : FirstOrder.Theory.Models M nativeZF)
    {w mul one two three Q R H unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q) (hMul : AdditionGraph hM w mul)
    (hH : ConstructionCutWeights.Graph hM true w one two one Q H) (hHM : MapsTo w R H)
    (hBound : ConstructionCutWeights.RangeBound unit H) : HeightOrder w mul R H := by
  refine ⟨hHM,fun x c h => (hBound x c h).1,?_⟩
  intro x y c d hxc hyd hxy
  obtain ⟨hx,q,hq,hp⟩ := (hH x c).mp hxc
  obtain ⟨hy,r,hr,hp'⟩ := (hH y d).mp hyd
  have hxyNat := (ConstructionBaseMonoid.le_iff hM hw hMul hx hy).mp hxy
  have hOneNE : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z one := by
    obtain ⟨z,_,hs⟩ := hd.2.2.2.1
    exact ⟨z,hs.predecessor_mem⟩
  have proper := fun n q hn hq => ConstructionBaseWeights.weight_proper hM (height := true) hw
    hd.2.2.2.1 hd.2.1 hd.2.2.2.2.1.predecessor_mem hd.1 hOneNE (n := n) (q := q) hn hq
  have hqQ := ConstructionFractionOrder.proper_in_carrier hQ (proper x q hx hq)
  have hrQ := ConstructionFractionOrder.proper_in_carrier hQ (proper y r hy hr)
  exact (principal_subset_iff hM hw hQ hqQ hrQ hp hp').mpr
    (ConstructionBaseHeightGap.height_mono hM hw hd hx hy hxyNat hq hr)

def Data (hM : FirstOrder.Theory.Models M nativeZF)
    (w mul zero one two three Q R H C unitCode unit : M.Carrier .set) : Prop :=
  AdditionGraph hM w mul ∧ (∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero) ∧
    ForcingDiagramPoset.LeftCancelMonoid w mul zero ∧ ForcingDiagramPoset.Conical w mul zero ∧
    one ≠ zero ∧ ConstructionBaseMonoid.Joins w mul ∧ Digits w one two three ∧ Carrier w Q ∧ CutCarrier hM w Q R ∧
    ConstructionCutWeights.Graph hM true w one two one Q H ∧ ConstructionCutWeights.Graph hM false w one two three Q C ∧
    MapsTo w R H ∧ MapsTo w R C ∧ Coordinates w unitCode one one ∧ Principal hM w Q unitCode unit ∧
    (Project.FirstOrderSemantics.reduct M).mem unit R ∧ ConstructionCutWeights.RangeBound unit H ∧
    ConstructionCutWeights.RangeBound unit C ∧ HeightOrder w mul R H ∧
    ConstructionProbeCostBounds.PointBound hM w w mul H C ∧
    (∀ x y qx qy cx, PureKuratowski.PairMember M x qx H → PureKuratowski.PairMember M y qy H →
      PureKuratowski.PairMember M x cx C → (Project.FirstOrderSemantics.reduct M).mem x y →
      ConstructionBaseHeightGap.MarginAt hM w Q C x y qx qy) ∧ UniformMargins hM w Q w mul H C

/-- Actual Base data: the completed full margin is retained, and both old
probe order/margin inputs are now conclusions rather than assumptions. -/
theorem exists_base (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ mul zero one two three Q R H C unitCode unit, Data hM w mul zero one two three Q R H C unitCode unit := by
  obtain ⟨mul,hMul⟩ := ConstructionBaseMonoid.exists_additionGraph hM hw
  obtain ⟨zero,hZero,hZeroW⟩ := hw.1.1
  obtain ⟨one,two,three,hd⟩ := ConstructionBaseWeights.digits_exists hw
  obtain ⟨Q,hQ⟩ := ConstructionFractionOrder.exists_carrier hM w
  obtain ⟨R,hR⟩ := exists_cutCarrier hM w Q
  have hOneNE : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z one := by
    obtain ⟨z,_,hs⟩ := hd.2.2.2.1
    exact ⟨z,hs.predecessor_mem⟩
  have hTwoNE : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z two := ⟨one,hd.2.2.2.2.1.predecessor_mem⟩
  have hThreeNE : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z three := ⟨two,hd.2.2.2.2.2.predecessor_mem⟩
  obtain ⟨H,hHM,hH,_⟩ := ConstructionCutWeights.exists_graph_with_map hM true hw hd.1 hd.2.1 hTwoNE hd.1 hQ hR (by
    intro n q hn hq
    exact ConstructionFractionOrder.proper_in_carrier hQ (ConstructionBaseWeights.weight_proper hM hw
      hd.2.2.2.1 hd.2.1 hd.2.2.2.2.1.predecessor_mem hd.1 hOneNE hn hq))
  obtain ⟨C,hCM,hC,_⟩ := ConstructionCutWeights.exists_graph_with_map hM false hw hd.1 hd.2.1 hTwoNE hd.2.2.1 hQ hR (by
    intro n q hn hq
    exact ConstructionFractionOrder.proper_in_carrier hQ (ConstructionBaseWeights.weight_proper hM hw
      hd.2.2.2.1 hd.2.1 hd.2.2.2.2.1.predecessor_mem hd.2.2.1 hThreeNE hn hq))
  obtain ⟨unitCode,hUnitCode⟩ := KuratowskiZF.exists_code hM one one
  have hUnitCoord : Coordinates w unitCode one one := ⟨hd.1,hd.1,hOneNE,hUnitCode⟩
  obtain ⟨unit,hUnit⟩ := exists_principal hM w Q unitCode
  have hUnitR := (hR unit).mpr (principal_cut hM hw hQ ((hQ unitCode).mpr ⟨one,one,hUnitCoord⟩) hUnit)
  obtain ⟨hHB,hCB⟩ := ConstructionCutWeights.weights_bounded hM hw hd hQ hUnitCoord hUnit hH hC
  have hNE : one ≠ zero := by
    intro he
    obtain ⟨z,hz⟩ := hOneNE
    exact hZero z (he ▸ hz)
  exact ⟨mul,zero,one,two,three,Q,R,H,C,unitCode,unit,hMul,hZero,
    ConstructionBaseMonoid.leftCancelMonoid hM hw hMul hZero hZeroW,ConstructionBaseMonoid.conical hM hw hMul hZero,
    hNE,ConstructionBaseMonoid.joins hM hw hMul,hd,hQ,hR,hH,hC,hHM,hCM,hUnitCoord,hUnit,hUnitR,hHB,hCB,
    base_height_order hM hw hd hQ hMul hH hHM hHB,ConstructionBasePointBound.base_point_bound hM hw hd hQ hMul hH hC,
    (fun _ _ _ _ _ hxh hyh hxc hxy => ConstructionBaseHeightGap.source_margin hM hw hd hQ hH hC hxh hyh hxc hxy),
    base_uniform hM hw hd hQ hR hMul hH hC hHM⟩

end PPAC.Migration.ConstructionBaseUniformMargin
