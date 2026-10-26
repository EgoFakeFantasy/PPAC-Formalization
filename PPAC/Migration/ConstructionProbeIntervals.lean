/- Pinned ProbeMargins.exists_letter_interval: the actual cut arithmetic
construction p=target-floor, K=max p C, delta=(exit-floor-K)/4,
u=floor+2*delta. Only the accepted operations and laws are reused. -/
import PPAC.Migration.ConstructionCutDifferenceSyntax
import PPAC.Migration.ConstructionCutQuarterSum

namespace PPAC.Migration.ConstructionProbeIntervals
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionRealCuts
open ConstructionCutAddition (SumCut AddBound)
open ConstructionCutArithmetic (MaxCut)
open ConstructionBaseWeights (Digits)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

abbrev Strict (a b : M.Carrier .set) : Prop := Subset a b ∧ ¬ Subset b a

theorem le_strict_trans {a b c : M.Carrier .set} (hab : Subset a b) (hbc : Strict b c) : Strict a c :=
  ⟨fun p hp => hbc.1 p (hab p hp),fun h => hbc.2 (fun p hp => hab p (h p hp))⟩

/-- Reassociation of the already defined actual sum relation. -/
theorem reassociate (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c ab bc result : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Cut hM w Q c)
    (hab : SumCut hM w Q a b ab) (hbc : SumCut hM w Q b c bc) :
    SumCut hM w Q ab c result ↔ SumCut hM w Q a bc result := by
  constructor
  · intro hLeft
    obtain ⟨r,_,hRight⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ ha
      (ConstructionCutAssociativity.sum_is_cut hM hw hQ hb hc hbc)
    have he := ConstructionCutAssociativity.cut_assoc hM hw hQ ha hb hc hab hbc hLeft hRight
    exact he.symm ▸ hRight
  · intro hRight
    obtain ⟨l,_,hLeft⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ
      (ConstructionCutAssociativity.sum_is_cut hM hw hQ ha hb hab) hc
    have he := ConstructionCutAssociativity.cut_assoc hM hw hQ ha hb hc hab hbc hLeft hRight
    exact he ▸ hLeft

/-- Adding a nonzero nonnegative cut strictly increases a cut. -/
theorem sum_positive (hM : FirstOrder.Theory.Models M nativeZF) {w Q a d result : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hd : Cut hM w Q d)
    (hNonempty : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p d)
    (hSum : SumCut hM w Q a d result) : Strict a result := by
  obtain ⟨zero,hzero,_⟩ := hw.1.1
  obtain ⟨q,hq,_⟩ := ha.2.2.2
  have hz : Cut hM w Q zero := ⟨fun p hp => (hzero p hp).elim,
    fun _ r hr _ => (hzero r hr).elim,fun p hp => (hzero p hp).elim,q,hq,hzero q⟩
  have hStrict : Strict zero d := by
    refine ⟨fun p hp => (hzero p hp).elim,?_⟩
    intro h
    obtain ⟨p,hp⟩ := hNonempty
    exact hzero p (h p hp)
  exact (ConstructionCutDifference.sum_strict_iff hM hw hQ hz hd ha
    (ConstructionCutArithmetic.sum_zero hzero ha).1 (ConstructionCutArithmetic.sum_comm hM hw hSum)).mpr hStrict

/-- The actual source recipe, retained so that graph construction can use
uniqueness of the selected offset, scale and bound without object Choice. -/
def Recipe (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q four floor target exit c offset delta bound : M.Carrier .set) : Prop :=
  ∃ p room gap double, ConstructionCutDifference.Value hM w Q floor target p ∧
    MaxCut p c bound ∧ ConstructionCutDifference.Value hM w Q floor exit room ∧
    ConstructionCutDifference.Value hM w Q bound room gap ∧
    ConstructionCutDivision.Value hM w Q four gap delta ∧ SumCut hM w Q delta delta double ∧
    SumCut hM w Q floor double offset

theorem recipe_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q four floor target exit c offset delta bound offset' delta' bound' : M.Carrier .set}
    (h : Recipe hM w Q four floor target exit c offset delta bound)
    (h' : Recipe hM w Q four floor target exit c offset' delta' bound') :
    offset = offset' ∧ delta = delta' ∧ bound = bound' := by
  obtain ⟨p,room,gap,double,hP,hMax,hRoom,hGap,hQuarter,hDouble,hOffset⟩ := h
  obtain ⟨p',room',gap',double',hP',hMax',hRoom',hGap',hQuarter',hDouble',hOffset'⟩ := h'
  have heP := ConstructionCutDifference.value_unique hM hP hP'
  subst p'
  have heBound := ConstructionCutArithmetic.max_unique hM hMax hMax'
  subst bound'
  have heRoom := ConstructionCutDifference.value_unique hM hRoom hRoom'
  subst room'
  have heGap := ConstructionCutDifference.value_unique hM hGap hGap'
  subst gap'
  have heDelta := ConstructionCutDivision.value_unique hM hQuarter hQuarter'
  subst delta'
  have heDouble := ConstructionCutAddition.sum_unique hM hDouble hDouble'
  subst double'
  exact ⟨ConstructionCutAddition.sum_unique hM hOffset hOffset',rfl,rfl⟩

/-- The source interval conclusion plus the actual target-floor gap used to
bound all old outside costs. No interval inequalities occur in the premises. -/
def Interval (hM : FirstOrder.Theory.Models M nativeZF) (w Q floor target exit c offset delta bound : M.Carrier .set) : Prop :=
  Cut hM w Q offset ∧ Cut hM w Q delta ∧ Cut hM w Q bound ∧
    (∃ p, (Project.FirstOrderSemantics.reduct M).mem p delta) ∧
    ∃ p lower upperStep upper, Cut hM w Q p ∧ SumCut hM w Q floor p target ∧ Subset p bound ∧ Subset c bound ∧
      SumCut hM w Q floor delta lower ∧ Strict lower offset ∧
      SumCut hM w Q offset delta upperStep ∧ SumCut hM w Q upperStep bound upper ∧ Strict upper exit

/-- Exact source arithmetic, with the source's uniformly strict missed-cost
bound expressed additively. K is the actual maximum and delta the actual /4. -/
theorem exists_interval (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q floor target exit c one two three four tc : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hd : Digits w one two three) (hf : (Project.FirstOrderSemantics.reduct M).SuccessorOf four three)
    (hfw : (Project.FirstOrderSemantics.reduct M).mem four w)
    (hFloor : Cut hM w Q floor) (hTarget : Cut hM w Q target) (hExit : Cut hM w Q exit) (hC : Cut hM w Q c)
    (hFT : Subset floor target) (hTC : SumCut hM w Q target c tc) (hRoom : Strict tc exit) :
    ∃ offset delta bound, Recipe hM w Q four floor target exit c offset delta bound ∧
      Interval hM w Q floor target exit c offset delta bound := by
  have hTargetExit := le_strict_trans (ConstructionCutArithmetic.sum_contains hTarget hC hTC).1 hRoom
  have hFloorExit : Subset floor exit := fun p hp => hTargetExit.1 p (hFT p hp)
  obtain ⟨p,hP,hPValue,hFloorP,_,_⟩ := ConstructionCutDifference.exists_difference hM hw hQ hFloor hTarget hFT
  obtain ⟨room,hRoomCut,hRoomValue,hFloorRoom,_,_⟩ := ConstructionCutDifference.exists_difference hM hw hQ hFloor hExit hFloorExit
  have hPRoom := (ConstructionCutDifference.sum_strict_iff hM hw hQ hP hRoomCut hFloor
    (ConstructionCutArithmetic.sum_comm hM hw hFloorP) (ConstructionCutArithmetic.sum_comm hM hw hFloorRoom)).mp hTargetExit
  obtain ⟨fc,_,hFloorC⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hFloor hC
  have hFCTC := ConstructionCutArithmetic.sum_mono hFloorC hTC hFT (fun _ hp => hp)
  have hFCExit := le_strict_trans hFCTC hRoom
  have hCRoom := (ConstructionCutDifference.sum_strict_iff hM hw hQ hC hRoomCut hFloor
    (ConstructionCutArithmetic.sum_comm hM hw hFloorC) (ConstructionCutArithmetic.sum_comm hM hw hFloorRoom)).mp hFCExit
  obtain ⟨bound,hBound,hMax⟩ := ConstructionCutArithmetic.exists_max hM hw hQ hP hC
  have hMaxLaws := ConstructionCutArithmetic.max_laws hM hw hQ hP hC hMax
  have hBoundRoom := hMaxLaws.2.2.2 room hPRoom.1 hPRoom.2 hCRoom.1 hCRoom.2
  obtain ⟨gap,hGap,hGapValue,hBoundGap,_,hGapPositive⟩ := ConstructionCutDifference.exists_difference hM hw hQ hBound hRoomCut hBoundRoom.1
  obtain ⟨delta,hQuarter⟩ := ConstructionCutDivision.exists_value hM w Q four gap
  have hDelta := ConstructionCutDivision.value_cut hw hQ hfw ⟨three,hf.predecessor_mem⟩ hGap hQuarter
  have hDeltaPositive := (ConstructionCutDivision.nonempty_iff hw hQ hfw ⟨three,hf.predecessor_mem⟩ hGap hQuarter).mpr
    (hGapPositive hBoundRoom.2)
  obtain ⟨double,hDouble,hDD⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hDelta hDelta
  obtain ⟨fourfold,hFourfold,hFour⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hDouble hDouble
  have hFourEq := ConstructionCutQuarterSum.quarter_fourfold hM hw hQ hd hf hfw hGap hDelta hDouble hFourfold hQuarter hDD hFour
  have hDDGap : SumCut hM w Q double double gap := hFourEq ▸ hFour
  have hDeltaDouble := sum_positive hM hw hQ hDelta hDelta hDeltaPositive hDD
  obtain ⟨offset,hOffset,hOffsetSum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hFloor hDouble
  obtain ⟨lower,_,hLower⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hFloor hDelta
  have hLow := (ConstructionCutDifference.sum_strict_iff hM hw hQ hDelta hDouble hFloor
    (ConstructionCutArithmetic.sum_comm hM hw hLower) (ConstructionCutArithmetic.sum_comm hM hw hOffsetSum)).mpr hDeltaDouble
  obtain ⟨triple,hTriple,hDDelta⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hDouble hDelta
  have hTripleGap := (ConstructionCutDifference.sum_strict_iff hM hw hQ hDelta hDouble hDouble
    (ConstructionCutArithmetic.sum_comm hM hw hDDelta) hDDGap).mpr hDeltaDouble
  obtain ⟨upperStep,hUpperStep,hStep⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hOffset hDelta
  have hFloorTriple := (reassociate hM hw hQ hFloor hDouble hDelta hOffsetSum hDDelta).mp hStep
  obtain ⟨tripleBound,hTripleBound,hTripleK⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hTriple hBound
  obtain ⟨upper,_,hUpper⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hUpperStep hBound
  have hFloorTripleBound := (reassociate hM hw hQ hFloor hTriple hBound hFloorTriple hTripleK).mp hUpper
  have hTripleBoundRoom := (ConstructionCutDifference.sum_strict_iff hM hw hQ hTriple hGap hBound
    hTripleK (ConstructionCutArithmetic.sum_comm hM hw hBoundGap)).mpr hTripleGap
  have hUpperExit := (ConstructionCutDifference.sum_strict_iff hM hw hQ hTripleBound hRoomCut hFloor
    (ConstructionCutArithmetic.sum_comm hM hw hFloorTripleBound) (ConstructionCutArithmetic.sum_comm hM hw hFloorRoom)).mpr hTripleBoundRoom
  exact ⟨offset,delta,bound,⟨p,room,gap,double,hPValue,hMax,hRoomValue,hGapValue,hQuarter,hDD,hOffsetSum⟩,
    hOffset,hDelta,hBound,hDeltaPositive,p,lower,upperStep,upper,hP,hFloorP,
    hMaxLaws.1,hMaxLaws.2.1,hLower,hLow,hStep,hUpper,hUpperExit⟩

/-- The source's target-outside additive bound is cancelled against the
actual target-floor gap, then bounded by the constructed maximum. -/
theorem outside_target_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q floor target exit c offset delta bound cost : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hFloor : Cut hM w Q floor) (hCost : Cut hM w Q cost)
    (hInterval : Interval hM w Q floor target exit c offset delta bound)
    (hOutside : AddBound hM w floor cost target) : Subset cost bound := by
  obtain ⟨_,_,_,_,p,_,_,_,hP,hFloorP,hPK,_,_,_,_,_,_⟩ := hInterval
  obtain ⟨sum,_,hSum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hFloor hCost
  have hSumTarget := (ConstructionCutAddition.bound_iff_subset hQ hFloor hCost hSum).mp hOutside
  have hCostP := (ConstructionCutDifference.sum_le_iff hM hw hQ hCost hP hFloor
    (ConstructionCutArithmetic.sum_comm hM hw hSum) (ConstructionCutArithmetic.sum_comm hM hw hFloorP)).mp hSumTarget
  exact fun q hq => hPK q (hCostP q hq)

end PPAC.Migration.ConstructionProbeIntervals
