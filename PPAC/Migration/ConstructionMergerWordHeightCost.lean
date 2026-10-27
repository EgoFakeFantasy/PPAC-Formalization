/- Pinned MergerCones.Word.wordHeightCost:523 and old_cost_supremum:563.
Complete SAME actual weight constructor, full strict missed-cost supremum
and old cost family/cap preservation for ALL old pairs, including empty
or incomparable intervals. No supplied new weight/margin or new backend. -/
import PPAC.Migration.ConstructionMergerWordMargins

namespace PPAC.Migration.ConstructionMergerWordHeightCost
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Cut CutCarrier)
open ConstructionCutAddition (SumCut)
open ConstructionProbeIntervals (Strict)
open ConstructionProbeRaw (Old Cons)
open ConstructionProbeLetterIntervals (UniformMargins MissedBound)
open ConstructionBaseMonoid (Divides)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem exists_heightCost (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D S zero W one u unit H C HD CD e mul A T G Pair unitW : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hW : ConstructionProbeRaw.Carrier w D S W)
    (hH : MapsTo D R H) (hC : MapsTo D R C)
    (hHB : ConstructionCutWeights.RangeBound unit H) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hCopies : ConstructionMergerHeightCost.CopiesHeightCost hM w Q R D S A unit HD CD)
    (hTable : ConstructionMergerWordAction.ActionTable w D S zero mul A T)
    (hMult : ConstructionMergerWordProduct.Laws w D S zero T G)
    (hPair : ConstructionProbeLetters.Representatives W W Pair) (hG : MapsTo Pair W G)
    (hWordM : ForcingDiagramPoset.LeftCancelMonoid W G unitW) (hWordCon : ForcingDiagramPoset.Conical W G unitW)
    (hOldUniform : UniformMargins hM w Q D mul H C)
    (he : (Project.FirstOrderSemantics.reduct M).mem e D) :
    ∃ two three four five six seven eight quarter eighth O V B HL CL, ((
      ConstructionBaseWeights.Digits w one two three ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf four three ∧ (Project.FirstOrderSemantics.reduct M).mem four w ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf five four ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf six five ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf seven six ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf eight seven ∧ (Project.FirstOrderSemantics.reduct M).mem eight w ∧
      ConstructionCutDivision.Value hM w Q four unit quarter ∧ ConstructionCutDivision.Value hM w Q eight unit eighth ∧
      (Project.FirstOrderSemantics.reduct M).mem quarter R ∧ (Project.FirstOrderSemantics.reduct M).mem eighth R ∧
      MapsTo S R O ∧ MapsTo S R V ∧ MapsTo S R B ∧
      ConstructionMergerWordParameters.Graph 0 hM w Q four unit quarter eighth S HD CD O ∧
      ConstructionMergerWordParameters.Graph 1 hM w Q four unit quarter eighth S HD CD V ∧
      ConstructionMergerWordParameters.Graph 2 hM w Q four unit quarter eighth S HD CD B ∧
      (∀ s theta sigma factor, PureKuratowski.PairMember M s theta O →
        PureKuratowski.PairMember M s sigma V → PureKuratowski.PairMember M s factor B →
        ConstructionMergerWordParameters.Recipe hM w Q four unit quarter eighth HD CD s theta sigma factor) ∧
      ConstructionCutWeights.RangeBound unit O ∧
      (∀ s sigma, PureKuratowski.PairMember M s sigma V → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p sigma) ∧
      ConstructionProbeGateCap.Bounds eighth B) ∧
      MapsTo W R HL ∧ ConstructionProbeHeightFold.Laws hM w D S zero W Q H O V HL ∧
      ConstructionMergerWordHeights.LiteralLaws hM w Q D S zero unit H O HL ∧
      ConstructionCutWeights.RangeBound unit HL ∧ MapsTo W R CL ∧
      (∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧ ConstructionMergerWordCosts.Value hM w Q D S zero unit HL C B q y) ∧
      ConstructionProbeGateCap.Bounds unit CL ∧
      (∀ x q y, Old zero D x q → (PureKuratowski.PairMember M q y CL ↔ PureKuratowski.PairMember M x y C)) ∧
      (∀ letter pref q y, Cons w D S letter pref q →
        (PureKuratowski.PairMember M q y CL ↔ ∃ h room factor, PureKuratowski.PairMember M pref h HL ∧
          ConstructionCutDifference.Value hM w Q h unit room ∧ SumCut hM w Q h room unit ∧
          PureKuratowski.PairMember M letter factor B ∧ ConstructionCutProduct.Value hM w Q room factor y))) ∧
      UniformMargins hM w Q W G HL CL ∧
      (∀ x y a b, PureKuratowski.PairMember M x a HL → PureKuratowski.PairMember M y b HL →
        Divides W G x y → ¬ Divides W G y x → ∃ cap total,
        Cut hM w Q cap ∧ ConstructionProbeCostSupremum.Cap W G CL x y cap ∧
        SumCut hM w Q a cap total ∧ Strict total b ∧ MissedBound W G CL x y cap) ∧
      (∀ x y ox oy, Old zero D x ox → Old zero D y oy →
        (∀ cd, ConstructionProbeCostSupremum.CostMember W G CL ox oy cd ↔ ConstructionProbeCostSupremum.CostMember D mul C x y cd) ∧
        (∀ cap, ConstructionProbeCostSupremum.Cap W G CL ox oy cap ↔ ConstructionProbeCostSupremum.Cap D mul C x y cap) ∧
        ∃ cap, Cut hM w Q cap ∧ ConstructionProbeCostSupremum.Cap D mul C x y cap ∧
          ConstructionProbeCostSupremum.Cap W G CL ox oy cap ∧
          ∀ c0 c1, ConstructionProbeCostSupremum.Cap D mul C x y c0 →
            ConstructionProbeCostSupremum.Cap W G CL ox oy c1 → c0 = c1) := by
  obtain ⟨hHD,hCD,hHDB,hCDB,hCopyMargin⟩ := hCopies
  have hLetterUniform : ∀ x y a b, PureKuratowski.PairMember M x a HD → PureKuratowski.PairMember M y b HD →
      ConstructionMergerCopyCones.Reaches D A x y → x ≠ y →
      ConstructionMergerUniformMargin.UniformAt hM w Q D S A CD x y a b := by
    intro x y a b hx hy hxy hne
    obtain ⟨cap,total,hCap,_,hSum,hStrict,hBound⟩ := hCopyMargin x y a b hx hy hxy hne
    exact ⟨cap,total,hCap,hSum,hStrict,hBound⟩
  obtain ⟨two,three,four,five,six,seven,eight,quarter,eighth,O,V,B,HL,CL,hFields⟩ :=
    ConstructionMergerWordCosts.exists_system hM hw hz hzw hQ hR hu hone hunit hW hH hC hHD hCD hHB hCB hHDB hCDB he
  have hRetained := hFields
  obtain ⟨hParameters,hHL,_,hLiteral,hHLB,hCL,hGraph,_,_,_⟩ := hFields
  obtain ⟨hd,hFour,hFourW,_,_,_,_,_,hQuarter,_,_,_,hO,hV,hB,_,_,_,hParams,_,_,_⟩ := hParameters
  have hfp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i four := ⟨three,hFour.predecessor_mem⟩
  have hUniform := ConstructionMergerWordMargins.word_uniform_margin hM hw hz hzw hQ hR hu hunit hFourW hfp hQuarter
    hW hTable hMult hHD hCD hHDB hCDB hO hV hB hParams hHL hHLB hLiteral hGraph hPair hG hWordM hWordCon hOldUniform hLetterUniform
  have hSup : ∀ x y a b, PureKuratowski.PairMember M x a HL → PureKuratowski.PairMember M y b HL →
      Divides W G x y → ¬ Divides W G y x → ∃ cap total,
      Cut hM w Q cap ∧ ConstructionProbeCostSupremum.Cap W G CL x y cap ∧
      SumCut hM w Q a cap total ∧ Strict total b ∧ MissedBound W G CL x y cap := by
    intro x y a b hx hy hxy hnyx
    exact ConstructionProbeCostSupremum.canonical_uniform hM hw hQ hR hCL ((hR a).mp (hHL.2 x a hx))
      (hUniform x y a b hx hy hxy hnyx)
  refine ⟨two,three,four,five,six,seven,eight,quarter,eighth,O,V,B,HL,CL,hRetained,hUniform,hSup,?_⟩
  intro x y ox oy hX hY
  have hCaps (cap : M.Carrier .set) := ConstructionMergerWordMargins.old_cap_iff (cap := cap) hM hw hz hzw hW hPair hG hTable hMult hGraph hX hY
  have hUnit := ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit
  obtain ⟨cap,hCap,hOldCap,hNewCap⟩ := ConstructionMergerWordMargins.exists_old_common_supremum hM hw hz hzw hR hUnit
    hW hPair hG hTable hMult hC hCB hGraph hX hY
  refine ⟨fun cd => ConstructionMergerWordMargins.old_missed_costs_iff hM hw hz hzw hW hPair hG hTable hMult hGraph hX hY,
    hCaps,cap,hCap,hOldCap,hNewCap,?_⟩
  intro c0 c1 hc0 hc1
  exact ConstructionProbeCostSupremum.cap_unique hM hc0 ((hCaps c1).mp hc1)

end PPAC.Migration.ConstructionMergerWordHeightCost
