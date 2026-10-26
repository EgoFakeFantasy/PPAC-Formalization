/- Pinned ProbeMargins.Path.exists_letter_interval on the actual floor,
target, exit and cost graphs. The old source uniform-margin input is retained;
the new interval inequalities and all outside-cost bounds are constructed. -/
import PPAC.Migration.ConstructionProbeIntervals

namespace PPAC.Migration.ConstructionProbeLetterIntervals
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeIntervals
open ConstructionRealCuts
open ConstructionCutAddition (SumCut)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeAlphabet (InCone ExitGraph)
open ConstructionProbeLetterFloor (FloorLaws)
open ConstructionProbeCostBounds (CostBounds)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The source uniformly missed-cost bound, in the accepted additive form. -/
def MissedBound (D mul cost x y bound : M.Carrier .set) : Prop := ∀ d cd,
  (Project.FirstOrderSemantics.reduct M).mem d D → PureKuratowski.PairMember M d cd cost →
    Divides D mul d y → ¬ Divides D mul d x → Subset cd bound

def UniformAt (hM : FirstOrder.Theory.Models M nativeZF) (w Q D mul cost x y hx hy : M.Carrier .set) : Prop :=
  ∃ c tc, Cut hM w Q c ∧ SumCut hM w Q hx c tc ∧ Strict tc hy ∧ MissedBound D mul cost x y c

def UniformMargins (hM : FirstOrder.Theory.Models M nativeZF) (w Q D mul H C : M.Carrier .set) : Prop :=
  ∀ x y hx hy, PureKuratowski.PairMember M x hx H → PureKuratowski.PairMember M y hy H →
    Divides D mul x y → ¬ Divides D mul y x → UniformAt hM w Q D mul C x y hx hy

def OutsideBound (D mul S A cost s exit bound : M.Carrier .set) : Prop := ∀ d cd,
  (Project.FirstOrderSemantics.reduct M).mem d D → PureKuratowski.PairMember M d cd cost →
    Divides D mul d exit → ¬ InCone S A d s → Subset cd bound

/-- Target is strictly below its actual exit, using the original left-cancel
and conical contracts and the same nonunit step parameter. -/
theorem target_strict_exit {D mul e d t exit : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hConical : Conical D mul e)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hne : d ≠ e)
    (ht : (Project.FirstOrderSemantics.reduct M).mem t D) (hExit : Product mul t d exit) :
    Divides D mul t exit ∧ ¬ Divides D mul exit t := by
  refine ⟨⟨d,hd,hExit⟩,?_⟩
  rintro ⟨k,hk,hBack⟩
  obtain ⟨dk,hdk,hProduct⟩ := (hm.2.1 d hd).1 k hk
  have hTdk := (hm.2.2 t d k exit dk t ht hd hk hExit hProduct).mp hBack
  have hUnit := ((hm.1.2 t ht t).2).mpr rfl
  have he := (hm.2.1 t ht).2.2 dk e t hdk hm.1.1 hTdk hUnit
  exact hne (hConical d k hd hk (he ▸ hProduct)).1

/-- Source pointwise interval theorem, on the already constructed path graphs.
No height/cost interval or bound on the new K is retained as an assumption. -/
theorem exists_letter_interval (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul e d S A K E H C F one two three four s floor t exit ht he : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hm : LeftCancelMonoid D mul e) (hConical : Conical D mul e)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hne : d ≠ e)
    (hK : MapsTo S D K) (hE : ExitGraph mul K d E) (hH : MapsTo D R H) (hC : MapsTo D R C) (hF : MapsTo S R F)
    (hFloor : FloorLaws D S A K H F) (hCost : CostBounds hM w Q D mul S A K H C F)
    (hUniform : UniformMargins hM w Q D mul H C)
    (hDigits : ConstructionBaseWeights.Digits w one two three)
    (hFour : (Project.FirstOrderSemantics.reduct M).SuccessorOf four three)
    (hFourW : (Project.FirstOrderSemantics.reduct M).mem four w)
    (hfs : PureKuratowski.PairMember M s floor F) (hkt : PureKuratowski.PairMember M s t K)
    (hexit : PureKuratowski.PairMember M s exit E)
    (hht : PureKuratowski.PairMember M t ht H) (hhe : PureKuratowski.PairMember M exit he H) :
    ∃ c offset delta bound, Recipe hM w Q four floor ht he c offset delta bound ∧
      Interval hM w Q floor ht he c offset delta bound ∧ OutsideBound D mul S A C s exit bound := by
  obtain ⟨t',hkt',hExit⟩ := (hE s exit).mp hexit
  have hEq := ForcingConditionGraphs.function_unique hK.1 hkt' hkt
  subst t'
  have hStrict := target_strict_exit hm hConical hd hne (hK.2 s t hkt) hExit
  obtain ⟨c,tc,hc,hTC,hRoom,hMissed⟩ := hUniform t exit ht he hht hhe hStrict.1 hStrict.2
  have hFloorCut := (hR floor).mp (hF.2 s floor hfs)
  have hTargetCut := (hR ht).mp (hH.2 t ht hht)
  have hExitCut := (hR he).mp (hH.2 exit he hhe)
  have hFloorTarget := (hFloor s floor hfs).2.2 t ht hkt hht
  obtain ⟨offset,delta,bound,hRecipe,hInterval⟩ := exists_interval hM hw hQ hDigits hFour hFourW
    hFloorCut hTargetCut hExitCut hc hFloorTarget hTC hRoom
  refine ⟨c,offset,delta,bound,hRecipe,hInterval,?_⟩
  intro x cx hx hcx hxe hNotCone
  by_cases hxt : Divides D mul x t
  · exact outside_target_bound hM hw hQ hFloorCut ((hR cx).mp (hC.2 x cx hcx)) hInterval
      ((hCost s floor hfs).2 t x ht cx hkt hx hxt hNotCone hht hcx).1
  · have hIntervalCopy := hInterval
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hCbound,_,_,_,_,_⟩ := hIntervalCopy
    exact fun p hp => hCbound p (hMissed x cx hx hcx hxe hxt p hp)

end PPAC.Migration.ConstructionProbeLetterIntervals
