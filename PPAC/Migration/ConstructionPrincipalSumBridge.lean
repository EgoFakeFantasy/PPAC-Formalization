/- Adapt the already proved Base margin from PrincipalAdd to the actual
SumCut used by probe heightIntervals. No Base estimate is reproved. -/
import PPAC.Migration.ConstructionCutDifference

namespace PPAC.Migration.ConstructionPrincipalSumBridge
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionFractionAddition (Sum)
open ConstructionPrincipalAddition (PrincipalAdd)
open ConstructionCutAddition (SumCut)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Existing principal addition and the current general cut addition have
exactly the same value, including zero and equivalent fraction codes. -/
theorem principal_sum (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hAdd : PrincipalAdd hM w Q a b c) : SumCut hM w Q a b c := by
  classical
  have hBound := ConstructionBasePointBound.principal_add_bound hM hw hQ hAdd
  obtain ⟨q,r,s,hqQ,hrQ,hA,hB,hSum,hC⟩ := hAdd
  have hq := (hQ q).mp hqQ
  have hr := (hQ r).mp hrQ
  have ha := principal_cut hM hw hQ hqQ hA
  intro p
  constructor
  · intro hpc
    obtain ⟨hpQ,hps⟩ := (hC p).mp hpc
    have hp := (hQ p).mp hpQ
    refine ⟨hpQ,?_⟩
    by_cases hrp : Le hM w r p
    · obtain ⟨g,t,hg,hGap,htp,hpt⟩ := ConstructionFractionDifference.difference_exists hM hw hrp
      have hts := le_lt_trans hM hw htp hps
      have hgq := (ConstructionFractionAddition.sum_right_lt_iff hM hw
        (ConstructionFractionAddition.sum_comm hM hw hGap) hSum).mp hts
      obtain ⟨u,hu,hgu,huq⟩ := dense hM hw hgq
      have hua := (hA u).mpr ⟨(hQ u).mpr hu,huq⟩
      obtain ⟨ur,hUR⟩ := ConstructionFractionAddition.sum_exists hM hw hu hr
      have htUR := (ConstructionFractionAddition.sum_right_lt_iff hM hw
        (ConstructionFractionAddition.sum_comm hM hw hGap) hUR).mpr hgu
      have hpUR := le_lt_trans hM hw hpt htUR
      by_cases hup : Le hM w u p
      · obtain ⟨v,pv,hv,hPV,hpvP,hPpv⟩ := ConstructionFractionDifference.difference_exists hM hw hup
        have hpvUR := le_lt_trans hM hw hpvP hpUR
        have hvr := (ConstructionFractionAddition.sum_right_lt_iff hM hw
          (ConstructionFractionAddition.sum_comm hM hw hPV)
          (ConstructionFractionAddition.sum_comm hM hw hUR)).mp hpvUR
        obtain ⟨v',hv',hvv',hvr'⟩ := dense hM hw hvr
        have hvb := (hB v').mpr ⟨(hQ v').mpr hv',hvr'⟩
        obtain ⟨out,hOut⟩ := ConstructionFractionAddition.sum_exists hM hw hu hv'
        have hpvOut := (ConstructionFractionAddition.sum_right_lt_iff hM hw
          (ConstructionFractionAddition.sum_comm hM hw hPV)
          (ConstructionFractionAddition.sum_comm hM hw hOut)).mpr hvv'
        exact Or.inr (Or.inr ⟨u,v',out,hua,hvb,hOut,le_trans hM hw hPpv hpvOut.1⟩)
      · have hpu := (le_total hM hw hp hu).resolve_right hup
        exact Or.inl (ha.2.1 p u hua hpu)
    · have hpr := (le_total hM hw hp hr).resolve_right hrp
      exact Or.inr (Or.inl ((hB p).mpr ⟨hpQ,hpr,hrp⟩))
  · exact fun hp => hBound p hp.2

end PPAC.Migration.ConstructionPrincipalSumBridge
