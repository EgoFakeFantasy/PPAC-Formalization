/- Pinned ProbeMargins.Word.uniform_margin_new_old:371.
Reuse the actual generator divisibility, old uniform margin, interval and
old-factor producers. The source witness is max(outsideBound, old remainder). -/
import PPAC.Migration.ConstructionProbeOldNewMargin

namespace PPAC.Migration.ConstructionProbeNewOldMargin
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts ConstructionFractionOrder
open ConstructionCutAddition (SumCut)
open ConstructionCutArithmetic (MaxCut)
open ConstructionProbeIntervals (Strict)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeGates (HeadSome)
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeLetterIntervals (UniformAt UniformMargins MissedBound)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source equality/strict split for the old remainder; equality uses zero. -/
theorem old_remainder_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D mul e zero R H C x y hx hy : M.Carrier .set}
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hCon : ForcingDiagramPoset.Conical D mul e)
    (hH : MapsTo D R H) (hHX : Cut hM w Q hx) (hUniform : UniformMargins hM w Q D mul H C)
    (hxh : PureKuratowski.PairMember M x hx H) (hyh : PureKuratowski.PairMember M y hy H)
    (hxy : Divides D mul x y) :
    ∃ c sum, Cut hM w Q c ∧ SumCut hM w Q hx c sum ∧ Subset sum hy ∧ MissedBound D mul C x y c := by
  by_cases hBack : Divides D mul y x
  · have he := ConstructionProbeGateCap.divides_antisymm hm hCon
      (ForcingConditionGraphs.function_input hH.1 hxh) hxy hBack
    subst y
    have heH := ForcingConditionGraphs.function_unique hH.1 hxh hyh
    subst hy
    obtain ⟨q,hq,_⟩ := hHX.2.2.2
    have hZero : Cut hM w Q zero :=
      ⟨fun p hp => (hz p hp).elim,fun _ p hp _ => (hz p hp).elim,
        fun p hp => (hz p hp).elim,q,hq,hz q⟩
    exact ⟨zero,hx,hZero,(ConstructionCutArithmetic.sum_zero hz hHX).2,
      fun _ h => h,fun _ _ _ _ hdx hn => (hn hdx).elim⟩
  · obtain ⟨c,sum,hC,hSum,hStrict,hMissed⟩ := hUniform x y hx hy hxh hyh hxy hBack
    exact ⟨c,sum,hC,hSum,hStrict.1,hMissed⟩

/-- The two literal max branches retain the source strict height gap. -/
theorem bound_below_old_height (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q hx hy he offset delta product outside c bound step upper oldSum sum : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hHX : Cut hM w Q hx) (hHE : Cut hM w Q he) (hOffset : Cut hM w Q offset)
    (hDelta : Cut hM w Q delta) (hOutside : Cut hM w Q outside) (hC : Cut hM w Q c)
    (hNew : SumCut hM w Q offset product hx) (hProdLe : Subset product delta)
    (hStep : SumCut hM w Q offset delta step) (hUpper : SumCut hM w Q step outside upper)
    (hUpperExit : Strict upper he) (hOldSum : SumCut hM w Q he c oldSum)
    (hOldLe : Subset oldSum hy) (hMax : MaxCut outside c bound)
    (hSum : SumCut hM w Q hx bound sum) : Strict sum hy := by
  have hNewStep := ConstructionCutArithmetic.sum_mono hNew hStep (fun _ h => h) hProdLe
  have hStepCut := ConstructionCutAssociativity.sum_is_cut hM hw hQ hOffset hDelta hStep
  have hNewUpper : Subset hx upper := fun p hp =>
    (ConstructionCutArithmetic.sum_contains hStepCut hOutside hUpper).1 p (hNewStep p hp)
  have hNewExit := ConstructionProbeIntervals.le_strict_trans hNewUpper hUpperExit
  have hExitY : Subset he hy := fun p hp => hOldLe p
    ((ConstructionCutArithmetic.sum_contains hHE hC hOldSum).1 p hp)
  rcases ConstructionCutArithmetic.max_cases hM hw hQ hOutside hC hMax with heMax | heMax
  · subst bound
    have hSumExit := ConstructionProbeIntervals.le_strict_trans
      (ConstructionCutArithmetic.sum_mono hSum hUpper hNewStep (fun _ h => h)) hUpperExit
    exact ⟨fun p hp => hExitY p (hSumExit.1 p hp),
      fun h => hSumExit.2 (fun p hp => h p (hExitY p hp))⟩
  · subst bound
    have hSumOld := (ConstructionCutDifference.sum_strict_iff hM hw hQ hHX hHE hC hSum hOldSum).mpr hNewExit
    exact ⟨fun p hp => hOldLe p (hSumOld.1 p hp),
      fun h => hSumOld.2 (fun p hp => h p (hOldLe p hp))⟩

/-- Source new-to-old strict margin; all structural prerequisites come from
accepted actual source constructors, including the old exit divisibility. -/
theorem uniform_margin_new_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul S A b zero W Emb H C Off V B F K E one u unit four e G unitW I HL LC Cap z s y oy hx hy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : Principal hM w Q u unit)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hCon : ForcingDiagramPoset.Conical D mul e)
    (hAlpha : ConstructionProbeAlphabet.Alphabet D mul e S I A E)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hW : WordCarrier w D S mul A b W)
    (hMult : ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G)
    (hWordUnit : ConstructionProbeRaw.Old zero D e unitW)
    (hEmb : MapsTo D W Emb) (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb)
    (hH : MapsTo D R H) (hC : MapsTo D R C) (hB : MapsTo S R B)
    (hHL : MapsTo W R HL) (hCap : MapsTo W R Cap)
    (hHB : ConstructionCutWeights.RangeBound unit HL)
    (hI : ConstructionProbeHeightIntervalGraphs.Laws hM w Q four D mul S A K E H C F Off V B)
    (hHeight : ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V HL)
    (hCapG : ConstructionProbeGateCap.Graph D W mul G Emb C unit Cap)
    (hLC : ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC)
    (hUniform : UniformMargins hM w Q D mul H C)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hConservative : ConstructionProbeConservative.Conservative D W mul G Emb)
    (hzW : (Project.FirstOrderSemantics.reduct M).mem z W) (hHead : HeadSome w D S z s)
    (hyo : PureKuratowski.PairMember M y oy Emb) (hzy : Divides W G z oy)
    (hxh : PureKuratowski.PairMember M z hx HL) (hyh : PureKuratowski.PairMember M oy hy HL) :
    UniformAt hM w Q W G LC z oy hx hy := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hWordUnit hMult
  have hEmbed := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hm hAlpha hW hb hWordUnit hMult hOld
  have hDiv := ConstructionProbeOldCostFactors.reflection_of_embedding hEmbed
  have hGates := ConstructionPersistentProfiles.probe_has_old_gates hM hw hz hzw hm hAlpha hW hb hMult hWordUnit hOld hJoins hConservative
  obtain ⟨tail,hCons⟩ := hHead
  have hs := ConstructionProbeRawAction.cons_letter hCons
  obtain ⟨v,htv,offset,delta,product,hOffset,hDelta,hProduct,hXSum⟩ :=
    (hHeight.2 s tail z hx hCons hzW).mp hxh
  obtain ⟨outside,hOutside,_⟩ := hB.1.2 s hs
  obtain ⟨_,_,exit,_,he,_,hCtx,_,hInterval,hOutsideBound⟩ := hI s offset delta outside hOffset hDelta hOutside
  obtain ⟨hOffsetCut,hDeltaCut,hOutsideCut,_,_,_,step,upper,_,_,_,_,_,_,hStep,hUpper,hUpperExit⟩ := hInterval
  have hHEEdge := hCtx.2.2.2.2.1
  have hHE := (hR he).mp (hH.2 exit he hHEEdge)
  have hOldY := (hOld y oy).mp hyo
  have hHYEdge := (hHeight.1 y oy hy hOldY).mp hyh
  obtain ⟨Gen,hGen,hGenGraph⟩ := ConstructionProbeGenerator.exists_generator_graph hM hw hz hzw hCon hW hb hne hWordUnit
  obtain ⟨gen,hgen,_⟩ := hGen.1.2 s hs
  have hGenCons := (hGenGraph s gen).mp hgen
  have hGenW := hGen.2 s gen hgen
  have hGenZ := ConstructionProbeProfiles.generator_dvd_of_head hM hw hz hzw hm hAlpha hW hb hMult hWordUnit hGenCons hGenW hzW ⟨tail,hCons⟩
  have hExitY := (ConstructionProbeGenerator.generator_dvd_old_iff hM hw hz hzw hm hAlpha hW hb hWordUnit hMult hGenCons hGenW hCtx.2.2.1 hOldY).mp
    (ConstructionProbeGates.divides_trans hmW hGenW hGenZ hzy)
  obtain ⟨c,oldSum,hCCut,hOldSum,hOldLe,hMissedOld⟩ :=
    old_remainder_bound hM hz hm hCon hH hHE hUniform hHEEdge hHYEdge hExitY
  obtain ⟨bound,hBound,hMax⟩ := ConstructionCutArithmetic.exists_max hM hw hQ hOutsideCut hCCut
  have hHX := (hR hx).mp (hHL.2 z hx hxh)
  obtain ⟨sum,_,hSum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hHX hBound
  have hProdLe := ConstructionCutProductUnit.bounded_right hM hw hQ hu hone hunit hDeltaCut hProduct (hHB tail v htv).2.1
  have hStrict := bound_below_old_height hM hw hQ hHX hHE hOffsetCut hDeltaCut hOutsideCut hCCut
    hXSum hProdLe hStep hUpper hUpperExit hOldSum hOldLe hMax hSum
  refine ⟨bound,sum,hBound,hSum,hStrict,?_⟩
  intro q cq hq hqc hqy hqz
  obtain ⟨g,og,cg,hgo,hgc,hMin,hqg,hgy,hCost⟩ :=
    ConstructionProbeOldCostFactors.cost_old_factor hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hLC hDiv hGates hq hyo hqy hqc
  have hNotCone : ¬ ConstructionProbeAlphabet.InCone S A g s := by
    intro hCone
    have hgz := (hEmbed.2.2.2.2 g og z hgo hzW).mpr
      ((ConstructionProbeGates.headDiv_of_head_eq_some hM hw hz ⟨tail,hCons⟩).mpr hCone)
    exact hqz (ConstructionProbeGates.divides_trans hmW hq hqg hgz)
  by_cases hgExit : Divides D mul g exit
  · have hLe := hOutsideBound g cg hMin.1 hgc hgExit hNotCone
    exact fun p hp => (hMax p).mpr (Or.inl (hLe p (hCost p hp)))
  · have hLe := hMissedOld g cg hMin.1 hgc hgy hgExit
    exact fun p hp => (hMax p).mpr (Or.inr (hLe p (hCost p hp)))

end PPAC.Migration.ConstructionProbeNewOldMargin
