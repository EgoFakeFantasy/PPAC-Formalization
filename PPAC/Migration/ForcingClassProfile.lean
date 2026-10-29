/- Pinned ClassFibers.classFromLocal_profile. The positive direction retains
one actual eligible class along the SAME map family; the negative direction
uses the existing full local-name support descent and actual OutsideLocal exclusion. -/
import PPAC.Migration.ForcingOutsideLocal
import PPAC.Migration.ForcingSystemAvailability

namespace PPAC.Migration.ForcingClassProfile
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingPowerName (trueTest)
open ForcingEligibleFamily (Data)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Sub Product Le)
open ForcingSupportedNames (Range)
open ForcingSupportSize (Small)
open ForcingProductFamily (Presentation)
open ForcingLocalAtomic (EqG)
open ForcingSupportingRoot (Code exists_code)
open ConstructionBaseMonoid (Divides)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The exact divisor profile and off-profile common-cone equation from source. -/
def Geometry (D mul a m t U : M.Carrier .set) : Prop :=
  (∀ n, (Project.FirstOrderSemantics.reduct M).mem n U ↔
    (Project.FirstOrderSemantics.reduct M).mem n D ∧ Divides D mul n a ∧ Divides D mul n m) ∧
  ∀ n, (Project.FirstOrderSemantics.reduct M).mem n D → Divides D mul n a →
    ¬ (Project.FirstOrderSemantics.reduct M).mem n U → ConstructionDiagramPlacements.ConeEquality D mul n m t

/-- Construct the actual source classFromLocal at a diagram below q.
The source diagram s itself need not lie below q. -/
theorem classFromLocal (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w one g q bound labels E s r As Hs XS QS ps OS Ar Hr XR QR pr OR sigma : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hs : Injection (env (rho 0)) I s) (hr : Injection (env (rho 0)) I r)
    (hrs : Le (env (rho 0)) (env mul) r s) (hrq : Le (env (rho 0)) (env mul) r q)
    (hDS : Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g q bound labels E s As Hs XS QS ps OS)
    (hDR : Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g q bound labels E r Ar Hr XR QR pr OR)
    (hn : ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) bound Hs sigma)
    (hel : ForcingEligibility.EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g s labels E sigma) :
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x OR ∧ PureKuratowski.PairMember M sigma x pr := by
  have hIncl : ForcingPowerName.Subset As Ar := fun j hj =>
    (hDR.1 j).mpr (ConstructionDescentPlacement.range_antitone hrs ((hDS.1 j).mp hj))
  have hnR := ForcingLocalNames.restrict_name hDS.2.1 hDR.2.1 hIncl hDS.2.2.1 hDR.2.2.1 sigma ((hDS.2.2.1 sigma).mpr hn)
  obtain ⟨x,hx,_⟩ := hDR.2.2.2.1.1.2 sigma hnR
  have helR := ForcingEligibility.eligibleName_restrict hM env rho G F mul hm hp hg hs hr hrs hel
  exact ⟨x,(hDR.2.2.2.2.2.2 x).mpr ⟨hDR.2.2.2.1.2 sigma x hx,hrq,sigma,hx,helR⟩,hx⟩

/-- Actual restriction edge from two projections of the SAME raw name. -/
theorem map_of_same_name (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G F mul g q bound labels E diagrams objects S maps s r OS OR
      As Hs XS QS ps Ar Hr XR QR pr sigma x y z a : M.Carrier .set}
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q bound labels E diagrams objects)
    (hMaps : ForcingEligibleMapFamily.Family R Hdom env v G F mul g q bound labels E S maps)
    (hs : PureKuratowski.PairMember M s OS objects) (hr : PureKuratowski.PairMember M r OR objects)
    (hDS : Data R Hdom env v G F mul g q bound labels E s As Hs XS QS ps OS)
    (hDR : Data R Hdom env v G F mul g q bound labels E r Ar Hr XR QR pr OR)
    (hz : PureKuratowski.Code M z s r) (ha : PureKuratowski.PairMember M z a maps)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x OS)
    (hpx : PureKuratowski.PairMember M sigma x ps) (hpy : PureKuratowski.PairMember M sigma y pr) :
    PureKuratowski.PairMember M x y a := by
  obtain ⟨As',Hs',XS',QS',ps',Ar',Hr',XR',QR',pr',f,hDS',hDR',_,hf,_,hRestr⟩ :=
    ForcingEligibleSystem.map_data hM hObj hMaps hs hr hz ha
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDS hDS'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDR hDR'
  exact (hRestr x y).mpr ⟨(hf x y).mpr ⟨sigma,hpx,hpy⟩,hx⟩

theorem outside_not_eqG_common (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s0 s1 v
      A0 A1 Ap fixing0 fixing1 fixingP g outsideD outsideZ XP ordinal enum list sigma0 sigma1 c t b labels nameBound : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hFilter : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hp : Injection (env (rho 0)) I p) (hs0 : Injection (env (rho 0)) I s0)
    (hs1 : Injection (env (rho 0)) I s1) (hv : Injection (env (rho 0)) I v)
    (hs0p : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s0 p)
    (hs1p : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s1 p)
    (hInter : ConstructionDiagramPlacements.RangeIntersection (env (rho 0)) s0 s1 p)
    (hv0 : ForcingDiagramOrder.Le (env (rho 0)) (env mul) v s0)
    (hv1 : ForcingDiagramOrder.Le (env (rho 0)) (env mul) v s1)
    (hRange0 : Range (env (rho 0)) s0 A0) (hRange1 : Range (env (rho 0)) s1 A1)
    (hRangeP : Range (env (rho 0)) p Ap)
    (hFix0 : ForcingLabelPermutations.Fixing (env G) A0 fixing0)
    (hFix1 : ForcingLabelPermutations.Fixing (env G) A1 fixing1)
    (hFixP : ForcingLabelPermutations.Fixing (env G) Ap fixingP)
    (hn0 : ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F) nameBound fixing0 sigma0)
    (hn1 : ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F) nameBound fixing1 sigma1)
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b labels)
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) I K c t b nameBound)
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hXP : ForcingLocalNames.Carrier (fun i => env (rho i)) (env G) (env F) nameBound fixingP XP)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal XP)
    (hList : ForcingCollectedName.Collected trueTest Fin.elim0 ordinal enum (env (rho 6)) list)
    (hdOut : (Project.FirstOrderSemantics.reduct M).mem outsideD g) (hzOut : Code outsideZ outsideD s0)
    (hout : ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) outsideZ sigma0 list) :
    ¬ EqG (orderFormula (rho 0) mul) env (env (rho 6)) g v sigma0 sigma1 := by
  rintro ⟨d,z,hdg,hz,heq⟩
  have hd := (hpres.2.2.1 d).mp (hg.1 d hdg)
  obtain ⟨d0,hd0,hRestr0,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hd A0
  obtain ⟨d1,_,hRestr1,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hd A1
  obtain ⟨z0,hz0⟩ := exists_code hM d0 s0
  obtain ⟨z1,hz1⟩ := exists_code hM d1 s1
  obtain ⟨name,hn,he0,_⟩ := ForcingLocalNameDescent.localName_descent hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1
    hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hn0 hn1 hd hRestr0 hRestr1 hz hz0 hz1 heq hc ht hLabels hBound
  have hd0g := hg.2.2.1 d d0 hdg ((hpres.2.2.1 d0).mpr hd0) (fun t ht => ((hRestr0 t).mp ht).1)
  exact ForcingOutsideLocal.not_eqG hM env rho mul hm hpres hg hs0 hdOut hzOut hXP hEnum hList hn hout ⟨d0,z0,hd0g,hz0,he0⟩

theorem classFromLocal_profile (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa one mark H C incoming base I K B c top bit labels bound g q E oi objects S mi maps
      r p sm Or OP Om Ap Hp XP QP prP Am Hm XM QM prM Ar Hr XR QR prR ordinal enum list d z sigma xr a e m b t U : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) one mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty top)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c top bit labels)
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) I K c top bit bound)
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hObj : MapsTo (env (rho 4)) oi objects)
    (hObjFamily : ForcingEligibleFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E (env (rho 4)) objects)
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env (rho 4)) S)
    (hMaps : MapsTo S mi maps)
    (hMapFamily : ForcingEligibleMapFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E S maps)
    (hSys : ForcingEligibleSystem.System (env (rho 0)) objects maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hP : PureKuratowski.PairMember M p OP objects)
    (hSm : PureKuratowski.PairMember M sm Om objects)
    (hDP : Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g q bound labels E p Ap Hp XP QP prP OP)
    (hDM : Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g q bound labels E sm Am Hm XM QM prM Om)
    (hDR : Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g q bound labels E r Ar Hr XR QR prR Or)
    (hq : Injection (env (rho 0)) I q)
    (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 0)))
    (hmD : (Project.FirstOrderSemantics.reduct M).mem m (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem b (env (rho 0)))
    (hae : Product (env mul) a e t) (hmb : Product (env mul) m b t)
    (hSuba : Sub (env (rho 0)) (env mul) r a q)
    (hSubm : Sub (env (rho 0)) (env mul) r m sm) (hSubp : Sub (env (rho 0)) (env mul) r t p)
    (hn : ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) bound Hm sigma)
    (hel : ForcingEligibility.EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g sm labels E sigma)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal XP)
    (hList : ForcingCollectedName.Collected trueTest Fin.elim0 ordinal enum (env (rho 6)) list)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d g) (hz : Code z d sm)
    (hout : ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) z sigma list)
    (hGeom : Geometry (env (rho 0)) (env mul) a m t U)
    (hxr : PureKuratowski.PairMember M sigma xr prR) :
    ForcingSystemAvailability.Carrier (env (rho 0)) (env mul) objects maps r xr a U := by
  have hDiagrams := hp.2.2.2.1
  have hrI := (hDiagrams r).mp (ForcingConditionGraphs.function_input hObj.1 hr)
  have hpI := (hDiagrams p).mp (ForcingConditionGraphs.function_input hObj.1 hP)
  have hmI := (hDiagrams sm).mp (ForcingConditionGraphs.function_input hObj.1 hSm)
  have hrm : Le (env (rho 0)) (env mul) r sm := ⟨m,hmD,hSubm⟩
  intro n
  constructor
  · intro hnU
    obtain ⟨hnD,hna,hnm⟩ := (hGeom.1 n).mp hnU
    obtain ⟨sn,hnI,hSubn⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 n hnD) hrI
    obtain ⟨On,hOn,_⟩ := hObj.1.2 sn ((hDiagrams sn).mpr hnI)
    obtain ⟨An,Hn,XN,QN,prN,hDN⟩ := ((hObjFamily sn On).mp hOn).2
    have hnmLe := ForcingSystemAvailability.sub_mono hM hm hnI hmI hnD hnm hSubn hSubm
    have hnq := ForcingSystemAvailability.sub_mono hM hm hnI hq hnD hna hSubn hSuba
    obtain ⟨yn,hyn,hypr⟩ := classFromLocal hM env rho G F mul hm hp hg hmI hnI hnmLe hnq hDM hDN hn hel
    obtain ⟨zn,fn,hzn,hfn,_⟩ := ForcingSystemAvailability.exists_map hM hObj hArrows hMaps hSys hr hOn ⟨n,hnD,hSubn⟩
    have heyn := map_of_same_name hM hObjFamily hMapFamily hOn hr hDN hDR hzn hfn hyn hypr hxr
    exact ⟨hnD,hna,sn,On,zn,fn,yn,hSubn,hOn,hzn,hfn,hyn,heyn⟩
  · rintro ⟨hnD,hna,hAvail⟩
    apply Classical.byContradiction
    intro hnU
    obtain ⟨sn,On,zn,fn,yn,hSubn,hOn,hzn,hfn,hyn,heyn⟩ := hAvail
    have hnI := (hDiagrams sn).mp (ForcingConditionGraphs.function_input hObj.1 hOn)
    obtain ⟨An,Hn,XN,QN,prN,Ar',Hr',XR',QR',prR',f,hDN,hDR',_,hf,_,hRestr⟩ :=
      ForcingEligibleSystem.map_data hM hObjFamily hMapFamily hOn hr hzn hfn
    obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDR hDR'
    obtain ⟨tau,htauN,htauR⟩ := (hf yn xr).mp ((hRestr yn xr).mp heyn).1
    have hnTau := (hDN.2.2.1 tau).mp ((hDN.2.2.2.2.2.1 tau yn).mp htauN).1
    have hEq := (ForcingLocalQuotient.equality_law hM env rho mul hm hp hg hrI hDR.2.2.2.2.2.1 sigma tau xr xr hxr htauR).mp rfl
    have hmp := ForcingSystemAvailability.sub_mono hM hm hmI hpI hmD ⟨b,hb,hmb⟩ hSubm hSubp
    have hnp := ForcingSystemAvailability.sub_mono hM hm hnI hpI hnD
      (ConstructionProbeGates.divides_trans hm hnD hna ⟨e,he,hae⟩) hSubn hSubp
    have hInter := ConstructionDiagramPlacements.range_inter_sub hrI hSubm hSubn hSubp
      (fun v hv => and_comm.trans (hGeom.2 n hnD hna hnU v hv))
    exact outside_not_eqG_common hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hp hG hF
      hpI hmI hnI hrI hmp hnp hInter hrm ⟨n,hnD,hSubn⟩ hDM.1 hDN.1 hDP.1 hDM.2.1 hDN.2.1 hDP.2.1 hn hnTau
      hc ht hLabels hBound hg hDP.2.2.1 hEnum hList hd hz hout hEq

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa one mark H C incoming base I K B c top bit labels bound g q E oi objects S mi maps
      r p sm Or OP Om Ap Hp XP QP prP Am Hm XM QM prM Ar Hr XR QR prR ordinal enum list d z sigma a e m b t U : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) one mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty top)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c top bit labels)
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) I K c top bit bound)
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hObj : MapsTo (env (rho 4)) oi objects)
    (hObjFamily : ForcingEligibleFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E (env (rho 4)) objects)
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env (rho 4)) S)
    (hMaps : MapsTo S mi maps)
    (hMapFamily : ForcingEligibleMapFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E S maps)
    (hSys : ForcingEligibleSystem.System (env (rho 0)) objects maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hP : PureKuratowski.PairMember M p OP objects)
    (hSm : PureKuratowski.PairMember M sm Om objects)
    (hDP : Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g q bound labels E p Ap Hp XP QP prP OP)
    (hDM : Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g q bound labels E sm Am Hm XM QM prM Om)
    (hDR : Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g q bound labels E r Ar Hr XR QR prR Or)
    (hq : Injection (env (rho 0)) I q)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a (env (rho 0)))
    (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 0)))
    (hmD : (Project.FirstOrderSemantics.reduct M).mem m (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem b (env (rho 0)))
    (hae : Product (env mul) a e t) (hmb : Product (env mul) m b t)
    (hSuba : Sub (env (rho 0)) (env mul) r a q)
    (hSubm : Sub (env (rho 0)) (env mul) r m sm) (hSubp : Sub (env (rho 0)) (env mul) r t p)
    (hn : ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) bound Hm sigma)
    (hel : ForcingEligibility.EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g sm labels E sigma)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal XP)
    (hList : ForcingCollectedName.Collected trueTest Fin.elim0 ordinal enum (env (rho 6)) list)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d g) (hz : Code z d sm)
    (hout : ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) z sigma list)
    (hGeom : Geometry (env (rho 0)) (env mul) a m t U) :
    ∃ xr, (Project.FirstOrderSemantics.reduct M).mem xr Or ∧ PureKuratowski.PairMember M sigma xr prR ∧
      ForcingSystemAvailability.Carrier (env (rho 0)) (env mul) objects maps r xr a U := by
  have hrI := (hp.2.2.2.1 r).mp (ForcingConditionGraphs.function_input hObj.1 hr)
  have hmI := (hp.2.2.2.1 sm).mp (ForcingConditionGraphs.function_input hObj.1 hSm)
  obtain ⟨xr,hxr,hpr⟩ := classFromLocal hM env rho G F mul hm hp hg hmI hrI ⟨m,hmD,hSubm⟩ ⟨a,ha,hSuba⟩ hDM hDR hn hel
  exact ⟨xr,hxr,hpr,classFromLocal_profile hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hp hG hF hc ht hLabels hBound hg hObj hObjFamily hArrows hMaps hMapFamily hSys hr hP hSm hDP hDM hDR hq he hmD hb hae hmb hSuba hSubm hSubp hn hel hEnum hList hd hz hout hGeom hpr⟩

def geometry {k : Nat} (D mul a m t U : Fin k) : Project.Formula 1 k :=
  let member : Project.Formula 1 (k+1) := .mem (.bound 0) (.bound U.succ)
  let profile : Project.Formula 1 (k+1) := .conj (.mem (.bound 0) (.bound D.succ))
    (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ mul.succ 0 a.succ))
      (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ mul.succ 0 m.succ)))
  .conj (.forallE (.conj (.imp member profile) (.imp profile member)))
    (.forallE (.imp (.mem (.bound 0) (.bound D.succ))
      (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ mul.succ 0 a.succ))
        (.imp (.neg member) (ConstructionDiagramPlacements.coneEquality D.succ mul.succ 0 m.succ t.succ)))))

theorem geometry_freeClosed {k : Nat} (D mul a m t U : Fin k) : (geometry D mul a m t U).FreeClosed := by
  simp -implicitDefEqProofs [geometry,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDiagramPlacements.coneEquality_freeClosed]

theorem geometry_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (D mul a m t U : Fin k) :
    Project.Formula.satisfies env (geometry D mul a m t U) ↔
      Geometry (env.bound D) (env.bound mul) (env.bound a) (env.bound m) (env.bound t) (env.bound U) := by
  simp only [geometry,Geometry,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M),ConstructionDiagramPlacements.coneEquality_semantics hM]
  exact ⟨fun ⟨hp,hi⟩ => ⟨fun n => ⟨(hp n).1,(hp n).2⟩,hi⟩,
    fun ⟨hp,hi⟩ => ⟨fun n => ⟨(hp n).mp,(hp n).mpr⟩,hi⟩⟩

def result {k : Nat} (D mul objects maps r Or sigma prR a U : Fin k) : Project.Formula 1 k :=
  .existsE (.conj (.mem (.bound 0) (.bound Or.succ))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge prR.succ sigma.succ 0))
      (ProjectSyntax.encode id (ForcingSystemAvailability.carrier D.succ mul.succ objects.succ maps.succ r.succ 0 a.succ U.succ))))

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p sm Or OP Om Ap Hp XP QP prP Am Hm XM QM prM Ar Hr XR QR prR ordinal enum list d z sigma a e m b t U : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c top bit bound))
    (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (rho 4) oi))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E (rho 4) objects))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul (rho 4) S))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mi))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E S maps))
    (.imp (ForcingEligibleSystem.system (rho 0) objects maps)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects r Or))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects p OP))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects sm Om))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E p Ap Hp XP QP prP OP))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E sm Am Hm XM QM prM Om))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E r Ar Hr XR QR prR Or))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (.mem (.bound a) (.bound (rho 0)))
    (.imp (.mem (.bound e) (.bound (rho 0)))
    (.imp (.mem (.bound m) (.bound (rho 0)))
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul a e t))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul m b t))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r a q))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r m sm))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r t p))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.localName rho G F bound Hm sigma))
    (.imp (ProjectSyntax.encode id (ForcingEligibility.eligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g sm labels E sigma))
    (.imp (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound ordinal) (.bound XP))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected trueTest Fin.elim0 ordinal enum (rho 6) list))
    (.imp (.mem (.bound d) (.bound g))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d sm))
    (.imp (ProjectSyntax.encode id (ForcingOutsideLocal.outside (orderFormula (rho 0) mul) id (rho 6) z sigma list))
    (.imp (geometry (rho 0) mul a m t U)
      (result (rho 0) mul objects maps r Or sigma prR a U))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingEligibleSystem.system_freeClosed,geometry_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p sm Or OP Om Ap Hp XP QP prP Am Hm XM QM prM Ar Hr XR QR prR ordinal enum list d z sigma a e m b t U : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p sm Or OP Om Ap Hp XP QP prP Am Hm XM QM prM Ar Hr XR QR prR ordinal enum list d z sigma a e m b t U)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleFamily.family_semantics (M := M),ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleMapFamily.family_semantics (M := M),
    ForcingEligibleSystem.system_semantics hM,KuratowskiZF.source_edge,ForcingEligibleFamily.data_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingLocalNames.localName_semantics (M := M),ForcingEligibility.eligibleName_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),ForcingOutsideLocal.outside_semantics (M := M),geometry_semantics hM]
  intro hw hMu hI hD hMergers hRow hm hp hG hF hc ht hLabels hBound hg hObj hObjFamily hArrows hMaps hMapFamily hSys hr hP hSm hDP hDM hDR hq ha he hmD hb hae hmb hSuba hSubm hSubp hn hel hEnum hList hd hz hout hGeom
  simp only [result,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSystemAvailability.carrier_semantics (M := M)]
  exact construct hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hp hG hF hc ht hLabels hBound hg hObj hObjFamily hArrows hMaps hMapFamily hSys hr hP hSm hDP hDM hDR hq ha he hmD hb hae hmb hSuba hSubm hSubp hn hel hEnum hList hd hz hout hGeom

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p sm Or OP Om Ap Hp XP QP prP Am Hm XM QM prM Ar Hr XR QR prR ordinal enum list d z sigma a e m b t U : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p sm Or OP Om Ap Hp XP QP prP Am Hm XM QM prM Ar Hr XR QR prR ordinal enum list d z sigma a e m b t U))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let inhabitant := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => inhabitant⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (construction_models rho w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p sm Or OP Om Ap Hp XP QP prP Am Hm XM QM prM Ar Hr XR QR prR ordinal enum list d z sigma a e m b t U hL hChoice)

end PPAC.Migration.ForcingClassProfile
