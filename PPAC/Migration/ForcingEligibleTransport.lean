/- Pinned QuotientTransport.eligibleName_coordinate_transport and
eligible_coordinate_transport. The actual filter, diagram and E all move.
Reuse Separation.symmetry for the existing full HS domain and the existing
local quotient projection; no alternative eligibility or forcing relation. -/
import PPAC.Migration.ForcingLocalQuotientTransport
import PPAC.Migration.ForcingEligibleRestriction
import PPAC.Migration.ForcingComponentMove

namespace PPAC.Migration.ForcingEligibleTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingSupportSize (Injection)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingStabilizerTransport (Image)
open ForcingStabilizer (Action)
open ForcingLocalAtomic (CohenFilter)
open ForcingLocalTransport (CohenPart)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula)
open ForcingSupportingRoot (Code)
open ForcingEligibility (EligibleName Eligible)
open ForcingFormula (Force)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem name_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w pi a ac g gT r rT labels E ET sigma sigmaT : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hNormal : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : Permutation I pi)
    (ha : ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) pi a)
    (hc : CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hg : CohenFilter (env (rho 3)) g) (hImage : Image ac g gT)
    (hr : Injection (env (rho 0)) I r) (hrT : Injection (env (rho 0)) I rT)
    (hComp : CompositionGraph (env (rho 0)) pi r rT)
    (hLabels : Action (env (rho 6)) a labels labels) (hE : Action (env (rho 6)) a E ET)
    (hs : Action (env (rho 6)) a sigma sigmaT) :
    EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) gT rT labels ET sigmaT ↔
      EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g r labels E sigma := by
  have hac := ForcingLocalTransport.part_permutation hc
  have hv : ∀ j : Fin 3, Action (env (rho 6)) a (args3 sigma labels E j) (args3 sigmaT labels ET j) := by
    intro j
    exact Fin.cases hs (fun j => Fin.cases hLabels (fun j => Fin.cases hE (fun j => Fin.elim0 j) j) j) j
  have hAt : ∀ d dT z zT, (Project.FirstOrderSemantics.reduct M).mem d g →
      PureKuratowski.PairMember M d dT ac → Code z d r → Code zT dT rT →
      (Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
          (args3 sigma labels E) (env (rho 6)) z (ForcingEligibility.isClass 0 1 2) ↔
        Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
          (args3 sigmaT labels ET) (env (rho 6)) zT (ForcingEligibility.isClass 0 1 2)) := by
    intro d dT z zT hd hdd hz hzT
    have hzW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 d).mp (hg.1 d hd)) hr hz
    exact ForcingSeparation.symmetry hM env rho G F mul hp hG hNormal hpi
      ((ForcingProductFamily.mapRel_action (fun j => env (rho j)) pi a).mpr ha)
      (ForcingEligibility.isClass 0 1 2) (args3 sigma labels E) (args3 sigmaT labels ET) hv hzW
      (ForcingLocalTransport.moved_code hM hp ha hc hdd hr hrT hComp hz hzT)
  constructor
  · rintro ⟨dT,zT,hdT,hzT,hforce⟩
    obtain ⟨d,hd,hdd⟩ := (hImage dT).mp hdT
    obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM d r
    exact ⟨d,z,hd,hz,(hAt d dT z zT hd hdd hz hzT).mpr hforce⟩
  · rintro ⟨d,z,hd,hz,hforce⟩
    obtain ⟨dT,hdd,_⟩ := hac.1.1.2 d (hg.1 d hd)
    obtain ⟨zT,hzT⟩ := ForcingSupportingRoot.exists_code hM dT rT
    exact ⟨dT,zT,(hImage dT).mpr ⟨d,hd,hdd⟩,hzT,(hAt d dT z zT hd hdd hz hzT).mp hforce⟩

theorem class_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w e pi a ac g gT r rT labels E ET X Y pr ps f x y : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hNormal : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : Permutation I pi)
    (ha : ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) pi a)
    (hc : CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hg : CohenFilter (env (rho 3)) g) (hImage : Image ac g gT)
    (hr : Injection (env (rho 0)) I r) (hrT : Injection (env (rho 0)) I rT)
    (hComp : CompositionGraph (env (rho 0)) pi r rT)
    (hLabels : Action (env (rho 6)) a labels labels) (hE : Action (env (rho 6)) a E ET)
    (hPr : ForcingLocalQuotient.Projection (orderFormula (rho 0) mul) env (env (rho 6)) g r X pr)
    (hPs : ForcingLocalQuotient.Projection (orderFormula (rho 0) mul) env (env (rho 6)) gT rT Y ps)
    (hGraph : ForcingLocalQuotientTransport.Graph (env (rho 6)) a pr ps f)
    (hxy : PureKuratowski.PairMember M x y f) :
    Eligible (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) gT rT labels ET ps y ↔
      Eligible (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g r labels E pr x := by
  have hOrder : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨_,t,_,_,ht,_,_,hacg⟩ := hc
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hacg
  have hgT := ForcingLocalTransport.filter_image (ForcingLocalTransport.part_permutation hc) hOrder hg hImage
  obtain ⟨sigma,tau,hsx,hAct,hty⟩ := (hGraph x y).mp hxy
  exact (ForcingEligibility.eligible_ofName hM env rho G F mul hm hp hgT hrT hPs hty).trans
    ((name_iff hM env rho G F mul hp hG hNormal hpi ha hc hg hImage hr hrT hComp hLabels hE hAct).trans
      (ForcingEligibility.eligible_ofName hM env rho G F mul hm hp hg hr hPr hsx).symm)

/-- The original labelSet, rather than a postulated fixed class of labels. -/
theorem literal_labels_fixed (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {I K B w G F mu pi inv c a ai labelMap top bit labels : M.Carrier .set}
    (hData : ForcingProductCovariance.SystemData v I K B w G F mu pi inv c a ai)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hSmall : ForcingSupportSize.Small w mu)
    (hNormal : ForcingNormalFilter.Normal I G F) (hLabelMap : ForcingConditionGraphs.FunctionOn K labelMap)
    (hTop : ForcingWithTopCarrier.Empty top) (hLabels : ForcingLabelSet.LabelSet (v 6) I K labelMap top bit labels) :
    Action (v 6) a labels labels := by
  have hFixed := (ForcingLabelSet.HS_and_fixed hM v hData.1 hData.2.1 hNormal
    hData.2.2.2.2.2.2.2.2.2 hw hSmall hLabelMap hTop hLabels).2
  exact hFixed pi ((hData.2.1 pi).mpr hData.2.2.1) a
    ((ForcingProductFamily.mapRel_action v pi a).mpr hData.2.2.2.2.2.2.2.1)

/-- Restrict the actual quotient transport to the existing eligible object
sets. This includes the root cone; both roots may move. The application
fixes q and E by their original support hypotheses. -/
theorem object_bijection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w e pi a ac g gT r rT q qT labels E ET X Y pr ps f Q T V U : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hNormal : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : Permutation I pi)
    (ha : ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) pi a)
    (hc : CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hg : CohenFilter (env (rho 3)) g) (hImage : Image ac g gT)
    (hr : Injection (env (rho 0)) I r) (hrT : Injection (env (rho 0)) I rT)
    (hComp : CompositionGraph (env (rho 0)) pi r rT)
    (hq : Injection (env (rho 0)) I q) (hqT : CompositionGraph (env (rho 0)) pi q qT)
    (hLabels : Action (env (rho 6)) a labels labels) (hE : Action (env (rho 6)) a E ET)
    (hPr : ForcingLocalQuotient.Projection (orderFormula (rho 0) mul) env (env (rho 6)) g r X pr)
    (hPs : ForcingLocalQuotient.Projection (orderFormula (rho 0) mul) env (env (rho 6)) gT rT Y ps)
    (hGraph : ForcingLocalQuotientTransport.Graph (env (rho 6)) a pr ps f)
    (hf : Injection Q T f)
    (hOnto : ∀ y, (Project.FirstOrderSemantics.reduct M).mem y T →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x Q ∧ PureKuratowski.PairMember M x y f)
    (hV : ForcingEligibleObjects.Carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 0)) (env mul) (env (rho 6)) g r q labels E pr Q V)
    (hU : ForcingEligibleObjects.Carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 0)) (env mul) (env (rho 6)) gT rT qT labels ET ps T U) :
    ∃ b, Injection V U b ∧ ForcingEligibleRestriction.Restricts b f V ∧
      ∀ y, (Project.FirstOrderSemantics.reduct M).mem y U →
        ∃ x, (Project.FirstOrderSemantics.reduct M).mem x V ∧ PureKuratowski.PairMember M x y b := by
  have hLe := ForcingDiagramOrder.le_iff hM (mul := env mul) hpi hr hq hComp hqT
  have hPres : ∀ x y, PureKuratowski.PairMember M x y f →
      ((Project.FirstOrderSemantics.reduct M).mem x V ↔ (Project.FirstOrderSemantics.reduct M).mem y U) := by
    intro x y hxy
    have hEl := class_iff hM env rho G F mul hm hp hG hNormal hpi ha hc hg hImage hr hrT hComp hLabels hE hPr hPs hGraph hxy
    exact (hV x).trans ((and_congr
      (iff_of_true (ForcingConditionGraphs.function_input hf.1.1 hxy) (hf.1.2 x y hxy))
      (and_congr hLe hEl.symm)).trans (hU y).symm)
  obtain ⟨b,hb⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) f V
  have hEdge : ForcingEligibleRestriction.Restricts b f V := fun x y => (hb.2 x y).trans and_comm
  have hMap : ForcingSupportSize.MapsTo V U b := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro row hrow
      obtain ⟨x,y,hcode⟩ := hb.1 row hrow
      exact ⟨x,y,((hb.2 x y).mp ⟨row,hcode,hrow⟩).1,hcode⟩
    · intro x hx
      obtain ⟨y,hxy,_⟩ := hf.1.1.2 x ((hV x).mp hx).1
      exact ⟨y,(hEdge x y).mpr ⟨hxy,hx⟩,fun z hxz =>
        ForcingConditionGraphs.function_unique hf.1.1 ((hEdge x z).mp hxz).1 hxy⟩
    · intro x y hxy
      obtain ⟨hxy,hx⟩ := (hEdge x y).mp hxy
      exact (hPres x y hxy).mp hx
  refine ⟨b,ForcingEligibleRestriction.restrict_injective hf hEdge hMap,hEdge,?_⟩
  intro y hy
  obtain ⟨x,_,hxy⟩ := hOnto y ((hU y).mp hy).1
  have hx := (hPres x y hxy).mpr hy
  exact ⟨x,hx,(hEdge x y).mpr ⟨hxy,hx⟩⟩

def onto {k : Nat} (f X Y : Fin k) : Formula k :=
  .all ((Formula.mem (Fin.last k) Y.castSucc).imp
    (.ex ((Formula.mem (Fin.last (k+1)) X.castSucc.castSucc).conj
      (Source.SetLanguage.edge f.castSucc.castSucc (Fin.last (k+1)) ((Fin.last k).castSucc)))))

theorem onto_semantics {k : Nat} (env : Fin k → M.Carrier .set) (f X Y : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (onto f X Y) ↔
      ∀ y, (Project.FirstOrderSemantics.reduct M).mem y (env Y) →
        ∃ x, (Project.FirstOrderSemantics.reduct M).mem x (env X) ∧ PureKuratowski.PairMember M x y (env f) := by
  simp only [onto,Formula.Realize,KuratowskiZF.source_edge,Fin.lastCases_last,Fin.lastCases_castSucc]

def restrictedBijection {k : Nat} (f V U : Fin k) : Formula k :=
  .ex ((Source.SetLanguage.injection (Fin.last k) V.castSucc U.castSucc).conj
    ((RestrictionSyntax.edgeLaw (Fin.last k) f.castSucc V.castSucc).conj (onto (Fin.last k) V.castSucc U.castSucc)))

theorem restrictedBijection_semantics {k : Nat} (env : Fin k → M.Carrier .set) (f V U : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (restrictedBijection f V U) ↔
      ∃ b, Injection (env V) (env U) b ∧ ForcingEligibleRestriction.Restricts b (env f) (env V) ∧
        ∀ y, (Project.FirstOrderSemantics.reduct M).mem y (env U) →
          ∃ x, (Project.FirstOrderSemantics.reduct M).mem x (env V) ∧ PureKuratowski.PairMember M x y b := by
  simp only [restrictedBijection,Formula.Realize,ForcingSupportSize.injection_semantics (M := M),
    ForcingEligibleRestriction.edgeLaw_semantics (M := M),onto_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Actual source root-group application: existing support of E and the
literal labelSet discharge both fixed-name premises, and existing root_fixed
discharges the root-cone transport premise. -/
theorem root_object_bijection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) I K B w (env G) (env F) mu pi inv c a ai)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hSmall : ForcingSupportSize.Small w mu)
    (hNormal : ForcingNormalFilter.Normal I (env G) (env F)) (hLabelMap : ForcingConditionGraphs.FunctionOn K labelMap)
    (hTop : ForcingWithTopCarrier.Empty top) (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K labelMap top bit labels)
    (hc : CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hg : CohenFilter (env (rho 3)) g) (hImage : Image ac g gT)
    (hr : Injection (env (rho 0)) I r) (hrT : Injection (env (rho 0)) I rT)
    (hComp : CompositionGraph (env (rho 0)) pi r rT)
    (hq : Injection (env (rho 0)) I q) (hA : ForcingSupportedNames.Range (env (rho 0)) q A)
    (hHq : ForcingLabelPermutations.Fixing (env G) A Hq) (hpiHq : (Project.FirstOrderSemantics.reduct M).mem pi Hq)
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) Hq E)
    (hPr : ForcingLocalQuotient.Projection (orderFormula (rho 0) mul) env (env (rho 6)) g r X pr)
    (hPs : ForcingLocalQuotient.Projection (orderFormula (rho 0) mul) env (env (rho 6)) gT rT Y ps)
    (hGraph : ForcingLocalQuotientTransport.Graph (env (rho 6)) a pr ps f)
    (hf : Injection Q T f)
    (hOnto : ∀ y, (Project.FirstOrderSemantics.reduct M).mem y T →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x Q ∧ PureKuratowski.PairMember M x y f)
    (hV : ForcingEligibleObjects.Carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 0)) (env mul) (env (rho 6)) g r q labels E pr Q V)
    (hU : ForcingEligibleObjects.Carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 0)) (env mul) (env (rho 6)) gT rT q labels E ps T U) :
    ∃ b, Injection V U b ∧ ForcingEligibleRestriction.Restricts b f V ∧
      ∀ y, (Project.FirstOrderSemantics.reduct M).mem y U →
        ∃ x, (Project.FirstOrderSemantics.reduct M).mem x V ∧ PureKuratowski.PairMember M x y b := by
  have ha := hData.2.2.2.2.2.2.2.1
  have hFix := ((hHq pi).mp hpiHq).2
  have hRoot := ForcingComponentMove.root_fixed hData.2.2.1 hq hA hFix
  have hLabelsAct := literal_labels_fixed hM hData hw hSmall hNormal hLabelMap hTop hLabels
  have hEAct := hE pi hpiHq a ((ForcingProductFamily.mapRel_action (fun j => env (rho j)) pi a).mpr ha)
  exact object_bijection hM env rho G F mul hm hData.1 hData.2.1 hNormal hData.2.2.1 ha hc hg hImage hr hrT hComp
    hq hRoot hLabelsAct hEAct hPr hPs hGraph hf hOnto hV hU

def nameSentence {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K B w pi a ac g gT r rT labels E ET sigma sigmaT : Fin k) : Source.Sentence :=
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp
    ((ForcingNormalFilter.normal I G F).imp
    ((ForcingConditionGraphs.permutation I pi).imp
    ((ForcingProductFamily.action (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6) pi a).imp
    ((ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) pi ac).imp
    ((ForcingLocalAtomic.cohenFilter (rho 3) g).imp
    ((ForcingStabilizerTransport.image ac g gT).imp
    ((Source.SetLanguage.injection r (rho 0) I).imp
    ((Source.SetLanguage.injection rT (rho 0) I).imp
    ((ForcingConditionGraphs.compositionGraph (rho 0) pi r rT).imp
    ((ForcingStabilizer.action (rho 6) a labels labels).imp
    ((ForcingStabilizer.action (rho 6) a E ET).imp
    ((ForcingStabilizer.action (rho 6) a sigma sigmaT).imp
    ((ForcingEligibility.eligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) gT rT labels ET sigmaT).iff (ForcingEligibility.eligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g r labels E sigma)))))))))))))))).close

theorem name_models {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K B w pi a ac g gT r rT labels E ET sigma sigmaT : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (nameSentence rho G F mul I K B w pi a ac g gT r rT labels E ET sigma sigmaT)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hNormal hpi ha hc hg hImage hr hrT hComp hLabels hE hs
  have h := name_iff hM env rho G F mul
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hNormal)
    ((ForcingConditionGraphs.permutation_semantics (M := M) env I pi).mp hpi)
    ((ForcingProductFamily.action_semantics (M := M) env (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6) pi a).mp ha)
    ((ForcingLocalTransport.cohenPart_semantics (M := M) env (rho 1) (rho 2) (rho 3) pi ac).mp hc)
    ((ForcingLocalAtomic.cohenFilter_semantics (M := M) env (rho 3) g).mp hg)
    ((ForcingStabilizerTransport.image_semantics (M := M) env ac g gT).mp hImage)
    ((ForcingSupportSize.injection_semantics (M := M) env r (rho 0) I).mp hr)
    ((ForcingSupportSize.injection_semantics (M := M) env rT (rho 0) I).mp hrT)
    ((ForcingConditionGraphs.compositionGraph_semantics (M := M) env (rho 0) pi r rT).mp hComp)
    ((ForcingStabilizer.action_semantics (M := M) env (rho 6) a labels labels).mp hLabels)
    ((ForcingStabilizer.action_semantics (M := M) env (rho 6) a E ET).mp hE)
    ((ForcingStabilizer.action_semantics (M := M) env (rho 6) a sigma sigmaT).mp hs)
  have ht := ForcingEligibility.eligibleName_semantics (M := M) env
    (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) gT rT labels ET sigmaT
  have hs := ForcingEligibility.eligibleName_semantics (M := M) env
    (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g r labels E sigma
  exact ⟨fun ht' => hs.mpr (h.mp (ht.mp ht')),fun hs' => ht.mpr (h.mpr (hs.mp hs'))⟩

theorem name_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K B w pi a ac g gT r rT labels E ET sigma sigmaT : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (nameSentence rho G F mul I K B w pi a ac g gT r rT labels E ET sigma sigmaT)) :=
  ModelTransfer.derives (fun _ hM => name_models rho G F mul I K B w pi a ac g gT r rT labels E ET sigma sigmaT hM)

def rootSentence {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
      (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c a ai))
      (.imp (Project.Formula.isOmega (.bound w))
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
      (.imp (ProjectSyntax.encode id (ForcingNormalFilter.normal I G F))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
      (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
      (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
      (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) pi ac))
      (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
      (.imp (ProjectSyntax.encode id (ForcingStabilizerTransport.image ac g gT))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection rT (rho 0) I))
      (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) pi r rT))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
      (.imp (ProjectSyntax.encode id (Formula.mem pi Hq))
      (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
      (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g r X pr))
      (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) gT rT Y ps))
      (.imp (ProjectSyntax.encode id (ForcingLocalQuotientTransport.graph (rho 6) a pr ps f))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection f Q T))
      (.imp (ProjectSyntax.encode id (onto f Q T))
      (.imp (ProjectSyntax.encode id (ForcingEligibleObjects.carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 0) mul (rho 6) g r q labels E pr Q V))
      (.imp (ProjectSyntax.encode id (ForcingEligibleObjects.carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 0) mul (rho 6) gT rT q labels E ps T U))
      (ProjectSyntax.encode id (restrictedBijection f V U))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed]

theorem root_models {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (rootSentence rho G F mul I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (rootSentence rho G F mul I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductCovariance.systemData_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingNormalFilter.normal_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLocalTransport.cohenPart_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),ForcingStabilizerTransport.image_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    Formula.Realize,ForcingSupportedNames.supported_semantics (M := M),ForcingLocalQuotient.projection_semantics (M := M),
    ForcingLocalQuotientTransport.graph_semantics (M := M),onto_semantics (M := M),
    ForcingEligibleObjects.carrier_semantics (M := M),restrictedBijection_semantics (M := M)]
  exact root_object_bijection hM env rho G F mul

theorem root_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (rootSentence rho G F mul I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U)) :=
  ModelTransfer.derives (fun _ hM => root_models rho G F mul I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U hM)

/-- One actual eligible-system app, assembled from the two already built
object rows. The quotient transport is constructed here, not assumed. -/
def App (W a pr ps Q T V U : M.Carrier .set) : Prop :=
  ∃ f b, Injection Q T f ∧ ForcingLocalQuotientTransport.Graph W a pr ps f ∧
    Injection V U b ∧ ForcingEligibleRestriction.Restricts b f V ∧
    ∀ y, (Project.FirstOrderSemantics.reduct M).mem y U →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x V ∧ PureKuratowski.PairMember M x y b

theorem assemble_app (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul a : Fin k)
    {I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound
      Ar Hr X Q pr V AT HT Y T ps U : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) I K B w (env G) (env F) mu pi inv c (env a) ai)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hSmall : ForcingSupportSize.Small w mu)
    (hNormal : ForcingNormalFilter.Normal I (env G) (env F)) (hLabelMap : ForcingConditionGraphs.FunctionOn K labelMap)
    (hTop : ForcingWithTopCarrier.Empty top) (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K labelMap top bit labels)
    (hBound : ForcingPowerName.Bound (env (rho 6)) labels bound)
    (hc : CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hg : CohenFilter (env (rho 3)) g) (hImage : Image ac g gT)
    (hr : Injection (env (rho 0)) I r) (hrT : Injection (env (rho 0)) I rT)
    (hComp : CompositionGraph (env (rho 0)) pi r rT)
    (hq : Injection (env (rho 0)) I q) (hA : ForcingSupportedNames.Range (env (rho 0)) q A)
    (hHq : ForcingLabelPermutations.Fixing (env G) A Hq) (hpiHq : (Project.FirstOrderSemantics.reduct M).mem pi Hq)
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) Hq E)
    (hSource : ForcingEligibleFamily.Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E r Ar Hr X Q pr V)
    (hTarget : ForcingEligibleFamily.Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) gT q bound labels E rT AT HT Y T ps U) :
    App (env (rho 6)) (env a) pr ps Q T V U := by
  obtain ⟨hAr,hHr,hX,hpr,hQ,hPr,hV⟩ := hSource
  obtain ⟨hAT,hHT,hY,hps,hT,hPs,hU⟩ := hTarget
  have hp := hData.1
  have hG := hData.2.1
  have hpi := hData.2.2.1
  have ha := hData.2.2.2.2.2.2.2.1
  obtain ⟨hHS,hFixed⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal
    hData.2.2.2.2.2.2.2.2.2 hw hSmall hLabelMap hTop hLabels
  have hStable := ForcingLocalNameTransport.bound_supported hM hp hG hHS hFixed hBound
  have hArI : ForcingPowerName.Subset Ar I := by
    intro y hy
    obtain ⟨x,_,hxy⟩ := (hAr y).mp hy
    exact hr.1.2 x y hxy
  obtain ⟨AT',hATImage,_⟩ := ForcingLabelConjugacy.exists_image hM hpi.1 (J := Ar)
  have hRangeT := ForcingLocalNameTransport.range_image hAr hComp hATImage
  have hSame : AT' = AT := (ModelTransfer.extensionality hM).eq_of_same_members AT' AT
    (fun y => (hRangeT y).trans (hAT y).symm)
  subst AT'
  obtain ⟨nf,hnf,hnGraph,hnOnto⟩ := ForcingLocalNameTransport.exists_graph hM hData hStable hArI hATImage hHr hHT hX hY
  have hOrder : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨_,t,_,_,ht,_,_,hacg⟩ := hc
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hacg
  have hgT := ForcingLocalTransport.filter_image (ForcingLocalTransport.part_permutation hc) hOrder hg hImage
  obtain ⟨f,hf,hGraph,hOnto⟩ := ForcingLocalQuotientTransport.exists_transport hM hnf.1 hnGraph hnOnto hpr hps hQ hT hPr hPs
    (ForcingLocalQuotient.equality_law hM env rho mul hm hp hg hr hPr)
    (ForcingLocalQuotient.equality_law hM env rho mul hm hp hgT hrT hPs)
    (fun sigma tau sigmaT tauT hs ht => ForcingLocalTransport.local_eq_transport_iff hM env rho mul a
      hp hpi ha hc hg hImage hr hrT hComp
      ((ForcingNameConjugacy.action_iff env (rho 6) a sigma sigmaT).mpr hs)
      ((ForcingNameConjugacy.action_iff env (rho 6) a tau tauT).mpr ht))
  obtain ⟨b,hb,hRestricts,hOntoB⟩ := root_object_bijection hM env rho G F mul hm hData hw hSmall hNormal hLabelMap hTop hLabels
    hc hg hImage hr hrT hComp hq hA hHq hpiHq hE hPr hPs hGraph hf hOnto hV hU
  exact ⟨f,b,hf,hGraph,hb,hRestricts,hOntoB⟩

def app {k : Nat} (W a pr ps Q T V U : Fin k) : Formula k :=
  let up := fun i : Fin k => i.castSucc.castSucc
  let f := (Fin.last k).castSucc
  let b := Fin.last (k+1)
  .ex (.ex ((Source.SetLanguage.injection f (up Q) (up T)).conj
    ((ForcingLocalQuotientTransport.graph (up W) (up a) (up pr) (up ps) f).conj
      ((Source.SetLanguage.injection b (up V) (up U)).conj
        ((RestrictionSyntax.edgeLaw b f (up V)).conj (onto b (up V) (up U)))))))

theorem app_semantics {k : Nat} (env : Fin k → M.Carrier .set) (W a pr ps Q T V U : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (app W a pr ps Q T V U) ↔
      App (env W) (env a) (env pr) (env ps) (env Q) (env T) (env V) (env U) := by
  simp only [app,App,Formula.Realize,ForcingSupportSize.injection_semantics (M := M),
    ForcingLocalQuotientTransport.graph_semantics (M := M),ForcingEligibleRestriction.edgeLaw_semantics (M := M),
    onto_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def assemblySentence {k : Nat} (rho : Fin 7 → Fin k) (G F mul a I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound Ar Hr X Q pr V AT HT Y T ps U : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
      (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c a ai))
      (.imp (Project.Formula.isOmega (.bound w))
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
      (.imp (ProjectSyntax.encode id (ForcingNormalFilter.normal I G F))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
      (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
      (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
      (.imp (ProjectSyntax.encode id (ForcingLabelBound.bound (rho 6) labels bound))
      (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) pi ac))
      (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
      (.imp (ProjectSyntax.encode id (ForcingStabilizerTransport.image ac g gT))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection rT (rho 0) I))
      (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) pi r rT))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
      (.imp (ProjectSyntax.encode id (Formula.mem pi Hq))
      (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
      (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E r Ar Hr X Q pr V))
      (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul gT q bound labels E rT AT HT Y T ps U))
      (ProjectSyntax.encode id (app (rho 6) a pr ps Q T V U))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed]

theorem assembly_models {k : Nat} (rho : Fin 7 → Fin k) (G F mul a I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound Ar Hr X Q pr V AT HT Y T ps U : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (assemblySentence rho G F mul a I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound Ar Hr X Q pr V AT HT Y T ps U)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (assemblySentence rho G F mul a I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound Ar Hr X Q pr V AT HT Y T ps U)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductCovariance.systemData_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingNormalFilter.normal_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.bound_semantics (M := M),
    ForcingLocalTransport.cohenPart_semantics (M := M),ForcingLocalAtomic.cohenFilter_semantics (M := M),
    ForcingStabilizerTransport.image_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),Formula.Realize,ForcingSupportedNames.supported_semantics (M := M),
    ForcingEligibleFamily.data_semantics (M := M),app_semantics (M := M)]
  exact assemble_app hM env rho G F mul a

theorem assembly_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F mul a I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound Ar Hr X Q pr V AT HT Y T ps U : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (assemblySentence rho G F mul a I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound Ar Hr X Q pr V AT HT Y T ps U)) :=
  ModelTransfer.derives (fun _ hM => assembly_models rho G F mul a I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound Ar Hr X Q pr V AT HT Y T ps U hM)

end PPAC.Migration.ForcingEligibleTransport
