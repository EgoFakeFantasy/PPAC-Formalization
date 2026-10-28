/- Pinned DiagramPlacements.descent_comparison_placement:491.
Consume existing three-copy placement, fixed-three diagram amalgamation and
actual Cohen compatibility/union. No given output lower bound or placement. -/
import PPAC.Migration.ConstructionDiagramThree
import PPAC.Migration.ConstructionCohenCompatibility
import PPAC.Migration.ForcingProductAction

namespace PPAC.Migration.ConstructionDescentPlacement
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Injection Small)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ForcingStabilizerTransport (Image)
open ConstructionPlacementTriple (ImageAt)
open ConstructionPlacementPasting (AgreesOn)
open ConstructionCohenCompatibility (Within Restricted Moved Entry Support)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ActualMoved (CC S w pi d q : M.Carrier .set) : Prop :=
  ∃ f g, Permutation CC f ∧ ForcingCohenCoordinates.Graph CC pi f ∧
    Permutation S g ∧ ForcingCohenCoordinates.Graph S f g ∧ Condition S w q ∧
    Image g d q ∧ Moved pi d q

def Boundary (D CC S w s0 alpha beta d c : M.Carrier .set) : Prop :=
  ∃ A delta deltaA deltaB, Image s0 D A ∧ Condition S w delta ∧ Restricted A d delta ∧
    ActualMoved CC S w alpha delta deltaA ∧ ActualMoved CC S w beta delta deltaB ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset deltaA c ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset deltaB c

def WithinRange (D v d : M.Carrier .set) : Prop :=
  ∀ i k b, Entry d i k b → ImageAt v D i

def Inputs (I J CC B S w D mul p s0 s1 v alpha beta sa sb d c t : M.Carrier .set) : Prop :=
  Cartesian I J CC ∧ Cartesian CC B S ∧ Injection D I p ∧ Injection D I s0 ∧
    Injection D I s1 ∧ Injection D I v ∧ Injection D I sa ∧ Injection D I sb ∧ Injection D I t ∧
    ConstructionDiagramPlacements.RangeIntersection D s0 s1 p ∧
    ForcingDiagramOrder.Le D mul v s0 ∧ ForcingDiagramOrder.Le D mul v s1 ∧
    Permutation I alpha ∧ Permutation I beta ∧
    ConstructionDiagramPlacements.FixesRange D p alpha ∧ ConstructionDiagramPlacements.FixesRange D p beta ∧
    CompositionGraph D alpha s0 sa ∧ CompositionGraph D beta s0 sb ∧
    ConstructionDiagramPlacements.RangeIntersection D sa sb p ∧ Condition S w d ∧ Condition S w c ∧
    WithinRange D v d ∧ ForcingDiagramOrder.Le D mul t sa ∧ ForcingDiagramOrder.Le D mul t sb ∧
    Boundary D CC S w s0 alpha beta d c

def Result (D I mul CC S w s0 s1 v sa sb d c t pi rho q : M.Carrier .set) : Prop :=
  Permutation I pi ∧ Permutation I rho ∧ CompositionGraph D pi s0 sa ∧ CompositionGraph D rho s0 sb ∧
    ∃ shared vP vR dP dR a z cT pP pR,
      Injection D I shared ∧ CompositionGraph D pi s1 shared ∧ CompositionGraph D rho s1 shared ∧
      Injection D I vP ∧ CompositionGraph D pi v vP ∧
      Injection D I vR ∧ CompositionGraph D rho v vR ∧
      ActualMoved CC S w pi d dP ∧ ActualMoved CC S w rho d dR ∧
      Condition S w a ∧ Injection D I z ∧ PureKuratowski.Code M q a z ∧
      PureKuratowski.Code M cT c t ∧ PureKuratowski.Code M pP dP vP ∧ PureKuratowski.Code M pR dR vR ∧
      ForcingProductAction.Le D mul q cT ∧ ForcingProductAction.Le D mul q pP ∧ ForcingProductAction.Le D mul q pR

/-- Package the original native range and the already available ordinal-image bound. -/
theorem diagram_range (hM : FirstOrder.Theory.Models M nativeZF)
    {D I r mu : M.Carrier .set}
    (hMu : (Project.FirstOrderSemantics.reduct M).IsOrdinal mu)
    (hr : Injection D I r) (hD : Small D mu) :
    ∃ A, Image r D A ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset A I ∧ Small A mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hNative := (ForcingSupportSize.native_injection hM D I r).mp hr
  obtain ⟨A,hA⟩ := ZF.exists_range_of_setFunction hZF pair hNative.1.1 hNative.1.2.1
  have hImage : Image r D A := fun y => ⟨fun hy => by
      obtain ⟨x,hxy⟩ := (hA y).mp hy
      exact ⟨x,hNative.1.input_mem_of_pairMember hxy,hxy⟩,
    fun ⟨x,_,hxy⟩ => (hA y).mpr ⟨x,hxy⟩⟩
  have hFunction : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo pair r D A := by
    refine ⟨hNative.1.1,hNative.1.2.1,?_⟩
    intro x hx
    obtain ⟨y,_,hxy⟩ := hNative.1.2.2 x hx
    exact ⟨y,(hA y).mpr ⟨x,hxy⟩,hxy⟩
  have hSurj : (Project.FirstOrderSemantics.reduct M).IsSetSurjectiveOnto pair r D A := by
    intro y hy
    exact (hImage y).mp hy
  exact ⟨A,hImage,fun y hy => by
    obtain ⟨x,_,hxy⟩ := (hImage y).mp hy
    exact hr.1.2 x y hxy,
    (ForcingSupportSize.native_small hM A mu).mpr
      (ExistingOrdinalImage.ordinal_image_bound_l pair hZF hMu
        ((ForcingSupportSize.native_small hM D mu).mp hD) hFunction hSurj)⟩

theorem range_antitone {D mul r s z : M.Carrier .set} (h : ForcingDiagramOrder.Le D mul r s) :
    ImageAt s D z → ImageAt r D z := by
  rintro ⟨x,hx,hxz⟩
  obtain ⟨n,_,hSub⟩ := h
  obtain ⟨_,y,hy,_,hyz⟩ := (hSub x z).mp hxz
  exact ⟨y,hy,hyz⟩

theorem range_permute {D r pi R A z : M.Carrier .set}
    (hA : Image r D A) (hR : CompositionGraph D pi r R) :
    ImageAt R D z ↔ ImageAt pi A z := by
  constructor
  · rintro ⟨x,_,hxz⟩
    obtain ⟨hx,y,hxy,hyz⟩ := (hR x z).mp hxz
    exact ⟨y,(hA y).mpr ⟨x,hx,hxy⟩,hyz⟩
  · rintro ⟨y,hy,hyz⟩
    obtain ⟨x,hx,hxy⟩ := (hA y).mp hy
    exact ⟨x,hx,(hR x z).mpr ⟨hx,y,hxy,hyz⟩⟩

theorem agrees_iff {I A pi rho : M.Carrier .set}
    (hAI : (Project.FirstOrderSemantics.reduct M).MemberSubset A I)
    (hpi : Permutation I pi) (hrho : Permutation I rho) (h : AgreesOn A pi rho) :
    ∀ x y, (Project.FirstOrderSemantics.reduct M).mem x A →
      (PureKuratowski.PairMember M x y pi ↔ PureKuratowski.PairMember M x y rho) := by
  intro x y hx
  constructor
  · intro hxy
    obtain ⟨z,hxz,_⟩ := hrho.1.1.2 x (hAI x hx)
    have he := ForcingConditionGraphs.function_unique hpi.1.1 hxy (h x z hx hxz)
    simpa only [he] using hxz
  · exact h x y hx

theorem composition_transport {D r pi rho R : M.Carrier .set}
    (h : ∀ y, ImageAt r D y → ∀ z,
      PureKuratowski.PairMember M y z pi ↔ PureKuratowski.PairMember M y z rho)
    (hR : CompositionGraph D pi r R) : CompositionGraph D rho r R := by
  intro x z
  constructor
  · intro hxz
    obtain ⟨hx,y,hxy,hyz⟩ := (hR x z).mp hxz
    exact ⟨hx,y,hxy,(h y ⟨x,hx,hxy⟩ z).mp hyz⟩
  · rintro ⟨hx,y,hxy,hyz⟩
    exact (hR x z).mpr ⟨hx,y,hxy,(h y ⟨x,hx,hxy⟩ z).mpr hyz⟩

theorem actual_moved_condition {CC S w pi d q : M.Carrier .set} (h : ActualMoved CC S w pi d q) :
    Condition S w q ∧ Moved pi d q := by
  obtain ⟨_,_,_,_,_,_,hq,_,hMoved⟩ := h
  exact ⟨hq,hMoved⟩

theorem descent_comparison_placement (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu history kappa D mul e mark H C incoming base I J B CC S p s0 s1 v alpha beta sa sb d c t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small D mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa D mul e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (h : Inputs I J CC B S w D mul p s0 s1 v alpha beta sa sb d c t) :
    ∃ pi rho q, Result D I mul CC S w s0 s1 v sa sb d c t pi rho q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨hC,hS,hp,hs0,hs1,hv,hsa,hsb,ht,hInter,hv0,hv1,hAlpha,hBeta,hFixAlpha,hFixBeta,
    hsaGraph,hsbGraph,hInd,hd,hc,hWithin,htAlpha,htBeta,hBoundary⟩ := h
  obtain ⟨A,delta,deltaA,deltaB,hA,hDelta,hRestr,hDeltaA,hDeltaB,hcAlpha,hcBeta⟩ := hBoundary
  obtain ⟨A0,hA0,hA0I,hA0Small⟩ := diagram_range hM hMu.1.1 hs0 hD
  have hEqA := ForcingCohenOrderAction.image_unique hM hA0 hA
  subst A0
  obtain ⟨E,hE,hEI,hESmall⟩ := diagram_range hM hMu.1.1 hs1 hD
  obtain ⟨V,hV,hVI,hVSmall⟩ := diagram_range hM hMu.1.1 hv hD
  obtain ⟨root,hRoot,hRootI,hRootSmall⟩ := diagram_range hM hMu.1.1 hp hD
  obtain ⟨T,hT,hTI,hTSmall⟩ := diagram_range hM hMu.1.1 ht hD
  obtain ⟨supportC,hSupportC,hSupportCI,hSupportSmall⟩ := ConstructionCohenCompatibility.exists_support hM hw hC hS hc
  have hSupportMu : Small supportC mu := (ForcingSupportSize.native_small hM supportC mu).mpr (by
    obtain ⟨toW,hToW⟩ := (ForcingSupportSize.native_small hM supportC w).mp hSupportSmall
    obtain ⟨toMu,hToMu⟩ := hMu.2
    exact ZF.exists_compositionInjection hZF pair hToW hToMu)
  obtain ⟨K,hK⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) T supportC
  have hKI : (Project.FirstOrderSemantics.reduct M).MemberSubset K I :=
    fun z hz => ((hK z).mp hz).elim (hTI z) (hSupportCI z)
  have hKSmall : Small K mu := (ForcingSupportSize.native_small hM K mu).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu
      ((ForcingSupportSize.native_small hM T mu).mp hTSmall)
      ((ForcingSupportSize.native_small hM supportC mu).mp hSupportMu) hK)
  have hAV : (Project.FirstOrderSemantics.reduct M).MemberSubset A V :=
    fun z hz => (hV z).mpr (range_antitone hv0 ((hA z).mp hz))
  have hEV : (Project.FirstOrderSemantics.reduct M).MemberSubset E V :=
    fun z hz => (hV z).mpr (range_antitone hv1 ((hE z).mp hz))
  have hRootInter : ConstructionPlacementPasting.Intersection A E root := by
    intro z
    exact (hRoot z).trans ((hInter z).symm.trans (and_congr (hA z).symm (hE z).symm))
  have hIndependent : ConstructionPlacementPasting.ImageIntersection alpha A beta A root := by
    intro z
    exact ((and_congr (range_permute hA hsaGraph).symm (range_permute hA hsbGraph).symm).trans
      ((hInd z).trans (hRoot z).symm)).symm
  have hAlphaK : ConstructionPlacementTriple.ImageInside alpha A K := by
    intro z hz
    exact (hK z).mpr (Or.inl ((hT z).mpr (range_antitone htAlpha ((range_permute hA hsaGraph).mpr hz))))
  have hBetaK : ConstructionPlacementTriple.ImageInside beta A K := by
    intro z hz
    exact (hK z).mpr (Or.inl ((hT z).mpr (range_antitone htBeta ((range_permute hA hsbGraph).mpr hz))))
  have hLarge : ¬ Small I mu := fun hi => hI.not_cardinalLessOrEqual (ZF.modelsKP hZF)
    ((ForcingSupportSize.native_small hM I mu).mp hi)
  obtain ⟨pi,rho,hpi,hrho,hPiA,hRhoA,hAgreeE,hPiK,hRhoK,hExact⟩ :=
    ConstructionPlacementTriple.three_copy_placement hM hChoice hw hMu hLarge
      ⟨hAV,hEV,hVI,hKI,hRootInter,hAlpha,hBeta,
        fun z hz => hFixAlpha z ((hRoot z).mp hz),
        fun z hz => hFixBeta z ((hRoot z).mp hz),hIndependent,hAlphaK,hBetaK⟩ hVSmall hKSmall
  have hPiS0 : CompositionGraph D pi s0 sa := composition_transport
    (fun y hy z => (agrees_iff hA0I hpi hAlpha hPiA y z ((hA y).mpr hy)).symm) hsaGraph
  have hRhoS0 : CompositionGraph D rho s0 sb := composition_transport
    (fun y hy z => (agrees_iff hA0I hrho hBeta hRhoA y z ((hA y).mpr hy)).symm) hsbGraph
  obtain ⟨shared,hShared,hPiS1⟩ := ForcingDiagramAction.exists_permute hM hpi hs1
  have hRhoS1 : CompositionGraph D rho s1 shared := composition_transport
    (fun y hy z => agrees_iff hEI hpi hrho hAgreeE y z ((hE y).mpr hy)) hPiS1
  obtain ⟨vP,hVP,hPiV⟩ := ForcingDiagramAction.exists_permute hM hpi hv
  obtain ⟨vR,hVR,hRhoV⟩ := ForcingDiagramAction.exists_permute hM hrho hv
  have hPiLe : ForcingDiagramOrder.Le D mul vP sa :=
    (ForcingDiagramOrder.le_iff hM hpi hv hs0 hPiV hPiS0).mp hv0
  have hRhoLe : ForcingDiagramOrder.Le D mul vR sb :=
    (ForcingDiagramOrder.le_iff hM hrho hv hs0 hRhoV hRhoS0).mp hv0
  have hPiShared : ForcingDiagramOrder.Le D mul vP shared :=
    (ForcingDiagramOrder.le_iff hM hpi hv hs1 hPiV hPiS1).mp hv1
  have hRhoShared : ForcingDiagramOrder.Le D mul vR shared :=
    (ForcingDiagramOrder.le_iff hM hrho hv hs1 hRhoV hRhoS1).mp hv1
  have hInterPi : ConstructionDiagramPlacements.RangeIntersection D vP t sa := by
    intro z
    constructor
    · rintro ⟨hvz,htz⟩
      exact (range_permute hA hsaGraph).mpr ((hPiK z).mp
        ⟨(range_permute hV hPiV).mp hvz,(hK z).mpr (Or.inl ((hT z).mpr htz))⟩)
    · intro hz
      exact ⟨(range_permute hV hPiV).mpr ((hPiK z).mpr ((range_permute hA hsaGraph).mp hz)).1,
        range_antitone htAlpha hz⟩
  have hInterRho : ConstructionDiagramPlacements.RangeIntersection D vR t sb := by
    intro z
    constructor
    · rintro ⟨hvz,htz⟩
      exact (range_permute hA hsbGraph).mpr ((hRhoK z).mp
        ⟨(range_permute hV hRhoV).mp hvz,(hK z).mpr (Or.inl ((hT z).mpr htz))⟩)
    · intro hz
      exact ⟨(range_permute hV hRhoV).mpr ((hRhoK z).mpr ((range_permute hA hsbGraph).mp hz)).1,
        range_antitone htBeta hz⟩
  have hInterPR : ConstructionDiagramPlacements.RangeIntersection D vP vR shared := by
    intro z
    exact (and_congr (range_permute hV hPiV) (range_permute hV hRhoV)).trans
      ((hExact z).trans (range_permute hE hPiS1).symm)
  obtain ⟨z,hZ,hZt,hZP,hZR⟩ := ConstructionDiagramThree.common_extension_three hM hChoice
    hw hMu hI hD hMergers hRow hm ht hVP hVR
    (ConstructionDiagramPlacements.exactOverlap_symm
      (ConstructionDiagramPlacements.exactOverlap_of_common hsa hPiLe htAlpha hInterPi))
    (ConstructionDiagramPlacements.exactOverlap_symm
      (ConstructionDiagramPlacements.exactOverlap_of_common hsb hRhoLe htBeta hInterRho))
    (ConstructionDiagramPlacements.exactOverlap_of_common hShared hPiShared hRhoShared hInterPR)
  obtain ⟨fP,gP,dP,hfP,hfgP,hgP,hggP,hdP,hImageP,hMovedP⟩ :=
    ConstructionCohenCompatibility.exists_moved hM hC hS hpi hd
  obtain ⟨fR,gR,dR,hfR,hfgR,hgR,hggR,hdR,hImageR,hMovedR⟩ :=
    ConstructionCohenCompatibility.exists_moved hM hC hS hrho hd
  obtain ⟨_,_,deltaP,_,_,_,_,hDeltaP,_,hMoveDeltaP⟩ :=
    ConstructionCohenCompatibility.exists_moved hM hC hS hpi hDelta
  obtain ⟨_,_,deltaR,_,_,_,_,hDeltaR,_,hMoveDeltaR⟩ :=
    ConstructionCohenCompatibility.exists_moved hM hC hS hrho hDelta
  have hActualA := actual_moved_condition hDeltaA
  have hActualB := actual_moved_condition hDeltaB
  obtain ⟨supportDelta,hSupportDelta,_,_⟩ := ConstructionCohenCompatibility.exists_support hM hw hC hS hDelta
  have hSupportDeltaA : (Project.FirstOrderSemantics.reduct M).MemberSubset supportDelta A := by
    intro i hi
    obtain ⟨k,b,he⟩ := (hSupportDelta i).mp hi
    exact ((ConstructionCohenCompatibility.restricted_entry hRestr).mp he).2
  have hDeltaPEq := ConstructionCohenCompatibility.permute_eq_of_agree hM hC hS hpi hAlpha
    hDelta hDeltaP hActualA.1 hSupportDelta
    (fun i j hi hij => hPiA i j (hSupportDeltaA i hi) hij) hMoveDeltaP hActualA.2
  have hDeltaREq := ConstructionCohenCompatibility.permute_eq_of_agree hM hC hS hrho hBeta
    hDelta hDeltaR hActualB.1 hSupportDelta
    (fun i j hi hij => hRhoA i j (hSupportDeltaA i hi) hij) hMoveDeltaR hActualB.2
  have hWithinV : Within d V := fun i k b he => (hV i).mpr (hWithin i k b he)
  have hTriggerP : ConstructionCohenCompatibility.Trigger pi V c A := by
    intro j hj hcj
    have hjK := (hK j).mpr (Or.inr ((hSupportC j).mpr hcj))
    exact (ConstructionPlacementTriple.image_congr hA0I hpi hAlpha hPiA j).mpr ((hPiK j).mp ⟨hj,hjK⟩)
  have hTriggerR : ConstructionCohenCompatibility.Trigger rho V c A := by
    intro j hj hcj
    have hjK := (hK j).mpr (Or.inr ((hSupportC j).mpr hcj))
    exact (ConstructionPlacementTriple.image_congr hA0I hrho hBeta hRhoA j).mpr ((hRhoK j).mp ⟨hj,hjK⟩)
  obtain ⟨a,ha,hca,hPa,hRa⟩ := ConstructionCohenCompatibility.comparison hM hw
    ⟨hC,hS,hpi,hrho,hd,hc,hdP,hdR,hWithinV,hRestr,hMoveDeltaP,hMoveDeltaR,hMovedP,hMovedR,
      hTriggerP,hTriggerR,fun j hp hr => (hExact j).mp ⟨hp,hr⟩,hAgreeE,
      hDeltaPEq.symm ▸ hcAlpha,hDeltaREq.symm ▸ hcBeta⟩
  obtain ⟨q,hq⟩ := KuratowskiZF.exists_code hM a z
  obtain ⟨cT,hcT⟩ := KuratowskiZF.exists_code hM c t
  obtain ⟨pP,hpP⟩ := KuratowskiZF.exists_code hM dP vP
  obtain ⟨pR,hpR⟩ := KuratowskiZF.exists_code hM dR vR
  exact ⟨pi,rho,q,hpi,hrho,hPiS0,hRhoS0,shared,vP,vR,dP,dR,a,z,cT,pP,pR,
    hShared,hPiS1,hRhoS1,hVP,hPiV,hVR,hRhoV,
    ⟨fP,gP,hfP,hfgP,hgP,hggP,hdP,hImageP,hMovedP⟩,
    ⟨fR,gR,hfR,hfgR,hgR,hggR,hdR,hImageR,hMovedR⟩,
    ha,hZ,hq,hcT,hpP,hpR,⟨a,z,c,t,hq,hcT,hca,hZt⟩,
    ⟨a,z,dP,vP,hq,hpP,hPa,hZP⟩,⟨a,z,dR,vR,hq,hpR,hRa,hZR⟩⟩

def actualMoved {m : Nat} (CC S w pi d q : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (ConstructionCohenCompatibility.movementResult CC.succ.succ S.succ.succ w.succ.succ
    pi.succ.succ d.succ.succ 1 0 q.succ.succ))

theorem actualMoved_freeClosed {m : Nat} (CC S w pi d q : Fin m) :
    (actualMoved CC S w pi d q).FreeClosed := by
  simp -implicitDefEqProofs [actualMoved,Definitional.Formula.FreeClosed,
    ConstructionCohenCompatibility.movementResult_freeClosed]

theorem actualMoved_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (CC S w pi d q : Fin m) :
    Project.Formula.satisfies env (actualMoved CC S w pi d q) ↔
      ActualMoved (env.bound CC) (env.bound S) (env.bound w) (env.bound pi) (env.bound d) (env.bound q) := by
  simp only [actualMoved,ActualMoved,Project.Formula.satisfies_exists_iff,
    ConstructionCohenCompatibility.movementResult_semantics hM]
  rfl

def boundary {m : Nat} (D CC S w s0 alpha beta d c : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+4) := fun i => i.succ.succ.succ.succ
  (.existsE (.existsE (.existsE (.existsE ((.conj (ProjectSyntax.encode id (ForcingStabilizerTransport.image
    (up s0) (up D) 3)) (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up S) (up w) 2))
    (.conj (ConstructionCohenCompatibility.restricted 3 (up d) 2) (.conj (actualMoved (up CC) (up S) (up w)
    (up alpha) 2 1) (.conj (actualMoved (up CC) (up S) (up w) (up beta) 2 0) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.subset 1 (up c))) (ProjectSyntax.encode id (Source.SetLanguage.subset 0 (up
    c))))))))))))))

theorem boundary_freeClosed {m : Nat} (D CC S w s0 alpha beta d c : Fin m) :
    (boundary D CC S w s0 alpha beta d c).FreeClosed := by
  simp -implicitDefEqProofs [boundary,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionCohenCompatibility.restricted_freeClosed,actualMoved_freeClosed]

theorem boundary_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D CC S w s0 alpha beta d c : Fin m) :
    Project.Formula.satisfies env (boundary D CC S w s0 alpha beta d c) ↔
      Boundary (env.bound D) (env.bound CC) (env.bound S) (env.bound w) (env.bound s0)
        (env.bound alpha) (env.bound beta) (env.bound d) (env.bound c) := by
  simp only [boundary,Boundary,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingStabilizerTransport.image_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ConstructionCohenCompatibility.restricted_semantics hM,actualMoved_semantics hM,
    ForcingLabelPermutations.subset_semantics (M := M)]
  rfl

def withinRange {m : Nat} (D v d : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.imp (ConstructionCohenCompatibility.entry d.succ.succ.succ 2 1 0)
    (ConstructionPlacementTriple.imageAt v.succ.succ.succ D.succ.succ.succ 2))))

theorem withinRange_freeClosed {m : Nat} (D v d : Fin m) : (withinRange D v d).FreeClosed := by
  simp -implicitDefEqProofs [withinRange,Definitional.Formula.FreeClosed,
    ConstructionCohenCompatibility.entry_freeClosed,ConstructionPlacementTriple.imageAt_freeClosed]

theorem withinRange_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D v d : Fin m) :
    Project.Formula.satisfies env (withinRange D v d) ↔ WithinRange (env.bound D) (env.bound v) (env.bound d) := by
  simp only [withinRange,WithinRange,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    ConstructionCohenCompatibility.entry_semantics hM,ConstructionPlacementTriple.imageAt_semantics hM]
  rfl

def inputs {m : Nat} (I J CC B S w D mul p s0 s1 v alpha beta sa sb d c t : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I J CC)) (.conj (ProjectSyntax.encode id
    (ForcingCohenCoordinates.cartesian CC B S)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection
    p D I)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection s0 D I)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.injection s1 D I)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.injection v D I)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection sa D
    I)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection sb D I)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.injection t D I)) (.conj (ConstructionDiagramPlacements.rangeIntersection D s0 s1 p)
    (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.le D mul v s0)) (.conj (ProjectSyntax.encode id
    (ForcingDiagramOrder.le D mul v s1)) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I
    alpha)) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I beta)) (.conj
    (ConstructionDiagramPlacements.fixesRange D p alpha) (.conj (ConstructionDiagramPlacements.fixesRange D p
    beta) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D alpha s0 sa)) (.conj
    (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D beta s0 sb)) (.conj
    (ConstructionDiagramPlacements.rangeIntersection D sa sb p) (.conj (ProjectSyntax.encode id
    (ForcingCohenConditions.condition S w d)) (.conj (ProjectSyntax.encode id
    (ForcingCohenConditions.condition S w c)) (.conj (withinRange D v d) (.conj (ProjectSyntax.encode id
    (ForcingDiagramOrder.le D mul t sa)) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.le D mul t sb))
    (boundary D CC S w s0 alpha beta d c)))))))))))))))))))))))))

theorem inputs_freeClosed {m : Nat} (I J CC B S w D mul p s0 s1 v alpha beta sa sb d c t : Fin m) :
    (inputs I J CC B S w D mul p s0 s1 v alpha beta sa sb d c t).FreeClosed := by
  simp -implicitDefEqProofs [inputs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionDiagramPlacements.rangeIntersection_freeClosed,ConstructionDiagramPlacements.fixesRange_freeClosed,
    withinRange_freeClosed,boundary_freeClosed]

theorem inputs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (I J CC B S w D mul p s0 s1 v alpha beta sa sb d c t : Fin m) :
    Project.Formula.satisfies env (inputs I J CC B S w D mul p s0 s1 v alpha beta sa sb d c t) ↔
      Inputs (env.bound I) (env.bound J) (env.bound CC) (env.bound B) (env.bound S) (env.bound w)
        (env.bound D) (env.bound mul) (env.bound p) (env.bound s0) (env.bound s1) (env.bound v)
        (env.bound alpha) (env.bound beta) (env.bound sa) (env.bound sb) (env.bound d) (env.bound c) (env.bound t) := by
  simp only [inputs,Inputs,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionDiagramPlacements.rangeIntersection_semantics hM,ForcingDiagramOrder.le_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),ConstructionDiagramPlacements.fixesRange_semantics hM,
    ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    withinRange_semantics hM,boundary_semantics hM]
  rfl

def result {m : Nat} (D I mul CC S w s0 s1 v sa sb d c t pi rho q : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+10) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi)) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.permutation I rho)) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.compositionGraph D pi s0 sa)) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.compositionGraph D rho s0 sb)) ((.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj (ProjectSyntax.encode id
    (Source.SetLanguage.injection 9 (up D) (up I))) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.compositionGraph (up D) (up pi) (up s1) 9)) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.compositionGraph (up D) (up rho) (up s1) 9)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.injection 8 (up D) (up I))) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.compositionGraph (up D) (up pi) (up v) 8)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.injection 7 (up D) (up I))) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.compositionGraph (up D) (up rho) (up v) 7)) (.conj (actualMoved (up CC) (up S) (up
    w) (up pi) (up d) 6) (.conj (actualMoved (up CC) (up S) (up w) (up rho) (up d) 5) (.conj
    (ProjectSyntax.encode id (ForcingCohenConditions.condition (up S) (up w) 4)) (.conj (ProjectSyntax.encode
    id (Source.SetLanguage.injection 3 (up D) (up I))) (.conj (PureKuratowskiProject.code (.bound (up q))
    (.bound 4) (.bound 3)) (.conj (PureKuratowskiProject.code (.bound 2) (.bound (up c)) (.bound (up t)))
    (.conj (PureKuratowskiProject.code (.bound 1) (.bound 6) (.bound 8)) (.conj (PureKuratowskiProject.code
    (.bound 0) (.bound 5) (.bound 7)) (.conj (ProjectSyntax.encode id (ForcingProductAction.le (up D) (up mul)
    (up q) 2)) (.conj (ProjectSyntax.encode id (ForcingProductAction.le (up D) (up mul) (up q) 1))
    (ProjectSyntax.encode id (ForcingProductAction.le (up D) (up mul) (up q)
    0)))))))))))))))))))))))))))))))))))

theorem result_freeClosed {m : Nat} (D I mul CC S w s0 s1 v sa sb d c t pi rho q : Fin m) :
    (result D I mul CC S w s0 s1 v sa sb d c t pi rho q).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    actualMoved_freeClosed,PureKuratowskiProject.code]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (D I mul CC S w s0 s1 v sa sb d c t pi rho q : Fin m) :
    Project.Formula.satisfies env (result D I mul CC S w s0 s1 v sa sb d c t pi rho q) ↔
      Result (env.bound D) (env.bound I) (env.bound mul) (env.bound CC) (env.bound S) (env.bound w)
        (env.bound s0) (env.bound s1) (env.bound v) (env.bound sa) (env.bound sb) (env.bound d) (env.bound c)
        (env.bound t) (env.bound pi) (env.bound rho) (env.bound q) := by
  simp only [result,Result,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),actualMoved_semantics hM,
    ForcingCohenConditions.condition_semantics (M := M),KuratowskiZF.code_correct hM,
    ForcingProductAction.le_semantics (M := M),Project.Term.eval_bound]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 28
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 28))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 28)) (.bound 1)) (.imp
    (ConstructionSaturationIndex.hartogs (1 : Fin 28) 12) (.imp (ProjectSyntax.encode id
    (ForcingSupportSize.small (4 : Fin 28) 1)) (.imp (ConstructionSaturationMergers.allMergers (0 : Fin 28) 2
    3) (.imp (ConstructionTowerHistory.row (2 : Fin 28) 3 4 5 6 7 8 9 10 11 3) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (4 : Fin 28) 5 6)) (.imp (inputs (12 : Fin 28) 13 15 14 16 0 4 5 17
    18 19 20 21 22 23 24 25 26 27) ((.existsE (.existsE (.existsE (result (4 : Fin 28).succ.succ.succ (12 :
    Fin 28).succ.succ.succ (5 : Fin 28).succ.succ.succ (15 : Fin 28).succ.succ.succ (16 : Fin
    28).succ.succ.succ (0 : Fin 28).succ.succ.succ (18 : Fin 28).succ.succ.succ (19 : Fin 28).succ.succ.succ
    (20 : Fin 28).succ.succ.succ (23 : Fin 28).succ.succ.succ (24 : Fin 28).succ.succ.succ (25 : Fin
    28).succ.succ.succ (26 : Fin 28).succ.succ.succ (27 : Fin 28).succ.succ.succ 2 1 0)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      inputs_freeClosed,result_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    inputs_semantics hM,result_semantics hM,Project.Term.eval_bound]
  exact fun hw hMu hI hD hMergers hRow hm h =>
    descent_comparison_placement hM hChoice hw hMu hI hD hMergers hRow hm h

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
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
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp (construction_models hL hChoice)

end PPAC.Migration.ConstructionDescentPlacement
