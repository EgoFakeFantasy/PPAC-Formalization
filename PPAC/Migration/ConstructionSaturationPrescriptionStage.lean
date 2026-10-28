/- Pinned SaturatedMonoids.prescription_stage:99.
Keep arbitrary internal finite optional start tables, including absent entries,
diagonals and n=0. Valid is NOT a premise of the stage lift.
Reuse existing native graph constructors, cardinal bounds and SAME tower cover. -/
import PPAC.Migration.ConstructionSaturationProbes

namespace PPAC.Migration.ConstructionSaturationPrescriptionStage
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid row_field)
open ForcingSupportSize (MapsTo Small)
open ForcingConditionGraphs (function_input function_unique)
open ConstructionMergerRelations (Prescription Start)
open ConstructionRequestCarrier (WellFormed)
open ConstructionMergerPrescriptionMap (Graph Mapped)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem prescription_small (hM : FirstOrder.Theory.Models M nativeZF)
    {w n N P : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hWell : WellFormed n N P) (hP : Prescription n N P) : Small P w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let rawM := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have hWC := ExistingCardinalBounds.omega_cardinal_l I hZF hw
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF I w
  have hWI : rawM.IsInfiniteCardinal I w w := ⟨hWC,id,hId.1⟩
  obtain ⟨WW,hWW⟩ := ZF.exists_cartesianProduct hZF I w w
  have hWWsmall := ExistingCardinalBounds.infinite_product_l I hZF hw hWI ⟨id,hId.1⟩ ⟨id,hId.1⟩ hWW
  let schema : Project.BinarySchema 0 := {
    body := .existsE (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,PureKuratowskiProject.code] }
  let env : SetTheory.Env rawM 0 := ⟨Fin.elim0,fun _ => P⟩
  have he row key : schema.denote env row key ↔ ∃ ab, PureKuratowski.Code M row key ab := by
    simp only [Project.BinarySchema.denote,schema,Project.Formula.satisfies_exists_iff,KuratowskiZF.code_correct hM]
    rfl
  obtain ⟨index,hIndex,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I schema env
    (source := P) (target := WW)
    (by
      intro row hrow
      obtain ⟨i,j,a,b,ij,ab,hrow,_,_,_,_,_,_⟩ := hWell row hrow
      exact ⟨ij,(he row ij).mpr ⟨ab,hrow⟩⟩)
    (by
      intro row _ key key' hk hk'
      obtain ⟨ab,hab⟩ := (he row key).mp hk
      obtain ⟨ab',hab'⟩ := (he row key').mp hk'
      exact (PureKuratowski.code_injective hab hab').1)
    (by
      intro row key hrow hkey
      obtain ⟨ab,hcode⟩ := (he row key).mp hkey
      obtain ⟨i,j,a,b,ij,ab',hc,hij,hab,hi,hj,_,_⟩ := hWell row hrow
      have ek := (PureKuratowski.code_injective hcode hc).1
      exact ek.symm ▸ (hWW ij).mpr ⟨i,hWC.1.transitive n hn i hi,j,hWC.1.transitive n hn j hj,hij⟩)
  have hInjection : rawM.IsSetInjectionFromTo I index P WW := by
    refine ⟨hIndex,?_⟩
    intro row row' key hr hr'
    obtain ⟨hrow,hrowKey⟩ := (hGraph row key).mp hr
    obtain ⟨hrow',hrowKey'⟩ := (hGraph row' key).mp hr'
    obtain ⟨ab,hcode⟩ := (he row key).mp hrowKey
    obtain ⟨ab',hcode'⟩ := (he row' key).mp hrowKey'
    have hab := ConstructionRequestPadding.prescription_single hM hWell hP
      ⟨row,hcode,hrow⟩ ⟨row',hcode',hrow'⟩
    subst ab'
    exact KuratowskiZF.code_unique hM hcode hcode'
  obtain ⟨toW,hToW⟩ := hWWsmall
  exact (ForcingSupportSize.native_small hM P w).mpr
    (ZF.exists_compositionInjection hZF I hInjection hToW)

def Component (right : Bool) (row value : M.Carrier .set) : Prop :=
  ∃ key ab a b, PureKuratowski.Code M row key ab ∧ PureKuratowski.Code M ab a b ∧
    value = if right then b else a

def component {m : Nat} (right : Bool) (row value : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (PureKuratowskiProject.code (.bound row.succ.succ.succ.succ) (.bound 3) (.bound 2))
      (.conj (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0))
        (Project.Formula.extensionalEq (.bound value.succ.succ.succ.succ) (.bound (if right then 0 else 1))))))))

theorem component_freeClosed {m : Nat} (right : Bool) (row value : Fin m) :
    (component right row value).FreeClosed := by
  cases right <;> simp -implicitDefEqProofs [component,Definitional.Formula.FreeClosed,
    PureKuratowskiProject.code,Project.Formula.extensionalEq]

theorem component_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (right : Bool) (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (row value : Fin m) :
    Project.Formula.satisfies env (component right row value) ↔ Component right (env.bound row) (env.bound value) := by
  cases right <;> simp only [component,Component,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,KuratowskiZF.code_correct hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound] <;> rfl

theorem component_unique {right : Bool} {row value other : M.Carrier .set}
    (h : Component right row value) (h' : Component right row other) : value = other := by
  obtain ⟨key,ab,a,b,hrow,hab,rfl⟩ := h
  obtain ⟨key',ab',a',b',hrow',hab',rfl⟩ := h'
  have he := (PureKuratowski.code_injective hrow hrow').2
  subst ab'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hab hab'
  rfl

theorem component_function (hM : FirstOrder.Theory.Models M nativeZF)
    (right : Bool) {n N P : M.Carrier .set} (hWell : WellFormed n N P) :
    ∃ f, MapsTo P N f ∧ ∀ row value, PureKuratowski.PairMember M row value f ↔
      (Project.FirstOrderSemantics.reduct M).mem row P ∧ Component right row value := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let schema : Project.BinarySchema 0 :=
    { body := component right 1 0, freeClosed := component_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 := ⟨Fin.elim0,fun _ => P⟩
  have he row value : schema.denote env row value ↔ Component right row value :=
    component_semantics hM right (env.push row |>.push value) 1 0
  obtain ⟨f,hf,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM) schema env
    (source := P) (target := N)
    (by
      intro row hrow
      obtain ⟨i,j,a,b,key,ab,hCode,_,hAB,_,_,_,_⟩ := hWell row hrow
      exact ⟨if right then b else a,(he row _).mpr ⟨key,ab,a,b,hCode,hAB,rfl⟩⟩)
    (by intro row _ x y hx hy; exact component_unique ((he row x).mp hx) ((he row y).mp hy))
    (by
      intro row value hrow hValue
      obtain ⟨i,j,a,b,key,ab,hCode,_,hAB,_,_,ha,hb⟩ := hWell row hrow
      have eq := component_unique ((he row value).mp hValue) (show Component right row (if right then b else a) from ⟨key,ab,a,b,hCode,hAB,rfl⟩)
      rw [eq]
      cases right <;> assumption)
  exact ⟨f,(ForcingSupportSize.native_mapsTo hM P N f).mpr hf,
    fun row value => (hGraph row value).trans (and_congr_right fun _ => he row value)⟩

theorem parameters (hM : FirstOrder.Theory.Models M nativeZF)
    {w n N P : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hWell : WellFormed n N P) (hP : Prescription n N P) :
    ∃ S, (Project.FirstOrderSemantics.reduct M).MemberSubset S N ∧ Small S w ∧
      ∀ i j a b, Start P i j a b →
        (Project.FirstOrderSemantics.reduct M).mem a S ∧ (Project.FirstOrderSemantics.reduct M).mem b S := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let rawM := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have hSmall := prescription_small hM hw hn hWell hP
  have hWC := ExistingCardinalBounds.omega_cardinal_l I hZF hw
  have image (right : Bool) : ∃ f R, MapsTo P N f ∧
      (∀ row value, PureKuratowski.PairMember M row value f ↔ rawM.mem row P ∧ Component right row value) ∧
      rawM.IsRangeOf I R f ∧ rawM.CardinalLessOrEqual I R w := by
    obtain ⟨f,hf,hGraph⟩ := component_function hM right hWell
    have hNative := (ForcingSupportSize.native_mapsTo hM P N f).mp hf
    obtain ⟨R,hR⟩ := ZF.exists_range_of_setFunction hZF I hNative.1 hNative.2.1
    have hToR : rawM.IsSetFunctionFromTo I f P R := ⟨hNative.1,hNative.2.1,fun row hrow => by
      obtain ⟨x,_,hx⟩ := hNative.2.2 row hrow
      exact ⟨x,(hR x).mpr ⟨row,hx⟩,hx⟩⟩
    have hRSmall := ExistingOrdinalImage.ordinal_image_bound_l I hZF hWC.1
      ((ForcingSupportSize.native_small hM P w).mp hSmall) hToR (fun x hx => by
        obtain ⟨row,hrx⟩ := (hR x).mp hx
        exact ⟨row,hNative.input_mem_of_pairMember hrx,hrx⟩)
    exact ⟨f,R,hf,hGraph,hR,hRSmall⟩
  obtain ⟨left,RL,hLeft,hLeftGraph,hRL,hRLSmall⟩ := image false
  obtain ⟨right,RR,hRight,hRightGraph,hRR,hRRSmall⟩ := image true
  obtain ⟨S,hS⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) RL RR
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF I w
  have hWI : rawM.IsInfiniteCardinal I w w := ⟨hWC,id,hId.1⟩
  refine ⟨S,?_,(ForcingSupportSize.native_small hM S w).mpr
    (ExistingCardinalBounds.infinite_union_two_l I hZF hw hWI hRLSmall hRRSmall hS),?_⟩
  · intro x hx
    rcases (hS x).mp hx with hx | hx
    · obtain ⟨row,hrow⟩ := (hRL x).mp hx
      exact hLeft.2 row x hrow
    · obtain ⟨row,hrow⟩ := (hRR x).mp hx
      exact hRight.2 row x hrow
  · intro i j a b hStart
    obtain ⟨ab,hab,key,hkey,row,hrow,hr⟩ := hStart
    exact ⟨(hS a).mpr (Or.inl ((hRL a).mpr ⟨row,(hLeftGraph row a).mpr
        ⟨hr,key,ab,a,b,hrow,hab,rfl⟩⟩)),
      (hS b).mpr (Or.inr ((hRR b).mpr ⟨row,(hRightGraph row b).mpr
        ⟨hr,key,ab,a,b,hrow,hab,rfl⟩⟩))⟩

/-- Recover the complete literal graph from the optional-start correspondence,
using the target's already required well-formed representation. -/
theorem graph_of_mapped (hM : FirstOrder.Theory.Models M nativeZF)
    {n N P f PN : M.Carrier .set} (hWell : WellFormed n N PN) (hMap : Mapped P f PN) :
    Graph P f PN := by
  intro q
  constructor
  · intro hq
    obtain ⟨i,j,fa,fb,key,ab,hqCode,hKey,hAB,_,_,_,_⟩ := hWell q hq
    have hStart : Start PN i j fa fb := ⟨ab,hAB,key,hKey,q,hqCode,hq⟩
    obtain ⟨a,b,hStart,hafa,hbfb⟩ := (hMap i j fa fb).mp hStart
    exact ⟨i,j,a,b,fa,fb,key,ab,hKey,hAB,hqCode,hStart,hafa,hbfb⟩
  · rintro ⟨i,j,a,b,fa,fb,key,ab,hKey,hAB,hqCode,hStart,hafa,hbfb⟩
    obtain ⟨ab',hAB',key',hKey',row,hRow,hr⟩ :=
      (hMap i j fa fb).mpr ⟨a,b,hStart,hafa,hbfb⟩
    have ek := KuratowskiZF.code_unique hM hKey hKey'
    have ea := KuratowskiZF.code_unique hM hAB hAB'
    subst key' ab'
    exact (KuratowskiZF.code_unique hM hqCode hRow).symm ▸ hr

def MergerStage (history F kappa n P : M.Carrier .set) : Prop :=
  ∃ j D mul e mark H C incoming base leg P0 S lift identity,
    (Project.FirstOrderSemantics.reduct M).mem j kappa ∧
    Row history j D mul e mark H C incoming base j ∧ ForcingDiagramOrder.Product F j kappa leg ∧
    WellFormed n D P0 ∧ Prescription n D P0 ∧ Graph P0 leg P ∧
    Prescription n S P ∧ MapsTo S D lift ∧ ForcingConditionGraphs.IdentityGraph S identity ∧
    ConstructionProbeMappedPath.NodeMap lift leg identity ∧ Graph P lift P0

theorem prescription_stage (hM : FirstOrder.Theory.Models M nativeZF)
    {w history F kappa n P N mulN eN markN HN CN incoming base : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hCover : ConstructionSaturationCover.Covered w history F kappa)
    (hRow : Row history kappa N mulN eN markN HN CN incoming base kappa)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hWell : WellFormed n N P) (hP : Prescription n N P) : MergerStage history F kappa n P := by
  obtain ⟨S,hSub,hSmall,hParameters⟩ := parameters hM hw hn hWell hP
  obtain ⟨identity,hPerm,hIdentity⟩ := ForcingConditionGraphs.exists_identity hM S
  have hIdentityMaps : MapsTo S N identity := ⟨hPerm.1.1,fun x y hxy => hSub y (hPerm.1.2 x y hxy)⟩
  obtain ⟨j,D0,mul0,e0,mark0,H0,C0,in0,base0,leg,lift,hj,hRow0,hLeg,hLift,hComposition⟩ :=
    hCover N mulN eN markN HN CN incoming base S identity hRow hSmall hIdentityMaps
  have hPS : Prescription n S P := by
    refine ⟨?_,hP.2⟩
    intro i j a b hStart
    have hi := hP.1 i j a b hStart
    have hS := hParameters i j a b hStart
    exact ⟨hi.1,hi.2.1,hS.1,hS.2⟩
  obtain ⟨P0,hForward⟩ := ConstructionMergerPrescriptionMap.exists_graph hM hPS hLift
  have hMapped := ConstructionMergerPrescriptionMap.mapped hM hForward
  have hP0 := ConstructionMergerPrescriptionMap.prescription hPS hLift hMapped
  have hWell0 := ConstructionRequestCarrier.wellFormed_of_graph hForward hP0
  have retract {x y} (hx : (Project.FirstOrderSemantics.reduct M).mem x S)
      (hxy : PureKuratowski.PairMember M x y lift) : PureKuratowski.PairMember M y x leg := by
    obtain ⟨z,hxz,hzx⟩ := (hComposition x x).mp ((hIdentity x x).mpr ⟨hx,rfl⟩)
    exact (function_unique hLift.1 hxz hxy) ▸ hzx
  have hBack : Mapped P0 leg P := by
    intro i j a b
    constructor
    · intro hStart
      obtain ⟨ha,hb⟩ := hParameters i j a b hStart
      obtain ⟨a0,haa0,_⟩ := hLift.1.2 a ha
      obtain ⟨b0,hbb0,_⟩ := hLift.1.2 b hb
      exact ⟨a0,b0,(hMapped i j a0 b0).mpr ⟨a,b,hStart,haa0,hbb0⟩,
        retract ha haa0,retract hb hbb0⟩
    · rintro ⟨a0,b0,hStart,ha0a,hb0b⟩
      obtain ⟨a',b',hOld,ha'a0,hb'b0⟩ := (hMapped i j a0 b0).mp hStart
      have ea := ((hIdentity a' a).mp ((hComposition a' a).mpr ⟨a0,ha'a0,ha0a⟩)).2
      have eb := ((hIdentity b' b).mp ((hComposition b' b).mpr ⟨b0,hb'b0,hb0b⟩)).2
      exact ea ▸ eb ▸ hOld
  exact ⟨j,D0,mul0,e0,mark0,H0,C0,in0,base0,leg,P0,S,lift,identity,
    hj,hRow0,hLeg,hWell0,hP0,graph_of_mapped hM hWell hBack,hPS,hLift,hIdentity,hComposition,hForward⟩


end PPAC.Migration.ConstructionSaturationPrescriptionStage
