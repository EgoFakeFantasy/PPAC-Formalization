/- Pinned Placements.extend_embedding_cover and Diagrams.extend_through.
Consumer: AvailableRecords.classRepresentationSet_denseBelow. Preserve all
prescribed edges and cover the designated set; reuse native inverse/range,
exact joining, and the existing whole-carrier embedding extension. -/
import PPAC.Migration.ConstructionDiagramAmalgamation

namespace PPAC.Migration.ConstructionDiagramCoverage
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Injection Small)
open ForcingDiagramOrder (Product Sub LeftInjection)
open ConstructionPlacementExtensions (Difference Extends)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Covers (D J r : M.Carrier .set) : Prop :=
  ∀ y, (Project.FirstOrderSemantics.reduct M).mem y J →
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.PairMember M x y r

/-- Only packages the already existing native range and inverse constructors. -/
private theorem range_inverse (hM : FirstOrder.Theory.Models M nativeZF)
    {D I f : M.Carrier .set} (hf : Injection D I f) :
    ∃ A inverse, (∀ y, (Project.FirstOrderSemantics.reduct M).mem y A ↔
      ∃ x, PureKuratowski.PairMember M x y f) ∧ Injection A D inverse ∧
      ∀ y x, PureKuratowski.PairMember M y x inverse ↔ PureKuratowski.PairMember M x y f := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hn := (ForcingSupportSize.native_injection hM D I f).mp hf
  obtain ⟨A,hA⟩ := ZF.exists_range_of_setFunction hZF pair hn.1.1 hn.1.2.1
  have hb : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo pair f D A := by
    refine ⟨⟨⟨hn.1.1,hn.1.2.1,?_⟩,hn.2⟩,?_⟩
    · intro x hx
      obtain ⟨y,_,hxy⟩ := hn.1.2.2 x hx
      exact ⟨y,(hA y).mpr ⟨x,hxy⟩,hxy⟩
    · intro y hy
      obtain ⟨x,hxy⟩ := (hA y).mp hy
      exact ⟨x,hn.1.input_mem_of_pairMember hxy,hxy⟩
  obtain ⟨inverse,hi,he⟩ := ZF.exists_inverseBijectionWithPairs hZF pair hb
  exact ⟨A,inverse,hA,(ForcingSupportSize.native_injection hM A D inverse).mpr hi.1,he⟩

/-- Source partial embedding with prescribed range coverage. Arrange the
uncovered labels in the spare domain first, then use the existing extension;
this reuses its complement-cardinal argument without duplicating it. -/
theorem extend_embedding_cover (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu D I U C J e f : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu) (hD : Small D mu)
    (he : Injection D I e) (hf : Injection U I f)
    (hUD : (Project.FirstOrderSemantics.reduct M).MemberSubset U D)
    (hC : Difference D U C) (hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset J I)
    (hJ : Small J C) :
    ∃ r, Injection D I r ∧ Extends f r ∧ Covers D J r := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨R,_,hR,_,_⟩ := range_inverse hM hf
  obtain ⟨K,hK⟩ := KP.difference_exists_d (ZF.modelsKP hZF) R J
  obtain ⟨k,hk⟩ := ForcingSupportSize.small_subset hM (fun y hy => ((hK y).mp hy).1) hJ
  obtain ⟨V,g,hV,hg,hInv⟩ := range_inverse hM hk
  have hVD : (Project.FirstOrderSemantics.reduct M).MemberSubset V D := by
    intro x hx
    obtain ⟨y,hyx⟩ := (hV x).mp hx
    exact ((hC x).mp (hk.1.2 y x hyx)).1
  have hgI : Injection V I g := ⟨⟨hg.1.1,fun x y hxy =>
    hJI y ((hK y).mp (hg.1.2 x y hxy)).1⟩,hg.2⟩
  obtain ⟨A,hA⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) U V
  have hAD : (Project.FirstOrderSemantics.reduct M).MemberSubset A D :=
    fun x hx => ((hA x).mp hx).elim (hUD x) (hVD x)
  have hDisj : (Project.FirstOrderSemantics.reduct M).IsDisjoint U V := by
    intro x hx
    obtain ⟨y,hyx⟩ := (hV x).mp hx.2
    exact ((hC x).mp (hk.1.2 y x hyx)).2 hx.1
  obtain ⟨joined,hJoined,hEdges⟩ := ConstructionPlacementExtensions.join_injections hM hA hDisj
    ((ForcingSupportSize.native_injection hM U I f).mp hf)
    ((ForcingSupportSize.native_injection hM V I g).mp hgI)
    (fun x y z hx hy => ((hK z).mp (hg.1.2 y z hy)).2 ((hR z).mpr ⟨x,hx⟩))
  obtain ⟨r,hr,hExtend⟩ := ConstructionDiagramAmalgamation.extend_embedding hM hChoice hw hMu hLarge hD he
    ((ForcingSupportSize.native_injection hM A I joined).mpr hJoined) hAD
  refine ⟨r,hr,fun x y hxy => hExtend x y ((hEdges x y).mpr (Or.inl hxy)),?_⟩
  intro y hy
  by_cases hyR : (Project.FirstOrderSemantics.reduct M).mem y R
  · obtain ⟨x,hxy⟩ := (hR y).mp hyR
    exact ⟨x,hUD x (ForcingConditionGraphs.function_input hf.1.1 hxy),
      hExtend x y ((hEdges x y).mpr (Or.inl hxy))⟩
  · have hyK := (hK y).mpr ⟨hy,hyR⟩
    obtain ⟨x,hyx,_⟩ := hk.1.1.2 y hyK
    have hxV := (hV x).mpr ⟨y,hyx⟩
    exact ⟨x,hVD x hxV,hExtend x y ((hEdges x y).mpr (Or.inr ((hInv x y).mpr hyx)))⟩

/-- Instantiate source extend_through at the SAME cardinal/complement data
already returned by the saturated monoid. -/
theorem extend_through (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu D I mul mark p J : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu) (hCard : ConstructionSaturationCardinals.Cardinals hM D mul mark mu)
    (hLeft : LeftInjection D mul mark) (hp : Injection D I p)
    (hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset J I) (hJ : Small J mu) :
    ∃ r, Injection D I r ∧ Sub D mul r mark p ∧ Covers D J r := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨dToMu,hdToMu⟩ := hCard.1
  have hD : Small D mu := (ForcingSupportSize.native_small hM D mu).mpr ⟨dToMu,hdToMu.1⟩
  obtain ⟨C,hC,hCMu⟩ := hCard.2
  obtain ⟨muToC,hMuToC⟩ := hCMu.symm hZF pair
  obtain ⟨jToMu,hJToMu⟩ := (ForcingSupportSize.native_small hM J mu).mp hJ
  have hJC : Small J C := (ForcingSupportSize.native_small hM J C).mpr
    (ZF.exists_compositionInjection hZF pair hJToMu hMuToC.1)
  obtain ⟨identity,hIdentity,hId⟩ := ForcingConditionGraphs.exists_identity hM D
  obtain ⟨left,hleft,hSub⟩ := ForcingDiagramOrder.exists_sub hM hLeft ⟨hIdentity.1,hIdentity.2.1⟩
  have hLeftEdges x y : PureKuratowski.PairMember M x y left ↔
      (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product mul mark x y := by
    constructor
    · intro hxy
      obtain ⟨hx,z,_,hxz,hzy⟩ := (hSub x y).mp hxy
      exact ⟨hx,((hId z y).mp hzy).2 ▸ hxz⟩
    · rintro ⟨hx,hxy⟩
      obtain ⟨z,hz,hxz⟩ := hLeft.1 x hx
      have hzy := hLeft.2.1 x z y hx hxz hxy
      exact (hSub x y).mpr ⟨hx,y,hzy ▸ hz,hxy,(hId y y).mpr ⟨hzy ▸ hz,rfl⟩⟩
  obtain ⟨U,inverse,hU,hInverse,hInv⟩ := range_inverse hM hleft
  have hUD : (Project.FirstOrderSemantics.reduct M).MemberSubset U D := by
    intro y hy
    obtain ⟨x,hxy⟩ := (hU y).mp hy
    exact hleft.1.2 x y hxy
  have hUC : Difference D U C := by
    intro y
    refine (hC y).trans (and_congr Iff.rfl ?_)
    apply not_congr
    exact ⟨fun ⟨x,hx,hxy⟩ => (hU y).mpr ⟨x,(hLeftEdges x y).mpr ⟨hx,hxy⟩⟩,
      fun hy => by obtain ⟨x,hxy⟩ := (hU y).mp hy; exact ⟨x,(hLeftEdges x y).mp hxy⟩⟩
  have hInvNative := (ForcingSupportSize.native_injection hM U D inverse).mp hInverse
  have hpNative := (ForcingSupportSize.native_injection hM D I p).mp hp
  obtain ⟨f,hf,hComp⟩ := ZF.exists_compositionFunction hZF pair hInvNative.1 hpNative.1
  have hfi : Injection U I f := by
    apply (ForcingSupportSize.native_injection hM U I f).mpr
    refine ⟨hf,?_⟩
    intro y z a hy hz
    obtain ⟨_,x,hyx,hxa⟩ := (hComp y a).mp hy
    obtain ⟨_,v,hzv,hva⟩ := (hComp z a).mp hz
    have hxv := hp.2 x v a hxa hva
    exact hInverse.2 y z x hyx (hxv.symm ▸ hzv)
  obtain ⟨r,hr,hExt,hCover⟩ := extend_embedding_cover hM hChoice hw hMu hLarge hD hp hfi hUD hUC hJI hJC
  refine ⟨r,hr,?_,hCover⟩
  intro x z
  constructor
  · intro hxz
    have hx := ForcingConditionGraphs.function_input hp.1.1 hxz
    obtain ⟨y,hy,hxy⟩ := hLeft.1 x hx
    have hxy' := (hLeftEdges x y).mpr ⟨hx,hxy⟩
    exact ⟨hx,y,hy,hxy,hExt y z ((hComp y z).mpr ⟨(hU y).mpr ⟨x,hxy'⟩,x,(hInv y x).mpr hxy',hxz⟩)⟩
  · rintro ⟨hx,y,_,hxy,hyz⟩
    obtain ⟨v,hxv,_⟩ := hp.1.1.2 x hx
    have hxy' := (hLeftEdges x y).mpr ⟨hx,hxy⟩
    have hyv := hExt y v ((hComp y v).mpr ⟨(hU y).mpr ⟨x,hxy'⟩,x,(hInv y x).mpr hxy',hxv⟩)
    have hzv := ForcingConditionGraphs.function_unique hr.1.1 hyz hyv
    exact hzv.symm ▸ hxv

def covers {k : Nat} (D J r : Fin k) : Project.Formula 1 k :=
  .forallE (.imp (.mem (.bound 0) (.bound J.succ))
    (ConstructionPlacementTriple.imageAt r.succ D.succ 0))

theorem covers_freeClosed {k : Nat} (D J r : Fin k) : (covers D J r).FreeClosed := by
  simp -implicitDefEqProofs [covers,Definitional.Formula.FreeClosed,ConstructionPlacementTriple.imageAt_freeClosed]

theorem covers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (D J r : Fin k) :
    Project.Formula.satisfies env (covers D J r) ↔ Covers (env.bound D) (env.bound J) (env.bound r) := by
  simp only [covers,Covers,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,ConstructionPlacementTriple.imageAt_semantics hM]
  rfl

end PPAC.Migration.ConstructionDiagramCoverage
