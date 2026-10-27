/- Pinned DirectLimits.ConservativeLimit.of_conservative:86.
Reuse actual limit monoid and the source conservative transition premise. -/
import PPAC.Migration.ConstructionDirectedFactors

namespace PPAC.Migration.ConstructionDirectedConservative
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family ProductAt HomLaws ConicalFamily)
open ConstructionDirectedConservativeData
open ConstructionDirectedLimitCarrier (Representatives Carrier Projection EqualityLaw)
open ConstructionDirectedProduct (Graph)
open ConstructionDirectedMonoid (UnitImage)
open ConstructionProbeConservative (Conservative)
open ConstructionDirectedFactors
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeAlphabetMap (FactorConservation DivisionReflection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {J E Domains F Muls Units C L projection B G unit : M.Carrier .set}

/-- Literal common-future reduction in source of_conservative. The comparison
stage and its canonical map are constructed, never assumed conservative. -/
theorem comparison_stage (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    {i D mul x y a fx fy fa w : M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y D)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a D)
    (hxf : Product projection i x fx) (hyf : Product projection i y fy) (haf : Product projection i a fa)
    (hw : (Project.FirstOrderSemantics.reduct M).mem w L) :
    ∃ Dk mk t gk xk yk ak wk, Conservative D Dk mul mk t ∧
      PureKuratowski.PairMember M x xk t ∧ PureKuratowski.PairMember M y yk t ∧
      PureKuratowski.PairMember M a ak t ∧ DivisionReflection Dk L mk G gk ∧
      PureKuratowski.PairMember M xk fx gk ∧ PureKuratowski.PairMember M yk fy gk ∧
      PureKuratowski.PairMember M ak fa gk ∧ (Project.FirstOrderSemantics.reduct M).mem wk Dk ∧
      PureKuratowski.PairMember M wk w gk := by
  obtain ⟨j,z,hz,hzw⟩ := ConstructionDirectedLimitCarrier.representative hC hL hP hw
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hi hz.1
  obtain ⟨xk,hxx⟩ := hT.1 i k x ⟨hi,D,hD,hx⟩ hk hik
  obtain ⟨Dk,mk,ek,hDk,hmk,hek,_⟩ := ConstructionDirectedMonoidData.family_at hFam hk
  obtain ⟨t,hFt,htx⟩ := hxx.2.2
  have hCov := hCons i k D Dk mul mk t hi hk hik hD hDk hm hmk hFt
  obtain ⟨yk,hyk,hty,hyy⟩ := transition_value hCov.1 hi hk hD hDk hFt hy
  obtain ⟨ak,hak,hta,haa⟩ := transition_value hCov.1 hi hk hD hDk hFt ha
  have hxp := projected_transition hM hC hp hE hT hEq hik hxx hxf
  have hyp := projected_transition hM hC hp hE hT hEq hik hyy hyf
  have hap := projected_transition hM hC hp hE hT hEq hik haa haf
  obtain ⟨wk,hwk,_,hwp⟩ := ConstructionDirectedLimitCarrier.projected_later hM hC hp hE hT hEq hk hjk hzw
  obtain ⟨gk,hgk,hGK,_⟩ := ConstructionDirectedLimitCarrier.exists_stage_map hM hC hp hE hT hEq hk hDk
  have hCore := stage_core hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hk hDk hmk hek hgk hGK
  have hxk := hCov.1.1.2 x xk htx
  have hwD := ConstructionDirectedMonoidData.domain_mem hFam hDk hwk
  exact ⟨Dk,mk,t,gk,xk,yk,ak,wk,hCov,htx,hty,hta,hCore.2.2,
    (hGK xk fx).mpr ⟨hxk,hxp⟩,(hGK yk fy).mpr ⟨hyk,hyp⟩,
    (hGK ak fa).mpr ⟨hak,hap⟩,hwD,(hGK wk w).mpr ⟨hwD,hwp⟩⟩

/-- Source of_conservative: all four original fields, against EVERY limit
element, for the SAME actual stage graph. -/
theorem stage_conservative (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    {i D mul e f : M.Carrier .set} (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (he : PureKuratowski.PairMember M i e Units) (hf : MapsTo D L f)
    (hFG : ∀ x z, PureKuratowski.PairMember M x z f ↔ (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z) :
    Conservative D L mul G f := by
  have hCore := stage_core hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm he hf hFG
  refine ⟨hCore.1,hCore.2.1,?_,?_⟩
  · intro x y a fx fy fa hxf hyf haf hJoin w hw
    obtain ⟨hx,hxp⟩ := (hFG x fx).mp hxf
    obtain ⟨hy,hyp⟩ := (hFG y fy).mp hyf
    obtain ⟨ha,hap⟩ := (hFG a fa).mp haf
    obtain ⟨Dk,mk,t,gk,xk,yk,ak,wk,hCov,htx,hty,hta,hDiv,hgx,hgy,hga,hwk,hgw⟩ :=
      comparison_stage hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm hx hy ha hxp hyp hap hw
    have hJK := hCov.2.2.1 x y a xk yk ak htx hty hta hJoin
    exact (and_congr (hDiv xk wk fx w hgx hgw) (hDiv yk wk fy w hgy hgw)).trans
      ((hJK wk hwk).trans (hDiv ak wk fa w hga hgw).symm)
  · intro x y fx fy hxf hyf hCommon
    obtain ⟨w,hw,hxw,hyw⟩ := hCommon
    obtain ⟨hx,hxp⟩ := (hFG x fx).mp hxf
    obtain ⟨hy,hyp⟩ := (hFG y fy).mp hyf
    obtain ⟨Dk,mk,t,gk,xk,yk,ak,wk,hCov,htx,hty,_,hDiv,hgx,hgy,_,hwk,hgw⟩ :=
      comparison_stage hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm hx hy hx hxp hyp hxp hw
    exact hCov.2.2.2 x y xk yk htx hty ⟨wk,hwk,(hDiv xk wk fx w hgx hgw).mp hxw,(hDiv yk wk fy w hgy hgw).mp hyw⟩

/-- Pinned conditionalJoins:111, using the same actual canonical stage graph. -/
theorem conditional_joins (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    (hJoins : JoinsFamily J Domains Muls Units) : ConstructionProbeSharedIntersections.ConditionalJoins L G := by
  intro a b c ha hb hc hac hbc
  obtain ⟨i,x,y,z,hx,hy,hz,hxa,hyb,hzc⟩ :=
    ConstructionDirectedLimitCarrier.common_stage_three hM hC hp hE hT hL hP hEq ha hb hc
  obtain ⟨D,mul,e,hD,hm,he,_⟩ := ConstructionDirectedMonoidData.family_at hFam hx.1
  obtain ⟨f,hf,hFG,_⟩ := ConstructionDirectedLimitCarrier.exists_stage_map hM hC hp hE hT hEq hx.1 hD
  have hxD := ConstructionDirectedMonoidData.domain_mem hFam hD hx
  have hyD := ConstructionDirectedMonoidData.domain_mem hFam hD hy
  have hzD := ConstructionDirectedMonoidData.domain_mem hFam hD hz
  have hfx := (hFG x a).mpr ⟨hxD,hxa⟩
  have hfy := (hFG y b).mpr ⟨hyD,hyb⟩
  have hfz := (hFG z c).mpr ⟨hzD,hzc⟩
  have hCore := stage_core hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hx.1 hD hm he hf hFG
  obtain ⟨j,hj,hJoin⟩ := hJoins i D mul e hx.1 hD hm he x y z hxD hyD hzD
    ((hCore.2.2 x z a c hfx hfz).mp hac) ((hCore.2.2 y z b c hfy hfz).mp hbc)
  obtain ⟨fj,hfj,_⟩ := hf.1.2 j hj
  have hCov := stage_conservative hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hx.1 hD hm he hf hFG
  exact ⟨fj,hf.2 j fj hfj,hCov.2.2.1 x y j a b fj hfx hfy hfj hJoin⟩

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    (J E Domains F Muls Units : M.Carrier .set)
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hFam : Family J Domains Muls Units) (hHom : HomLaws J E Domains F Muls Units)
    (hCons : ConservativeTransitions J E Domains F Muls) :
    ∃ C L projection B G unit, Representatives J Domains C ∧ MapsTo C L projection ∧ Carrier J E Domains F C L ∧
      Projection J E Domains F C projection ∧ EqualityLaw J E Domains F projection ∧
      ConstructionProbeLetters.Representatives L L B ∧ MapsTo B L G ∧ Graph J Domains Muls projection G ∧
      (Project.FirstOrderSemantics.reduct M).mem unit L ∧ UnitImage J Domains Units projection unit ∧
      LeftCancelMonoid L G unit ∧ (ConicalFamily J Domains Muls Units → Conical L G unit) ∧
      (JoinsFamily J Domains Muls Units → ConstructionProbeSharedIntersections.ConditionalJoins L G) ∧
      ∀ i D mul e, (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i D Domains →
        PureKuratowski.PairMember M i mul Muls → PureKuratowski.PairMember M i e Units →
        ∃ f, MapsTo D L f ∧ (∀ x z, PureKuratowski.PairMember M x z f ↔
          (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z) ∧
          ConstructionProbeLiftHom.PreservesProducts mul G f ∧ PureKuratowski.PairMember M e unit f ∧
          Conservative D L mul G f := by
  obtain ⟨C,L,projection,B,G,unit,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hCon,hStages⟩ :=
    ConstructionDirectedMonoid.exists_system hM J E Domains F Muls Units hne hE hT hFam hHom
  refine ⟨C,L,projection,B,G,unit,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hCon,
    fun hJoins => conditional_joins hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hJoins,?_⟩
  intro i D mul e hi hD hm he
  obtain ⟨f,hf,hFG,hProd,hOne,_⟩ := hStages i D mul e hi hD hm he
  exact ⟨f,hf,hFG,hProd,hOne,stage_conservative hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm he hf hFG⟩

end PPAC.Migration.ConstructionDirectedConservative
