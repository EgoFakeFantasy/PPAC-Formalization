/- Pinned DirectLimits.ConservativeLimit.of_factors:65 / of_dvd_iff:79.
SAME actual carrier/multiplication and stage maps. Original conservative
transition graphs give the particular source right factor; no supplied limit
factor/Conservative premise. Reuse existing division_reflection unchanged. -/
import PPAC.Migration.ConstructionDirectedConservativeData

namespace PPAC.Migration.ConstructionDirectedFactors
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family ProductAt)
open ConstructionDirectedConservativeData
open ConstructionDirectedLimitCarrier (Representatives Carrier Projection EqualityLaw)
open ConstructionDirectedProduct (Graph)
open ConstructionDirectedMonoid (UnitImage)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionProbeAlphabetMap (FactorConservation DivisionReflection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {J E Domains F Muls Units C L projection B G unit : M.Carrier .set}

/-- Transport along a GIVEN transition, preserving the SAME quotient value. -/
theorem projected_transition (hM : FirstOrder.Theory.Models M nativeZF)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F) (hEq : EqualityLaw J E Domains F projection)
    {i j x y c : M.Carrier .set} (hij : PureKuratowski.PairMember M i j E)
    (hxy : Transition J Domains F i j x y) (hc : Product projection i x c) : Product projection j y c := by
  obtain ⟨d,_,hd⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hxy.2.1
  exact (ConstructionDirectedLimitCarrier.of_map hE hT hEq hij hxy hc hd).symm ▸ hd

theorem product_reflect (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F) (hI : InjectiveTransitions J E Domains F)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    {i x y z a b c : M.Carrier .set} (hx : Product projection i x a) (hy : Product projection i y b)
    (hz : Product projection i z c) (hprod : Product G a b c) : ProductAt J Domains Muls i x y z := by
  obtain ⟨w,hw⟩ := ConstructionDirectedMonoidData.product_total hFam
    (ConstructionDirectedLimitCarrier.projected_indices hC hp hx) (ConstructionDirectedLimitCarrier.projected_indices hC hp hy)
  obtain ⟨out,_,hout⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hw.2.2.1
  have he := ConstructionProbeHomEvaluation.product_unique hM hG
    (ConstructionDirectedMonoid.graph_of_product hGraph hw hx hy hout) hprod
  have hwz := ConstructionDirectedLimitCarrier.of_injective hC hp hE hT hI hEq (he ▸ hout) hz
  exact hwz ▸ hw

/-- Source of_factors: reflects the SPECIFIED arbitrary limit factor. -/
theorem of_factors (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    {i D mul x y a b c : M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (hx : Product projection i x a) (hy : Product projection i y c)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b L) (hprod : Product G a b c) :
    ∃ t, (Project.FirstOrderSemantics.reduct M).mem t D ∧ Product projection i t b := by
  have hI := injective_transitions hFam hT hCons
  obtain ⟨j,z,hz,hzb⟩ := ConstructionDirectedLimitCarrier.representative hC hL hP hb
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hi hz.1
  obtain ⟨xx,_,hxx,hxa⟩ := ConstructionDirectedLimitCarrier.projected_later hM hC hp hE hT hEq hk hik hx
  obtain ⟨yy,_,hyy,hyc⟩ := ConstructionDirectedLimitCarrier.projected_later hM hC hp hE hT hEq hk hik hy
  obtain ⟨zz,_,_,hzzb⟩ := ConstructionDirectedLimitCarrier.projected_later hM hC hp hE hT hEq hk hjk hzb
  have hProdK := product_reflect hM hFam hC hp hE hT hI hEq hG hGraph hxa hzzb hyc hprod
  obtain ⟨Dk,mk,ek,hDk,hmk,_,_⟩ := ConstructionDirectedMonoidData.family_at hFam hk
  obtain ⟨f,hF,hfx⟩ := hxx.2.2
  have hf := hCons i k D Dk mul mk f hi hk hik hD hDk hm hmk hF
  have hyD := ConstructionDirectedMonoidData.domain_mem hFam hD (ConstructionDirectedLimitCarrier.projected_indices hC hp hy)
  have hfy := transition_edge hT hf.1 hi hk hD hDk hF hik hyD hyy
  obtain ⟨_,hzzD,_,hProd⟩ := ConstructionDirectedMonoidData.product_data hFam hDk hmk hProdK
  obtain ⟨t,hft⟩ := hf.2.1 x y zz xx yy hfx hfy hzzD hProd
  have htD := ForcingConditionGraphs.function_input hf.1.1.1 hft
  have htt : Transition J Domains F i k t zz := ⟨⟨hi,D,hD,htD⟩,hProdK.2.1,f,hF,hft⟩
  obtain ⟨pt,_,htp⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp ⟨hi,D,hD,htD⟩
  exact ⟨t,htD,(ConstructionDirectedLimitCarrier.of_map hE hT hEq hik htt htp hzzb) ▸ htp⟩

/-- Existing actual stage graph has injection, particular-factor reflection
and exact divisibility reflection. These are NOT called full Conservative. -/
theorem stage_core (hM : FirstOrder.Theory.Models M nativeZF)
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
    Injection D L f ∧ FactorConservation L G f ∧ DivisionReflection D L mul G f := by
  have hI := injective_transitions hFam hT hCons
  have hInj : Injection D L f := ⟨hf,fun x y z hx hy =>
    ConstructionDirectedLimitCarrier.of_injective hC hp hE hT hI hEq ((hFG x z).mp hx).2 ((hFG y z).mp hy).2⟩
  have hFactors : FactorConservation L G f := by
    intro x y z fx fy hxf hyf hz hprod
    obtain ⟨t,ht,htp⟩ := of_factors hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hi hD hm
      ((hFG x fx).mp hxf).2 ((hFG y fy).mp hyf).2 hz hprod
    exact ⟨t,(hFG t z).mpr ⟨ht,htp⟩⟩
  have hPres := (ConstructionDirectedMonoid.stage_hom hFam hGraph hImage hi hD hm he hFG).1
  have hDiv := ConstructionProbeAlphabetMap.division_reflection
    (hFam.2.2.2 i D mul e hD hm he) hMon hInj hPres hFactors
  exact ⟨hInj,hFactors,hDiv⟩

end PPAC.Migration.ConstructionDirectedFactors
