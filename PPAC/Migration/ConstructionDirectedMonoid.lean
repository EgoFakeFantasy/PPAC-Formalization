/- Pinned DirectLimits.ConservativeLimit.of.map_one/map_mul,
LeftCancelMonoid:32 and IsConical:44, on SAME actual quotient/multiplication.
Source common-stage induction and later equality witnesses are used; NO
injectivity of transition maps is assumed. Source Conical is conditional. -/
import PPAC.Migration.ConstructionDirectedProduct
import PPAC.Migration.ConstructionProbeLiftHom

namespace PPAC.Migration.ConstructionDirectedMonoid
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family ProductAt UnitAt HomLaws ConicalFamily)
open ConstructionDirectedLimitCarrier (Representatives Carrier Projection EqualityLaw)
open ConstructionDirectedProduct (Value Graph)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {J E Domains F Muls Units C L projection B G unit : M.Carrier .set}

def UnitImage (J Domains Units projection unit : M.Carrier .set) : Prop :=
  ∀ i e, UnitAt J Domains Units i e → Product projection i e unit

theorem exists_unit_image (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hHom : HomLaws J E Domains F Muls Units) (hC : Representatives J Domains C)
    (hp : MapsTo C L projection) (hEq : EqualityLaw J E Domains F projection)
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J) :
    ∃ unit, (Project.FirstOrderSemantics.reduct M).mem unit L ∧ UnitImage J Domains Units projection unit := by
  obtain ⟨i,hi⟩ := hne
  obtain ⟨ei,hei⟩ := ConstructionDirectedMonoidData.unit_total hFam hi
  obtain ⟨unit,hu,hip⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hei.1
  refine ⟨unit,hu,?_⟩
  intro j ej hej
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hi hej.1.1
  obtain ⟨eik,heik⟩ := hT.1 i k ei hei.1 hk hik
  obtain ⟨ejk,hejk⟩ := hT.1 j k ej hej.1 hk hjk
  have hU1 := hHom.2 i k ei eik hik hei heik
  have hU2 := hHom.2 j k ej ejk hjk hej hejk
  have he := ConstructionDirectedMonoidData.unit_unique hFam.2.2.1 hU1 hU2
  subst ejk
  obtain ⟨out,_,hjp⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hej.1
  have heq : unit = out := (ConstructionDirectedLimitCarrier.projected_eq_iff hEq hip hjp).mpr
    ⟨hei.1,hej.1,k,eik,hk,hik,hjk,heik,hejk⟩
  exact heq.symm ▸ hjp

theorem graph_of_product (hGraph : Graph J Domains Muls projection G)
    {i x y z a b c : M.Carrier .set} (hprod : ProductAt J Domains Muls i x y z)
    (ha : Product projection i x a) (hb : Product projection i y b) (hc : Product projection i z c) :
    Product G a b c := (hGraph a b c).mpr ⟨i,x,y,z,hprod,ha,hb,hc⟩

theorem unit_laws (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hC : Representatives J Domains C)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    (hu : (Project.FirstOrderSemantics.reduct M).mem unit L) (hImage : UnitImage J Domains Units projection unit) :
    ForcingDiagramPoset.Unit L G unit := by
  refine ⟨hu,?_⟩
  intro a ha out
  obtain ⟨i,x,hx,hxa⟩ := ConstructionDirectedLimitCarrier.representative hC hL hP ha
  obtain ⟨e,he⟩ := ConstructionDirectedMonoidData.unit_total hFam hx.1
  have hOne := hImage i e he
  have hl := graph_of_product hGraph (ConstructionDirectedMonoidData.unit_left hFam he hx) hOne hxa hxa
  have hr := graph_of_product hGraph (ConstructionDirectedMonoidData.unit_right hFam he hx) hxa hOne hxa
  exact ⟨⟨fun h => ConstructionProbeHomEvaluation.product_unique hM hG h hl,fun h => h.symm ▸ hl⟩,
    ⟨fun h => ConstructionProbeHomEvaluation.product_unique hM hG h hr,fun h => h.symm ▸ hr⟩⟩

theorem associative (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G) :
    ForcingDiagramPoset.Associative L G := by
  intro a b c ab bc out ha hb hc hab hbc
  obtain ⟨i,x,y,z,hx,hy,hz,hxa,hyb,hzc⟩ :=
    ConstructionDirectedLimitCarrier.common_stage_three hM hC hp hE hT hL hP hEq ha hb hc
  obtain ⟨xy,hxy⟩ := ConstructionDirectedMonoidData.product_total hFam hx hy
  obtain ⟨yz,hyz⟩ := ConstructionDirectedMonoidData.product_total hFam hy hz
  obtain ⟨xyz,hxyz⟩ := ConstructionDirectedMonoidData.product_total hFam hxy.2.2.1 hz
  obtain ⟨p,_,hxp⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hxy.2.2.1
  obtain ⟨q,_,hyq⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hyz.2.2.1
  obtain ⟨r,_,hzr⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hxyz.2.2.1
  have habp := graph_of_product hGraph hxy hxa hyb hxp
  have hbcq := graph_of_product hGraph hyz hyb hzc hyq
  have heab := ConstructionProbeHomEvaluation.product_unique hM hG hab habp
  have hebc := ConstructionProbeHomEvaluation.product_unique hM hG hbc hbcq
  subst ab
  subst bc
  have hLeft := graph_of_product hGraph hxyz hxp hzc hzr
  have hRight := graph_of_product hGraph (ConstructionDirectedMonoidData.product_assoc hFam hxy hyz hxyz) hxa hyq hzr
  exact ⟨fun h => (ConstructionProbeHomEvaluation.product_unique hM hG h hLeft).symm ▸ hRight,
    fun h => (ConstructionProbeHomEvaluation.product_unique hM hG h hRight).symm ▸ hLeft⟩

theorem left_cancel (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hHom : HomLaws J E Domains F Muls Units) (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    {a b c out : M.Carrier .set} (ha : (Project.FirstOrderSemantics.reduct M).mem a L)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b L) (hc : (Project.FirstOrderSemantics.reduct M).mem c L)
    (hp1 : Product G a b out) (hp2 : Product G a c out) : b = c := by
  obtain ⟨i,x,y,z,hx,hy,hz,hxa,hyb,hzc⟩ :=
    ConstructionDirectedLimitCarrier.common_stage_three hM hC hp hE hT hL hP hEq ha hb hc
  obtain ⟨u,hxy⟩ := ConstructionDirectedMonoidData.product_total hFam hx hy
  obtain ⟨v,hxz⟩ := ConstructionDirectedMonoidData.product_total hFam hx hz
  obtain ⟨p,_,hup⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hxy.2.2.1
  obtain ⟨q,_,hvq⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hxz.2.2.1
  have heP := ConstructionProbeHomEvaluation.product_unique hM hG hp1 (graph_of_product hGraph hxy hxa hyb hup)
  have heQ := ConstructionProbeHomEvaluation.product_unique hM hG hp2 (graph_of_product hGraph hxz hxa hzc hvq)
  obtain ⟨_,_,k,w,hk,hik,_,huw,hvw⟩ := (ConstructionDirectedLimitCarrier.projected_eq_iff hEq hup hvq).mp (heP.symm.trans heQ)
  obtain ⟨xx,hxx⟩ := hT.1 i k x hx hk hik
  obtain ⟨yy,hyy⟩ := hT.1 i k y hy hk hik
  obtain ⟨zz,hzz⟩ := hT.1 i k z hz hk hik
  have hxyk := hHom.1 i k x y u xx yy w hik hxy hxx hyy huw
  have hxzk := hHom.1 i k x z v xx zz w hik hxz hxx hzz hvw
  have he := ConstructionDirectedMonoidData.product_left_cancel hFam hxyk hxzk
  exact (ConstructionDirectedLimitCarrier.projected_eq_iff hEq hyb hzc).mpr
    ⟨hy,hz,k,yy,hk,hik,hik,hyy,he.symm ▸ hzz⟩

theorem monoid_laws (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hHom : HomLaws J E Domains F Muls Units) (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    (hu : (Project.FirstOrderSemantics.reduct M).mem unit L) (hImage : UnitImage J Domains Units projection unit) :
    LeftCancelMonoid L G unit := by
  refine ⟨unit_laws hM hFam hC hL hP hG hGraph hu hImage,?_,associative hM hFam hE hT hC hp hL hP hEq hG hGraph⟩
  intro a ha
  refine ⟨?_,fun _ _ _ _ hp1 hp2 => ConstructionProbeHomEvaluation.product_unique hM hG hp1 hp2,?_⟩
  · intro b hb
    obtain ⟨c,hc,hv⟩ := ConstructionDirectedProduct.value_total hM hFam hE hT hC hp hL hP hEq ha hb
    exact ⟨c,hc,(hGraph a b c).mpr hv⟩
  · intro b c out hb hc hp1 hp2
    exact left_cancel hM hFam hE hT hHom hC hp hL hP hEq hG hGraph ha hb hc hp1 hp2

theorem conical_laws (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hCon : ConicalFamily J Domains Muls Units)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F) (hHom : HomLaws J E Domains F Muls Units)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    (hImage : UnitImage J Domains Units projection unit) : Conical L G unit := by
  intro a b ha hb hab
  obtain ⟨i,x,y,hx,hy,hxa,hyb⟩ := ConstructionDirectedLimitCarrier.common_stage_pair hM hC hp hE hT hL hP hEq ha hb
  obtain ⟨z,hxyz⟩ := ConstructionDirectedMonoidData.product_total hFam hx hy
  obtain ⟨c,_,hzc⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hxyz.2.2.1
  have hec := ConstructionProbeHomEvaluation.product_unique hM hG (graph_of_product hGraph hxyz hxa hyb hzc) hab
  obtain ⟨ei,hei⟩ := ConstructionDirectedMonoidData.unit_total hFam hx.1
  have hEi := hImage i ei hei
  obtain ⟨_,_,k,w,hk,hik,_,hzw,hew⟩ := (ConstructionDirectedLimitCarrier.projected_eq_iff hEq hzc hEi).mp hec
  obtain ⟨xx,hxx⟩ := hT.1 i k x hx hk hik
  obtain ⟨yy,hyy⟩ := hT.1 i k y hy hk hik
  have hUnitK := hHom.2 i k ei w hik hei hew
  have hProdK := hHom.1 i k x y z xx yy w hik hxyz hxx hyy hzw
  obtain ⟨hex,hey⟩ := ConstructionDirectedMonoidData.product_conical hFam hCon hUnitK hProdK
  have hUw := hImage k w hUnitK
  exact ⟨ConstructionDirectedLimitCarrier.of_map hE hT hEq hik hxx hxa (hex.symm ▸ hUw),
    ConstructionDirectedLimitCarrier.of_map hE hT hEq hik hyy hyb (hey.symm ▸ hUw)⟩

theorem stage_hom (hFam : Family J Domains Muls Units) (hGraph : Graph J Domains Muls projection G)
    (hImage : UnitImage J Domains Units projection unit)
    {i D mul e f : M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (he : PureKuratowski.PairMember M i e Units)
    (hf : ∀ x z, PureKuratowski.PairMember M x z f ↔
      (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z) :
    ConstructionProbeLiftHom.PreservesProducts mul G f ∧ PureKuratowski.PairMember M e unit f := by
  have hMon := hFam.2.2.2 i D mul e hD hm he
  refine ⟨?_,(hf e unit).mpr ⟨hMon.1.1,hImage i e ⟨⟨hi,D,hD,hMon.1.1⟩,he⟩⟩⟩
  intro x y z fx fy fz hxyz hxf hyf hzf
  obtain ⟨hx,hxp⟩ := (hf x fx).mp hxf
  obtain ⟨hy,hyp⟩ := (hf y fy).mp hyf
  obtain ⟨hz,hzp⟩ := (hf z fz).mp hzf
  exact graph_of_product hGraph (ConstructionDirectedMonoidData.product_mk hi hD hm hx hy hz hxyz) hxp hyp hzp

/-- Execute the original direct-limit monoid construction from its actual
stage tables. All old carrier objects are produced by the SAME accepted
constructor. Conical/injective conclusions stay conditional exactly as source. -/
theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    (J E Domains F Muls Units : M.Carrier .set)
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hFam : Family J Domains Muls Units) (hHom : HomLaws J E Domains F Muls Units) :
    ∃ C L projection B G unit, Representatives J Domains C ∧ MapsTo C L projection ∧ Carrier J E Domains F C L ∧
      Projection J E Domains F C projection ∧ EqualityLaw J E Domains F projection ∧
      ConstructionProbeLetters.Representatives L L B ∧ MapsTo B L G ∧ Graph J Domains Muls projection G ∧
      (Project.FirstOrderSemantics.reduct M).mem unit L ∧ UnitImage J Domains Units projection unit ∧
      LeftCancelMonoid L G unit ∧ (ConicalFamily J Domains Muls Units → Conical L G unit) ∧
      ∀ i D mul e, (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i D Domains →
        PureKuratowski.PairMember M i mul Muls → PureKuratowski.PairMember M i e Units →
        ∃ f, MapsTo D L f ∧ (∀ x z, PureKuratowski.PairMember M x z f ↔
          (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z) ∧
          ConstructionProbeLiftHom.PreservesProducts mul G f ∧ PureKuratowski.PairMember M e unit f ∧
          (InjectiveTransitions J E Domains F → Injection D L f) := by
  obtain ⟨C,L,projection,hC,hp,hL,hP,hEq,_,_,_,_,_,_,_⟩ := ConstructionDirectedLimitCarrier.exists_system hM J E Domains F hE hT
  obtain ⟨B,G,hB,hG,hGraph⟩ := ConstructionDirectedProduct.exists_graph hM hFam hE hT hHom hC hp hL hP hEq
  obtain ⟨unit,hu,hImage⟩ := exists_unit_image hM hFam hE hT hHom hC hp hEq hne
  have hMon := monoid_laws hM hFam hE hT hHom hC hp hL hP hEq hG hGraph hu hImage
  refine ⟨C,L,projection,B,G,unit,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,
    fun hCon => conical_laws hM hFam hCon hE hT hHom hC hp hL hP hEq hG hGraph hImage,?_⟩
  intro i D mul e hi hD hm he
  obtain ⟨f,hf,hGraphF,hInj⟩ := ConstructionDirectedLimitCarrier.exists_stage_map hM hC hp hE hT hEq hi hD
  obtain ⟨hProd,hOne⟩ := stage_hom hFam hGraph hImage hi hD hm he hGraphF
  exact ⟨f,hf,hGraphF,hProd,hOne,hInj⟩

def unitImage {m : Nat} (J Domains Units projection unit : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp
    (ConstructionDirectedMonoidData.unitAt J.succ.succ Domains.succ.succ Units.succ.succ 1 0)
    (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ.succ 1 0 unit.succ.succ))))

theorem unitImage_freeClosed {m : Nat} (J Domains Units projection unit : Fin m) :
    (unitImage J Domains Units projection unit).FreeClosed := by
  simp -implicitDefEqProofs [unitImage,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionDirectedMonoidData.unitAt_freeClosed]

theorem unitImage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Units projection unit : Fin m) :
    Project.Formula.satisfies env (unitImage J Domains Units projection unit) ↔
      UnitImage (env.bound J) (env.bound Domains) (env.bound Units) (env.bound projection) (env.bound unit) := by
  simp only [unitImage,UnitImage,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M),
    ConstructionDirectedMonoidData.unitAt_semantics hM]
  rfl

end PPAC.Migration.ConstructionDirectedMonoid
