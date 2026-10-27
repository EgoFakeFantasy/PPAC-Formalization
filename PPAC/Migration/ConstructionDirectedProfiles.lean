/- Pinned DirectLimits.ConservativeLimit.probeProfile:130.
Preserve every later-stage profile and the SAME original path. -/
import PPAC.Migration.ConstructionDirectedConservative
import PPAC.Migration.ConstructionPersistentProfiles

namespace PPAC.Migration.ConstructionDirectedProfiles
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
open ConstructionPersistentProfiles (ProbeProfile)
open ConstructionProbeMappedPath (NodeMap)
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

/-- Literal source hP: EVERY later stage has the profile of the SAME mapped
path and four source elements. No initial-only or supplied limit profile. -/
def PersistentProfile (J E Domains F Muls w i a b d p node : M.Carrier .set) : Prop :=
  ∀ j D mul f mapped aa bb dd pp, (Project.FirstOrderSemantics.reduct M).mem j J →
    PureKuratowski.PairMember M i j E → PureKuratowski.PairMember M j D Domains →
    PureKuratowski.PairMember M j mul Muls → Product F i j f → MapsTo w D mapped → NodeMap node f mapped →
    PureKuratowski.PairMember M a aa f → PureKuratowski.PairMember M b bb f →
    PureKuratowski.PairMember M d dd f → PureKuratowski.PairMember M p pp f →
    ProbeProfile w D mul aa bb dd pp mapped

/-- Source hi follows from hP at the identity transition; no extra profile
assumption is added to the typed source data. -/
theorem initial_profile
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    {w i D mul e a b d p node : M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (he : PureKuratowski.PairMember M i e Units)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a D)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D)
    (hp0 : (Project.FirstOrderSemantics.reduct M).mem p D) (hn : MapsTo w D node)
    (hPersist : PersistentProfile J E Domains F Muls w i a b d p node) :
    ProbeProfile w D mul a b d p node := by
  have hMon := hFam.2.2.2 i D mul e hD hm he
  have hii := hE.1 i hi
  obtain ⟨ee,hee⟩ := hT.1 i i e ⟨hi,D,hD,hMon.1.1⟩ hi hii
  obtain ⟨f,hF,_⟩ := hee.2.2
  have hf := (hCons i i D D mul mul f hi hi hii hD hD hm hm hF).1
  have hId : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x D → PureKuratowski.PairMember M x x f :=
    fun x hx => transition_edge hT hf hi hi hD hD hF hii hx (hT.2.2.1 i x ⟨hi,D,hD,hx⟩)
  have hNode : NodeMap node f node := by
    intro l y
    constructor
    · intro hly
      exact ⟨y,hly,hId y (hn.2 l y hly)⟩
    · rintro ⟨x,hlx,hxy⟩
      exact (ForcingConditionGraphs.function_unique hf.1.1 (hId x (hn.2 l x hlx)) hxy) ▸ hlx
  exact hPersist i D mul f node a b d p hi hii hD hm hF hn hNode (hId a ha) (hId b hb) (hId d hd) (hId p hp0)

/-- Actual comparison stage for source probeProfile: same original path,
actual transition images, and canonical stage graph into the SAME limit. -/
theorem comparison_profile (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    {w i D mul f a b d p node mapped fa fb fd fp x : M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (hf : MapsTo D L f)
    (hFG : ∀ v z, PureKuratowski.PairMember M v z f ↔ (Project.FirstOrderSemantics.reduct M).mem v D ∧ Product projection i v z)
    (hn : MapsTo w D node) (hMap : NodeMap node f mapped)
    (hfa : PureKuratowski.PairMember M a fa f) (hfb : PureKuratowski.PairMember M b fb f)
    (hfd : PureKuratowski.PairMember M d fd f) (hfp : PureKuratowski.PairMember M p fp f)
    (hPersist : PersistentProfile J E Domains F Muls w i a b d p node)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x L) :
    ∃ Dk mk gk ak bk dk pk xk nodek, MapsTo Dk L gk ∧
      ConstructionProbeConservative.Conservative Dk L mk G gk ∧
      ConstructionProbeLiftHom.PreservesProducts mk G gk ∧ DivisionReflection Dk L mk G gk ∧
      ProbeProfile w Dk mk ak bk dk pk nodek ∧ NodeMap nodek gk mapped ∧
      PureKuratowski.PairMember M ak fa gk ∧ PureKuratowski.PairMember M bk fb gk ∧
      PureKuratowski.PairMember M dk fd gk ∧ PureKuratowski.PairMember M pk fp gk ∧
      (Project.FirstOrderSemantics.reduct M).mem xk Dk ∧ PureKuratowski.PairMember M xk x gk := by
  obtain ⟨j,z,hz,hzx⟩ := ConstructionDirectedLimitCarrier.representative hC hL hP hx
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hi hz.1
  obtain ⟨ak,hak⟩ := hT.1 i k a ⟨hi,D,hD,ForcingConditionGraphs.function_input hf.1 hfa⟩ hk hik
  obtain ⟨Dk,mk,ek,hDk,hmk,hek,_⟩ := ConstructionDirectedMonoidData.family_at hFam hk
  obtain ⟨t,hFt,hta⟩ := hak.2.2
  have hCov := hCons i k D Dk mul mk t hi hk hik hD hDk hm hmk hFt
  obtain ⟨bk,_,htb,hbk⟩ := transition_value hCov.1 hi hk hD hDk hFt (ForcingConditionGraphs.function_input hf.1 hfb)
  obtain ⟨dk,_,htd,hdk⟩ := transition_value hCov.1 hi hk hD hDk hFt (ForcingConditionGraphs.function_input hf.1 hfd)
  obtain ⟨pk,_,htp,hpk⟩ := transition_value hCov.1 hi hk hD hDk hFt (ForcingConditionGraphs.function_input hf.1 hfp)
  obtain ⟨nodek,hNodeK,hNK⟩ := ConstructionProbeMappedPath.exists_node_map hM hn hCov.1.1
  have hProf := hPersist k Dk mk t nodek ak bk dk pk hk hik hDk hmk hFt hNodeK hNK hta htb htd htp
  obtain ⟨xk,hxk,_,hxp⟩ := ConstructionDirectedLimitCarrier.projected_later hM hC hp hE hT hEq hk hjk hzx
  obtain ⟨gk,hgk,hGK,_⟩ := ConstructionDirectedLimitCarrier.exists_stage_map hM hC hp hE hT hEq hk hDk
  have hCore := stage_core hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hk hDk hmk hek hgk hGK
  have hConK := ConstructionDirectedConservative.stage_conservative hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hk hDk hmk hek hgk hGK
  have hPresK := (ConstructionDirectedMonoid.stage_hom hFam hGraph hImage hk hDk hmk hek hGK).1
  have hForward : ∀ v vk out, PureKuratowski.PairMember M v out f → PureKuratowski.PairMember M v vk t → PureKuratowski.PairMember M vk out gk := by
    intro v vk out hv htv
    have hvD := ForcingConditionGraphs.function_input hf.1 hv
    have hvkD := hCov.1.1.2 v vk htv
    have hTrans : Transition J Domains F i k v vk := ⟨⟨hi,D,hD,hvD⟩,⟨hk,Dk,hDk,hvkD⟩,t,hFt,htv⟩
    exact (hGK vk out).mpr ⟨hvkD,projected_transition hM hC hp hE hT hEq hik hTrans ((hFG v out).mp hv).2⟩
  have hBack : ∀ v vk out, (Project.FirstOrderSemantics.reduct M).mem v D → PureKuratowski.PairMember M v vk t → PureKuratowski.PairMember M vk out gk → PureKuratowski.PairMember M v out f := by
    intro v vk out hvD htv hgv
    obtain ⟨fv,hfv,_⟩ := hf.1.2 v hvD
    have heq := ForcingConditionGraphs.function_unique hgk.1 (hForward v vk fv hfv htv) hgv
    exact heq ▸ hfv
  have hNodes : NodeMap nodek gk mapped := by
    intro l out
    constructor
    · intro hl
      obtain ⟨v,hlv,hfv⟩ := (hMap l out).mp hl
      obtain ⟨vk,htv,_⟩ := hCov.1.1.1.2 v (hn.2 l v hlv)
      exact ⟨vk,(hNK l vk).mpr ⟨v,hlv,htv⟩,hForward v vk out hfv htv⟩
    · rintro ⟨vk,hlvk,hgv⟩
      obtain ⟨v,hlv,htv⟩ := (hNK l vk).mp hlvk
      exact (hMap l out).mpr ⟨v,hlv,hBack v vk out (hn.2 l v hlv) htv hgv⟩
  have hxD := ConstructionDirectedMonoidData.domain_mem hFam hDk hxk
  exact ⟨Dk,mk,gk,ak,bk,dk,pk,xk,nodek,hgk,hConK,hPresK,hCore.2.2,hProf,hNodes,
    hForward a ak fa hfa hta,hForward b bk fb hfb htb,hForward d dk fd hfd htd,hForward p pk fp hfp htp,
    hxD,(hGK xk x).mpr ⟨hxD,hxp⟩⟩

/-- Literal source profile proof over arbitrary limit elements. No old-gate
hypothesis or independently selected limit path is used. -/
theorem profile (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    {w i D mul e f a b d p node mapped fa fb fd fp : M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (he : PureKuratowski.PairMember M i e Units) (hf : MapsTo D L f)
    (hFG : ∀ v z, PureKuratowski.PairMember M v z f ↔ (Project.FirstOrderSemantics.reduct M).mem v D ∧ Product projection i v z)
    (hn : MapsTo w D node) (hMap : NodeMap node f mapped) (hMapped : MapsTo w L mapped)
    (hfa : PureKuratowski.PairMember M a fa f) (hfb : PureKuratowski.PairMember M b fb f)
    (hfd : PureKuratowski.PairMember M d fd f) (hfp : PureKuratowski.PairMember M p fp f)
    (hPersist : PersistentProfile J E Domains F Muls w i a b d p node) :
    ProbeProfile w L G fa fb fd fp mapped := by
  have hmD := hFam.2.2.2 i D mul e hD hm he
  have hInitial := initial_profile hFam hE hT hCons hi hD hm he
    (ForcingConditionGraphs.function_input hf.1 hfa) (ForcingConditionGraphs.function_input hf.1 hfb)
    (ForcingConditionGraphs.function_input hf.1 hfd) (ForcingConditionGraphs.function_input hf.1 hfp) hn hPersist
  have hCore := stage_core hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm he hf hFG
  have hPres := (ConstructionDirectedMonoid.stage_hom hFam hGraph hImage hi hD hm he hFG).1
  obtain ⟨_,_,_,_,_,ad,hadD,had,hpb,hnot,hdiv,_⟩ := hInitial
  obtain ⟨fad,hfad,_⟩ := hf.1.2 ad hadD
  refine ⟨hf.2 a fa hfa,hf.2 b fb hfb,hf.2 d fd hfd,hf.2 p fp hfp,hMapped,
    fad,hf.2 ad fad hfad,hPres a d ad fa fd fad had hfa hfd hfad,
    hPres p b ad fp fb fad hpb hfp hfb hfad,fun h => hnot ((hCore.2.2 p a fp fa hfp hfa).mp h),?_,?_⟩
  · intro x hx
    constructor
    · rintro ⟨hxa,hxp⟩
      obtain ⟨Dk,mk,gk,ak,bk,dk,pk,xk,nodek,hgk,_,_,hDivK,hProfK,hNodes,hga,_,_,hgp,hxk,hgx⟩ :=
        comparison_profile hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm hf hFG hn hMap hfa hfb hfd hfp hPersist hx
      obtain ⟨_,_,_,_,hnK,_,_,_,_,_,hdivK,_⟩ := hProfK
      obtain ⟨l,n,hl,hln,hxn⟩ := (hdivK xk hxk).mp ⟨(hDivK xk ak x fa hgx hga).mp hxa,(hDivK xk pk x fp hgx hgp).mp hxp⟩
      obtain ⟨fn,hfn,_⟩ := hgk.1.2 n (hnK.2 l n hln)
      exact ⟨l,fn,hl,(hNodes l fn).mpr ⟨n,hln,hfn⟩,(hDivK xk n x fn hgx hfn).mpr hxn⟩
    · rintro ⟨l,fn,hl,hln,hxfn⟩
      obtain ⟨n,hln0,hfn⟩ := (hMap l fn).mp hln
      have hnD := hn.2 l n hln0
      have hnProf := (hdiv n hnD).mpr ⟨l,n,hl,hln0,e,hmD.1.1,((hmD.1.2 n hnD n).2).mpr rfl⟩
      exact ⟨ConstructionProbeGates.divides_trans hMon hx hxfn ((hCore.2.2 n a fn fa hfn hfa).mpr hnProf.1),
        ConstructionProbeGates.divides_trans hMon hx hxfn ((hCore.2.2 n p fn fp hfn hfp).mpr hnProf.2)⟩
  · intro x hx hxa hxp
    obtain ⟨Dk,mk,gk,ak,bk,dk,pk,xk,nodek,hgk,hConK,hPresK,hDivK,hProfK,_,hga,_,hgd,hgp,hxk,hgx⟩ :=
      comparison_profile hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm hf hFG hn hMap hfa hfb hfd hfp hPersist hx
    obtain ⟨_,_,_,_,_,adK,hadK,hProdK,_,_,_,hjoinK⟩ := hProfK
    obtain ⟨out,hout,_⟩ := hgk.1.2 adK hadK
    have hOut := ConstructionProbeHomEvaluation.product_unique hM hG
      (hPresK ak dk adK fa fd out hProdK hga hgd hout) (hPres a d ad fa fd fad had hfa hfd hfad)
    have hAd : PureKuratowski.PairMember M adK fad gk := hOut ▸ hout
    exact hConK.2.2.1 xk pk adK x fp fad hgx hgp hAd
      (hjoinK xk hxk ((hDivK xk ak x fa hgx hga).mp hxa) (fun h => hxp ((hDivK xk pk x fp hgx hgp).mpr h)))

/-- Every original typed path/profile at a stage is transported by the SAME
canonical stage graph. Source all-later-stage persistence remains explicit. -/
def ProfileTransport (J E Domains F Muls i D L G f : M.Carrier .set) : Prop :=
  ∀ w a b d p node, (Project.FirstOrderSemantics.reduct M).mem a D →
    (Project.FirstOrderSemantics.reduct M).mem b D → (Project.FirstOrderSemantics.reduct M).mem d D →
    (Project.FirstOrderSemantics.reduct M).mem p D → MapsTo w D node →
    PersistentProfile J E Domains F Muls w i a b d p node →
    ∃ mapped fa fb fd fp, NodeMap node f mapped ∧
      PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f ∧
      PureKuratowski.PairMember M d fd f ∧ PureKuratowski.PairMember M p fp f ∧
      ProbeProfile w L G fa fb fd fp mapped

theorem profile_transport (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    {i D mul e f : M.Carrier .set} (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (he : PureKuratowski.PairMember M i e Units) (hf : MapsTo D L f)
    (hFG : ∀ v z, PureKuratowski.PairMember M v z f ↔ (Project.FirstOrderSemantics.reduct M).mem v D ∧ Product projection i v z) :
    ProfileTransport J E Domains F Muls i D L G f := by
  intro w a b d p node ha hb hd hp0 hn hPersist
  obtain ⟨mapped,hMapped,hMap⟩ := ConstructionProbeMappedPath.exists_node_map hM hn hf
  obtain ⟨fa,hfa,_⟩ := hf.1.2 a ha
  obtain ⟨fb,hfb,_⟩ := hf.1.2 b hb
  obtain ⟨fd,hfd,_⟩ := hf.1.2 d hd
  obtain ⟨fp,hfp,_⟩ := hf.1.2 p hp0
  exact ⟨mapped,fa,fb,fd,fp,hMap,hfa,hfb,hfd,hfp,
    profile hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm he hf hFG hn hMap hMapped hfa hfb hfd hfp hPersist⟩

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
          Conservative D L mul G f ∧ ProfileTransport J E Domains F Muls i D L G f := by
  obtain ⟨C,L,projection,B,G,unit,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hCon,hJoins,hStages⟩ :=
    ConstructionDirectedConservative.exists_system hM J E Domains F Muls Units hne hE hT hFam hHom hCons
  refine ⟨C,L,projection,B,G,unit,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hCon,hJoins,?_⟩
  intro i D mul e hi hD hm he
  obtain ⟨f,hf,hFG,hProd,hOne,hCov⟩ := hStages i D mul e hi hD hm he
  exact ⟨f,hf,hFG,hProd,hOne,hCov,
    profile_transport hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm he hf hFG⟩

def persistentProfile {m : Nat} (J E Domains F Muls w i a b d p node : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem
  (.bound (8 : Fin (m+9))) (.bound J.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge E.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)) (7 : Fin
  (m+9)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Muls.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)) (6 : Fin (m+9)))) (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product F.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)) (5 : Fin (m+9)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (4 : Fin (m+9))
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+9)))) (.imp
  (ConstructionProbeMappedPathSyntax.nodeMap node.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
  (m+9)) (4 : Fin (m+9))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin (m+9))
  a.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+9)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge (5 : Fin (m+9)) b.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+9))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin (m+9))
  d.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+9)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge (5 : Fin (m+9)) p.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+9))))
  (ConstructionPersistentProfiles.probeProfile w.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
  (m+9)) (6 : Fin (m+9)) (3 : Fin (m+9)) (2 : Fin (m+9)) (1 : Fin (m+9)) (0 : Fin (m+9)) (4 : Fin
  (m+9)))))))))))))))))))))))

theorem persistentProfile_freeClosed {m : Nat} (J E Domains F Muls w i a b d p node : Fin m) :
    (persistentProfile J E Domains F Muls w i a b d p node).FreeClosed := by
  simp -implicitDefEqProofs [persistentProfile,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionPersistentProfiles.probeProfile_freeClosed]

theorem persistentProfile_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Muls w i a b d p node : Fin m) :
    Project.Formula.satisfies env (persistentProfile J E Domains F Muls w i a b d p node) ↔
      PersistentProfile (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls)
        (env.bound w) (env.bound i) (env.bound a) (env.bound b) (env.bound d) (env.bound p) (env.bound node) := by
  simp only [persistentProfile,PersistentProfile,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    ConstructionPersistentProfiles.probeProfile_semantics hM]
  rfl

def profileTransport {m : Nat} (J E Domains F Muls i D L G f : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (4 : Fin (m+6))) (.bound
  D.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (3 : Fin (m+6))) (.bound
  D.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (2 : Fin (m+6))) (.bound
  D.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (1 : Fin (m+6))) (.bound
  D.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+6))
  (5 : Fin (m+6)) D.succ.succ.succ.succ.succ.succ)) (.imp (persistentProfile J.succ.succ.succ.succ.succ.succ
  E.succ.succ.succ.succ.succ.succ Domains.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ
  Muls.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) i.succ.succ.succ.succ.succ.succ (4 : Fin (m+6)) (3 : Fin
  (m+6)) (2 : Fin (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6))) (.existsE (.existsE (.existsE (.existsE (.existsE
  (.conj (ConstructionProbeMappedPathSyntax.nodeMap (5 : Fin (m+11))
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin (m+11))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin (m+11)) (3 : Fin
  (m+11)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+11)) (2 : Fin (m+11)))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (7 : Fin (m+11)) (1 : Fin (m+11)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+11)) (0 : Fin (m+11))))
  (ConstructionPersistentProfiles.probeProfile (10 : Fin (m+11))
  L.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+11)) (2 : Fin (m+11)) (1 : Fin (m+11))
  (0 : Fin (m+11)) (4 : Fin (m+11)))))))))))))))))))))))))

theorem profileTransport_freeClosed {m : Nat} (J E Domains F Muls i D L G f : Fin m) :
    (profileTransport J E Domains F Muls i D L G f).FreeClosed := by
  simp -implicitDefEqProofs [profileTransport,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    persistentProfile_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
    ConstructionPersistentProfiles.probeProfile_freeClosed]

theorem profileTransport_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Muls i D L G f : Fin m) :
    Project.Formula.satisfies env (profileTransport J E Domains F Muls i D L G f) ↔
      ProfileTransport (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls)
        (env.bound i) (env.bound D) (env.bound L) (env.bound G) (env.bound f) := by
  simp only [profileTransport,ProfileTransport,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),persistentProfile_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionPersistentProfiles.probeProfile_semantics hM]
  rfl

end PPAC.Migration.ConstructionDirectedProfiles
