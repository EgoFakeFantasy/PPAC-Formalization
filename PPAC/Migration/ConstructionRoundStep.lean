/- Pinned MonoidRounds.Round.step:93/fromBase:103 and Request operation
witnesses. Execute either base request at the SAME current weighted stage,
construct its actual successor/inclusion and SAME fromBase composition.
No supplied successor, composite, profile, root or cap is an input. -/
import PPAC.Migration.ConstructionRoundSuccessors

namespace PPAC.Migration.ConstructionRoundStep
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRoundFields
open ConstructionRoundSuccessors
open ConstructionProbeMappedPath (NodeMap)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Step (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW : M.Carrier .set) : Prop :=
  Successor hM w Q R top zero N mulN eN markN HN CN W G unitW markW HL LC O ∧
    NodeMap f O baseW ∧ MapFields hM w Q D W mul G e unitW mark markW H C HL LC baseW ∧
    (Profiles w D N mul mulN f → Profiles w D W mul G baseW)

theorem probe_step (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one u D mul e mark H C N mulN eN markN HN CN f a b node : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (htop : ConstructionRealCuts.Principal hM w Q u top)
    (hObjN : ObjectFields hM w Q R top N mulN eN markN HN CN)
    (hf : MapFields hM w Q D N mul mulN e eN mark markN H C HN CN f)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hPath : ConstructionProbePath.Path w D mul e zero a node) :
    ∃ W G unitW markW HL LC O baseW,
      Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW ∧
      ProbeDone w W G markW baseW a b node := by
  obtain ⟨fa,fb,mappedN,hfa,hfb,hbN,hneN,_,hMapN,hPathN,_⟩ :=
    ConstructionRequestMaps.probe_map hM hf.1 hf.2.1 hf.2.2.1 hb hne hPath
  obtain ⟨W,G,unitW,markW,HL,LC,O,hSucc,gen,oa,ob,mappedW,ha,hb',hMapW,hProfile,hNotOld⟩ :=
    ConstructionRoundSuccessors.probe hM hw hz hzw hQ hR hu hone htop hObjN hbN hneN hPathN
  obtain ⟨baseW,_,hComp,hBase⟩ := exists_fromBase hM hObjN.1 hSucc.1.1 hf hSucc.2.1
  refine ⟨W,G,unitW,markW,HL,LC,O,baseW,
    ⟨hSucc,hComp,hBase,fun hp => profiles_comp hComp hp hSucc.2.2.2.2.1⟩,
    gen,oa,ob,mappedW,(hComp a oa).mpr ⟨fa,hfa,ha⟩,(hComp b ob).mpr ⟨fb,hfb,hb'⟩,
    node_comp hComp hMapN hMapW,hProfile,?_⟩
  intro x hx
  obtain ⟨y,_,hy⟩ := (hComp x gen).mp hx
  exact hNotOld y hy

theorem merger_step (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one u D mul e mark H C N mulN eN markN HN CN f n P : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (htop : ConstructionRealCuts.Principal hM w Q u top)
    (hObjD : ObjectFields hM w Q R top D mul e mark H C)
    (hObjN : ObjectFields hM w Q R top N mulN eN markN HN CN)
    (hf : MapFields hM w Q D N mul mulN e eN mark markN H C HN CN f)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hP : ConstructionMergerRelations.Prescription n D P) (hValid : ConstructionMergerRelations.Valid n D mul P) :
    ∃ W G unitW markW HL LC O baseW roots,
      Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW ∧
      MergerDone n D W mul G P baseW roots := by
  obtain ⟨PN,_,_,hPN,hValidIff,hRel,_⟩ := ConstructionMergerPrescriptionMap.exists_system hM
    hObjD.1 hObjN.1 hP hf.1 hf.2.1 hObjD.2.2.1
  obtain ⟨W,G,unitW,markW,HL,LC,O,roots,hSucc,hRoots,hReal,hNotOld⟩ :=
    ConstructionRoundSuccessors.merger hM hw hz hzw hQ hR hu hone htop hObjN hn hnp hPN (hValidIff.mpr hValid)
  obtain ⟨baseW,_,hComp,hBase⟩ := exists_fromBase hM hObjN.1 hSucc.1.1 hf hSucc.2.1
  refine ⟨W,G,unitW,markW,HL,LC,O,baseW,roots,
    ⟨hSucc,hComp,hBase,fun hp => profiles_comp hComp hp hSucc.2.2.2.2.1⟩,hRoots,?_,?_⟩
  · intro i j x y ri rj ox oy u v hir hjr hx hy hpu hpv
    obtain ⟨nx,hfx,hOx⟩ := (hComp x ox).mp hx
    obtain ⟨ny,hfy,hOy⟩ := (hComp y oy).mp hy
    exact (hReal i j nx ny ri rj ox oy u v hir hjr hOx hOy hpu hpv).trans (hRel i j x y nx ny hfx hfy)
  · intro i r x hir hx
    obtain ⟨y,_,hy⟩ := (hComp x r).mp hx
    exact hNotOld i r y hir hy

def Steps (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero D mul e mark H C N mulN eN markN HN CN f : M.Carrier .set) : Prop :=
  (∀ a b node, (Project.FirstOrderSemantics.reduct M).mem b D → b ≠ e →
    ConstructionProbePath.Path w D mul e zero a node →
    ∃ W G unitW markW HL LC O baseW,
      Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW ∧
      ProbeDone w W G markW baseW a b node) ∧
  ∀ n P, (Project.FirstOrderSemantics.reduct M).mem n w →
    (∃ i, (Project.FirstOrderSemantics.reduct M).mem i n) →
    ConstructionMergerRelations.Prescription n D P → ConstructionMergerRelations.Valid n D mul P →
    ∃ W G unitW markW HL LC O baseW roots,
      Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW ∧
      MergerDone n D W mul G P baseW roots

theorem steps (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one u D mul e mark H C N mulN eN markN HN CN f : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (htop : ConstructionRealCuts.Principal hM w Q u top)
    (hObjD : ObjectFields hM w Q R top D mul e mark H C)
    (hObjN : ObjectFields hM w Q R top N mulN eN markN HN CN)
    (hf : MapFields hM w Q D N mul mulN e eN mark markN H C HN CN f) :
    Steps hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f :=
  ⟨fun _ _ _ hb hne hp => probe_step hM hw hz hzw hQ hR hu hone htop hObjN hf hb hne hp,
    fun _ _ hn hnp hp hv => merger_step hM hw hz hzw hQ hR hu hone htop hObjD hObjN hf hn hnp hp hv⟩

end PPAC.Migration.ConstructionRoundStep
