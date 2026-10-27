/- Pinned original request map and concrete Probe/Merger normal forms.
Retain ACTUAL parent source data together with full weighted Step and
current freshness; selector must choose an original operation witness.
Consumer: Candidate/Picked/Extended/global map_succ; exact cones next. -/
import PPAC.Migration.ConstructionRoundFresh
import PPAC.Migration.ConstructionOperationSource

namespace PPAC.Migration.ConstructionRoundSource
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRoundFields
open ConstructionRoundFresh (ProbeWitness)
open ConstructionRoundSuccessors (MergerDone)
open ConstructionRequestSchedule (ProbeCode MergerCode)
open ConstructionProbeMappedPath (NodeMap)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Provenance (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero one request N mulN eN markN f W G unit O roots : M.Carrier .set) : Prop :=
  (∃ a b node fa fb mapped, ProbeCode zero a b node request ∧
    PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f ∧ NodeMap node f mapped ∧
    ConstructionOperationSource.Probe hM w N mulN eN zero markN fa fb mapped W G unit O roots) ∨
  ∃ n P PN, MergerCode one n P request ∧ ConstructionMergerPrescriptionMap.Graph P f PN ∧
    ConstructionOperationSource.Merger w n N mulN eN zero PN W G unit O roots


def provenance {m : Nat} (w zero one request N mulN eN markN f W G unit O roots : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ConstructionRequestSchedule.probeCode zero.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6))
  (3 : Fin (m+6)) request.succ.succ.succ.succ.succ.succ) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (2 : Fin (m+6)))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ (4 : Fin (m+6)) (1 : Fin
  (m+6)))) (.conj (ConstructionProbeMappedPathSyntax.nodeMap (3 : Fin (m+6)) f.succ.succ.succ.succ.succ.succ
  (0 : Fin (m+6))) (ConstructionOperationSource.probe w.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ eN.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ markN.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (1 : Fin (m+6)) (0
  : Fin (m+6)) W.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ
  unit.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ
  roots.succ.succ.succ.succ.succ.succ))))))))))) (.existsE (.existsE (.existsE (.conj
  (ConstructionRequestSchedule.mergerCode one.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3))
  request.succ.succ.succ) (.conj (ConstructionMergerPrescriptionMapSyntax.graph (1 : Fin (m+3))
  f.succ.succ.succ (0 : Fin (m+3))) (ConstructionOperationSource.merger w.succ.succ.succ (2 : Fin (m+3))
  N.succ.succ.succ mulN.succ.succ.succ eN.succ.succ.succ zero.succ.succ.succ (0 : Fin (m+3))
  W.succ.succ.succ G.succ.succ.succ unit.succ.succ.succ O.succ.succ.succ roots.succ.succ.succ)))))))

theorem provenance_freeClosed {m : Nat} (w zero one request N mulN eN markN f W G unit O roots : Fin m) :
    (provenance w zero one request N mulN eN markN f W G unit O roots).FreeClosed := by
  simp -implicitDefEqProofs [provenance,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionOperationSource.probe_freeClosed,ConstructionRequestSchedule.mergerCode_freeClosed,ConstructionMergerPrescriptionMapSyntax.graph_freeClosed,ConstructionOperationSource.merger_freeClosed]

theorem provenance_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero one request N mulN eN markN f W G unit O roots : Fin m) :
    Project.Formula.satisfies env (provenance w zero one request N mulN eN markN f W G unit O roots) ↔ Provenance hM (env.bound w) (env.bound zero) (env.bound one) (env.bound request) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound f) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound roots) := by
  simp only [provenance,Provenance,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_disj_iff,ConstructionRequestSchedule.probeCode_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionOperationSource.probe_semantics hM,ConstructionRequestSchedule.mergerCode_semantics hM,ConstructionMergerPrescriptionMapSyntax.graph_semantics hM,ConstructionOperationSource.merger_semantics hM]
  rfl

theorem probe (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one u D mul e mark H C N mulN eN markN HN CN f a b node request : M.Carrier .set}
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
    (hPath : ConstructionProbePath.Path w D mul e zero a node)
    (hCode : ProbeCode zero a b node request) :
    ∃ W G unitW markW HL LC O baseW gen,
      ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW ∧
      ProbeWitness w W G markW baseW a b node gen ∧
      (∀ x, ¬ PureKuratowski.PairMember M x gen O) ∧
      Provenance hM w zero one request N mulN eN markN f W G unitW O gen := by
  have hObjN0 := hObjN
  obtain ⟨fa,fb,mappedN,hfa,hfb,hbN,hneN,_,hMapN,hPathN,_⟩ :=
    ConstructionRequestMaps.probe_map hM hf.1 hf.2.1 hf.2.2.1 hb hne hPath
  obtain ⟨hm,hCon,hJoins,hmark,hmarkNe,hH,hHB,hC,hCB,hUniform,_,_⟩ := hObjN
  obtain ⟨S,A,E,Off,V,projection,hAlphaData,W,unitW,J,G,O,markW,KG,P,gen,oa,ob,mappedW,
    hWordCarrier,hOldUnit,hJ,hG,hMul,hMon,hConW,hJoinsW,hO,hCons,hEmb,hGates,hMark,hMarkMem,hMarkNe,
    hKG,hKGGraph,hPMap,hPGraph,hGen,ha,hbCurrent,hMapW,hProfile,hNotOld,hCard,hProfiles,HL,GateCap,LC,hFields,hValues⟩ :=
    ConstructionProbeParent.exists_probe_with_source hM hw hz hzw hQ hR hu hone htop hm hCon hbN hneN hH hHB hC hCB hUniform hJoins hmark hmarkNe hPathN
  obtain ⟨hHL,_,hHBW,_,_,_,hLC,_,hCBW,hUniformW,hExactW,_,_,hSup⟩ := hFields
  have hProd : ConstructionProbeLiftHom.PreservesProducts mulN G O :=
    fun x y z ox oy oz hxyz hx hy hz => hEmb.2.1 x y z ox oy oz hx hy hz hxyz
  have hSucc : Successor hM w Q R top zero N mulN eN markN HN CN W G unitW markW HL LC O :=
    ⟨⟨hMon,hConW,hJoinsW,hMarkMem,hMarkNe,hHL,hHBW,hLC,hCBW,hUniformW,hExactW,J,hJ,hG⟩,
    ⟨hCons,hProd,hEmb.1,hMark,fun x ox r hx => (hValues x ox r hx).1,
      fun x ox r hx => (hValues x ox r hx).2,hSup⟩,hO,hGates,hProfiles,hCard⟩

  have hBuilt : ConstructionOperationSource.Probe hM w N mulN eN zero markN fa fb mappedN W G unitW O gen :=
    ⟨hPathN,hbN,hneN,S,A,E,projection,KG,P,hAlphaData,hWordCarrier,hOldUnit,hMul,hO,hKG,hKGGraph,hPMap,hPGraph,hGen⟩
  obtain ⟨baseW,_,hComp,hBase⟩ := exists_fromBase hM hObjN0.1 hSucc.1.1 hf hSucc.2.1
  refine ⟨W,G,unitW,markW,HL,LC,O,baseW,gen,
    ⟨hSucc,hComp,hBase,fun hp => profiles_comp hComp hp hSucc.2.2.2.2.1⟩,?_,hNotOld,?_⟩
  · exact ⟨oa,ob,mappedW,(hComp a oa).mpr ⟨fa,hfa,ha⟩,(hComp b ob).mpr ⟨fb,hfb,hbCurrent⟩,
      node_comp hComp hMapN hMapW,hProfile⟩
  · exact Or.inl ⟨a,b,node,fa,fb,mappedN,hCode,hfa,hfb,hMapN,hBuilt⟩

theorem merger (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one u D mul e mark H C N mulN eN markN HN CN f n P request : M.Carrier .set}
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
    (hP : ConstructionMergerRelations.Prescription n D P) (hValid : ConstructionMergerRelations.Valid n D mul P)
    (hCode : MergerCode one n P request) :
    ∃ W G unitW markW HL LC O baseW roots,
      ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW ∧
      MergerDone n D W mul G P baseW roots ∧
      (∀ i r x, PureKuratowski.PairMember M i r roots → ¬ PureKuratowski.PairMember M x r O) ∧
      Provenance hM w zero one request N mulN eN markN f W G unitW O roots := by
  have hObjN0 := hObjN
  obtain ⟨PN,hMapGraph,_,hPN,hValidIff,hRel,_⟩ := ConstructionMergerPrescriptionMap.exists_system hM
    hObjD.1 hObjN0.1 hP hf.1 hf.2.1 hObjD.2.2.1
  have hPNValid := hValidIff.mpr hValid
  obtain ⟨hm,hCon,hJoins,hmark,hmarkNe,hH,hHB,hC,hCB,hUniform,_,_⟩ := hObjN
  obtain ⟨Copies,L,projection,K,A,W,I,T,B,G,unitW,hParent,hOldUnit,hMon,hConW,_,hJoinsW,
    O,hO,hCons,hProd,hGates,hOne,hProfiles,roots,hRoots,hRootGraph,hRootLaws,Rest⟩ :=
    ConstructionMergerParent.exists_system hM hw hz hzw hm hCon hJoins hPN hPNValid hQ hn hnp hu hone htop hR hH hHB hC hCB hUniform hmark hmarkNe
  have hParentSource := hParent
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hB,hG,_⟩ := hParent
  obtain ⟨J,CH,CC,_,_,_,_,_,_,unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,
    _,_,hCard,twoW,threeW,fourW,fiveW,sixW,sevenW,eightW,quarterW,eighthW,OffW,ScaleW,FactorW,HL,LC,
    hWord,markW,hMark,hMarkMem,hMarkNe,_,hValues⟩ := Rest
  obtain ⟨hActual,hUniformW,hExactW,hSup⟩ := hWord
  obtain ⟨_,hHL,_,_,hHBW,hLC,_,hCBW,_,_⟩ := hActual
  have hOldSup : ConstructionDirectedHeightCost.OldSuprema hM w Q N W mulN G CN LC O := by
    intro x y ox oy hx hy
    obtain ⟨_,_,cap,hCut,hCap0,hCap1,hUnique⟩ := hSup x y ox oy ((hO x ox).mp hx) ((hO y oy).mp hy)
    obtain ⟨f0,hF0,hU0,hL0⟩ := hCap0
    obtain ⟨f1,hF1,hU1,hL1⟩ := hCap1
    exact ⟨f0,f1,cap,hF0,hF1,hCut,⟨f0,hF0,hU0,hL0⟩,⟨f1,hF1,hU1,hL1⟩,hUnique⟩
  have hSucc : Successor hM w Q R top zero N mulN eN markN HN CN W G unitW markW HL LC O :=
    ⟨⟨hMon,hConW,hJoinsW,hMarkMem,hMarkNe,hHL,hHBW,hLC,hCBW,hUniformW,hExactW,B,hB,hG⟩,
    ⟨hCons,hProd,hOne,hMark,fun x ox r hx => (hValues x ox r hx).1,
      fun x ox r hx => (hValues x ox r hx).2,hOldSup⟩,hO,hGates,hProfiles,hCard⟩

  have hBuilt : ConstructionOperationSource.Merger w n N mulN eN zero PN W G unitW O roots := by
    refine ⟨hPN,hPNValid,Copies,L,projection,K,A,I,T,B,?_⟩
    rcases hParentSource with ⟨c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18⟩
    exact ⟨c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,hOldUnit,hO,hRootGraph,hRootLaws⟩
  have hNotOld := hRootLaws.2.2
  have hReal := hRootLaws.2.1
  obtain ⟨baseW,_,hComp,hBase⟩ := exists_fromBase hM hObjN0.1 hSucc.1.1 hf hSucc.2.1
  refine ⟨W,G,unitW,markW,HL,LC,O,baseW,roots,
    ⟨hSucc,hComp,hBase,fun hp => profiles_comp hComp hp hSucc.2.2.2.2.1⟩,⟨hRoots,?_,?_⟩,hNotOld,?_⟩
  · intro i j x y ri rj ox oy u v hir hjr hx hy hpu hpv
    obtain ⟨nx,hfx,hOx⟩ := (hComp x ox).mp hx
    obtain ⟨ny,hfy,hOy⟩ := (hComp y oy).mp hy
    exact (hReal i j nx ny ri rj ox oy u v hir hjr hOx hOy hpu hpv).trans (hRel i j x y nx ny hfx hfy)
  · intro i r x hir hx
    obtain ⟨y,_,hy⟩ := (hComp x r).mp hx
    exact hNotOld i r y hir hy
  · exact Or.inr ⟨n,P,PN,hCode,hMapGraph,hBuilt⟩

end PPAC.Migration.ConstructionRoundSource
