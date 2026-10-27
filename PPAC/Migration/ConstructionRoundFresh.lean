/- Pinned Round.creates_probe / CompleteRounds.probe_new and Merger roots.
Keep the actual parent CURRENT-inclusion freshness, not just the weaker
round-base image consequence. The existing ninth tuple field stores the
ACTUAL probe generator (or actual Merger root graph), never a zero placeholder.
Consumer: SAME Candidate/Picked/Extended and global map_succ. -/
import PPAC.Migration.ConstructionRequestSchedule

namespace PPAC.Migration.ConstructionRoundFresh
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRoundFields
open ConstructionRoundSuccessors (MergerDone)
open ConstructionRequestSchedule (ProbeCode MergerCode)
open ConstructionProbeMappedPath (NodeMap)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ProbeWitness (w W G mark base a b node gen : M.Carrier .set) : Prop :=
  ∃ oa ob mapped, PureKuratowski.PairMember M a oa base ∧ PureKuratowski.PairMember M b ob base ∧
    NodeMap node base mapped ∧ ConstructionPersistentProfiles.ProbeProfile w W G oa ob mark gen mapped

def Completed (w D mul zero one request W G mark O base roots : M.Carrier .set) : Prop :=
  (∃ a b node, ProbeCode zero a b node request ∧ ProbeWitness w W G mark base a b node roots ∧
    ∀ x, ¬ PureKuratowski.PairMember M x roots O) ∨
  ∃ n P, MergerCode one n P request ∧ MergerDone n D W mul G P base roots ∧
    ∀ i r x, PureKuratowski.PairMember M i r roots → ¬ PureKuratowski.PairMember M x r O


def probeWitness {m : Nat} (w W G mark base a b node gen : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge base.succ.succ.succ
  a.succ.succ.succ (2 : Fin (m+3)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  base.succ.succ.succ b.succ.succ.succ (1 : Fin (m+3)))) (.conj (ConstructionProbeMappedPathSyntax.nodeMap
  node.succ.succ.succ base.succ.succ.succ (0 : Fin (m+3))) (ConstructionPersistentProfiles.probeProfile
  w.succ.succ.succ W.succ.succ.succ G.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)) mark.succ.succ.succ
  gen.succ.succ.succ (0 : Fin (m+3)))))))))

theorem probeWitness_freeClosed {m : Nat} (w W G mark base a b node gen : Fin m) :
    (probeWitness w W G mark base a b node gen).FreeClosed := by
  simp -implicitDefEqProofs [probeWitness,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionPersistentProfiles.probeProfile_freeClosed]

theorem probeWitness_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w W G mark base a b node gen : Fin m) :
    Project.Formula.satisfies env (probeWitness w W G mark base a b node gen) ↔ ProbeWitness (env.bound w) (env.bound W) (env.bound G) (env.bound mark) (env.bound base) (env.bound a) (env.bound b) (env.bound node) (env.bound gen) := by
  simp only [probeWitness,ProbeWitness,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionPersistentProfiles.probeProfile_semantics hM]
  rfl


def completed {m : Nat} (w D mul zero one request W G mark O base roots : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.existsE (.existsE (.conj (ConstructionRequestSchedule.probeCode zero.succ.succ.succ (2 :
  Fin (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3)) request.succ.succ.succ) (.conj (probeWitness w.succ.succ.succ
  W.succ.succ.succ G.succ.succ.succ mark.succ.succ.succ base.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3))
  (0 : Fin (m+3)) roots.succ.succ.succ) (.forallE (.neg (ProjectSyntax.encode id (Source.SetLanguage.edge
  O.succ.succ.succ.succ (0 : Fin (m+4)) roots.succ.succ.succ.succ))))))))) (.existsE (.existsE (.conj
  (ConstructionRequestSchedule.mergerCode one.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)) request.succ.succ)
  (.conj (ConstructionRoundStepSyntax.mergerDone (1 : Fin (m+2)) D.succ.succ W.succ.succ mul.succ.succ
  G.succ.succ (0 : Fin (m+2)) base.succ.succ roots.succ.succ) (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge roots.succ.succ.succ.succ.succ (2 : Fin (m+5)) (1 : Fin
  (m+5)))) (.neg (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ.succ (0 : Fin
  (m+5)) (1 : Fin (m+5))))))))))))))

theorem completed_freeClosed {m : Nat} (w D mul zero one request W G mark O base roots : Fin m) :
    (completed w D mul zero one request W G mark O base roots).FreeClosed := by
  simp -implicitDefEqProofs [completed,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,probeWitness_freeClosed,ConstructionRequestSchedule.mergerCode_freeClosed,ConstructionRoundStepSyntax.mergerDone_freeClosed]

theorem completed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul zero one request W G mark O base roots : Fin m) :
    Project.Formula.satisfies env (completed w D mul zero one request W G mark O base roots) ↔ Completed (env.bound w) (env.bound D) (env.bound mul) (env.bound zero) (env.bound one) (env.bound request) (env.bound W) (env.bound G) (env.bound mark) (env.bound O) (env.bound base) (env.bound roots) := by
  simp only [completed,Completed,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_disj_iff,ConstructionRequestSchedule.probeCode_semantics hM,probeWitness_semantics hM,ConstructionRequestSchedule.mergerCode_semantics hM,ConstructionRoundStepSyntax.mergerDone_semantics hM]
  rfl


theorem probe_of_completed {w D mul zero one request W G mark O base roots a b node : M.Carrier .set}
    (hne : zero ≠ one) (hc : ProbeCode zero a b node request)
    (h : Completed w D mul zero one request W G mark O base roots) :
    ProbeWitness w W G mark base a b node roots ∧ ∀ x, ¬ PureKuratowski.PairMember M x roots O := by
  rcases h with ⟨a',b',node',hc',hp,hFresh⟩ | ⟨n,P,hc',_⟩
  · obtain ⟨ea,eb,en⟩ := ConstructionRequestSchedule.probe_code_injective hc hc'
    subst a'; subst b'; subst node'
    exact ⟨hp,hFresh⟩
  · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hc hc')

theorem merger_of_completed {w D mul zero one request W G mark O base roots n P : M.Carrier .set}
    (hne : zero ≠ one) (hc : MergerCode one n P request)
    (h : Completed w D mul zero one request W G mark O base roots) :
    MergerDone n D W mul G P base roots ∧
    ∀ i r x, PureKuratowski.PairMember M i r roots → ¬ PureKuratowski.PairMember M x r O := by
  rcases h with ⟨a,b,node,hc',_⟩ | ⟨n',P',hc',hp,hFresh⟩
  · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hc' hc)
  · obtain ⟨en,ep⟩ := ConstructionRequestSchedule.merger_code_injective hc hc'
    subst n'; subst P'
    exact ⟨hp,hFresh⟩

theorem probe (hM : FirstOrder.Theory.Models M nativeZF)
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
    ∃ W G unitW markW HL LC O baseW gen,
      ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW ∧
      ProbeWitness w W G markW baseW a b node gen ∧
      (∀ x, ¬ PureKuratowski.PairMember M x gen O) := by
  obtain ⟨fa,fb,mappedN,hfa,hfb,hbN,hneN,_,hMapN,hPathN,_⟩ :=
    ConstructionRequestMaps.probe_map hM hf.1 hf.2.1 hf.2.2.1 hb hne hPath
  obtain ⟨W,G,unitW,markW,HL,LC,O,hSucc,gen,oa,ob,mappedW,ha,hb',hMapW,hProfile,hNotOld⟩ :=
    ConstructionRoundSuccessors.probe hM hw hz hzw hQ hR hu hone htop hObjN hbN hneN hPathN
  obtain ⟨baseW,_,hComp,hBase⟩ := exists_fromBase hM hObjN.1 hSucc.1.1 hf hSucc.2.1
  refine ⟨W,G,unitW,markW,HL,LC,O,baseW,gen,
    ⟨hSucc,hComp,hBase,fun hp => profiles_comp hComp hp hSucc.2.2.2.2.1⟩,?_,hNotOld⟩
  exact ⟨oa,ob,mappedW,(hComp a oa).mpr ⟨fa,hfa,ha⟩,(hComp b ob).mpr ⟨fb,hfb,hb'⟩,
    node_comp hComp hMapN hMapW,hProfile⟩

theorem merger (hM : FirstOrder.Theory.Models M nativeZF)
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
      ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW ∧
      MergerDone n D W mul G P baseW roots ∧
      (∀ i r x, PureKuratowski.PairMember M i r roots → ¬ PureKuratowski.PairMember M x r O) := by
  obtain ⟨PN,_,_,hPN,hValidIff,hRel,_⟩ := ConstructionMergerPrescriptionMap.exists_system hM
    hObjD.1 hObjN.1 hP hf.1 hf.2.1 hObjD.2.2.1
  obtain ⟨W,G,unitW,markW,HL,LC,O,roots,hSucc,hRoots,hReal,hNotOld⟩ :=
    ConstructionRoundSuccessors.merger hM hw hz hzw hQ hR hu hone htop hObjN hn hnp hPN (hValidIff.mpr hValid)
  obtain ⟨baseW,_,hComp,hBase⟩ := exists_fromBase hM hObjN.1 hSucc.1.1 hf hSucc.2.1
  refine ⟨W,G,unitW,markW,HL,LC,O,baseW,roots,
    ⟨hSucc,hComp,hBase,fun hp => profiles_comp hComp hp hSucc.2.2.2.2.1⟩,⟨hRoots,?_,?_⟩,hNotOld⟩
  · intro i j x y ri rj ox oy u v hir hjr hx hy hpu hpv
    obtain ⟨nx,hfx,hOx⟩ := (hComp x ox).mp hx
    obtain ⟨ny,hfy,hOy⟩ := (hComp y oy).mp hy
    exact (hReal i j nx ny ri rj ox oy u v hir hjr hOx hOy hpu hpv).trans (hRel i j x y nx ny hfx hfy)
  · intro i r x hir hx
    obtain ⟨y,_,hy⟩ := (hComp x r).mp hx
    exact hNotOld i r y hir hy

end PPAC.Migration.ConstructionRoundFresh
