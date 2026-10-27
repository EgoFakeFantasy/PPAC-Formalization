/- Pinned MonoidRounds.Request.map / Round.step schedule evaluation.
Concrete Kuratowski codes of the TWO existing Request constructors, then
native Replacement/function construction for arbitrary varying stage domains.
No omega-only stage restriction or Type-level choice of mapped requests. -/
import PPAC.Migration.ConstructionRoundStepSyntax
import PPAC.Migration.ConstructionDirectedMonoidData

namespace PPAC.Migration.ConstructionRequestSchedule
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeMappedPath (NodeMap)
open ConstructionMergerRelations (Prescription Valid)
open ForcingConditionGraphs (FunctionOn function_unique)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ProbeCode (zero a b node q : M.Carrier .set) : Prop :=
  ∃ t s, PureKuratowski.Code M q zero t ∧ PureKuratowski.Code M t a s ∧ PureKuratowski.Code M s b node

def MergerCode (one n P q : M.Carrier .set) : Prop :=
  ∃ t, PureKuratowski.Code M q one t ∧ PureKuratowski.Code M t n P

def Request (w D mul e zero one q : M.Carrier .set) : Prop :=
  (∃ a b node, ProbeCode zero a b node q ∧ (Project.FirstOrderSemantics.reduct M).mem b D ∧
    b ≠ e ∧ ConstructionProbePath.Path w D mul e zero a node) ∨
  (∃ n P, MergerCode one n P q ∧ (Project.FirstOrderSemantics.reduct M).mem n w ∧
    (∃ i, (Project.FirstOrderSemantics.reduct M).mem i n) ∧ Prescription n D P ∧ Valid n D mul P)

def Transport (w D mul e zero one N mulN eN f q qN : M.Carrier .set) : Prop :=
  (∃ a b node fa fb mapped, ProbeCode zero a b node q ∧ ProbeCode zero fa fb mapped qN ∧
    (Project.FirstOrderSemantics.reduct M).mem b D ∧ b ≠ e ∧ ConstructionProbePath.Path w D mul e zero a node ∧
    PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f ∧
    (Project.FirstOrderSemantics.reduct M).mem fb N ∧ fb ≠ eN ∧ MapsTo w N mapped ∧
    NodeMap node f mapped ∧ ConstructionProbePath.Path w N mulN eN zero fa mapped) ∨
  (∃ n P PN, MergerCode one n P q ∧ MergerCode one n PN qN ∧
    (Project.FirstOrderSemantics.reduct M).mem n w ∧ (∃ i, (Project.FirstOrderSemantics.reduct M).mem i n) ∧
    Prescription n D P ∧ Valid n D mul P ∧ ConstructionMergerPrescriptionMap.Graph P f PN ∧
    Prescription n N PN ∧ Valid n N mulN PN)

theorem probe_code_injective {zero a b node a' b' node' q : M.Carrier .set}
    (h1 : ProbeCode zero a b node q) (h2 : ProbeCode zero a' b' node' q) : a = a' ∧ b = b' ∧ node = node' := by
  obtain ⟨t,s,hq,ht,hs⟩ := h1
  obtain ⟨t',s',hq',ht',hs'⟩ := h2
  obtain ⟨_,rfl⟩ := PureKuratowski.code_injective hq hq'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ht ht'
  exact ⟨rfl,PureKuratowski.code_injective hs hs'⟩

theorem merger_code_injective {one n P n' P' q : M.Carrier .set}
    (h1 : MergerCode one n P q) (h2 : MergerCode one n' P' q) : n = n' ∧ P = P' := by
  obtain ⟨t,hq,ht⟩ := h1
  obtain ⟨t',hq',ht'⟩ := h2
  obtain ⟨_,rfl⟩ := PureKuratowski.code_injective hq hq'
  exact PureKuratowski.code_injective ht ht'

theorem probe_code_unique (hM : FirstOrder.Theory.Models M nativeZF) {zero a b node q r : M.Carrier .set}
    (hq : ProbeCode zero a b node q) (hr : ProbeCode zero a b node r) : q = r := by
  obtain ⟨t,s,hq,ht,hs⟩ := hq
  obtain ⟨t',s',hr,ht',hs'⟩ := hr
  have he := KuratowskiZF.code_unique hM hs hs'
  subst s'
  have he := KuratowskiZF.code_unique hM ht ht'
  subst t'
  exact KuratowskiZF.code_unique hM hq hr

theorem merger_code_unique (hM : FirstOrder.Theory.Models M nativeZF) {one n P q r : M.Carrier .set}
    (hq : MergerCode one n P q) (hr : MergerCode one n P r) : q = r := by
  obtain ⟨t,hq,ht⟩ := hq
  obtain ⟨t',hr,ht'⟩ := hr
  have he := KuratowskiZF.code_unique hM ht ht'
  subst t'
  exact KuratowskiZF.code_unique hM hq hr

theorem code_disjoint {zero one a b node n P q : M.Carrier .set} (hne : zero ≠ one)
    (hp : ProbeCode zero a b node q) (hm : MergerCode one n P q) : False := by
  obtain ⟨_,_,hp,_,_⟩ := hp
  obtain ⟨_,hm,_⟩ := hm
  exact hne (PureKuratowski.code_injective hp hm).1

theorem zero_ne_one {zero one : M.Carrier .set}
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) : zero ≠ one := by
  obtain ⟨z,_,hSucc⟩ := hone
  intro heq
  exact hz z (heq.symm ▸ (hSucc z).mpr (Or.inr (fun _ => Iff.rfl)))

theorem transport_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero one N mulN eN f q : M.Carrier .set}
    (hMaps : ConstructionRequestMaps.MapsRequests w D mul e zero N mulN eN f)
    (hq : Request w D mul e zero one q) : ∃ qN, Transport w D mul e zero one N mulN eN f q qN := by
  rcases hq with ⟨a,b,node,hCode,hb,hne,hPath⟩ | ⟨n,P,hCode,hn,hnp,hP,hValid⟩
  · obtain ⟨fa,fb,mapped,hfa,hfb,hfbN,hneN,hmapped,hNode,hPathN,_⟩ := hMaps.1 a b node hb hne hPath
    obtain ⟨s,hs⟩ := KuratowskiZF.exists_code hM fb mapped
    obtain ⟨t,ht⟩ := KuratowskiZF.exists_code hM fa s
    obtain ⟨qN,hqN⟩ := KuratowskiZF.exists_code hM zero t
    exact ⟨qN,Or.inl ⟨a,b,node,fa,fb,mapped,hCode,⟨t,s,hqN,ht,hs⟩,hb,hne,hPath,hfa,hfb,hfbN,hneN,hmapped,hNode,hPathN⟩⟩
  · obtain ⟨PN,hGraph,_,_,_,hPN,hValidN,_⟩ := hMaps.2 n P hn hnp hP hValid
    obtain ⟨t,ht⟩ := KuratowskiZF.exists_code hM n PN
    obtain ⟨qN,hqN⟩ := KuratowskiZF.exists_code hM one t
    exact ⟨qN,Or.inr ⟨n,P,PN,hCode,⟨t,hqN,ht⟩,hn,hnp,hP,hValid,hGraph,hPN,hValidN⟩⟩

theorem transport_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero one N mulN eN f q r s : M.Carrier .set}
    (hne : zero ≠ one) (hf : MapsTo D N f)
    (hr : Transport w D mul e zero one N mulN eN f q r)
    (hs : Transport w D mul e zero one N mulN eN f q s) : r = s := by
  rcases hr with ⟨a,b,node,fa,fb,mapped,hCode,hOut,_,_,_,ha,hb,_,_,hMapped,hNode,_⟩ |
    ⟨n,P,PN,hCode,hOut,_,_,_,_,hGraph,_,_⟩
  · rcases hs with ⟨a',b',node',fa',fb',mapped',hCode',hOut',_,_,_,ha',hb',_,_,hMapped',hNode',_⟩ |
      ⟨n',P',PN',hCode',_,_⟩
    · obtain ⟨rfl,rfl,rfl⟩ := probe_code_injective hCode hCode'
      have ea := function_unique hf.1 ha ha'
      have eb := function_unique hf.1 hb hb'
      subst fa'; subst fb'
      have em := ConstructionRequestMaps.node_map_unique hM hMapped hMapped' hNode hNode'
      subst mapped'
      exact probe_code_unique hM hOut hOut'
    · exact (code_disjoint hne hCode hCode').elim
  · rcases hs with ⟨a',b',node',fa',fb',mapped',hCode',_,_⟩ |
      ⟨n',P',PN',hCode',hOut',_,_,_,_,hGraph',_,_⟩
    · exact (code_disjoint hne hCode' hCode).elim
    · obtain ⟨rfl,rfl⟩ := merger_code_injective hCode hCode'
      have ep := ConstructionMergerPrescriptionMap.graph_unique hM hGraph hGraph'
      subst PN'
      exact merger_code_unique hM hOut hOut'

theorem transport_target {w D mul e zero one N mulN eN f q qN : M.Carrier .set}
    (h : Transport w D mul e zero one N mulN eN f q qN) : Request w N mulN eN zero one qN := by
  rcases h with ⟨_,_,_,fa,fb,mapped,_,hCode,_,_,_,_,_,hb,hne,_,_,hPath⟩ |
    ⟨n,_,PN,_,hCode,hn,hnp,_,_,_,hPN,hValid⟩
  · exact Or.inl ⟨fa,fb,mapped,hCode,hb,hne,hPath⟩
  · exact Or.inr ⟨n,PN,hCode,hn,hnp,hPN,hValid⟩

def BaseMaps (J Domains Muls Units Origins D mul e : M.Carrier .set) : Prop :=
  ∀ i N mulN eN f, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i N Domains → PureKuratowski.PairMember M i mulN Muls →
    PureKuratowski.PairMember M i eN Units → PureKuratowski.PairMember M i f Origins →
    ConstructionProbeConservative.Conservative D N mul mulN f ∧
    ConstructionProbeLiftHom.PreservesProducts mul mulN f ∧ PureKuratowski.PairMember M e eN f

def Requests (Schedule w D mul e zero one : M.Carrier .set) : Prop :=
  ∀ i q, PureKuratowski.PairMember M i q Schedule → Request w D mul e zero one q

def Value (w D mul e zero one Domains Muls Units Origins Schedule i qN : M.Carrier .set) : Prop :=
  ∃ N mulN eN f q, PureKuratowski.PairMember M i N Domains ∧ PureKuratowski.PairMember M i mulN Muls ∧
    PureKuratowski.PairMember M i eN Units ∧ PureKuratowski.PairMember M i f Origins ∧
    PureKuratowski.PairMember M i q Schedule ∧ Transport w D mul e zero one N mulN eN f q qN

def Graph (w D mul e zero one J Domains Muls Units Origins Schedule Out : M.Carrier .set) : Prop :=
  ∀ i qN, PureKuratowski.PairMember M i qN Out ↔
    (Project.FirstOrderSemantics.reduct M).mem i J ∧ Value w D mul e zero one Domains Muls Units Origins Schedule i qN


def probeCode {m : Nat} (zero a b node q : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound q.succ.succ) (.bound zero.succ.succ) (.bound
  (1 : Fin (m+2)))) (.conj (PureKuratowskiProject.code (.bound (1 : Fin (m+2))) (.bound a.succ.succ) (.bound
  (0 : Fin (m+2)))) (PureKuratowskiProject.code (.bound (0 : Fin (m+2))) (.bound b.succ.succ) (.bound
  node.succ.succ))))))

theorem probeCode_freeClosed {m : Nat} (zero a b node q : Fin m) :
    (probeCode zero a b node q).FreeClosed := by
  simp -implicitDefEqProofs [probeCode,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem probeCode_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero a b node q : Fin m) :
    Project.Formula.satisfies env (probeCode zero a b node q) ↔ ProbeCode (env.bound zero) (env.bound a) (env.bound b) (env.bound node) (env.bound q) := by
  simp only [probeCode,ProbeCode,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    KuratowskiZF.code_correct hM]
  rfl


def mergerCode {m : Nat} (one n P q : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (PureKuratowskiProject.code (.bound q.succ) (.bound one.succ) (.bound (0 : Fin (m+1))))
  (PureKuratowskiProject.code (.bound (0 : Fin (m+1))) (.bound n.succ) (.bound P.succ))))

theorem mergerCode_freeClosed {m : Nat} (one n P q : Fin m) :
    (mergerCode one n P q).FreeClosed := by
  simp -implicitDefEqProofs [mergerCode,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem mergerCode_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (one n P q : Fin m) :
    Project.Formula.satisfies env (mergerCode one n P q) ↔ MergerCode (env.bound one) (env.bound n) (env.bound P) (env.bound q) := by
  simp only [mergerCode,MergerCode,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    KuratowskiZF.code_correct hM]
  rfl


def request {m : Nat} (w D mul e zero one q : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.existsE (.existsE (.conj (probeCode zero.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3))
  (0 : Fin (m+3)) q.succ.succ.succ) (.conj (.mem (.bound (1 : Fin (m+3))) (.bound D.succ.succ.succ)) (.conj
  (.neg (Project.Formula.extensionalEq (.bound (1 : Fin (m+3))) (.bound e.succ.succ.succ)))
  (ConstructionProbePath.path w.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  zero.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))))))))) (.existsE (.existsE (.conj (mergerCode
  one.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)) q.succ.succ) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound
  w.succ.succ)) (.conj (.existsE (.mem (.bound (0 : Fin (m+3))) (.bound (1 : Fin (m+2)).succ))) (.conj
  (ConstructionMergerRelations.prescription (1 : Fin (m+2)) D.succ.succ (0 : Fin (m+2)))
  (ConstructionMergerRelations.valid (1 : Fin (m+2)) D.succ.succ mul.succ.succ (0 : Fin (m+2))))))))))

theorem request_freeClosed {m : Nat} (w D mul e zero one q : Fin m) :
    (request w D mul e zero one q).FreeClosed := by
  simp -implicitDefEqProofs [request,Definitional.Formula.FreeClosed,probeCode_freeClosed,mergerCode_freeClosed,Project.Formula.extensionalEq,ConstructionProbePath.path_freeClosed,ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed]

theorem request_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero one q : Fin m) :
    Project.Formula.satisfies env (request w D mul e zero one q) ↔ Request (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound one) (env.bound q) := by
  simp only [request,Request,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    probeCode_semantics hM,mergerCode_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionProbePath.path_semantics hM,ConstructionMergerRelations.prescription_semantics hM,ConstructionMergerRelations.valid_semantics hM]
  rfl


def transport {m : Nat} (w D mul e zero one N mulN eN f q qN : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (probeCode
  zero.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)) (3 : Fin (m+6))
  q.succ.succ.succ.succ.succ.succ) (.conj (probeCode zero.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (1 :
  Fin (m+6)) (0 : Fin (m+6)) qN.succ.succ.succ.succ.succ.succ) (.conj (.mem (.bound (4 : Fin (m+6))) (.bound
  D.succ.succ.succ.succ.succ.succ)) (.conj (.neg (Project.Formula.extensionalEq (.bound (4 : Fin (m+6)))
  (.bound e.succ.succ.succ.succ.succ.succ))) (.conj (ConstructionProbePath.path
  w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (3 : Fin (m+6))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (2 : Fin
  (m+6)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ (4 : Fin
  (m+6)) (1 : Fin (m+6)))) (.conj (.mem (.bound (1 : Fin (m+6))) (.bound N.succ.succ.succ.succ.succ.succ))
  (.conj (.neg (Project.Formula.extensionalEq (.bound (1 : Fin (m+6))) (.bound
  eN.succ.succ.succ.succ.succ.succ))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin
  (m+6)) w.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ)) (.conj
  (ConstructionProbeMappedPathSyntax.nodeMap (3 : Fin (m+6)) f.succ.succ.succ.succ.succ.succ (0 : Fin
  (m+6))) (ConstructionProbePath.path w.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ
  mulN.succ.succ.succ.succ.succ.succ eN.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ (2
  : Fin (m+6)) (0 : Fin (m+6)))))))))))))))))))) (.existsE (.existsE (.existsE (.conj (mergerCode
  one.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)) q.succ.succ.succ) (.conj (mergerCode one.succ.succ.succ
  (2 : Fin (m+3)) (0 : Fin (m+3)) qN.succ.succ.succ) (.conj (.mem (.bound (2 : Fin (m+3))) (.bound
  w.succ.succ.succ)) (.conj (.existsE (.mem (.bound (0 : Fin (m+4))) (.bound (2 : Fin (m+3)).succ))) (.conj
  (ConstructionMergerRelations.prescription (2 : Fin (m+3)) D.succ.succ.succ (1 : Fin (m+3))) (.conj
  (ConstructionMergerRelations.valid (2 : Fin (m+3)) D.succ.succ.succ mul.succ.succ.succ (1 : Fin (m+3)))
  (.conj (ConstructionMergerPrescriptionMapSyntax.graph (1 : Fin (m+3)) f.succ.succ.succ (0 : Fin (m+3)))
  (.conj (ConstructionMergerRelations.prescription (2 : Fin (m+3)) N.succ.succ.succ (0 : Fin (m+3)))
  (ConstructionMergerRelations.valid (2 : Fin (m+3)) N.succ.succ.succ mulN.succ.succ.succ (0 : Fin
  (m+3)))))))))))))))

theorem transport_freeClosed {m : Nat} (w D mul e zero one N mulN eN f q qN : Fin m) :
    (transport w D mul e zero one N mulN eN f q qN).FreeClosed := by
  simp -implicitDefEqProofs [transport,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,probeCode_freeClosed,mergerCode_freeClosed,Project.Formula.extensionalEq,ConstructionProbePath.path_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed,ConstructionMergerPrescriptionMapSyntax.graph_freeClosed]

theorem transport_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero one N mulN eN f q qN : Fin m) :
    Project.Formula.satisfies env (transport w D mul e zero one N mulN eN f q qN) ↔ Transport (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound one) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound f) (env.bound q) (env.bound qN) := by
  simp only [transport,Transport,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,probeCode_semantics hM,mergerCode_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbePath.path_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionMergerRelations.prescription_semantics hM,ConstructionMergerRelations.valid_semantics hM,ConstructionMergerPrescriptionMapSyntax.graph_semantics hM]
  rfl


def baseMaps {m : Nat} (J Domains Muls Units Origins D mul e : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (4 : Fin (m+5))) (.bound
  J.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ (4 : Fin (m+5)) (3 : Fin (m+5)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ (4 : Fin (m+5)) (2 : Fin (m+5)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Units.succ.succ.succ.succ.succ (4 : Fin (m+5)) (1 : Fin
  (m+5)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Origins.succ.succ.succ.succ.succ (4 : Fin
  (m+5)) (0 : Fin (m+5)))) (.conj (ConstructionProbeConservativeSyntax.conservative
  D.succ.succ.succ.succ.succ (3 : Fin (m+5)) mul.succ.succ.succ.succ.succ (2 : Fin (m+5)) (0 : Fin (m+5)))
  (.conj (ConstructionProbeLiftHomSyntax.preservesProducts mul.succ.succ.succ.succ.succ (2 : Fin (m+5)) (0 :
  Fin (m+5))) (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+5)) e.succ.succ.succ.succ.succ
  (1 : Fin (m+5))))))))))))))))

theorem baseMaps_freeClosed {m : Nat} (J Domains Muls Units Origins D mul e : Fin m) :
    (baseMaps J Domains Muls Units Origins D mul e).FreeClosed := by
  simp -implicitDefEqProofs [baseMaps,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed]

theorem baseMaps_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Muls Units Origins D mul e : Fin m) :
    Project.Formula.satisfies env (baseMaps J Domains Muls Units Origins D mul e) ↔ BaseMaps (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Units) (env.bound Origins) (env.bound D) (env.bound mul) (env.bound e) := by
  simp only [baseMaps,BaseMaps,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM]
  rfl


def requests {m : Nat} (Schedule w D mul e zero one : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Schedule.succ.succ (1 : Fin
  (m+2)) (0 : Fin (m+2)))) (request w.succ.succ D.succ.succ mul.succ.succ e.succ.succ zero.succ.succ
  one.succ.succ (0 : Fin (m+2))))))

theorem requests_freeClosed {m : Nat} (Schedule w D mul e zero one : Fin m) :
    (requests Schedule w D mul e zero one).FreeClosed := by
  simp -implicitDefEqProofs [requests,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,request_freeClosed]

theorem requests_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Schedule w D mul e zero one : Fin m) :
    Project.Formula.satisfies env (requests Schedule w D mul e zero one) ↔ Requests (env.bound Schedule) (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound one) := by
  simp only [requests,Requests,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,request_semantics hM]
  rfl


def value {m : Nat} (w D mul e zero one Domains Muls Units Origins Schedule i qN : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ (4 : Fin (m+5)))) (.conj (ProjectSyntax.encode
  id (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ (3 : Fin (m+5))))
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Units.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ (2 : Fin (m+5)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  Origins.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ (1 : Fin (m+5)))) (.conj (ProjectSyntax.encode
  id (Source.SetLanguage.edge Schedule.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ (0 : Fin (m+5))))
  (transport w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ (4 : Fin (m+5)) (3 :
  Fin (m+5)) (2 : Fin (m+5)) (1 : Fin (m+5)) (0 : Fin (m+5)) qN.succ.succ.succ.succ.succ)))))))))))

theorem value_freeClosed {m : Nat} (w D mul e zero one Domains Muls Units Origins Schedule i qN : Fin m) :
    (value w D mul e zero one Domains Muls Units Origins Schedule i qN).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,transport_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero one Domains Muls Units Origins Schedule i qN : Fin m) :
    Project.Formula.satisfies env (value w D mul e zero one Domains Muls Units Origins Schedule i qN) ↔ Value (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound one) (env.bound Domains) (env.bound Muls) (env.bound Units) (env.bound Origins) (env.bound Schedule) (env.bound i) (env.bound qN) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,transport_semantics hM]
  rfl


def graph {m : Nat} (w D mul e zero one J Domains Muls Units Origins Schedule Out : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge Out.succ.succ (1 : Fin (m+2)) (0
  : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound J.succ.succ)) (value w.succ.succ D.succ.succ
  mul.succ.succ e.succ.succ zero.succ.succ one.succ.succ Domains.succ.succ Muls.succ.succ Units.succ.succ
  Origins.succ.succ Schedule.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))))))

theorem graph_freeClosed {m : Nat} (w D mul e zero one J Domains Muls Units Origins Schedule Out : Fin m) :
    (graph w D mul e zero one J Domains Muls Units Origins Schedule Out).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero one J Domains Muls Units Origins Schedule Out : Fin m) :
    Project.Formula.satisfies env (graph w D mul e zero one J Domains Muls Units Origins Schedule Out) ↔ Graph (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound one) (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Units) (env.bound Origins) (env.bound Schedule) (env.bound Out) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM]
  rfl


/-- Construct one exact mapped request at every given stage; stage domains
and base maps may vary arbitrarily. Collection is used only with proven uniqueness. -/
theorem exists_schedule (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero one J Domains Muls Units Origins Schedule : M.Carrier .set}
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hFam : ConstructionDirectedMonoidData.Family J Domains Muls Units)
    (hOrigins : FunctionOn J Origins) (hSchedule : FunctionOn J Schedule)
    (hReq : Requests Schedule w D mul e zero one)
    (hBase : BaseMaps J Domains Muls Units Origins D mul e) :
    ∃ Out, FunctionOn J Out ∧ Graph w D mul e zero one J Domains Muls Units Origins Schedule Out ∧
      (∀ i N mulN eN qN, (Project.FirstOrderSemantics.reduct M).mem i J →
        PureKuratowski.PairMember M i N Domains → PureKuratowski.PairMember M i mulN Muls →
        PureKuratowski.PairMember M i eN Units → PureKuratowski.PairMember M i qN Out →
        Request w N mulN eN zero one qN) ∧
      ∀ other, FunctionOn J other → Graph w D mul e zero one J Domains Muls Units Origins Schedule other → other = Out := by
  let schema : Project.BinarySchema 11 := {
    body := value 2 3 4 5 6 7 8 9 10 11 12 1 0
    freeClosed := value_freeClosed _ _ _ _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 11 := {
    bound := fun i => match i with
      | 0 => w | 1 => D | 2 => mul | 3 => e | 4 => zero | 5 => one
      | 6 => Domains | 7 => Muls | 8 => Units | 9 => Origins | _ => Schedule
    free := fun _ => w }
  have he (i qN) : schema.denote env i qN ↔ Value w D mul e zero one Domains Muls Units Origins Schedule i qN :=
    value_semantics hM ((env.push i).push qN) 2 3 4 5 6 7 8 9 10 11 12 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∃ qN, schema.denote env i qN := by
    intro i hi
    obtain ⟨N,mulN,eN,hN,hMul,hUnit,hmN⟩ := ConstructionDirectedMonoidData.family_at hFam hi
    obtain ⟨f,hf,_⟩ := hOrigins.2 i hi
    obtain ⟨q,hq,_⟩ := hSchedule.2 i hi
    obtain ⟨hCons,hPres,hOne⟩ := hBase i N mulN eN f hi hN hMul hUnit hf
    obtain ⟨qN,hTrans⟩ := transport_exists hM
      (ConstructionRequestMaps.maps_requests hM hm hmN hCons hPres hOne hJoins) (hReq i q hq)
    exact ⟨qN,(he i qN).mpr ⟨N,mulN,eN,f,q,hN,hMul,hUnit,hf,hq,hTrans⟩⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∀ r s,
      schema.denote env i r → schema.denote env i s → r = s := by
    intro i hi r s hr hs
    obtain ⟨N,mulN,eN,f,q,hN,hMul,hUnit,hf,hq,hTrans⟩ := (he i r).mp hr
    obtain ⟨N',mulN',eN',f',q',hN',hMul',hUnit',hf',hq',hTrans'⟩ := (he i s).mp hs
    have en := function_unique hFam.1 hN hN'
    have em := function_unique hFam.2.1 hMul hMul'
    have eu := function_unique hFam.2.2.1 hUnit hUnit'
    have ef := function_unique hOrigins hf hf'
    have eq := function_unique hSchedule hq hq'
    subst N'; subst mulN'; subst eN'; subst f'; subst q'
    exact transport_unique hM (zero_ne_one hz hone) (hBase i N mulN eN f hi hN hMul hUnit hf).1.1.1 hTrans hTrans'
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema env J ht hu
  obtain ⟨Out,hOut,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    schema env ht hu (fun i qN hi hq => (hA qN).mpr ⟨i,hi,hq⟩)
  have hOutMaps := (ForcingSupportSize.native_mapsTo hM J A Out).mpr hOut
  have hG : Graph w D mul e zero one J Domains Muls Units Origins Schedule Out :=
    fun i qN => (hGraph i qN).trans (and_congr_right fun _ => he i qN)
  refine ⟨Out,hOutMaps.1,hG,?_,?_⟩
  · intro i N mulN eN qN _ hN hMul hUnit hqN
    obtain ⟨_,N',mulN',eN',f,q,hN',hMul',hUnit',_,_,hTrans⟩ := (hG i qN).mp hqN
    have en := function_unique hFam.1 hN' hN
    have em := function_unique hFam.2.1 hMul' hMul
    have eu := function_unique hFam.2.2.1 hUnit' hUnit
    subst N'; subst mulN'; subst eN'
    exact transport_target hTrans
  · intro other hFn hOther
    have hOtherMaps : MapsTo J A other := ⟨hFn,fun i qN hq => (hA qN).mpr
      ⟨i,((hOther i qN).mp hq).1,(he i qN).mpr ((hOther i qN).mp hq).2⟩⟩
    exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
      ((ForcingSupportSize.native_mapsTo hM J A other).mp hOtherMaps).1.1 hOut.1.1
      (fun i qN => (hOther i qN).trans (hG i qN).symm)

end PPAC.Migration.ConstructionRequestSchedule
