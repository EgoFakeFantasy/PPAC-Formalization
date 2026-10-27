/- Pinned CompleteRounds.ProbeData.code/MergerData.code/Request data and
MonoidRounds.Request.defaultProbe: full MODEL-INTERNAL request set.
Native function space bounds all omega paths; native powerset bounds all
canonical finite partial start graphs. No external Nat/List enumeration. -/
import PPAC.Migration.ConstructionRequestScheduleSyntax
import PPAC.Migration.ForcingWithTopCarrier
import YesMetaZFC.SetTheory.FunctionSpaceConstruction

namespace PPAC.Migration.ConstructionRequestCarrier
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRequestSchedule (ProbeCode MergerCode Transport)
open ConstructionMergerRelations (Prescription Valid)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The partial graph of the source Option-valued start table has ONLY
pairs of index-pairs and old-element-pairs; absent starts have no row. -/
def WellFormed (n D P : M.Carrier .set) : Prop := ∀ row,
  (Project.FirstOrderSemantics.reduct M).mem row P →
    ∃ i j a b ij ab, PureKuratowski.Code M row ij ab ∧ PureKuratowski.Code M ij i j ∧
      PureKuratowski.Code M ab a b ∧ (Project.FirstOrderSemantics.reduct M).mem i n ∧
      (Project.FirstOrderSemantics.reduct M).mem j n ∧ (Project.FirstOrderSemantics.reduct M).mem a D ∧
      (Project.FirstOrderSemantics.reduct M).mem b D

def Element (w D mul e zero one q : M.Carrier .set) : Prop :=
  (∃ a b node, ProbeCode zero a b node q ∧ (Project.FirstOrderSemantics.reduct M).mem b D ∧
    b ≠ e ∧ ConstructionProbePath.Path w D mul e zero a node) ∨
  (∃ n P, MergerCode one n P q ∧ (Project.FirstOrderSemantics.reduct M).mem n w ∧
    (∃ i, (Project.FirstOrderSemantics.reduct M).mem i n) ∧ WellFormed n D P ∧ Prescription n D P ∧ Valid n D mul P)

def Carrier (w D mul e zero one Requests : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q Requests ↔ Element w D mul e zero one q

def ConstantNode (w e node : M.Carrier .set) : Prop := ∀ i x,
  PureKuratowski.PairMember M i x node ↔ (Project.FirstOrderSemantics.reduct M).mem i w ∧ x = e

theorem element_request {w D mul e zero one q : M.Carrier .set}
    (h : Element w D mul e zero one q) : ConstructionRequestSchedule.Request w D mul e zero one q := by
  rcases h with ⟨a,b,node,hCode,hb,hne,hPath⟩ | ⟨n,P,hCode,hn,hnp,_,hP,hValid⟩
  · exact Or.inl ⟨a,b,node,hCode,hb,hne,hPath⟩
  · exact Or.inr ⟨n,P,hCode,hn,hnp,hP,hValid⟩

theorem wellFormed_of_graph {n N P f PN : M.Carrier .set}
    (hGraph : ConstructionMergerPrescriptionMap.Graph P f PN) (hPN : Prescription n N PN) :
    WellFormed n N PN := by
  intro row hrow
  obtain ⟨i,j,a,b,fa,fb,ij,ab,hij,hab,hcode,hS,hfa,hfb⟩ := (hGraph row).mp hrow
  have hStart : ConstructionMergerRelations.Start PN i j fa fb := ⟨ab,hab,ij,hij,row,hcode,hrow⟩
  obtain ⟨hi,hj,ha,hb⟩ := hPN.1 i j fa fb hStart
  exact ⟨i,j,fa,fb,ij,ab,hcode,hij,hab,hi,hj,ha,hb⟩

theorem transport_element {w D mul e zero one N mulN eN f q qN : M.Carrier .set}
    (h : Transport w D mul e zero one N mulN eN f q qN) : Element w N mulN eN zero one qN := by
  rcases h with ⟨_,_,_,fa,fb,mapped,_,hCode,_,_,_,_,_,hb,hne,_,_,hPath⟩ |
    ⟨n,P,PN,_,hCode,hn,hnp,_,_,hGraph,hPN,hValid⟩
  · exact Or.inl ⟨fa,fb,mapped,hCode,hb,hne,hPath⟩
  · exact Or.inr ⟨n,PN,hCode,hn,hnp,wellFormed_of_graph hGraph hPN,hPN,hValid⟩

theorem carrier_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero one A B : M.Carrier .set} (hA : Carrier w D mul e zero one A)
    (hB : Carrier w D mul e zero one B) : A = B :=
  (ModelTransfer.extensionality hM).eq_of_same_members A B (fun q => (hA q).trans (hB q).symm)

theorem constant_node (hM : FirstOrder.Theory.Models M nativeZF) {w D mul e zero : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) :
    ∃ node, MapsTo w D node ∧ ConstantNode w e node ∧ ConstructionProbePath.Path w D mul e zero e node := by
  let schema : Project.BinarySchema 1 := {
    body := Project.Formula.extensionalEq (.bound 0) (.bound 2)
    freeClosed := by simp [Project.Formula.extensionalEq,Definitional.Formula.FreeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => e, free := fun _ => e }
  have he (i x) : schema.denote env i x ↔ x = e := by
    simp only [Project.BinarySchema.denote,schema,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
    rfl
  obtain ⟨node,hNode,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := w) (target := D)
    (fun i _ => ⟨e,(he i e).mpr rfl⟩)
    (fun i _ x y hx hy => ((he i x).mp hx).trans ((he i y).mp hy).symm)
    (fun i x _ hx => ((he i x).mp hx).symm ▸ hm.1.1)
  have hMaps := (ForcingSupportSize.native_mapsTo hM w D node).mpr hNode
  have hConst : ConstantNode w e node := fun i x => (hGraph i x).trans (and_congr_right fun _ => he i x)
  have hp : ForcingDiagramOrder.Product mul e e e := (hm.1.2 e hm.1.1 e).2.mpr rfl
  refine ⟨node,hMaps,hConst,hMaps,hm.1.1,(hConst zero e).mpr ⟨hzw,rfl⟩,?_,?_⟩
  · intro i j hi hj _
    exact ⟨e,e,e,(hConst i e).mpr ⟨hi,rfl⟩,(hConst j e).mpr ⟨hj,rfl⟩,hm.1.1,hp⟩
  · intro i hi
    exact ⟨e,e,(hConst i e).mpr ⟨hi,rfl⟩,hm.1.1,hp⟩


def wellFormed {m : Nat} (n D P : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound (0 : Fin (m+1))) (.bound P.succ)) (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound (0 : Fin
  (m+1)).succ.succ.succ.succ.succ.succ) (.bound (1 : Fin (m+7))) (.bound (0 : Fin (m+7)))) (.conj
  (PureKuratowskiProject.code (.bound (1 : Fin (m+7))) (.bound (5 : Fin (m+7))) (.bound (4 : Fin (m+7))))
  (.conj (PureKuratowskiProject.code (.bound (0 : Fin (m+7))) (.bound (3 : Fin (m+7))) (.bound (2 : Fin
  (m+7)))) (.conj (.mem (.bound (5 : Fin (m+7))) (.bound n.succ.succ.succ.succ.succ.succ.succ)) (.conj (.mem
  (.bound (4 : Fin (m+7))) (.bound n.succ.succ.succ.succ.succ.succ.succ)) (.conj (.mem (.bound (3 : Fin
  (m+7))) (.bound D.succ.succ.succ.succ.succ.succ.succ)) (.mem (.bound (2 : Fin (m+7))) (.bound
  D.succ.succ.succ.succ.succ.succ.succ))))))))))))))))

theorem wellFormed_freeClosed {m : Nat} (n D P : Fin m) :
    (wellFormed n D P).FreeClosed := by
  simp -implicitDefEqProofs [wellFormed,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem wellFormed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D P : Fin m) :
    Project.Formula.satisfies env (wellFormed n D P) ↔ WellFormed (env.bound n) (env.bound D) (env.bound P) := by
  simp only [wellFormed,WellFormed,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    KuratowskiZF.code_correct hM]
  rfl


def element {m : Nat} (w D mul e zero one q : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.existsE (.existsE (.conj (ConstructionRequestSchedule.probeCode zero.succ.succ.succ (2 :
  Fin (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3)) q.succ.succ.succ) (.conj (.mem (.bound (1 : Fin (m+3))) (.bound
  D.succ.succ.succ)) (.conj (.neg (Project.Formula.extensionalEq (.bound (1 : Fin (m+3))) (.bound
  e.succ.succ.succ))) (ConstructionProbePath.path w.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ
  e.succ.succ.succ zero.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))))))))) (.existsE (.existsE (.conj
  (ConstructionRequestSchedule.mergerCode one.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)) q.succ.succ) (.conj
  (.mem (.bound (1 : Fin (m+2))) (.bound w.succ.succ)) (.conj (.existsE (.mem (.bound (0 : Fin (m+3)))
  (.bound (1 : Fin (m+2)).succ))) (.conj (wellFormed (1 : Fin (m+2)) D.succ.succ (0 : Fin (m+2))) (.conj
  (ConstructionMergerRelations.prescription (1 : Fin (m+2)) D.succ.succ (0 : Fin (m+2)))
  (ConstructionMergerRelations.valid (1 : Fin (m+2)) D.succ.succ mul.succ.succ (0 : Fin (m+2)))))))))))

theorem element_freeClosed {m : Nat} (w D mul e zero one q : Fin m) :
    (element w D mul e zero one q).FreeClosed := by
  simp -implicitDefEqProofs [element,Definitional.Formula.FreeClosed,ConstructionRequestSchedule.probeCode_freeClosed,ConstructionRequestSchedule.mergerCode_freeClosed,Project.Formula.extensionalEq,ConstructionProbePath.path_freeClosed,wellFormed_freeClosed,ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed]

theorem element_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero one q : Fin m) :
    Project.Formula.satisfies env (element w D mul e zero one q) ↔ Element (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound one) (env.bound q) := by
  simp only [Project.Formula.satisfies_disj_iff,element,Element,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionRequestSchedule.probeCode_semantics hM,ConstructionRequestSchedule.mergerCode_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionProbePath.path_semantics hM,wellFormed_semantics hM,ConstructionMergerRelations.prescription_semantics hM,ConstructionMergerRelations.valid_semantics hM]
  rfl


def carrier {m : Nat} (w D mul e zero one Requests : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound (0 : Fin (m+1))) (.bound Requests.succ)) (element w.succ D.succ mul.succ
  e.succ zero.succ one.succ (0 : Fin (m+1)))))

theorem carrier_freeClosed {m : Nat} (w D mul e zero one Requests : Fin m) :
    (carrier w D mul e zero one Requests).FreeClosed := by
  simp -implicitDefEqProofs [carrier,Definitional.Formula.FreeClosed,element_freeClosed]

theorem carrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero one Requests : Fin m) :
    Project.Formula.satisfies env (carrier w D mul e zero one Requests) ↔ Carrier (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound one) (env.bound Requests) := by
  simp only [carrier,Carrier,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    element_semantics hM]
  rfl


def constantNode {m : Nat} (w e node : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ.succ (1 : Fin (m+2))
  (0 : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound w.succ.succ))
  (Project.Formula.extensionalEq (.bound (0 : Fin (m+2))) (.bound e.succ.succ))))))

theorem constantNode_freeClosed {m : Nat} (w e node : Fin m) :
    (constantNode w e node).FreeClosed := by
  simp -implicitDefEqProofs [constantNode,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem constantNode_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w e node : Fin m) :
    Project.Formula.satisfies env (constantNode w e node) ↔ ConstantNode (env.bound w) (env.bound e) (env.bound node) := by
  simp only [constantNode,ConstantNode,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (D mul e zero one : M.Carrier .set) :
    ∃ Requests, Carrier w D mul e zero one Requests := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨Functions,hFunctions⟩ := ZF.exists_functionSpace hZF I w D
  obtain ⟨A,hA⟩ := ZF.exists_cartesianProduct hZF I D Functions
  obtain ⟨B,hB⟩ := ZF.exists_cartesianProduct hZF I D A
  obtain ⟨Z0,hZ0⟩ := KP.exists_singleton (ZF.modelsKP hZF) zero
  obtain ⟨Probes,hProbes⟩ := ZF.exists_cartesianProduct hZF I Z0 B
  obtain ⟨WW,hWW⟩ := ZF.exists_cartesianProduct hZF I w w
  obtain ⟨DD,hDD⟩ := ZF.exists_cartesianProduct hZF I D D
  obtain ⟨Box,hBox⟩ := ZF.exists_cartesianProduct hZF I WW DD
  obtain ⟨Power,hPower⟩ := ZF.exists_powerSet hZF Box
  obtain ⟨C,hC⟩ := ZF.exists_cartesianProduct hZF I w Power
  obtain ⟨Z1,hZ1⟩ := KP.exists_singleton (ZF.modelsKP hZF) one
  obtain ⟨Mergers,hMergers⟩ := ZF.exists_cartesianProduct hZF I Z1 C
  obtain ⟨Raw,hRaw⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) Probes Mergers
  have hBound : ∀ q, Element w D mul e zero one q → (Project.FirstOrderSemantics.reduct M).mem q Raw := by
    intro q hq
    rcases hq with ⟨a,b,node,hCode,hb,_,hPath⟩ | ⟨n,P,hCode,hn,_,hWell,_,_⟩
    · obtain ⟨t,s,hq,ht,hs⟩ := hCode
      have hnF := (hFunctions node).mpr ((ForcingSupportSize.native_mapsTo hM w D node).mp hPath.1)
      have hsA := (hA s).mpr ⟨b,hb,node,hnF,hs⟩
      have htB := (hB t).mpr ⟨a,hPath.2.1,s,hsA,ht⟩
      exact (hRaw q).mpr (Or.inl ((hProbes q).mpr ⟨zero,(hZ0 zero).mpr rfl,t,htB,hq⟩))
    · obtain ⟨t,hq,ht⟩ := hCode
      have hPPower : (Project.FirstOrderSemantics.reduct M).mem P Power := (hPower P).mpr (by
        intro row hr
        obtain ⟨i,j,a,b,ij,ab,hrow,hij,hab,hi,hj,ha,hb⟩ := hWell row hr
        have hiw := (hw.isOrdinal hZF).transitive n hn i hi
        have hjw := (hw.isOrdinal hZF).transitive n hn j hj
        exact (hBox row).mpr ⟨ij,(hWW ij).mpr ⟨i,hiw,j,hjw,hij⟩,ab,(hDD ab).mpr ⟨a,ha,b,hb,hab⟩,hrow⟩)
      have htC := (hC t).mpr ⟨n,hn,P,hPPower,ht⟩
      exact (hRaw q).mpr (Or.inr ((hMergers q).mpr ⟨one,(hZ1 one).mpr rfl,t,htC,hq⟩))
  let schema : Project.UnarySchema 6 := {
    body := element 1 2 3 4 5 6 0
    freeClosed := element_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := fun i => match i with | 0 => w | 1 => D | 2 => mul | 3 => e | 4 => zero | _ => one
    free := fun _ => w }
  have he (q) : schema.denote env q ↔ Element w D mul e zero one q :=
    element_semantics hM (env.push q) 1 2 3 4 5 6 0
  obtain ⟨Requests,hRequests⟩ := ZF.separation_exists_d hZF schema env Raw
  exact ⟨Requests,fun q => ⟨fun hq => (he q).mp ((hRequests q).mp hq).2,
    fun hq => (hRequests q).mpr ⟨hBound q hq,(he q).mpr hq⟩⟩⟩

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e mark zero one : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D) (hne : mark ≠ e) :
    ∃ Requests node q0, Carrier w D mul e zero one Requests ∧ MapsTo w D node ∧ ConstantNode w e node ∧
      ConstructionProbePath.Path w D mul e zero e node ∧ ProbeCode zero e mark node q0 ∧
      (Project.FirstOrderSemantics.reduct M).mem q0 Requests ∧ zero ≠ one ∧
      (∀ q, (Project.FirstOrderSemantics.reduct M).mem q Requests → ConstructionRequestSchedule.Request w D mul e zero one q) ∧
      (∀ N mulN eN f q qN, (Project.FirstOrderSemantics.reduct M).mem q Requests →
        Transport w D mul e zero one N mulN eN f q qN → Element w N mulN eN zero one qN) ∧
      ∀ other, Carrier w D mul e zero one other → other = Requests := by
  obtain ⟨Requests,hR⟩ := exists_carrier hM hw D mul e zero one
  obtain ⟨node,hNode,hConst,hPath⟩ := constant_node hM hm hzw
  obtain ⟨s,hs⟩ := KuratowskiZF.exists_code hM mark node
  obtain ⟨t,ht⟩ := KuratowskiZF.exists_code hM e s
  obtain ⟨q0,hq0⟩ := KuratowskiZF.exists_code hM zero t
  have hCode : ProbeCode zero e mark node q0 := ⟨t,s,hq0,ht,hs⟩
  exact ⟨Requests,node,q0,hR,hNode,hConst,hPath,hCode,
    (hR q0).mpr (Or.inl ⟨e,mark,node,hCode,hmark,hne,hPath⟩),ConstructionRequestSchedule.zero_ne_one hz hone,
    fun q hq => element_request ((hR q).mp hq),
    fun _ _ _ _ _ _ _ ht => transport_element ht,fun _ hOther => carrier_unique hM hOther hR⟩

end PPAC.Migration.ConstructionRequestCarrier
