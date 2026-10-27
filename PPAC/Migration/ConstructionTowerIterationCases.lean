/- Pinned ConstructionIteration.structureWithTime / Round.step:
the THREE actual deterministic cases on the SAME full record history.
Fixed Context is only the already accepted source geometric/base/Schedule
contract. Internal L/order is supplied by the existing producer. -/
import PPAC.Migration.ConstructionTowerHistoryClosure

namespace PPAC.Migration.ConstructionTowerIterationCases
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerValidity (Valid)
open ConstructionTowerHistoryClosure (Continues)
open ForcingConditionGraphs (FunctionOn function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one u lengthBound Schedule J S output : M.Carrier .set}

def Context (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one u lengthBound Schedule : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsOmega w ∧
  ConstructionFractionOrder.Carrier w Q ∧ ConstructionRealCuts.CutCarrier hM w Q R ∧
  ConstructionFractionOrder.Coordinates w u one one ∧
  (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one ∧
  ConstructionRealCuts.Principal hM w Q u top ∧
  ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C ∧
  (∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero) ∧
  (Project.FirstOrderSemantics.reduct M).mem zero w ∧
  (Project.FirstOrderSemantics.reduct M).IsOrdinal lengthBound ∧
  FunctionOn lengthBound Schedule ∧ ConstructionRequestSchedule.Requests Schedule w D mul e zero one

def Case (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one Schedule J S output : M.Carrier .set) : Prop :=
  (J = zero ∧ ConstructionTowerInitial.Value hM w Q R top D mul e mark H C zero one output) ∨
  (J ≠ zero ∧ ∃ prev request, (Project.FirstOrderSemantics.reduct M).SuccessorOf J prev ∧
    PureKuratowski.PairMember M prev request Schedule ∧
    ConstructionTowerHistorySuccessor.Value hM w Q R top D mul e mark H C zero one request prev J S output) ∨
  (J ≠ zero ∧ ¬ (∃ prev, (Project.FirstOrderSemantics.reduct M).SuccessorOf J prev) ∧
    ConstructionTowerHistoryLimit.Value hM w Q R top D mul e mark H C J S zero output)

theorem context_top (hM : FirstOrder.Theory.Models M nativeZF)
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule) :
    ConstructionRealCuts.Cut hM w Q top := by
  obtain ⟨hw,hQ,_,hu,_,htop,_,_,_,_,_,_⟩ := hCtx
  exact ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) htop

theorem nonzero_nonempty (hM : FirstOrder.Theory.Models M nativeZF)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero) (hne : J ≠ zero) :
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x J := by
  classical
  apply Classical.byContradiction
  intro hn
  exact hne ((ModelTransfer.extensionality hM).eq_of_same_members J zero
    (fun x => ⟨fun h => False.elim (hn ⟨x,h⟩),fun h => False.elim (hz x h)⟩))

theorem predecessor_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    {a b : M.Carrier .set}
    (ha : (Project.FirstOrderSemantics.reduct M).SuccessorOf J a)
    (hb : (Project.FirstOrderSemantics.reduct M).SuccessorOf J b) : a = b := by
  have haJ := ha.predecessor_mem
  have hbJ := hb.predecessor_mem
  rcases (ha b).mp hbJ with hba | he
  · rcases (hb a).mp haJ with hab | he
    · exact False.elim (hJ.wellOrder.linear.irrefl a haJ
        (hJ.wellOrder.linear.trans a haJ b hbJ a haJ hab hba))
    · exact (ModelTransfer.extensionality hM).eq_of_same_members a b he
  · exact ((ModelTransfer.extensionality hM).eq_of_same_members b a he).symm

/-- The real first history is an append of ANY empty input graph. -/
theorem initial_continues (hM : FirstOrder.Theory.Models M nativeZF)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hS : FunctionOn zero S)
    (hValue : ConstructionTowerInitial.Value hM w Q R top D mul e mark H C zero one output) :
    Continues hM w Q R top D mul e mark H C zero S output := by
  obtain ⟨S1,hConst,hValid⟩ := ConstructionTowerHistoryInitial.history_of_value hM hz hone hValue
  obtain ⟨z,hz',hSucc⟩ := hone
  have ez := (ModelTransfer.extensionality hM).eq_of_same_members z zero
    (fun x => ⟨fun h => False.elim (hz' x h),fun h => False.elim (hz x h)⟩)
  subst z
  have mem_one (i) : (Project.FirstOrderSemantics.reduct M).mem i one ↔ i = zero := by
    constructor
    · intro hi
      rcases (hSucc i).mp hi with h | he
      · exact False.elim (hz i h)
      · exact (ModelTransfer.extensionality hM).eq_of_same_members i zero he
    · rintro rfl
      exact hSucc.predecessor_mem
  refine ⟨one,S1,⟨hSucc,hValid.1.1,?_⟩,hValid⟩
  intro i code
  constructor
  · intro hc
    obtain ⟨hi,he⟩ := (hConst i code).mp hc
    exact Or.inr ⟨(mem_one i).mp hi,he⟩
  · rintro (hc | ⟨hi,he⟩)
    · exact False.elim (hz i (ForcingConditionGraphs.function_input hS hc))
    · exact (hConst i code).mpr ⟨(mem_one i).mpr hi,he⟩

theorem case_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hBound : (Project.FirstOrderSemantics.reduct M).mem J lengthBound)
    (hV : Valid hM w Q R top D mul e mark H C J S) :
    ∃ output, Case hM w Q R top D mul e mark H C zero one Schedule J S output := by
  classical
  have hTop := context_top hM hCtx
  obtain ⟨hw,hQ,hR,hu,hone,htop,hObj,hz,hzw,hLength,hFn,hReq⟩ := hCtx
  by_cases he : J = zero
  · subst J
    obtain ⟨out,hValue,_⟩ := ConstructionTowerInitial.exists_value hM hR hTop hObj hz hone
    exact ⟨out,Or.inl ⟨rfl,hValue⟩⟩
  · by_cases hs : ∃ prev, (Project.FirstOrderSemantics.reduct M).SuccessorOf J prev
    · obtain ⟨prev,hSucc⟩ := hs
      have hpBound := hLength.transitive J hBound prev hSucc.predecessor_mem
      obtain ⟨request,hq,_⟩ := hFn.2 prev hpBound
      obtain ⟨out,hValue⟩ := ConstructionTowerHistorySuccessor.exists_value hM hOrder
        hV hJ hSucc hw hz hzw hQ hR hu hone htop hObj (hReq prev request hq)
      exact ⟨out,Or.inr (Or.inl ⟨he,prev,request,hSucc,hq,hValue⟩)⟩
    · obtain ⟨out,hValue⟩ := ConstructionTowerHistoryLimit.exists_value hM hV hJ
        (nonzero_nonempty hM hz he) hw hQ hR hTop zero
      exact ⟨out,Or.inr (Or.inr ⟨he,hs,hValue⟩)⟩

theorem case_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    {x y : M.Carrier .set}
    (hx : Case hM w Q R top D mul e mark H C zero one Schedule J S x)
    (hy : Case hM w Q R top D mul e mark H C zero one Schedule J S y) : x = y := by
  obtain ⟨_,_,_,_,_,_,_,hz,_,_,hFn,_⟩ := hCtx
  rcases hx with ⟨he,hx⟩ | ⟨hne,p,q,hp,hq,hx⟩ | ⟨hne,hno,hx⟩
  · subst J
    rcases hy with ⟨_,hy⟩ | ⟨hn,_⟩ | ⟨hn,_⟩
    · exact ConstructionTowerInitial.value_unique hM hx hy
    · exact False.elim (hn rfl)
    · exact False.elim (hn rfl)
  · rcases hy with ⟨he,_⟩ | ⟨_,p',q',hp',hq',hy⟩ | ⟨_,hn,_⟩
    · exact False.elim (hne he)
    · have ep := predecessor_unique hM hJ hp' hp
      subst p'
      have eq := function_unique hFn hq' hq
      subst q'
      exact ConstructionTowerHistorySuccessor.value_unique hM hOrder hV hx hy
    · exact False.elim (hn ⟨p,hp⟩)
  · rcases hy with ⟨he,_⟩ | ⟨_,p,q,hp,_,_⟩ | ⟨_,_,hy⟩
    · exact False.elim (hne he)
    · exact False.elim (hno ⟨p,hp⟩)
    · exact ConstructionTowerHistoryLimit.value_unique hM hV hJ (nonzero_nonempty hM hz hne) hx hy

theorem case_continues (hM : FirstOrder.Theory.Models M nativeZF)
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hCase : Case hM w Q R top D mul e mark H C zero one Schedule J S output) :
    Continues hM w Q R top D mul e mark H C J S output := by
  have hTop := context_top hM hCtx
  obtain ⟨_,_,hR,_,hone,_,_,hz,_,_,_,_⟩ := hCtx
  rcases hCase with ⟨he,hValue⟩ | ⟨_,p,q,_,_,hValue⟩ | ⟨_,_,hValue⟩
  · subst J
    exact initial_continues hM hz hone hV.1.1 hValue
  · exact ConstructionTowerHistoryClosure.successor_preserves hM hJ hV hR hTop hValue
  · exact ConstructionTowerHistoryClosure.limit_preserves hM hJ hV hR hTop hValue


def context {m : Nat} (w Q R top D mul e mark H C zero one u lengthBound Schedule : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.isOmega (.bound w)) (.conj (ConstructionFractionOrder.carrier w Q) (.conj
  (ConstructionRealCuts.cutCarrier w Q R) (.conj (ConstructionFractionOrder.coordinates w u one one) (.conj
  (Project.Formula.isOrdinalOne (.bound one)) (.conj (ConstructionRealCuts.principal w Q u top) (.conj
  (ConstructionRoundStepSyntax.objectFields w Q R top D mul e mark H C) (.conj (Project.Formula.isEmpty
  (.bound zero)) (.conj (.mem (.bound zero) (.bound w)) (.conj (Project.Formula.isOrdinal (.bound
  lengthBound)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Schedule lengthBound))
  (ConstructionRequestSchedule.requests Schedule w D mul e zero one))))))))))))

theorem context_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one u lengthBound Schedule : Fin m) :
    (context w Q R top D mul e mark H C zero one u lengthBound Schedule).FreeClosed := by
  simp -implicitDefEqProofs [context,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,Project.Formula.isOrdinalOne,ConstructionRealCuts.principal_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,Project.Formula.isEmpty,Project.Formula.isOrdinal,ConstructionRequestSchedule.requests_freeClosed]

theorem context_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one u lengthBound Schedule : Fin m) :
    Project.Formula.satisfies env (context w Q R top D mul e mark H C zero one u lengthBound Schedule) ↔ Context hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound u) (env.bound lengthBound) (env.bound Schedule) := by
  simp only [context,Context,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,Project.Formula.satisfies_isOrdinalOne_iff,ConstructionRealCuts.principal_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isOrdinal_iff,ForcingConditionGraphs.functionOn_semantics (M := M),ConstructionRequestSchedule.requests_semantics hM]
  rfl


def caseValue {m : Nat} (w Q R top D mul e mark H C zero one Schedule J S output : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (Project.Formula.extensionalEq (.bound J) (.bound zero)) (ConstructionTowerInitial.value w Q R
  top D mul e mark H C zero one output)) (.disj (.conj (.neg (Project.Formula.extensionalEq (.bound J)
  (.bound zero))) (.existsE (.existsE (.conj (Project.Formula.isSuccessor (.bound J.succ.succ) (.bound (1 :
  Fin (m+2)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Schedule.succ.succ (1 : Fin (m+2))
  (0 : Fin (m+2)))) (ConstructionTowerHistorySuccessor.value w.succ.succ Q.succ.succ R.succ.succ
  top.succ.succ D.succ.succ mul.succ.succ e.succ.succ mark.succ.succ H.succ.succ C.succ.succ zero.succ.succ
  one.succ.succ (0 : Fin (m+2)) (1 : Fin (m+2)) J.succ.succ S.succ.succ output.succ.succ)))))) (.conj (.neg
  (Project.Formula.extensionalEq (.bound J) (.bound zero))) (.conj (.neg (.existsE
  (Project.Formula.isSuccessor (.bound J.succ) (.bound (0 : Fin (m+1))))))
  (ConstructionTowerHistoryLimit.value w Q R top D mul e mark H C J S zero output)))))

theorem caseValue_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one Schedule J S output : Fin m) :
    (caseValue w Q R top D mul e mark H C zero one Schedule J S output).FreeClosed := by
  simp -implicitDefEqProofs [caseValue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionTowerInitial.value_freeClosed,Project.Formula.isSuccessor,ConstructionTowerHistorySuccessor.value_freeClosed,ConstructionTowerHistoryLimit.value_freeClosed]

theorem caseValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one Schedule J S output : Fin m) :
    Project.Formula.satisfies env (caseValue w Q R top D mul e mark H C zero one Schedule J S output) ↔ Case hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound Schedule) (env.bound J) (env.bound S) (env.bound output) := by
  simp only [caseValue,Case,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionTowerInitial.value_semantics hM,Project.Formula.satisfies_isSuccessor_iff,ConstructionTowerHistorySuccessor.value_semantics hM,ConstructionTowerHistoryLimit.value_semantics hM]
  rfl


end PPAC.Migration.ConstructionTowerIterationCases
