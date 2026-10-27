/- Pinned ConstructionIteration / Round.underFunctor: BOTH ACTUAL
accepted case values extend the same history and preserve FULL Valid.
Consume existing Result/Extended weighted fan and self-identity equations.
No output validity or arbitrary replacement fan is assumed. -/
import PPAC.Migration.ConstructionTowerAppend

namespace PPAC.Migration.ConstructionTowerHistoryClosure
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerValidity (Valid)
open ConstructionTowerAppend (Append)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C J S zero one request prev output : M.Carrier .set}

def Continues (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C J S output : M.Carrier .set) : Prop :=
  ∃ next S', Append J S output next S' ∧ Valid hM w Q R top D mul e mark H C next S'

theorem limit_preserves (hM : FirstOrder.Theory.Models M nativeZF)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R) (hTop : ConstructionRealCuts.Cut hM w Q top)
    (hValue : ConstructionTowerHistoryLimit.Value hM w Q R top D mul e mark H C J S zero output) :
    Continues hM w Q R top D mul e mark H C J S output := by
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,hE,hF,
    W,G,unitW,markW,HL,LC,Out,base,next,identity,NewDomains,NewOut,hResult,hNext,hSelf,hPack⟩ := hValue
  obtain ⟨rep,projection,B,hRep,hp,hCar,hProj,hB,hG,hGraph,hUnit,hMark,hWeights,
    hObj,hKC,hFull,hProfiles,hBase,hNatural,hBaseProfiles,hColimit,hCard,hUnique⟩ := hResult
  obtain ⟨next',S',hAppend⟩ := ConstructionTowerAppend.exists_append hM hJ hV.1.1 output
  have eqNext := (ModelTransfer.extensionality hM).eq_of_same_members next' next
    (fun x => (hAppend.1 x).trans (hNext x).symm)
  subst next'
  exact ⟨next,S',hAppend,ConstructionTowerAppend.preserves hM hJ hV hR hTop
    hCharts hE hF hObj hBase hBaseProfiles hKC.1 hKC.2.1 hFull hProfiles hNatural hSelf hPack hAppend⟩

theorem successor_preserves (hM : FirstOrder.Theory.Models M nativeZF)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R) (hTop : ConstructionRealCuts.Cut hM w Q top)
    (hValue : ConstructionTowerHistorySuccessor.Value hM w Q R top D mul e mark H C
      zero one request prev J S output) :
    Continues hM w Q R top D mul e mark H C J S output := by
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    N,mulN,eN,markN,HN,CN,K,f,next,hCharts,hE,hF,hRow,hNext,
    raw,W,G,unitW,markW,HL,LC,O,base,roots,Out,identity,NewDomains,NewOut,
    hExt,hRaw,hGraph,hOut,hSelf,hPack⟩ := hValue
  obtain ⟨_,W0,G0,unit0,mark0,H0,C0,O0,base0,roots0,Out0,hRaw0,hStep,_,hGraph0,hOut0,
    _,hStable,hFull,hProfiles,hNatural,_,hUnique⟩ := hExt
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ :=
    ConstructionRoundSelection.pack_injective hRaw0 hRaw
  have eqOut := hUnique Out hOut.1 hGraph
  subst Out0
  have hprev : (Project.FirstOrderSemantics.reduct M).mem prev J := by
    obtain ⟨code,hc,_⟩ := hRow
    exact ForcingConditionGraphs.function_input hV.1.1 hc
  have hBaseProfiles := (hV.2.1 prev hprev N mulN eN markN HN CN K f hRow).2.2.1
  obtain ⟨next',S',hAppend⟩ := ConstructionTowerAppend.exists_append hM hJ hV.1.1 output
  have eqNext := (ModelTransfer.extensionality hM).eq_of_same_members next' next
    (fun x => (hAppend.1 x).trans (hNext x).symm)
  subst next'
  exact ⟨next,S',hAppend,ConstructionTowerAppend.preserves hM hJ hV hR hTop hCharts hE hF
    hStep.1.1 hStep.2.2.1 (hStep.2.2.2 hBaseProfiles)
    hOut hStable hFull hProfiles hNatural hSelf hPack hAppend⟩


def continues {m : Nat} (w Q R top D mul e mark H C J S output : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ConstructionTowerAppend.append J.succ.succ S.succ.succ output.succ.succ (1 : Fin
  (m+2)) (0 : Fin (m+2))) (ConstructionTowerValidity.valid w.succ.succ Q.succ.succ R.succ.succ top.succ.succ
  D.succ.succ mul.succ.succ e.succ.succ mark.succ.succ H.succ.succ C.succ.succ (1 : Fin (m+2)) (0 : Fin
  (m+2))))))

theorem continues_freeClosed {m : Nat} (w Q R top D mul e mark H C J S output : Fin m) :
    (continues w Q R top D mul e mark H C J S output).FreeClosed := by
  simp -implicitDefEqProofs [continues,Definitional.Formula.FreeClosed,ConstructionTowerAppend.append_freeClosed,ConstructionTowerValidity.valid_freeClosed]

theorem continues_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C J S output : Fin m) :
    Project.Formula.satisfies env (continues w Q R top D mul e mark H C J S output) ↔ Continues hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound J) (env.bound S) (env.bound output) := by
  simp only [continues,Continues,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionTowerAppend.append_semantics hM,ConstructionTowerValidity.valid_semantics hM]
  rfl


def limitSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 14 (.imp (Project.Formula.isOrdinal (.bound (10 : Fin 14))) (.imp
    (ConstructionTowerValidity.valid (0 : Fin 14) (1 : Fin 14) (2 : Fin 14) (3 : Fin 14) (4 : Fin 14) (5 :
    Fin 14) (6 : Fin 14) (7 : Fin 14) (8 : Fin 14) (9 : Fin 14) (10 : Fin 14) (11 : Fin 14)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 14) (1 : Fin 14) (2 : Fin 14)) (.imp (ConstructionRealCuts.cut
    (0 : Fin 14) (1 : Fin 14) (3 : Fin 14)) (.imp (ConstructionTowerHistoryLimit.value (0 : Fin 14) (1 : Fin
    14) (2 : Fin 14) (3 : Fin 14) (4 : Fin 14) (5 : Fin 14) (6 : Fin 14) (7 : Fin 14) (8 : Fin 14) (9 : Fin
    14) (10 : Fin 14) (11 : Fin 14) (12 : Fin 14) (13 : Fin 14)) (continues (0 : Fin 14) (1 : Fin 14) (2 :
    Fin 14) (3 : Fin 14) (4 : Fin 14) (5 : Fin 14) (6 : Fin 14) (7 : Fin 14) (8 : Fin 14) (9 : Fin 14) (10 :
    Fin 14) (11 : Fin 14) (13 : Fin 14))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,
      ConstructionTowerValidity.valid_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,ConstructionTowerHistoryLimit.value_freeClosed,continues_freeClosed]

theorem limit_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence limitSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) limitSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOrdinal_iff,
    Project.Term.eval_bound,ConstructionTowerValidity.valid_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,
    ConstructionTowerHistoryLimit.value_semantics hM,continues_semantics hM]
  exact fun hJ hV hR hTop hValue => limit_preserves hM hJ hV hR hTop hValue

theorem limit_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence limitSentence) := ModelTransfer.derives (fun _ hM => limit_models hM)

def successorSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 17 (.imp (Project.Formula.isOrdinal (.bound (14 : Fin 17))) (.imp
    (ConstructionTowerValidity.valid (0 : Fin 17) (1 : Fin 17) (2 : Fin 17) (3 : Fin 17) (4 : Fin 17) (5 :
    Fin 17) (6 : Fin 17) (7 : Fin 17) (8 : Fin 17) (9 : Fin 17) (14 : Fin 17) (15 : Fin 17)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 17) (1 : Fin 17) (2 : Fin 17)) (.imp (ConstructionRealCuts.cut
    (0 : Fin 17) (1 : Fin 17) (3 : Fin 17)) (.imp (ConstructionTowerHistorySuccessor.value (0 : Fin 17) (1 :
    Fin 17) (2 : Fin 17) (3 : Fin 17) (4 : Fin 17) (5 : Fin 17) (6 : Fin 17) (7 : Fin 17) (8 : Fin 17) (9 :
    Fin 17) (10 : Fin 17) (11 : Fin 17) (12 : Fin 17) (13 : Fin 17) (14 : Fin 17) (15 : Fin 17) (16 : Fin
    17)) (continues (0 : Fin 17) (1 : Fin 17) (2 : Fin 17) (3 : Fin 17) (4 : Fin 17) (5 : Fin 17) (6 : Fin
    17) (7 : Fin 17) (8 : Fin 17) (9 : Fin 17) (14 : Fin 17) (15 : Fin 17) (16 : Fin 17))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,
      ConstructionTowerValidity.valid_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,ConstructionTowerHistorySuccessor.value_freeClosed,continues_freeClosed]

theorem successor_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence successorSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) successorSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOrdinal_iff,
    Project.Term.eval_bound,ConstructionTowerValidity.valid_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,
    ConstructionTowerHistorySuccessor.value_semantics hM,continues_semantics hM]
  exact fun hJ hV hR hTop hValue => successor_preserves hM hJ hV hR hTop hValue

theorem successor_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence successorSentence) := ModelTransfer.derives (fun _ hM => successor_models hM)

/-- Complete source-parent successor consumer: the old Principal top
already supplies Cut via principal_cut; no new top assumption. -/
def successorConstructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 17 (.imp (ConstructionTowerValidity.valid (0 : Fin 17) (1 : Fin 17) (2 : Fin
    17) (3 : Fin 17) (4 : Fin 17) (5 : Fin 17) (6 : Fin 17) (7 : Fin 17) (8 : Fin 17) (9 : Fin 17) (14 : Fin
    17) (15 : Fin 17)) (.imp (Project.Formula.isOrdinal (.bound (14 : Fin 17))) (.imp
    (Project.Formula.isSuccessor (.bound (14 : Fin 17)) (.bound (13 : Fin 17))) (.imp
    (Project.Formula.isOmega (.bound (0 : Fin 17))) (.imp (Project.Formula.isEmpty (.bound (10 : Fin 17)))
    (.imp (.mem (.bound (10 : Fin 17)) (.bound (0 : Fin 17))) (.imp (ConstructionFractionOrder.carrier (0 :
    Fin 17) (1 : Fin 17)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 17) (1 : Fin 17) (2 : Fin 17))
    (.imp (ConstructionFractionOrder.coordinates (0 : Fin 17) (16 : Fin 17) (11 : Fin 17) (11 : Fin 17))
    (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 17))) (.imp (ConstructionRealCuts.principal (0 :
    Fin 17) (1 : Fin 17) (16 : Fin 17) (3 : Fin 17)) (.imp (ConstructionRoundStepSyntax.objectFields (0 :
    Fin 17) (1 : Fin 17) (2 : Fin 17) (3 : Fin 17) (4 : Fin 17) (5 : Fin 17) (6 : Fin 17) (7 : Fin 17) (8 :
    Fin 17) (9 : Fin 17)) (.imp (ConstructionRequestSchedule.request (0 : Fin 17) (4 : Fin 17) (5 : Fin 17)
    (6 : Fin 17) (10 : Fin 17) (11 : Fin 17) (12 : Fin 17)) (.existsE (.conj
    (ConstructionTowerHistorySuccessor.value (0 : Fin 17).succ (1 : Fin 17).succ (2 : Fin 17).succ (3 : Fin
    17).succ (4 : Fin 17).succ (5 : Fin 17).succ (6 : Fin 17).succ (7 : Fin 17).succ (8 : Fin 17).succ (9 :
    Fin 17).succ (10 : Fin 17).succ (11 : Fin 17).succ (12 : Fin 17).succ (13 : Fin 17).succ (14 : Fin
    17).succ (15 : Fin 17).succ (0 : Fin 18)) (.conj (continues (0 : Fin 17).succ (1 : Fin 17).succ (2 : Fin
    17).succ (3 : Fin 17).succ (4 : Fin 17).succ (5 : Fin 17).succ (6 : Fin 17).succ (7 : Fin 17).succ (8 :
    Fin 17).succ (9 : Fin 17).succ (14 : Fin 17).succ (15 : Fin 17).succ (0 : Fin 18)) (.forallE (.imp
    (ConstructionTowerHistorySuccessor.value (0 : Fin 17).succ.succ (1 : Fin 17).succ.succ (2 : Fin
    17).succ.succ (3 : Fin 17).succ.succ (4 : Fin 17).succ.succ (5 : Fin 17).succ.succ (6 : Fin
    17).succ.succ (7 : Fin 17).succ.succ (8 : Fin 17).succ.succ (9 : Fin 17).succ.succ (10 : Fin
    17).succ.succ (11 : Fin 17).succ.succ (12 : Fin 17).succ.succ (13 : Fin 17).succ.succ (14 : Fin
    17).succ.succ (15 : Fin 17).succ.succ (0 : Fin 19)) (Project.Formula.extensionalEq (.bound (0 : Fin 19))
    (.bound (1 : Fin 19))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionTowerValidity.valid_freeClosed,Project.Formula.isOrdinal,Project.Formula.isSuccessor,
      Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.isOrdinalOne,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionRequestSchedule.request_freeClosed,
      ConstructionTowerHistorySuccessor.value_freeClosed,continues_freeClosed,Project.Formula.extensionalEq]

theorem successorConstruction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence successorConstructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) successorConstructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isSuccessor_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionTowerValidity.valid_semantics hM,ConstructionFractionOrder.carrier_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    ConstructionRealCuts.principal_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,
    ConstructionRequestSchedule.request_semantics hM,
    ConstructionTowerHistorySuccessor.value_semantics hM,continues_semantics hM]
  intro hV hJ hSucc hw hz hzw hQ hR hu hone htop hObjD hq
  obtain ⟨output,hout⟩ := ConstructionTowerHistorySuccessor.exists_value hM hOrder
    hV hJ hSucc hw hz hzw hQ hR hu hone htop hObjD hq
  have hTop := ConstructionRealCuts.principal_cut hM hw hQ
    ((hQ (bound 16)).mpr ⟨bound 11,bound 11,hu⟩) htop
  exact ⟨output,hout,successor_preserves hM hJ hV hR hTop hout,
    fun other hOther => ConstructionTowerHistorySuccessor.value_unique hM hOrder hV hOther hout⟩

theorem successorConstruction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative successorConstructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM successorConstructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) successorConstructionSentence).mp
    (successorConstruction_models (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

def limitConstructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 13 (.imp (ConstructionTowerValidity.valid (0 : Fin 13) (1 : Fin 13) (2 : Fin
    13) (3 : Fin 13) (4 : Fin 13) (5 : Fin 13) (6 : Fin 13) (7 : Fin 13) (8 : Fin 13) (9 : Fin 13) (10 : Fin
    13) (11 : Fin 13)) (.imp (Project.Formula.isOrdinal (.bound (10 : Fin 13))) (.imp (.existsE (.mem
    (.bound (0 : Fin 14)) (.bound (10 : Fin 13).succ))) (.imp (Project.Formula.isOmega (.bound (0 : Fin
    13))) (.imp (ConstructionFractionOrder.carrier (0 : Fin 13) (1 : Fin 13)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 13) (1 : Fin 13) (2 : Fin 13)) (.imp (ConstructionRealCuts.cut
    (0 : Fin 13) (1 : Fin 13) (3 : Fin 13)) (.existsE (.conj (ConstructionTowerHistoryLimit.value (0 : Fin
    13).succ (1 : Fin 13).succ (2 : Fin 13).succ (3 : Fin 13).succ (4 : Fin 13).succ (5 : Fin 13).succ (6 :
    Fin 13).succ (7 : Fin 13).succ (8 : Fin 13).succ (9 : Fin 13).succ (10 : Fin 13).succ (11 : Fin 13).succ
    (12 : Fin 13).succ (0 : Fin 14)) (.conj (continues (0 : Fin 13).succ (1 : Fin 13).succ (2 : Fin 13).succ
    (3 : Fin 13).succ (4 : Fin 13).succ (5 : Fin 13).succ (6 : Fin 13).succ (7 : Fin 13).succ (8 : Fin
    13).succ (9 : Fin 13).succ (10 : Fin 13).succ (11 : Fin 13).succ (0 : Fin 14)) (.forallE (.imp
    (ConstructionTowerHistoryLimit.value (0 : Fin 13).succ.succ (1 : Fin 13).succ.succ (2 : Fin
    13).succ.succ (3 : Fin 13).succ.succ (4 : Fin 13).succ.succ (5 : Fin 13).succ.succ (6 : Fin
    13).succ.succ (7 : Fin 13).succ.succ (8 : Fin 13).succ.succ (9 : Fin 13).succ.succ (10 : Fin
    13).succ.succ (11 : Fin 13).succ.succ (12 : Fin 13).succ.succ (0 : Fin 15))
    (Project.Formula.extensionalEq (.bound (0 : Fin 15)) (.bound (1 : Fin 15))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionTowerValidity.valid_freeClosed,Project.Formula.isOrdinal,Project.Formula.isOmega,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,ConstructionTowerHistoryLimit.value_freeClosed,
      continues_freeClosed,Project.Formula.extensionalEq]

theorem limitConstruction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence limitConstructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) limitConstructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionTowerValidity.valid_semantics hM,ConstructionFractionOrder.carrier_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,
    ConstructionTowerHistoryLimit.value_semantics hM,continues_semantics hM]
  intro hV hJ hne hw hQ hR hTop
  obtain ⟨output,hout⟩ := ConstructionTowerHistoryLimit.exists_value hM hV hJ hne hw hQ hR hTop (bound 12)
  exact ⟨output,hout,limit_preserves hM hJ hV hR hTop hout,
    fun other hOther => ConstructionTowerHistoryLimit.value_unique hM hV hJ hne hOther hout⟩

theorem limitConstruction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence limitConstructionSentence) :=
  ModelTransfer.derives (fun _ hM => limitConstruction_models hM)

end PPAC.Migration.ConstructionTowerHistoryClosure
