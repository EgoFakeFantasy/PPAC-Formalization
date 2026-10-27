/- Pinned CompleteRounds.Round.probe/probe_transition and CompleteRound.probe.
Collect the SAME Picked raw execution and its existing ninth-field projection.
No new codec, choice mechanism, recurrence, or externally finite index set. -/
import PPAC.Migration.ConstructionTowerRequestCones

namespace PPAC.Migration.ConstructionTowerExecution
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerMapSucc (SelectedAt)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive)
open ConstructionTowerTransitions (Matrix)
open ConstructionTowerHistory (Chart Field)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def StepSet (J Steps : M.Carrier .set) : Prop := ∀ i,
  (Project.FirstOrderSemantics.reduct M).mem i Steps ↔
    (Project.FirstOrderSemantics.reduct M).mem i J ∧ ∃ j,
      (Project.FirstOrderSemantics.reduct M).mem j J ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf j i

def Value (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one Schedule history F J i raw : M.Carrier .set) : Prop :=
  ∃ j, (Project.FirstOrderSemantics.reduct M).mem j J ∧
    (Project.FirstOrderSemantics.reduct M).SuccessorOf j i ∧
    SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F i j raw

def Graph (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one Schedule history F J Steps Events : M.Carrier .set) : Prop :=
  ∀ i raw, PureKuratowski.PairMember M i raw Events ↔
    (Project.FirstOrderSemantics.reduct M).mem i Steps ∧
      Value hM w Q R top D mul e mark H C zero one Schedule history F J i raw

def stepSet {m : Nat} (J Steps : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound (0 : Fin (m+1))) (.bound Steps.succ)) (.conj (.mem (.bound (0 : Fin (m+1)))
  (.bound J.succ)) (.existsE (.conj (.mem (.bound (0 : Fin (m+2))) (.bound J.succ.succ))
  (Project.Formula.isSuccessor (.bound (0 : Fin (m+2))) (.bound (0 : Fin (m+1)).succ)))))))

theorem stepSet_freeClosed {m : Nat} (J Steps : Fin m) :
    (stepSet J Steps).FreeClosed := by
  simp -implicitDefEqProofs [stepSet,Definitional.Formula.FreeClosed,Project.Formula.isSuccessor]

theorem stepSet_semantics {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Steps : Fin m) :
    Project.Formula.satisfies env (stepSet J Steps) ↔ StepSet (env.bound J) (env.bound Steps) := by
  simp only [stepSet,StepSet,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isSuccessor_iff]
  rfl


def value {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F J i raw : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (.mem (.bound (0 : Fin (m+1))) (.bound J.succ)) (.conj (Project.Formula.isSuccessor (.bound
  (0 : Fin (m+1))) (.bound i.succ)) (ConstructionTowerMapSucc.selectedAt w.succ Q.succ R.succ top.succ
  D.succ mul.succ e.succ mark.succ H.succ C.succ zero.succ one.succ Schedule.succ history.succ F.succ i.succ
  (0 : Fin (m+1)) raw.succ))))

theorem value_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F J i raw : Fin m) :
    (value w Q R top D mul e mark H C zero one Schedule history F J i raw).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,Project.Formula.isSuccessor,ConstructionTowerMapSucc.selectedAt_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one Schedule history F J i raw : Fin m) :
    Project.Formula.satisfies env (value w Q R top D mul e mark H C zero one Schedule history F J i raw) ↔ Value hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound Schedule) (env.bound history) (env.bound F) (env.bound J) (env.bound i) (env.bound raw) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isSuccessor_iff,ConstructionTowerMapSucc.selectedAt_semantics hM]
  rfl


def graph {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F J Steps Events : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge Events.succ.succ (1 : Fin (m+2))
  (0 : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound Steps.succ.succ)) (value w.succ.succ
  Q.succ.succ R.succ.succ top.succ.succ D.succ.succ mul.succ.succ e.succ.succ mark.succ.succ H.succ.succ
  C.succ.succ zero.succ.succ one.succ.succ Schedule.succ.succ history.succ.succ F.succ.succ J.succ.succ (1 :
  Fin (m+2)) (0 : Fin (m+2)))))))

theorem graph_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F J Steps Events : Fin m) :
    (graph w Q R top D mul e mark H C zero one Schedule history F J Steps Events).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one Schedule history F J Steps Events : Fin m) :
    Project.Formula.satisfies env (graph w Q R top D mul e mark H C zero one Schedule history F J Steps Events) ↔ Graph hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound Schedule) (env.bound history) (env.bound F) (env.bound J) (env.bound Steps) (env.bound Events) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM]
  rfl


/-- Uniqueness of the actual event tuple comes from existing source Picked,
the same Schedule entry and the same current history row. -/
theorem selected_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top D mul e mark H C zero one Schedule history F J i j j' raw raw' : M.Carrier .set}
    (hSchedule : FunctionOn J Schedule) (hHistory : FunctionOn J history)
    (h1 : SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F i j raw)
    (h2 : SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F i j' raw') : raw = raw' := by
  obtain ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,
    hReq,hRow,_,hPicked,_⟩ := h1
  obtain ⟨request',N',mulN',eN',markN',HN',CN',K',f',W',G',unitW',markW',HL',LC',NewOut',base',O',roots',
    hReq',hRow',_,hPicked',_⟩ := h2
  have eqReq := ForcingConditionGraphs.function_unique hSchedule hReq hReq'
  subst request'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ := ConstructionTowerHistory.row_unique hHistory hRow hRow'
  exact ConstructionRoundSelection.picked_unique hM hOrder hPicked hPicked'

theorem exists_steps (hM : FirstOrder.Theory.Models M nativeZF) (J : M.Carrier .set) :
    ∃ Steps, StepSet J Steps := by
  let p : Project.UnarySchema 1 := {
    body := .existsE (.conj (.mem (.bound 0) (.bound 2))
      (Project.Formula.isSuccessor (.bound 0) (.bound 1)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isSuccessor] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := {
    bound := fun _ => J, free := fun _ => J }
  have he (i) : p.denote env i ↔ ∃ j, (Project.FirstOrderSemantics.reduct M).mem j J ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf j i := by
    change Project.Formula.satisfies (env.push i) p.body ↔ _
    simp only [p,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound]
    rfl
  obtain ⟨Steps,hSteps⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) p env J
  exact ⟨Steps,fun i => (hSteps i).trans (and_congr_right (fun _ => he i))⟩

/-- Native Replacement/function construction collects every INTERNAL valid
execution and its actual ninth field. The original selector supplies uniqueness. -/
theorem exists_execution (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top D mul e mark H C zero one u J Schedule history P F : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hF : Matrix J history zero P F) :
    ∃ Steps Outputs Events RootValues Roots, StepSet J Steps ∧ MapsTo Steps Outputs Events ∧
      Graph hM w Q R top D mul e mark H C zero one Schedule history F J Steps Events ∧
      MapsTo Steps RootValues Roots ∧ Chart 8 Steps Events Roots := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hValid := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hSchedule,_⟩ := hCtxCopy
  obtain ⟨Steps,hSteps⟩ := exists_steps hM J
  let schema : Project.BinarySchema 16 := {
    body := value 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 1 0
    freeClosed := value_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 16 := {
    bound := fun i => match i.val with
      | 0 => w | 1 => Q | 2 => R | 3 => top | 4 => D | 5 => mul | 6 => e | 7 => mark
      | 8 => H | 9 => C | 10 => zero | 11 => one | 12 => Schedule | 13 => history | 14 => F | _ => J
    free := fun _ => J }
  have he (i raw) : schema.denote env i raw ↔
      Value hM w Q R top D mul e mark H C zero one Schedule history F J i raw :=
    value_semantics hM ((env.push i).push raw) 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 1 0
  have ht (i) (hi : (Project.FirstOrderSemantics.reduct M).mem i Steps) : ∃ raw, schema.denote env i raw := by
    obtain ⟨hiJ,j,hj,hs⟩ := (hSteps i).mp hi
    obtain ⟨raw,hSelected⟩ := ConstructionTowerMapSucc.map_succ_selected hM hCtx hRec hF hiJ hj hs
    exact ⟨raw,(he i raw).mpr ⟨j,hj,hs,hSelected⟩⟩
  have hu (i) (_ : (Project.FirstOrderSemantics.reduct M).mem i Steps) (x y)
      (hx : schema.denote env i x) (hy : schema.denote env i y) : x = y := by
    obtain ⟨j,_,_,hX⟩ := (he i x).mp hx
    obtain ⟨j',_,_,hY⟩ := (he i y).mp hy
    exact selected_unique hM hOrder hSchedule hValid.1.1 hX hY
  obtain ⟨Outputs,hOutputs⟩ := ZF.exists_functionalImageOn hZF schema env Steps ht hu
  obtain ⟨Events,hEvents,hEG⟩ := ZF.exists_setFunctionFromTo_of_denote hZF
    (KuratowskiZF.interpretation hM) schema env ht hu
    (fun i raw hi hv => (hOutputs raw).mpr ⟨i,hi,hv⟩)
  have hE : MapsTo Steps Outputs Events := (ForcingSupportSize.native_mapsTo hM Steps Outputs Events).mpr hEvents
  have hGraph : Graph hM w Q R top D mul e mark H C zero one Schedule history F J Steps Events :=
    fun i raw => (hEG i raw).trans (and_congr_right (fun _ => he i raw))
  let rp : Project.BinarySchema 1 := {
    body := ConstructionTowerHistory.field 8 2 1 0
    freeClosed := ConstructionTowerHistory.field_freeClosed .. }
  let renv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := {
    bound := fun _ => Events, free := fun _ => J }
  have hr (i root) : rp.denote renv i root ↔ Field 8 Events i root :=
    ConstructionTowerHistory.field_semantics hM 8 ((renv.push i).push root) 2 1 0
  have hrt (i) (hi : (Project.FirstOrderSemantics.reduct M).mem i Steps) : ∃ root, rp.denote renv i root := by
    obtain ⟨raw,hERaw,_⟩ := hE.1.2 i hi
    obtain ⟨j,_,_,hSelected⟩ := ((hGraph i raw).mp hERaw).2
    obtain ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,
      _,_,_,_,hPack,_⟩ := hSelected
    exact ⟨roots,(hr i roots).mpr ⟨W,G,unitW,markW,HL,LC,O,base,roots,⟨raw,hERaw,hPack⟩,rfl⟩⟩
  have hru (i) (_ : (Project.FirstOrderSemantics.reduct M).mem i Steps) (x y)
      (hx : rp.denote renv i x) (hy : rp.denote renv i y) : x = y :=
    ConstructionTowerHistory.field_unique 8 hE.1 ((hr i x).mp hx) ((hr i y).mp hy)
  obtain ⟨RootValues,hValues⟩ := ZF.exists_functionalImageOn hZF rp renv Steps hrt hru
  obtain ⟨Roots,hRoots,hRG⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    rp renv hrt hru (fun i root hi hv => (hValues root).mpr ⟨i,hi,hv⟩)
  have hR : MapsTo Steps RootValues Roots := (ForcingSupportSize.native_mapsTo hM Steps RootValues Roots).mpr hRoots
  exact ⟨Steps,Outputs,Events,RootValues,Roots,hSteps,hE,hGraph,hR,hR.1,
    fun i root => (hRG i root).trans (and_congr_right (fun _ => hr i root))⟩

/-- The stored field is exactly the SAME selected generator/root object. -/
theorem selected_root (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one Schedule history F J Steps Events Roots i j raw
      W G unitW markW HL LC O base root : M.Carrier .set}
    (hSteps : StepSet J Steps)
    (hGraph : Graph hM w Q R top D mul e mark H C zero one Schedule history F J Steps Events)
    (hRoots : Chart 8 Steps Events Roots)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf j i)
    (hSelected : SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F i j raw)
    (hPack : ConstructionRoundSelection.Pack W G unitW markW HL LC O base root raw) :
    PureKuratowski.PairMember M i root Roots := by
  have hiS := (hSteps i).mpr ⟨hi,j,hj,hs⟩
  have hERaw := (hGraph i raw).mpr ⟨hiS,j,hj,hs,hSelected⟩
  exact (hRoots.2 i root).mpr ⟨hiS,W,G,unitW,markW,HL,LC,O,base,root,⟨raw,hERaw,hPack⟩,rfl⟩


def executionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 18 (.imp (ConstructionTowerIterationCases.context (0 : Fin 18) (1 : Fin 18)
    (2 : Fin 18) (3 : Fin 18) (4 : Fin 18) (5 : Fin 18) (6 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18)
    (10 : Fin 18) (11 : Fin 18) (12 : Fin 18) (13 : Fin 18) (14 : Fin 18)) (.imp
    (ConstructionTowerIteration.recursive (0 : Fin 18) (1 : Fin 18) (2 : Fin 18) (3 : Fin 18) (4 : Fin 18)
    (5 : Fin 18) (6 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18) (10 : Fin 18) (11 : Fin 18) (13 : Fin
    18) (14 : Fin 18) (13 : Fin 18) (15 : Fin 18)) (.imp (ConstructionTowerTransitions.matrix (13 : Fin 18)
    (15 : Fin 18) (10 : Fin 18) (16 : Fin 18) (17 : Fin 18)) (.existsE (.existsE (.existsE (.existsE
    (.existsE (.conj (stepSet (13 : Fin 18).succ.succ.succ.succ.succ (4 : Fin 23)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (2 : Fin 23) (4 : Fin 23) (3 : Fin 23))) (.conj
    (graph (0 : Fin 18).succ.succ.succ.succ.succ (1 : Fin 18).succ.succ.succ.succ.succ (2 : Fin
    18).succ.succ.succ.succ.succ (3 : Fin 18).succ.succ.succ.succ.succ (4 : Fin 18).succ.succ.succ.succ.succ
    (5 : Fin 18).succ.succ.succ.succ.succ (6 : Fin 18).succ.succ.succ.succ.succ (7 : Fin
    18).succ.succ.succ.succ.succ (8 : Fin 18).succ.succ.succ.succ.succ (9 : Fin 18).succ.succ.succ.succ.succ
    (10 : Fin 18).succ.succ.succ.succ.succ (11 : Fin 18).succ.succ.succ.succ.succ (14 : Fin
    18).succ.succ.succ.succ.succ (15 : Fin 18).succ.succ.succ.succ.succ (17 : Fin
    18).succ.succ.succ.succ.succ (13 : Fin 18).succ.succ.succ.succ.succ (4 : Fin 23) (2 : Fin 23)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 23) (4 : Fin 23) (1 : Fin 23)))
    (ConstructionTowerHistory.chart 8 (4 : Fin 23) (2 : Fin 23) (0 : Fin 23)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionTowerIterationCases.context_freeClosed,ConstructionTowerIteration.recursive_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,stepSet_freeClosed,graph_freeClosed,
      ConstructionTowerHistory.chart_freeClosed]

theorem execution_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence executionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) executionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    ConstructionTowerIterationCases.context_semantics hM,ConstructionTowerIteration.recursive_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,stepSet_semantics,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),graph_semantics hM,ConstructionTowerHistory.chart_semantics hM 8]
  exact fun hCtx hRec hF => exists_execution hM hOrder hCtx hRec hF

theorem execution_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative executionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM executionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) executionSentence).mp
    (execution_models (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

end PPAC.Migration.ConstructionTowerExecution
