/- Pinned BlockTowers.Saturation.blockIndex/blockFunctor/blocks: retain one
actual inner execution per outer stage, independently of the queried word.
Consume CompleteRound.Built and map_succ_selected; do not rerun the round.
The existing nine-field Pack and L least-denote/function constructors suffice. -/
import PPAC.Migration.ConstructionSaturationIterationValidity

namespace PPAC.Migration.ConstructionBlockTraces
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerExecution (StepSet)
open ConstructionTowerTransitions (Before Matrix)
open ConstructionTowerHistory (Row Chart)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive)
open ConstructionProbeMappedPath (NodeMap)
open ForcingSupportSize (MapsTo Injection Small)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

open ConstructionRoundSelection (Pack)
open ForcingConditionGraphs (FunctionOn)

def Trace (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code : M.Carrier .set) : Prop :=
  ∃ u A I indexTop default oldSchedule oldPlace r order J collapse inverse Schedule Place last
      history P F Steps Events Roots L,
    Pack J Schedule last history F Steps Events Roots L code ∧
    Context hM w Q R top D mul e mark H C zero one u J Schedule ∧
    ConstructionOrdinalSchedule.Data hM Requests K A I indexTop default oldSchedule oldPlace r order
      J collapse inverse Schedule Place last ∧ Small J mu ∧
    Recursive hM w Q R top D mul e mark H C zero one J Schedule J history ∧
    Matrix J history zero P F ∧ StepSet J Steps ∧
    ConstructionTowerExecution.Graph hM w Q R top D mul e mark H C zero one Schedule history F J Steps Events ∧
    Chart 8 Steps Events Roots ∧ Row history last W G unitW markW HW CW L O last ∧
    ConstructionTowerCardinality.AllSmall J history mu


def trace {m : Nat} (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.conj (ConstructionRoundSelection.pack 12 9 7 6 4 3 2 1 0
  code.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionTowerIterationCases.context
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  21 12 9) (.conj (ConstructionOrdinalScheduleSyntax.data
  Requests.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  20 19 18 17 16 15 14 13 12 11 10 9 8 7) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small 12
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ConstructionTowerIteration.recursive
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  12 9 12 6) (.conj (ConstructionTowerTransitions.matrix 12 6
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  5 4) (.conj (ConstructionTowerExecution.stepSet 12 3) (.conj (ConstructionTowerExecution.graph
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  9 6 4 12 3 2) (.conj (ConstructionTowerHistory.chart 8 3 2 1) (.conj (ConstructionTowerHistory.row 6 7
  W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unitW.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  markW.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  HW.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  CW.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  0
  O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  7) (ConstructionTowerCardinality.allSmall 12 6
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))))))))))))))))))

theorem trace_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code : Fin m) :
    (trace w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code).FreeClosed := by
  simp -implicitDefEqProofs [trace,Definitional.Formula.FreeClosed,ConstructionRoundSelection.pack_freeClosed,ProjectSyntax.freeClosed,ConstructionTowerIterationCases.context_freeClosed,ConstructionOrdinalScheduleSyntax.data_freeClosed,ConstructionTowerIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerExecution.stepSet_freeClosed,ConstructionTowerExecution.graph_freeClosed,ConstructionTowerHistory.chart_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionTowerCardinality.allSmall_freeClosed]

theorem trace_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code : Fin m) :
    Project.Formula.satisfies env (trace w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code) ↔ Trace hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound Requests) (env.bound W) (env.bound G) (env.bound unitW) (env.bound markW) (env.bound HW) (env.bound CW) (env.bound O) (env.bound code) := by
  simp only [trace,Trace,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,ConstructionRoundSelection.pack_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionTowerIterationCases.context_semantics hM,ConstructionOrdinalScheduleSyntax.data_semantics hM,ForcingSupportSize.small_semantics (M := M),ConstructionTowerIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerExecution.stepSet_semantics,ConstructionTowerExecution.graph_semantics hM,ConstructionTowerHistory.chart_semantics hM 8,ConstructionTowerHistory.row_semantics hM,ConstructionTowerCardinality.allSmall_semantics hM]
  rfl

theorem trace_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O : M.Carrier .set} (h : ConstructionCompleteRound.Built hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O) :
    ∃ code, Trace hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code := by
  obtain ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J,collapse,inverse,Schedule,Place,last,history,P,F,Steps,Events,Roots,L,h⟩ := h
  obtain ⟨code,hcode⟩ := ConstructionRoundSelection.pack_exists hM J Schedule last history F Steps Events Roots L
  exact ⟨code,u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J,collapse,inverse,Schedule,Place,last,history,P,F,Steps,Events,Roots,L,hcode,h⟩

theorem trace_built (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code : M.Carrier .set} (h : Trace hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code) :
    ConstructionCompleteRound.Built hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O := by
  obtain ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J,collapse,inverse,Schedule,Place,last,history,P,F,Steps,Events,Roots,L,_,h⟩ := h
  exact ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J,collapse,inverse,Schedule,Place,last,history,P,F,Steps,Events,Roots,L,h⟩

/-- A trace of the actual selected round, with both original outer rows and
its original global inclusion retained. The code records the inner nine fields. -/
def At (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero one K mu history F i code : M.Carrier .set) : Prop :=
  ∃ j raw Requests N mulN eN markN HN CN L f W G unitW markW HW CW NewOut baseW O,
    (Project.FirstOrderSemantics.reduct M).SuccessorOf j i ∧
    Row history i N mulN eN markN HN CN L f i ∧
    Row history j W G unitW markW HW CW NewOut baseW j ∧
    ConstructionSaturationStep.Picked hM w Q R top N mulN eN markN HN CN zero one K mu raw ∧
    ConstructionSaturationStep.Candidate hM w Q R top N mulN eN markN HN CN zero one K mu raw ∧
    Pack W G unitW markW HW CW O Requests zero raw ∧
    Product F i j O ∧ NodeMap f O baseW ∧
    Trace hM w Q R top N mulN eN markN HN CN zero one K mu Requests W G unitW markW HW CW O code

def traceAt {m : Nat} (w Q R top zero one K mu history F i code : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (Project.Formula.isSuccessor (.bound 19) (.bound
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj
  (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 16 15 14
  13 12 11 10 9
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 19
  8 7 6 5 4 3 2 1 19) (.conj (ConstructionSaturationStep.picked
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 16 15
  14 13 12 11
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 18)
  (.conj (ConstructionSaturationStep.candidate
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 16 15
  14 13 12 11
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 18)
  (.conj (ConstructionRoundSelection.pack 8 7 6 5 4 3 0 17
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 18)
  (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 19 0))
  (.conj (ConstructionProbeMappedPathSyntax.nodeMap 9 0 1) (trace
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 16 15
  14 13 12 11
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 17 8 7
  6 5 4 3 0
  code.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))))))))))))))

theorem at_freeClosed {m : Nat} (w Q R top zero one K mu history F i code : Fin m) :
    (traceAt w Q R top zero one K mu history F i code).FreeClosed := by
  simp -implicitDefEqProofs [traceAt,Definitional.Formula.FreeClosed,Project.Formula.isSuccessor,ConstructionTowerHistory.row_freeClosed,ConstructionSaturationStep.picked_freeClosed,ConstructionSaturationStep.candidate_freeClosed,ConstructionRoundSelection.pack_freeClosed,ProjectSyntax.freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,trace_freeClosed]

theorem at_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero one K mu history F i code : Fin m) :
    Project.Formula.satisfies env (traceAt w Q R top zero one K mu history F i code) ↔ At hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound history) (env.bound F) (env.bound i) (env.bound code) := by
  simp only [traceAt,At,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionTowerHistory.row_semantics hM,ConstructionSaturationStep.picked_semantics hM,ConstructionSaturationStep.candidate_semantics hM,ConstructionRoundSelection.pack_semantics hM,ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,trace_semantics hM]
  rfl

theorem at_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one K mu history F i j raw : M.Carrier .set}
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf j i)
    (h : ConstructionSaturationIterationValidity.SelectedAt hM w Q R top zero one K mu history F i j raw) :
    ∃ code, At hM w Q R top zero one K mu history F i code := by
  obtain ⟨Requests,N,mulN,eN,markN,HN,CN,L,f,W,G,unitW,markW,HW,CW,NewOut,baseW,O,
    hSource,hTarget,hPicked,hCandidate,hPack,hGlobal,hBase⟩ := h
  have hCandidateCopy := hCandidate
  obtain ⟨Requests',W',G',unitW',markW',HW',CW',O',hp,_,_,_,_,_,_,_,hBuilt⟩ := hCandidateCopy
  obtain ⟨eqW,eqG,eqUnit,eqMark,eqH,eqC,eqO,eqRequests,_⟩ :=
    ConstructionRoundSelection.pack_injective hp hPack
  subst W' G' unitW' markW' HW' CW' O' Requests'
  obtain ⟨code,hTrace⟩ := trace_exists hM hBuilt
  exact ⟨code,j,raw,Requests,N,mulN,eN,markN,HN,CN,L,f,W,G,unitW,markW,HW,CW,NewOut,baseW,O,hs,hSource,hTarget,hPicked,hCandidate,hPack,hGlobal,hBase,hTrace⟩

theorem at_selected (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one K mu history F i code : M.Carrier .set} (h : At hM w Q R top zero one K mu history F i code) :
    ∃ j raw, (Project.FirstOrderSemantics.reduct M).SuccessorOf j i ∧
      ConstructionSaturationIterationValidity.SelectedAt hM w Q R top zero one K mu history F i j raw := by
  obtain ⟨j,raw,Requests,N,mulN,eN,markN,HN,CN,L,f,W,G,unitW,markW,HW,CW,NewOut,baseW,O,hs,hSource,hTarget,hPicked,hCandidate,hPack,hGlobal,hBase,_⟩ := h
  exact ⟨j,raw,hs,Requests,N,mulN,eN,markN,HN,CN,L,f,W,G,unitW,markW,HW,CW,NewOut,baseW,O,hSource,hTarget,hPicked,hCandidate,hPack,hGlobal,hBase⟩

def PickedAt (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero one K mu history F i code : M.Carrier .set) : Prop :=
  At hM w Q R top zero one K mu history F i code ∧ ∀ other, At hM w Q R top zero one K mu history F i other →
    ¬ InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M) other code

def pickedAt {m : Nat} (w Q R top zero one K mu history F i code : Fin m) : Project.Formula 1 m :=
  (.conj (traceAt w Q R top zero one K mu history F i code) (.forallE (.imp (traceAt w.succ Q.succ R.succ top.succ
  zero.succ one.succ K.succ mu.succ history.succ F.succ i.succ 0) (.neg (InnerModel.js_less_m (.bound 0) (.bound
  code.succ))))))

theorem pickedAt_freeClosed {m : Nat} (w Q R top zero one K mu history F i code : Fin m) :
    (pickedAt w Q R top zero one K mu history F i code).FreeClosed := by
  simp -implicitDefEqProofs [pickedAt,Definitional.Formula.FreeClosed,at_freeClosed,InnerModel.js_less_m_freeClosed]

theorem pickedAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero one K mu history F i code : Fin m) :
    Project.Formula.satisfies env (pickedAt w Q R top zero one K mu history F i code) ↔
      PickedAt hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound history) (env.bound F) (env.bound i) (env.bound code) := by
  simp only [pickedAt,PickedAt,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    at_semantics hM,InnerModel.js_less_formula_l (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM))]
  rfl

theorem pickedAt_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top zero one K mu history F i : M.Carrier .set} (h : ∃ code, At hM w Q R top zero one K mu history F i code) :
    ∃ code, PickedAt hM w Q R top zero one K mu history F i code := by
  let schema : Project.UnarySchema 11 := {
    body := traceAt 1 2 3 4 5 6 7 8 9 10 11 0
    freeClosed := at_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 11 := {
    bound := (Fin.cases w (Fin.cases Q (Fin.cases R (Fin.cases top (Fin.cases zero (Fin.cases one (Fin.cases K (Fin.cases mu (Fin.cases history (Fin.cases F (fun _ => i))))))))))), free := fun _ => i }
  have he code : schema.denote env code ↔ At hM w Q R top zero one K mu history F i code :=
    at_semantics hM (env.push code) 1 2 3 4 5 6 7 8 9 10 11 0
  obtain ⟨code,hcode,hmin⟩ := ConstructionRoundSelection.least_denote hM hOrder schema env
    (h.elim fun code hc => ⟨code,(he code).mpr hc⟩)
  exact ⟨code,(he code).mp hcode,fun other ho => hmin other ((he other).mpr ho)⟩

theorem pickedAt_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top zero one K mu history F i x y : M.Carrier .set}
    (hx : PickedAt hM w Q R top zero one K mu history F i x) (hy : PickedAt hM w Q R top zero one K mu history F i y) : x = y := by
  rcases hOrder.2.2.1 x y with he | hxy | hyx
  · exact he
  · exact False.elim (hy.2 x hx.1 hxy)
  · exact False.elim (hx.2 y hy.1 hyx)

/-- An internal function of the outer stage alone; all word queries reuse it. -/
def Family (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero one K mu history F kappa traces : M.Carrier .set) : Prop :=
  FunctionOn kappa traces ∧ ∀ i code, PureKuratowski.PairMember M i code traces ↔
    (Project.FirstOrderSemantics.reduct M).mem i kappa ∧ PickedAt hM w Q R top zero one K mu history F i code

def family {m : Nat} (w Q R top zero one K mu history F kappa traces : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn traces kappa)) (.forallE (.forallE (.iff
  (ProjectSyntax.encode id (Source.SetLanguage.edge traces.succ.succ 1 0)) (.conj (.mem (.bound 1) (.bound
  kappa.succ.succ)) (pickedAt w.succ.succ Q.succ.succ R.succ.succ top.succ.succ zero.succ.succ one.succ.succ
  K.succ.succ mu.succ.succ history.succ.succ F.succ.succ 1 0))))))

theorem family_freeClosed {m : Nat} (w Q R top zero one K mu history F kappa traces : Fin m) :
    (family w Q R top zero one K mu history F kappa traces).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,pickedAt_freeClosed]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero one K mu history F kappa traces : Fin m) :
    Project.Formula.satisfies env (family w Q R top zero one K mu history F kappa traces) ↔
      Family hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound history) (env.bound F) (env.bound kappa) (env.bound traces) := by
  simp only [family,Family,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingConditionGraphs.functionOn_semantics (M := M),pickedAt_semantics hM]
  rfl

/-- Construct the whole family from the already-selected outer successors. -/
theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top zero one K mu history F kappa : M.Carrier .set}
    (hSelected : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i kappa →
      ∃ j raw, (Project.FirstOrderSemantics.reduct M).SuccessorOf j i ∧
        ConstructionSaturationIterationValidity.SelectedAt hM w Q R top zero one K mu history F i j raw) :
    ∃ traces, Family hM w Q R top zero one K mu history F kappa traces := by
  let schema : Project.BinarySchema 10 := {
    body := pickedAt 2 3 4 5 6 7 8 9 10 11 1 0
    freeClosed := pickedAt_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 10 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases R (Fin.cases top (Fin.cases zero
      (Fin.cases one (Fin.cases K (Fin.cases mu (Fin.cases history (fun _ => F)))))))))
    free := fun _ => kappa }
  have he i code : schema.denote env i code ↔ PickedAt hM w Q R top zero one K mu history F i code :=
    pickedAt_semantics hM ((env.push i).push code) 2 3 4 5 6 7 8 9 10 11 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i kappa → ∃ code, schema.denote env i code := by
    intro i hi
    obtain ⟨j,raw,hs,hSelected⟩ := hSelected i hi
    obtain ⟨code,hcode⟩ := pickedAt_exists hM hOrder (at_exists hM hs hSelected)
    exact ⟨code,(he i code).mpr hcode⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i kappa → ∀ x y,
      schema.denote env i x → schema.denote env i y → x = y :=
    fun _ _ _ _ hx hy => pickedAt_unique hM hOrder ((he _ _).mp hx) ((he _ _).mp hy)
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn (ModelTransfer.project_models_iff.mp hM) schema env kappa ht hu
  obtain ⟨traces,hTraces,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema env ht hu
    (fun i code hi hc => (hA code).mpr ⟨i,hi,hc⟩)
  exact ⟨traces,((ForcingSupportSize.native_mapsTo hM kappa A traces).mpr hTraces).1,
    fun i code => (hGraph i code).trans (and_congr_right fun _ => he i code)⟩

/-- Consume the actual fixed outer recursion and its global matrix. No
complete-round witnesses or per-stage selection are assumed by the caller. -/
theorem recursive_family (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu B history P F kappa : M.Carrier .set}
    (hCtx : ConstructionSaturationIterationCases.Context hM w Q R top D mul e mark H C zero one u K mu B)
    (hRec : ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history)
    (hF : Matrix B history zero P F)
    (hk : (Project.FirstOrderSemantics.reduct M).mem kappa B) :
    ∃ traces, Family hM w Q R top zero one K mu history F kappa traces := by
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hB,_⟩ := hCtxCopy
  apply exists_family hM hOrder
  intro i hi
  obtain ⟨j,hj,hs,_⟩ := ConstructionCompleteRound.successor_before_last hM hB hk hi
  obtain ⟨raw,hSelected⟩ := ConstructionSaturationIterationValidity.map_succ_selected hM hOrder hChoice
    hCtx hRec hF (hB.transitive kappa hk i hi) hj hs
  exact ⟨j,raw,hs,hSelected⟩

theorem family_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one K mu history F kappa X Y : M.Carrier .set}
    (hx : Family hM w Q R top zero one K mu history F kappa X) (hy : Family hM w Q R top zero one K mu history F kappa Y) : X = Y := by
  have rel {f} (hf : FunctionOn kappa f) :
      (Project.FirstOrderSemantics.reduct M).IsSetRelation (KuratowskiZF.interpretation hM) f := by
    intro p hp
    obtain ⟨i,code,_,hc⟩ := hf.1 p hp
    exact ⟨i,code,hc⟩
  apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    (rel hx.1) (rel hy.1)
  intro i code
  exact (hx.2 i code).trans (hy.2 i code).symm

/-- Expose the nine fields from the SAME fixed trace row, ready for the
existing Field/Chart syntax. No word, finite support or query parameter. -/
theorem family_row (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one K mu history F kappa traces i : M.Carrier .set}
    (hf : Family hM w Q R top zero one K mu history F kappa traces) (hi : (Project.FirstOrderSemantics.reduct M).mem i kappa) :
    ∃ J Schedule last inner Finner Steps Events Roots L,
      Row traces i J Schedule last inner Finner Steps Events Roots L := by
  obtain ⟨code,hcode,_⟩ := hf.1.2 i hi
  have hAt := ((hf.2 i code).mp hcode).2.1
  obtain ⟨j,raw,Requests,N,mulN,eN,markN,HN,CN,L0,f,W,G,unitW,markW,HW,CW,NewOut,baseW,O,
    _,_,_,_,_,_,_,_,hTrace⟩ := hAt
  obtain ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J,collapse,inverse,Schedule,Place,last,
    inner,P,Finner,Steps,Events,Roots,L,hPack,_⟩ := hTrace
  exact ⟨J,Schedule,last,inner,Finner,Steps,Events,Roots,L,code,hcode,hPack⟩

/-- Pure set-language sentence; the actual producer runs in the existing
constructible interpretation. All outer-history and matrix parameters stay fixed. -/
def constructionSentence {m : Nat} (w Q R top D mul e mark H C zero one u K mu B history P F kappa : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionSaturationIterationCases.context w Q R top D mul e mark H C zero one u K mu B) (.imp
    (ConstructionSaturationIteration.recursive w Q R top D mul e mark H C zero one K mu B B history) (.imp
    (ConstructionTowerTransitions.matrix B history zero P F) (.imp (.mem (.bound kappa) (.bound B)) (.existsE
    (family w.succ Q.succ R.succ top.succ zero.succ one.succ K.succ mu.succ history.succ F.succ kappa.succ
    0))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionSaturationIterationCases.context_freeClosed,
      ConstructionSaturationIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,
      family_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {m : Nat} (w Q R top D mul e mark H C zero one u K mu B history P F kappa : Fin m) :
    (Project.fo_sentence (constructionSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionSaturationIterationCases.context_semantics hM,
    ConstructionSaturationIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,
    family_semantics hM]
  exact recursive_family hM hOrder hChoice

theorem construction_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one u K mu B history P F kappa : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa)).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice w Q R top D mul e mark H C zero one u K mu B history P F kappa)

end PPAC.Migration.ConstructionBlockTraces
