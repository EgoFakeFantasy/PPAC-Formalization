/- Pinned BlockTowers.request_rangeAttachment / Saturation.blockStage_step.
Read the SAME SelectedAt execution, original scheduled request, old inclusion,
word carrier, multiplication, and root graph. Assemble the existing concrete
presentations from retained OperationSource/Done fields; no new cell or
replacement execution is selected. Consumer: actual rangeAttachment. -/
import PPAC.Migration.ConstructionCellSimulationEquiv
import PPAC.Migration.ConstructionTowerExecution

namespace PPAC.Migration.ConstructionExecutedCellPresentation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive)
open ConstructionTowerMapSucc (SelectedAt)
open ConstructionRequestSchedule (ProbeCode MergerCode)
open ConstructionProbeMappedPath (NodeMap)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ProbeData (hM : FirstOrder.Theory.Models M nativeZF)
    (w D mul e zero mark a b node W G unit O gen : M.Carrier .set) : Prop :=
  ∃ factor terminal target S C projection I act E K P,
    ConstructionProbePushout.Presentation hM w zero D mul e a b mark node factor terminal target S C projection I act E W unit G K P O ∧
    PureKuratowski.PairMember M zero gen P

/-- Recover the missing presentation views from the SAME retained tables.
In particular, TargetLaws is converted to TargetGraph using the original
projection's surjectivity, not by choosing a new target or alphabet. -/
theorem probe (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero mark a b node W G unit O gen : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hm : LeftCancelMonoid D mul e)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D)
    (hO : MapsTo D W O)
    (hSource : ConstructionOperationSource.Probe hM w D mul e zero mark a b node W G unit O gen) :
    ProbeData hM w D mul e zero mark a b node W G unit O gen := by
  obtain ⟨hPath,hb,_,S,act,E,projection,K,P,hAlphaSource,hWord,hUnit,hG,hOld,hK,hGen,hP,hProbe,hgen⟩ := hSource
  obtain ⟨I,target,factor,terminal,C,hAlpha,_,hTargetMap,hFactor,hTerminalMap,hTerminal,hTargetLaws,hExit,hC,hProjectionMap,hLetters,hProjection,hAction⟩ := hAlphaSource
  have hTable := ConstructionProbePath.table_laws hM hw hz hm hPath hFactor hTerminal
  have hMeets := ConstructionProbeTransitions.meets_laws hM hw hm hPath hFactor hTable
  have hEq := ConstructionProbeLetters.equality_law hM hC hMeets hProjection
  have hTarget : ConstructionProbeTarget.TargetGraph D mul projection terminal target := by
    intro c z
    constructor
    · intro hcz
      obtain ⟨i,x,hi,hx,hxc⟩ := ConstructionProbeAction.representative hC hLetters hProjection (ForcingConditionGraphs.function_input hTargetMap.1 hcz)
      obtain ⟨t,hit,_⟩ := hTerminalMap.1.2 i hi
      exact ⟨i,x,t,hx,hxc,hit,(hTargetLaws.1 i x t c z hxc hit).mp hcz⟩
    · rintro ⟨i,x,t,_,hxc,hit,hxt⟩
      exact (hTargetLaws.1 i x t c z hxc hit).mpr hxt
  exact ⟨factor,terminal,target,S,C,projection,I,act,E,K,P,
    ⟨hm,hAlpha,hWord,hb,hUnit,hG,hK,hGen,hC,hLetters,hProjectionMap,hProjection,hEq,hAction,
      hPath,hFactor,hP,hProbe,hTerminalMap,hTarget,hExit,hmark,hOld,hO⟩,hgen⟩

def MergerData (w n D mul e zero P W G unit O roots : M.Carrier .set) : Prop :=
  ∃ C L projection A T B,
    ConstructionMergerPushout.Presentation w n zero D mul e P C L projection A W T B G unit O roots

/-- Keep the original roots graph. Its MapsTo field comes from Done; only
its existing algebra laws are repackaged using the established producers. -/
theorem merger (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e zero P W G unit O roots : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hO : MapsTo D W O) (hRoots : MapsTo n W roots)
    (hSource : ConstructionOperationSource.Merger w n D mul e zero P W G unit O roots) :
    MergerData w n D mul e zero P W G unit O roots := by
  obtain ⟨hP,_,C,L,projection,K,A,I,T,B,hC,hp,hL,hProjection,hEq,_,_,hAction,_,hCopy,
    hW,_,hT,hWordAction,hWordFree,hB,hG,hProduct,hUnit,hOld,hRootGraph,_⟩ := hSource
  have hUW := ConstructionMergerWordMonoid.unit_laws hM hw hz hzw hm hW hT hWordFree hWordAction hProduct hUnit
  have hAssoc := ConstructionMergerWordMonoid.associative hM hw hz hzw hW hB hG hT hWordFree hWordAction hProduct
  have hOH : ConstructionProbePushout.Hom D W mul G e unit O :=
    ⟨hO,(hOld e unit).mpr hUnit,ConstructionMergerOldEmbedding.preserves_products hOld hWordAction hProduct⟩
  exact ⟨C,L,projection,A,T,B,hm,hP,hC,hL,hp,hProjection,hEq,hAction,hCopy,hW,hWordAction,hProduct,
    hUnit,hUW,hAssoc,hB,hG,hOld,hOH,hRoots,hRootGraph⟩

def Presented (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero one request N mulN eN markN f W G unit O roots : M.Carrier .set) : Prop :=
  (∃ a b node fa fb mapped, ProbeCode zero a b node request ∧
    PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f ∧ NodeMap node f mapped ∧
    ProbeData hM w N mulN eN zero markN fa fb mapped W G unit O roots) ∨
  ∃ n P PN, MergerCode one n P request ∧ ConstructionMergerPrescriptionMap.Graph P f PN ∧
    MergerData w n N mulN eN zero PN W G unit O roots

theorem of_provenance (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one request D mul N mulN eN markN f W G unit markW O base roots : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hne : zero ≠ one) (hm : LeftCancelMonoid N mulN eN)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem markN N) (hO : MapsTo N W O)
    (hDone : ConstructionRoundSelection.Done w D mul zero one request W G markW O base roots)
    (hSource : ConstructionRoundSource.Provenance hM w zero one request N mulN eN markN f W G unit O roots) :
    Presented hM w zero one request N mulN eN markN f W G unit O roots := by
  rcases hSource with ⟨a,b,node,fa,fb,mapped,hCode,hfa,hfb,hMap,hSource⟩ | ⟨n,P,PN,hCode,hMap,hSource⟩
  · exact Or.inl ⟨a,b,node,fa,fb,mapped,hCode,hfa,hfb,hMap,probe hM hw hz hm hmark hO hSource⟩
  · rcases hDone with ⟨a,b,node,hProbe,_⟩ | ⟨n',P',hCode',hDone,_⟩
    · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hProbe hCode)
    · obtain ⟨en,ep⟩ := ConstructionRequestSchedule.merger_code_injective hCode hCode'
      subst n'; subst P'
      exact Or.inr ⟨n,P,PN,hCode,hMap,merger hM hw hz hzw hm hO hDone.1 hSource⟩

def At (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one Schedule history F i j raw : M.Carrier .set) : Prop :=
  ∃ request N mulN eN markN HN CN K f W G unitW markW HL LC NewOut base O roots,
    PureKuratowski.PairMember M i request Schedule ∧
    Row history i N mulN eN markN HN CN K f i ∧
    Row history j W G unitW markW HL LC NewOut base j ∧
    ConstructionRoundSelection.Picked hM w Q R top zero one D mul e mark H C
      N mulN eN markN HN CN f request raw ∧
    ConstructionRoundSelection.Pack W G unitW markW HL LC O base roots raw ∧
    ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f
      W G unitW markW HL LC O base ∧
    ConstructionRoundSelection.Done w D mul zero one request W G markW O base roots ∧
    Product F i j O ∧ Presented hM w zero one request N mulN eN markN f W G unitW O roots

/-- No existential witness is reselected: all 19 fields of the actual
selected successor are retained, including the ninth raw roots field. -/
theorem of_selected (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u lengthBound Schedule history F i j raw : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule lengthBound history)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i lengthBound)
    (hSelected : SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F i j raw) :
    At hM w Q R top D mul e mark H C zero one Schedule history F i j raw := by
  have hValid := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  obtain ⟨hw,_,_,_,hone,_,_,hz,hzw,_,_,_⟩ := hCtx
  obtain ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,
    hRequest,hRowI,hRowJ,hPicked,hRaw,hStep,hDone,hO,hSource⟩ := hSelected
  have hObj := (hValid.2.1 i hi N mulN eN markN HN CN K f hRowI).1
  have hPresent := of_provenance hM hw hz hzw (ConstructionRequestSchedule.zero_ne_one hz hone)
    hObj.1 hObj.2.2.2.1 hStep.1.2.1.1.1.1 hDone hSource
  exact ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,
    hRequest,hRowI,hRowJ,hPicked,hRaw,hStep,hDone,hO,hPresent⟩

theorem map_succ (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u lengthBound Schedule history P F i j : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule lengthBound history)
    (hF : ConstructionTowerTransitions.Matrix lengthBound history zero P F)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i lengthBound)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j lengthBound)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf j i) :
    ∃ raw, SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F i j raw ∧
      At hM w Q R top D mul e mark H C zero one Schedule history F i j raw := by
  obtain ⟨raw,hSelected⟩ := ConstructionTowerMapSucc.map_succ_selected hM hCtx hRec hF hi hj hs
  exact ⟨raw,hSelected,of_selected hM hCtx hRec hi hSelected⟩

def probeData {m : Nat} (w D mul e zero mark a b node W G unit O gen : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionProbePushoutSyntax.presentation w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ node.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin (m+11)) (9 : Fin (m+11)) (8 : Fin (m+11)) (7 : Fin (m+11)) (6 : Fin (m+11)) (5 : Fin (m+11)) (4 : Fin (m+11)) (3 : Fin (m+11)) (2 : Fin (m+11)) W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+11)) (0 : Fin (m+11)) O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+11)) zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ gen.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))

theorem probeData_freeClosed {m : Nat} (w D mul e zero mark a b node W G unit O gen : Fin m) :
    (probeData w D mul e zero mark a b node W G unit O gen).FreeClosed := by
  simp -implicitDefEqProofs [probeData,Definitional.Formula.FreeClosed,ConstructionProbePushoutSyntax.presentation_freeClosed,ProjectSyntax.freeClosed]

theorem probeData_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero mark a b node W G unit O gen : Fin m) :
    Project.Formula.satisfies env (probeData w D mul e zero mark a b node W G unit O gen) ↔ ProbeData hM (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound mark) (env.bound a) (env.bound b) (env.bound node) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound gen) := by
  simp only [probeData,ProbeData,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionProbePushoutSyntax.presentation_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def mergerData {m : Nat} (w n D mul e zero P W G unit O roots : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (ConstructionMergerPushout.presentation w.succ.succ.succ.succ.succ.succ n.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ P.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)) (3 : Fin (m+6)) (2 : Fin (m+6)) W.succ.succ.succ.succ.succ.succ (1 : Fin (m+6)) (0 : Fin (m+6)) G.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ roots.succ.succ.succ.succ.succ.succ)))))))

theorem mergerData_freeClosed {m : Nat} (w n D mul e zero P W G unit O roots : Fin m) :
    (mergerData w n D mul e zero P W G unit O roots).FreeClosed := by
  simp -implicitDefEqProofs [mergerData,Definitional.Formula.FreeClosed,ConstructionMergerPushout.presentation_freeClosed]

theorem mergerData_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w n D mul e zero P W G unit O roots : Fin m) :
    Project.Formula.satisfies env (mergerData w n D mul e zero P W G unit O roots) ↔ MergerData (env.bound w) (env.bound n) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound P) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound roots) := by
  simp only [mergerData,MergerData,Project.Formula.satisfies_exists_iff,ConstructionMergerPushout.presentation_semantics hM]
  rfl

def presented {m : Nat} (w zero one request N mulN eN markN f W G unit O roots : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ConstructionRequestSchedule.probeCode zero.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6))
  (3 : Fin (m+6)) request.succ.succ.succ.succ.succ.succ) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (2 : Fin (m+6)))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ (4 : Fin (m+6)) (1 : Fin
  (m+6)))) (.conj (ConstructionProbeMappedPathSyntax.nodeMap (3 : Fin (m+6)) f.succ.succ.succ.succ.succ.succ
  (0 : Fin (m+6))) (probeData w.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ eN.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ markN.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (1 : Fin (m+6)) (0
  : Fin (m+6)) W.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ
  unit.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ
  roots.succ.succ.succ.succ.succ.succ))))))))))) (.existsE (.existsE (.existsE (.conj
  (ConstructionRequestSchedule.mergerCode one.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3))
  request.succ.succ.succ) (.conj (ConstructionMergerPrescriptionMapSyntax.graph (1 : Fin (m+3))
  f.succ.succ.succ (0 : Fin (m+3))) (mergerData w.succ.succ.succ (2 : Fin (m+3))
  N.succ.succ.succ mulN.succ.succ.succ eN.succ.succ.succ zero.succ.succ.succ (0 : Fin (m+3))
  W.succ.succ.succ G.succ.succ.succ unit.succ.succ.succ O.succ.succ.succ roots.succ.succ.succ)))))))

theorem presented_freeClosed {m : Nat} (w zero one request N mulN eN markN f W G unit O roots : Fin m) :
    (presented w zero one request N mulN eN markN f W G unit O roots).FreeClosed := by
  simp -implicitDefEqProofs [presented,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,probeData_freeClosed,ConstructionRequestSchedule.mergerCode_freeClosed,ConstructionMergerPrescriptionMapSyntax.graph_freeClosed,mergerData_freeClosed]

theorem presented_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero one request N mulN eN markN f W G unit O roots : Fin m) :
    Project.Formula.satisfies env (presented w zero one request N mulN eN markN f W G unit O roots) ↔ Presented hM (env.bound w) (env.bound zero) (env.bound one) (env.bound request) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound f) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound roots) := by
  simp only [presented,Presented,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_disj_iff,ConstructionRequestSchedule.probeCode_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,probeData_semantics hM,ConstructionRequestSchedule.mergerCode_semantics hM,ConstructionMergerPrescriptionMapSyntax.graph_semantics hM,mergerData_semantics hM]
  rfl

def atFormula {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F i j raw : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge
  Schedule.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (18 : Fin
  (m+19)))) (.conj (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (17 : Fin
  (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (13 : Fin (m+19)) (12 : Fin (m+19)) (11 :
  Fin (m+19)) (10 : Fin (m+19))
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
  (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (6 : Fin (m+19)) (5 : Fin (m+19)) (4 : Fin (m+19)) (3 : Fin
  (m+19)) (2 : Fin (m+19))
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionRoundSelection.picked
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (17 : Fin
  (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (13 : Fin (m+19)) (12 : Fin (m+19)) (10 :
  Fin (m+19)) (18 : Fin (m+19))
  raw.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionRoundSelection.pack (9 : Fin (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (6 : Fin (m+19)) (5 :
  Fin (m+19)) (4 : Fin (m+19)) (1 : Fin (m+19)) (2 : Fin (m+19)) (0 : Fin (m+19))
  raw.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionRoundStepSyntax.step
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (17 : Fin
  (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (13 : Fin (m+19)) (12 : Fin (m+19)) (10 :
  Fin (m+19)) (9 : Fin (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (6 : Fin (m+19)) (5 : Fin (m+19)) (4 : Fin
  (m+19)) (1 : Fin (m+19)) (2 : Fin (m+19))) (.conj (ConstructionRoundSelection.done
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (18 :
  Fin (m+19)) (9 : Fin (m+19)) (8 : Fin (m+19)) (6 : Fin (m+19)) (1 : Fin (m+19)) (2 : Fin (m+19)) (0 : Fin
  (m+19))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
  (m+19)))) (presented
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (18 :
  Fin (m+19)) (17 : Fin (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (10 : Fin (m+19)) (9 :
  Fin (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (1 : Fin (m+19)) (0 : Fin
  (m+19))))))))))))))))))))))))))))))

theorem atFormula_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F i j raw : Fin m) :
    (atFormula w Q R top D mul e mark H C zero one Schedule history F i j raw).FreeClosed := by
  simp -implicitDefEqProofs [atFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRoundSelection.picked_freeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionRoundStepSyntax.step_freeClosed,ConstructionRoundSelection.done_freeClosed,presented_freeClosed]

theorem atFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one Schedule history F i j raw : Fin m) :
    Project.Formula.satisfies env (atFormula w Q R top D mul e mark H C zero one Schedule history F i j raw) ↔ At hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound Schedule) (env.bound history) (env.bound F) (env.bound i) (env.bound j) (env.bound raw) := by
  simp only [atFormula,At,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,

    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerHistory.row_semantics hM,ConstructionRoundSelection.picked_semantics hM,ConstructionRoundSelection.pack_semantics hM,ConstructionRoundStepSyntax.step_semantics hM,ConstructionRoundSelection.done_semantics hM,presented_semantics hM,ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def selectedSentence {m : Nat} (w Q R top D mul e mark H C zero one u lengthBound Schedule history F i j raw : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionTowerIterationCases.context w Q R top D mul e mark H C zero one u lengthBound Schedule)
      (.imp (ConstructionTowerIteration.recursive w Q R top D mul e mark H C zero one lengthBound Schedule lengthBound history)
      (.imp (.mem (.bound i) (.bound lengthBound))
      (.imp (ConstructionTowerMapSucc.selectedAt w Q R top D mul e mark H C zero one Schedule history F i j raw)
      (atFormula w Q R top D mul e mark H C zero one Schedule history F i j raw)))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionTowerIterationCases.context_freeClosed,
      ConstructionTowerIteration.recursive_freeClosed,
      ConstructionTowerMapSucc.selectedAt_freeClosed,
      atFormula_freeClosed]

theorem selected_models {m : Nat} (w Q R top D mul e mark H C zero one u lengthBound Schedule history F i j raw : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (selectedSentence w Q R top D mul e mark H C zero one u lengthBound Schedule history F i j raw)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (selectedSentence w Q R top D mul e mark H C zero one u lengthBound Schedule history F i j raw)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    ConstructionTowerIterationCases.context_semantics hM,
    ConstructionTowerIteration.recursive_semantics hM,
    ConstructionTowerMapSucc.selectedAt_semantics hM,
    atFormula_semantics hM]
  exact of_selected hM

theorem selected_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one u lengthBound Schedule history F i j raw : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (selectedSentence w Q R top D mul e mark H C zero one u lengthBound Schedule history F i j raw)) :=
  ModelTransfer.derives (fun _ hM => selected_models w Q R top D mul e mark H C zero one u lengthBound Schedule history F i j raw hM)

def mapSuccSentence {m : Nat} (w Q R top D mul e mark H C zero one u lengthBound Schedule history P F i j : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionTowerIterationCases.context w Q R top D mul e mark H C zero one u lengthBound Schedule)
      (.imp (ConstructionTowerIteration.recursive w Q R top D mul e mark H C zero one lengthBound Schedule lengthBound history)
      (.imp (ConstructionTowerTransitions.matrix lengthBound history zero P F)
      (.imp (.mem (.bound i) (.bound lengthBound))
      (.imp (.mem (.bound j) (.bound lengthBound))
      (.imp (Project.Formula.isSuccessor (.bound j) (.bound i))
      (.existsE (.conj (ConstructionTowerMapSucc.selectedAt w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ zero.succ one.succ Schedule.succ history.succ F.succ i.succ j.succ 0) (atFormula w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ zero.succ one.succ Schedule.succ history.succ F.succ i.succ j.succ 0)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionTowerIterationCases.context_freeClosed,
      ConstructionTowerIteration.recursive_freeClosed,
      ConstructionTowerMapSucc.selectedAt_freeClosed,
      atFormula_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,
      Project.Formula.isSuccessor]

theorem mapSucc_models {m : Nat} (w Q R top D mul e mark H C zero one u lengthBound Schedule history P F i j : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (mapSuccSentence w Q R top D mul e mark H C zero one u lengthBound Schedule history P F i j)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (mapSuccSentence w Q R top D mul e mark H C zero one u lengthBound Schedule history P F i j)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    ConstructionTowerIterationCases.context_semantics hM,
    ConstructionTowerIteration.recursive_semantics hM,
    ConstructionTowerMapSucc.selectedAt_semantics hM,
    atFormula_semantics hM,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isSuccessor_iff,
    ConstructionTowerTransitions.matrix_semantics hM]
  exact map_succ hM

theorem mapSucc_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one u lengthBound Schedule history P F i j : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (mapSuccSentence w Q R top D mul e mark H C zero one u lengthBound Schedule history P F i j)) :=
  ModelTransfer.derives (fun _ hM => mapSucc_models w Q R top D mul e mark H C zero one u lengthBound Schedule history P F i j hM)

end PPAC.Migration.ConstructionExecutedCellPresentation
