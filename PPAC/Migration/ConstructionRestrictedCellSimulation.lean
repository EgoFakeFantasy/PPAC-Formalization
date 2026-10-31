/- Pinned CellCuts.restrict_selected: construct the actual cell over the
retained base and its conservative simulation into the ORIGINAL fixed cell.
The original target presentation is never regenerated. -/
import PPAC.Migration.ConstructionSelectedCellRestriction

namespace PPAC.Migration.ConstructionRestrictedCellSimulation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePushout (Hom IsPushout SquareComm)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionProbePath (TerminalTable)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionCellGeneration (Generated)
open ConstructionProbeSimulation (EndpointLaws)
open ForcingSupportSize (MapsTo)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Complete preimage Probe, including its actual multiplication and indexed
generators, and the conservative pushout map into the supplied target. -/
def Probe (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero cut cutMul e D mul a b d node W unit G O P inc
      a0 b0 d0 node0 factor0 terminal0 target0 L0 C0 projection0 I0 act0 E0 W0 unit0 G0 K0 P0 O0 H : M.Carrier .set) : Prop :=
  PureKuratowski.PairMember M a0 a inc ∧ PureKuratowski.PairMember M b0 b inc ∧
    PureKuratowski.PairMember M d0 d inc ∧ NodeMap node0 inc node ∧
    ConstructionProbePushout.Presentation hM w zero cut cutMul e a0 b0 d0 node0 factor0 terminal0 target0 L0 C0 projection0 I0 act0 E0 W0 unit0 G0 K0 P0 O0 ∧
    TerminalTable w cut cutMul node0 a0 terminal0 ∧ Conservative cut W0 cutMul G0 O0 ∧
    LeftCancelMonoid W0 G0 unit0 ∧ Generated cut w W0 G0 unit0 O0 P0 ∧
    Hom W0 W G0 G unit0 unit H ∧ Conservative W0 W G0 G H ∧
    EndpointLaws inc H O0 O P0 P ∧ IsPushout D W0 W mul G0 G e unit0 unit O0 inc H O

/-- Source exists_preimage -> c.simulation f -> c.pushout f, Probe branch.
Reuse the fixed target's terminal table and old conservativity. -/
theorem probe (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero cut cutMul e D mul a b d node factor terminal target L C projection I act E W unit G K P O inc : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hmCut : LeftCancelMonoid cut cutMul e) (hcCut : Conical cut cutMul e)
    (hJCut : ConditionalJoins cut cutMul)
    (hA : ConstructionProbePushout.Presentation hM w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
    (hTerminal : TerminalTable w D mul node a terminal) (hOld : Conservative D W mul G O)
    (hbne : b ≠ e) (hdne : d ≠ e)
    (hInc : Hom cut D cutMul mul e e inc) (hCon : Conservative cut D cutMul mul inc)
    (hCovered : ConstructionCellPreimage.ProbeCovered inc a b d node) :
    ∃ a0 b0 d0 node0 factor0 terminal0 target0 L0 C0 projection0 I0 act0 E0 W0 unit0 G0 K0 P0 O0 H,
      Probe hM w zero cut cutMul e D mul a b d node W unit G O P inc
        a0 b0 d0 node0 factor0 terminal0 target0 L0 C0 projection0 I0 act0 E0 W0 unit0 G0 K0 P0 O0 H := by
  obtain ⟨a0,b0,d0,node0,ha,hb,hd,hNode,hPath,hb0,hb0ne,hd0,hd0ne⟩ :=
    ConstructionCellPreimage.probe_preimage hM hmCut hA.monoid hCon hInc hA.path hbne hdne hCovered
  obtain ⟨factor0,terminal0,target0,L0,C0,projection0,I0,act0,E0,W0,unit0,G0,K0,P0,O0,hB,hTerminal0,hOld0⟩ :=
    ConstructionMappedProbe.exists_presentation hM hw hz hzw hmCut hcCut hJCut hb0 hb0ne hd0 hd0ne hPath
  have hFactorMap := ConstructionProbeMappedPath.factor_map hB.path hInc.1 hNode hInc.2.2 hB.factors hA.factors
  have hTerminalMap := ConstructionProbeMappedPath.terminal_map hB.path hInc.1 hNode hInc.2.2 ha hTerminal0 hTerminal
  have hTable0 := ConstructionProbePath.table_laws hM hw hz hmCut hB.path hB.factors hTerminal0
  have hMeets0 := ConstructionProbeTransitions.meets_laws hM hw hmCut hB.path hB.factors hTable0
  have hTable := ConstructionProbePath.table_laws hM hw hz hA.monoid hA.path hA.factors hTerminal
  have hMeets := ConstructionProbeTransitions.meets_laws hM hw hA.monoid hA.path hA.factors hTable
  obtain ⟨letters,hLetters,_,hAlphabet⟩ := ConstructionProbeAlphabetMap.exists_alphabet_simulation hM
    hmCut hA.monoid hB.path hA.path hB.factors hA.factors hCon.1 hInc.2.2 hCon.2.1 hFactorMap
    hB.representatives hB.letters hB.projection_map hB.projection_law hB.equality
    hA.representatives hA.projection_map hA.equality hMeets0 hMeets hB.action hA.action
    hB.terminals_map hTerminalMap hB.target_law hA.target_law hB.exit_law hA.exit_law hd
  obtain ⟨H,_,hH,hConH,hEnd,hPush⟩ := ConstructionProbePushout.exists_pushout hB hA hw hz hzw
    hCon hInc.2.2 hAlphabet hb hInc.2.1 hd hFactorMap hTerminalMap hJCut hOld0 hOld hLetters
  have hm0 := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hmCut hB.alphabet hB.word hB.b_mem hB.old_unit hB.multiplication
  exact ⟨a0,b0,d0,node0,factor0,terminal0,target0,L0,C0,projection0,I0,act0,E0,W0,unit0,G0,K0,P0,O0,H,
    ha,hb,hd,hNode,hB,hTerminal0,hOld0,hm0,ConstructionCellGeneration.probe_generated hM hB hw hz hzw,
    hH,hConH,hEnd,hPush⟩

/-- Complete preimage Merger and literal map of its WHOLE prescription back
to the fixed original graph, together with actual conservative pushout. -/
def Merger (w n zero cut cutMul e D mul P W G unit O roots inc
    P0 C0 L0 projection0 A0 W0 T0 B0 G0 unit0 O0 roots0 H : M.Carrier .set) : Prop :=
  ConstructionRequestCarrier.WellFormed n cut P0 ∧ ConstructionMergerRelations.Valid n cut cutMul P0 ∧
    ConstructionMergerPrescriptionMap.Graph P0 inc P ∧
    ConstructionMergerPushout.Presentation w n zero cut cutMul e P0 C0 L0 projection0 A0 W0 T0 B0 G0 unit0 O0 roots0 ∧
    LeftCancelMonoid W0 G0 unit0 ∧ Conical W0 G0 unit0 ∧ Generated cut n W0 G0 unit0 O0 roots0 ∧
    Hom W0 W G0 G unit0 unit H ∧ Conservative W0 W G0 G H ∧
    SquareComm O0 inc H O ∧ NodeMap roots0 H roots ∧ IsPushout D W0 W mul G0 G e unit0 unit O0 inc H O

theorem merger (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero cut cutMul e D mul P C L projection A W T B G unit O roots inc : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hmCut : LeftCancelMonoid cut cutMul e) (hcCut : Conical cut cutMul e)
    (hJCut : ConditionalJoins cut cutMul)
    (hA : ConstructionMergerPushout.Presentation w n zero D mul e P C L projection A W T B G unit O roots)
    (hWell : ConstructionRequestCarrier.WellFormed n D P) (hValid : ConstructionMergerRelations.Valid n D mul P)
    (hInc : Hom cut D cutMul mul e e inc) (hCon : Conservative cut D cutMul mul inc)
    (hCovered : ConstructionCellPreimage.MergerCovered P inc) :
    ∃ P0 C0 L0 projection0 A0 W0 T0 B0 G0 unit0 O0 roots0 H,
      Merger w n zero cut cutMul e D mul P W G unit O roots inc P0 C0 L0 projection0 A0 W0 T0 B0 G0 unit0 O0 roots0 H := by
  obtain ⟨P0,hWell0,hP0,hValid0,hGraph⟩ := ConstructionCellPreimage.merger_preimage hM
    hmCut hA.monoid hCon hInc hWell hA.prescription hValid hCovered
  obtain ⟨C0,L0,projection0,A0,W0,T0,B0,G0,unit0,O0,roots0,hB,hm0,hc0⟩ :=
    ConstructionMappedMerger.exists_conical_presentation hM hw hz hzw hmCut hcCut hP0 hValid0
  have hMap := ConstructionMergerPrescriptionMap.mapped hM hGraph
  obtain ⟨H,hH,hRoots,_,hPush⟩ := ConstructionMergerPushout.exists_pushout hM hB hA hw hz hzw hInc hMap
  have hConH := ConstructionMergerWordTransport.simulation_conservative hB hA hM hw hz hzw
    hCon hInc.2.2 hInc.2.1 hMap hJCut hH hPush.1 hRoots
  exact ⟨P0,C0,L0,projection0,A0,W0,T0,B0,G0,unit0,O0,roots0,H,
    hWell0,hValid0,hGraph,hB,hm0,hc0,ConstructionCellGeneration.merger_generated hM hB hw hz hzw,
    hH,hConH,hPush.1,hRoots,hPush⟩

def probeData {m : Nat} (w zero cut cutMul e D mul a b d node W unit G O P inc a0 b0 d0 node0 factor0 terminal0 target0 L0 C0 projection0 I0 act0 E0 W0 unit0 G0 K0 P0 O0 H : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge inc a0 a)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge inc b0 b)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge inc d0 d)) (.conj (ConstructionProbeMappedPathSyntax.nodeMap node0 inc node) (.conj (ConstructionProbePushoutSyntax.presentation w zero cut cutMul e a0 b0 d0 node0 factor0 terminal0 target0 L0 C0 projection0 I0 act0 E0 W0 unit0 G0 K0 P0 O0) (.conj (ConstructionProbePath.terminalTable w cut cutMul node0 a0 terminal0) (.conj (ConstructionProbeConservativeSyntax.conservative cut W0 cutMul G0 O0) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid W0 G0 unit0)) (.conj (ConstructionCellGeneration.generated cut w W0 G0 unit0 O0 P0) (.conj (ConstructionProbePushoutSyntax.hom W0 W G0 G unit0 unit H) (.conj (ConstructionProbeConservativeSyntax.conservative W0 W G0 G H) (.conj (ConstructionProbeSimulation.endpointLaws inc H O0 O P0 P) (ConstructionProbePushoutSyntax.isPushout D W0 W mul G0 G e unit0 unit O0 inc H O)))))))))))))

theorem probeData_freeClosed {m : Nat} (w zero cut cutMul e D mul a b d node W unit G O P inc a0 b0 d0 node0 factor0 terminal0 target0 L0 C0 projection0 I0 act0 E0 W0 unit0 G0 K0 P0 O0 H : Fin m) : (probeData w zero cut cutMul e D mul a b d node W unit G O P inc a0 b0 d0 node0 factor0 terminal0 target0 L0 C0 projection0 I0 act0 E0 W0 unit0 G0 K0 P0 O0 H).FreeClosed := by
  simp -implicitDefEqProofs [probeData,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionProbePushoutSyntax.presentation_freeClosed,ConstructionProbePath.terminalTable_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionCellGeneration.generated_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeSimulation.endpointLaws_freeClosed,ConstructionProbePushoutSyntax.isPushout_freeClosed]

theorem probeData_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero cut cutMul e D mul a b d node W unit G O P inc a0 b0 d0 node0 factor0 terminal0 target0 L0 C0 projection0 I0 act0 E0 W0 unit0 G0 K0 P0 O0 H : Fin m) :
    Project.Formula.satisfies env (probeData w zero cut cutMul e D mul a b d node W unit G O P inc a0 b0 d0 node0 factor0 terminal0 target0 L0 C0 projection0 I0 act0 E0 W0 unit0 G0 K0 P0 O0 H) ↔ Probe hM (env.bound w) (env.bound zero) (env.bound cut) (env.bound cutMul) (env.bound e) (env.bound D) (env.bound mul) (env.bound a) (env.bound b) (env.bound d) (env.bound node) (env.bound W) (env.bound unit) (env.bound G) (env.bound O) (env.bound P) (env.bound inc) (env.bound a0) (env.bound b0) (env.bound d0) (env.bound node0) (env.bound factor0) (env.bound terminal0) (env.bound target0) (env.bound L0) (env.bound C0) (env.bound projection0) (env.bound I0) (env.bound act0) (env.bound E0) (env.bound W0) (env.bound unit0) (env.bound G0) (env.bound K0) (env.bound P0) (env.bound O0) (env.bound H) := by
  simp only [probeData,Probe,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionProbePushoutSyntax.presentation_semantics hM,ConstructionProbePath.terminalTable_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionCellGeneration.generated_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeSimulation.endpointLaws_semantics hM,ConstructionProbePushoutSyntax.isPushout_semantics hM]
  rfl

def mergerData {m : Nat} (w n zero cut cutMul e D mul P W G unit O roots inc P0 C0 L0 projection0 A0 W0 T0 B0 G0 unit0 O0 roots0 H : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionRequestCarrier.wellFormed n cut P0) (.conj (ConstructionMergerRelations.valid n cut cutMul P0) (.conj (ConstructionMergerPrescriptionMapSyntax.graph P0 inc P) (.conj (ConstructionMergerPushout.presentation w n zero cut cutMul e P0 C0 L0 projection0 A0 W0 T0 B0 G0 unit0 O0 roots0) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid W0 G0 unit0)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical W0 G0 unit0)) (.conj (ConstructionCellGeneration.generated cut n W0 G0 unit0 O0 roots0) (.conj (ConstructionProbePushoutSyntax.hom W0 W G0 G unit0 unit H) (.conj (ConstructionProbeConservativeSyntax.conservative W0 W G0 G H) (.conj (ConstructionProbePushoutSyntax.squareComm O0 inc H O) (.conj (ConstructionProbeMappedPathSyntax.nodeMap roots0 H roots) (ConstructionProbePushoutSyntax.isPushout D W0 W mul G0 G e unit0 unit O0 inc H O))))))))))))

theorem mergerData_freeClosed {m : Nat} (w n zero cut cutMul e D mul P W G unit O roots inc P0 C0 L0 projection0 A0 W0 T0 B0 G0 unit0 O0 roots0 H : Fin m) : (mergerData w n zero cut cutMul e D mul P W G unit O roots inc P0 C0 L0 projection0 A0 W0 T0 B0 G0 unit0 O0 roots0 H).FreeClosed := by
  simp -implicitDefEqProofs [mergerData,Definitional.Formula.FreeClosed,ConstructionRequestCarrier.wellFormed_freeClosed,ConstructionMergerRelations.valid_freeClosed,ConstructionMergerPrescriptionMapSyntax.graph_freeClosed,ConstructionMergerPushout.presentation_freeClosed,ProjectSyntax.freeClosed,ConstructionCellGeneration.generated_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbePushoutSyntax.squareComm_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionProbePushoutSyntax.isPushout_freeClosed]

theorem mergerData_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w n zero cut cutMul e D mul P W G unit O roots inc P0 C0 L0 projection0 A0 W0 T0 B0 G0 unit0 O0 roots0 H : Fin m) :
    Project.Formula.satisfies env (mergerData w n zero cut cutMul e D mul P W G unit O roots inc P0 C0 L0 projection0 A0 W0 T0 B0 G0 unit0 O0 roots0 H) ↔ Merger (env.bound w) (env.bound n) (env.bound zero) (env.bound cut) (env.bound cutMul) (env.bound e) (env.bound D) (env.bound mul) (env.bound P) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound roots) (env.bound inc) (env.bound P0) (env.bound C0) (env.bound L0) (env.bound projection0) (env.bound A0) (env.bound W0) (env.bound T0) (env.bound B0) (env.bound G0) (env.bound unit0) (env.bound O0) (env.bound roots0) (env.bound H) := by
  simp only [mergerData,Merger,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionRequestCarrier.wellFormed_semantics hM,ConstructionMergerRelations.valid_semantics hM,ConstructionMergerPrescriptionMapSyntax.graph_semantics hM,ConstructionMergerPushout.presentation_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionCellGeneration.generated_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionProbePushoutSyntax.squareComm_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionProbePushoutSyntax.isPushout_semantics hM]
  rfl

def probeSentence {m : Nat} (w zero cut cutMul e D mul a b d node factor terminal target L C projection I act E W unit G K P O inc : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid cut cutMul e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical cut cutMul e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins cut cutMul) (.imp (ConstructionProbePushoutSyntax.presentation w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O) (.imp (ConstructionProbePath.terminalTable w D mul node a terminal) (.imp (ConstructionProbeConservativeSyntax.conservative D W mul G O) (.imp (.neg (Project.Formula.extensionalEq (.bound b) (.bound e))) (.imp (.neg (Project.Formula.extensionalEq (.bound d) (.bound e))) (.imp (ConstructionProbePushoutSyntax.hom cut D cutMul mul e e inc) (.imp (ConstructionProbeConservativeSyntax.conservative cut D cutMul mul inc) (.imp (ConstructionCellPreimage.probeCovered inc a b d node) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (probeData w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ cut.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ cutMul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ d.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ node.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ P.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ inc.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0)))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionProbePushoutSyntax.presentation_freeClosed,ConstructionProbePath.terminalTable_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,Project.Formula.extensionalEq,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionCellPreimage.probeCovered_freeClosed,probeData_freeClosed]

theorem probe_models {m : Nat} (w zero cut cutMul e D mul a b d node factor terminal target L C projection I act E W unit G K P O inc : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (probeSentence w zero cut cutMul e D mul a b d node factor terminal target L C projection I act E W unit G K P O inc)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (probeSentence w zero cut cutMul e D mul a b d node factor terminal target L C projection I act E W unit G K P O inc)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionProbePushoutSyntax.presentation_semantics hM,ConstructionProbePath.terminalTable_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Formula.satisfies_neg_iff,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionCellPreimage.probeCovered_semantics hM,probeData_semantics hM]
  exact probe hM

theorem probe_kernel_certificate {m : Nat} (w zero cut cutMul e D mul a b d node factor terminal target L C projection I act E W unit G K P O inc : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (probeSentence w zero cut cutMul e D mul a b d node factor terminal target L C projection I act E W unit G K P O inc)) :=
  ModelTransfer.derives (fun _ hM => probe_models w zero cut cutMul e D mul a b d node factor terminal target L C projection I act E W unit G K P O inc hM)

def mergerSentence {m : Nat} (w n zero cut cutMul e D mul P C L projection A W T B G unit O roots inc : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid cut cutMul e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical cut cutMul e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins cut cutMul) (.imp (ConstructionMergerPushout.presentation w n zero D mul e P C L projection A W T B G unit O roots) (.imp (ConstructionRequestCarrier.wellFormed n D P) (.imp (ConstructionMergerRelations.valid n D mul P) (.imp (ConstructionProbePushoutSyntax.hom cut D cutMul mul e e inc) (.imp (ConstructionProbeConservativeSyntax.conservative cut D cutMul mul inc) (.imp (ConstructionCellPreimage.mergerCovered P inc) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (mergerData w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ cut.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ cutMul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ P.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ roots.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ inc.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 11 10 9 8 7 6 5 4 3 2 1 0))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionMergerPushout.presentation_freeClosed,ConstructionRequestCarrier.wellFormed_freeClosed,ConstructionMergerRelations.valid_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionCellPreimage.mergerCovered_freeClosed,mergerData_freeClosed]

theorem merger_models {m : Nat} (w n zero cut cutMul e D mul P C L projection A W T B G unit O roots inc : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (mergerSentence w n zero cut cutMul e D mul P C L projection A W T B G unit O roots inc)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (mergerSentence w n zero cut cutMul e D mul P C L projection A W T B G unit O roots inc)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionMergerPushout.presentation_semantics hM,ConstructionRequestCarrier.wellFormed_semantics hM,ConstructionMergerRelations.valid_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionCellPreimage.mergerCovered_semantics hM,mergerData_semantics hM]
  exact merger hM

theorem merger_kernel_certificate {m : Nat} (w n zero cut cutMul e D mul P C L projection A W T B G unit O roots inc : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (mergerSentence w n zero cut cutMul e D mul P C L projection A W T B G unit O roots inc)) :=
  ModelTransfer.derives (fun _ hM => merger_models w n zero cut cutMul e D mul P C L projection A W T B G unit O roots inc hM)

end PPAC.Migration.ConstructionRestrictedCellSimulation
