/- Pinned BlockTowers.Cell.rangeAttachment, Probe branch. Keep the actual
source word/product/old graph/generator. Consume its retained terminal and cone
tables, construct only the mapped target, and reuse existing simulationEquiv. -/
import PPAC.Migration.ConstructionRangeObject
import PPAC.Migration.ConstructionExecutedCellPresentation

namespace PPAC.Migration.ConstructionMappedProbe
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePushout (Presentation Hom SquareComm)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionProbePath (Path TerminalTable)
open ConstructionProbeCones (ConeLaws)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportedNames (Range)
open ForcingConditionGraphs (InverseGraph)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Expose the SAME retained witnesses as ExecutedCellPresentation.probe,
also keeping the original TerminalTable/ConeLaws needed by the actual map. -/
theorem source_presentation (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero mark a b node W G unit O gen : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hm : LeftCancelMonoid D mul e)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D) (hO : MapsTo D W O)
    (hSource : ConstructionOperationSource.Probe hM w D mul e zero mark a b node W G unit O gen) :
    ∃ factor terminal target S C projection I act E K P,
      Presentation hM w zero D mul e a b mark node factor terminal target S C projection I act E W unit G K P O ∧
      PureKuratowski.PairMember M zero gen P ∧ TerminalTable w D mul node a terminal ∧
      ConeLaws w D mul e zero node factor S projection act := by
  obtain ⟨hPath,hb,_,S,act,E,projection,K,P,hAlphaSource,hWord,hUnit,hG,hOld,hK,hGen,hP,hProbe,hgen⟩ := hSource
  obtain ⟨I,target,factor,terminal,C,hAlpha,hCone,hTargetMap,hFactor,hTerminalMap,hTerminal,hTargetLaws,hExit,hC,hProjectionMap,hLetters,hProjection,hAction⟩ := hAlphaSource
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
      hPath,hFactor,hP,hProbe,hTerminalMap,hTarget,hExit,hmark,hOld,hO⟩,hgen,hTerminal,hCone⟩

/-- Package the existing alphabet, word, old embedding and indexed generators.
All algebra laws and conservation come from their accepted producers. -/
theorem exists_presentation (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul e a b d node : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hJ : ConditionalJoins D mul)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hbne : b ≠ e)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hdne : d ≠ e)
    (hPath : Path w D mul e zero a node) :
    ∃ factor terminal target S C projection I act E W unit G K P O,
      Presentation hM w zero D mul e a b d node factor terminal target S C projection I act E W unit G K P O ∧
      TerminalTable w D mul node a terminal ∧ Conservative D W mul G O ∧
      ∃ pairs, ConstructionProbeLetters.Representatives W W pairs ∧ MapsTo pairs W G := by
  obtain ⟨pairs,hpairs⟩ := ConstructionProbePath.exists_ordered_pairs hM w
  obtain ⟨factor,_,hFactor⟩ := ConstructionProbePath.exists_factor_table hM hm hPath hpairs
  obtain ⟨terminal,hTerminalMap,hTerminal⟩ := ConstructionProbePath.exists_terminal_table hM hm hPath
  have hTable := ConstructionProbePath.table_laws hM hw hz hm hPath hFactor hTerminal
  have hMeets := ConstructionProbeTransitions.meets_laws hM hw hm hPath hFactor hTable
  obtain ⟨C,hC⟩ := ConstructionProbeLetters.exists_representatives hM w D
  obtain ⟨S,hS⟩ := ConstructionProbeLetters.exists_letters hM w D mul factor C
  obtain ⟨projection,hp,hProjection⟩ := ConstructionProbeLetters.exists_projection hM hS
  have hEq := ConstructionProbeLetters.equality_law hM hC hMeets hProjection
  obtain ⟨I,act,hI,hActMap,hAction⟩ := ConstructionProbeAction.exists_action hM hm hFactor hC hS hp hProjection hEq
  have hAct := ConstructionProbeAction.action_laws hM hm hFactor hC hS hp hProjection hEq hAction
  obtain ⟨target,hTargetMap,hTarget⟩ := ConstructionProbeTarget.exists_target hM hm hFactor hC hS hp hProjection hEq hTerminalMap hTable
  have hTargetLaws := ConstructionProbeTarget.target_laws hm hFactor hC hp hEq hTerminalMap hTable hAction hTarget
  obtain ⟨E,hEMap,hExit⟩ := ConstructionProbeAlphabet.exists_exit hM hm hTargetMap hd
  have hAlpha := ConstructionProbeAlphabet.alphabet_laws hm hc hI hActMap hAct hTargetMap hTargetLaws hd hdne hEMap hExit
  have hCone := ConstructionProbeCones.cone_laws hM hm hPath hFactor hTable hC hS hp hProjection hEq hMeets hI hActMap hAction hAct hTargetMap hTargetLaws
  obtain ⟨W,unit,J,G,hW,hUnit,hPairs,hMapG,hG,_,_,_⟩ := ConstructionProbeConditionalJoins.exists_extension hM hw hz hzw hm hc hAlpha hb hbne hCone hJ
  obtain ⟨O,hOld,_,hConO⟩ := ConstructionProbeConservative.exists_conservative_old hM hw hz hzw hm hAlpha hW hb hG hUnit hCone
  obtain ⟨K,hK,hGen⟩ := ConstructionProbeGenerator.exists_generator_graph hM hw hz hzw hc hW hb hbne hUnit
  obtain ⟨P,hP,hProbe⟩ := ConstructionProbeIndexedGenerators.exists_probe_graph hM hC hp hm.1.1 hK
  exact ⟨factor,terminal,target,S,C,projection,I,act,E,W,unit,G,K,P,O,
    ⟨hm,hAlpha,hW,hb,hUnit,hG,hK,hGen,hC,hS,hp,hProjection,hEq,hAction,hPath,hFactor,
      hP,hProbe,hTerminalMap,hTarget,hExit,hd,hOld,hConO.1.1⟩,hTerminal,hConO,J,hPairs,hMapG⟩

/-- Mapped source parameters, full target presentation and actual simulation
identified with the SAME terminal range. The raw distinguished generator is
transported explicitly, as are all old elements. -/
def Data (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero a b d node W unit G O gen N mulN eN f V GV unitV g R
      fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON genN H inv embedding : M.Carrier .set) : Prop :=
  PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f ∧
    PureKuratowski.PairMember M d fd f ∧ NodeMap node f mapped ∧
    Presentation hM w zero N mulN eN fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON ∧
    TerminalTable w N mulN mapped fa terminalN ∧ Conservative N WN mulN GN ON ∧
    PureKuratowski.PairMember M zero genN PN ∧ Hom W WN G GN unit unitN H ∧
    Conservative W WN G GN H ∧ SquareComm O f H ON ∧ PureKuratowski.PairMember M gen genN H ∧
    Range W H WN ∧ Hom WN W GN G unitN unit inv ∧ InverseGraph H inv ∧
    Hom WN V GN GV unitN unitV embedding ∧ Injection WN V embedding ∧
    NodeMap inv g embedding ∧ ConstructionAttachmentCoefficients.OldFixed ON embedding ∧ Range WN embedding R ∧ fb ≠ eN ∧ fd ≠ eN

/-- Pinned d.map e, conservative simulation, simulationEquiv and literal range
identification. Original Source/old graph/raw gen are never regenerated. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul e a b d node W unit G O gen V GV unitV f g N R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hJ : ConditionalJoins D mul)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hdne : d ≠ e)
    (hO : MapsTo D W O)
    (hSource : ConstructionOperationSource.Probe hM w D mul e zero d a b node W G unit O gen)
    (hv : LeftCancelMonoid V GV unitV) (hc : Conical V GV unitV) (hJV : ConditionalJoins V GV)
    (hf : Hom D V mul GV e unitV f) (hCons : Conservative D V mul GV f) (hRange : Range D f N)
    (hg : Hom W V G GV unit unitV g) (hInj : Injection W V g)
    (hOld : NodeMap O g f) (hTerminalRange : Range W g R) :
    ∃ basePairs mulN inc baseInv fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON genN H inv embedding,
      ConstructionRangeObject.Data w zero D V mul GV e unitV f N basePairs mulN inc baseInv ∧
      Data hM w zero a b d node W unit G O gen N mulN unitV f V GV unitV g R
        fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON genN H inv embedding := by
  have hbne := hSource.2.2.1
  obtain ⟨factor,terminal,target,S,C,projection,I,act,E,K,P,hA,hgen,hTerminal,hCone⟩ :=
    source_presentation hM hw hz hm hd hO hSource
  obtain ⟨basePairs,mulN,inc,baseInv,hBase⟩ := ConstructionRangeObject.construction hM hm hJ hv hc hJV hf hCons hRange
  have hKeep := hBase
  obtain ⟨_,_,_,_,hmN,hcN,hJN,_,_,_,hfN,hConsN,_,_,_,_,_⟩ := hBase
  obtain ⟨fa,fb,mapped,hfa,hfb,hfbN,hfbne,_,hMapped,hPathN,_⟩ :=
    ConstructionRequestMaps.probe_map hM hConsN hfN.2.2 hfN.2.1 hA.b_mem hbne hA.path
  obtain ⟨fd,hfd,_⟩ := hfN.1.1.2 d hd
  have hfdne : fd ≠ unitV := fun heq => hdne (hConsN.1.2 d e unitV (heq ▸ hfd) hfN.2.1)
  obtain ⟨factorN,terminalN,targetN,SN,CN,projectionN,IN,actN,EN,WN,unitN,GN,KN,PN,ON,hB,hTerminalN,hConON,_⟩ :=
    exists_presentation hM hw hz hzw hmN hcN hJN hfbN hfbne (hfN.1.2 d fd hfd) hfdne hPathN
  have hFactorMap := ConstructionProbeMappedPath.factor_map hA.path hfN.1 hMapped hfN.2.2 hA.factors hB.factors
  have hTerminalMap := ConstructionProbeMappedPath.terminal_map hA.path hfN.1 hMapped hfN.2.2 hfa hTerminal hTerminalN
  have hTable := ConstructionProbePath.table_laws hM hw hz hm hA.path hA.factors hTerminal
  have hMeets := ConstructionProbeTransitions.meets_laws hM hw hm hA.path hA.factors hTable
  have hTableN := ConstructionProbePath.table_laws hM hw hz hmN hB.path hB.factors hTerminalN
  have hMeetsN := ConstructionProbeTransitions.meets_laws hM hw hmN hB.path hB.factors hTableN
  obtain ⟨letters,hLetters,_,hAlphabet⟩ := ConstructionProbeAlphabetMap.exists_alphabet_simulation hM
    hm hmN hA.path hB.path hA.factors hB.factors hConsN.1 hfN.2.2 hConsN.2.1 hFactorMap
    hA.representatives hA.letters hA.projection_map hA.projection_law hA.equality
    hB.representatives hB.projection_map hB.equality hMeets hMeetsN hA.action hB.action
    hA.terminals_map hTerminalMap hA.target_law hB.target_law hA.exit_law hB.exit_law hfd
  have hOInj : Injection D W O := ⟨hO,fun x y q hx hy =>
    ConstructionProbeRaw.old_injective ((hA.old_graph x q).mp hx) ((hA.old_graph y q).mp hy)⟩
  have hEmb := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hm hA.alphabet hA.word hA.b_mem hA.old_unit hA.multiplication hA.old_graph
  have hConO := ConstructionProbeConservative.old_conservative hM hw hz hzw hCone hA.word hA.old_graph hOInj hEmb
  obtain ⟨H,_,hH,hConH,hEnd,hPush⟩ := ConstructionProbePushout.exists_pushout hA hB hw hz hzw
    hConsN hfN.2.2 hAlphabet hfb hfN.2.1 hfd hFactorMap hTerminalMap hJ hConO hConON hLetters
  obtain ⟨hOnto,inv,hInv,hInverse⟩ := ConstructionCellSimulationEquiv.probe_equiv hM hw hz hzw hA hB hH hConH.1 hRange hEnd
  obtain ⟨genN,hgenN,_⟩ := hB.probes_map.1.2 zero hzw
  have hGenMap := hEnd.2 zero gen genN hgen hgenN
  obtain ⟨embedding,hEmbedding,hEmbeddingInj,hComp,hFixed,hExact⟩ :=
    ConstructionCellSimulationEquiv.range_identification hM hO hB.old_map hH hInv hInverse
      hg hInj hRange hOld hPush.1 hTerminalRange
  exact ⟨basePairs,mulN,inc,baseInv,fa,fb,fd,mapped,factorN,terminalN,targetN,SN,CN,projectionN,IN,actN,EN,WN,unitN,GN,KN,PN,ON,genN,H,inv,embedding,hKeep,
    hfa,hfb,hfd,hMapped,hB,hTerminalN,hConON,hgenN,hH,hConH,hPush.1,hGenMap,hOnto,hInv,hInverse,hEmbedding,hEmbeddingInj,hComp,hFixed,hExact,hfbne,hfdne⟩

def data {m : Nat} (w zero a b d node W unit G O gen N mulN eN f V GV unitV g R fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON genN H inv embedding : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.edge f a fa))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f b fb))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f d fd))
    (.conj (ConstructionProbeMappedPathSyntax.nodeMap node f mapped)
    (.conj (ConstructionProbePushoutSyntax.presentation w zero N mulN eN fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON)
    (.conj (ConstructionProbePath.terminalTable w N mulN mapped fa terminalN)
    (.conj (ConstructionProbeConservativeSyntax.conservative N WN mulN GN ON)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge PN zero genN))
    (.conj (ConstructionProbePushoutSyntax.hom W WN G GN unit unitN H)
    (.conj (ConstructionProbeConservativeSyntax.conservative W WN G GN H)
    (.conj (ConstructionProbePushoutSyntax.squareComm O f H ON)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge H gen genN))
    (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range W H WN))
    (.conj (ConstructionProbePushoutSyntax.hom WN W GN G unitN unit inv)
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph H inv))
    (.conj (ConstructionProbePushoutSyntax.hom WN V GN GV unitN unitV embedding)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection embedding WN V))
    (.conj (ConstructionProbeMappedPathSyntax.nodeMap inv g embedding)
    (.conj (ConstructionAttachmentCoefficients.oldFixed ON embedding)
    (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range WN embedding R)) (.conj (.neg (Project.Formula.extensionalEq (.bound fb) (.bound eN))) (.neg (Project.Formula.extensionalEq (.bound fd) (.bound eN)))))))))))))))))))))))

theorem data_freeClosed {m : Nat} (w zero a b d node W unit G O gen N mulN eN f V GV unitV g R fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON genN H inv embedding : Fin m) :
    (data w zero a b d node W unit G O gen N mulN eN f V GV unitV g R fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON genN H inv embedding).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,
    ProjectSyntax.freeClosed,
    ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
    ConstructionProbePushoutSyntax.presentation_freeClosed,
    ConstructionProbePath.terminalTable_freeClosed,
    ConstructionProbeConservativeSyntax.conservative_freeClosed,
    ConstructionProbePushoutSyntax.hom_freeClosed,
    ConstructionProbePushoutSyntax.squareComm_freeClosed,
    ConstructionAttachmentCoefficients.oldFixed_freeClosed]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero a b d node W unit G O gen N mulN eN f V GV unitV g R fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON genN H inv embedding : Fin m) :
    Project.Formula.satisfies env (data w zero a b d node W unit G O gen N mulN eN f V GV unitV g R fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON genN H inv embedding) ↔
      Data hM (env.bound w) (env.bound zero) (env.bound a) (env.bound b) (env.bound d) (env.bound node) (env.bound W) (env.bound unit) (env.bound G) (env.bound O) (env.bound gen) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound f) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound g) (env.bound R) (env.bound fa) (env.bound fb) (env.bound fd) (env.bound mapped) (env.bound factorN) (env.bound terminalN) (env.bound targetN) (env.bound SN) (env.bound CN) (env.bound projectionN) (env.bound IN) (env.bound actN) (env.bound EN) (env.bound WN) (env.bound unitN) (env.bound GN) (env.bound KN) (env.bound PN) (env.bound ON) (env.bound genN) (env.bound H) (env.bound inv) (env.bound embedding) := by
  simp only [data,Data,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    ConstructionProbePushoutSyntax.presentation_semantics hM,
    ConstructionProbePath.terminalTable_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbePushoutSyntax.squareComm_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),
    ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),
    ConstructionAttachmentCoefficients.oldFixed_semantics hM]
  rfl

/-- Actual retained Probe source to its mapped presentation and exact range;
all twenty-seven newly constructed sets and graphs are object existentials. -/
def constructionSentence {m : Nat} (w zero D mul e a b d node W unit G O gen V GV unitV f g N R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isEmpty (.bound zero))
    (.imp (.mem (.bound zero) (.bound w))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul)
    (.imp (.mem (.bound d) (.bound D))
    (.imp (.neg (Project.Formula.extensionalEq (.bound d) (.bound e)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo O D W))
    (.imp (ConstructionOperationSource.probe w D mul e zero d a b node W G unit O gen)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV unitV))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV unitV))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV)
    (.imp (ConstructionProbePushoutSyntax.hom D V mul GV e unitV f)
    (.imp (ConstructionProbeConservativeSyntax.conservative D V mul GV f)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D f N))
    (.imp (ConstructionProbePushoutSyntax.hom W V G GV unit unitV g)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection g W V))
    (.imp (ConstructionProbeMappedPathSyntax.nodeMap O g f)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range W g R))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRangeObject.data w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 26 25 24 23)
      (data w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ d.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ node.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ gen.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 25 unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ g.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInductive,Project.Formula.isSuccessor,Project.Formula.isEmpty,
      Project.Formula.extensionalEq,data_freeClosed,ConstructionRangeObject.data_freeClosed,
      ConstructionOperationSource.probe_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem construction_models {m : Nat} (w zero D mul e a b d node W unit G O gen V GV unitV f g N R : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w zero D mul e a b d node W unit G O gen V GV unitV f g N R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w zero D mul e a b d node W unit G O gen V GV unitV f g N R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionOperationSource.probe_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionRangeObject.data_semantics hM,data_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w zero D mul e a b d node W unit G O gen V GV unitV f g N R : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w zero D mul e a b d node W unit G O gen V GV unitV f g N R)) :=
  ModelTransfer.derives (fun _ hM => construction_models w zero D mul e a b d node W unit G O gen V GV unitV f g N R hM)

end PPAC.Migration.ConstructionMappedProbe
