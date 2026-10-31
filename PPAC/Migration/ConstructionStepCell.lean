/- Pinned CellTowers.stepCell/coefficients/dependencies.
Encode the COMPLETE actual presentation, its terminal embedding and the
existing parameter/support/dependency graphs in ONE internal record. -/
import PPAC.Migration.ConstructionFlatAttachments

namespace PPAC.Migration.ConstructionStepCell
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRoundSelection (Pack)
open ConstructionProbePushout (Hom)
open ConstructionAttachmentCoefficients (OldFixed)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (Injection)
open ForcingSupportedNames (Range)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Keep the multiplication typing already supplied by the actual range
producer. This witness is not a new premise on the original attachment. -/
def TypedProduct (D mul : M.Carrier .set) : Prop :=
  ∃ pairs, ConstructionProbeLetters.Representatives D D pairs ∧ ForcingSupportSize.MapsTo pairs D mul

def typedProduct {m : Nat} (D mul : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ConstructionProbeLetters.representatives D.succ D.succ 0)
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo mul.succ 0 D.succ)))

theorem typedProduct_freeClosed {m : Nat} (D mul : Fin m) : (typedProduct D mul).FreeClosed := by
  simp -implicitDefEqProofs [typedProduct,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeLetters.representatives_freeClosed]

theorem typedProduct_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul : Fin m) :
    Project.Formula.satisfies env (typedProduct D mul) ↔ TypedProduct (env.bound D) (env.bound mul) := by
  simp only [typedProduct,TypedProduct,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

def Probe (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero V GV unitV D R cell : M.Carrier .set) : Prop :=
  ∃ mul a b d node factor terminal target L C projection I act E W unit G K P O F
      p0 p1 presentation parameters old generators supports deps,
    Pack mul a b d node factor terminal target L p0 ∧
    Pack C projection I act E W unit G K p1 ∧
    Pack P O F p0 p1 zero zero zero zero presentation ∧
    LeftCancelMonoid D mul unitV ∧ Conical D mul unitV ∧ ConditionalJoins D mul ∧
    ConstructionProbePushout.Presentation hM w zero D mul unitV a b d node factor terminal target L C projection I act E W unit G K P O ∧
    Hom W V G GV unit unitV F ∧ Injection W V F ∧ OldFixed O F ∧ Range W F R ∧
    ConstructionCellParameters.ProbeParameters a b d node parameters ∧
    ConstructionCellParameters.Result w D w W V GV unitV O P F R parameters old generators supports deps ∧
    Pack zero presentation parameters old generators supports deps zero zero cell ∧ b ≠ unitV ∧ d ≠ unitV ∧
    ConstructionProbePath.TerminalTable w D mul node a terminal ∧
    ConstructionProbeConservative.Conservative D W mul G O ∧
    ConstructionConservativeHull.Closure V GV unitV D ∧ ConstructionConservativeHull.ProductGraph D GV mul ∧ TypedProduct D mul

def Merger (w zero one V GV unitV D R cell : M.Carrier .set) : Prop :=
  ∃ mul n P C L projection A W T B G unit O roots F p0 presentation parameters old generators supports deps,
    Pack mul n P C L projection A W T p0 ∧
    Pack B G unit O roots F p0 zero zero presentation ∧
    (Project.FirstOrderSemantics.reduct M).mem n w ∧
    LeftCancelMonoid D mul unitV ∧ Conical D mul unitV ∧ ConditionalJoins D mul ∧
    ConstructionMergerRelations.Valid n D mul P ∧
    ConstructionMergerPushout.Presentation w n zero D mul unitV P C L projection A W T B G unit O roots ∧
    Hom W V G GV unit unitV F ∧ Injection W V F ∧ OldFixed O F ∧ Range W F R ∧
    ConstructionCellParameters.MergerParameters P parameters ∧
    ConstructionCellParameters.Result w D n W V GV unitV O roots F R parameters old generators supports deps ∧
    Pack one presentation parameters old generators supports deps zero zero cell ∧ LeftCancelMonoid W G unit ∧ Conical W G unit ∧
    ConstructionConservativeHull.Closure V GV unitV D ∧ ConstructionConservativeHull.ProductGraph D GV mul ∧ ConstructionRequestCarrier.WellFormed n D P ∧ TypedProduct D mul

def Data (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero one V GV unitV D R cell : M.Carrier .set) : Prop :=
  Probe hM w zero V GV unitV D R cell ∨ Merger w zero one V GV unitV D R cell

def DependencyField (zero cell deps : M.Carrier .set) : Prop :=
  ∃ tag presentation parameters old generators supports,
    Pack tag presentation parameters old generators supports deps zero zero cell

theorem dependencyField_unique {zero cell deps other : M.Carrier .set}
    (h : DependencyField zero cell deps) (h' : DependencyField zero cell other) : deps = other := by
  obtain ⟨_,_,_,_,_,_,hp⟩ := h
  obtain ⟨_,_,_,_,_,_,hp'⟩ := h'
  exact (ConstructionRoundSelection.pack_injective hp hp').2.2.2.2.2.2.1

/-- Reading the fixed code gives the SAME support and dependency graphs
for every queried word; the whole complete cell remains in its payload. -/
theorem dependencies (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV unitV D R cell : M.Carrier .set}
    (h : Data hM w zero one V GV unitV D R cell) :
    ∃ deps, DependencyField zero cell deps ∧ ConstructionCountableConservativeHull.Dependencies w R deps := by
  rcases h with h | h
  · obtain ⟨mul,a,b,d,node,factor,terminal,target,L,C,projection,I,act,E,W,unit,G,K,P,O,F,
      p0,p1,presentation,parameters,old,generators,supports,deps,
      _,_,_,_,_,_,_,_,_,_,_,_,hResult,hPack,_,_,_,_,_,_⟩ := h
    exact ⟨deps,⟨zero,presentation,parameters,old,generators,supports,hPack⟩,hResult.2.2.2.2.2.2⟩
  · obtain ⟨mul,n,P,C,L,projection,A,W,T,B,G,unit,O,roots,F,p0,presentation,parameters,old,generators,supports,deps,
      _,_,_,_,_,_,_,_,_,_,_,_,_,hResult,hPack,_,_,_,_,_⟩ := h
    exact ⟨deps,⟨one,presentation,parameters,old,generators,supports,hPack⟩,hResult.2.2.2.2.2.2⟩

/-- Use the retained mapped presentation and actual embedding. The
Merger internal finite index is recovered from the ORIGINAL Request. -/
theorem from_attached (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w zero one D0 mul0 e0 request N mulN eN markN f W G unit O roots V GV unitV leg nextLeg S R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hne : zero ≠ one)
    (hRequest : ConstructionRequestSchedule.Request w D0 mul0 e0 zero one request)
    (h : ConstructionSelectedAttachments.Attached hM w zero one request N mulN eN markN f W G unit O roots V GV unitV leg nextLeg S R) :
    ∃ cell, Data hM w zero one V GV unitV S R cell := by
  rcases h with ⟨a,b,node,fa,fb,mapped,_,_,_,_,h⟩ | ⟨n,P,PN,hCode,_,h⟩
  · obtain ⟨basePairs,mulS,inc,baseInv,aa,bb,dd,nn,factor,terminal,target,L,C,projection,I,act,E,WW,uu,GG,K,PP,OO,gen,H,inv,F,hBase,hMapped⟩ := h
    obtain ⟨hBaseClosed,hBasePairs,hBaseMap,hBaseProduct,hm,hc,hJ,_⟩ := hBase
    obtain ⟨_,_,_,_,hA,hTerminal,hCons,_,_,_,_,_,_,_,_,hF,hInj,_,hFixed,hRange,hbne,hdne⟩ := hMapped
    obtain ⟨parameters,old,generators,supports,deps,hParams,hResult⟩ :=
      ConstructionCellParameters.actual_probe hM hOrder hw hz hzw hA hF hFixed hRange
    obtain ⟨p0,h0⟩ := ConstructionRoundSelection.pack_exists hM mulS aa bb dd nn factor terminal target L
    obtain ⟨p1,h1⟩ := ConstructionRoundSelection.pack_exists hM C projection I act E WW uu GG K
    obtain ⟨presentation,hp⟩ := ConstructionRoundSelection.pack_exists hM PP OO F p0 p1 zero zero zero zero
    obtain ⟨cell,hcell⟩ := ConstructionRoundSelection.pack_exists hM zero presentation parameters old generators supports deps zero zero
    exact ⟨cell,Or.inl ⟨mulS,aa,bb,dd,nn,factor,terminal,target,L,C,projection,I,act,E,WW,uu,GG,K,PP,OO,F,
      p0,p1,presentation,parameters,old,generators,supports,deps,h0,h1,hp,hm,hc,hJ,hA,hF,hInj,hFixed,hRange,hParams,hResult,hcell,hbne,hdne,hTerminal,hCons,hBaseClosed,hBaseProduct,basePairs,hBasePairs,hBaseMap⟩⟩
  · have hn : (Project.FirstOrderSemantics.reduct M).mem n w := by
      rcases hRequest with ⟨a,b,node,hProbe,_⟩ | ⟨n',P',hCode',hn,_⟩
      · exact (ConstructionRequestSchedule.code_disjoint hne hProbe hCode).elim
      · have en := (ConstructionRequestSchedule.merger_code_injective hCode hCode').1
        exact en ▸ hn
    obtain ⟨basePairs,mulS,inc,baseInv,PP,C,L,projection,A,WW,T,B,GG,uu,OO,rr,H,inv,F,hBase,hMapped⟩ := h
    obtain ⟨hBaseClosed,hBasePairs,hBaseMap,hBaseProduct,hm,hc,hJ,_⟩ := hBase
    obtain ⟨hGraph,hValid,hA,hmW,hcW,_,_,_,_,_,_,_,hF,hInj,_,hFixed,hRange⟩ := hMapped
    obtain ⟨parameters,old,generators,supports,deps,hParams,hResult⟩ :=
      ConstructionCellParameters.actual_merger hM hOrder hw hn hz hzw hA hF hFixed hRange
    obtain ⟨p0,h0⟩ := ConstructionRoundSelection.pack_exists hM mulS n PP C L projection A WW T
    obtain ⟨presentation,hp⟩ := ConstructionRoundSelection.pack_exists hM B GG uu OO rr F p0 zero zero
    obtain ⟨cell,hcell⟩ := ConstructionRoundSelection.pack_exists hM one presentation parameters old generators supports deps zero zero
    exact ⟨cell,Or.inr ⟨mulS,n,PP,C,L,projection,A,WW,T,B,GG,uu,OO,rr,F,p0,presentation,parameters,old,generators,supports,deps,
      h0,hp,hn,hm,hc,hJ,hValid,hA,hF,hInj,hFixed,hRange,hParams,hResult,hcell,hmW,hcW,hBaseClosed,hBaseProduct,ConstructionRequestCarrier.wellFormed_of_graph hGraph hA.prescription,basePairs,hBasePairs,hBaseMap⟩⟩

/-- Recover Context.Requests from the same serialized complete round.
The already selected original raw and both literal ranges stay unchanged. -/
theorem from_block (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q values top zero one K mu history outerF i code V GV unitV J Out j k A0 A1 : M.Carrier .set}
    (ht : ConstructionBlockTraces.At hM w Q values top zero one K mu history outerF i code)
    (ha : ConstructionBlockAttachments.At hM w Q values top zero one code V GV unitV J Out j k A0 A1) :
    ∃ cell, Data hM w zero one V GV unitV A0 A1 cell := by
  obtain ⟨D,mul,e,mark,H,C,Schedule,last,inner,F,EventsSet,Events,Roots,L,raw,hpack,hSelected⟩ := ha
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hTrace⟩ := ht
  obtain ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J',collapse,inverse,Schedule',Place,last',
    inner',P,F',EventsSet',Events',Roots',L',hpack',hctx,_⟩ := hTrace
  obtain ⟨eJ,eS,el,eh,eF,eSteps,eEvents,eRoots,eL⟩ := ConstructionRoundSelection.pack_injective hpack hpack'
  subst J' Schedule' last' inner' F' EventsSet' Events' Roots' L'
  obtain ⟨hw,_,_,_,hone,_,_,hz,hzw,_,_,hRequests⟩ := hctx
  obtain ⟨request,N,mulN,eN,markN,HN,CN,KK,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,leg,nextLeg,
    hReq,_,_,_,_,_,_,_,_,_,_,_,_,hAttached⟩ := hSelected
  exact from_attached hM hOrder hw hz hzw (ConstructionRequestSchedule.zero_ne_one hz hone) (hRequests j request hReq) hAttached

theorem from_step (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q values top zero one K mu history outerF kappa traces V GV unitV A0 A1 : M.Carrier .set}
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (h : ConstructionFlatAttachments.Step hM w Q values top zero one traces V GV unitV A0 A1)
    (hne : A0 ≠ A1) : ∃ cell, Data hM w zero one V GV unitV A0 A1 cell := by
  rcases h with he | ⟨i,code,J,Out,j,k,hcode,ha⟩
  · exact (hne he).elim
  · exact from_block hM hOrder ((ht.2 i code).mp hcode).2.1 ha

def probe {m : Nat} (w zero V GV unitV D R cell : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRoundSelection.pack 28
  27 26 25 24 23 22 21 20 7) (.conj (ConstructionRoundSelection.pack 19 18 17 16 15 14 13 12 11 6) (.conj
  (ConstructionRoundSelection.pack 10 9 8 7 6
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  5) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  28
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  28
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ConstructionProbeSharedIntersections.conditionalJoins
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  28) (.conj (ConstructionProbePushoutSyntax.presentation
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  28
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9) (.conj (ConstructionProbePushoutSyntax.hom 14
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  12
  GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  13
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  8) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 8 14
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ConstructionAttachmentCoefficients.oldFixed 9 8) (.conj (ProjectSyntax.encode id
  (ForcingSupportedNames.range 14 8
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ConstructionCellParameters.probeParameters 27 26 25 24 4) (.conj (ConstructionCellParameters.result
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  14
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  9 10 8
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  4 3 2 1 0) (.conj (ConstructionRoundSelection.pack
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  5 4 3 2 1 0
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  cell.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (.neg (Project.Formula.extensionalEq (.bound 26) (.bound unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))) (.conj (.neg (Project.Formula.extensionalEq (.bound 25) (.bound unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))) (.conj (ConstructionProbePath.terminalTable w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 28 24 27 22) (.conj (ConstructionProbeConservativeSyntax.conservative D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 14 28 12 9) (.conj (ConstructionConservativeHull.closure V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (ConstructionConservativeHull.productGraph D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 28) (typedProduct D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 28))))))))))))))))))))))))))))))))))))))))))))))))))

theorem probe_freeClosed {m : Nat} (w zero V GV unitV D R cell : Fin m) :
    (probe w zero V GV unitV D R cell).FreeClosed := by
  simp -implicitDefEqProofs [probe,Definitional.Formula.FreeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionConservativeHull.productGraph_freeClosed,Project.Formula.extensionalEq,ConstructionProbePath.terminalTable_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ProjectSyntax.freeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionProbePushoutSyntax.presentation_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionAttachmentCoefficients.oldFixed_freeClosed,ConstructionCellParameters.probeParameters_freeClosed,ConstructionCellParameters.result_freeClosed,typedProduct_freeClosed]

theorem probe_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero V GV unitV D R cell : Fin m) :
    Project.Formula.satisfies env (probe w zero V GV unitV D R cell) ↔ Probe hM (env.bound w) (env.bound zero) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound D) (env.bound R) (env.bound cell) := by
  simp only [probe,Probe,ConstructionConservativeHull.closure_semantics hM,ConstructionConservativeHull.productGraph_semantics hM,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionProbePath.terminalTable_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),ConstructionRoundSelection.pack_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionProbePushoutSyntax.presentation_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionAttachmentCoefficients.oldFixed_semantics hM,ConstructionCellParameters.probeParameters_semantics hM,ConstructionCellParameters.result_semantics hM,typedProduct_semantics hM]
  rfl

def merger {m : Nat} (w zero one V GV unitV D R cell : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.conj (ConstructionRoundSelection.pack 21 20 19 18 17 16 15 14 13 6) (.conj (ConstructionRoundSelection.pack 12
  11 10 9 8 7 6
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  5) (.conj (.mem (.bound 20) (.bound
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  21
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  21
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ConstructionProbeSharedIntersections.conditionalJoins
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  21) (.conj (ConstructionMergerRelations.valid 20
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  21 19) (.conj (ConstructionMergerPushout.presentation
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  20
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  21
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  19 18 17 16 15 14 13 12 11 10 9 8) (.conj (ConstructionProbePushoutSyntax.hom 14
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  11
  GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  10
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  7) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 7 14
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ConstructionAttachmentCoefficients.oldFixed 9 7) (.conj (ProjectSyntax.encode id
  (ForcingSupportedNames.range 14 7
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ConstructionCellParameters.mergerParameters 19 4) (.conj (ConstructionCellParameters.result
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  20 14
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  9 8 7
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 4
  3 2 1 0) (.conj (ConstructionRoundSelection.pack
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  5 4 3 2 1 0
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  cell.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid 14 11 10)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical 14 11 10)) (.conj (ConstructionConservativeHull.closure V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (ConstructionConservativeHull.productGraph D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 21) (.conj (ConstructionRequestCarrier.wellFormed 20 D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 19) (typedProduct D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 21)))))))))))))))))))))))))))))))))))))))))))

theorem merger_freeClosed {m : Nat} (w zero one V GV unitV D R cell : Fin m) :
    (merger w zero one V GV unitV D R cell).FreeClosed := by
  simp -implicitDefEqProofs [merger,Definitional.Formula.FreeClosed,ConstructionRequestCarrier.wellFormed_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionConservativeHull.productGraph_freeClosed,ProjectSyntax.freeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionMergerRelations.valid_freeClosed,ConstructionMergerPushout.presentation_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionAttachmentCoefficients.oldFixed_freeClosed,ConstructionCellParameters.mergerParameters_freeClosed,ConstructionCellParameters.result_freeClosed,typedProduct_freeClosed]

theorem merger_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero one V GV unitV D R cell : Fin m) :
    Project.Formula.satisfies env (merger w zero one V GV unitV D R cell) ↔ Merger (env.bound w) (env.bound zero) (env.bound one) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound D) (env.bound R) (env.bound cell) := by
  simp only [merger,Merger,ConstructionRequestCarrier.wellFormed_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionConservativeHull.productGraph_semantics hM,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),ConstructionRoundSelection.pack_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionMergerRelations.valid_semantics hM,ConstructionMergerPushout.presentation_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionAttachmentCoefficients.oldFixed_semantics hM,ConstructionCellParameters.mergerParameters_semantics hM,ConstructionCellParameters.result_semantics hM,typedProduct_semantics hM]
  rfl

def data {m : Nat} (w zero one V GV unitV D R cell : Fin m) : Project.Formula 1 m :=
  (.disj (probe w zero V GV unitV D R cell) (merger w zero one V GV unitV D R cell))

theorem data_freeClosed {m : Nat} (w zero one V GV unitV D R cell : Fin m) :
    (data w zero one V GV unitV D R cell).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,probe_freeClosed,merger_freeClosed]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero one V GV unitV D R cell : Fin m) :
    Project.Formula.satisfies env (data w zero one V GV unitV D R cell) ↔ Data hM (env.bound w) (env.bound zero) (env.bound one) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound D) (env.bound R) (env.bound cell) := by
  simp only [data,Data,Project.Formula.satisfies_disj_iff,probe_semantics hM,merger_semantics hM]

def dependencyField {m : Nat} (zero cell deps : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (ConstructionRoundSelection.pack 5 4 3 2 1 0
  deps.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ
  cell.succ.succ.succ.succ.succ.succ)))))))

theorem dependencyField_freeClosed {m : Nat} (zero cell deps : Fin m) :
    (dependencyField zero cell deps).FreeClosed := by
  simp -implicitDefEqProofs [dependencyField,Definitional.Formula.FreeClosed,ConstructionRoundSelection.pack_freeClosed]

theorem dependencyField_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero cell deps : Fin m) :
    Project.Formula.satisfies env (dependencyField zero cell deps) ↔ DependencyField (env.bound zero) (env.bound cell) (env.bound deps) := by
  simp only [dependencyField,DependencyField,Project.Formula.satisfies_exists_iff,ConstructionRoundSelection.pack_semantics hM]
  rfl

def dependenciesSentence {m : Nat} (w zero one V GV unitV D R cell : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (data w zero one V GV unitV D R cell) (.existsE (.conj (dependencyField zero.succ cell.succ 0) (ConstructionCountableConservativeHull.dependencies w.succ R.succ 0))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,data_freeClosed,dependencyField_freeClosed,ConstructionCountableConservativeHull.dependencies_freeClosed]

theorem dependencies_models {m : Nat} (w zero one V GV unitV D R cell : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (dependenciesSentence w zero one V GV unitV D R cell)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (dependenciesSentence w zero one V GV unitV D R cell)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,data_semantics hM,dependencyField_semantics hM,ConstructionCountableConservativeHull.dependencies_semantics hM]
  exact dependencies hM

theorem dependencies_kernel_certificate {m : Nat} (w zero one V GV unitV D R cell : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (dependenciesSentence w zero one V GV unitV D R cell)) :=
  ModelTransfer.derives (fun _ hM => dependencies_models w zero one V GV unitV D R cell hM)

def constructionSentence {m : Nat} (w Q values top zero one K mu history outerF kappa traces V GV unitV A0 A1 : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionBlockTraces.family w Q values top zero one K mu history outerF kappa traces) (.imp (ConstructionFlatAttachments.step w Q values top zero one traces V GV unitV A0 A1) (.imp (.neg (Project.Formula.extensionalEq (.bound A0) (.bound A1))) (.existsE (data w.succ zero.succ one.succ V.succ GV.succ unitV.succ A0.succ A1.succ 0)))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionFlatAttachments.step_freeClosed,Project.Formula.extensionalEq,data_freeClosed]

theorem construction_models {m : Nat} (w Q values top zero one K mu history outerF kappa traces V GV unitV A0 A1 : Fin m) (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence (constructionSentence w Q values top zero one K mu history outerF kappa traces V GV unitV A0 A1)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w Q values top zero one K mu history outerF kappa traces V GV unitV A0 A1)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,ConstructionBlockTraces.family_semantics hM,ConstructionFlatAttachments.step_semantics hM,data_semantics hM]
  exact from_step hM hOrder

theorem construction_kernel_certificate {m : Nat} (w Q values top zero one K mu history outerF kappa traces V GV unitV A0 A1 : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w Q values top zero one K mu history outerF kappa traces V GV unitV A0 A1))) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM (constructionSentence w Q values top zero one K mu history outerF kappa traces V GV unitV A0 A1)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) (constructionSentence w Q values top zero one K mu history outerF kappa traces V GV unitV A0 A1)).mp
    (construction_models w Q values top zero one K mu history outerF kappa traces V GV unitV A0 A1 (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

end PPAC.Migration.ConstructionStepCell
