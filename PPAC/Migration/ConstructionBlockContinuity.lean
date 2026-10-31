/- Pinned BlockTowers.blockStage_limit / outerStage_limit / blocks limits.
Read actual recursive limit rows. Inner adaptation follows the already
accepted SaturationCover.exists_rep projection path; outer uses it directly.
Reuse native membership relation and ranges_earlier for exact range continuity. -/
import PPAC.Migration.ConstructionBlockBoundary

namespace PPAC.Migration.ConstructionBlockContinuity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Field Chart Charts)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerTransitions (Order Matrix)
open ConstructionSaturationCover (Representative)
open ConstructionDirectedWeightData (WeightFamily Stable)
open ConstructionBlockStages (Ranges Prior Earlier)
open ConstructionFirstAppearance (At)
open ForcingConditionGraphs (function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem inner_exists_rep (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u B Schedule history P F kappa N m v a W V incoming base x : M.Carrier .set}
    (hCtx : ConstructionTowerIterationCases.Context hM w Q R top D mul e mark H C zero one u B Schedule)
    (hRec : ConstructionTowerIteration.Recursive hM w Q R top D mul e mark H C zero one B Schedule B history)
    (hF : ConstructionTowerTransitions.Matrix B history zero P F)
    (hLimit : (Project.FirstOrderSemantics.reduct M).IsLimitOrdinal kappa)
    (hk : (Project.FirstOrderSemantics.reduct M).mem kappa B)
    (hRow : Row history kappa N m v a W V incoming base kappa)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x N) :
    Representative history F kappa x := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let rawM := Project.FirstOrderSemantics.reduct M
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,hz,_,hB,_,_⟩ := hCtxCopy
  have hValid := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  obtain ⟨code,hCode,hTargetPack⟩ := hRow
  obtain ⟨prior,hRestrict,hOp⟩ := hRec.2 kappa hk code hCode
  have hPriorRec := Structure.IsRecursiveSequence.restriction hRec hk hRestrict
  have hPrior := ConstructionTowerIterationValidity.recursive_valid hM
    hCtx hPriorRec (hB.transitive kappa hk)
  have hCase := (ConstructionTowerIteration.valid_step hM hCtx
    ⟨hLimit.1,hk,hPrior⟩ hOp).1
  rcases hCase with ⟨he,_⟩ | ⟨_,prev,request,hSucc,_⟩ | ⟨_,_,hValue⟩
  · obtain ⟨q,hq⟩ := hLimit.2.1
    exact False.elim (hz q (he ▸ hq))
  · obtain ⟨larger,hl,hpl⟩ := hLimit.2.2 prev hSucc.predecessor_mem
    rcases (hSucc larger).mp hl with hlp | he
    · exact False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) prev
        ((hLimit.1.mem hSucc.predecessor_mem).transitive larger hlp prev hpl))
    · have eq := hZF.1.eq_of_same_members larger prev he
      subst larger
      exact False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) prev hpl)
  · obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P0,F0,hCharts,_,_,
      L,G,unitL,markL,HL,LC,Legs,baseL,next,identity,NewDomains,NewOut,hResult,_,hSelf,hPack⟩ := hValue
    have eqN := (ConstructionRoundSelection.pack_injective hPack hTargetPack).1
    subst N
    obtain ⟨rep,projection,Bproduct,hRep,hProjectionMap,hCarrier,hProjection,hBproduct,hG,hGraph,
      hUnit,hMark,hWeights,hObj,hCocone,hFull,hProfiles,hBase,hNatural,hBaseProfiles,hColimit,hCard,hUnique⟩ := hResult
    obtain ⟨p,hp,hpx⟩ := ConstructionDirectedLimitCarrier.projection_onto hCarrier hProjection hx
    obtain ⟨i,y,⟨hi,A,hAi,hy⟩,hCodeP⟩ := (hRep p).mp hp
    obtain ⟨leg,hLeg,_⟩ := hCocone.1.1.2 i hi
    have hyx : PureKuratowski.PairMember M y x leg :=
      (hCocone.2.2 i A leg hi hAi hLeg y x).mpr ⟨hy,p,hCodeP,hpx⟩
    obtain ⟨N0,m0,v0,a0,W0,V0,in0,b0,hSourceRow⟩ := hPrior.1.2 i hi
    have hN0 := ConstructionTowerHistory.chart_of_row 0 hCharts.1 hi hSourceRow
    have eqA := ForcingConditionGraphs.function_unique hCharts.1.1 hAi hN0
    subst A
    have hGlobalRow : Row history i N0 m0 v0 a0 W0 V0 in0 b0 i := by
      obtain ⟨c,hc,hp⟩ := hSourceRow
      exact ⟨c,((hRestrict.2 i c).mp hc).2,hp⟩
    obtain ⟨_,_,_,_,_,hNewGraph,_⟩ := hSelf
    have hNewLeg := (hNewGraph i leg).mpr (Or.inl hLeg)
    have hFinalRow : Row history kappa L G unitL markL HL LC NewOut baseL kappa :=
      ⟨code,hCode,hPack⟩
    have hGlobalLeg : ForcingDiagramOrder.Product F i kappa leg :=
      (ConstructionTowerTransitions.matrix_at hValid.1 hF (hB.transitive kappa hk i hi) hk
        (Or.inl hi) (row_field 6 hFinalRow)).mpr hNewLeg
    exact ⟨i,N0,m0,v0,a0,W0,V0,in0,b0,leg,y,hi,hGlobalRow,hGlobalLeg,hy,hyx⟩

/-- Internal limit continuity of the actual range family. -/
def Continuous (J Images : M.Carrier .set) : Prop :=
  ∀ j, (Project.FirstOrderSemantics.reduct M).mem j J →
    (Project.FirstOrderSemantics.reduct M).IsLimitOrdinal j → ∀ x, At Images j x →
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i j ∧ At Images i x

/-- The earlier-representative witness is transported by the existing
range theorem; the strict relation is a native membership instance. -/
theorem ranges_continuous (hM : FirstOrder.Theory.Models M nativeZF)
    {J history E Domains F V Legs Images : M.Carrier .set}
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hc : Chart 0 J history Domains) (he : Order J E)
    (hw : WeightFamily J Domains V Legs) (hs : Stable J E Domains F Legs)
    (hr : Ranges J Domains Legs Images)
    (hrep : ∀ j N x, (Project.FirstOrderSemantics.reduct M).mem j J →
      (Project.FirstOrderSemantics.reduct M).IsLimitOrdinal j → Field 0 history j N →
      (Project.FirstOrderSemantics.reduct M).mem x N → Representative history F j x) :
    Continuous J Images := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 := {bound := Fin.elim0,free := fun _ => J}
  obtain ⟨r,_,hrel⟩ := ZF.exists_setRelationOn_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    Project.RelationSchema.membership env J
  have hstrict (i j : M.Carrier .set) : PureKuratowski.PairMember M i j r ↔
      (Project.FirstOrderSemantics.reduct M).mem i J ∧
      (Project.FirstOrderSemantics.reduct M).mem j J ∧ (Project.FirstOrderSemantics.reduct M).mem i j := by
    simpa [Project.RelationSchema.membership,Project.BinarySchema.denote,
      Project.Formula.satisfies_mem_iff] using! hrel i j
  intro j hj hlimit x hx
  have hp : Prior J r Domains F j := by
    intro N y hNj hy
    obtain ⟨i,Ni,mi,ei,ai,Hi,Ci,Ki,fi,t,z,hij,hrow,ht,hz,hzy⟩ :=
      hrep j N y hj hlimit ((hc.2 j N).mp hNj).2 hy
    have hi := hJ.transitive j hj i hij
    have hNi := ConstructionTowerHistory.chart_of_row 0 hc hi hrow
    exact ⟨i,z,hi,(hstrict i j).mpr ⟨hi,hj,hij⟩,
      ⟨⟨hi,Ni,hNi,hz⟩,⟨hj,N,hNj,hy⟩,t,ht,hzy⟩⟩
  have hle : ∀ i k, PureKuratowski.PairMember M i k r → PureKuratowski.PairMember M i k E := by
    intro i k hik
    obtain ⟨hi,hk,hik⟩ := (hstrict i k).mp hik
    exact (he.2 i k).mpr ⟨hi,hk,Or.inl hik⟩
  obtain ⟨i,_,hij,hix⟩ := ConstructionBlockStages.ranges_earlier hc.1 hw hs hr hle hp x hx
  exact ⟨i,((hstrict i j).mp hij).2.2,hix⟩

/-- No supplied continuity: read the exact recursive trace in the block data. -/
theorem trace_continuous (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V
      J Domains E F L Out Images : M.Carrier .set}
    (ht : ConstructionBlockTraces.Trace hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code)
    (hd : ConstructionActualBlocks.Data code W after V J Domains E F L Out Images) :
    Continuous J Images := by
  obtain ⟨Schedule,last,history,Steps,Events,Roots,hpack,hchart,hE,_,_,hresult,_,_⟩ := hd
  obtain ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J',collapse,inverse,Schedule',Place,last',
    history',P,F',Steps',Events',Roots',L',hpack',hctx,_,_,hrec,hF,_,_,_,_,_⟩ := ht
  obtain ⟨eJ,eS,el,eh,eF,eSteps,eEvents,eRoots,eL⟩ := ConstructionRoundSelection.pack_injective hpack hpack'
  subst J' Schedule' last' history' F' Steps' Events' Roots' L'
  have hv := ConstructionTowerIterationValidity.recursive_valid hM hctx hrec (fun _ h => h)
  have hJ := hctx.2.2.2.2.2.2.2.2.2.1
  apply ranges_continuous hM hJ hchart hE hresult.2.1 hresult.2.2.2.1 hresult.2.2.2.2.1
  intro j N x hj hlimit hN hx
  obtain ⟨Nj,mj,ej,aj,Hj,Cj,Kj,fj,hrow⟩ := hv.1.2 j hj
  have en : Nj = N := ConstructionTowerHistory.field_unique 0 hv.1.1 (row_field 0 hrow) hN
  subst Nj
  exact inner_exists_rep hM hctx hrec hF hlimit hj hrow hx

/-- Actual outer-stage ranges of the saved terminal incoming maps. -/
def OuterData (B history F terminalLegs V Domains E Images : M.Carrier .set) : Prop :=
  Chart 0 B history Domains ∧ Order B E ∧ WeightFamily B Domains V terminalLegs ∧
    Stable B E Domains F terminalLegs ∧ Ranges B Domains terminalLegs Images ∧
    ConstructionBlockStages.Bounded V Images ∧ ConstructionBlockStages.MonotoneImages B E Images ∧
    Continuous B Images

/-- All actual outer limit stages, including the final internal limit. -/
theorem outer_continuous (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu B history P F kappa
      V mulV unitV markV HV CV terminalLegs baseV : M.Carrier .set}
    (hctx : ConstructionSaturationIterationCases.Context hM w Q R top D mul e mark H C zero one u K mu B)
    (hrec : ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history)
    (hF : Matrix B history zero P F)
    (hk : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hrow : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa) :
    ∃ Domains E Images, OuterData B history F terminalLegs V Domains E Images := by
  have hv := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice hctx hrec (fun _ h => h)).1
  have hctxCopy := hctx
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hB,_⟩ := hctxCopy
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,hcharts,_⟩ :=
    ConstructionTowerHistory.exists_charts hM hv.1
  obtain ⟨E,hE⟩ := ConstructionTowerTransitions.exists_order hM B
  have hd := ConstructionTowerDiagram.data_of_valid hM hB hv hcharts hE hF
  obtain ⟨hLegs,hStable⟩ := ConstructionActualBlocks.terminal_family hM hv hcharts hE hF hk hrow
  obtain ⟨Images,hImages⟩ := ConstructionBlockStages.exists_ranges hM hcharts.1.1 hLegs
  refine ⟨Domains,E,Images,hcharts.1,hE,hLegs,hStable,hImages,
    ConstructionBlockStages.ranges_bounded hLegs hImages,
    ConstructionBlockStages.ranges_mono hcharts.1.1 hd.2.1 hStable hImages,?_⟩
  apply ranges_continuous hM hB hcharts.1 hE hLegs hStable hImages
  intro j N x hj hlimit hN hx
  obtain ⟨Nj,mj,ej,aj,Hj,Cj,Kj,fj,hrj⟩ := hv.1.2 j hj
  have en : Nj = N := ConstructionTowerHistory.field_unique 0 hv.1.1 (row_field 0 hrj) hN
  subst Nj
  exact ConstructionSaturationCover.exists_rep hM hOrder hChoice hctx hrec hF hlimit hj hrj hx

def continuous {m : Nat} (J Images : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound J.succ)) (.imp (Project.Formula.isLimitOrdinal (.bound 0))
  (.forallE (.imp (ConstructionFirstAppearance.atStage Images.succ.succ 1 0) (.existsE (.conj (.mem (.bound 0)
  (.bound 2)) (ConstructionFirstAppearance.atStage Images.succ.succ.succ 0 1))))))))

theorem continuous_freeClosed {m : Nat} (J Images : Fin m) :
    (continuous J Images).FreeClosed := by
  simp -implicitDefEqProofs [continuous,Definitional.Formula.FreeClosed,Project.Formula.isLimitOrdinal,ConstructionFirstAppearance.atStage_freeClosed]

theorem continuous_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Images : Fin m) :
    Project.Formula.satisfies env (continuous J Images) ↔ Continuous (env.bound J) (env.bound Images) := by
  simp only [continuous,Continuous,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isLimitOrdinal_iff,ConstructionFirstAppearance.atStage_semantics hM]
  rfl

def outerData {m : Nat} (B history F terminalLegs V Domains E Images : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionTowerHistory.chart 0 B history Domains) (.conj (ConstructionTowerTransitions.order B E)
  (.conj (ConstructionDirectedWeightData.weightFamily B Domains V terminalLegs) (.conj
  (ConstructionDirectedWeightData.stable B E Domains F terminalLegs) (.conj (ConstructionBlockStages.ranges B
  Domains terminalLegs Images) (.conj (ConstructionBlockStages.bounded V Images) (.conj
  (ConstructionBlockStages.monotoneImages B E Images) (continuous B Images))))))))

theorem outerData_freeClosed {m : Nat} (B history F terminalLegs V Domains E Images : Fin m) :
    (outerData B history F terminalLegs V Domains E Images).FreeClosed := by
  simp -implicitDefEqProofs [outerData,Definitional.Formula.FreeClosed,ConstructionTowerHistory.chart_freeClosed,ConstructionTowerTransitions.order_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,ConstructionBlockStages.ranges_freeClosed,ConstructionBlockStages.bounded_freeClosed,ConstructionBlockStages.monotoneImages_freeClosed,continuous_freeClosed]

theorem outerData_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (B history F terminalLegs V Domains E Images : Fin m) :
    Project.Formula.satisfies env (outerData B history F terminalLegs V Domains E Images) ↔ OuterData (env.bound B) (env.bound history) (env.bound F) (env.bound terminalLegs) (env.bound V) (env.bound Domains) (env.bound E) (env.bound Images) := by
  simp only [outerData,OuterData,Project.Formula.satisfies_conj_iff,ConstructionTowerHistory.chart_semantics hM,ConstructionTowerTransitions.order_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ConstructionBlockStages.ranges_semantics hM,ConstructionBlockStages.bounded_semantics hM,ConstructionBlockStages.monotoneImages_semantics hM,continuous_semantics hM]

def innerSentence {m : Nat} (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionBlockTraces.trace w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW
    CW O code) (.imp (ConstructionActualBlocks.data code W after V J Domains E F L Out Images) (continuous J
    Images)))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionBlockTraces.trace_freeClosed,ConstructionActualBlocks.data_freeClosed,continuous_freeClosed]

theorem inner_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images : Fin m) : (Project.fo_sentence (innerSentence w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (innerSentence w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,ConstructionBlockTraces.trace_semantics hM,ConstructionActualBlocks.data_semantics hM,continuous_semantics hM]
  exact trace_continuous hM

theorem inner_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (innerSentence w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images)) := by
  apply ModelTransfer.derives
  intro M hM
  exact inner_models hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images

def outerSentence {m : Nat} (w Q R top D mul e mark H C zero one u K mu B history P F kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionSaturationIterationCases.context w Q R top D mul e mark H C zero one u K mu B) (.imp
    (ConstructionSaturationIteration.recursive w Q R top D mul e mark H C zero one K mu B B history) (.imp
    (ConstructionTowerTransitions.matrix B history zero P F) (.imp (Project.Formula.isSuccessor (.bound B)
    (.bound kappa)) (.imp (ConstructionTowerHistory.row history kappa V mulV unitV markV HV CV terminalLegs
    baseV kappa) (.existsE (.existsE (.existsE (outerData B.succ.succ.succ history.succ.succ.succ
    F.succ.succ.succ terminalLegs.succ.succ.succ V.succ.succ.succ 2 1 0)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,Project.Formula.isSuccessor,ConstructionTowerHistory.row_freeClosed,outerData_freeClosed]

theorem outer_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {m : Nat}
    (w Q R top D mul e mark H C zero one u K mu B history P F kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : (Project.fo_sentence (outerSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa V mulV unitV markV HV CV terminalLegs baseV)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (outerSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa V mulV unitV markV HV CV terminalLegs baseV)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,outerData_semantics hM]
  exact outer_continuous hM hOrder hChoice

theorem outer_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one u K mu B history P F kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (outerSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa V mulV unitV markV HV CV terminalLegs baseV))) := by
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
  apply ConstructibleGround.relative_models hM (outerSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa V mulV unitV markV HV CV terminalLegs baseV)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (outerSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa V mulV unitV markV HV CV terminalLegs baseV)).mp
    (outer_models hL (ConstructionRoundSelection.l_order hM) hChoice w Q R top D mul e mark H C zero one u K mu B history P F kappa V mulV unitV markV HV CV terminalLegs baseV)

end PPAC.Migration.ConstructionBlockContinuity
