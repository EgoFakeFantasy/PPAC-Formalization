/- Pinned BlockTowers.Saturation.blockMap/blockStage/top: consume the SAME
saved inner trace and outer terminal row. The last incoming family already
contains every inner-to-last map. Reuse validity, composite graphs and ranges;
no new recursion or terminal carrier is chosen. -/
import PPAC.Migration.ConstructionBlockTraces
import PPAC.Migration.ConstructionBlockStages

namespace PPAC.Migration.ConstructionActualBlocks
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Chart Charts)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerTransitions (Before Order Matrix)
open ConstructionDirectedWeightData (WeightFamily Stable)
open ConstructionRoundSelection (Pack)
open ForcingConditionGraphs (FunctionOn function_unique function_input)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingSupportedNames (Range)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- All internal indices, including the last one; no externally finite list. -/
theorem before_last (hM : FirstOrder.Theory.Models M nativeZF)
    {J last i : M.Carrier .set}
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf J last)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J) : Before i last := by
  rcases (hs i).mp hi with h | h
  · exact Or.inl h
  · exact Or.inr ((ModelTransfer.extensionality hM).eq_of_same_members i last h)

/-- Extract the actual terminal cocone from the saved incoming field. -/
theorem terminal_family (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C J history zero P F E
      Domains Muls Units Marks Heights Costs Incoming Origins Times
      last W G unitW markW HW CW L baseW : M.Carrier .set}
    (hv : Valid hM w Q R top D mul e mark H C J history)
    (hc : Charts J history Domains Muls Units Marks Heights Costs Incoming Origins Times)
    (he : Order J E) (hf : Matrix J history zero P F)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf J last)
    (hr : Row history last W G unitW markW HW CW L baseW last) :
    WeightFamily J Domains W L ∧ Stable J E Domains F L := by
  have hl := hs.predecessor_mem
  obtain ⟨_,_,_,next,identity,hnext,hfn,_,_⟩ :=
    hv.2.1 last hl W G unitW markW HW CW L baseW hr
  have en : next = J := (ModelTransfer.extensionality hM).eq_of_same_members next J
    (fun x => (hnext x).trans (hs x).symm)
  subst next
  refine ⟨⟨hfn,?_⟩,?_⟩
  · intro i Di f hi hDi hif
    obtain ⟨Ni,mi,ei,ai,Hi,Ci,Ki,fi,ri,d_i,_⟩ :=
      ConstructionTowerValidity.stage_at hM hv hc hi
    have ed := function_unique hc.1.1 d_i hDi
    subst Ni
    have hm := hv.2.2.1 i last Di mi ei ai Hi Ci Ki fi W G unitW markW HW CW L baseW f
      hi hl (before_last hM hs hi) ri hr hif
    exact hm.1.1.1.1
  · intro i j x y z fi fj hij hxy hfi hfj hxz
    obtain ⟨hi,hj,hbefore⟩ := (he.2 i j).mp hij
    obtain ⟨Nj,mj,ej,aj,Hj,Cj,Kj,bj,rj⟩ := hv.1.2 j hj
    obtain ⟨t,ht,hxt⟩ := hxy.2.2
    have htK := (ConstructionTowerTransitions.matrix_at hv.1 hf hi hj hbefore (row_field 6 rj)).mp ht
    have hcomp := hv.2.2.2.1 i j last Kj L t fj fi hi hj hl hbefore
      (before_last hM hs hj) (row_field 6 rj) (row_field 6 hr) htK hfj hfi
    obtain ⟨y',hxy',hyz⟩ := (hcomp x z).mp hxz
    obtain ⟨Ni,mi,ei,ai,Hi,Ci,Ki,bi,ri⟩ := hv.1.2 i hi
    have htMap := hv.2.2.1 i j Ni mi ei ai Hi Ci Ki bi Nj mj ej aj Hj Cj Kj bj t
      hi hj hbefore ri rj htK
    have ey := function_unique htMap.1.1.1.1.1 hxy' hxt
    exact ey ▸ hyz

/-- Saved trace fields plus actual block maps and exact ranges in V. -/
def Data (code W after V J Domains E F L Out Images : M.Carrier .set) : Prop :=
  ∃ Schedule last history Steps Events Roots,
    Pack J Schedule last history F Steps Events Roots L code ∧
    Chart 0 J history Domains ∧ Order J E ∧
    WeightFamily J Domains W L ∧ Stable J E Domains F L ∧
    ConstructionBlockStages.Result J E Domains F L after V Out Images ∧
    PureKuratowski.PairMember M last after Out ∧
    ∀ A, PureKuratowski.PairMember M last A Images → Range W after A

/-- Source blockMap and blockStage for one actual retained complete round.
The input is Trace, not assumed final-leg/stability/range witnesses. -/
theorem trace_block (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V : M.Carrier .set}
    (ht : ConstructionBlockTraces.Trace hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code)
    (ha : MapsTo W V after) :
    ∃ J Domains E F L Out Images, Data code W after V J Domains E F L Out Images := by
  obtain ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J,collapse,inverse,Schedule,Place,last,
    history,P,F,Steps,Events,Roots,L,hpack,hctx,hschedule,_,hrec,hF,_,_,_,hrow,_⟩ := ht
  have hv := ConstructionTowerIterationValidity.recursive_valid hM hctx hrec (fun _ h => h)
  have hctxCopy := hctx
  obtain ⟨_,_,_,_,_,_,_,_,_,hJ,_,_⟩ := hctxCopy
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hl,_,_,hends,_⟩ := hschedule
  have hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf J last := by
    intro x
    constructor
    · intro hx
      rcases (hends x).mp hx with h | h
      · exact Or.inl h
      · subst x
        exact Or.inr (fun _ => Iff.rfl)
    · rintro (h | h)
      · exact (hends x).mpr (Or.inl h)
      · exact (hends x).mpr (Or.inr ((ModelTransfer.extensionality hM).eq_of_same_members x last h))
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,hcharts,_⟩ :=
    ConstructionTowerHistory.exists_charts hM hv.1
  obtain ⟨E,hE⟩ := ConstructionTowerTransitions.exists_order hM J
  have hd := ConstructionTowerDiagram.data_of_valid hM hJ hv hcharts hE hF
  obtain ⟨hL,hstable⟩ := terminal_family hM hv hcharts hE hF hs hrow
  obtain ⟨Out,Images,hresult⟩ := ConstructionBlockStages.exists_block hM hcharts.1.1 hL hstable hd.2.1 ha
  obtain ⟨_,_,_,next,identity,_,_,hidentity,hid⟩ := hv.2.1 last hl W G unitW markW HW CW L O hrow
  obtain ⟨out,hout,_⟩ := hresult.2.1.1.2 last hl
  have eo := ConstructionTowerSuccessor.successor_equation hM hcharts.1.1 hresult.2.1
    hresult.2.2.1 ha last identity out hl hidentity hid hout
  subst out
  refine ⟨J,Domains,E,F,L,Out,Images,Schedule,last,history,Steps,Events,Roots,
    hpack,hcharts.1,hE,hL,hstable,hresult,hout,?_⟩
  intro A hA
  exact ConstructionBlockStages.range_at hcharts.1.1 hresult.2.1.1 hresult.2.2.2.2.1
    (ConstructionTowerHistory.chart_of_row 0 hcharts.1 hl hrow) hout hA

/-- The afterRound leg is read from the SAME actual outer terminal row.
No extra map into the final carrier is supplied by the caller. -/
theorem at_block (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV i code : M.Carrier .set}
    (hv : Valid hM w Q R top D mul e mark H C B history)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.At hM w Q R top zero one K mu history outerF i code) :
    ∃ j W after J Domains E F L Out Images,
      (Project.FirstOrderSemantics.reduct M).SuccessorOf j i ∧ Product outerF j kappa after ∧
      Data code W after V J Domains E F L Out Images := by
  obtain ⟨j,raw,Requests,N,mulN,eN,markN,HN,CN,L0,f,W,G,unitW,markW,HW,CW,NewOut,baseW,O,
    hsucc,_,hrj,_,_,_,_,_,htrace⟩ := ht
  have hj : (Project.FirstOrderSemantics.reduct M).mem j B := by
    obtain ⟨raw,hraw,_⟩ := hrj
    exact function_input hv.1.1 hraw
  have hk := hs.predecessor_mem
  have hjk := before_last hM hs hj
  obtain ⟨next,hn,hfn⟩ := ConstructionTowerValidity.incoming_rows hM hv kappa terminalLegs hk (row_field 6 hr)
  have hjn : (Project.FirstOrderSemantics.reduct M).mem j next := by
    apply (hn j).mpr
    rcases hjk with h | h
    · exact Or.inl h
    · subst j
      exact Or.inr (fun _ => Iff.rfl)
  obtain ⟨after,hafter,_⟩ := hfn.2 j hjn
  have hm := hv.2.2.1 j kappa W G unitW markW HW CW NewOut baseW
    V mulV unitV markV HV CV terminalLegs baseV after hj hk hjk hrj hr hafter
  obtain ⟨J,Domains,E,F,L,Out,Images,hd⟩ := trace_block hM htrace hm.1.1.1.1
  exact ⟨j,W,after,J,Domains,E,F,L,Out,Images,hsucc,
    (ConstructionTowerTransitions.matrix_at hv.1 hf hj hk hjk (row_field 6 hr)).mpr hafter,hd⟩

/-- Every selected outer trace is interpreted in the identical final V. -/
theorem family_blocks (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces : M.Carrier .set}
    (hv : Valid hM w Q R top D mul e mark H C B history)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q R top zero one K mu history outerF kappa traces) :
    ∀ i code, PureKuratowski.PairMember M i code traces →
      ∃ j W after J Domains E F L Out Images,
        (Project.FirstOrderSemantics.reduct M).SuccessorOf j i ∧ Product outerF j kappa after ∧
        Data code W after V J Domains E F L Out Images := by
  intro i code hcode
  exact at_block hM hv hs hf hr ((ht.2 i code).mp hcode).2.1

def data {m : Nat} (code W after V J Domains E F L Out Images : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRoundSelection.pack
  J.succ.succ.succ.succ.succ.succ 5 4 3 F.succ.succ.succ.succ.succ.succ 2 1 0 L.succ.succ.succ.succ.succ.succ
  code.succ.succ.succ.succ.succ.succ) (.conj (ConstructionTowerHistory.chart 0 J.succ.succ.succ.succ.succ.succ
  3 Domains.succ.succ.succ.succ.succ.succ) (.conj (ConstructionTowerTransitions.order
  J.succ.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionDirectedWeightData.weightFamily J.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ L.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionDirectedWeightData.stable J.succ.succ.succ.succ.succ.succ
  E.succ.succ.succ.succ.succ.succ Domains.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ
  L.succ.succ.succ.succ.succ.succ) (.conj (ConstructionBlockStages.result J.succ.succ.succ.succ.succ.succ
  E.succ.succ.succ.succ.succ.succ Domains.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ
  L.succ.succ.succ.succ.succ.succ after.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ
  Out.succ.succ.succ.succ.succ.succ Images.succ.succ.succ.succ.succ.succ) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge Out.succ.succ.succ.succ.succ.succ 4 after.succ.succ.succ.succ.succ.succ)) (.forallE
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Images.succ.succ.succ.succ.succ.succ.succ 5 0))
  (ProjectSyntax.encode id (ForcingSupportedNames.range W.succ.succ.succ.succ.succ.succ.succ
  after.succ.succ.succ.succ.succ.succ.succ 0)))))))))))))))))

theorem data_freeClosed {m : Nat} (code W after V J Domains E F L Out Images : Fin m) :
    (data code W after V J Domains E F L Out Images).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionTowerHistory.chart_freeClosed,ConstructionTowerTransitions.order_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,ConstructionBlockStages.result_freeClosed,ProjectSyntax.freeClosed]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (code W after V J Domains E F L Out Images : Fin m) :
    Project.Formula.satisfies env (data code W after V J Domains E F L Out Images) ↔ Data (env.bound code) (env.bound W) (env.bound after) (env.bound V) (env.bound J) (env.bound Domains) (env.bound E) (env.bound F) (env.bound L) (env.bound Out) (env.bound Images) := by
  simp only [data,Data,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,ConstructionRoundSelection.pack_semantics hM,ConstructionTowerHistory.chart_semantics hM,ConstructionTowerTransitions.order_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ConstructionBlockStages.result_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportedNames.range_semantics (M := M)]
  rfl

def traceConstructionSentence {m : Nat} (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionBlockTraces.trace w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW
    CW O code) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo after W V)) (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (data code.succ.succ.succ.succ.succ.succ.succ
    W.succ.succ.succ.succ.succ.succ.succ after.succ.succ.succ.succ.succ.succ.succ
    V.succ.succ.succ.succ.succ.succ.succ 6 5 4 3 2 1 0))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionBlockTraces.trace_freeClosed,ProjectSyntax.freeClosed,data_freeClosed]

theorem traceConstruction_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V : Fin m) : (Project.fo_sentence (traceConstructionSentence w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (traceConstructionSentence w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,ConstructionBlockTraces.trace_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),data_semantics hM]
  exact trace_block hM

theorem traceConstruction_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (traceConstructionSentence w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V)) := by
  apply ModelTransfer.derives
  intro M hM
  exact traceConstruction_models hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V

def familyConstructionSentence {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionTowerValidity.valid w Q R top D mul e mark H C B history) (.imp
    (Project.Formula.isSuccessor (.bound B) (.bound kappa)) (.imp (ConstructionTowerTransitions.matrix B
    history zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V mulV unitV markV HV CV
    terminalLegs baseV kappa) (.imp (ConstructionBlockTraces.family w Q R top zero one K mu history outerF
    kappa traces) (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge traces.succ.succ
    1 0)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (Project.Formula.isSuccessor (.bound 9) (.bound 11)) (.conj (ProjectSyntax.encode id
    (ForcingDiagramOrder.product outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7)) (data 10 8 7
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 4 3 2 1 0)))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerValidity.valid_freeClosed,Project.Formula.isSuccessor,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ProjectSyntax.freeClosed,data_freeClosed]

theorem familyConstruction_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces : Fin m) : (Project.fo_sentence (familyConstructionSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (familyConstructionSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,ConstructionTowerValidity.valid_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),data_semantics hM]
  exact family_blocks hM

theorem familyConstruction_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (familyConstructionSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces)) := by
  apply ModelTransfer.derives
  intro M hM
  exact familyConstruction_models hM w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces

end PPAC.Migration.ConstructionActualBlocks
