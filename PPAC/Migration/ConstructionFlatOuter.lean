/- Pinned Saturation.blockStage_base / blocks.covers and the top branch
of BlockTower.flatten.continuous. Reuse actual outer range continuity at the
existing regular terminal limit. No new coverage, ordinal or L foundation. -/
import PPAC.Migration.ConstructionFlatStages

namespace PPAC.Migration.ConstructionFlatOuter
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionBlockCuts (Cut)
open ConstructionBlockBoundary (Realized)
open ConstructionFirstAppearance (At)
open ConstructionTowerHistory (Field Row)
open ForcingConditionGraphs (function_unique function_input)
open ForcingWithTopCarrier (Empty)
open ForcingSupportedNames (Range)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Read the SAME outer matrix leg in the actual outer range graph. -/
theorem outer_range (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C B history zero P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV ODomains OE OImages i N f A : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages)
    (hN : Field 0 history i N) (hp : ForcingDiagramOrder.Product outerF i kappa f)
    (hA : PureKuratowski.PairMember M i A OImages) : Range N f A := by
  have hi := ((hf.2.2 i kappa f).mp hp).1
  have hD := (ho.1.2 i N).mpr ⟨hi,hN⟩
  have hleg := (ConstructionTowerTransitions.matrix_at hv.1 hf hi hB.predecessor_mem
    (ConstructionActualBlocks.before_last hM hB hi) (ConstructionTowerValidity.row_field 6 hr)).mp hp
  exact ConstructionBlockStages.range_at ho.1.1 ho.2.2.1.1 ho.2.2.2.2.1 hD hleg hA

/-- The bottom of EVERY actual round is the literal outer-stage range. -/
theorem base_at (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C B history zero P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV ODomains OE OImages
      i code next N W fromBase after J Domains E F L Out Images x : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages)
    (hb : Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images)
    (hz : (Project.FirstOrderSemantics.reduct M).mem zero J) : At Images zero x ↔ At OImages i x := by
  have hi := ((hf.2.2 i kappa fromBase).mp hb.2.2.2.1).1
  have equal (A AO : M.Carrier .set) (hA : PureKuratowski.PairMember M zero A Images)
      (hAO : PureKuratowski.PairMember M i AO OImages) : A = AO :=
    ConstructionBlockStages.range_unique hM (hb.2.2.2.2.2.2 A hA)
      (outer_range hM hv hB hf hr ho hb.2.1 hb.2.2.2.1 hAO)
  constructor
  · rintro ⟨A,hA,hx⟩
    obtain ⟨AO,hAO,_⟩ := ho.2.2.2.2.1.1.2 i hi
    have eq := equal A AO hA hAO
    subst AO
    exact ⟨A,hAO,hx⟩
  · rintro ⟨AO,hAO,hx⟩
    obtain ⟨Schedule,last,inner,Steps,Events,Roots,_,_,_,_,_,hresult,_,_⟩ := hb.2.2.2.2.2.1
    obtain ⟨A,hA,_⟩ := hresult.2.2.2.2.1.1.2 zero hz
    have eq := equal A AO hA hAO
    subst AO
    exact ⟨A,hA,hx⟩

/-- Existing Ends and the retained pack determine the same inner ordinal. -/
theorem realized_zero (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top zero one K mu history outerF kappa traces
      V i code next N W fromBase after J Domains E F L Out Images : M.Carrier .set}
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hcode : PureKuratowski.PairMember M i code traces)
    (hb : Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images) :
    (Project.FirstOrderSemantics.reduct M).mem zero J := by
  obtain ⟨J',last',hends,_,_,_,hz⟩ := ConstructionBlockCuts.actual_ends hM ht (function_input ht.1 hcode)
  obtain ⟨Schedule',inner',F',Steps',Events',Roots',L',code',hcode',hpack'⟩ := hends
  obtain ⟨Schedule,last,inner,Steps,Events,Roots,hpack,_⟩ := hb.2.2.2.2.2.1
  have ec := function_unique ht.1 hcode' hcode
  subst code'
  have eJ := (ConstructionRoundSelection.pack_injective hpack' hpack).1
  subst J'
  exact hz

theorem realized_index (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R history outerF V zero i code next N W fromBase after J Domains E F L Out Images : M.Carrier .set}
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i kappa)
    (hcode : PureKuratowski.PairMember M i code traces)
    (hb : Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images) :
    PureKuratowski.PairMember M i J Indices := by
  obtain ⟨Schedule,last,inner,Steps,Events,Roots,hpack,_⟩ := hb.2.2.2.2.2.1
  exact ConstructionTowerHistory.chart_of_row 0 hd.1 hi ⟨code,hcode,hpack⟩

def Bottoms (kappa zero S OImages : M.Carrier .set) : Prop :=
  ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i kappa → Cut i zero c →
    ∀ x, At S c x ↔ At OImages i x

def Covers (V I R S : M.Carrier .set) : Prop :=
  ∀ terminal, Empty (M := M) terminal → ∀ x, (Project.FirstOrderSemantics.reduct M).mem x V →
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c I ∧ PureKuratowski.PairMember M c terminal R ∧ At S c x

theorem align_bottoms (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hg : ConstructionFlatStages.Graph history outerF kappa V zero traces I S)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages) :
    Bottoms kappa zero S OImages := by
  intro i c hi hc x
  obtain ⟨code,hcode,_⟩ := ht.1.2 i hi
  obtain ⟨next,N,W,fromBase,after,J,Domains,E,F,L,Out,Images,hb⟩ :=
    ConstructionBlockBoundary.family_realized hM hv hB hf hr ht i code hcode
  have hz := realized_zero hM ht hcode hb
  have hJ := realized_index hM hd hi hcode hb
  have hcI := (ConstructionBlockCuts.cut_mem hM hd hc).mpr ⟨J,hi,hJ,hz⟩
  exact (ConstructionFlatStages.realized_at hM ht.1 hf.2.1 hg hc hcI hcode hb hz).trans
    (base_at hM hv hB hf hr ho hb hz)

/-- The actual outer terminal leg stored by Valid is its identity graph. -/
theorem outer_top (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C B history outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV ODomains OE OImages x : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hk : (Project.FirstOrderSemantics.reduct M).mem kappa B)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages) :
    At OImages kappa x ↔ (Project.FirstOrderSemantics.reduct M).mem x V := by
  constructor
  · rintro ⟨A,hA,hx⟩
    exact ho.2.2.2.2.2.1 kappa A hA x hx
  · intro hx
    obtain ⟨_,_,_,next,identity,_,_,hidentity,hid⟩ := hv.2.1 kappa hk V mulV unitV markV HV CV terminalLegs baseV hr
    obtain ⟨A,hA,_⟩ := ho.2.2.2.2.1.1.2 kappa hk
    have hD := ConstructionTowerHistory.chart_of_row 0 ho.1 hk hr
    have hrange := ConstructionBlockStages.range_at ho.1.1 ho.2.2.1.1 ho.2.2.2.2.1 hD hidentity hA
    exact ⟨A,hA,(hrange x).mpr ⟨x,hx,(hid x x).mpr ⟨hx,rfl⟩⟩⟩

/-- Strictly earlier coverage of the final top, using existing continuity
at the actual regular terminal limit; the top itself is NEVER the witness. -/
theorem strict_cover (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages)
    (hb : Bottoms kappa zero S OImages) : Covers V I R S := by
  intro terminal hterminal x hx
  have hB := hindex.2.2.2.1
  have hAt := (outer_top hM hv hB.predecessor_mem hr ho).mpr hx
  obtain ⟨i,hi,hxi⟩ := ho.2.2.2.2.2.2.2 kappa hB.predecessor_mem hindex.2.1.isLimitOrdinal x hAt
  obtain ⟨J,last,hends,_,_,_,hz⟩ := ConstructionBlockCuts.actual_ends hM ht hi
  have hJ := ConstructionBlockCuts.ends_index hM hd hi hends
  obtain ⟨c,hcI,hc⟩ := ConstructionBlockCuts.exists_cut hM hd hJ hz
  have hdCopy := hd
  obtain ⟨_,_,_,_,_,hI,_,hR⟩ := hdCopy
  have htI := (hI terminal).mpr (Or.inl hterminal)
  have hcCopy := hc
  obtain ⟨p,_,hs⟩ := hcCopy
  exact ⟨c,hcI,(hR c terminal).mpr ⟨hcI,htI,Or.inl ⟨ForcingWithTopCarrier.single_nonempty hs,hterminal⟩⟩,
    (hb i c hi hc x).mpr hxi⟩

theorem assembly (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hg : ConstructionFlatStages.Graph history outerF kappa V zero traces I S)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages) :
    Bottoms kappa zero S OImages ∧ Covers V I R S := by
  have hb := align_bottoms hM hv hindex.2.2.2.1 hf hr ht hd hg ho
  exact ⟨hb,strict_cover hM hv hindex hr ht hd ho hb⟩

/-- Actual caller: obtain BOTH graphs and the cut index from the SAME
saved recursion. Choice/order are discharged by the existing L interpretation. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q values top D mul e mark H C zero one u K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV : M.Carrier .set}
    (hctx : ConstructionSaturationIterationCases.Context hM w Q values top D mul e mark H C zero one u K mu B)
    (hrec : ConstructionSaturationIteration.Recursive hM w Q values top D mul e mark H C zero one K mu B B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa) :
    ∃ traces Indices A r I R S ODomains OE OImages,
      ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces ∧
      ConstructionBlockIndex.Data hM kappa traces Indices A r I R ∧
      ConstructionFlatStages.Result history outerF kappa V zero traces I S ∧
      ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages ∧
      Bottoms kappa zero S OImages ∧ Covers V I R S := by
  have hv := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice hctx hrec (fun _ h => h)).1
  have hB := hindex.2.2.2.1
  obtain ⟨traces,Indices,A,r,I,R,ht,hd⟩ := ConstructionBlockIndex.recursive_index hM hOrder hChoice hctx hrec hf hB.predecessor_mem
  obtain ⟨S,hS⟩ := ConstructionFlatStages.construction hM hv hB hf hr ht hd
  obtain ⟨ODomains,OE,OImages,ho⟩ := ConstructionBlockContinuity.outer_continuous hM hOrder hChoice hctx hrec hf hB hr
  exact ⟨traces,Indices,A,r,I,R,S,ODomains,OE,OImages,ht,hd,hS,ho,assembly hM hv hindex hf hr ht hd hS.1 ho⟩

def bottoms {m : Nat} (kappa zero S OImages : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound 1) (.bound kappa.succ.succ)) (.imp (ConstructionBlockCuts.cut 1
  zero.succ.succ 0) (.forallE (.iff (ConstructionFirstAppearance.atStage S.succ.succ.succ 1 0)
  (ConstructionFirstAppearance.atStage OImages.succ.succ.succ 2 0)))))))

theorem bottoms_freeClosed {m : Nat} (kappa zero S OImages : Fin m) :
    (bottoms kappa zero S OImages).FreeClosed := by
  simp -implicitDefEqProofs [bottoms,Definitional.Formula.FreeClosed,ConstructionBlockCuts.cut_freeClosed,ConstructionFirstAppearance.atStage_freeClosed]

theorem bottoms_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (kappa zero S OImages : Fin m) :
    Project.Formula.satisfies env (bottoms kappa zero S OImages) ↔ Bottoms (env.bound kappa) (env.bound zero) (env.bound S) (env.bound OImages) := by
  simp only [bottoms,Bottoms,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_iff_iff,ConstructionBlockCuts.cut_semantics hM,ConstructionFirstAppearance.atStage_semantics hM]
  rfl

def covers {m : Nat} (V I R S : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty 0)) (.forallE (.imp (.mem (.bound 0)
  (.bound V.succ.succ)) (.existsE (.conj (.mem (.bound 0) (.bound I.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ.succ 0 2))
  (ConstructionFirstAppearance.atStage S.succ.succ.succ 0 1))))))))

theorem covers_freeClosed {m : Nat} (V I R S : Fin m) :
    (covers V I R S).FreeClosed := by
  simp -implicitDefEqProofs [covers,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionFirstAppearance.atStage_freeClosed]

theorem covers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V I R S : Fin m) :
    Project.Formula.satisfies env (covers V I R S) ↔ Covers (env.bound V) (env.bound I) (env.bound R) (env.bound S) := by
  simp only [covers,Covers,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingWithTopCarrier.empty_semantics (M := M),ConstructionFirstAppearance.atStage_semantics hM]
  rfl

def assemblySentence {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionTowerValidity.valid w Q values top D mul e mark H C B history) (.imp
    (ConstructionSaturationIndex.data w mu kappa B) (.imp (ConstructionTowerTransitions.matrix B history
    zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V mulV unitV markV HV CV terminalLegs
    baseV kappa) (.imp (ConstructionBlockTraces.family w Q values top zero one K mu history outerF kappa
    traces) (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R) (.imp
    (ConstructionFlatStages.graph history outerF kappa V zero traces I S) (.imp
    (ConstructionBlockContinuity.outerData B history outerF terminalLegs V ODomains OE OImages) (.conj
    (bottoms kappa zero S OImages) (covers V I R S))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerValidity.valid_freeClosed,ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.graph_freeClosed,ConstructionBlockContinuity.outerData_freeClosed,bottoms_freeClosed,covers_freeClosed]

theorem assembly_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : Fin m) : (Project.fo_sentence (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,ConstructionTowerValidity.valid_semantics hM,ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.graph_semantics hM,ConstructionBlockContinuity.outerData_semantics hM,bottoms_semantics hM,covers_semantics hM]
  exact assembly hM

theorem assembly_kernel_certificate {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages)) := by
  apply ModelTransfer.derives
  intro M hM
  exact assembly_models hM w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R S ODomains OE OImages

def constructionSentence {m : Nat} (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionSaturationIterationCases.context w Q values top D mul e mark H C zero one u K mu B)
    (.imp (ConstructionSaturationIteration.recursive w Q values top D mul e mark H C zero one K mu B B
    history) (.imp (ConstructionSaturationIndex.data w mu kappa B) (.imp
    (ConstructionTowerTransitions.matrix B history zero P outerF) (.imp (ConstructionTowerHistory.row
    history kappa V mulV unitV markV HV CV terminalLegs baseV kappa) (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionBlockTraces.family
    w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    values.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9) (.conj (ConstructionBlockIndex.data
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 7 6 5 4) (.conj
    (ConstructionFlatStages.result history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 5 3) (.conj
    (ConstructionBlockContinuity.outerData B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    terminalLegs.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 2 1 0) (.conj (bottoms
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 0) (covers
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 5 4 3)))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.result_freeClosed,ConstructionBlockContinuity.outerData_freeClosed,bottoms_freeClosed,covers_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {m : Nat}
    (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : (Project.fo_sentence (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.result_semantics hM,ConstructionBlockContinuity.outerData_semantics hM,bottoms_semantics hM,covers_semantics hM]
  exact construction hM hOrder hChoice

theorem construction_kernel_certificate {m : Nat} (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)

end PPAC.Migration.ConstructionFlatOuter
