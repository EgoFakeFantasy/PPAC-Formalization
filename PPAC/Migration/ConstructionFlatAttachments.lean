/- Pinned BlockTower.flatten.step: SAME actual stages and final monoid.
The final top and inter-block boundary are identity steps; each proper
inner successor consumes the actual block attachment. -/
import PPAC.Migration.ConstructionBlockAttachments
import PPAC.Migration.ConstructionFlatTimeline

namespace PPAC.Migration.ConstructionFlatAttachments
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid)
open ConstructionTowerTransitions (Matrix)
open ConstructionBlockBoundary (Realized)
open ConstructionBlockCuts (Cut)
open ConstructionFirstAppearance (Cover Timeline)
open ForcingConditionGraphs (FunctionOn function_unique)
open ForcingWithTopCarrier (Empty)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Step (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q values top zero one traces V GV unitV A0 A1 : M.Carrier .set) : Prop :=
  A0 = A1 ∨ ∃ i code J Out j k, PureKuratowski.PairMember M i code traces ∧
    ConstructionBlockAttachments.At hM w Q values top zero one code V GV unitV J Out j k A0 A1

def Next (I R c d : M.Carrier .set) : Prop := Cover I R c d ∨ Empty (M := M) c ∧ d = c

/-- Every internal index has its original successor, with the same two
stage sets. The final top is kept as an identity step. -/
def Steps (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q values top zero one traces V GV unitV I R S : M.Carrier .set) : Prop :=
  ∀ c, (Project.FirstOrderSemantics.reduct M).mem c I →
    ∃ d, Next I R c d ∧ ∀ A0 A1,
      PureKuratowski.PairMember M c A0 S → PureKuratowski.PairMember M d A1 S →
      Step hM w Q values top zero one traces V GV unitV A0 A1

/-- Exact set equality is already available; use it to read the original
Images edge rather than merely transferring element membership. -/
theorem image_at (hM : FirstOrder.Theory.Models M nativeZF)
    {P history outerF kappa V zero traces I S i j c code next N W fromBase after
      J Domains E F L Out Images A0 : M.Carrier .set}
    (ht : FunctionOn kappa traces) (hf : FunctionOn P outerF)
    (hg : ConstructionFlatStages.Graph history outerF kappa V zero traces I S)
    (hc : Cut i j c) (hcI : (Project.FirstOrderSemantics.reduct M).mem c I)
    (hcode : PureKuratowski.PairMember M i code traces)
    (hr : Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hA0 : PureKuratowski.PairMember M c A0 S) : PureKuratowski.PairMember M j A0 Images := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hresult,_,_⟩ := hr.2.2.2.2.2.1
  obtain ⟨A1,hA1,_⟩ := hresult.2.2.2.2.1.1.2 j hj
  have hvalue : ConstructionFlatStages.Value history outerF kappa V zero traces i j A1 :=
    ⟨code,next,N,W,fromBase,after,J,Domains,E,F,L,Out,Images,hcode,hr,hA1⟩
  have eq := ConstructionFlatStages.value_unique hM ht hf
    ((ConstructionFlatStages.graph_cut hg hc hcI).mp hA0) hvalue
  exact eq ▸ hA1

/-- The actual flatten.step proof, including both identity branches.
All attachment premises are discharged by the retained outer execution. -/
theorem assembly (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S : M.Carrier .set}
    (hv : Valid hM w Q values top D mul e mark H C B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hg : ConstructionFlatStages.Graph history outerF kappa V zero traces I S) :
    Steps hM w Q values top zero one traces V GV unitV I R S := by
  intro c hcI
  have hdCopy := hd
  obtain ⟨_,_,hCarrier,_,_,hI,_,_⟩ := hdCopy
  rcases (hI c).mp hcI with he | ⟨p,hp,hsc⟩
  · exact ⟨c,Or.inr ⟨he,rfl⟩,fun _ _ h0 h1 => Or.inl (function_unique hg.1 h0 h1)⟩
  · obtain ⟨i,J,j,hi,hJi,hj,hpc⟩ := (hCarrier p).mp hp
    have hc : Cut i j c := ⟨p,hpc,hsc⟩
    obtain ⟨code,hcode,_⟩ := ht.1.2 i hi
    obtain ⟨next,N,W,fromBase,after,J',Domains,E,F,L,Out,Images,hreal⟩ :=
      ConstructionBlockBoundary.family_realized hM hv hindex.2.2.2.1 hf hr ht i code hcode
    have eqJ := function_unique hd.2.1.1 hJi (ConstructionFlatOuter.realized_index hM hd hi hcode hreal)
    subst J'
    obtain ⟨Schedule,last,inner,EventsSet,Events,Roots,hpack,_,_,_,_,_,_,_⟩ := hreal.2.2.2.2.2.1
    obtain ⟨hJ,hlast,hzero,_⟩ := ConstructionFlatTimeline.ends_at hM ht hcode hpack
    classical
    by_cases eqLast : j = last
    · subst j
      obtain ⟨upper,hupper,hiupper⟩ := hindex.2.1.isLimitOrdinal.2.2 i hi
      obtain ⟨next',hn,hs,_⟩ := ConstructionCompleteRound.successor_before_last hM hindex.1.1 hupper hiupper
      have en : next' = next := (ModelTransfer.extensionality hM).eq_of_same_members next' next
        (fun x => (hs x).trans (hreal.1 x).symm)
      subst next'
      obtain ⟨codeNext,hcodeNext,_⟩ := ht.1.2 next hn
      obtain ⟨nextNext,Nnext,Wnext,fromNext,afterNext,Jnext,DomainsNext,Enext,Fnext,Lnext,OutNext,ImagesNext,hrealNext⟩ :=
        ConstructionBlockBoundary.family_realized hM hv hindex.2.2.2.1 hf hr ht next codeNext hcodeNext
      have hJnext := ConstructionFlatOuter.realized_index hM hd hn hcodeNext hrealNext
      have hzNext := ConstructionFlatOuter.realized_zero hM ht hcodeNext hrealNext
      obtain ⟨d,hdI,hdCut⟩ := ConstructionBlockCuts.exists_cut hM hd hJnext hzNext
      have hCover := ConstructionBlockCuts.boundary_cover hM hindex.1.1 hd hJi hJnext
        hreal.1 hlast hzero hzNext hc hdCut
      refine ⟨d,Or.inl hCover,?_⟩
      intro A0 A1 hA0 hA1
      exact Or.inl (ConstructionBlockBoundary.boundary_equal hM hv.1.1 hf.2.1 hreal hrealNext hpack
        (image_at hM ht.1 hf.2.1 hg hc hcI hcode hreal hj hA0)
        (image_at hM ht.1 hf.2.1 hg hdCut hdI hcodeNext hrealNext hzNext hA1))
    · have hjLast : (Project.FirstOrderSemantics.reduct M).mem j last := by
        rcases (hlast j).mp hj with h | he
        · exact h
        · exact (eqLast ((ModelTransfer.extensionality hM).eq_of_same_members j last he)).elim
      obtain ⟨k,hk,hjk,_⟩ := ConstructionCompleteRound.successor_before_last hM hJ hlast.predecessor_mem hjLast
      obtain ⟨d,hdI,hdCut⟩ := ConstructionBlockCuts.exists_cut hM hd hJi hk
      have hCover := ConstructionBlockCuts.inner_cover hM hindex.1.1 hd hJi hk hjk hc hdCut
      have hSteps := ConstructionBlockAttachments.family_steps hM hv hindex.2.2.2.1 hf hr ht hcode hreal
      refine ⟨d,Or.inl hCover,?_⟩
      intro A0 A1 hA0 hA1
      exact Or.inr ⟨i,code,J,Out,j,k,hcode,hSteps j k A0 A1 hj hk hjk
        (image_at hM ht.1 hf.2.1 hg hc hcI hcode hreal hj hA0)
        (image_at hM ht.1 hf.2.1 hg hdCut hdI hcode hreal hk hA1)⟩

theorem cover_step (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S c d A0 A1 : M.Carrier .set}
    (hv : Valid hM w Q values top D mul e mark H C B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hg : ConstructionFlatStages.Graph history outerF kappa V zero traces I S)
    (hCover : Cover I R c d)
    (hA0 : PureKuratowski.PairMember M c A0 S) (hA1 : PureKuratowski.PairMember M d A1 S) :
    Step hM w Q values top zero one traces V GV unitV A0 A1 := by
  obtain ⟨d',hnext,hstep⟩ := assembly hM hv hindex hf hr ht hd hg c hCover.1
  rcases hnext with hc | ⟨he,rfl⟩
  · rcases ConstructionFirstAppearance.cover_le hM hd.2.2.2.2.2.2.1 hc hCover.2.1 hCover.2.2.1 with eq | hlt
    · subst d'
      exact hstep A0 A1 hA0 hA1
    · exact (hCover.2.2.2 d' hc.2.1 hc.2.2.1 hlt).elim
  · obtain ⟨i,J,j,_,_,_,q,_,hSingle⟩ := ConstructionBlockCuts.source_cut hM hd hCover.2.2.1
    exact (ForcingWithTopCarrier.single_nonempty hSingle he).elim

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
    ∃ traces Indices A r I R S ODomains OE OImages bottom,
      ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces ∧
      ConstructionBlockIndex.Data hM kappa traces Indices A r I R ∧
      ConstructionFlatStages.Result history outerF kappa V zero traces I S ∧
      ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages ∧
      ConstructionFlatOuter.Bottoms kappa zero S OImages ∧ ConstructionFlatOuter.Covers V I R S ∧
      Timeline hM V I R bottom S ∧
      Steps hM w Q values top zero one traces V mulV unitV I R S := by
  obtain ⟨traces,Indices,A,r,I,R,S,ODomains,OE,OImages,bottom,ht,hd,hS,ho,hb,hcovers,hTimeline⟩ :=
    ConstructionFlatTimeline.construction hM hOrder hChoice hctx hrec hindex hf hr
  have hv := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice hctx hrec (fun _ h => h)).1
  exact ⟨traces,Indices,A,r,I,R,S,ODomains,OE,OImages,bottom,ht,hd,hS,ho,hb,hcovers,hTimeline,
    assembly hM hv hindex hf hr ht hd hS.1⟩

def step {m : Nat} (w Q values top zero one traces V GV unitV A0 A1 : Fin m) : Project.Formula 1 m :=
  (.disj (Project.Formula.extensionalEq (.bound A0) (.bound A1)) (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge traces.succ.succ.succ.succ.succ.succ 5 4))
  (ConstructionBlockAttachments.atFormula w.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ
  values.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ 4 V.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ
  unitV.succ.succ.succ.succ.succ.succ 3 2 1 0 A0.succ.succ.succ.succ.succ.succ
  A1.succ.succ.succ.succ.succ.succ)))))))))

theorem step_freeClosed {m : Nat} (w Q values top zero one traces V GV unitV A0 A1 : Fin m) :
    (step w Q values top zero one traces V GV unitV A0 A1).FreeClosed := by
  simp -implicitDefEqProofs [step,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionBlockAttachments.atFormula_freeClosed]

theorem step_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q values top zero one traces V GV unitV A0 A1 : Fin m) :
    Project.Formula.satisfies env (step w Q values top zero one traces V GV unitV A0 A1) ↔ Step hM (env.bound w) (env.bound Q) (env.bound values) (env.bound top) (env.bound zero) (env.bound one) (env.bound traces) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound A0) (env.bound A1) := by
  simp only [step,Step,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBlockAttachments.atFormula_semantics hM]
  rfl

def nextFormula {m : Nat} (I R c d : Fin m) : Project.Formula 1 m :=
  (.disj (ConstructionFirstAppearance.cover I R c d) (.conj (Project.Formula.isEmpty (.bound c))
  (Project.Formula.extensionalEq (.bound d) (.bound c))))

theorem nextFormula_freeClosed {m : Nat} (I R c d : Fin m) :
    (nextFormula I R c d).FreeClosed := by
  simp -implicitDefEqProofs [nextFormula,Definitional.Formula.FreeClosed,ConstructionFirstAppearance.cover_freeClosed,Project.Formula.isEmpty,Project.Formula.extensionalEq]

theorem nextFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I R c d : Fin m) :
    Project.Formula.satisfies env (nextFormula I R c d) ↔ Next (M := M) (env.bound I) (env.bound R) (env.bound c) (env.bound d) := by
  simp only [nextFormula,Next,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,ConstructionFirstAppearance.cover_semantics hM]
  rfl

def steps {m : Nat} (w Q values top zero one traces V GV unitV I R S : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound I.succ)) (.existsE (.conj (nextFormula I.succ.succ R.succ.succ 1 0)
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ 3 1))     (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ 2 0))     (step w.succ.succ.succ.succ
  Q.succ.succ.succ.succ values.succ.succ.succ.succ top.succ.succ.succ.succ zero.succ.succ.succ.succ
  one.succ.succ.succ.succ traces.succ.succ.succ.succ V.succ.succ.succ.succ GV.succ.succ.succ.succ
  unitV.succ.succ.succ.succ 1 0)))))))))

theorem steps_freeClosed {m : Nat} (w Q values top zero one traces V GV unitV I R S : Fin m) :
    (steps w Q values top zero one traces V GV unitV I R S).FreeClosed := by
  simp -implicitDefEqProofs [steps,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,nextFormula_freeClosed,step_freeClosed]

theorem steps_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q values top zero one traces V GV unitV I R S : Fin m) :
    Project.Formula.satisfies env (steps w Q values top zero one traces V GV unitV I R S) ↔ Steps hM (env.bound w) (env.bound Q) (env.bound values) (env.bound top) (env.bound zero) (env.bound one) (env.bound traces) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound I) (env.bound R) (env.bound S) := by
  simp only [steps,Steps,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,nextFormula_semantics hM,step_semantics hM]
  rfl

def assemblySentence {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionTowerValidity.valid w Q values top D mul e mark H C B history)
    (.imp (ConstructionSaturationIndex.data w mu kappa B)
    (.imp (ConstructionTowerTransitions.matrix B history zero P outerF)
    (.imp (ConstructionTowerHistory.row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (.imp (ConstructionBlockTraces.family w Q values top zero one K mu history outerF kappa traces)
    (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R)
    (.imp (ConstructionFlatStages.graph history outerF kappa V zero traces I S)
    (steps w Q values top zero one traces V GV unitV I R S))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerValidity.valid_freeClosed,ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.graph_freeClosed,steps_freeClosed]

theorem assembly_models {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,ConstructionTowerValidity.valid_semantics hM,ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.graph_semantics hM,steps_semantics hM]
  exact assembly hM

theorem assembly_kernel_certificate {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S)) :=
  ModelTransfer.derives (fun _ hM => assembly_models w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S hM)

def coverStepSentence {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S c d A0 A1 : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionTowerValidity.valid w Q values top D mul e mark H C B history)
    (.imp (ConstructionSaturationIndex.data w mu kappa B)
    (.imp (ConstructionTowerTransitions.matrix B history zero P outerF)
    (.imp (ConstructionTowerHistory.row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (.imp (ConstructionBlockTraces.family w Q values top zero one K mu history outerF kappa traces)
    (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R)
    (.imp (ConstructionFlatStages.graph history outerF kappa V zero traces I S)
    (.imp (ConstructionFirstAppearance.cover I R c d)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S c A0))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S d A1))
    (step w Q values top zero one traces V GV unitV A0 A1)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerValidity.valid_freeClosed,ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.graph_freeClosed,ConstructionFirstAppearance.cover_freeClosed,step_freeClosed]

theorem coverStep_models {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S c d A0 A1 : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (coverStepSentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S c d A0 A1)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (coverStepSentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S c d A0 A1)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerValidity.valid_semantics hM,ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.graph_semantics hM,ConstructionFirstAppearance.cover_semantics hM,step_semantics hM]
  exact cover_step hM

theorem coverStep_kernel_certificate {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S c d A0 A1 : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (coverStepSentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S c d A0 A1)) :=
  ModelTransfer.derives (fun _ hM => coverStep_models w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S c d A0 A1 hM)

def constructionSentence {m : Nat} (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionSaturationIterationCases.context w Q values top D mul e mark H C zero one u K mu B)
    (.imp (ConstructionSaturationIteration.recursive w Q values top D mul e mark H C zero one K mu B B
    history) (.imp (ConstructionSaturationIndex.data w mu kappa B) (.imp
    (ConstructionTowerTransitions.matrix B history zero P outerF) (.imp (ConstructionTowerHistory.row
    history kappa V mulV unitV markV HV CV terminalLegs baseV kappa) (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionBlockTraces.family w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    values.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10) (.conj (ConstructionBlockIndex.data
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 9 8 7 6 5) (.conj
    (ConstructionFlatStages.result history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 6 4) (.conj
    (ConstructionBlockContinuity.outerData B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    terminalLegs.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 2 1) (.conj (ConstructionFlatOuter.bottoms
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 4 1) (.conj (ConstructionFlatOuter.covers
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 4) (.conj (ConstructionFirstAppearance.timeline
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 0 4) (steps w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ values.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mulV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 4))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.result_freeClosed,ConstructionBlockContinuity.outerData_freeClosed,ConstructionFlatOuter.bottoms_freeClosed,ConstructionFlatOuter.covers_freeClosed,ConstructionFirstAppearance.timeline_freeClosed,steps_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {m : Nat}
    (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : (Project.fo_sentence (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.result_semantics hM,ConstructionBlockContinuity.outerData_semantics hM,ConstructionFlatOuter.bottoms_semantics hM,ConstructionFlatOuter.covers_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,steps_semantics hM]
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

end PPAC.Migration.ConstructionFlatAttachments
