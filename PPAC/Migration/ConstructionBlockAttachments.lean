/- Pinned BlockTowers.Saturation.blockStage_step.
Consume the same retained complete-round Trace and Realized block. Recover
its full outer terminal map from Valid; read the existing Out/Images.
No alternate round, image family, terminal carrier or Choice premise. -/
import PPAC.Migration.ConstructionSelectedAttachments
import PPAC.Migration.ConstructionBlockBoundary

namespace PPAC.Migration.ConstructionBlockAttachments
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerTransitions (Matrix)
open ConstructionRoundFields (ObjectFields MapFields)
open ConstructionRoundSelection (Pack)
open ConstructionBlockBoundary (Realized)
open ForcingConditionGraphs (function_input)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The attachment retains the same serialized execution and exact Out.
The inner source fields are witnesses from that execution, not a new tower. -/
def At (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero one code V GV unitV J Out i j A0 A1 : M.Carrier .set) : Prop :=
  ∃ D mul e mark H C Schedule last history F Steps Events Roots L raw,
    Pack J Schedule last history F Steps Events Roots L code ∧
    ConstructionSelectedAttachments.At hM w Q R top D mul e mark H C zero one
      Schedule history F i j raw V GV unitV Out A0 A1

def Steps (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero one code V GV unitV J Out Images : M.Carrier .set) : Prop :=
  ∀ i j A0 A1, (Project.FirstOrderSemantics.reduct M).mem i J →
    (Project.FirstOrderSemantics.reduct M).mem j J →
    (Project.FirstOrderSemantics.reduct M).SuccessorOf j i →
    PureKuratowski.PairMember M i A0 Images → PureKuratowski.PairMember M j A1 Images →
    At hM w Q R top zero one code V GV unitV J Out i j A0 A1

/-- Reconcile the two views of the SAME saved Pack, then consume the
accepted successor attachment producer without reconstructing any field. -/
theorem trace_steps (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after
      V GV unitV markV HV CV J Domains E F L Out Images : M.Carrier .set}
    (ht : ConstructionBlockTraces.Trace hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code)
    (hd : ConstructionActualBlocks.Data code W after V J Domains E F L Out Images)
    (hV : ObjectFields hM w Q R top V GV unitV markV HV CV)
    (ha : MapFields hM w Q W V G GV unitW unitV markW markV HW CW HV CV after) :
    Steps hM w Q R top zero one code V GV unitV J Out Images := by
  obtain ⟨Schedule,last,history,EventsSet,Events,Roots,hpack,hchart,_,_,_,hresult,_,_⟩ := hd
  obtain ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J',collapse,inverse,Schedule',Place,last',
    history',P,F',EventsSet',Events',Roots',L',hpack',hctx,hschedule,_,hrec,hF,_,_,_,hrow,_⟩ := ht
  obtain ⟨eJ,eS,el,eh,eF,eSteps,eEvents,eRoots,eL⟩ := ConstructionRoundSelection.pack_injective hpack hpack'
  subst J' Schedule' last' history' F' EventsSet' Events' Roots' L'
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hends,_⟩ := hschedule
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
  intro i j A0 A1 hi hj hij hA0 hA1
  obtain ⟨raw,_,hAttached⟩ := ConstructionSelectedAttachments.map_succ hM
    hctx hrec hF hchart hs hrow hV ha hresult hi hj hij hA0 hA1
  exact ⟨D,mul,e,mark,H,C,Schedule,last,history,F,EventsSet,Events,Roots,L,raw,hpack,hAttached⟩

/-- Actual source blockStage_step: the target object and full afterRound
map follow from the original outer history, not extra caller assumptions. -/
theorem realized_steps (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu B history P outerF kappa
      V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after
      J Domains E F L Out Images : M.Carrier .set}
    (hv : Valid hM w Q R top D mul e mark H C B history)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.At hM w Q R top zero one K mu history outerF i code)
    (hd : Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images) :
    Steps hM w Q R top zero one code V GV unitV J Out Images := by
  obtain ⟨next',raw,Requests,N',mulN,eN,markN,HN,CN,L0,f,W',G,unitW,markW,HW,CW,NewOut,baseW,O,
    hsucc,_,hrj,_,_,_,_,_,htrace⟩ := ht
  have en : next' = next := (ModelTransfer.extensionality hM).eq_of_same_members next' next
    (fun x => (hsucc x).trans (hd.1 x).symm)
  subst next'
  have eW : W' = W := ConstructionTowerHistory.field_unique 0 hv.1.1 (row_field 0 hrj) hd.2.2.1
  subst W'
  have hj : (Project.FirstOrderSemantics.reduct M).mem next B := by
    obtain ⟨raw,hraw,_⟩ := hrj
    exact function_input hv.1.1 hraw
  have hk := hs.predecessor_mem
  have hbefore := ConstructionActualBlocks.before_last hM hs hj
  have hAfter := (ConstructionTowerTransitions.matrix_at hv.1 hf hj hk hbefore (row_field 6 hr)).mp hd.2.2.2.2.1
  have ha := (hv.2.2.1 next kappa W G unitW markW HW CW NewOut baseW
    V GV unitV markV HV CV terminalLegs baseV after hj hk hbefore hrj hr hAfter).1
  have hV := (hv.2.1 kappa hk V GV unitV markV HV CV terminalLegs baseV hr).1
  exact trace_steps hM htrace hd.2.2.2.2.2.1 hV ha

/-- Every original selected outer round and every realization of its
literal range family have the required internal successor attachments. -/
theorem family_steps (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu B history P outerF kappa
      V GV unitV markV HV CV terminalLegs baseV traces i code next N W fromBase after
      J Domains E F L Out Images : M.Carrier .set}
    (hv : Valid hM w Q R top D mul e mark H C B history)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q R top zero one K mu history outerF kappa traces)
    (hcode : PureKuratowski.PairMember M i code traces)
    (hd : Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images) :
    Steps hM w Q R top zero one code V GV unitV J Out Images :=
  realized_steps hM hv hs hf hr ((ht.2 i code).mp hcode).2.1 hd

def atFormula {m : Nat} (w Q R top zero one code V GV unitV J Out i j A0 A1 : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRoundSelection.pack
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 7 6 5 4 3 2 1
  code.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (ConstructionSelectedAttachments.atFormula
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 14 13 12 11 10 9
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 6 5
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 0
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Out.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  A0.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  A1.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))

theorem atFormula_freeClosed {m : Nat} (w Q R top zero one code V GV unitV J Out i j A0 A1 : Fin m) :
    (atFormula w Q R top zero one code V GV unitV J Out i j A0 A1).FreeClosed := by
  simp -implicitDefEqProofs [atFormula,Definitional.Formula.FreeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionSelectedAttachments.atFormula_freeClosed]

theorem atFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero one code V GV unitV J Out i j A0 A1 : Fin m) :
    Project.Formula.satisfies env (atFormula w Q R top zero one code V GV unitV J Out i j A0 A1) ↔ At hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound one) (env.bound code) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound J) (env.bound Out) (env.bound i) (env.bound j) (env.bound A0) (env.bound A1) := by
  simp only [atFormula,At,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionRoundSelection.pack_semantics hM,ConstructionSelectedAttachments.atFormula_semantics hM]
  rfl

def steps {m : Nat} (w Q R top zero one code V GV unitV J Out Images : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound J.succ.succ.succ.succ))     (.imp (.mem
  (.bound 2) (.bound J.succ.succ.succ.succ))     (.imp (Project.Formula.isSuccessor (.bound 2) (.bound 3))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Images.succ.succ.succ.succ 3 1))     (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Images.succ.succ.succ.succ 2 0))     (atFormula
  w.succ.succ.succ.succ Q.succ.succ.succ.succ R.succ.succ.succ.succ top.succ.succ.succ.succ
  zero.succ.succ.succ.succ one.succ.succ.succ.succ code.succ.succ.succ.succ V.succ.succ.succ.succ
  GV.succ.succ.succ.succ unitV.succ.succ.succ.succ J.succ.succ.succ.succ Out.succ.succ.succ.succ 3 2 1 0))))))))))

theorem steps_freeClosed {m : Nat} (w Q R top zero one code V GV unitV J Out Images : Fin m) :
    (steps w Q R top zero one code V GV unitV J Out Images).FreeClosed := by
  simp -implicitDefEqProofs [steps,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isSuccessor,atFormula_freeClosed]

theorem steps_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero one code V GV unitV J Out Images : Fin m) :
    Project.Formula.satisfies env (steps w Q R top zero one code V GV unitV J Out Images) ↔ Steps hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound one) (env.bound code) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound J) (env.bound Out) (env.bound Images) := by
  simp only [steps,Steps,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isSuccessor_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,atFormula_semantics hM]
  rfl

def realizedSentence {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionTowerValidity.valid w Q R top D mul e mark H C B history)
    (.imp (Project.Formula.isSuccessor (.bound B) (.bound kappa))
    (.imp (ConstructionTowerTransitions.matrix B history zero P outerF)
    (.imp (ConstructionTowerHistory.row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (.imp (ConstructionBlockTraces.traceAt w Q R top zero one K mu history outerF i code)
    (.imp (ConstructionBlockBoundary.realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images)
    (steps w Q R top zero one code V GV unitV J Out Images)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isSuccessor,ConstructionTowerValidity.valid_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockBoundary.realized_freeClosed,steps_freeClosed,ConstructionBlockTraces.at_freeClosed]

theorem realized_models {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (realizedSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (realizedSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,ConstructionTowerValidity.valid_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockBoundary.realized_semantics hM,steps_semantics hM,ConstructionBlockTraces.at_semantics hM]
  exact realized_steps hM

theorem realized_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (realizedSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images)) :=
  ModelTransfer.derives (fun _ hM => realized_models w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images hM)

def familySentence {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images traces : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionTowerValidity.valid w Q R top D mul e mark H C B history)
    (.imp (Project.Formula.isSuccessor (.bound B) (.bound kappa))
    (.imp (ConstructionTowerTransitions.matrix B history zero P outerF)
    (.imp (ConstructionTowerHistory.row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (.imp (ConstructionBlockTraces.family w Q R top zero one K mu history outerF kappa traces)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge traces i code))
    (.imp (ConstructionBlockBoundary.realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images)
    (steps w Q R top zero one code V GV unitV J Out Images))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isSuccessor,ProjectSyntax.freeClosed,ConstructionTowerValidity.valid_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockBoundary.realized_freeClosed,steps_freeClosed,ConstructionBlockTraces.family_freeClosed]

theorem family_models {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images traces : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (familySentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images traces)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (familySentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images traces)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerValidity.valid_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockBoundary.realized_semantics hM,steps_semantics hM,ConstructionBlockTraces.family_semantics hM]
  exact family_steps hM

theorem family_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images traces : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (familySentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images traces)) :=
  ModelTransfer.derives (fun _ hM => family_models w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after J Domains E F L Out Images traces hM)

end PPAC.Migration.ConstructionBlockAttachments
