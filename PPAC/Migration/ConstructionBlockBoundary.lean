/- Pinned BlockTowers.Saturation.blockStage_base and blocks.boundary.
Extract the literal initial identity from the SAME recursive trace, then
consume existing naturality and range_comp_surjective. Adjacent blocks
meet at the SAME outer carrier and terminal map, not just an isomorphic one. -/
import PPAC.Migration.ConstructionActualBlocks

namespace PPAC.Migration.ConstructionBlockBoundary
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Field)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerTransitions (Before Matrix)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive Good)
open ConstructionRoundSelection (Pack)
open ConstructionProbeMappedPath (NodeMap)
open ForcingConditionGraphs (FunctionOn function_unique function_input IdentityGraph)
open ForcingSupportSize (MapsTo)
open ForcingSupportedNames (Range)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Recover the identity which the accepted initial branch actually stored. -/
theorem zero_row (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u J Schedule history : M.Carrier .set}
    (hctx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hrec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hzJ : (Project.FirstOrderSemantics.reduct M).mem zero J) :
    ∃ K identity, Row history zero D mul e mark H C K identity zero ∧
      MapsTo D D identity ∧ IdentityGraph D identity := by
  have hJ := hctx.2.2.2.2.2.2.2.2.2.1
  have hv := ConstructionTowerIterationValidity.recursive_valid hM hctx hrec (fun _ h => h)
  obtain ⟨code,hcode,_⟩ := hv.1.1.2 zero hzJ
  obtain ⟨prior,hr,hop⟩ := hrec.2 zero hzJ code hcode
  have hpriorRec := Structure.IsRecursiveSequence.restriction hrec hzJ hr
  have hpriorValid := ConstructionTowerIterationValidity.recursive_valid hM hctx hpriorRec (hJ.transitive zero hzJ)
  have hgood : Good hM w Q R top D mul e mark H C J prior zero := ⟨hJ.mem hzJ,hzJ,hpriorValid⟩
  have hcase := (ConstructionTowerIteration.valid_step hM hctx hgood hop).1
  rcases hcase with ⟨_,hinit⟩ | ⟨hne,_⟩ | ⟨hne,_⟩
  · obtain ⟨_,identity,K,hm,hi,_,_,_,_,_,_,hp⟩ := hinit
    exact ⟨K,identity,⟨code,hcode,hp⟩,hm,hi⟩
  · exact False.elim (hne rfl)
  · exact False.elim (hne rfl)

def Base (D fromBase zero Images : M.Carrier .set) : Prop :=
  ∀ A, PureKuratowski.PairMember M zero A Images → Range D fromBase A

/-- The actual bottom image equals the image of the original base map. -/
theorem trace_base (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V
      J Domains E F L Out Images fromBase : M.Carrier .set}
    (ht : ConstructionBlockTraces.Trace hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code)
    (hd : ConstructionActualBlocks.Data code W after V J Domains E F L Out Images)
    (hf : MapsTo D V fromBase) (hcomp : NodeMap O after fromBase) : Base D fromBase zero Images := by
  obtain ⟨Schedule,last,history,Steps,Events,Roots,hpack,hchart,_,hL,_,hresult,_,_⟩ := hd
  obtain ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J',collapse,inverse,Schedule',Place,last',
    history',P,F',Steps',Events',Roots',L',hpack',hctx,hschedule,_,hrec,_,_,_,_,hrow,_⟩ := ht
  obtain ⟨eJ,eS,el,eh,eF,eSteps,eEvents,eRoots,eL⟩ := ConstructionRoundSelection.pack_injective hpack hpack'
  subst J' Schedule' last' history' F' Steps' Events' Roots' L'
  have hv := ConstructionTowerIterationValidity.recursive_valid hM hctx hrec (fun _ h => h)
  have hctxCopy := hctx
  obtain ⟨_,_,_,_,_,_,_,hz,_,hJ,_,_⟩ := hctxCopy
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hl,_,_,hends,_⟩ := hschedule
  have hzJ := Structure.IsOrdinal.empty_mem_of_nonempty
    (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) hJ ⟨last,hl⟩ hz
  obtain ⟨K0,identity,hr0,hidMap,hid⟩ := zero_row hM hctx hrec hzJ
  obtain ⟨leg,hleg,_⟩ := hL.1.2 zero hzJ
  obtain ⟨out,hout,_⟩ := hresult.2.1.1.2 zero hzJ
  have hn := hv.2.2.2.2 zero last identity O L leg hzJ hl ((hends zero).mp hzJ)
    (row_field 7 hr0) (row_field 7 hrow) (row_field 6 hrow) hleg
  have hc := hresult.2.2.1 zero leg out hzJ hleg hout
  have hfinal := ConstructionRoundFields.node_comp hc hn hcomp
  obtain ⟨Afrom,hAfrom⟩ := ConstructionBlockStages.range_exists hM hf
  intro A hA
  have hAout := ConstructionBlockStages.range_at hchart.1 hresult.2.1.1 hresult.2.2.2.2.1
    (ConstructionTowerHistory.chart_of_row 0 hchart hzJ hr0) hout hA
  have he := ConstructionBlockStages.range_comp_surjective hM hidMap
    (fun x hx => ⟨x,hx,(hid x x).mpr ⟨hx,rfl⟩⟩) hfinal hAfrom hAout
  exact he ▸ hAfrom

/-- Keep the actual outer carriers and matrix values for adjacent alignment. -/
def Realized (history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).SuccessorOf j i ∧
  Field 0 history i N ∧ Field 0 history j W ∧
  Product outerF i kappa fromBase ∧ Product outerF j kappa after ∧
  ConstructionActualBlocks.Data code W after V J Domains E F L Out Images ∧ Base N fromBase zero Images

/-- Actual caller: discharge the bottom equation for the selected round. -/
theorem at_realized (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV i code : M.Carrier .set}
    (hv : Valid hM w Q R top D mul e mark H C B history)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.At hM w Q R top zero one K mu history outerF i code) :
    ∃ j N W fromBase after J Domains E F L Out Images,
      Realized history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images := by
  obtain ⟨j,raw,Requests,N,mulN,eN,markN,HN,CN,L0,f,W,G,unitW,markW,HW,CW,NewOut,baseW,O,
    hsucc,hri,hrj,_,_,_,hO,_,htrace⟩ := ht
  have hi : (Project.FirstOrderSemantics.reduct M).mem i B := by
    obtain ⟨raw,hraw,_⟩ := hri
    exact function_input hv.1.1 hraw
  have hj : (Project.FirstOrderSemantics.reduct M).mem j B := by
    obtain ⟨raw,hraw,_⟩ := hrj
    exact function_input hv.1.1 hraw
  have hk := hs.predecessor_mem
  have bik := ConstructionActualBlocks.before_last hM hs hi
  have bjk := ConstructionActualBlocks.before_last hM hs hj
  obtain ⟨next,hn,hfn⟩ := ConstructionTowerValidity.incoming_rows hM hv kappa terminalLegs hk (row_field 6 hr)
  have get (x : M.Carrier .set) (hx : Before x kappa) : ∃ t, PureKuratowski.PairMember M x t terminalLegs := by
    have hxn : (Project.FirstOrderSemantics.reduct M).mem x next := by
      apply (hn x).mpr
      rcases hx with h | h
      · exact Or.inl h
      · subst x
        exact Or.inr (fun _ => Iff.rfl)
    obtain ⟨t,ht,_⟩ := hfn.2 x hxn
    exact ⟨t,ht⟩
  obtain ⟨fromBase,hfrom⟩ := get i bik
  obtain ⟨after,hafter⟩ := get j bjk
  have hm := hv.2.2.1 i kappa N mulN eN markN HN CN L0 f
    V mulV unitV markV HV CV terminalLegs baseV fromBase hi hk bik hri hr hfrom
  have ha := hv.2.2.1 j kappa W G unitW markW HW CW NewOut baseW
    V mulV unitV markV HV CV terminalLegs baseV after hj hk bjk hrj hr hafter
  have hlegO := (ConstructionTowerTransitions.matrix_at hv.1 hf hi hj
    (Or.inl hsucc.predecessor_mem) (row_field 6 hrj)).mp hO
  have hc := hv.2.2.2.1 i j kappa NewOut terminalLegs O after fromBase hi hj hk
    (Or.inl hsucc.predecessor_mem) bjk (row_field 6 hrj) (row_field 6 hr) hlegO hafter hfrom
  obtain ⟨J,Domains,E,F,L,Out,Images,hd⟩ := ConstructionActualBlocks.trace_block hM htrace ha.1.1.1.1
  exact ⟨j,N,W,fromBase,after,J,Domains,E,F,L,Out,Images,hsucc,row_field 0 hri,row_field 0 hrj,
    (ConstructionTowerTransitions.matrix_at hv.1 hf hi hk bik (row_field 6 hr)).mpr hfrom,
    (ConstructionTowerTransitions.matrix_at hv.1 hf hj hk bjk (row_field 6 hr)).mpr hafter,
    hd,trace_base hM htrace hd hm.1.1.1.1 hc⟩

theorem family_realized (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces : M.Carrier .set}
    (hv : Valid hM w Q R top D mul e mark H C B history)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q R top zero one K mu history outerF kappa traces) :
    ∀ i code, PureKuratowski.PairMember M i code traces →
      ∃ j N W fromBase after J Domains E F L Out Images,
        Realized history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images := by
  intro i code hcode
  exact at_realized hM hv hs hf hr ((ht.2 i code).mp hcode).2.1

/-- Source blocks.boundary is literal equality of the two range sets. -/
theorem boundary_equal (hM : FirstOrder.Theory.Models M nativeZF)
    {B P history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images
      codeNext next Nnext Wnext fromNext afterNext Jnext DomainsNext Enext Fnext Lnext OutNext ImagesNext
      Schedule last inner Steps Events Roots A Anew : M.Carrier .set}
    (hh : FunctionOn B history) (hf : FunctionOn P outerF)
    (hi : Realized history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images)
    (hj : Realized history outerF kappa V zero j codeNext next Nnext Wnext fromNext afterNext Jnext DomainsNext Enext Fnext Lnext OutNext ImagesNext)
    (hp : Pack J Schedule last inner F Steps Events Roots L code)
    (hA : PureKuratowski.PairMember M last A Images)
    (hAnew : PureKuratowski.PairMember M zero Anew ImagesNext) : A = Anew := by
  have eW := ConstructionTowerHistory.field_unique 0 hh hi.2.2.1 hj.2.1
  subst Nnext
  obtain ⟨p,hp0,hpAfter⟩ := hi.2.2.2.2.1
  obtain ⟨p',hp0',hpFrom⟩ := hj.2.2.2.1
  have ep := KuratowskiZF.code_unique hM hp0 hp0'
  subst p'
  have ef := function_unique hf hpAfter hpFrom
  subst fromNext
  obtain ⟨sch,last',inner',steps,events,roots,hpack,_,_,_,_,_,_,htop⟩ := hi.2.2.2.2.2.1
  have el := (ConstructionRoundSelection.pack_injective hp hpack).2.2.1
  subst last'
  exact ConstructionBlockStages.range_unique hM (htop A hA) (hj.2.2.2.2.2.2 Anew hAnew)

def base {m : Nat} (D fromBase zero Images : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Images.succ zero.succ 0))
  (ProjectSyntax.encode id (ForcingSupportedNames.range D.succ fromBase.succ 0))))

theorem base_freeClosed {m : Nat} (D fromBase zero Images : Fin m) :
    (base D fromBase zero Images).FreeClosed := by
  simp -implicitDefEqProofs [base,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem base_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D fromBase zero Images : Fin m) :
    Project.Formula.satisfies env (base D fromBase zero Images) ↔ Base (env.bound D) (env.bound fromBase) (env.bound zero) (env.bound Images) := by
  simp only [base,Base,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportedNames.range_semantics (M := M)]
  rfl

def realized {m : Nat} (history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.isSuccessor (.bound j) (.bound i)) (.conj (ConstructionTowerHistory.field 0 history
  i N) (.conj (ConstructionTowerHistory.field 0 history j W) (.conj (ProjectSyntax.encode id
  (ForcingDiagramOrder.product outerF i kappa fromBase)) (.conj (ProjectSyntax.encode id
  (ForcingDiagramOrder.product outerF j kappa after)) (.conj (ConstructionActualBlocks.data code W after V J
  Domains E F L Out Images) (base N fromBase zero Images)))))))

theorem realized_freeClosed {m : Nat} (history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images : Fin m) :
    (realized history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images).FreeClosed := by
  simp -implicitDefEqProofs [realized,Definitional.Formula.FreeClosed,Project.Formula.isSuccessor,ConstructionTowerHistory.field_freeClosed,ProjectSyntax.freeClosed,ConstructionActualBlocks.data_freeClosed,base_freeClosed]

theorem realized_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images : Fin m) :
    Project.Formula.satisfies env (realized history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images) ↔ Realized (env.bound history) (env.bound outerF) (env.bound kappa) (env.bound V) (env.bound zero) (env.bound i) (env.bound code) (env.bound j) (env.bound N) (env.bound W) (env.bound fromBase) (env.bound after) (env.bound J) (env.bound Domains) (env.bound E) (env.bound F) (env.bound L) (env.bound Out) (env.bound Images) := by
  simp only [realized,Realized,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,ConstructionTowerHistory.field_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M),ConstructionActualBlocks.data_semantics hM,base_semantics hM]
  rfl

def constructionSentence {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionTowerValidity.valid w Q R top D mul e mark H C B history) (.imp
    (Project.Formula.isSuccessor (.bound B) (.bound kappa)) (.imp (ConstructionTowerTransitions.matrix B
    history zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V mulV unitV markV HV CV
    terminalLegs baseV kappa) (.imp (ConstructionBlockTraces.family w Q R top zero one K mu history outerF
    kappa traces) (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge traces.succ.succ
    1 0)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (realized
    history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13 12 11 10 9 8 7 6 5 4 3 2 1
    0)))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerValidity.valid_freeClosed,Project.Formula.isSuccessor,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ProjectSyntax.freeClosed,realized_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces : Fin m) : (Project.fo_sentence (constructionSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,ConstructionTowerValidity.valid_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,realized_semantics hM]
  exact family_realized hM

theorem construction_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (constructionSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces)) := by
  apply ModelTransfer.derives
  intro M hM
  exact construction_models hM w Q R top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces

def boundarySentence {m : Nat} (B P history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images codeNext next Nnext Wnext fromNext afterNext Jnext DomainsNext Enext Fnext Lnext OutNext ImagesNext Schedule last inner Steps Events Roots A Anew : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn history B)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.functionOn outerF P)) (.imp (realized history outerF kappa V zero i code j N W
    fromBase after J Domains E F L Out Images) (.imp (realized history outerF kappa V zero j codeNext next
    Nnext Wnext fromNext afterNext Jnext DomainsNext Enext Fnext Lnext OutNext ImagesNext) (.imp
    (ConstructionRoundSelection.pack J Schedule last inner F Steps Events Roots L code) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge Images last A)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge ImagesNext zero Anew)) (Project.Formula.extensionalEq (.bound A) (.bound
    Anew)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,realized_freeClosed,ConstructionRoundSelection.pack_freeClosed,Project.Formula.extensionalEq]

theorem boundary_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (B P history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images codeNext next Nnext Wnext fromNext afterNext Jnext DomainsNext Enext Fnext Lnext OutNext ImagesNext Schedule last inner Steps Events Roots A Anew : Fin m) : (Project.fo_sentence (boundarySentence B P history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images codeNext next Nnext Wnext fromNext afterNext Jnext DomainsNext Enext Fnext Lnext OutNext ImagesNext Schedule last inner Steps Events Roots A Anew)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (boundarySentence B P history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images codeNext next Nnext Wnext fromNext afterNext Jnext DomainsNext Enext Fnext Lnext OutNext ImagesNext Schedule last inner Steps Events Roots A Anew)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,realized_semantics hM,ConstructionRoundSelection.pack_semantics hM]
  exact boundary_equal hM

theorem boundary_kernel_certificate {m : Nat} (B P history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images codeNext next Nnext Wnext fromNext afterNext Jnext DomainsNext Enext Fnext Lnext OutNext ImagesNext Schedule last inner Steps Events Roots A Anew : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (boundarySentence B P history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images codeNext next Nnext Wnext fromNext afterNext Jnext DomainsNext Enext Fnext Lnext OutNext ImagesNext Schedule last inner Steps Events Roots A Anew)) := by
  apply ModelTransfer.derives
  intro M hM
  exact boundary_models hM B P history outerF kappa V zero i code j N W fromBase after J Domains E F L Out Images codeNext next Nnext Wnext fromNext afterNext Jnext DomainsNext Enext Fnext Lnext OutNext ImagesNext Schedule last inner Steps Events Roots A Anew

end PPAC.Migration.ConstructionBlockBoundary
