/- Pinned BlockTower.flatStage / flatStage_cut / flatten.terminal.
Collect the SAME actual block ranges with the existing native function graph
constructor. The empty cut maps to the SAME final V, not a replacement model.
Consumers: flattened Timeline, block boundary/continuity and stepCell. -/
import PPAC.Migration.ConstructionBlockBoundary
import PPAC.Migration.ConstructionCutLimits

namespace PPAC.Migration.ConstructionFlatStages
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionBlockCuts (Cut)
open ConstructionBlockBoundary (Realized)
open ForcingConditionGraphs (FunctionOn function_unique function_input)
open ForcingWithTopCarrier (Empty)
open ConstructionRealCuts (Subset)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- A range of the actual selected round, keeping its original terminal leg. -/
def Value (history outerF kappa V zero traces i j A : M.Carrier .set) : Prop :=
  ∃ code next N W fromBase after J Domains E F L Out Images,
    PureKuratowski.PairMember M i code traces ∧
    Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images ∧
    PureKuratowski.PairMember M j A Images

def FlatValue (history outerF kappa V zero traces c A : M.Carrier .set) : Prop :=
  (Empty (M := M) c ∧ A = V) ∨ ∃ i j, Cut i j c ∧ Value history outerF kappa V zero traces i j A

def Graph (history outerF kappa V zero traces I S : M.Carrier .set) : Prop :=
  FunctionOn I S ∧ ∀ c A, PureKuratowski.PairMember M c A S ↔
    (Project.FirstOrderSemantics.reduct M).mem c I ∧ FlatValue history outerF kappa V zero traces c A

/-- Auxiliary presentations of one retained trace give literally equal ranges. -/
theorem data_range_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {code W W' after V J Domains E F L Out Images J' Domains' E' F' L' Out' Images' j A A' : M.Carrier .set}
    (hd : ConstructionActualBlocks.Data code W after V J Domains E F L Out Images)
    (hd' : ConstructionActualBlocks.Data code W' after V J' Domains' E' F' L' Out' Images')
    (ha : PureKuratowski.PairMember M j A Images) (ha' : PureKuratowski.PairMember M j A' Images') : A = A' := by
  obtain ⟨Schedule,last,inner,Steps,Events,Roots,hp,hchart,_,hL,_,hr,_,_⟩ := hd
  obtain ⟨Schedule',last',inner',Steps',Events',Roots',hp',hchart',_,_,_,hr',_,_⟩ := hd'
  obtain ⟨eJ,eS,el,eh,eF,eSteps,eEvents,eRoots,eL⟩ := ConstructionRoundSelection.pack_injective hp hp'
  subst J' Schedule' last' inner' F' Steps' Events' Roots' L'
  have eD := ConstructionTowerHistory.chart_unique hM 0 hchart hchart'
  subst Domains'
  have hj := function_input hr.2.2.2.2.1.1 ha
  obtain ⟨out,hout,_⟩ := hr.2.1.1.2 j hj
  obtain ⟨out',hout',_⟩ := hr'.2.1.1.2 j hj
  have eo := ConstructionTowerSuccessor.value_unique hM hchart.1 hL.1
    ((hr.1 j out).mp hout).2 ((hr'.1 j out').mp hout').2
  subst out'
  obtain ⟨D,hD,_⟩ := hchart.1.2 j hj
  exact ConstructionBlockStages.range_unique hM
    (ConstructionBlockStages.range_at hchart.1 hr.2.1.1 hr.2.2.2.2.1 hD hout ha)
    (ConstructionBlockStages.range_at hchart.1 hr'.2.1.1 hr'.2.2.2.2.1 hD hout' ha')

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {P history outerF kappa V zero traces i j A A' : M.Carrier .set}
    (ht : FunctionOn kappa traces) (hf : FunctionOn P outerF)
    (ha : Value history outerF kappa V zero traces i j A)
    (ha' : Value history outerF kappa V zero traces i j A') : A = A' := by
  obtain ⟨code,next,N,W,fromBase,after,J,Domains,E,F,L,Out,Images,hcode,hr,hA⟩ := ha
  obtain ⟨code',next',N',W',fromBase',after',J',Domains',E',F',L',Out',Images',hcode',hr',hA'⟩ := ha'
  have ec := function_unique ht hcode hcode'
  subst code'
  have en : next = next' := (ModelTransfer.extensionality hM).eq_of_same_members next next'
    (fun x => (hr.1 x).trans (hr'.1 x).symm)
  subst next'
  obtain ⟨p,hp,hafter⟩ := hr.2.2.2.2.1
  obtain ⟨p',hp',hafter'⟩ := hr'.2.2.2.2.1
  have ep := KuratowskiZF.code_unique hM hp hp'
  subst p'
  have ea := function_unique hf hafter hafter'
  subst after'
  exact data_range_unique hM hr.2.2.2.2.2.1 hr'.2.2.2.2.2.1 hA hA'

theorem value_bounded {history outerF kappa V zero traces i j A : M.Carrier .set}
    (ha : Value history outerF kappa V zero traces i j A) : Subset A V := by
  obtain ⟨code,next,N,W,fromBase,after,J,Domains,E,F,L,Out,Images,_,hr,hA⟩ := ha
  obtain ⟨Schedule,last,inner,Steps,Events,Roots,_,_,_,_,_,hresult,_,_⟩ := hr.2.2.2.2.2.1
  exact hresult.2.2.2.2.2.1 j A hA

theorem flatValue_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {P history outerF kappa V zero traces c A A' : M.Carrier .set}
    (ht : FunctionOn kappa traces) (hf : FunctionOn P outerF)
    (ha : FlatValue history outerF kappa V zero traces c A)
    (ha' : FlatValue history outerF kappa V zero traces c A') : A = A' := by
  rcases ha with ⟨he,rfl⟩ | ⟨i,j,hc,hA⟩
  · rcases ha' with ⟨_,rfl⟩ | ⟨i,j,⟨p,_,hs⟩,_⟩
    · rfl
    · exact (ForcingWithTopCarrier.single_nonempty hs he).elim
  · rcases ha' with ⟨he,_⟩ | ⟨i',j',hc',hA'⟩
    · obtain ⟨p,_,hs⟩ := hc
      exact (ForcingWithTopCarrier.single_nonempty hs he).elim
    · obtain ⟨p,hp,hs⟩ := hc
      obtain ⟨p',hp',hs'⟩ := hc'
      have ep := ForcingWithTopCarrier.single_injective hs hs'
      subst p'
      obtain ⟨ei,ej⟩ := PureKuratowski.code_injective hp hp'
      subst i' j'
      exact value_unique hM ht hf hA hA'

/-- Totality uses actual family_realized, not a newly assumed stage family. -/
theorem value_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R i J j : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : ConstructionTowerHistory.Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hi : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hJ : PureKuratowski.PairMember M i J Indices)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J) :
    ∃ A, Value history outerF kappa V zero traces i j A := by
  have hik := function_input hi.1.1 hJ
  obtain ⟨code,hcode,_⟩ := ht.1.2 i hik
  obtain ⟨next,N,W,fromBase,after,J',Domains,E,F,L,Out,Images,hreal⟩ :=
    ConstructionBlockBoundary.family_realized hM hv hB hf hr ht i code hcode
  obtain ⟨Schedule,last,inner,Steps,Events,Roots,hpack,hchart,horder,hL,hstable,hresult,hend,htop⟩ := hreal.2.2.2.2.2.1
  have hJ' := ConstructionTowerHistory.chart_of_row 0 hi.1 hik ⟨code,hcode,hpack⟩
  have eJ : J = J' := function_unique hi.1.1 hJ hJ'
  subst J'
  obtain ⟨image,himage,_⟩ := hresult.2.2.2.2.1.1.2 j hj
  exact ⟨image,code,next,N,W,fromBase,after,J,Domains,E,F,L,Out,Images,hcode,hreal,himage⟩

theorem flatValue_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R c : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : ConstructionTowerHistory.Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hi : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c I) :
    ∃ image, FlatValue history outerF kappa V zero traces c image := by
  have hiCopy := hi
  obtain ⟨_,_,hA,_,_,hI,_,_⟩ := hiCopy
  rcases (hI c).mp hc with he | ⟨p,hp,hs⟩
  · exact ⟨V,Or.inl ⟨he,rfl⟩⟩
  · obtain ⟨i,J,j,_,hJ,hj,hcode⟩ := (hA p).mp hp
    obtain ⟨image,himage⟩ := value_total hM hv hB hf hr ht hi hJ hj
    exact ⟨image,Or.inr ⟨i,j,⟨p,hcode,hs⟩,himage⟩⟩

def value {m : Nat} (history outerF kappa V zero traces i j A : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  traces.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12)) (.conj
  (ConstructionBlockBoundary.realized
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 11 10 9 8 7 6 5 4 3 2 1 0)
  (ProjectSyntax.encode id (Source.SetLanguage.edge 0
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  A.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))

theorem value_freeClosed {m : Nat} (history outerF kappa V zero traces i j A : Fin m) :
    (value history outerF kappa V zero traces i j A).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionBlockBoundary.realized_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (history outerF kappa V zero traces i j A : Fin m) :
    Project.Formula.satisfies env (value history outerF kappa V zero traces i j A) ↔ Value (env.bound history) (env.bound outerF) (env.bound kappa) (env.bound V) (env.bound zero) (env.bound traces) (env.bound i) (env.bound j) (env.bound A) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBlockBoundary.realized_semantics hM]
  rfl

def flatValue {m : Nat} (history outerF kappa V zero traces c A : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (ProjectSyntax.encode id (ForcingWithTopCarrier.empty c)) (Project.Formula.extensionalEq
  (.bound A) (.bound V))) (.existsE (.existsE (.conj (ConstructionBlockCuts.cut 1 0 c.succ.succ) (value
  history.succ.succ outerF.succ.succ kappa.succ.succ V.succ.succ zero.succ.succ traces.succ.succ 1 0
  A.succ.succ)))))

theorem flatValue_freeClosed {m : Nat} (history outerF kappa V zero traces c A : Fin m) :
    (flatValue history outerF kappa V zero traces c A).FreeClosed := by
  simp -implicitDefEqProofs [flatValue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionBlockCuts.cut_freeClosed,value_freeClosed]

theorem flatValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (history outerF kappa V zero traces c A : Fin m) :
    Project.Formula.satisfies env (flatValue history outerF kappa V zero traces c A) ↔ FlatValue (env.bound history) (env.bound outerF) (env.bound kappa) (env.bound V) (env.bound zero) (env.bound traces) (env.bound c) (env.bound A) := by
  simp only [flatValue,FlatValue,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingWithTopCarrier.empty_semantics (M := M),ConstructionBlockCuts.cut_semantics hM,value_semantics hM]
  rfl

def graph {m : Nat} (history outerF kappa V zero traces I S : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn S I)) (.forallE (.forallE (.iff
  (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ 1 0)) (.conj (.mem (.bound 1) (.bound
  I.succ.succ)) (flatValue history.succ.succ outerF.succ.succ kappa.succ.succ V.succ.succ zero.succ.succ
  traces.succ.succ 1 0))))))

theorem graph_freeClosed {m : Nat} (history outerF kappa V zero traces I S : Fin m) :
    (graph history outerF kappa V zero traces I S).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,flatValue_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (history outerF kappa V zero traces I S : Fin m) :
    Project.Formula.satisfies env (graph history outerF kappa V zero traces I S) ↔ Graph (env.bound history) (env.bound outerF) (env.bound kappa) (env.bound V) (env.bound zero) (env.bound traces) (env.bound I) (env.bound S) := by
  simp only [graph,Graph,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics (M := M),flatValue_semantics hM]
  rfl

/-- Reuse the native internal functional-image and function constructors. -/
theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : ConstructionTowerHistory.Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hi : ConstructionBlockIndex.Data hM kappa traces Indices A r I R) :
    ∃ S, Graph history outerF kappa V zero traces I S := by
  let schema : Project.BinarySchema 6 := {
    body := flatValue 2 3 4 5 6 7 1 0
    freeClosed := flatValue_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases history (Fin.cases outerF (Fin.cases kappa (Fin.cases V (Fin.cases zero (fun _ => traces)))))
    free := fun _ => I }
  have he c image : schema.denote env c image ↔ FlatValue history outerF kappa V zero traces c image :=
    flatValue_semantics hM ((env.push c).push image) 2 3 4 5 6 7 1 0
  have htotal : ∀ c, (Project.FirstOrderSemantics.reduct M).mem c I → ∃ image, schema.denote env c image := by
    intro c hc
    obtain ⟨image,himage⟩ := flatValue_total hM hv hB hf hr ht hi hc
    exact ⟨image,(he c image).mpr himage⟩
  have hunique : ∀ c, (Project.FirstOrderSemantics.reduct M).mem c I → ∀ x y,
      schema.denote env c x → schema.denote env c y → x = y :=
    fun _ _ _ _ hx hy => flatValue_unique hM ht.1 hf.2.1 ((he _ _).mp hx) ((he _ _).mp hy)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨images,himages⟩ := ZF.exists_functionalImageOn hZF schema env I htotal hunique
  obtain ⟨S,hS,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    schema env htotal hunique (fun c image hc hv => (himages image).mpr ⟨c,hc,hv⟩)
  exact ⟨S,((ForcingSupportSize.native_mapsTo hM I images S).mpr hS).1,
    fun c image => (hgraph c image).trans (and_congr_right fun _ => he c image)⟩

/-- Literal source flatStage_cut, independently of auxiliary presentations. -/
theorem graph_cut {history outerF kappa V zero traces I S i j c A : M.Carrier .set}
    (hg : Graph history outerF kappa V zero traces I S) (hc : Cut i j c)
    (hcI : (Project.FirstOrderSemantics.reduct M).mem c I) :
    PureKuratowski.PairMember M c A S ↔ Value history outerF kappa V zero traces i j A := by
  constructor
  · intro hA
    rcases ((hg.2 c A).mp hA).2 with ⟨he,_⟩ | ⟨i',j',hc',hv⟩
    · obtain ⟨p,_,hs⟩ := hc
      exact (ForcingWithTopCarrier.single_nonempty hs he).elim
    · obtain ⟨p,hp,hs⟩ := hc
      obtain ⟨p',hp',hs'⟩ := hc'
      have ep := ForcingWithTopCarrier.single_injective hs hs'
      subst p'
      obtain ⟨ei,ej⟩ := PureKuratowski.code_injective hp hp'
      subst i' j'
      exact hv
  · intro hv
    exact (hg.2 c A).mpr ⟨hcI,Or.inr ⟨i,j,hc,hv⟩⟩

theorem graph_bounded {history outerF kappa V zero traces I S : M.Carrier .set}
    (hg : Graph history outerF kappa V zero traces I S) : ConstructionBlockStages.Bounded V S := by
  intro c image h x hx
  rcases ((hg.2 c image).mp h).2 with ⟨_,rfl⟩ | ⟨i,j,_,hv⟩
  · exact hx
  · exact value_bounded hv x hx

/-- Coverage here uses top itself. Strict earlier coverage AT top is separate. -/
def Result (history outerF kappa V zero traces I S : M.Carrier .set) : Prop :=
  Graph history outerF kappa V zero traces I S ∧ ConstructionBlockStages.Bounded V S ∧
    (∀ c, Empty (M := M) c → PureKuratowski.PairMember M c V S) ∧
    ∀ x, (Project.FirstOrderSemantics.reduct M).mem x V →
      ∃ c, (Project.FirstOrderSemantics.reduct M).mem c I ∧ ConstructionFirstAppearance.At S c x

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R : M.Carrier .set}
    (hv : ConstructionTowerValidity.Valid hM w Q values top D mul e mark H C B history)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : ConstructionTowerHistory.Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hi : ConstructionBlockIndex.Data hM kappa traces Indices A r I R) :
    ∃ S, Result history outerF kappa V zero traces I S := by
  obtain ⟨S,hS⟩ := exists_graph hM hv hB hf hr ht hi
  have hiCopy := hi
  obtain ⟨_,_,_,_,_,hI,_,_⟩ := hiCopy
  have htop : ∀ c, Empty (M := M) c → PureKuratowski.PairMember M c V S :=
    fun c hc => (hS.2 c V).mpr ⟨(hI c).mpr (Or.inl hc),Or.inl ⟨hc,rfl⟩⟩
  refine ⟨S,hS,graph_bounded hS,htop,?_⟩
  intro x hx
  obtain ⟨c,hc⟩ := ForcingWithTopCarrier.exists_empty hM
  exact ⟨c,(hI c).mpr (Or.inl hc),V,htop c hc,hx⟩

/-- Transport actual range membership in both directions, for EVERY
presentation of the same retained round, not merely a chosen representative. -/
theorem realized_at (hM : FirstOrder.Theory.Models M nativeZF)
    {P history outerF kappa V zero traces I S i j c code next N W fromBase after J Domains E F L Out Images x : M.Carrier .set}
    (ht : FunctionOn kappa traces) (hf : FunctionOn P outerF)
    (hg : Graph history outerF kappa V zero traces I S)
    (hc : Cut i j c) (hcI : (Project.FirstOrderSemantics.reduct M).mem c I)
    (hcode : PureKuratowski.PairMember M i code traces)
    (hr : Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J) :
    ConstructionFirstAppearance.At S c x ↔ ConstructionFirstAppearance.At Images j x := by
  constructor
  · rintro ⟨image,himage,hx⟩
    obtain ⟨Schedule,last,inner,Steps,Events,Roots,_,_,_,_,_,hresult,_,_⟩ := hr.2.2.2.2.2.1
    obtain ⟨image',himage',_⟩ := hresult.2.2.2.2.1.1.2 j hj
    have hv : Value history outerF kappa V zero traces i j image' :=
      ⟨code,next,N,W,fromBase,after,J,Domains,E,F,L,Out,Images,hcode,hr,himage'⟩
    have eq := value_unique hM ht hf ((graph_cut hg hc hcI).mp himage) hv
    subst image'
    exact ⟨image,himage',hx⟩
  · rintro ⟨image,himage,hx⟩
    exact ⟨image,(graph_cut hg hc hcI).mpr
      ⟨code,next,N,W,fromBase,after,J,Domains,E,F,L,Out,Images,hcode,hr,himage⟩,hx⟩

def result {m : Nat} (history outerF kappa V zero traces I S : Fin m) : Project.Formula 1 m :=
  (.conj (graph history outerF kappa V zero traces I S) (.conj (ConstructionBlockStages.bounded V S) (.conj
  (.forallE (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty 0)) (ProjectSyntax.encode id
  (Source.SetLanguage.edge S.succ 0 V.succ)))) (.forallE (.imp (.mem (.bound 0) (.bound V.succ)) (.existsE
  (.conj (.mem (.bound 0) (.bound I.succ.succ)) (ConstructionFirstAppearance.atStage S.succ.succ 0 1))))))))

theorem result_freeClosed {m : Nat} (history outerF kappa V zero traces I S : Fin m) :
    (result history outerF kappa V zero traces I S).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,graph_freeClosed,ConstructionBlockStages.bounded_freeClosed,ProjectSyntax.freeClosed,ConstructionFirstAppearance.atStage_freeClosed]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (history outerF kappa V zero traces I S : Fin m) :
    Project.Formula.satisfies env (result history outerF kappa V zero traces I S) ↔ Result (env.bound history) (env.bound outerF) (env.bound kappa) (env.bound V) (env.bound zero) (env.bound traces) (env.bound I) (env.bound S) := by
  simp only [result,Result,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,graph_semantics hM,ConstructionBlockStages.bounded_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingWithTopCarrier.empty_semantics (M := M),ConstructionFirstAppearance.atStage_semantics hM]
  rfl

def constructionSentence {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionTowerValidity.valid w Q values top D mul e mark H C B history) (.imp
    (Project.Formula.isSuccessor (.bound B) (.bound kappa)) (.imp (ConstructionTowerTransitions.matrix B
    history zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V mulV unitV markV HV CV
    terminalLegs baseV kappa) (.imp (ConstructionBlockTraces.family w Q values top zero one K mu history
    outerF kappa traces) (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R) (.existsE (result
    history.succ outerF.succ kappa.succ V.succ zero.succ traces.succ I.succ 0))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerValidity.valid_freeClosed,Project.Formula.isSuccessor,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,result_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R : Fin m) : (Project.fo_sentence (constructionSentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,ConstructionTowerValidity.valid_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,result_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (constructionSentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R)) := by
  apply ModelTransfer.derives
  intro M hM
  exact construction_models hM w Q values top D mul e mark H C zero one K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV traces Indices A r I R

def transportSentence {m : Nat} (P history outerF kappa V zero traces I S i j c code next N W fromBase after J Domains E F L Out Images x : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn traces kappa)) (.imp (ProjectSyntax.encode
    id (Source.SetLanguage.functionOn outerF P)) (.imp (graph history outerF kappa V zero traces I S) (.imp
    (ConstructionBlockCuts.cut i j c) (.imp (.mem (.bound c) (.bound I)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge traces i code)) (.imp (ConstructionBlockBoundary.realized history outerF kappa
    V zero i code next N W fromBase after J Domains E F L Out Images) (.imp (.mem (.bound j) (.bound J))
    (.iff (ConstructionFirstAppearance.atStage S c x) (ConstructionFirstAppearance.atStage Images j
    x))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,graph_freeClosed,ConstructionBlockCuts.cut_freeClosed,ConstructionBlockBoundary.realized_freeClosed,ConstructionFirstAppearance.atStage_freeClosed]

theorem transport_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (P history outerF kappa V zero traces I S i j c code next N W fromBase after J Domains E F L Out Images x : Fin m) : (Project.fo_sentence (transportSentence P history outerF kappa V zero traces I S i j c code next N W fromBase after J Domains E F L Out Images x)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (transportSentence P history outerF kappa V zero traces I S i j c code next N W fromBase after J Domains E F L Out Images x)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics (M := M),graph_semantics hM,ConstructionBlockCuts.cut_semantics hM,ConstructionBlockBoundary.realized_semantics hM,ConstructionFirstAppearance.atStage_semantics hM]
  exact realized_at hM

theorem transport_kernel_certificate {m : Nat} (P history outerF kappa V zero traces I S i j c code next N W fromBase after J Domains E F L Out Images x : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (transportSentence P history outerF kappa V zero traces I S i j c code next N W fromBase after J Domains E F L Out Images x)) := by
  apply ModelTransfer.derives
  intro M hM
  exact transport_models hM P history outerF kappa V zero traces I S i j c code next N W fromBase after J Domains E F L Out Images x

end PPAC.Migration.ConstructionFlatStages
