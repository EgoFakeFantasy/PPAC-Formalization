/- Fixed OrbitAssignments.Assigned auxiliary functions. Project the SAME actual
record chosen by ForcingOrbitParameterFamily; reuse existing reps/chains and
native definable function graphs. No new choices of independent witnesses. -/
import PPAC.Migration.ForcingOrbitParameterFamily
import PPAC.Migration.ForcingAssigned

namespace PPAC.Migration.ForcingAssignedParameterFields
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (FunctionOn function_unique function_input)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (j : Fin 16) (high output value : M.Carrier .set) : Prop :=
  ∃ root chain r index U labelSet codes order group support fixing ranks selection rankBound tab germGroup quotient projection reps N X detector J patternCarrier patternOrder selectorDomain selector packA packB packC,
    ConstructionRoundSelection.Pack root chain r index U labelSet codes order group packA ∧
    ConstructionRoundSelection.Pack support fixing ranks selection rankBound tab germGroup quotient projection packB ∧
    ConstructionRoundSelection.Pack reps N X detector J patternCarrier patternOrder selectorDomain selector packC ∧
    ConstructionComponentCarrier.Code output packA packB packC ∧
    value = match j.val with
      | 0 => root
      | 1 => chain
      | 2 => codes
      | 3 => order
      | 4 => ranks
      | 5 => selection
      | 6 => rankBound
      | 7 => labelSet
      | 8 => tab
      | 9 => r
      | 10 => germGroup
      | 11 => quotient
      | 12 => N
      | 13 => high
      | 14 => detector
      | _ => patternOrder

theorem value_intro (j : Fin 16) (high output root chain r index U labelSet codes order group support fixing ranks selection rankBound tab germGroup quotient projection reps N X detector J patternCarrier patternOrder selectorDomain selector packA packB packC : M.Carrier .set)
    (hA : ConstructionRoundSelection.Pack root chain r index U labelSet codes order group packA)
    (hB : ConstructionRoundSelection.Pack support fixing ranks selection rankBound tab germGroup quotient projection packB)
    (hC : ConstructionRoundSelection.Pack reps N X detector J patternCarrier patternOrder selectorDomain selector packC)
    (hCode : ConstructionComponentCarrier.Code output packA packB packC) :
    Value j high output (match j.val with
      | 0 => root
      | 1 => chain
      | 2 => codes
      | 3 => order
      | 4 => ranks
      | 5 => selection
      | 6 => rankBound
      | 7 => labelSet
      | 8 => tab
      | 9 => r
      | 10 => germGroup
      | 11 => quotient
      | 12 => N
      | 13 => high
      | 14 => detector
      | _ => patternOrder) :=
  ⟨root,chain,r,index,U,labelSet,codes,order,group,support,fixing,ranks,selection,rankBound,tab,germGroup,quotient,projection,reps,N,X,detector,J,patternCarrier,patternOrder,selectorDomain,selector,packA,packB,packC,hA,hB,hC,hCode,rfl⟩

theorem value_unique (j : Fin 16) {high output x y : M.Carrier .set}
    (hx : Value j high output x) (hy : Value j high output y) : x = y := by
  obtain ⟨root,chain,r,index,U,labelSet,codes,order,group,support,fixing,ranks,selection,rankBound,tab,germGroup,quotient,projection,reps,N,X,detector,J,patternCarrier,patternOrder,selectorDomain,selector,packA,packB,packC,hA,hB,hC,hCode,hx⟩ := hx
  obtain ⟨root',chain',r',index',U',labelSet',codes',order',group',support',fixing',ranks',selection',rankBound',tab',germGroup',quotient',projection',reps',N',X',detector',J',patternCarrier',patternOrder',selectorDomain',selector',packA',packB',packC',hA',hB',hC',hCode',hy⟩ := hy
  obtain ⟨eA,eB,eC⟩ := ConstructionComponentCarrier.code_injective hCode hCode'
  have ha := ConstructionRoundSelection.pack_injective hA (eA.symm ▸ hA')
  have hb := ConstructionRoundSelection.pack_injective hB (eB.symm ▸ hB')
  have hc := ConstructionRoundSelection.pack_injective hC (eC.symm ▸ hC')
  obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7,e8⟩ := ha
  obtain ⟨e9,e10,e11,e12,e13,e14,e15,e16,e17⟩ := hb
  obtain ⟨e18,e19,e20,e21,e22,e23,e24,e25,e26⟩ := hc
  apply hx.trans
  simpa only [e0,e1,e6,e7,e11,e12,e13,e5,e14,e2,e15,e16,e19,e21,e24] using hy.symm

def value (j : Fin 16) {m : Nat} (high output value : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+30) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj (ConstructionRoundSelection.pack 29 28 27 26 25 24 23 22 21 2)
    (.conj (ConstructionRoundSelection.pack 20 19 18 17 16 15 14 13 12 1)
    (.conj (ConstructionRoundSelection.pack 11 10 9 8 7 6 5 4 3 0)
    (.conj (ConstructionComponentCarrier.code (up output) 2 1 0)
    (Project.Formula.extensionalEq (.bound (up value)) (.bound (match j.val with
      | 0 => 29
      | 1 => 28
      | 2 => 23
      | 3 => 22
      | 4 => 18
      | 5 => 17
      | 6 => 16
      | 7 => 24
      | 8 => 15
      | 9 => 27
      | 10 => 14
      | 11 => 13
      | 12 => 10
      | 13 => (up high)
      | 14 => 8
      | _ => 5)))))))))))))))))))))))))))))))))))))

theorem value_freeClosed (j : Fin 16) {m : Nat} (high output v : Fin m) :
    (value j high output v).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,
    ConstructionRoundSelection.pack_freeClosed,ConstructionComponentCarrier.code_freeClosed,
    Project.Formula.extensionalEq]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) (j : Fin 16) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (high output v : Fin m) :
    Project.Formula.satisfies env (value j high output v) ↔ Value j (env.bound high) (env.bound output) (env.bound v) := by
  rcases j with ⟨j,hj⟩
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    subst j
    simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      ConstructionRoundSelection.pack_semantics hM,ConstructionComponentCarrier.code_semantics hM,
      Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
    rfl

theorem record_values (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero root chain names high objects maps : Fin k)
    {output : M.Carrier .set}
    (h : ForcingOrbitParameterRecord.Record hM env rho I K B w G F mul q bound labels E zero root chain names high objects maps output) :
    (∀ j : Fin 16, ∃ v, Value j (env high) output v) ∧
      Value 0 (env high) output (env root) ∧ Value 1 (env high) output (env chain) := by
  obtain ⟨r,index,U,labelSet,codes,order,group,support,fixing,ranks,selection,rankBound,tab,germGroup,quotient,projection,reps,N,X,detector,J,patternCarrier,patternOrder,selectorDomain,selector,packA,packB,packC,hA,hB,hC,hCode,_⟩ := h
  have hv (j : Fin 16) := value_intro j (env high) output (env root) (env chain) r index U labelSet codes order group support fixing ranks selection rankBound tab germGroup quotient projection reps N X detector J patternCarrier patternOrder selectorDomain selector packA packB packC hA hB hC hCode
  exact ⟨fun j => ⟨_,hv j⟩,hv 0,hv 1⟩

def Field (j : Fin 16) (high records a v : M.Carrier .set) : Prop :=
  ∃ output, PureKuratowski.PairMember M a output records ∧ Value j high output v

def field (j : Fin 16) {m : Nat} (high records a v : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge records.succ a.succ 0))
    (value j high.succ 0 v.succ))

theorem field_freeClosed (j : Fin 16) {m : Nat} (high records a v : Fin m) :
    (field j high records a v).FreeClosed := by
  simp -implicitDefEqProofs [field,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem field_semantics (hM : FirstOrder.Theory.Models M nativeZF) (j : Fin 16) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (high records a v : Fin m) :
    Project.Formula.satisfies env (field j high records a v) ↔
      Field j (env.bound high) (env.bound records) (env.bound a) (env.bound v) := by
  simp only [field,Field,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM]
  rfl

theorem field_unique (j : Fin 16) {high records Q a x y : M.Carrier .set}
    (h : FunctionOn Q records) (hx : Field j high records a x) (hy : Field j high records a y) : x = y := by
  obtain ⟨output,hOutput,hx⟩ := hx
  obtain ⟨other,hOther,hy⟩ := hy
  have e := function_unique h hOutput hOther
  exact value_unique j hx (e.symm ▸ hy)

def Projection (j : Fin 16) (high Q records graph : M.Carrier .set) : Prop :=
  FunctionOn Q graph ∧ ∀ a v, PureKuratowski.PairMember M a v graph ↔
    (Project.FirstOrderSemantics.reduct M).mem a Q ∧ Field j high records a v

def projection (j : Fin 16) {m : Nat} (high Q records graph : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn graph Q))
    (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge graph.succ.succ 1 0))
      (.conj (.mem (.bound 1) (.bound Q.succ.succ)) (field j high.succ.succ records.succ.succ 1 0)))))

theorem projection_freeClosed (j : Fin 16) {m : Nat} (high Q records graph : Fin m) :
    (projection j high Q records graph).FreeClosed := by
  simp -implicitDefEqProofs [projection,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,field_freeClosed]

theorem projection_semantics (hM : FirstOrder.Theory.Models M nativeZF) (j : Fin 16) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (high Q records graph : Fin m) :
    Project.Formula.satisfies env (projection j high Q records graph) ↔
      Projection j (env.bound high) (env.bound Q) (env.bound records) (env.bound graph) := by
  simp only [projection,Projection,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingConditionGraphs.functionOn_semantics (M := M),field_semantics hM]
  rfl

theorem exists_projection (hM : FirstOrder.Theory.Models M nativeZF) (j : Fin 16) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient : Fin k)
    {records : M.Carrier .set}
    (hFamily : ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records) :
    ∃ graph, Projection j (env high) (env orbitQuotient) records graph := by
  let schema : Project.BinarySchema 2 := { body := field j 2 3 1 0, freeClosed := field_freeClosed .. }
  let e : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := { bound := Fin.cases (env high) (fun _ => records), free := fun _ => records }
  have he a v : schema.denote e a v ↔ Field j (env high) records a v :=
    field_semantics hM j ((e.push a).push v) 2 3 1 0
  have ht : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a (env orbitQuotient) → ∃ v, schema.denote e a v := by
    intro a ha
    obtain ⟨output,hOutput,_⟩ := hFamily.1.2 a ha
    obtain ⟨root,chain,_,_,hRecord⟩ := hFamily.2 a output hOutput
    obtain ⟨v,hv⟩ := (record_values hM (Fin.cases chain (Fin.cases root env)) (fun i => (rho i).succ.succ)
      I.succ.succ K.succ.succ B.succ.succ w.succ.succ G.succ.succ F.succ.succ mul.succ.succ q.succ.succ bound.succ.succ labels.succ.succ E.succ.succ zero.succ.succ 1 0 names.succ.succ high.succ.succ objects.succ.succ maps.succ.succ hRecord).1 j
    exact ⟨v,(he a v).mpr ⟨output,hOutput,hv⟩⟩
  have hu : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a (env orbitQuotient) → ∀ x y,
      schema.denote e a x → schema.denote e a y → x = y :=
    fun _ _ _ _ hx hy => field_unique j hFamily.1 ((he _ _).mp hx) ((he _ _).mp hy)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema e (env orbitQuotient) ht hu
  obtain ⟨graph,hg,hG⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM) schema e ht hu
    (fun a v ha hv => (hA v).mpr ⟨a,ha,hv⟩)
  exact ⟨graph,((ForcingSupportSize.native_mapsTo hM (env orbitQuotient) A graph).mpr hg).1,
    fun a v => (hG a v).trans (and_congr_right fun _ => he a v)⟩

theorem projection_of_graph (j : Fin 16) {high Q records graph : M.Carrier .set}
    (hRecords : FunctionOn Q records) (hGraph : FunctionOn Q graph)
    (hValue : ∀ a output, PureKuratowski.PairMember M a output records →
      ∃ v, PureKuratowski.PairMember M a v graph ∧ Value j high output v) :
    Projection j high Q records graph := by
  refine ⟨hGraph,fun a v => ?_⟩
  constructor
  · intro hav
    have ha := function_input hGraph hav
    obtain ⟨output,hOutput,_⟩ := hRecords.2 a ha
    obtain ⟨v',hav',hv'⟩ := hValue a output hOutput
    have e := function_unique hGraph hav' hav
    exact ⟨ha,output,hOutput,e ▸ hv'⟩
  · rintro ⟨_,output,hOutput,hv⟩
    obtain ⟨v',hav',hv'⟩ := hValue a output hOutput
    have e := value_unique j hv' hv
    exact e ▸ hav'

theorem existing_projections (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient : Fin k)
    {records : M.Carrier .set}
    (hFamily : ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records)
    (hReps : FunctionOn (env orbitQuotient) (env reps)) (hChains : FunctionOn (env orbitQuotient) (env chains)) :
    Projection 0 (env high) (env orbitQuotient) records (env reps) ∧
      Projection 1 (env high) (env orbitQuotient) records (env chains) := by
  have hValues a output (hOutput : PureKuratowski.PairMember M a output records) := hFamily.2 a output hOutput
  constructor
  · apply projection_of_graph 0 hFamily.1 hReps
    intro a output hOutput
    obtain ⟨root,chain,hRoot,hChain,hRecord⟩ := hValues a output hOutput
    have hv := record_values hM (Fin.cases chain (Fin.cases root env)) (fun i => (rho i).succ.succ)
      I.succ.succ K.succ.succ B.succ.succ w.succ.succ G.succ.succ F.succ.succ mul.succ.succ q.succ.succ bound.succ.succ labels.succ.succ E.succ.succ zero.succ.succ 1 0 names.succ.succ high.succ.succ objects.succ.succ maps.succ.succ hRecord
    exact ⟨root,hRoot,hv.2.1⟩
  · apply projection_of_graph 1 hFamily.1 hChains
    intro a output hOutput
    obtain ⟨root,chain,hRoot,hChain,hRecord⟩ := hValues a output hOutput
    have hv := record_values hM (Fin.cases chain (Fin.cases root env)) (fun i => (rho i).succ.succ)
      I.succ.succ K.succ.succ B.succ.succ w.succ.succ G.succ.succ F.succ.succ mul.succ.succ q.succ.succ bound.succ.succ labels.succ.succ E.succ.succ zero.succ.succ 1 0 names.succ.succ high.succ.succ objects.succ.succ maps.succ.succ hRecord
    exact ⟨chain,hChain,hv.2.2⟩

end PPAC.Migration.ForcingAssignedParameterFields
