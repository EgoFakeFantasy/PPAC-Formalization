/- Pinned MonoidTowers.ConstructionIteration.structureWithTime and
MonoidRounds.Round.fromBase_naturality: extract the ACTUAL nine field tables
from a set-coded history of the accepted stage packets. No new codec,
recursor, external sequence indexing, or choice of stage components. -/
import PPAC.Migration.ConstructionTowerCanonicalSuccessor

namespace PPAC.Migration.ConstructionTowerHistory
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (FunctionOn function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Row (S i D mul e mark H C incoming base time : M.Carrier .set) : Prop :=
  ∃ code, PureKuratowski.PairMember M i code S ∧
    ConstructionRoundSelection.Pack D mul e mark H C incoming base time code

/-- Only the record and its literal internal time are required here.
Algebraic/transition validity is a separate, stronger invariant. -/
def Records (J S : M.Carrier .set) : Prop :=
  FunctionOn J S ∧ ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J →
    ∃ D mul e mark H C incoming base, Row S i D mul e mark H C incoming base i

def Field (k : Fin 9) (S i value : M.Carrier .set) : Prop :=
  ∃ D mul e mark H C incoming base time,
    Row S i D mul e mark H C incoming base time ∧
    value = match k.val with
      | 0 => D | 1 => mul | 2 => e | 3 => mark | 4 => H
      | 5 => C | 6 => incoming | 7 => base | _ => time

def Chart (k : Fin 9) (J S graph : M.Carrier .set) : Prop :=
  FunctionOn J graph ∧ ∀ i value, PureKuratowski.PairMember M i value graph ↔
    (Project.FirstOrderSemantics.reduct M).mem i J ∧ Field k S i value

def Charts (J S Domains Muls Units Marks Heights Costs Incoming Origins Times : M.Carrier .set) : Prop :=
  Chart 0 J S Domains ∧ Chart 1 J S Muls ∧ Chart 2 J S Units ∧
  Chart 3 J S Marks ∧ Chart 4 J S Heights ∧ Chart 5 J S Costs ∧
  Chart 6 J S Incoming ∧ Chart 7 J S Origins ∧ Chart 8 J S Times

theorem row_unique {J S i D mul e mark H C incoming base time
    D' mul' e' mark' H' C' incoming' base' time' : M.Carrier .set}
    (hS : FunctionOn J S)
    (h1 : Row S i D mul e mark H C incoming base time)
    (h2 : Row S i D' mul' e' mark' H' C' incoming' base' time') :
    D = D' ∧ mul = mul' ∧ e = e' ∧ mark = mark' ∧ H = H' ∧ C = C' ∧
      incoming = incoming' ∧ base = base' ∧ time = time' := by
  obtain ⟨code,hc,hp⟩ := h1
  obtain ⟨code',hc',hp'⟩ := h2
  have he := function_unique hS hc hc'
  subst code'
  exact ConstructionRoundSelection.pack_injective hp hp'

theorem field_total {J S i : M.Carrier .set} (k : Fin 9)
    (hS : Records J S) (hi : (Project.FirstOrderSemantics.reduct M).mem i J) :
    ∃ value, Field k S i value := by
  obtain ⟨D,mul,e,mark,H,C,incoming,base,hR⟩ := hS.2 i hi
  exact ⟨_,D,mul,e,mark,H,C,incoming,base,i,hR,rfl⟩

theorem field_unique {J S i x y : M.Carrier .set} (k : Fin 9)
    (hS : FunctionOn J S) (hx : Field k S i x) (hy : Field k S i y) : x = y := by
  obtain ⟨D,mul,e,mark,H,C,incoming,base,time,hR,rfl⟩ := hx
  obtain ⟨D',mul',e',mark',H',C',incoming',base',time',hR',rfl⟩ := hy
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := row_unique hS hR hR'
  rfl

theorem time_field {J S i value : M.Carrier .set}
    (hS : Records J S) (hi : (Project.FirstOrderSemantics.reduct M).mem i J) :
    Field 8 S i value ↔ value = i := by
  obtain ⟨D,mul,e,mark,H,C,incoming,base,hR⟩ := hS.2 i hi
  have hf : Field 8 S i i := ⟨D,mul,e,mark,H,C,incoming,base,i,hR,rfl⟩
  exact ⟨fun hv => field_unique 8 hS.1 hv hf,fun he => he ▸ hf⟩

def row {m : Nat} (S i D mul e mark H C incoming base time : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ i.succ (0 : Fin (m+1))))
  (ConstructionRoundSelection.pack D.succ mul.succ e.succ mark.succ H.succ C.succ incoming.succ base.succ
  time.succ (0 : Fin (m+1)))))

theorem row_freeClosed {m : Nat} (S i D mul e mark H C incoming base time : Fin m) :
    (row S i D mul e mark H C incoming base time).FreeClosed := by
  simp -implicitDefEqProofs [row,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRoundSelection.pack_freeClosed]

theorem row_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S i D mul e mark H C incoming base time : Fin m) :
    Project.Formula.satisfies env (row S i D mul e mark H C incoming base time) ↔ Row (env.bound S) (env.bound i) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound incoming) (env.bound base) (env.bound time) := by
  simp only [row,Row,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionRoundSelection.pack_semantics hM]
  rfl


def records {m : Nat} (J S : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn S J)) (.forallE (.imp (.mem (.bound (0 : Fin
  (m+1))) (.bound J.succ)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (row S.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)) (7 : Fin (m+9)) (6 : Fin (m+9)) (5 :
  Fin (m+9)) (4 : Fin (m+9)) (3 : Fin (m+9)) (2 : Fin (m+9)) (1 : Fin (m+9)) (0 : Fin (m+9)) (8 : Fin
  (m+9))))))))))))))

theorem records_freeClosed {m : Nat} (J S : Fin m) :
    (records J S).FreeClosed := by
  simp -implicitDefEqProofs [records,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,row_freeClosed]

theorem records_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J S : Fin m) :
    Project.Formula.satisfies env (records J S) ↔ Records (env.bound J) (env.bound S) := by
  simp only [records,Records,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.functionOn_semantics (M := M),row_semantics hM]
  rfl


def field (k : Fin 9) {m : Nat} (S i value : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (row
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
  (m+9)) (7 : Fin (m+9)) (6 : Fin (m+9)) (5 : Fin (m+9)) (4 : Fin (m+9)) (3 : Fin (m+9)) (2 : Fin (m+9)) (1
  : Fin (m+9)) (0 : Fin (m+9))) (Project.Formula.extensionalEq (.bound
  value.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.bound (match k.val with
    | 0 => (8 : Fin (m+9))
    | 1 => (7 : Fin (m+9))
    | 2 => (6 : Fin (m+9))
    | 3 => (5 : Fin (m+9))
    | 4 => (4 : Fin (m+9))
    | 5 => (3 : Fin (m+9))
    | 6 => (2 : Fin (m+9))
    | 7 => (1 : Fin (m+9))
    | _ => (0 : Fin (m+9)))))))))))))))

theorem field_freeClosed (k : Fin 9) {m : Nat} (S i value : Fin m) :
    (field k S i value).FreeClosed := by
  simp -implicitDefEqProofs [field,Definitional.Formula.FreeClosed,row_freeClosed,
    Project.Formula.extensionalEq]

theorem field_semantics (hM : FirstOrder.Theory.Models M nativeZF) (k : Fin 9) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S i value : Fin m) :
    Project.Formula.satisfies env (field k S i value) ↔
      Field k (env.bound S) (env.bound i) (env.bound value) := by
  rcases k with ⟨k,hk⟩
  have hs : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases hs with h | h | h | h | h | h | h | h | h
  all_goals
    subst k
    simp only [field,Field,Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff,row_semantics hM,
      Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
      Project.Term.eval_bound]
    rfl


def chart (k : Fin 9) {m : Nat} (J S graph : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn graph J)) (.forallE (.forallE (.iff
  (ProjectSyntax.encode id (Source.SetLanguage.edge graph.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (.conj
  (.mem (.bound (1 : Fin (m+2))) (.bound J.succ.succ)) (field k S.succ.succ (1 : Fin (m+2)) (0 : Fin
  (m+2))))))))

theorem chart_freeClosed (k : Fin 9) {m : Nat} (J S graph : Fin m) :
    (chart k J S graph).FreeClosed := by
  simp -implicitDefEqProofs [chart,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,field_freeClosed]

theorem chart_semantics (hM : FirstOrder.Theory.Models M nativeZF) (k : Fin 9) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J S graph : Fin m) :
    Project.Formula.satisfies env (chart k J S graph) ↔ Chart k (env.bound J) (env.bound S) (env.bound graph) := by
  simp only [chart,Chart,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics (M := M),field_semantics hM]
  rfl


def charts {m : Nat} (J S Domains Muls Units Marks Heights Costs Incoming Origins Times : Fin m) : Project.Formula 1 m :=
  (.conj (chart 0 J S Domains) (.conj (chart 1 J S Muls) (.conj (chart 2 J S Units) (.conj (chart 3 J S Marks)
  (.conj (chart 4 J S Heights) (.conj (chart 5 J S Costs) (.conj (chart 6 J S Incoming) (.conj (chart 7 J S
  Origins) (chart 8 J S Times)))))))))

theorem charts_freeClosed {m : Nat} (J S Domains Muls Units Marks Heights Costs Incoming Origins Times : Fin m) :
    (charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times).FreeClosed := by
  simp -implicitDefEqProofs [charts,Definitional.Formula.FreeClosed,chart_freeClosed]

theorem charts_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J S Domains Muls Units Marks Heights Costs Incoming Origins Times : Fin m) :
    Project.Formula.satisfies env (charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times) ↔ Charts (env.bound J) (env.bound S) (env.bound Domains) (env.bound Muls) (env.bound Units) (env.bound Marks) (env.bound Heights) (env.bound Costs) (env.bound Incoming) (env.bound Origins) (env.bound Times) := by
  simp only [charts,Charts,
    Project.Formula.satisfies_conj_iff,
    
    chart_semantics hM]


theorem exists_chart (hM : FirstOrder.Theory.Models M nativeZF) (k : Fin 9)
    {J S : M.Carrier .set} (hS : Records J S) :
    ∃ graph, Chart k J S graph := by
  let schema : Project.BinarySchema 1 := {
    body := field k 2 1 0
    freeClosed := field_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := {
    bound := fun _ => S
    free := fun _ => J }
  have he (i value) : schema.denote env i value ↔ Field k S i value :=
    field_semantics hM k ((env.push i).push value) 2 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J →
      ∃ value, schema.denote env i value := by
    intro i hi
    obtain ⟨value,hv⟩ := field_total k hS hi
    exact ⟨value,(he i value).mpr hv⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∀ x y,
      schema.denote env i x → schema.denote env i y → x = y :=
    fun _ _ _ _ hx hy => field_unique k hS.1 ((he _ _).mp hx) ((he _ _).mp hy)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema env J ht hu
  obtain ⟨graph,hg,hG⟩ := ZF.exists_setFunctionFromTo_of_denote hZF
    (KuratowskiZF.interpretation hM) schema env ht hu
    (fun i value hi hv => (hA value).mpr ⟨i,hi,hv⟩)
  exact ⟨graph,((ForcingSupportSize.native_mapsTo hM J A graph).mpr hg).1,
    fun i value => (hG i value).trans (and_congr_right fun _ => he i value)⟩

theorem chart_unique (hM : FirstOrder.Theory.Models M nativeZF) (k : Fin 9)
    {J S graph graph' : M.Carrier .set}
    (hg : Chart k J S graph) (hg' : Chart k J S graph') : graph = graph' := by
  have rel {f} (hf : FunctionOn J f) :
      (Project.FirstOrderSemantics.reduct M).IsSetRelation (KuratowskiZF.interpretation hM) f := by
    intro p hp
    obtain ⟨x,y,_,hc⟩ := hf.1 p hp
    exact ⟨x,y,hc⟩
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    (rel hg.1) (rel hg'.1) (fun i value => (hg.2 i value).trans (hg'.2 i value).symm)

theorem time_identity {J S Times : M.Carrier .set}
    (hS : Records J S) (ht : Chart 8 J S Times) :
    ForcingConditionGraphs.IdentityGraph J Times := by
  intro i value
  exact (ht.2 i value).trans (and_congr_right fun hi => (time_field hS hi).trans eq_comm)

theorem exists_charts (hM : FirstOrder.Theory.Models M nativeZF)
    {J S : M.Carrier .set} (hS : Records J S) :
    ∃ Domains Muls Units Marks Heights Costs Incoming Origins Times,
      Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times ∧
      ForcingConditionGraphs.IdentityGraph J Times := by
  obtain ⟨Domains,hDomains⟩ := exists_chart hM 0 hS
  obtain ⟨Muls,hMuls⟩ := exists_chart hM 1 hS
  obtain ⟨Units,hUnits⟩ := exists_chart hM 2 hS
  obtain ⟨Marks,hMarks⟩ := exists_chart hM 3 hS
  obtain ⟨Heights,hHeights⟩ := exists_chart hM 4 hS
  obtain ⟨Costs,hCosts⟩ := exists_chart hM 5 hS
  obtain ⟨Incoming,hIncoming⟩ := exists_chart hM 6 hS
  obtain ⟨Origins,hOrigins⟩ := exists_chart hM 7 hS
  obtain ⟨Times,hTimes⟩ := exists_chart hM 8 hS
  exact ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,⟨hDomains,hMuls,hUnits,hMarks,hHeights,hCosts,hIncoming,hOrigins,hTimes⟩,time_identity hS hTimes⟩

theorem chart_of_row (k : Fin 9)
    {J S graph i D mul e mark H C incoming base time : M.Carrier .set}
    (hChart : Chart k J S graph)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hRow : Row S i D mul e mark H C incoming base time) :
    PureKuratowski.PairMember M i
      (match k.val with
        | 0 => D | 1 => mul | 2 => e | 3 => mark | 4 => H
        | 5 => C | 6 => incoming | 7 => base | _ => time) graph :=
  (hChart.2 i _).mpr ⟨hi,D,mul,e,mark,H,C,incoming,base,time,hRow,rfl⟩

theorem charts_row
    {J S Domains Muls Units Marks Heights Costs Incoming Origins Times
      i D mul e mark H C incoming base time : M.Carrier .set}
    (hCharts : Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hRow : Row S i D mul e mark H C incoming base time) :
    PureKuratowski.PairMember M i D Domains ∧ PureKuratowski.PairMember M i mul Muls ∧
    PureKuratowski.PairMember M i e Units ∧ PureKuratowski.PairMember M i mark Marks ∧
    PureKuratowski.PairMember M i H Heights ∧ PureKuratowski.PairMember M i C Costs ∧
    PureKuratowski.PairMember M i incoming Incoming ∧ PureKuratowski.PairMember M i base Origins ∧
    PureKuratowski.PairMember M i time Times := by
  obtain ⟨hD,hm,he,hmark,hH,hC,hI,hO,hT⟩ := hCharts
  exact ⟨chart_of_row 0 hD hi hRow,chart_of_row 1 hm hi hRow,
    chart_of_row 2 he hi hRow,chart_of_row 3 hmark hi hRow,chart_of_row 4 hH hi hRow,
    chart_of_row 5 hC hi hRow,chart_of_row 6 hI hi hRow,chart_of_row 7 hO hi hRow,
    chart_of_row 8 hT hi hRow⟩

/-- All displayed graph values decode ONE AND THE SAME saved packet.
This supplies the original full successor/limit parent field arguments. -/
theorem charts_decode
    {J S Domains Muls Units Marks Heights Costs Incoming Origins Times
      i D mul e mark H C incoming base time : M.Carrier .set}
    (hS : Records J S)
    (hCharts : Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains)
    (hm : PureKuratowski.PairMember M i mul Muls)
    (he : PureKuratowski.PairMember M i e Units)
    (hmark : PureKuratowski.PairMember M i mark Marks)
    (hH : PureKuratowski.PairMember M i H Heights)
    (hC : PureKuratowski.PairMember M i C Costs)
    (hI : PureKuratowski.PairMember M i incoming Incoming)
    (hO : PureKuratowski.PairMember M i base Origins)
    (hT : PureKuratowski.PairMember M i time Times) :
    Row S i D mul e mark H C incoming base time ∧ time = i := by
  obtain ⟨D',mul',e',mark',H',C',incoming',base',hRow⟩ := hS.2 i hi
  obtain ⟨hD',hm',he',hmark',hH',hC',hI',hO',hT'⟩ := charts_row hCharts hi hRow
  obtain ⟨cD,cm,ce,cmark,cH,cC,cI,cO,cT⟩ := hCharts
  have eD := function_unique cD.1 hD hD'
  have em := function_unique cm.1 hm hm'
  have ee := function_unique ce.1 he he'
  have emark := function_unique cmark.1 hmark hmark'
  have eH := function_unique cH.1 hH hH'
  have eC := function_unique cC.1 hC hC'
  have eI := function_unique cI.1 hI hI'
  have eO := function_unique cO.1 hO hO'
  have eT := function_unique cT.1 hT hT'
  subst D; subst mul; subst e; subst mark; subst H; subst C; subst incoming; subst base; subst time
  exact ⟨hRow,rfl⟩


theorem records_restrict {J S J' S' : M.Carrier .set}
    (hS : Records J S) (hFn : FunctionOn J' S')
    (hJ : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J' →
      (Project.FirstOrderSemantics.reduct M).mem i J)
    (hEdge : ∀ i code, (Project.FirstOrderSemantics.reduct M).mem i J' →
      (PureKuratowski.PairMember M i code S' ↔ PureKuratowski.PairMember M i code S)) :
    Records J' S' := by
  refine ⟨hFn,fun i hi => ?_⟩
  obtain ⟨D,mul,e,mark,H,C,incoming,base,code,hc,hp⟩ := hS.2 i (hJ i hi)
  exact ⟨D,mul,e,mark,H,C,incoming,base,code,(hEdge i code hi).mpr hc,hp⟩


def extractionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 2 (.imp (records (0 : Fin 2) (1 : Fin 2)) (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (charts (0 : Fin
    2).succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    2).succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin 11) (7 : Fin 11) (6 : Fin 11) (5 : Fin 11)
    (4 : Fin 11) (3 : Fin 11) (2 : Fin 11) (1 : Fin 11) (0 : Fin 11)) (ProjectSyntax.encode id
    (ForcingConditionGraphs.identityGraph (0 : Fin 2).succ.succ.succ.succ.succ.succ.succ.succ.succ (0 :
    Fin 11)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,records_freeClosed,charts_freeClosed,
      ProjectSyntax.freeClosed]

theorem extraction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence extractionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) extractionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,records_semantics hM,charts_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.identityGraph_semantics (M := M)]
  exact fun hS => exists_charts hM hS

theorem extraction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence extractionSentence) := ModelTransfer.derives (fun _ hM => extraction_models hM)

end PPAC.Migration.ConstructionTowerHistory
