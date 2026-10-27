/- Pinned CompleteRounds.Round.probe / probe_transition / CompleteRound.probe.
The actual selected execution/root graphs define ONE probe at each eligible
position and cut. Internal Separation/function construction, no new selector. -/
import PPAC.Migration.ConstructionTowerExecution

namespace PPAC.Migration.ConstructionTowerProbeFamily
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerExecution (StepSet)
open ConstructionTowerMapSucc (SelectedAt)
open ConstructionTowerTransitions (Before Matrix)
open ConstructionTowerValidity (Valid)
open ConstructionTowerHistory (Row Chart)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Positions (J Steps Schedule request k Inputs : M.Carrier .set) : Prop := ∀ i,
  (Project.FirstOrderSemantics.reduct M).mem i Inputs ↔
    (Project.FirstOrderSemantics.reduct M).mem i Steps ∧ PureKuratowski.PairMember M i request Schedule ∧
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j J ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf j i ∧ Before j k

def ProbeAt (J F Roots i k p : M.Carrier .set) : Prop :=
  ∃ j root leg, (Project.FirstOrderSemantics.reduct M).mem j J ∧
    (Project.FirstOrderSemantics.reduct M).SuccessorOf j i ∧ Before j k ∧
    PureKuratowski.PairMember M i root Roots ∧ Product F j k leg ∧
    PureKuratowski.PairMember M root p leg

def positions {m : Nat} (J Steps Schedule request k Inputs : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound (0 : Fin (m+1))) (.bound Inputs.succ)) (.conj (.mem (.bound (0 : Fin (m+1)))
  (.bound Steps.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Schedule.succ (0 : Fin
  (m+1)) request.succ)) (.existsE (.conj (.mem (.bound (0 : Fin (m+2))) (.bound J.succ.succ)) (.conj
  (Project.Formula.isSuccessor (.bound (0 : Fin (m+2))) (.bound (0 : Fin (m+1)).succ))
  (ConstructionTowerTransitions.before (0 : Fin (m+2)) k.succ.succ))))))))

theorem positions_freeClosed {m : Nat} (J Steps Schedule request k Inputs : Fin m) :
    (positions J Steps Schedule request k Inputs).FreeClosed := by
  simp -implicitDefEqProofs [positions,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isSuccessor,ConstructionTowerTransitions.before_freeClosed]

theorem positions_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Steps Schedule request k Inputs : Fin m) :
    Project.Formula.satisfies env (positions J Steps Schedule request k Inputs) ↔ Positions (env.bound J) (env.bound Steps) (env.bound Schedule) (env.bound request) (env.bound k) (env.bound Inputs) := by
  simp only [positions,Positions,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_isSuccessor_iff,ConstructionTowerTransitions.before_semantics hM]
  rfl


def probeAt {m : Nat} (J F Roots i k p : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (.mem (.bound (2 : Fin (m+3))) (.bound J.succ.succ.succ)) (.conj
  (Project.Formula.isSuccessor (.bound (2 : Fin (m+3))) (.bound i.succ.succ.succ)) (.conj
  (ConstructionTowerTransitions.before (2 : Fin (m+3)) k.succ.succ.succ) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge Roots.succ.succ.succ i.succ.succ.succ (1 : Fin (m+3)))) (.conj
  (ProjectSyntax.encode id (ForcingDiagramOrder.product F.succ.succ.succ (2 : Fin (m+3)) k.succ.succ.succ (0
  : Fin (m+3)))) (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+3)) (1 : Fin (m+3))
  p.succ.succ.succ))))))))))

theorem probeAt_freeClosed {m : Nat} (J F Roots i k p : Fin m) :
    (probeAt J F Roots i k p).FreeClosed := by
  simp -implicitDefEqProofs [probeAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isSuccessor,ConstructionTowerTransitions.before_freeClosed]

theorem probeAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J F Roots i k p : Fin m) :
    Project.Formula.satisfies env (probeAt J F Roots i k p) ↔ ProbeAt (env.bound J) (env.bound F) (env.bound Roots) (env.bound i) (env.bound k) (env.bound p) := by
  simp only [probeAt,ProbeAt,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_isSuccessor_iff,ConstructionTowerTransitions.before_semantics hM,ForcingDiagramOrder.product_semantics (M := M)]
  rfl


theorem exists_positions (hM : FirstOrder.Theory.Models M nativeZF)
    (J Steps Schedule request k : M.Carrier .set) :
    ∃ Inputs, Positions J Steps Schedule request k Inputs := by
  let schema : Project.UnarySchema 4 := {
    body := .conj (ProjectSyntax.encode id (Source.SetLanguage.edge 2 0 3))
      (.existsE (.conj (.mem (.bound 0) (.bound 2))
        (.conj (Project.Formula.isSuccessor (.bound 0) (.bound 1))
          (ConstructionTowerTransitions.before 0 5))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isSuccessor,ConstructionTowerTransitions.before_freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := fun i => match i.val with | 0 => J | 1 => Schedule | 2 => request | _ => k,
    free := fun _ => J }
  have he (i) : schema.denote env i ↔ PureKuratowski.PairMember M i request Schedule ∧
      ∃ j, (Project.FirstOrderSemantics.reduct M).mem j J ∧
        (Project.FirstOrderSemantics.reduct M).SuccessorOf j i ∧ Before j k := by
    change Project.Formula.satisfies (env.push i) schema.body ↔ _
    simp only [schema,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
      Project.Formula.satisfies_isSuccessor_iff,ConstructionTowerTransitions.before_semantics hM,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
    rfl
  obtain ⟨Inputs,hI⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env Steps
  exact ⟨Inputs,fun i => (hI i).trans (and_congr_right (fun _ => he i))⟩

/-- The actual root table and actual target incoming function make the cut
value unique. No separately chosen pointwise witness may change it. -/
theorem probe_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C J history zero P F Steps Roots i k x y : M.Carrier .set}
    (hV : Valid hM w Q R top D mul e mark H C J history) (hF : Matrix J history zero P F)
    (hRoots : FunctionOn Steps Roots) (hx : ProbeAt J F Roots i k x) (hy : ProbeAt J F Roots i k y) : x = y := by
  obtain ⟨j,root,leg,hj,hs,hBefore,hroot,hLeg,hx⟩ := hx
  obtain ⟨j',root',leg',hj',hs',_,hroot',hLeg',hy⟩ := hy
  have eqJ := (ModelTransfer.extensionality hM).eq_of_same_members j j'
    (fun z => (hs z).trans (hs' z).symm)
  subst j'
  have eqRoot := ForcingConditionGraphs.function_unique hRoots hroot hroot'
  subst root'
  obtain ⟨pair,hPair,hPL⟩ := hLeg
  obtain ⟨pair',hPair',hPL'⟩ := hLeg'
  have eqPair := KuratowskiZF.code_unique hM hPair hPair'
  subst pair'
  have eqLeg := ForcingConditionGraphs.function_unique hF.2.1 hPL hPL'
  subst leg'
  have hLeg : Product F j k leg := ⟨pair,hPair,hPL⟩
  have hk := ((hF.2.2 j k leg).mp hLeg).2.1
  obtain ⟨A,m,u,a,HA,CA,KA,baseA,hRowA⟩ := hV.1.2 j hj
  obtain ⟨V,GV,unitV,markV,HV,CV,KV,baseV,hRowV⟩ := hV.1.2 k hk
  have hEntry := (ConstructionTowerTransitions.matrix_at hV.1 hF hj hk hBefore
    (ConstructionTowerValidity.row_field 6 hRowV)).mp hLeg
  have hMap := (hV.2.2.1 j k A m u a HA CA KA baseA V GV unitV markV HV CV KV baseV leg
    hj hk hBefore hRowA hRowV hEntry).1
  exact ForcingConditionGraphs.function_unique hMap.1.1.1.1 hx hy

/-- Construct the actual single-valued probe family at a fixed cut and retain
the exact source profile at that cut's SAME fromBase and distinguished mark. -/
theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u J Schedule history P F Steps Events Roots
      request a b node k V GV unitV markV HV CV KV baseV : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hF : Matrix J history zero P F) (hSteps : StepSet J Steps)
    (hEvents : ConstructionTowerExecution.Graph hM w Q R top D mul e mark H C zero one Schedule history F J Steps Events)
    (hRoots : Chart 8 Steps Events Roots)
    (hCode : ConstructionRequestSchedule.ProbeCode zero a b node request)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k J)
    (hCut : Row history k V GV unitV markV HV CV KV baseV k) :
    ∃ Inputs Family, Positions J Steps Schedule request k Inputs ∧ MapsTo Inputs V Family ∧
      (∀ i p, PureKuratowski.PairMember M i p Family ↔
        (Project.FirstOrderSemantics.reduct M).mem i Inputs ∧ ProbeAt J F Roots i k p) ∧
      ∀ i p, PureKuratowski.PairMember M i p Family →
        ConstructionRoundFresh.ProbeWitness w V GV markV baseV a b node p := by
  have hV := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hSchedule,_⟩ := hCtxCopy
  obtain ⟨Inputs,hInputs⟩ := exists_positions hM J Steps Schedule request k
  have build (i) (hi : (Project.FirstOrderSemantics.reduct M).mem i Inputs) :
      ∃ p, ProbeAt J F Roots i k p ∧ ConstructionRoundFresh.ProbeWitness w V GV markV baseV a b node p := by
    obtain ⟨hiS,hScheduleI,j,hj,hs,hBefore⟩ := (hInputs i).mp hi
    have hiJ := ((hSteps i).mp hiS).1
    obtain ⟨raw,req,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,root,
      V',GV',unitV',markV',HV',CV',KV',baseV',leg,
      hReq,hRowI,hRowJ,hRowK,hPicked,hPack,hStep,hDone,hO,hSource,hLeg,hProbe,_⟩ :=
      ConstructionTowerRequestCones.at_later hM hCtx hRec hF hiJ hj hk hs hBefore
    have eqReq := ForcingConditionGraphs.function_unique hSchedule hReq hScheduleI
    subst req
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ := ConstructionTowerHistory.row_unique hV.1.1 hCut hRowK
    have hSelected : SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F i j raw :=
      ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,root,
        hReq,hRowI,hRowJ,hPicked,hPack,hStep,hDone,hO,hSource⟩
    have hRoot := ConstructionTowerExecution.selected_root hM hSteps hEvents hRoots hiJ hj hs hSelected hPack
    obtain ⟨ON,p,_,_,_,hp,_,hWitness,_⟩ := hProbe a b node hCode
    exact ⟨p,⟨j,root,leg,hj,hs,hBefore,hRoot,hLeg,hp⟩,hWitness⟩
  let schema : Project.BinarySchema 4 := {
    body := probeAt 2 3 4 1 5 0
    freeClosed := probeAt_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := fun i => match i.val with | 0 => J | 1 => F | 2 => Roots | _ => k,
    free := fun _ => J }
  have he (i p) : schema.denote env i p ↔ ProbeAt J F Roots i k p :=
    probeAt_semantics hM ((env.push i).push p) 2 3 4 1 5 0
  have ht (i) (hi : (Project.FirstOrderSemantics.reduct M).mem i Inputs) : ∃ p, schema.denote env i p := by
    obtain ⟨p,hp,_⟩ := build i hi
    exact ⟨p,(he i p).mpr hp⟩
  have hu (i) (_ : (Project.FirstOrderSemantics.reduct M).mem i Inputs) (p q)
      (hp : schema.denote env i p) (hq : schema.denote env i q) : p = q :=
    probe_unique hM hV hF hRoots.1 ((he i p).mp hp) ((he i q).mp hq)
  obtain ⟨Family,hFamily,hFG⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht hu (by
      intro i p hi hp
      obtain ⟨q,hq,hWitness⟩ := build i hi
      have eq := probe_unique hM hV hF hRoots.1 ((he i p).mp hp) hq
      subst q
      obtain ⟨_,_,_,_,_,_,hProfile⟩ := hWitness
      exact hProfile.2.2.2.1)
  have hMap : MapsTo Inputs V Family := (ForcingSupportSize.native_mapsTo hM Inputs V Family).mpr hFamily
  have hGraph : ∀ i p, PureKuratowski.PairMember M i p Family ↔
      (Project.FirstOrderSemantics.reduct M).mem i Inputs ∧ ProbeAt J F Roots i k p :=
    fun i p => (hFG i p).trans (and_congr_right (fun _ => he i p))
  refine ⟨Inputs,Family,hInputs,hMap,hGraph,?_⟩
  intro i p hip
  obtain ⟨hi,hp⟩ := (hGraph i p).mp hip
  obtain ⟨q,hq,hWitness⟩ := build i hi
  have eq := probe_unique hM hV hF hRoots.1 hp hq
  subst q
  exact hWitness


/-- Literal source probe_transition, with the SAME root object and the actual
global transition table. Internal cut order and composition are consumed. -/
theorem transition (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C J history zero P F Roots i k l leg x : M.Carrier .set}
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hV : Valid hM w Q R top D mul e mark H C J history)
    (hF : Matrix J history zero P F) (hKL : Before k l)
    (hLeg : Product F k l leg) (hProbe : ProbeAt J F Roots i k x) :
    ∃ y, ProbeAt J F Roots i l y ∧ PureKuratowski.PairMember M x y leg := by
  obtain ⟨j,root,t,hj,hs,hJK,hRoot,hT,hRootX⟩ := hProbe
  have hk := ((hF.2.2 k l leg).mp hLeg).1
  have hl := ((hF.2.2 k l leg).mp hLeg).2.1
  have hJL : Before j l := by
    rcases hJK with hjk | he
    · rcases hKL with hkl | he
      · exact Or.inl ((hJ.mem hl).transitive k hkl j hjk)
      · subst l
        exact Or.inl hjk
    · subst j
      exact hKL
  obtain ⟨A,m,u,a,HA,CA,KA,baseA,hRowJ⟩ := hV.1.2 j hj
  obtain ⟨B,n,v,b,HB,CB,KB,baseB,hRowK⟩ := hV.1.2 k hk
  obtain ⟨V,GV,unitV,markV,HV,CV,KV,baseV,hRowL⟩ := hV.1.2 l hl
  have hEntryJK := (ConstructionTowerTransitions.matrix_at hV.1 hF hj hk hJK
    (ConstructionTowerValidity.row_field 6 hRowK)).mp hT
  have hEntryKL := (ConstructionTowerTransitions.matrix_at hV.1 hF hk hl hKL
    (ConstructionTowerValidity.row_field 6 hRowL)).mp hLeg
  have hMapJK := (hV.2.2.1 j k A m u a HA CA KA baseA B n v b HB CB KB baseB t
    hj hk hJK hRowJ hRowK hEntryJK).1
  have hMapKL := (hV.2.2.1 k l B n v b HB CB KB baseB V GV unitV markV HV CV KV baseV leg
    hk hl hKL hRowK hRowL hEntryKL).1
  have hxB := hMapJK.1.1.1.2 root x hRootX
  obtain ⟨y,hxy,_⟩ := hMapKL.1.1.1.1.2 x hxB
  obtain ⟨final,hFinal⟩ := ConstructionTowerTransitions.leg_total (i := j) hV.1
    (ConstructionTowerValidity.incoming_rows hM hV) hl
  have hGlobal : Product F j l final := (hF.2.2 j l final).mpr ⟨hj,hl,hFinal⟩
  have hEntryJL := (ConstructionTowerTransitions.matrix_at hV.1 hF hj hl hJL
    (ConstructionTowerValidity.row_field 6 hRowL)).mp hGlobal
  have hComp := hV.2.2.2.1 j k l KB KV t leg final hj hk hl hJK hKL
    (ConstructionTowerValidity.row_field 6 hRowK) (ConstructionTowerValidity.row_field 6 hRowL)
    hEntryJK hEntryKL hEntryJL
  exact ⟨y,⟨j,root,final,hj,hs,hJL,hRoot,hGlobal,(hComp root y).mpr ⟨x,hRootX,hxy⟩⟩,hxy⟩


def familySentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 34 (.imp (ConstructionTowerIterationCases.context (0 : Fin 34) (1 : Fin 34)
    (2 : Fin 34) (3 : Fin 34) (4 : Fin 34) (5 : Fin 34) (6 : Fin 34) (7 : Fin 34) (8 : Fin 34) (9 : Fin 34)
    (10 : Fin 34) (11 : Fin 34) (12 : Fin 34) (13 : Fin 34) (14 : Fin 34)) (.imp
    (ConstructionTowerIteration.recursive (0 : Fin 34) (1 : Fin 34) (2 : Fin 34) (3 : Fin 34) (4 : Fin 34)
    (5 : Fin 34) (6 : Fin 34) (7 : Fin 34) (8 : Fin 34) (9 : Fin 34) (10 : Fin 34) (11 : Fin 34) (13 : Fin
    34) (14 : Fin 34) (13 : Fin 34) (15 : Fin 34)) (.imp (ConstructionTowerTransitions.matrix (13 : Fin 34)
    (15 : Fin 34) (10 : Fin 34) (16 : Fin 34) (17 : Fin 34)) (.imp (ConstructionTowerExecution.stepSet (13 :
    Fin 34) (18 : Fin 34)) (.imp (ConstructionTowerExecution.graph (0 : Fin 34) (1 : Fin 34) (2 : Fin 34) (3
    : Fin 34) (4 : Fin 34) (5 : Fin 34) (6 : Fin 34) (7 : Fin 34) (8 : Fin 34) (9 : Fin 34) (10 : Fin 34)
    (11 : Fin 34) (14 : Fin 34) (15 : Fin 34) (17 : Fin 34) (13 : Fin 34) (18 : Fin 34) (19 : Fin 34)) (.imp
    (ConstructionTowerHistory.chart 8 (18 : Fin 34) (19 : Fin 34) (20 : Fin 34)) (.imp
    (ConstructionRequestSchedule.probeCode (10 : Fin 34) (22 : Fin 34) (23 : Fin 34) (24 : Fin 34) (21 : Fin
    34)) (.imp (.mem (.bound (25 : Fin 34)) (.bound (13 : Fin 34))) (.imp (ConstructionTowerHistory.row (15
    : Fin 34) (25 : Fin 34) (26 : Fin 34) (27 : Fin 34) (28 : Fin 34) (29 : Fin 34) (30 : Fin 34) (31 : Fin
    34) (32 : Fin 34) (33 : Fin 34) (25 : Fin 34)) (.existsE (.existsE (.conj (positions (13 : Fin
    34).succ.succ (18 : Fin 34).succ.succ (14 : Fin 34).succ.succ (21 : Fin 34).succ.succ (25 : Fin
    34).succ.succ (1 : Fin 36)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 36) (1 :
    Fin 36) (26 : Fin 34).succ.succ)) (.conj (.forallE (.forallE (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge (0 : Fin 36).succ.succ (1 : Fin 38) (0 : Fin 38))) (.conj (.mem (.bound (1 :
    Fin 38)) (.bound (1 : Fin 36).succ.succ)) (probeAt (13 : Fin 34).succ.succ.succ.succ (17 : Fin
    34).succ.succ.succ.succ (20 : Fin 34).succ.succ.succ.succ (1 : Fin 38) (25 : Fin 34).succ.succ.succ.succ
    (0 : Fin 38)))))) (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin
    36).succ.succ (1 : Fin 38) (0 : Fin 38))) (ConstructionRoundFresh.probeWitness (0 : Fin
    34).succ.succ.succ.succ (26 : Fin 34).succ.succ.succ.succ (27 : Fin 34).succ.succ.succ.succ (29 : Fin
    34).succ.succ.succ.succ (33 : Fin 34).succ.succ.succ.succ (22 : Fin 34).succ.succ.succ.succ (23 : Fin
    34).succ.succ.succ.succ (24 : Fin 34).succ.succ.succ.succ (0 : Fin 38))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerIterationCases.context_freeClosed,ConstructionTowerIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerExecution.stepSet_freeClosed,ConstructionTowerExecution.graph_freeClosed,ConstructionTowerHistory.chart_freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,ConstructionTowerHistory.row_freeClosed,positions_freeClosed,probeAt_freeClosed,ConstructionRoundFresh.probeWitness_freeClosed]

theorem family_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence familySentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) familySentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionTowerIterationCases.context_semantics hM,ConstructionTowerIteration.recursive_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerExecution.stepSet_semantics,
    ConstructionTowerExecution.graph_semantics hM,ConstructionTowerHistory.chart_semantics hM 8,
    ConstructionRequestSchedule.probeCode_semantics hM,ConstructionTowerHistory.row_semantics hM,
    positions_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),probeAt_semantics hM,
    ConstructionRoundFresh.probeWitness_semantics hM]
  exact fun hCtx hRec hF hSteps hEvents hRoots hCode hk hCut =>
    exists_family hM hCtx hRec hF hSteps hEvents hRoots hCode hk hCut

theorem family_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence familySentence) := ModelTransfer.derives (fun _ hM => family_models hM)

def transitionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 21 (.imp (Project.Formula.isOrdinal (.bound (10 : Fin 21))) (.imp
    (ConstructionTowerValidity.valid (0 : Fin 21) (1 : Fin 21) (2 : Fin 21) (3 : Fin 21) (4 : Fin 21) (5 :
    Fin 21) (6 : Fin 21) (7 : Fin 21) (8 : Fin 21) (9 : Fin 21) (10 : Fin 21) (11 : Fin 21)) (.imp
    (ConstructionTowerTransitions.matrix (10 : Fin 21) (11 : Fin 21) (12 : Fin 21) (13 : Fin 21) (14 : Fin
    21)) (.imp (ConstructionTowerTransitions.before (17 : Fin 21) (18 : Fin 21)) (.imp (ProjectSyntax.encode
    id (ForcingDiagramOrder.product (14 : Fin 21) (17 : Fin 21) (18 : Fin 21) (19 : Fin 21))) (.imp (probeAt
    (10 : Fin 21) (14 : Fin 21) (15 : Fin 21) (16 : Fin 21) (17 : Fin 21) (20 : Fin 21)) (.existsE (.conj
    (probeAt (10 : Fin 21).succ (14 : Fin 21).succ (15 : Fin 21).succ (16 : Fin 21).succ (18 : Fin 21).succ
    (0 : Fin 22)) (ProjectSyntax.encode id (Source.SetLanguage.edge (19 : Fin 21).succ (20 : Fin 21).succ (0
    : Fin 22))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,ConstructionTowerValidity.valid_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerTransitions.before_freeClosed,probeAt_freeClosed]

theorem transition_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence transitionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) transitionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Term.eval_bound,
    ConstructionTowerValidity.valid_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,
    ConstructionTowerTransitions.before_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M),probeAt_semantics hM]
  exact fun hJ hV hF hKL hLeg hProbe => transition hM hJ hV hF hKL hLeg hProbe

theorem transition_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence transitionSentence) := ModelTransfer.derives (fun _ hM => transition_models hM)

end PPAC.Migration.ConstructionTowerProbeFamily
