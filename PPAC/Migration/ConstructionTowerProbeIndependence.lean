/- Pinned CompleteRounds.probes_ne_of_lt / probes_independent_of_lt.
Use the canonical family, prior-cut profile, actual transition, and the later
probe's full old-stage freshness/independence. All positions/cuts are internal. -/
import PPAC.Migration.ConstructionTowerProbeFamily

namespace PPAC.Migration.ConstructionTowerProbeIndependence
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerExecution (StepSet)
open ConstructionTowerTransitions (Before Matrix)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerHistory (Row Chart)
open ConstructionTowerMapSucc (SelectedAt)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive)
open ConstructionTowerProbeFamily (Positions ProbeAt)
open ConstructionProbeCones (JoinProperty)
open ConstructionBaseMonoid (Divides)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Independent (Inputs V GV Family baseV a markV : M.Carrier .set) : Prop :=
  Injection Inputs V Family ∧ ∀ i j pi pj,
    PureKuratowski.PairMember M i pi Family → PureKuratowski.PairMember M j pj Family → i ≠ j →
    ∃ fa exit, PureKuratowski.PairMember M a fa baseV ∧ Product GV fa markV exit ∧
      JoinProperty V GV pi pj exit

/-- One proof supplies both original ordered conclusions. The earlier probe is
first read at the later execution stage, exactly as in the fixed source. -/
theorem independent_of_lt (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u J Schedule history P F Steps Events Roots
      request a b node k V GV unitV markV HV CV KV baseV Inputs Family i j pi pj : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hF : Matrix J history zero P F) (hSteps : StepSet J Steps)
    (hEvents : ConstructionTowerExecution.Graph hM w Q R top D mul e mark H C zero one Schedule history F J Steps Events)
    (hRoots : Chart 8 Steps Events Roots)
    (hCode : ConstructionRequestSchedule.ProbeCode zero a b node request)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k J)
    (hCut : Row history k V GV unitV markV HV CV KV baseV k)
    (hPositions : Positions J Steps Schedule request k Inputs)
    (hGraph : ∀ t p, PureKuratowski.PairMember M t p Family ↔
      (Project.FirstOrderSemantics.reduct M).mem t Inputs ∧ ProbeAt J F Roots t k p)
    (hip : PureKuratowski.PairMember M i pi Family) (hjp : PureKuratowski.PairMember M j pj Family)
    (hij : (Project.FirstOrderSemantics.reduct M).mem i j) :
    pi ≠ pj ∧ ∃ fa exit, PureKuratowski.PairMember M a fa baseV ∧ Product GV fa markV exit ∧
      JoinProperty V GV pi pj exit := by
  have hV := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,_,_,hJ,hSchedule,_⟩ := hCtxCopy
  obtain ⟨hiI,hProbeI⟩ := (hGraph i pi).mp hip
  obtain ⟨hjI,hProbeJ⟩ := (hGraph j pj).mp hjp
  obtain ⟨hiS,hScheduleI,si,hsi,hSuccI,hAfterI⟩ := (hPositions i).mp hiI
  obtain ⟨hjS,hScheduleJ,sj,hsj,hSuccJ,hAfterJ⟩ := (hPositions j).mp hjI
  have hiJ := ((hSteps i).mp hiS).1
  have hjJ := ((hSteps j).mp hjS).1
  have hFirstAtJ : Before si j := by
    rcases hJ.wellOrder.linear.compare si hsi j hjJ with he | hlt | hgt
    · exact Or.inr ((ModelTransfer.extensionality hM).eq_of_same_members si j he)
    · exact Or.inl hlt
    · rcases (hSuccI j).mp hgt with hji | he
      · exact False.elim (hJ.wellOrder.linear.irrefl i hiJ
          (hJ.wellOrder.linear.trans i hiJ j hjJ i hiJ hij hji))
      · have eq := (ModelTransfer.extensionality hM).eq_of_same_members j i he
        subst j
        exact False.elim (hJ.wellOrder.linear.irrefl i hiJ hij)
  have hJK : Before j k := by
    rcases hAfterJ with hsk | he
    · exact Or.inl ((hJ.mem hk).transitive sj hsk j hSuccJ.predecessor_mem)
    · subst k
      exact Or.inl hSuccJ.predecessor_mem
  obtain ⟨raw,req,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,root,
    V',GV',unitV',markV',HV',CV',KV',baseV',leg,
    hReq,hRowI,hRowJ,hRowK,hPicked,hPack,hStep,hDone,hO,hSource,hLeg,hProbe,_⟩ :=
    ConstructionTowerRequestCones.at_later hM hCtx hRec hF hjJ hsj hk hSuccJ hAfterJ
  have eqReq := ForcingConditionGraphs.function_unique hSchedule hReq hScheduleJ
  subst req
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ := ConstructionTowerHistory.row_unique hV.1.1 hCut hRowK
  have hSelected : SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F j sj raw :=
    ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,root,
      hReq,hRowI,hRowJ,hPicked,hPack,hStep,hDone,hO,hSource⟩
  have hRoot := ConstructionTowerExecution.selected_root hM hSteps hEvents hRoots hjJ hsj hSuccJ hSelected hPack
  obtain ⟨ON,pj',hMap,hOC,hON,hGen, hRealized,hWitness,hFresh⟩ := hProbe a b node hCode
  have hProbeJ' : ProbeAt J F Roots j k pj' := ⟨sj,root,leg,hsj,hSuccJ,hAfterJ,hRoot,hLeg,hGen⟩
  have eqPj := ConstructionTowerProbeFamily.probe_unique hM hV hF hRoots.1 hProbeJ' hProbeJ
  subst pj'
  obtain ⟨InputsJ,FamilyJ,hPosJ,hMapJ,hGraphJ,hProfilesJ⟩ :=
    ConstructionTowerProbeFamily.exists_family hM hCtx hRec hF hSteps hEvents hRoots hCode hjJ hRowI
  have hiInputsJ := (hPosJ i).mpr ⟨hiS,hScheduleI,si,hsi,hSuccI,hFirstAtJ⟩
  obtain ⟨x,hx,_⟩ := hMapJ.1.2 i hiInputsJ
  have hProfileX := hProfilesJ i x hx
  have hProbeX := ((hGraphJ i x).mp hx).2
  obtain ⟨xFinal,hProbeXFinal,hXFinal⟩ :=
    ConstructionTowerProbeFamily.transition hM hJ hV hF hJK hON hProbeX
  have eqPi := ConstructionTowerProbeFamily.probe_unique hM hV hF hRoots.1 hProbeXFinal hProbeI
  subst xFinal
  have hNe : pi ≠ pj := by
    intro he
    exact hFresh x (he ▸ hXFinal)
  obtain ⟨fa,fb,mapped,hfa,hfb,_,hInd⟩ := hRealized
  obtain ⟨aX,bX,mappedX,haX,_,_,hProfile⟩ := hProfileX
  have hOrigin : MapsTo D N f := (hV.2.1 j hjJ N mulN eN markN HN CN K f hRowI).2.1.1.1.1
  have eqFa := ForcingConditionGraphs.function_unique hOrigin.1 haX hfa
  subst aX
  obtain ⟨ex,hExN,hAEx,hXb,hXA,_⟩ := hProfile.2.2.2.2.2
  have hMapsON : MapsTo N V ON := hMap.1.1.1
  obtain ⟨faV,hFaV,_⟩ := hMapsON.1.2 fa hProfile.1
  obtain ⟨exV,hExV,_⟩ := hMapsON.1.2 ex hExN
  have hMark := hMap.2.2.2.1
  have hExit := hMap.2.1 fa markN ex faV markV exV hAEx hFaV hMark hExV
  have hONEntry := (ConstructionTowerTransitions.matrix_at hV.1 hF hjJ hk hJK (row_field 6 hCut)).mp hON
  have hNatural := hV.2.2.2.2 j k f baseV KV ON hjJ hk hJK
    (row_field 7 hRowI) (row_field 7 hCut) (row_field 6 hCut) hONEntry
  refine ⟨hNe,faV,exV,(hNatural a faV).mpr ⟨fa,hfa,hFaV⟩,hExit,?_⟩
  intro z hzV
  exact hInd ex hAEx x pi exV z hProfile.2.2.2.1 hXFinal hExV hzV ⟨bX,hProfile.2.1,hXb⟩ hXA

/-- Internal ordinal comparison yields both source family injectivity and
the exact common-exit cone for every pair of different execution positions. -/
theorem independent (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u J Schedule history P F Steps Events Roots
      request a b node k V GV unitV markV HV CV KV baseV Inputs Family : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hF : Matrix J history zero P F) (hSteps : StepSet J Steps)
    (hEvents : ConstructionTowerExecution.Graph hM w Q R top D mul e mark H C zero one Schedule history F J Steps Events)
    (hRoots : Chart 8 Steps Events Roots)
    (hCode : ConstructionRequestSchedule.ProbeCode zero a b node request)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k J)
    (hCut : Row history k V GV unitV markV HV CV KV baseV k)
    (hPositions : Positions J Steps Schedule request k Inputs) (hMap : MapsTo Inputs V Family)
    (hGraph : ∀ t p, PureKuratowski.PairMember M t p Family ↔
      (Project.FirstOrderSemantics.reduct M).mem t Inputs ∧ ProbeAt J F Roots t k p) :
    Independent Inputs V GV Family baseV a markV := by
  classical
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,_,_,hJ,_,_⟩ := hCtxCopy
  have pair {i j pi pj} (hip : PureKuratowski.PairMember M i pi Family)
      (hjp : PureKuratowski.PairMember M j pj Family) (hne : i ≠ j) :
      pi ≠ pj ∧ ∃ fa exit, PureKuratowski.PairMember M a fa baseV ∧
        Product GV fa markV exit ∧ JoinProperty V GV pi pj exit := by
    have hiI := ((hGraph i pi).mp hip).1
    have hjI := ((hGraph j pj).mp hjp).1
    have hiJ := ((hSteps i).mp ((hPositions i).mp hiI).1).1
    have hjJ := ((hSteps j).mp ((hPositions j).mp hjI).1).1
    rcases hJ.wellOrder.linear.compare i hiJ j hjJ with he | hlt | hgt
    · exact False.elim (hne ((ModelTransfer.extensionality hM).eq_of_same_members i j he))
    · exact independent_of_lt hM hCtx hRec hF hSteps hEvents hRoots hCode hk hCut hPositions hGraph hip hjp hlt
    · obtain ⟨hNe,fa,exit,hfa,hExit,hCone⟩ :=
        independent_of_lt hM hCtx hRec hF hSteps hEvents hRoots hCode hk hCut hPositions hGraph hjp hip hgt
      exact ⟨fun h => hNe h.symm,fa,exit,hfa,hExit,fun z hz => and_comm.trans (hCone z hz)⟩
  refine ⟨⟨hMap,?_⟩,?_⟩
  · intro i j p hip hjp
    by_cases he : i = j
    · exact he
    · exact False.elim ((pair hip hjp he).1 rfl)
  · intro i j pi pj hip hjp hne
    exact (pair hip hjp hne).2


/-- Strengthen the ACTUAL family producer; no injective/independent family
is supplied as input. All previous graph and profile conclusions survive. -/
theorem exists_independent_family (hM : FirstOrder.Theory.Models M nativeZF)
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
      (∀ i p, PureKuratowski.PairMember M i p Family →
        ConstructionRoundFresh.ProbeWitness w V GV markV baseV a b node p) ∧
      Independent Inputs V GV Family baseV a markV := by
  obtain ⟨Inputs,Family,hPositions,hMap,hGraph,hProfiles⟩ :=
    ConstructionTowerProbeFamily.exists_family hM hCtx hRec hF hSteps hEvents hRoots hCode hk hCut
  exact ⟨Inputs,Family,hPositions,hMap,hGraph,hProfiles,
    independent hM hCtx hRec hF hSteps hEvents hRoots hCode hk hCut hPositions hMap hGraph⟩

def independentFamily {m : Nat} (Inputs V GV Family baseV a markV : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection Family Inputs V)) (.forallE (.forallE
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Family.succ.succ.succ.succ (3
  : Fin (m+4)) (1 : Fin (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Family.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin (m+4)))) (.imp (.neg (Project.Formula.extensionalEq
  (.bound (3 : Fin (m+4))) (.bound (2 : Fin (m+4))))) (.existsE (.existsE (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge baseV.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ (1 : Fin
  (m+6)))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product GV.succ.succ.succ.succ.succ.succ (1
  : Fin (m+6)) markV.succ.succ.succ.succ.succ.succ (0 : Fin (m+6)))) (ConstructionProbeCones.joinProperty
  V.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ (1 : Fin (m+4)).succ.succ (0 : Fin
  (m+4)).succ.succ (0 : Fin (m+6)))))))))))))))

theorem independentFamily_freeClosed {m : Nat} (Inputs V GV Family baseV a markV : Fin m) :
    (independentFamily Inputs V GV Family baseV a markV).FreeClosed := by
  simp -implicitDefEqProofs [independentFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionProbeCones.joinProperty_freeClosed]

theorem independentFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Inputs V GV Family baseV a markV : Fin m) :
    Project.Formula.satisfies env (independentFamily Inputs V GV Family baseV a markV) ↔ Independent (env.bound Inputs) (env.bound V) (env.bound GV) (env.bound Family) (env.bound baseV) (env.bound a) (env.bound markV) := by
  simp only [independentFamily,Independent,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeCones.joinProperty_semantics hM]
  rfl


def constructionSentence : Project.Sentence where
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
    34) (32 : Fin 34) (33 : Fin 34) (25 : Fin 34)) (.existsE (.existsE (.conj
    (ConstructionTowerProbeFamily.positions (13 : Fin 34).succ.succ (18 : Fin 34).succ.succ (14 : Fin
    34).succ.succ (21 : Fin 34).succ.succ (25 : Fin 34).succ.succ (1 : Fin 36)) (.conj (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (0 : Fin 36) (1 : Fin 36) (26 : Fin 34).succ.succ)) (.conj (.forallE
    (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin 36).succ.succ (1 : Fin 38) (0
    : Fin 38))) (.conj (.mem (.bound (1 : Fin 38)) (.bound (1 : Fin 36).succ.succ))
    (ConstructionTowerProbeFamily.probeAt (13 : Fin 34).succ.succ.succ.succ (17 : Fin
    34).succ.succ.succ.succ (20 : Fin 34).succ.succ.succ.succ (1 : Fin 38) (25 : Fin 34).succ.succ.succ.succ
    (0 : Fin 38)))))) (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0
    : Fin 36).succ.succ (1 : Fin 38) (0 : Fin 38))) (ConstructionRoundFresh.probeWitness (0 : Fin
    34).succ.succ.succ.succ (26 : Fin 34).succ.succ.succ.succ (27 : Fin 34).succ.succ.succ.succ (29 : Fin
    34).succ.succ.succ.succ (33 : Fin 34).succ.succ.succ.succ (22 : Fin 34).succ.succ.succ.succ (23 : Fin
    34).succ.succ.succ.succ (24 : Fin 34).succ.succ.succ.succ (0 : Fin 38))))) (independentFamily (1 : Fin
    36) (26 : Fin 34).succ.succ (27 : Fin 34).succ.succ (0 : Fin 36) (33 : Fin 34).succ.succ (22 : Fin
    34).succ.succ (29 : Fin 34).succ.succ)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionTowerIterationCases.context_freeClosed,ConstructionTowerIteration.recursive_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerExecution.stepSet_freeClosed,
      ConstructionTowerExecution.graph_freeClosed,ConstructionTowerHistory.chart_freeClosed,
      ConstructionRequestSchedule.probeCode_freeClosed,ConstructionTowerHistory.row_freeClosed,
      ConstructionTowerProbeFamily.positions_freeClosed,ConstructionTowerProbeFamily.probeAt_freeClosed,
      ConstructionRoundFresh.probeWitness_freeClosed,independentFamily_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionTowerIterationCases.context_semantics hM,ConstructionTowerIteration.recursive_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerExecution.stepSet_semantics,
    ConstructionTowerExecution.graph_semantics hM,ConstructionTowerHistory.chart_semantics hM 8,
    ConstructionRequestSchedule.probeCode_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ConstructionTowerProbeFamily.positions_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionTowerProbeFamily.probeAt_semantics hM,ConstructionRoundFresh.probeWitness_semantics hM,
    independentFamily_semantics hM]
  exact fun hCtx hRec hF hSteps hEvents hRoots hCode hk hCut =>
    exists_independent_family hM hCtx hRec hF hSteps hEvents hRoots hCode hk hCut

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionTowerProbeIndependence
