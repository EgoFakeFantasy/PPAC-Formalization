/- Pinned CompleteRounds.Saturation.tower / preservesProfiles / cardinal_le.
Prove the actual native recursive outer history fully Valid AND AllSmall.
Reuse the existing native internal ordinal induction, explicit pure bad-set
Separation, restriction/locality and full weighted diagram extraction.
No given valid recursive tower, external standard indices or host WF. -/
import PPAC.Migration.ConstructionSaturationIteration

namespace PPAC.Migration.ConstructionSaturationIterationValidity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionSaturationIterationCases (Context)
open ConstructionSaturationIteration (Good Operation Recursive)
open ConstructionTowerHistory (Row Field)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerCardinality (AllSmall)
open ForcingConditionGraphs (FunctionOn)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one u K mu lengthBound length history : M.Carrier .set}

def Correct (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu lengthBound length : M.Carrier .set) : Prop :=
  ∀ history, Recursive hM w Q R top D mul e mark H C zero one K mu lengthBound length history →
    (Project.FirstOrderSemantics.reduct M).MemberSubset length lengthBound →
      Valid hM w Q R top D mul e mark H C length history ∧ AllSmall length history mu

def correct {m : Nat} (w Q R top D mul e mark H C zero one K mu lengthBound length : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (ConstructionSaturationIteration.recursive w.succ Q.succ R.succ top.succ D.succ mul.succ
  e.succ mark.succ H.succ C.succ zero.succ one.succ K.succ mu.succ lengthBound.succ length.succ (0 : Fin
  (m+1))) (.imp (.forallE (.imp (.mem (.bound (0 : Fin (m+2))) (.bound length.succ.succ)) (.mem (.bound (0 :
  Fin (m+2))) (.bound lengthBound.succ.succ)))) (.conj (ConstructionTowerValidity.valid w.succ Q.succ R.succ
  top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ length.succ (0 : Fin (m+1)))
  (ConstructionTowerCardinality.allSmall length.succ (0 : Fin (m+1)) mu.succ)))))

theorem correct_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu lengthBound length : Fin m) :
    (correct w Q R top D mul e mark H C zero one K mu lengthBound length).FreeClosed := by
  simp -implicitDefEqProofs [correct,Definitional.Formula.FreeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionTowerValidity.valid_freeClosed,ConstructionTowerCardinality.allSmall_freeClosed]

theorem correct_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu lengthBound length : Fin m) :
    Project.Formula.satisfies env (correct w Q R top D mul e mark H C zero one K mu lengthBound length) ↔ Correct hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound lengthBound) (env.bound length) := by
  simp only [correct,Correct,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionSaturationIteration.recursive_semantics hM,ConstructionTowerValidity.valid_semantics hM,ConstructionTowerCardinality.allSmall_semantics hM]
  rfl


theorem recursive_valid_small (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u K mu lengthBound)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one K mu lengthBound length history)
    (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset length lengthBound) :
    Valid hM w Q R top D mul e mark H C length history ∧ AllSmall length history mu := by
  let rawM := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  let property : M.Carrier .set → Prop := Correct hM w Q R top D mul e mark H C zero one K mu lengthBound
  let schema : Project.UnarySchema 15 := {
    body := correct 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 0
    freeClosed := correct_freeClosed .. }
  let env := ConstructionSaturationIteration.operatorEnv w Q R top D mul e mark H C zero one K mu lengthBound
  have he (index) : schema.denote env index ↔ property index :=
    correct_semantics hM (env.push index) 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 0
  have hAll : property length := by
    apply hRec.1.1.induction property
    · obtain ⟨bad,hBad⟩ := ZF.separation_exists_d hZF schema.neg env length
      refine ⟨bad,fun index => (hBad index).trans (and_congr_right fun _ => ?_)⟩
      simp only [Project.UnarySchema.neg,Project.Formula.satisfies_neg_iff]
      exact not_congr (he index)
    · intro current hCurrent hPrevious seq hSequence hSubset
      have hFn := ConstructionTowerIterationValidity.function_of_sequence hM hSequence.1
      have hCover : ∀ i, rawM.mem i current →
          ∃ next segment, rawM.SuccessorOf next i ∧
            Valid hM w Q R top D mul e mark H C next segment ∧ AllSmall next segment mu ∧
            rawM.IsRestrictionOf I segment seq next := by
        intro i hi
        obtain ⟨value,hv,_⟩ := hFn.2 i hi
        obtain ⟨prior,hRestriction,hOp⟩ := hSequence.2 i hi value hv
        have hPriorRec := Structure.IsRecursiveSequence.restriction hSequence hi hRestriction
        have hPriorSub : rawM.MemberSubset i lengthBound :=
          fun x hx => hSubset x (hCurrent.transitive i hi x hx)
        have hPrior := hPrevious i hi prior hPriorRec hPriorSub
        have hGood : Good hM w Q R top D mul e mark H C mu lengthBound prior i :=
          ⟨hCurrent.mem hi,hSubset i hi,hPrior.1,hPrior.2⟩
        obtain ⟨next,segment,hAppend,hValid,hSmall⟩ :=
          (ConstructionSaturationIteration.valid_step hM hOrder hChoice hCtx hGood hOp).2
        have hSucc := hAppend.1
        have hGraph := hAppend.2.2
        have hPrefixRel : rawM.IsSetRelation I segment := by
          intro p hp
          obtain ⟨x,y,_,hc⟩ := hValid.1.1.1 p hp
          exact ⟨x,y,hc⟩
        have hPrefixRestriction : rawM.IsRestrictionOf I segment seq next := by
          refine ⟨hPrefixRel,fun j v => ?_⟩
          constructor
          · intro hjv
            rcases (hGraph j v).mp hjv with hjv | ⟨rfl,rfl⟩
            · obtain ⟨hj,hv0⟩ := (hRestriction.2 j v).mp hjv
              exact ⟨(hSucc j).mpr (Or.inl hj),hv0⟩
            · exact ⟨hSucc.predecessor_mem,hv⟩
          · rintro ⟨hj,hjv⟩
            apply (hGraph j v).mpr
            rcases (hSucc j).mp hj with hj | he
            · exact Or.inl ((hRestriction.2 j v).mpr ⟨hj,hjv⟩)
            · have ej := (ModelTransfer.extensionality hM).eq_of_same_members j i he
              subst j
              exact Or.inr ⟨rfl,ForcingConditionGraphs.function_unique hFn hjv hv⟩
        exact ⟨next,segment,hSucc,hValid,hSmall,hPrefixRestriction⟩
      refine ⟨ConstructionTowerIterationValidity.valid_of_cover hM hCurrent hFn (fun i hi => ?_),?_⟩
      · obtain ⟨next,segment,hs,hV,_,hr⟩ := hCover i hi
        exact ⟨next,segment,hs,hV,hr⟩
      · intro i hi N hN
        obtain ⟨next,segment,hs,_,hSmall,hr⟩ := hCover i hi
        obtain ⟨A,m,v,a,U,V,L,f,time,⟨code,hCode,hPack⟩,he⟩ := hN
        have hSegmentRow : Row segment i A m v a U V L f time :=
          ⟨code,(hr.2 i code).mpr ⟨hs.predecessor_mem,hCode⟩,hPack⟩
        exact hSmall i hs.predecessor_mem N ⟨A,m,v,a,U,V,L,f,time,hSegmentRow,he⟩
  exact hAll history hRec hSub

theorem exists_valid (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u K mu lengthBound) :
    ∃ history, Recursive hM w Q R top D mul e mark H C zero one K mu lengthBound lengthBound history ∧
      Valid hM w Q R top D mul e mark H C lengthBound history ∧ AllSmall lengthBound history mu := by
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLength,_⟩ := hCtxCopy
  obtain ⟨history,hRec⟩ := ConstructionSaturationIteration.recursive_exists hM hOrder hChoice hCtx hLength
  exact ⟨history,hRec,recursive_valid_small hM hOrder hChoice hCtx hRec (fun _ h => h)⟩


/-- The exact global transition is the inclusion of the SAME trace-bearing
selected complete round; preserve its raw tuple and current/base equations. -/
def SelectedAt (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero one K mu history F i j raw : M.Carrier .set) : Prop :=
  ∃ Requests N mulN eN markN HN CN L f W G unitW markW HW CW NewOut baseW O,
    Row history i N mulN eN markN HN CN L f i ∧
    Row history j W G unitW markW HW CW NewOut baseW j ∧
    ConstructionSaturationStep.Picked hM w Q R top N mulN eN markN HN CN zero one K mu raw ∧
    ConstructionSaturationStep.Candidate hM w Q R top N mulN eN markN HN CN zero one K mu raw ∧
    ConstructionRoundSelection.Pack W G unitW markW HW CW O Requests zero raw ∧
    ForcingDiagramOrder.Product F i j O ∧ ConstructionProbeMappedPath.NodeMap f O baseW

theorem map_succ_selected (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {P F i j : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u K mu lengthBound)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one K mu lengthBound lengthBound history)
    (hF : ConstructionTowerTransitions.Matrix lengthBound history zero P F)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i lengthBound)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j lengthBound)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf j i) :
    ∃ raw, SelectedAt hM w Q R top zero one K mu history F i j raw := by
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,hz,_,_,_,_,_,_,hLength,_⟩ := hCtxCopy
  have hValid := (recursive_valid_small hM hOrder hChoice hCtx hRec (fun _ h => h)).1
  obtain ⟨code,hCode,_⟩ := hValid.1.1.2 j hj
  obtain ⟨prior,hRestrict,hOp⟩ := hRec.2 j hj code hCode
  have hPriorRec := Structure.IsRecursiveSequence.restriction hRec hj hRestrict
  have hPriorSub : (Project.FirstOrderSemantics.reduct M).MemberSubset j lengthBound :=
    hLength.transitive j hj
  have hPrior := recursive_valid_small hM hOrder hChoice hCtx hPriorRec hPriorSub
  have hGood : Good hM w Q R top D mul e mark H C mu lengthBound prior j :=
    ⟨hLength.mem hj,hj,hPrior.1,hPrior.2⟩
  have hCase := (ConstructionSaturationIteration.valid_step hM hOrder hChoice hCtx hGood hOp).1
  rcases hCase with ⟨he,_⟩ | ⟨_,prev,hSucc,hValue⟩ | ⟨_,hNo,_⟩
  · exact False.elim (hz i (he ▸ hs.predecessor_mem))
  · have eqPrev := ConstructionTowerIterationCases.predecessor_unique hM (hLength.mem hj) hSucc hs
    subst prev
    obtain ⟨Domains,N,mulN,eN,markN,HN,CN,L,f,next,raw,Requests,W,G,unitW,markW,HW,CW,O,Out,baseW,
      identity,NewDomains,NewOut,hChart,hRow,_,hNext,hPicked,hCandidate,hRaw,hGraph,hOut,hSuccEq,
      hBaseGraph,hMap,hSelf,hPack⟩ := hValue
    have hRowGlobal : Row history i N mulN eN markN HN CN L f i := by
      obtain ⟨c,hc,hp⟩ := hRow
      exact ⟨c,((hRestrict.2 i c).mp hc).2,hp⟩
    have hTarget : Row history j W G unitW markW HW CW NewOut baseW j := ⟨code,hCode,hPack⟩
    obtain ⟨_,_,_,next0,id0,_,_,hId0,hIdentity0⟩ :=
      hPrior.1.2.1 i hs.predecessor_mem N mulN eN markN HN CN L f hRow
    obtain ⟨leg,hLeg,_⟩ := hOut.1.2 i hs.predecessor_mem
    have eqLeg := hSuccEq i id0 leg hs.predecessor_mem hId0 hIdentity0 hLeg
    have hOldO : PureKuratowski.PairMember M i O Out := eqLeg ▸ hLeg
    obtain ⟨_,_,_,_,_,hNewGraph,_⟩ := hSelf
    have hNewO : PureKuratowski.PairMember M i O NewOut := (hNewGraph i O).mpr (Or.inl hOldO)
    have hGlobalO : ForcingDiagramOrder.Product F i j O :=
      (ConstructionTowerTransitions.matrix_at hValid.1 hF hi hj
        (Or.inl hs.predecessor_mem) (row_field 6 hTarget)).mpr hNewO
    exact ⟨raw,Requests,N,mulN,eN,markN,HN,CN,L,f,W,G,unitW,markW,HW,CW,NewOut,baseW,O,
      hRowGlobal,hTarget,hPicked,hCandidate,hRaw,hGlobalO,hBaseGraph⟩
  · exact False.elim (hNo ⟨i,hs⟩)

/-- Actual multi-round recursive tower with the SAME original full weighted
diagram, all base maps/naturality, identity time and all internal stage bounds. -/
theorem exists_tower (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u K mu lengthBound) :
    ∃ history Domains Muls Units Marks Heights Costs Incoming Origins Times E P F,
      Recursive hM w Q R top D mul e mark H C zero one K mu lengthBound lengthBound history ∧
      Valid hM w Q R top D mul e mark H C lengthBound history ∧ AllSmall lengthBound history mu ∧
      ConstructionTowerHistory.Charts lengthBound history Domains Muls Units Marks Heights Costs Incoming Origins Times ∧
      ForcingConditionGraphs.IdentityGraph lengthBound Times ∧
      ConstructionTowerTransitions.Order lengthBound E ∧
      ConstructionTowerTransitions.Matrix lengthBound history zero P F ∧
      ConstructionTowerDiagram.Data hM w Q R top D mul e mark H C lengthBound E Domains F Muls Units Marks Heights Costs Origins ∧
      (∀ i j, (Project.FirstOrderSemantics.reduct M).mem i lengthBound →
        (Project.FirstOrderSemantics.reduct M).mem j lengthBound →
        (Project.FirstOrderSemantics.reduct M).SuccessorOf j i →
        ∃ raw, SelectedAt hM w Q R top zero one K mu history F i j raw) := by
  obtain ⟨history,hRec,hValid,hSmall⟩ := exists_valid hM hOrder hChoice hCtx
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLength,_⟩ := hCtxCopy
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,hE,hF,hData⟩ :=
    ConstructionTowerDiagram.exists_data hM zero hLength hValid
  have hCopy := hCharts
  obtain ⟨_,_,_,_,_,_,_,_,cT⟩ := hCharts
  exact ⟨history,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    hRec,hValid,hSmall,hCopy,ConstructionTowerHistory.time_identity hValid.1 cT,hE,hF,hData,
      fun i j hi hj hs => map_succ_selected hM hOrder hChoice hCtx hRec hF hi hj hs⟩

def selectedAt {m : Nat} (w Q R top zero one K mu history F i j raw : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (16 : Fin
  (m+18)) (15 : Fin (m+18)) (14 : Fin (m+18)) (13 : Fin (m+18)) (12 : Fin (m+18)) (11 : Fin (m+18)) (10 :
  Fin (m+18)) (9 : Fin (m+18))
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
  (m+18)) (7 : Fin (m+18)) (6 : Fin (m+18)) (5 : Fin (m+18)) (4 : Fin (m+18)) (3 : Fin (m+18)) (2 : Fin
  (m+18)) (1 : Fin (m+18))
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionSaturationStep.picked
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (16 : Fin
  (m+18)) (15 : Fin (m+18)) (14 : Fin (m+18)) (13 : Fin (m+18)) (12 : Fin (m+18)) (11 : Fin (m+18))
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  raw.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionSaturationStep.candidate
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (16 : Fin
  (m+18)) (15 : Fin (m+18)) (14 : Fin (m+18)) (13 : Fin (m+18)) (12 : Fin (m+18)) (11 : Fin (m+18))
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  raw.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionRoundSelection.pack (8 : Fin (m+18)) (7 : Fin (m+18)) (6 : Fin (m+18)) (5 : Fin (m+18)) (4 :
  Fin (m+18)) (3 : Fin (m+18)) (0 : Fin (m+18)) (17 : Fin (m+18))
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  raw.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ProjectSyntax.encode id (ForcingDiagramOrder.product
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin
  (m+18)))) (ConstructionProbeMappedPathSyntax.nodeMap (9 : Fin (m+18)) (0 : Fin (m+18)) (1 : Fin
  (m+18)))))))))))))))))))))))))))

theorem selectedAt_freeClosed {m : Nat} (w Q R top zero one K mu history F i j raw : Fin m) :
    (selectedAt w Q R top zero one K mu history F i j raw).FreeClosed := by
  simp -implicitDefEqProofs [selectedAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionSaturationStep.picked_freeClosed,ConstructionSaturationStep.candidate_freeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem selectedAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero one K mu history F i j raw : Fin m) :
    Project.Formula.satisfies env (selectedAt w Q R top zero one K mu history F i j raw) ↔ SelectedAt hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound history) (env.bound F) (env.bound i) (env.bound j) (env.bound raw) := by
  simp only [selectedAt,SelectedAt,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,

    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionTowerHistory.row_semantics hM,ConstructionSaturationStep.picked_semantics hM,ConstructionSaturationStep.candidate_semantics hM,ConstructionRoundSelection.pack_semantics hM,ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl


def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 16 (.imp (ConstructionSaturationIterationCases.context (0 : Fin 16) (1 : Fin
    16) (2 : Fin 16) (3 : Fin 16) (4 : Fin 16) (5 : Fin 16) (6 : Fin 16) (7 : Fin 16) (8 : Fin 16) (9 : Fin
    16) (10 : Fin 16) (11 : Fin 16) (12 : Fin 16) (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)) (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.conj (ConstructionSaturationIteration.recursive (0 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (14 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin 29)) (.conj
    (ConstructionTowerValidity.valid (0 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin 29)) (.conj
    (ConstructionTowerCardinality.allSmall (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin 29) (14 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
    (ConstructionTowerHistory.charts (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin 29) (11 : Fin 29) (10 :
    Fin 29) (9 : Fin 29) (8 : Fin 29) (7 : Fin 29) (6 : Fin 29) (5 : Fin 29) (4 : Fin 29) (3 : Fin 29))
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin 29))) (.conj
    (ConstructionTowerTransitions.order (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin 29)) (.conj
    (ConstructionTowerTransitions.matrix (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin 29) (10 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 29) (0 : Fin 29)) (.conj
    (ConstructionTowerDiagram.data (0 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin 29) (11 : Fin 29) (0 : Fin
    29) (10 : Fin 29) (9 : Fin 29) (8 : Fin 29) (7 : Fin 29) (6 : Fin 29) (4 : Fin 29)) (.forallE (.forallE
    (.imp (.mem (.bound (1 : Fin 31)) (.bound (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (0
    : Fin 31)) (.bound (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
    (Project.Formula.isSuccessor (.bound (0 : Fin 31)) (.bound (1 : Fin 31))) (.existsE (selectedAt (0 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (14 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin
    29).succ.succ.succ (0 : Fin 29).succ.succ.succ (2 : Fin 32) (1 : Fin 32) (0 : Fin
    32)))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,
      ConstructionTowerValidity.valid_freeClosed,ConstructionTowerCardinality.allSmall_freeClosed,
      ConstructionTowerHistory.charts_freeClosed,ConstructionTowerTransitions.order_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerDiagram.data_freeClosed,
      Project.Formula.isSuccessor,selectedAt_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isSuccessor_iff,
    ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,
    ConstructionTowerValidity.valid_semantics hM,ConstructionTowerCardinality.allSmall_semantics hM,
    ConstructionTowerHistory.charts_semantics hM,ConstructionTowerTransitions.order_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerDiagram.data_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.identityGraph_semantics (M := M),selectedAt_semantics hM]
  exact fun hCtx => exists_tower hM hOrder hChoice hCtx

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
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
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice)



end PPAC.Migration.ConstructionSaturationIterationValidity
