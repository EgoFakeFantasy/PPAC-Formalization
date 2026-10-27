/- Pinned MonoidRounds.Round.map_succ / ConstructionIteration.map_succ.
Read the SAME actual recursive tower, SAME scheduled request and selected
Extended successor. Its global transition graph is literally the SAME
inclusion O, with full Step and BOTH original request witness alternatives.
No supplied adjacent-step law, alternative object, or new algebra backend. -/
import PPAC.Migration.ConstructionTowerIterationValidity

namespace PPAC.Migration.ConstructionTowerMapSucc
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive Good)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one u lengthBound Schedule history P F i j : M.Carrier .set}

def SuccessorAt (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one Schedule history F i j : M.Carrier .set) : Prop :=
  ∃ request N mulN eN markN HN CN K f W G unitW markW HL LC NewOut base O roots,
    PureKuratowski.PairMember M i request Schedule ∧
    Row history i N mulN eN markN HN CN K f i ∧
    Row history j W G unitW markW HL LC NewOut base j ∧
    ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f
      W G unitW markW HL LC O base ∧
    ConstructionRoundSelection.Done w D mul zero one request W G markW O base roots ∧
    Product F i j O ∧ ConstructionRoundSource.Provenance hM w zero one request N mulN eN markN f W G unitW O roots

def SelectedAt (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one Schedule history F i j raw : M.Carrier .set) : Prop :=
  ∃ request N mulN eN markN HN CN K f W G unitW markW HL LC NewOut base O roots,
    PureKuratowski.PairMember M i request Schedule ∧
    Row history i N mulN eN markN HN CN K f i ∧
    Row history j W G unitW markW HL LC NewOut base j ∧
    ConstructionRoundSelection.Picked hM w Q R top zero one D mul e mark H C
      N mulN eN markN HN CN f request raw ∧
    ConstructionRoundSelection.Pack W G unitW markW HL LC O base roots raw ∧
    ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f
      W G unitW markW HL LC O base ∧
    ConstructionRoundSelection.Done w D mul zero one request W G markW O base roots ∧
    Product F i j O ∧ ConstructionRoundSource.Provenance hM w zero one request N mulN eN markN f W G unitW O roots

theorem map_succ_selected (hM : FirstOrder.Theory.Models M nativeZF)
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule lengthBound history)
    (hF : ConstructionTowerTransitions.Matrix lengthBound history zero P F)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i lengthBound)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j lengthBound)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf j i) :
    ∃ raw, SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F i j raw := by
  have hLength := hCtx.2.2.2.2.2.2.2.2.2.1
  have hz := hCtx.2.2.2.2.2.2.2.1
  have hValid := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  obtain ⟨code,hCode,_⟩ := hValid.1.1.2 j hj
  obtain ⟨prior,hRestrict,hOp⟩ := hRec.2 j hj code hCode
  have hPriorRec := Structure.IsRecursiveSequence.restriction hRec hj hRestrict
  have hPriorSub : (Project.FirstOrderSemantics.reduct M).MemberSubset j lengthBound :=
    hLength.transitive j hj
  have hPriorValid := ConstructionTowerIterationValidity.recursive_valid hM hCtx hPriorRec hPriorSub
  have hGood : Good hM w Q R top D mul e mark H C lengthBound prior j :=
    ⟨hLength.mem hj,hj,hPriorValid⟩
  have hCase := (ConstructionTowerIteration.valid_step hM hCtx hGood hOp).1
  rcases hCase with ⟨he,_⟩ | ⟨_,prev,request,hSucc,hRequest,hValue⟩ | ⟨_,hNo,_⟩
  · exact False.elim (hz i (he ▸ hs.predecessor_mem))
  · have eqPrev := ConstructionTowerIterationCases.predecessor_unique hM (hLength.mem hj) hSucc hs
    subst prev
    obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P0,F0,
      N,mulN,eN,markN,HN,CN,K,f,next,hCharts,hE,hF0,hRow,hNext,
      raw,W,G,unitW,markW,HL,LC,O,base,roots,Out,identity,NewDomains,NewOut,
      hExt,hRaw,hGraph,hOut,hSelf,hPack⟩ := hValue
    obtain ⟨hPicked,W0,G0,unit0,mark0,H0,C0,O0,base0,roots0,Out0,hRaw0,hStep,hDone,hGraph0,hOut0,
      _,hStable,hFull,hProfiles,hNatural,hSuccEq,hUnique,hSource⟩ := hExt
    obtain ⟨eW,eG,eUnit,eMark,eH,eC,eO,eBase,eRoots⟩ :=
      ConstructionRoundSelection.pack_injective hRaw0 hRaw
    subst W0; subst G0; subst unit0; subst mark0; subst H0; subst C0; subst O0; subst base0; subst roots0
    have eqOut := hUnique Out hOut.1 hGraph
    subst Out0
    have hRowGlobal : Row history i N mulN eN markN HN CN K f i := by
      obtain ⟨c,hc,hp⟩ := hRow
      exact ⟨c,((hRestrict.2 i c).mp hc).2,hp⟩
    have hTarget : Row history j W G unitW markW HL LC NewOut base j := ⟨code,hCode,hPack⟩
    obtain ⟨_,_,_,next0,id0,_,_,hId0,hIdentity0⟩ :=
      hPriorValid.2.1 i hs.predecessor_mem N mulN eN markN HN CN K f hRow
    obtain ⟨leg,hLeg,_⟩ := hOut.1.2 i hs.predecessor_mem
    have eqLeg := hSuccEq i id0 leg hs.predecessor_mem hId0 hIdentity0 hLeg
    have hOldO : PureKuratowski.PairMember M i O Out := eqLeg ▸ hLeg
    obtain ⟨_,_,_,_,_,hNewGraph,_⟩ := hSelf
    have hNewO : PureKuratowski.PairMember M i O NewOut :=
      (hNewGraph i O).mpr (Or.inl hOldO)
    have hGlobalO : Product F i j O :=
      (ConstructionTowerTransitions.matrix_at hValid.1 hF hi hj
        (Or.inl hs.predecessor_mem) (row_field 6 hTarget)).mpr hNewO
    exact ⟨raw,request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,
      hRequest,hRowGlobal,hTarget,hPicked,hRaw,hStep,hDone,hGlobalO,hSource⟩
  · exact False.elim (hNo ⟨i,hs⟩)

theorem map_succ (hM : FirstOrder.Theory.Models M nativeZF)
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule lengthBound history)
    (hF : ConstructionTowerTransitions.Matrix lengthBound history zero P F)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i lengthBound)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j lengthBound)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf j i) :
    SuccessorAt hM w Q R top D mul e mark H C zero one Schedule history F i j := by
  obtain ⟨raw,request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,
    hRequest,hRowI,hRowJ,_,_,hStep,hDone,hO,hSource⟩ :=
    map_succ_selected hM hCtx hRec hF hi hj hs
  exact ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,
    hRequest,hRowI,hRowJ,hStep,hDone,hO,hSource⟩



def successorAt {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F i j : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge
  Schedule.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (18 : Fin
  (m+19)))) (.conj (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (17 : Fin
  (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (13 : Fin (m+19)) (12 : Fin (m+19)) (11 :
  Fin (m+19)) (10 : Fin (m+19))
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
  (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (6 : Fin (m+19)) (5 : Fin (m+19)) (4 : Fin (m+19)) (3 : Fin
  (m+19)) (2 : Fin (m+19))
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionRoundStepSyntax.step
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (17 : Fin
  (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (13 : Fin (m+19)) (12 : Fin (m+19)) (10 :
  Fin (m+19)) (9 : Fin (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (6 : Fin (m+19)) (5 : Fin (m+19)) (4 : Fin
  (m+19)) (1 : Fin (m+19)) (2 : Fin (m+19))) (.conj (ConstructionRoundSelection.done
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (18 :
  Fin (m+19)) (9 : Fin (m+19)) (8 : Fin (m+19)) (6 : Fin (m+19)) (1 : Fin (m+19)) (2 : Fin (m+19)) (0 : Fin (m+19)))
  (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
  (m+19)))) (ConstructionRoundSource.provenance w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (18 : Fin (m+19)) (17 : Fin (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (10 : Fin (m+19)) (9 : Fin (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (1 : Fin (m+19)) (0 : Fin (m+19))))))))))))))))))))))))))))

theorem successorAt_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F i j : Fin m) :
    (successorAt w Q R top D mul e mark H C zero one Schedule history F i j).FreeClosed := by
  simp -implicitDefEqProofs [successorAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRoundStepSyntax.step_freeClosed,ConstructionRoundSelection.done_freeClosed,ConstructionRoundSource.provenance_freeClosed]

theorem successorAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one Schedule history F i j : Fin m) :
    Project.Formula.satisfies env (successorAt w Q R top D mul e mark H C zero one Schedule history F i j) ↔ SuccessorAt hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound Schedule) (env.bound history) (env.bound F) (env.bound i) (env.bound j) := by
  simp only [successorAt,SuccessorAt,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,

    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerHistory.row_semantics hM,ConstructionRoundStepSyntax.step_semantics hM,ConstructionRoundSelection.done_semantics hM,ForcingDiagramOrder.product_semantics (M := M),ConstructionRoundSource.provenance_semantics hM]
  rfl

def mapSuccSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 20 (.imp (ConstructionTowerIterationCases.context (0 : Fin 20) (1 : Fin 20)
    (2 : Fin 20) (3 : Fin 20) (4 : Fin 20) (5 : Fin 20) (6 : Fin 20) (7 : Fin 20) (8 : Fin 20) (9 : Fin 20)
    (10 : Fin 20) (11 : Fin 20) (12 : Fin 20) (13 : Fin 20) (14 : Fin 20)) (.imp
    (ConstructionTowerIteration.recursive (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20)
    (5 : Fin 20) (6 : Fin 20) (7 : Fin 20) (8 : Fin 20) (9 : Fin 20) (10 : Fin 20) (11 : Fin 20) (13 : Fin
    20) (14 : Fin 20) (13 : Fin 20) (15 : Fin 20)) (.imp (ConstructionTowerTransitions.matrix (13 : Fin 20)
    (15 : Fin 20) (10 : Fin 20) (16 : Fin 20) (17 : Fin 20)) (.imp (.mem (.bound (18 : Fin 20)) (.bound (13
    : Fin 20))) (.imp (.mem (.bound (19 : Fin 20)) (.bound (13 : Fin 20))) (.imp
    (Project.Formula.isSuccessor (.bound (19 : Fin 20)) (.bound (18 : Fin 20))) (successorAt (0 : Fin 20) (1
    : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20) (5 : Fin 20) (6 : Fin 20) (7 : Fin 20) (8 : Fin 20) (9
    : Fin 20) (10 : Fin 20) (11 : Fin 20) (14 : Fin 20) (15 : Fin 20) (17 : Fin 20) (18 : Fin 20) (19 : Fin
    20)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionTowerIterationCases.context_freeClosed,ConstructionTowerIteration.recursive_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,Project.Formula.isSuccessor,successorAt_freeClosed]

theorem mapSucc_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence mapSuccSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) mapSuccSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,
    ConstructionTowerIterationCases.context_semantics hM,ConstructionTowerIteration.recursive_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,successorAt_semantics hM]
  exact fun hCtx hRec hF hi hj hs => map_succ hM hCtx hRec hF hi hj hs

theorem mapSucc_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence mapSuccSentence) := ModelTransfer.derives (fun _ hM => mapSucc_models hM)

theorem exists_tower (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule) :
    ∃ history Domains Muls Units Marks Heights Costs Incoming Origins Times E P F,
      Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule lengthBound history ∧
      Valid hM w Q R top D mul e mark H C lengthBound history ∧
      ConstructionTowerHistory.Charts lengthBound history Domains Muls Units Marks Heights Costs Incoming Origins Times ∧
      ForcingConditionGraphs.IdentityGraph lengthBound Times ∧
      ConstructionTowerTransitions.Order lengthBound E ∧
      ConstructionTowerTransitions.Matrix lengthBound history zero P F ∧
      ConstructionTowerDiagram.Data hM w Q R top D mul e mark H C lengthBound E Domains F Muls Units Marks Heights Costs Origins ∧
      ∀ i j, (Project.FirstOrderSemantics.reduct M).mem i lengthBound →
        (Project.FirstOrderSemantics.reduct M).mem j lengthBound →
        (Project.FirstOrderSemantics.reduct M).SuccessorOf j i →
        SuccessorAt hM w Q R top D mul e mark H C zero one Schedule history F i j := by
  obtain ⟨history,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    hRec,hValid,hCharts,hTime,hE,hF,hData⟩ :=
    ConstructionTowerIterationValidity.exists_tower hM hOrder hCtx
  exact ⟨history,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    hRec,hValid,hCharts,hTime,hE,hF,hData,fun _ _ hi hj hs => map_succ hM hCtx hRec hF hi hj hs⟩

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 15 (.imp (ConstructionTowerIterationCases.context (0 : Fin 15) (1 : Fin 15)
    (2 : Fin 15) (3 : Fin 15) (4 : Fin 15) (5 : Fin 15) (6 : Fin 15) (7 : Fin 15) (8 : Fin 15) (9 : Fin 15)
    (10 : Fin 15) (11 : Fin 15) (12 : Fin 15) (13 : Fin 15) (14 : Fin 15)) (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (ConstructionTowerIteration.recursive (0 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (14 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin 28)) (.conj
    (ConstructionTowerValidity.valid (0 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin 28)) (.conj
    (ConstructionTowerHistory.charts (13 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin 28) (11 : Fin 28) (10 :
    Fin 28) (9 : Fin 28) (8 : Fin 28) (7 : Fin 28) (6 : Fin 28) (5 : Fin 28) (4 : Fin 28) (3 : Fin 28))
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph (13 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin 28))) (.conj
    (ConstructionTowerTransitions.order (13 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin 28)) (.conj
    (ConstructionTowerTransitions.matrix (13 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin 28) (10 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 28) (0 : Fin 28)) (.conj
    (ConstructionTowerDiagram.data (0 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin 28) (11 : Fin 28) (0 : Fin
    28) (10 : Fin 28) (9 : Fin 28) (8 : Fin 28) (7 : Fin 28) (6 : Fin 28) (4 : Fin 28)) (.forallE (.forallE
    (.imp (.mem (.bound (1 : Fin 30)) (.bound (13 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (0
    : Fin 30)) (.bound (13 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
    (Project.Formula.isSuccessor (.bound (0 : Fin 30)) (.bound (1 : Fin 30))) (successorAt (0 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (14 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin 28).succ.succ
    (0 : Fin 28).succ.succ (1 : Fin 30) (0 : Fin 30)))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionTowerIterationCases.context_freeClosed,ConstructionTowerIteration.recursive_freeClosed,
      ConstructionTowerValidity.valid_freeClosed,ConstructionTowerHistory.charts_freeClosed,
      ConstructionTowerTransitions.order_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,
      ConstructionTowerDiagram.data_freeClosed,Project.Formula.isSuccessor,successorAt_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,
    ConstructionTowerIterationCases.context_semantics hM,ConstructionTowerIteration.recursive_semantics hM,
    ConstructionTowerValidity.valid_semantics hM,ConstructionTowerHistory.charts_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.identityGraph_semantics (M := M),
    ConstructionTowerTransitions.order_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,
    ConstructionTowerDiagram.data_semantics hM,successorAt_semantics hM]
  exact fun hCtx => exists_tower hM hOrder hCtx

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) constructionSentence).mp
    (construction_models (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))


def selectedAt {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F i j raw : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge
  Schedule.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (18 : Fin
  (m+19)))) (.conj (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (17 : Fin
  (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (13 : Fin (m+19)) (12 : Fin (m+19)) (11 :
  Fin (m+19)) (10 : Fin (m+19))
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
  (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (6 : Fin (m+19)) (5 : Fin (m+19)) (4 : Fin (m+19)) (3 : Fin
  (m+19)) (2 : Fin (m+19))
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionRoundSelection.picked
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (17 : Fin
  (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (13 : Fin (m+19)) (12 : Fin (m+19)) (10 :
  Fin (m+19)) (18 : Fin (m+19))
  raw.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionRoundSelection.pack (9 : Fin (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (6 : Fin (m+19)) (5 :
  Fin (m+19)) (4 : Fin (m+19)) (1 : Fin (m+19)) (2 : Fin (m+19)) (0 : Fin (m+19))
  raw.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionRoundStepSyntax.step
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (17 : Fin
  (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (13 : Fin (m+19)) (12 : Fin (m+19)) (10 :
  Fin (m+19)) (9 : Fin (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (6 : Fin (m+19)) (5 : Fin (m+19)) (4 : Fin
  (m+19)) (1 : Fin (m+19)) (2 : Fin (m+19))) (.conj (ConstructionRoundSelection.done
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (18 :
  Fin (m+19)) (9 : Fin (m+19)) (8 : Fin (m+19)) (6 : Fin (m+19)) (1 : Fin (m+19)) (2 : Fin (m+19)) (0 : Fin
  (m+19))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
  (m+19)))) (ConstructionRoundSource.provenance
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (18 :
  Fin (m+19)) (17 : Fin (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (10 : Fin (m+19)) (9 :
  Fin (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (1 : Fin (m+19)) (0 : Fin
  (m+19))))))))))))))))))))))))))))))

theorem selectedAt_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F i j raw : Fin m) :
    (selectedAt w Q R top D mul e mark H C zero one Schedule history F i j raw).FreeClosed := by
  simp -implicitDefEqProofs [selectedAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRoundSelection.picked_freeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionRoundStepSyntax.step_freeClosed,ConstructionRoundSelection.done_freeClosed,ConstructionRoundSource.provenance_freeClosed]

theorem selectedAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one Schedule history F i j raw : Fin m) :
    Project.Formula.satisfies env (selectedAt w Q R top D mul e mark H C zero one Schedule history F i j raw) ↔ SelectedAt hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound Schedule) (env.bound history) (env.bound F) (env.bound i) (env.bound j) (env.bound raw) := by
  simp only [selectedAt,SelectedAt,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,

    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerHistory.row_semantics hM,ConstructionRoundSelection.picked_semantics hM,ConstructionRoundSelection.pack_semantics hM,ConstructionRoundStepSyntax.step_semantics hM,ConstructionRoundSelection.done_semantics hM,ConstructionRoundSource.provenance_semantics hM,ForcingDiagramOrder.product_semantics (M := M)]
  rfl


end PPAC.Migration.ConstructionTowerMapSucc
