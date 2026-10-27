/- Pinned ConstructionIteration / Round.underFunctor: prove the ACTUAL
recursive history fully valid, using INTERNAL ordinal induction with the
explicit pure counterexample formula. No Type-level well-foundedness,
external standard length, or supplied valid recursive history. -/
import PPAC.Migration.ConstructionTowerIteration

namespace PPAC.Migration.ConstructionTowerIterationValidity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Records Field)
open ConstructionTowerValidity (Valid)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Good Operation Recursive)
open ForcingConditionGraphs (FunctionOn)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one u lengthBound Schedule length history : M.Carrier .set}

theorem function_of_sequence (hM : FirstOrder.Theory.Models M nativeZF)
    {S J : M.Carrier .set}
    (hSeq : (Project.FirstOrderSemantics.reduct M).IsSequenceOfLength
      (KuratowskiZF.interpretation hM) S J) : FunctionOn J S := by
  constructor
  · intro row hrow
    obtain ⟨x,y,hc⟩ := hSeq.2.1.1 row hrow
    exact ⟨x,y,(hSeq.2.2 x).mpr ⟨y,row,hc,hrow⟩,hc⟩
  · intro x hx
    obtain ⟨y,hy⟩ := (hSeq.2.2 x).mp hx
    exact ⟨y,hy,fun z hz => hSeq.2.1.2 x z y hz hy⟩

/-- Full validity is local to ONE valid initial segment containing the
largest mentioned index. This is a history-locality proof, not a new
algebraic colimit construction. -/
theorem valid_of_cover (hM : FirstOrder.Theory.Models M nativeZF)
    (hLength : (Project.FirstOrderSemantics.reduct M).IsOrdinal length)
    (hFn : FunctionOn length history)
    (hCover : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i length →
      ∃ next segment, (Project.FirstOrderSemantics.reduct M).SuccessorOf next i ∧
        Valid hM w Q R top D mul e mark H C next segment ∧
        (Project.FirstOrderSemantics.reduct M).IsRestrictionOf
          (KuratowskiZF.interpretation hM) segment history next) :
    Valid hM w Q R top D mul e mark H C length history := by
  have row_iff {next segment i A m v a U V K f time}
      (hr : (Project.FirstOrderSemantics.reduct M).IsRestrictionOf
        (KuratowskiZF.interpretation hM) segment history next)
      (hi : (Project.FirstOrderSemantics.reduct M).mem i next) :
      Row segment i A m v a U V K f time ↔ Row history i A m v a U V K f time := by
    constructor
    · rintro ⟨code,hc,hp⟩
      exact ⟨code,((hr.2 i code).mp hc).2,hp⟩
    · rintro ⟨code,hc,hp⟩
      exact ⟨code,(hr.2 i code).mpr ⟨hi,hc⟩,hp⟩
  have field_iff {next segment i value} (k : Fin 9)
      (hr : (Project.FirstOrderSemantics.reduct M).IsRestrictionOf
        (KuratowskiZF.interpretation hM) segment history next)
      (hi : (Project.FirstOrderSemantics.reduct M).mem i next) :
      Field k segment i value ↔ Field k history i value := by
    constructor
    · rintro ⟨A,m,v,a,U,V,K,f,time,hRow,he⟩
      exact ⟨A,m,v,a,U,V,K,f,time,(row_iff hr hi).mp hRow,he⟩
    · rintro ⟨A,m,v,a,U,V,K,f,time,hRow,he⟩
      exact ⟨A,m,v,a,U,V,K,f,time,(row_iff hr hi).mpr hRow,he⟩
  have before_mem {next i j}
      (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf next j)
      (hij : ConstructionTowerTransitions.Before i j) :
      (Project.FirstOrderSemantics.reduct M).mem i next := by
    apply (hs i).mpr
    rcases hij with hi | he
    · exact Or.inl hi
    · subst i
      exact Or.inr fun _ => Iff.rfl
  refine ⟨⟨hFn,?_⟩,?_,?_,?_,?_⟩
  · intro i hi
    obtain ⟨next,segment,hs,hV,hr⟩ := hCover i hi
    obtain ⟨A,m,v,a,U,V,K,f,hRow⟩ := hV.1.2 i hs.predecessor_mem
    exact ⟨A,m,v,a,U,V,K,f,(row_iff hr hs.predecessor_mem).mp hRow⟩
  · intro i hi A m v a U V K f hRow
    obtain ⟨next,segment,hs,hV,hr⟩ := hCover i hi
    exact hV.2.1 i hs.predecessor_mem A m v a U V K f
      ((row_iff hr hs.predecessor_mem).mpr hRow)
  · intro i j A m v a U V K f B n z b X Y L g t _ hj bij ri rj ht
    obtain ⟨next,segment,hs,hV,hr⟩ := hCover j hj
    have hi' := before_mem hs bij
    exact hV.2.2.1 i j A m v a U V K f B n z b X Y L g t
      hi' hs.predecessor_mem bij ((row_iff hr hi').mpr ri)
      ((row_iff hr hs.predecessor_mem).mpr rj) ht
  · intro i j k L K f g h hi hj hk bij bjk hL hK hf hg hh
    obtain ⟨next,segment,hs,hV,hr⟩ := hCover k hk
    have bik : ConstructionTowerTransitions.Before i k := by
      rcases bij with hij | he
      · rcases bjk with hjk | he'
        · exact Or.inl (hLength.wellOrder.linear.trans i hi j hj k hk hij hjk)
        · subst k
          exact Or.inl hij
      · subst j
        exact bjk
    have hi' := before_mem hs bik
    have hj' := before_mem hs bjk
    exact hV.2.2.2.1 i j k L K f g h hi' hj' hs.predecessor_mem bij bjk
      ((field_iff 6 hr hj').mpr hL) ((field_iff 6 hr hs.predecessor_mem).mpr hK) hf hg hh
  · intro i j f g K t _ hj bij hf hg hK ht
    obtain ⟨next,segment,hs,hV,hr⟩ := hCover j hj
    have hi' := before_mem hs bij
    exact hV.2.2.2.2 i j f g K t hi' hs.predecessor_mem bij
      ((field_iff 7 hr hi').mpr hf) ((field_iff 7 hr hs.predecessor_mem).mpr hg)
      ((field_iff 6 hr hs.predecessor_mem).mpr hK) ht

def Correct (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one lengthBound Schedule length : M.Carrier .set) : Prop :=
  ∀ history, Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule length history →
    (Project.FirstOrderSemantics.reduct M).MemberSubset length lengthBound →
      Valid hM w Q R top D mul e mark H C length history


def correct {m : Nat} (w Q R top D mul e mark H C zero one lengthBound Schedule length : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (ConstructionTowerIteration.recursive w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ
  mark.succ H.succ C.succ zero.succ one.succ lengthBound.succ Schedule.succ length.succ (0 : Fin (m+1)))
  (.imp (.forallE (.imp (.mem (.bound (0 : Fin (m+2))) (.bound length.succ.succ)) (.mem (.bound (0 : Fin
  (m+2))) (.bound lengthBound.succ.succ)))) (ConstructionTowerValidity.valid w.succ Q.succ R.succ top.succ
  D.succ mul.succ e.succ mark.succ H.succ C.succ length.succ (0 : Fin (m+1))))))

theorem correct_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one lengthBound Schedule length : Fin m) :
    (correct w Q R top D mul e mark H C zero one lengthBound Schedule length).FreeClosed := by
  simp -implicitDefEqProofs [correct,Definitional.Formula.FreeClosed,ConstructionTowerIteration.recursive_freeClosed,ConstructionTowerValidity.valid_freeClosed]

theorem correct_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one lengthBound Schedule length : Fin m) :
    Project.Formula.satisfies env (correct w Q R top D mul e mark H C zero one lengthBound Schedule length) ↔ Correct hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound lengthBound) (env.bound Schedule) (env.bound length) := by
  simp only [correct,Correct,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionTowerIteration.recursive_semantics hM,ConstructionTowerValidity.valid_semantics hM]
  rfl


theorem recursive_valid (hM : FirstOrder.Theory.Models M nativeZF)
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule length history)
    (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset length lengthBound) :
    Valid hM w Q R top D mul e mark H C length history := by
  let rawM := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  let property : M.Carrier .set → Prop := Correct hM w Q R top D mul e mark H C zero one lengthBound Schedule
  let schema : Project.UnarySchema 14 := {
    body := correct 1 2 3 4 5 6 7 8 9 10 11 12 13 14 0
    freeClosed := correct_freeClosed .. }
  let env := ConstructionTowerIteration.operatorEnv w Q R top D mul e mark H C zero one lengthBound Schedule
  have he (index) : schema.denote env index ↔ property index :=
    correct_semantics hM (env.push index) 1 2 3 4 5 6 7 8 9 10 11 12 13 14 0
  have hAll : property length := by
    apply hRec.1.1.induction property
    · obtain ⟨bad,hBad⟩ := ZF.separation_exists_d hZF schema.neg env length
      refine ⟨bad,fun index => (hBad index).trans (and_congr_right fun _ => ?_)⟩
      simp only [Project.UnarySchema.neg,Project.Formula.satisfies_neg_iff]
      exact not_congr (he index)
    · intro current hCurrent hPrevious seq hSequence hSubset
      have hFn := function_of_sequence hM hSequence.1
      apply valid_of_cover hM hCurrent hFn
      intro i hi
      obtain ⟨value,hv,_⟩ := hFn.2 i hi
      obtain ⟨prior,hRestriction,hOp⟩ := hSequence.2 i hi value hv
      have hPriorRec := Structure.IsRecursiveSequence.restriction hSequence hi hRestriction
      have hPriorSub : rawM.MemberSubset i lengthBound :=
        fun x hx => hSubset x (hCurrent.transitive i hi x hx)
      have hPriorValid := hPrevious i hi prior hPriorRec hPriorSub
      have hGood : Good hM w Q R top D mul e mark H C lengthBound prior i :=
        ⟨hCurrent.mem hi,hSubset i hi,hPriorValid⟩
      obtain ⟨next,segment,hAppend,hValid⟩ :=
        (ConstructionTowerIteration.valid_step hM hCtx hGood hOp).2
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
      exact ⟨next,segment,hSucc,hValid,hPrefixRestriction⟩
  exact hAll history hRec hSub

theorem exists_valid (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule) :
    ∃ history, Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule lengthBound history ∧
      Valid hM w Q R top D mul e mark H C lengthBound history := by
  have hLength := hCtx.2.2.2.2.2.2.2.2.2.1
  obtain ⟨history,hRec⟩ := ConstructionTowerIteration.recursive_exists hM hOrder hCtx hLength
  exact ⟨history,hRec,recursive_valid hM hCtx hRec (fun _ h => h)⟩

/-- Actual recursive tower WITH the original full weighted diagram, all
fromBase maps/naturality, and exact internal time table. -/
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
      ConstructionTowerDiagram.Data hM w Q R top D mul e mark H C lengthBound E Domains F Muls Units Marks Heights Costs Origins := by
  obtain ⟨history,hRec,hValid⟩ := exists_valid hM hOrder hCtx
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,hE,hF,hData⟩ :=
    ConstructionTowerDiagram.exists_data hM zero hCtx.2.2.2.2.2.2.2.2.2.1 hValid
  have hCopy := hCharts
  obtain ⟨_,_,_,_,_,_,_,_,cT⟩ := hCharts
  exact ⟨history,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    hRec,hValid,hCopy,ConstructionTowerHistory.time_identity hValid.1 cT,hE,hF,hData⟩

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
    15).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 28) (0 : Fin 28))
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
    28) (10 : Fin 28) (9 : Fin 28) (8 : Fin 28) (7 : Fin 28) (6 : Fin 28) (4 : Fin 28)))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionTowerIterationCases.context_freeClosed,ConstructionTowerIteration.recursive_freeClosed,
      ConstructionTowerValidity.valid_freeClosed,ConstructionTowerHistory.charts_freeClosed,
      ConstructionTowerTransitions.order_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,
      ConstructionTowerDiagram.data_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,ConstructionTowerIterationCases.context_semantics hM,
    ConstructionTowerIteration.recursive_semantics hM,ConstructionTowerValidity.valid_semantics hM,
    ConstructionTowerHistory.charts_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.identityGraph_semantics (M := M),
    ConstructionTowerTransitions.order_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,
    ConstructionTowerDiagram.data_semantics hM]
  exact fun hCtx => exists_tower hM hOrder hCtx

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) constructionSentence).mp
    (construction_models (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

end PPAC.Migration.ConstructionTowerIterationValidity
