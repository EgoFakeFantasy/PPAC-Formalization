/- Pinned MonoidRounds.Round.cardinal_le / ContinuousTower.cardinal_le.
Actual SAME source recursive tower; INTERNAL ordinal induction on a pure
stage-size formula. Reuse existing full successor SizeBound and actual
canonical colimit Bound; object Choice explicit only for source union bound. -/
import PPAC.Migration.ConstructionTowerMapSucc

namespace PPAC.Migration.ConstructionTowerCardinality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small)
open ConstructionTowerHistory (Field Row)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive Good)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one u lengthBound Schedule history mu : M.Carrier .set}

def At (S mu i : M.Carrier .set) : Prop := ∀ N, Field 0 S i N → Small N mu

def AllSmall (J S mu : M.Carrier .set) : Prop := ∀ i,
  (Project.FirstOrderSemantics.reduct M).mem i J → At S mu i


def atStage {m : Nat} (S mu i : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (ConstructionTowerHistory.field 0 S.succ i.succ (0 : Fin (m+1))) (ProjectSyntax.encode id
  (ForcingSupportSize.small (0 : Fin (m+1)) mu.succ))))

theorem atStage_freeClosed {m : Nat} (S mu i : Fin m) :
    (atStage S mu i).FreeClosed := by
  simp -implicitDefEqProofs [atStage,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.field_freeClosed]

theorem atStage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S mu i : Fin m) :
    Project.Formula.satisfies env (atStage S mu i) ↔ At (env.bound S) (env.bound mu) (env.bound i) := by
  simp only [atStage,At,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionTowerHistory.field_semantics hM 0,ForcingSupportSize.small_semantics (M := M)]
  rfl


def allSmall {m : Nat} (J S mu : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound (0 : Fin (m+1))) (.bound J.succ)) (atStage S.succ mu.succ (0 : Fin (m+1)))))

theorem allSmall_freeClosed {m : Nat} (J S mu : Fin m) :
    (allSmall J S mu).FreeClosed := by
  simp -implicitDefEqProofs [allSmall,Definitional.Formula.FreeClosed,atStage_freeClosed]

theorem allSmall_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J S mu : Fin m) :
    Project.Formula.satisfies env (allSmall J S mu) ↔ AllSmall (env.bound J) (env.bound S) (env.bound mu) := by
  simp only [allSmall,AllSmall,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    atStage_semantics hM]
  rfl


theorem stage_small (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule lengthBound history)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hD : Small D mu) (hLengthSmall : Small lengthBound mu) : AllSmall lengthBound history mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let rawM := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have hLength := hCtx.2.2.2.2.2.2.2.2.2.1
  have hw := hCtx.1
  have hValid := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  let property : M.Carrier .set → Prop := fun i => rawM.mem i lengthBound → At history mu i
  let schema : Project.UnarySchema 3 := {
    body := .imp (.mem (.bound 0) (.bound 1)) (atStage 2 3 0)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,atStage_freeClosed] }
  let env : SetTheory.Env rawM 3 := {
    bound := Fin.cases lengthBound (Fin.cases history (Fin.cases mu Fin.elim0)), free := fun _ => zero }
  have he (i) : schema.denote env i ↔ property i := by
    simp only [Project.UnarySchema.denote,schema,Project.Formula.satisfies_imp_iff,
      Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,atStage_semantics hM]
    rfl
  intro i hi
  have hAll : property i := by
    apply (hLength.mem hi).induction property
    · obtain ⟨bad,hBad⟩ := ZF.separation_exists_d hZF schema.neg env i
      refine ⟨bad,fun index => (hBad index).trans (and_congr_right fun _ => ?_)⟩
      simp only [Project.UnarySchema.neg,Project.Formula.satisfies_neg_iff]
      exact not_congr (he index)
    · intro current hCurrent hPrevious hCurrentBound N hField
      obtain ⟨N0,m0,e0,a0,H0,C0,K0,f0,time,⟨code,hCode,hPack⟩,eqN⟩ := hField
      change N = N0 at eqN
      subst N0
      obtain ⟨prior,hRestrict,hOp⟩ := hRec.2 current hCurrentBound code hCode
      have hPriorRec := Structure.IsRecursiveSequence.restriction hRec hCurrentBound hRestrict
      have hPriorValid := ConstructionTowerIterationValidity.recursive_valid hM hCtx hPriorRec
        (hLength.transitive current hCurrentBound)
      have hGood : Good hM w Q R top D mul e mark H C lengthBound prior current :=
        ⟨hCurrent,hCurrentBound,hPriorValid⟩
      have hOldSmall (j L) (hj : rawM.mem j current) (hF : Field 0 prior j L) : Small L mu := by
        obtain ⟨A,m,e,a,H,C,K,f,t,⟨c,hc,hp⟩,eqL⟩ := hF
        have hGlobal : Row history j A m e a H C K f t :=
          ⟨c,((hRestrict.2 j c).mp hc).2,hp⟩
        exact hPrevious j hj (hLength.transitive current hCurrentBound j hj) L
          ⟨A,m,e,a,H,C,K,f,t,hGlobal,eqL⟩
      have hCase := (ConstructionTowerIteration.valid_step hM hCtx hGood hOp).1
      rcases hCase with ⟨_,hInit⟩ | ⟨_,prev,request,hSucc,_,hSuccValue⟩ | ⟨_,_,hLimitValue⟩
      · obtain ⟨_,identity,K,_,_,_,_,_,_,_,_,hInitialPack⟩ := hInit
        have eqD := (ConstructionRoundSelection.pack_injective hInitialPack hPack).1
        exact eqD ▸ hD
      · obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
          old,mOld,eOld,aOld,HOld,COld,K,f,next,_,_,_,hOldRow,_,
          raw,W,G,unitW,markW,HL,LC,O,base,roots,Out,identity,NewDomains,NewOut,
          hExt,hRaw,_,_,_,hNextPack⟩ := hSuccValue
        obtain ⟨_,W0,G0,unit0,mark0,HL0,LC0,O0,base0,roots0,Out0,hRaw0,hStep,_⟩ := hExt
        have hOld := hOldSmall prev old hSucc.predecessor_mem (ConstructionTowerValidity.row_field 0 hOldRow)
        have hW0 := hStep.1.2.2.2.2.2 mu hmu hOld
        have eqW := (ConstructionRoundSelection.pack_injective hRaw0 hRaw).1
        have eqN := (ConstructionRoundSelection.pack_injective hNextPack hPack).1
        exact (eqW.trans eqN) ▸ hW0
      · obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,_,_,
          L,G,unitL,markL,HL,LC,K,base,next,identity,NewDomains,NewOut,
          hResult,_,_,hLimitPack⟩ := hLimitValue
        obtain ⟨rep,projection,B,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hBound,_⟩ := hResult
        have hCurrentSmall : Small current mu := ForcingSupportSize.small_subset hM
          (hLength.transitive current hCurrentBound) hLengthSmall
        have hStages : ConstructionDirectedCardinality.StageSmall current Domains mu := by
          intro j A hj hAj
          have hField := (hCharts.1.2 j A).mp hAj
          exact hOldSmall j A hj hField.2
        have hL := hBound hChoice w mu hw hmu hCurrentSmall hStages
        have eqL := (ConstructionRoundSelection.pack_injective hLimitPack hPack).1
        exact eqL ▸ hL
  exact hAll hi


def boundSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 17 (.imp (ConstructionDirectedCardinality.choice ) (.imp
    (ConstructionTowerIterationCases.context (0 : Fin 17) (1 : Fin 17) (2 : Fin 17) (3 : Fin 17) (4 : Fin
    17) (5 : Fin 17) (6 : Fin 17) (7 : Fin 17) (8 : Fin 17) (9 : Fin 17) (10 : Fin 17) (11 : Fin 17) (12 :
    Fin 17) (13 : Fin 17) (14 : Fin 17)) (.imp (ConstructionTowerIteration.recursive (0 : Fin 17) (1 : Fin
    17) (2 : Fin 17) (3 : Fin 17) (4 : Fin 17) (5 : Fin 17) (6 : Fin 17) (7 : Fin 17) (8 : Fin 17) (9 : Fin
    17) (10 : Fin 17) (11 : Fin 17) (13 : Fin 17) (14 : Fin 17) (13 : Fin 17) (15 : Fin 17)) (.imp
    (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound (0 : Fin 17)) (.bound (16 :
    Fin 17))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (4 : Fin 17) (16 : Fin 17))) (.imp
    (ProjectSyntax.encode id (ForcingSupportSize.small (13 : Fin 17) (16 : Fin 17))) (allSmall (13 : Fin 17)
    (15 : Fin 17) (16 : Fin 17)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionDirectedCardinality.choice_freeClosed,ConstructionTowerIterationCases.context_freeClosed,
      ConstructionTowerIteration.recursive_freeClosed,allSmall_freeClosed]

theorem bound_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence boundSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) boundSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    ConstructionDirectedCardinality.choice_semantics hM,ConstructionTowerIterationCases.context_semantics hM,
    ConstructionTowerIteration.recursive_semantics hM,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),allSmall_semantics hM]
  exact fun hc hCtx hRec hmu hD hJ => stage_small hM hc hCtx hRec hmu hD hJ

theorem bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence boundSentence) := ModelTransfer.derives (fun _ hM => bound_models hM)


theorem exists_tower (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hD : Small D mu) (hLength : Small lengthBound mu) :
    ∃ history Domains Muls Units Marks Heights Costs Incoming Origins Times E P F,
      Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule lengthBound history ∧
      ConstructionTowerValidity.Valid hM w Q R top D mul e mark H C lengthBound history ∧
      ConstructionTowerHistory.Charts lengthBound history Domains Muls Units Marks Heights Costs Incoming Origins Times ∧
      ForcingConditionGraphs.IdentityGraph lengthBound Times ∧
      ConstructionTowerTransitions.Order lengthBound E ∧
      ConstructionTowerTransitions.Matrix lengthBound history zero P F ∧
      ConstructionTowerDiagram.Data hM w Q R top D mul e mark H C lengthBound E Domains F Muls Units Marks Heights Costs Origins ∧
      (∀ i j, (Project.FirstOrderSemantics.reduct M).mem i lengthBound →
        (Project.FirstOrderSemantics.reduct M).mem j lengthBound →
        (Project.FirstOrderSemantics.reduct M).SuccessorOf j i →
        ConstructionTowerMapSucc.SuccessorAt hM w Q R top D mul e mark H C zero one Schedule history F i j) ∧
      AllSmall lengthBound history mu ∧ ConstructionDirectedCardinality.StageSmall lengthBound Domains mu := by
  obtain ⟨history,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    hRec,hValid,hCharts,hTime,hE,hF,hData,hSucc⟩ := ConstructionTowerMapSucc.exists_tower hM hOrder hCtx
  have hSmall := stage_small hM hChoice hCtx hRec hmu hD hLength
  have hStages : ConstructionDirectedCardinality.StageSmall lengthBound Domains mu := by
    intro i N hi hN
    exact hSmall i hi N ((hCharts.1.2 i N).mp hN).2
  exact ⟨history,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    hRec,hValid,hCharts,hTime,hE,hF,hData,hSucc,hSmall,hStages⟩

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 16 (.imp (ConstructionTowerIterationCases.context (0 : Fin 16) (1 : Fin 16)
    (2 : Fin 16) (3 : Fin 16) (4 : Fin 16) (5 : Fin 16) (6 : Fin 16) (7 : Fin 16) (8 : Fin 16) (9 : Fin 16)
    (10 : Fin 16) (11 : Fin 16) (12 : Fin 16) (13 : Fin 16) (14 : Fin 16)) (.imp
    (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound (0 : Fin 16)) (.bound (15 :
    Fin 16))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (4 : Fin 16) (15 : Fin 16))) (.imp
    (ProjectSyntax.encode id (ForcingSupportSize.small (13 : Fin 16) (15 : Fin 16))) (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.conj (ConstructionTowerIteration.recursive (0 : Fin
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
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (29))) (.conj
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
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (29))) (.conj
    (ConstructionTowerHistory.charts (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (29)) (11 : Fin (29)) (10
    : Fin (29)) (9 : Fin (29)) (8 : Fin (29)) (7 : Fin (29)) (6 : Fin (29)) (5 : Fin (29)) (4 : Fin (29)) (3
    : Fin (29))) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (29)))) (.conj
    (ConstructionTowerTransitions.order (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (29))) (.conj
    (ConstructionTowerTransitions.matrix (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (29)) (10 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (29)) (0 : Fin (29)))
    (.conj (ConstructionTowerDiagram.data (0 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (29)) (11 : Fin (29)) (0 :
    Fin (29)) (10 : Fin (29)) (9 : Fin (29)) (8 : Fin (29)) (7 : Fin (29)) (6 : Fin (29)) (4 : Fin (29)))
    (.conj (.forallE (.forallE (.imp (.mem (.bound (1 : Fin 31)) (.bound (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (0
    : Fin 31)) (.bound (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
    (Project.Formula.isSuccessor (.bound (0 : Fin 31)) (.bound (1 : Fin 31)))
    (ConstructionTowerMapSucc.successorAt (0 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (14 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (29)).succ.succ
    (0 : Fin (29)).succ.succ (1 : Fin 31) (0 : Fin 31))))))) (.conj (allSmall (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (29)) (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
    (ConstructionDirectedCardinality.stageSmall (13 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin (29)) (15 : Fin
    16).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionTowerIterationCases.context_freeClosed,ConstructionTowerIteration.recursive_freeClosed,
      ConstructionTowerValidity.valid_freeClosed,ConstructionTowerHistory.charts_freeClosed,
      ConstructionTowerTransitions.order_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,
      ConstructionTowerDiagram.data_freeClosed,ConstructionTowerMapSucc.successorAt_freeClosed,
      Project.Formula.isSuccessor,allSmall_freeClosed,ConstructionDirectedCardinality.stageSmall_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isSuccessor_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),
    ConstructionTowerIterationCases.context_semantics hM,ConstructionTowerIteration.recursive_semantics hM,
    ConstructionTowerValidity.valid_semantics hM,ConstructionTowerHistory.charts_semantics hM,
    ForcingConditionGraphs.identityGraph_semantics (M := M),
    ConstructionTowerTransitions.order_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,
    ConstructionTowerDiagram.data_semantics hM,ConstructionTowerMapSucc.successorAt_semantics hM,
    allSmall_semantics hM,ConstructionDirectedCardinality.stageSmall_semantics hM]
  exact fun hCtx hmu hD hJ => exists_tower hM hOrder hChoice hCtx hmu hD hJ

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

end PPAC.Migration.ConstructionTowerCardinality
