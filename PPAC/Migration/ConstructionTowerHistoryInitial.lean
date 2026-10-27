/- Pinned Under.mk(identity) initial stage: build the ACTUAL first
record history and prove full validity, including all Hom/profile/identity/
composition/base-naturality clauses. Use the accepted initial value and
unchanged native constant-function producer; no supplied valid history. -/
import PPAC.Migration.ConstructionTowerHistoryLimit

namespace PPAC.Migration.ConstructionTowerHistoryInitial
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Records Field)
open ConstructionTowerValidity (Valid row_field)
open ForcingConditionGraphs (FunctionOn function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one output : M.Carrier .set}

theorem history_of_value (hM : FirstOrder.Theory.Models M nativeZF)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hOne : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hValue : ConstructionTowerInitial.Value hM w Q R top D mul e mark H C zero one output) :
    ∃ S, ConstructionRequestCarrier.ConstantNode one output S ∧
      Valid hM w Q R top D mul e mark H C one S := by
  obtain ⟨hObj,identity,K,hMaps,hId,hFields,hProfiles,hKF,hKG,hKZero,hNatural,hPack⟩ := hValue
  obtain ⟨z,hz0,hSucc⟩ := hOne
  have eqz := (ModelTransfer.extensionality hM).eq_of_same_members z zero
    (fun x => ⟨fun h => False.elim (hz0 x h),fun h => False.elim (hz x h)⟩)
  subst z
  have mem_one (i) : (Project.FirstOrderSemantics.reduct M).mem i one ↔ i = zero := by
    constructor
    · intro hi
      rcases (hSucc i).mp hi with hi | he
      · exact False.elim (hz i hi)
      · exact (ModelTransfer.extensionality hM).eq_of_same_members i zero he
    · intro he
      subst i
      exact hSucc.predecessor_mem
  have hzOne := (mem_one zero).mpr rfl
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨singleton,hSingleton⟩ := KP.exists_singleton (ZF.modelsKP hZF) output
  obtain ⟨S,hS,hSG⟩ := ZF.exists_constantFunction hZF (KuratowskiZF.interpretation hM)
    (source := one) ((hSingleton output).mpr rfl)
  have hFn := ((ForcingSupportSize.native_mapsTo hM one singleton S).mpr hS).1
  have hRecords : Records one S := by
    refine ⟨hFn,fun i hi => ?_⟩
    have he := (mem_one i).mp hi
    subst i
    exact ⟨D,mul,e,mark,H,C,K,identity,output,(hSG zero output).mpr ⟨hzOne,rfl⟩,hPack⟩
  have row0 : Row S zero D mul e mark H C K identity zero :=
    ⟨output,(hSG zero output).mpr ⟨hzOne,rfl⟩,hPack⟩
  have decode {i N m u a W V L f : M.Carrier .set}
      (hi : (Project.FirstOrderSemantics.reduct M).mem i one)
      (hRow : Row S i N m u a W V L f i) :
      i = zero ∧ N = D ∧ m = mul ∧ u = e ∧ a = mark ∧ W = H ∧ V = C ∧ L = K ∧ f = identity := by
    have he := (mem_one i).mp hi
    subst i
    obtain ⟨code,hc,hp⟩ := hRow
    have hec := ((hSG zero code).mp hc).2
    subst code
    obtain ⟨hN,hm,hu,ha,hW,hV,hL,hf,_⟩ := ConstructionRoundSelection.pack_injective hp hPack
    exact ⟨rfl,hN,hm,hu,ha,hW,hV,hL,hf⟩
  have comp : ConstructionProbeMappedPath.NodeMap identity identity identity :=
    hNatural zero identity identity hzOne hKZero hKZero
  refine ⟨S,hSG,hRecords,?_,?_,?_,?_⟩
  · intro i hi N m u a W V L f hRow
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := decode hi hRow
    exact ⟨hObj,hFields,hProfiles,one,_,hSucc,hKF,hKZero,hId⟩
  · intro i j N m u a W V L f N' m' u' a' W' V' L' f' t hi hj _ ri rj ht
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := decode hi ri
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := decode hj rj
    have he := function_unique hKF ht hKZero
    subst t
    exact ⟨hFields,hProfiles⟩
  · intro i j k L K' f g h hi hj hk _ _ hL hK' hf hg hh
    have ei := (mem_one i).mp hi
    have ej := (mem_one j).mp hj
    have ek := (mem_one k).mp hk
    subst i; subst j; subst k
    have eL := ConstructionTowerHistory.field_unique 6 hFn hL (row_field 6 row0)
    have eK := ConstructionTowerHistory.field_unique 6 hFn hK' (row_field 6 row0)
    subst L; subst K'
    have ef := function_unique hKF hf hKZero
    have eg := function_unique hKF hg hKZero
    have eh := function_unique hKF hh hKZero
    subst f; subst g; subst h
    exact comp
  · intro i j f g K' t hi hj _ hf hg hK' ht
    have ei := (mem_one i).mp hi
    have ej := (mem_one j).mp hj
    subst i; subst j
    have ef := ConstructionTowerHistory.field_unique 7 hFn hf (row_field 7 row0)
    have eg := ConstructionTowerHistory.field_unique 7 hFn hg (row_field 7 row0)
    have eK := ConstructionTowerHistory.field_unique 6 hFn hK' (row_field 6 row0)
    subst f; subst g; subst K'
    have et := function_unique hKF ht hKZero
    subst t
    exact comp

def Initialized (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one S : M.Carrier .set) : Prop :=
  ∃ output, ConstructionTowerInitial.Value hM w Q R top D mul e mark H C zero one output ∧
    ConstructionRequestCarrier.ConstantNode one output S ∧
    Valid hM w Q R top D mul e mark H C one S

theorem exists_initialized (hM : FirstOrder.Theory.Models M nativeZF)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hTop : ConstructionRealCuts.Cut hM w Q top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hOne : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) :
    ∃ S, Initialized hM w Q R top D mul e mark H C zero one S := by
  obtain ⟨output,hValue,_⟩ := ConstructionTowerInitial.exists_value hM hR hTop hObj hz hOne
  obtain ⟨S,hConst,hValid⟩ := history_of_value hM hz hOne hValue
  exact ⟨S,output,hValue,hConst,hValid⟩


def initialized {m : Nat} (w Q R top D mul e mark H C zero one S : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ConstructionTowerInitial.value w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ
  mark.succ H.succ C.succ zero.succ one.succ (0 : Fin (m+1))) (.conj
  (ConstructionRequestCarrier.constantNode one.succ (0 : Fin (m+1)) S.succ) (ConstructionTowerValidity.valid
  w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ one.succ S.succ))))

theorem initialized_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one S : Fin m) :
    (initialized w Q R top D mul e mark H C zero one S).FreeClosed := by
  simp -implicitDefEqProofs [initialized,Definitional.Formula.FreeClosed,ConstructionTowerInitial.value_freeClosed,ConstructionRequestCarrier.constantNode_freeClosed,ConstructionTowerValidity.valid_freeClosed]

theorem initialized_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one S : Fin m) :
    Project.Formula.satisfies env (initialized w Q R top D mul e mark H C zero one S) ↔ Initialized hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound S) := by
  simp only [initialized,Initialized,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionTowerInitial.value_semantics hM,ConstructionRequestCarrier.constantNode_semantics hM,ConstructionTowerValidity.valid_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 12 (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 12) (1 : Fin 12) (2 :
    Fin 12)) (.imp (ConstructionRealCuts.cut (0 : Fin 12) (1 : Fin 12) (3 : Fin 12)) (.imp
    (ConstructionRoundStepSyntax.objectFields (0 : Fin 12) (1 : Fin 12) (2 : Fin 12) (3 : Fin 12) (4 : Fin
    12) (5 : Fin 12) (6 : Fin 12) (7 : Fin 12) (8 : Fin 12) (9 : Fin 12)) (.imp (Project.Formula.isEmpty
    (.bound (10 : Fin 12))) (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 12))) (.existsE
    (initialized (0 : Fin 12).succ (1 : Fin 12).succ (2 : Fin 12).succ (3 : Fin 12).succ (4 : Fin 12).succ
    (5 : Fin 12).succ (6 : Fin 12).succ (7 : Fin 12).succ (8 : Fin 12).succ (9 : Fin 12).succ (10 : Fin
    12).succ (11 : Fin 12).succ (0 : Fin 13)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,
      Project.Formula.isEmpty,Project.Formula.isOrdinalOne,initialized_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Term.eval_bound,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionRealCuts.cut_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,
    initialized_semantics hM]
  exact fun hR hTop hObj hz hOne => exists_initialized hM hR hTop hObj hz hOne

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionTowerHistoryInitial
