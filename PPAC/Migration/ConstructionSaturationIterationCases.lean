/- Pinned CompleteRounds.Saturation.tower / ConstructionIteration:
the SAME existing initial and canonical limit, with the accepted actual
complete-round successor. All cases preserve full Valid AND AllSmall.
No new ordinal, limit, selection, tuple, or recursion implementation. -/
import PPAC.Migration.ConstructionSaturationSuccessor

namespace PPAC.Migration.ConstructionSaturationIterationCases
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerCardinality (AllSmall)
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one u K mu lengthBound J S output : M.Carrier .set}

def Context (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one u K mu lengthBound : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsOmega w ∧
  ConstructionFractionOrder.Carrier w Q ∧ ConstructionRealCuts.CutCarrier hM w Q R ∧
  ConstructionFractionOrder.Coordinates w u one one ∧
  (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one ∧
  ConstructionRealCuts.Principal hM w Q u top ∧
  ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C ∧
  (∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero) ∧
  (Project.FirstOrderSemantics.reduct M).mem zero w ∧
  (∃ k, (Project.FirstOrderSemantics.reduct M).mem k K) ∧
  (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu ∧
  (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w ∧
  Small D mu ∧ Small K mu ∧
  (Project.FirstOrderSemantics.reduct M).IsOrdinal lengthBound ∧ Small lengthBound mu

def Case (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu J S output : M.Carrier .set) : Prop :=
  (J = zero ∧ ConstructionTowerInitial.Value hM w Q R top D mul e mark H C zero one output) ∨
  (J ≠ zero ∧ ∃ prev, (Project.FirstOrderSemantics.reduct M).SuccessorOf J prev ∧
    ConstructionSaturationSuccessor.Value hM w Q R top D mul e mark H C zero one K mu J S prev output) ∨
  (J ≠ zero ∧ ¬ (∃ prev, (Project.FirstOrderSemantics.reduct M).SuccessorOf J prev) ∧
    ConstructionTowerHistoryLimit.Value hM w Q R top D mul e mark H C J S zero output)

theorem case_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u K mu lengthBound)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hV : Valid hM w Q R top D mul e mark H C J S) (hSmall : AllSmall J S mu) :
    ∃ output, Case hM w Q R top D mul e mark H C zero one K mu J S output := by
  classical
  obtain ⟨hw,hQ,hR,hu,hone,htop,hObj,hz,hzw,hK,hmu,hpow,_,hKSmall,_,_⟩ := hCtx
  have hTop := ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) htop
  by_cases he : J = zero
  · subst J
    obtain ⟨out,hValue,_⟩ := ConstructionTowerInitial.exists_value hM hR hTop hObj hz hone
    exact ⟨out,Or.inl ⟨rfl,hValue⟩⟩
  · by_cases hs : ∃ prev, (Project.FirstOrderSemantics.reduct M).SuccessorOf J prev
    · obtain ⟨prev,hSucc⟩ := hs
      obtain ⟨out,hValue,_⟩ := ConstructionSaturationSuccessor.exists_value hM hOrder hChoice
        hw hQ hR hu hone htop hz hzw hK hmu hpow hKSmall hJ hSucc hV hSmall
      exact ⟨out,Or.inr (Or.inl ⟨he,prev,hSucc,hValue⟩)⟩
    · obtain ⟨out,hValue⟩ := ConstructionTowerHistoryLimit.exists_value hM hV hJ
        (ConstructionTowerIterationCases.nonzero_nonempty hM hz he) hw hQ hR hTop zero
      exact ⟨out,Or.inr (Or.inr ⟨he,hs,hValue⟩)⟩

theorem case_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    {x y : M.Carrier .set}
    (hx : Case hM w Q R top D mul e mark H C zero one K mu J S x)
    (hy : Case hM w Q R top D mul e mark H C zero one K mu J S y) : x = y := by
  rcases hx with ⟨he,hx⟩ | ⟨hne,p,hp,hx⟩ | ⟨hne,hno,hx⟩
  · subst J
    rcases hy with ⟨_,hy⟩ | ⟨hn,_⟩ | ⟨hn,_⟩
    · exact ConstructionTowerInitial.value_unique hM hx hy
    · exact False.elim (hn rfl)
    · exact False.elim (hn rfl)
  · rcases hy with ⟨he,_⟩ | ⟨_,p',hp',hy⟩ | ⟨_,hn,_⟩
    · exact False.elim (hne he)
    · have ep := ConstructionTowerIterationCases.predecessor_unique hM hJ hp' hp
      subst p'
      exact ConstructionSaturationSuccessor.value_unique hM hOrder hV hx hy
    · exact False.elim (hn ⟨p,hp⟩)
  · rcases hy with ⟨he,_⟩ | ⟨_,p,hp,_⟩ | ⟨_,_,hy⟩
    · exact False.elim (hne he)
    · exact False.elim (hno ⟨p,hp⟩)
    · exact ConstructionTowerHistoryLimit.value_unique hM hV hJ
        (ConstructionTowerIterationCases.nonzero_nonempty hM hz hne) hx hy

theorem case_continues (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u K mu lengthBound)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hBound : (Project.FirstOrderSemantics.reduct M).mem J lengthBound)
    (hV : Valid hM w Q R top D mul e mark H C J S) (hSmall : AllSmall J S mu)
    (hCase : Case hM w Q R top D mul e mark H C zero one K mu J S output) :
    ∃ next S', ConstructionTowerAppend.Append J S output next S' ∧
      Valid hM w Q R top D mul e mark H C next S' ∧ AllSmall next S' mu := by
  obtain ⟨hw,hQ,hR,hu,hone,htop,hObj,hz,hzw,hK,hmu,hpow,hD,hKSmall,hLength,hLengthSmall⟩ := hCtx
  have hTop := ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) htop
  rcases hCase with ⟨he,hValue⟩ | ⟨_,p,hp,hValue⟩ | ⟨_,_,hValue⟩
  · subst J
    obtain ⟨next,S',hAppend,hValid⟩ :=
      ConstructionTowerIterationCases.initial_continues hM hz hone hV.1.1 hValue
    obtain ⟨_,identity,L,_,_,_,_,_,_,_,_,hPack⟩ := hValue
    exact ⟨next,S',hAppend,hValid,ConstructionTowerCardinality.append_small hV.1.1 hSmall hPack hD hAppend⟩
  · obtain ⟨out,hValue',hUnique,next,S',hAppend,hValid,hSmall'⟩ :=
      ConstructionSaturationSuccessor.exists_value hM hOrder hChoice
        hw hQ hR hu hone htop hz hzw hK hmu hpow hKSmall hJ hp hV hSmall
    have eq := hUnique output hValue
    subst output
    exact ⟨next,S',hAppend,hValid,hSmall'⟩
  · have hValueCopy := hValue
    obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,_,_,
      L,G,unitL,markL,HL,LC,Legs,base,next,identity,NewDomains,NewOut,
      hResult,_,_,hPack⟩ := hValueCopy
    obtain ⟨rep,projection,B,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLimitBound,_⟩ := hResult
    have hCurrentSmall : Small J mu := ForcingSupportSize.small_subset hM
      (hLength.transitive J hBound) hLengthSmall
    have hStages : ConstructionDirectedCardinality.StageSmall J Domains mu := by
      intro j A hj hAj
      exact hSmall j hj A ((hCharts.1.2 j A).mp hAj).2
    have hL := hLimitBound hChoice w mu hw hmu hCurrentSmall hStages
    obtain ⟨next',S',hAppend,hValid⟩ := ConstructionTowerHistoryClosure.limit_preserves hM hJ hV hR hTop hValue
    exact ⟨next',S',hAppend,hValid,ConstructionTowerCardinality.append_small hV.1.1 hSmall hPack hL hAppend⟩

def context {m : Nat} (w Q R top D mul e mark H C zero one u K mu lengthBound : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.isOmega (.bound w)) (.conj (ConstructionFractionOrder.carrier w Q) (.conj
  (ConstructionRealCuts.cutCarrier w Q R) (.conj (ConstructionFractionOrder.coordinates w u one one) (.conj
  (Project.Formula.isOrdinalOne (.bound one)) (.conj (ConstructionRealCuts.principal w Q u top) (.conj
  (ConstructionRoundStepSyntax.objectFields w Q R top D mul e mark H C) (.conj (Project.Formula.isEmpty
  (.bound zero)) (.conj (.mem (.bound zero) (.bound w)) (.conj (.existsE (.mem (.bound (0 : Fin (m+1)))
  (.bound K.succ))) (.conj (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w)
  (.bound mu)) (.conj (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound mu)
  (.bound mu) (.bound w)) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small D mu)) (.conj
  (ProjectSyntax.encode id (ForcingSupportSize.small K mu)) (.conj (Project.Formula.isOrdinal (.bound
  lengthBound)) (ProjectSyntax.encode id (ForcingSupportSize.small lengthBound mu)))))))))))))))))

theorem context_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one u K mu lengthBound : Fin m) :
    (context w Q R top D mul e mark H C zero one u K mu lengthBound).FreeClosed := by
  simp -implicitDefEqProofs [context,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,Project.Formula.isOrdinalOne,ConstructionRealCuts.principal_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,Project.Formula.isEmpty,Project.Formula.isInfiniteCardinal,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,Project.Formula.isOrdinal]

theorem context_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one u K mu lengthBound : Fin m) :
    Project.Formula.satisfies env (context w Q R top D mul e mark H C zero one u K mu lengthBound) ↔ Context hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound u) (env.bound K) (env.bound mu) (env.bound lengthBound) := by
  simp only [context,Context,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,Project.Formula.satisfies_isOrdinalOne_iff,ConstructionRealCuts.principal_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),Project.Formula.satisfies_isOrdinal_iff]
  rfl


def caseValue {m : Nat} (w Q R top D mul e mark H C zero one K mu J S output : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (Project.Formula.extensionalEq (.bound J) (.bound zero)) (ConstructionTowerInitial.value w Q R
  top D mul e mark H C zero one output)) (.disj (.conj (.neg (Project.Formula.extensionalEq (.bound J)
  (.bound zero))) (.existsE (.conj (Project.Formula.isSuccessor (.bound J.succ) (.bound (0 : Fin (m+1))))
  (ConstructionSaturationSuccessor.value w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ
  H.succ C.succ zero.succ one.succ K.succ mu.succ J.succ S.succ (0 : Fin (m+1)) output.succ)))) (.conj (.neg
  (Project.Formula.extensionalEq (.bound J) (.bound zero))) (.conj (.neg (.existsE
  (Project.Formula.isSuccessor (.bound J.succ) (.bound (0 : Fin (m+1))))))
  (ConstructionTowerHistoryLimit.value w Q R top D mul e mark H C J S zero output)))))

theorem caseValue_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu J S output : Fin m) :
    (caseValue w Q R top D mul e mark H C zero one K mu J S output).FreeClosed := by
  simp -implicitDefEqProofs [caseValue,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,ConstructionTowerInitial.value_freeClosed,Project.Formula.isSuccessor,ConstructionSaturationSuccessor.value_freeClosed,ConstructionTowerHistoryLimit.value_freeClosed]

theorem caseValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu J S output : Fin m) :
    Project.Formula.satisfies env (caseValue w Q R top D mul e mark H C zero one K mu J S output) ↔ Case hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound J) (env.bound S) (env.bound output) := by
  simp only [caseValue,Case,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionTowerInitial.value_semantics hM,Project.Formula.satisfies_isSuccessor_iff,ConstructionSaturationSuccessor.value_semantics hM,ConstructionTowerHistoryLimit.value_semantics hM]
  rfl


end PPAC.Migration.ConstructionSaturationIterationCases
