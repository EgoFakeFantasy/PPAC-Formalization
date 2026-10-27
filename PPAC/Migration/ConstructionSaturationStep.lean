/- Pinned CompleteRounds.Saturation.step:535 / succIso / map_succ.
Turn the accepted COMPLETE round into the actual definable unique successor
for the outer ordinal recursion. Reuse the existing bounded-initial-segment
L minimum and the existing nine-field tuple, with all source requests.
No new choice/codec/recursor backend and no host WellFounded premise. -/
import PPAC.Migration.ConstructionCompleteRound

namespace PPAC.Migration.ConstructionSaturationStep
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRoundFields (ObjectFields MapFields Profiles)
open ConstructionCompleteRound (ProbeFamilies MergerFamilies)
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Candidate (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu output : M.Carrier .set) : Prop :=
  ∃ Requests W G unitW markW HW CW O,
    ConstructionRoundSelection.Pack W G unitW markW HW CW O Requests zero output ∧
    ConstructionRequestCarrier.Carrier w D mul e zero one Requests ∧
    ObjectFields hM w Q R top W G unitW markW HW CW ∧
    MapFields hM w Q D W mul G e unitW mark markW H C HW CW O ∧
    Profiles w D W mul G O ∧ Small W mu ∧
    ProbeFamilies w K W G markW O zero Requests ∧ MergerFamilies W G O one Requests ∧
    ConstructionCompleteRound.Built hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O

def Picked (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu output : M.Carrier .set) : Prop :=
  (Candidate hM w Q R top D mul e mark H C zero one K mu output ∧
    ∀ other, Candidate hM w Q R top D mul e mark H C zero one K mu other →
      ¬ InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M) other output) ∨
  (¬ (∃ other, Candidate hM w Q R top D mul e mark H C zero one K mu other)) ∧ output = zero

theorem candidate_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hCoordinates : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hTop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : Small D mu) (hKSmall : Small K mu) :
    ∃ output, Candidate hM w Q R top D mul e mark H C zero one K mu output := by
  obtain ⟨Requests,W,G,unitW,markW,HW,CW,O,hCarrier,hObject,hMap,hProfile,hSize,hProbes,hMergers,hBuilt⟩ :=
    ConstructionCompleteRound.exists_from_parent_built hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall
  obtain ⟨output,hPack⟩ := ConstructionRoundSelection.pack_exists hM W G unitW markW HW CW O Requests zero
  exact ⟨output,Requests,W,G,unitW,markW,HW,CW,O,hPack,hCarrier,hObject,hMap,hProfile,hSize,hProbes,hMergers,hBuilt⟩

theorem picked_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top D mul e mark H C zero one K mu x y : M.Carrier .set}
    (hx : Picked hM w Q R top D mul e mark H C zero one K mu x)
    (hy : Picked hM w Q R top D mul e mark H C zero one K mu y) : x = y := by
  rcases hx with ⟨hx,hxmin⟩ | ⟨hnx,rfl⟩
  · rcases hy with ⟨hy,hymin⟩ | ⟨hny,_⟩
    · rcases hOrder.2.2.1 x y with he | hxy | hyx
      · exact he
      · exact False.elim (hymin x hx hxy)
      · exact False.elim (hxmin y hy hyx)
    · exact False.elim (hny ⟨x,hx⟩)
  · rcases hy with ⟨hy,_⟩ | ⟨_,rfl⟩
    · exact False.elim (hnx ⟨y,hy⟩)
    · rfl

theorem picked_is_candidate (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu output : M.Carrier .set}
    (hn : ∃ other, Candidate hM w Q R top D mul e mark H C zero one K mu other)
    (hp : Picked hM w Q R top D mul e mark H C zero one K mu output) :
    Candidate hM w Q R top D mul e mark H C zero one K mu output := by
  rcases hp with ⟨hc,_⟩ | ⟨hn',_⟩
  · exact hc
  · exact False.elim (hn' hn)


def candidate {m : Nat} (w Q R top D mul e mark H C zero one K mu output : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ConstructionRoundSelection.pack (6 : Fin (m+8)) (5 : Fin (m+8)) (4 : Fin (m+8)) (3 : Fin (m+8)) (2 : Fin
  (m+8)) (1 : Fin (m+8)) (0 : Fin (m+8)) (7 : Fin (m+8)) zero.succ.succ.succ.succ.succ.succ.succ.succ
  output.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (ConstructionRequestCarrier.carrier
  w.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)))
  (.conj (ConstructionRoundStepSyntax.objectFields w.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8)) (5 : Fin (m+8)) (4 : Fin (m+8)) (3 : Fin
  (m+8)) (2 : Fin (m+8)) (1 : Fin (m+8))) (.conj (ConstructionRoundStepSyntax.mapFields
  w.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8)) mul.succ.succ.succ.succ.succ.succ.succ.succ (5 :
  Fin (m+8)) e.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin (m+8))
  mark.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+8)) H.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+8)) (1 : Fin (m+8)) (0 : Fin (m+8))) (.conj
  (ConstructionRoundStepSyntax.profiles w.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8)) mul.succ.succ.succ.succ.succ.succ.succ.succ (5 :
  Fin (m+8)) (0 : Fin (m+8))) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small (6 : Fin (m+8))
  mu.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ConstructionCompleteRound.probeFamilies
  w.succ.succ.succ.succ.succ.succ.succ.succ K.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8)) (5 :
  Fin (m+8)) (3 : Fin (m+8)) (0 : Fin (m+8)) zero.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)))
  (.conj (ConstructionCompleteRound.mergerFamilies (6 : Fin (m+8)) (5 : Fin (m+8)) (0 : Fin (m+8))
  one.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8))) (ConstructionCompleteRound.built
  w.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ mark.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ mu.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (6 :
  Fin (m+8)) (5 : Fin (m+8)) (4 : Fin (m+8)) (3 : Fin (m+8)) (2 : Fin (m+8)) (1 : Fin (m+8)) (0 : Fin
  (m+8)))))))))))))))))))

theorem candidate_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu output : Fin m) :
    (candidate w Q R top D mul e mark H C zero one K mu output).FreeClosed := by
  simp -implicitDefEqProofs [candidate,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionRequestCarrier.carrier_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,ConstructionRoundStepSyntax.profiles_freeClosed,ConstructionCompleteRound.probeFamilies_freeClosed,ConstructionCompleteRound.mergerFamilies_freeClosed,ConstructionCompleteRound.built_freeClosed]

theorem candidate_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu output : Fin m) :
    Project.Formula.satisfies env (candidate w Q R top D mul e mark H C zero one K mu output) ↔ Candidate hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound output) := by
  simp only [candidate,Candidate,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,

    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionRoundSelection.pack_semantics hM,ConstructionRequestCarrier.carrier_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionRoundStepSyntax.profiles_semantics hM,ForcingSupportSize.small_semantics (M := M),ConstructionCompleteRound.probeFamilies_semantics hM,ConstructionCompleteRound.mergerFamilies_semantics hM,ConstructionCompleteRound.built_semantics hM]
  rfl


def picked {m : Nat} (w Q R top D mul e mark H C zero one K mu output : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (candidate w Q R top D mul e mark H C zero one K mu output) (.forallE (.imp (candidate w.succ
  Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ zero.succ one.succ K.succ mu.succ (0
  : Fin (m+1))) (.neg (InnerModel.js_less_m (.bound (0 : Fin (m+1))) (.bound output.succ)))))) (.conj (.neg
  (.existsE (candidate w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ
  zero.succ one.succ K.succ mu.succ (0 : Fin (m+1))))) (Project.Formula.extensionalEq (.bound output)
  (.bound zero))))

theorem picked_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu output : Fin m) :
    (picked w Q R top D mul e mark H C zero one K mu output).FreeClosed := by
  simp -implicitDefEqProofs [picked,Definitional.Formula.FreeClosed,candidate_freeClosed,InnerModel.js_less_m_freeClosed,Project.Formula.extensionalEq]

theorem picked_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu output : Fin m) :
    Project.Formula.satisfies env (picked w Q R top D mul e mark H C zero one K mu output) ↔ Picked hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound output) := by
  simp only [picked,Picked,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_disj_iff,candidate_semantics hM,InnerModel.js_less_formula_l (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


theorem picked_total (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (w Q R top D mul e mark H C zero one K mu : M.Carrier .set) :
    ∃ output, Picked hM w Q R top D mul e mark H C zero one K mu output ∧
      ∀ other, Picked hM w Q R top D mul e mark H C zero one K mu other → other = output := by
  classical
  let schema : Project.UnarySchema 14 := {
    body := candidate (0 : Fin 14).succ (1 : Fin 14).succ (2 : Fin 14).succ (3 : Fin 14).succ (4 : Fin 14).succ (5 : Fin 14).succ (6 : Fin 14).succ (7 : Fin 14).succ (8 : Fin 14).succ (9 : Fin 14).succ (10 : Fin 14).succ (11 : Fin 14).succ (12 : Fin 14).succ (13 : Fin 14).succ (0 : Fin 15)
    freeClosed := candidate_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 14 := {
    bound := fun i => match i.val with
      | 0 => w
      | 1 => Q
      | 2 => R
      | 3 => top
      | 4 => D
      | 5 => mul
      | 6 => e
      | 7 => mark
      | 8 => H
      | 9 => C
      | 10 => zero
      | 11 => one
      | 12 => K
      | _ => mu
    free := fun _ => zero }
  have he (output) : schema.denote env output ↔ Candidate hM w Q R top D mul e mark H C zero one K mu output :=
    candidate_semantics hM (env.push output) (0 : Fin 14).succ (1 : Fin 14).succ (2 : Fin 14).succ (3 : Fin 14).succ (4 : Fin 14).succ (5 : Fin 14).succ (6 : Fin 14).succ (7 : Fin 14).succ (8 : Fin 14).succ (9 : Fin 14).succ (10 : Fin 14).succ (11 : Fin 14).succ (12 : Fin 14).succ (13 : Fin 14).succ (0 : Fin 15)
  by_cases hn : ∃ output, Candidate hM w Q R top D mul e mark H C zero one K mu output
  · obtain ⟨output,hc,hmin⟩ := ConstructionRoundSelection.least_denote hM hOrder schema env
      (by obtain ⟨output,hc⟩ := hn; exact ⟨output,(he output).mpr hc⟩)
    have hp : Picked hM w Q R top D mul e mark H C zero one K mu output :=
      Or.inl ⟨(he output).mp hc,fun other hOther => hmin other ((he other).mpr hOther)⟩
    exact ⟨output,hp,fun other hOther => picked_unique hM hOrder hOther hp⟩
  · have hp : Picked hM w Q R top D mul e mark H C zero one K mu zero := Or.inr ⟨hn,rfl⟩
    exact ⟨zero,hp,fun other hOther => picked_unique hM hOrder hOther hp⟩

theorem exists_step (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hCoordinates : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hTop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : Small D mu) (hKSmall : Small K mu) :
    ∃ output, Picked hM w Q R top D mul e mark H C zero one K mu output ∧ Candidate hM w Q R top D mul e mark H C zero one K mu output ∧
      ∀ other, Picked hM w Q R top D mul e mark H C zero one K mu other → other = output := by

  have hn := candidate_exists hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall
  obtain ⟨output,hPicked,hUnique⟩ := picked_total hM hOrder w Q R top D mul e mark H C zero one K mu
  exact ⟨output,hPicked,picked_is_candidate hM hn hPicked,hUnique⟩

def stepSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 15 (.imp (Project.Formula.isOmega (.bound (0 : Fin 15))) (.imp
    (ConstructionFractionOrder.carrier (0 : Fin 15) (1 : Fin 15)) (.imp (ConstructionRealCuts.cutCarrier (0
    : Fin 15) (1 : Fin 15) (2 : Fin 15)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 15) (12 : Fin
    15) (11 : Fin 15) (11 : Fin 15)) (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 15))) (.imp
    (ConstructionRealCuts.principal (0 : Fin 15) (1 : Fin 15) (12 : Fin 15) (3 : Fin 15)) (.imp
    (ConstructionRoundStepSyntax.objectFields (0 : Fin 15) (1 : Fin 15) (2 : Fin 15) (3 : Fin 15) (4 : Fin
    15) (5 : Fin 15) (6 : Fin 15) (7 : Fin 15) (8 : Fin 15) (9 : Fin 15)) (.imp (Project.Formula.isEmpty
    (.bound (10 : Fin 15))) (.imp (.mem (.bound (10 : Fin 15)) (.bound (0 : Fin 15))) (.imp (.existsE (.mem
    (.bound (0 : Fin 16)) (.bound (13 : Fin 15).succ))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 15)) (.bound (14 : Fin 15))) (.imp
    (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound (14 : Fin 15))
    (.bound (14 : Fin 15)) (.bound (0 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small
    (4 : Fin 15) (14 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (13 : Fin 15) (14
    : Fin 15))) (.existsE (.conj (picked (0 : Fin 15).succ (1 : Fin 15).succ (2 : Fin 15).succ (3 : Fin
    15).succ (4 : Fin 15).succ (5 : Fin 15).succ (6 : Fin 15).succ (7 : Fin 15).succ (8 : Fin 15).succ (9 :
    Fin 15).succ (10 : Fin 15).succ (11 : Fin 15).succ (13 : Fin 15).succ (14 : Fin 15).succ (0 : Fin 16))
    (.conj (candidate (0 : Fin 15).succ (1 : Fin 15).succ (2 : Fin 15).succ (3 : Fin 15).succ (4 : Fin
    15).succ (5 : Fin 15).succ (6 : Fin 15).succ (7 : Fin 15).succ (8 : Fin 15).succ (9 : Fin 15).succ (10 :
    Fin 15).succ (11 : Fin 15).succ (13 : Fin 15).succ (14 : Fin 15).succ (0 : Fin 16)) (.forallE (.imp
    (picked (0 : Fin 15).succ.succ (1 : Fin 15).succ.succ (2 : Fin 15).succ.succ (3 : Fin 15).succ.succ (4 :
    Fin 15).succ.succ (5 : Fin 15).succ.succ (6 : Fin 15).succ.succ (7 : Fin 15).succ.succ (8 : Fin
    15).succ.succ (9 : Fin 15).succ.succ (10 : Fin 15).succ.succ (11 : Fin 15).succ.succ (13 : Fin
    15).succ.succ (14 : Fin 15).succ.succ (0 : Fin 17)) (Project.Formula.extensionalEq (.bound (0 : Fin 17))
    (.bound (1 : Fin 17)))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      Project.Formula.isOrdinalOne,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,Project.Formula.isEmpty,
      Project.Formula.isInfiniteCardinal,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,
      picked_freeClosed,candidate_freeClosed,Project.Formula.extensionalEq]

theorem step_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence stepSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) stepSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),picked_semantics hM,candidate_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall =>
    exists_step hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall


theorem step_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative stepSentence)) := by
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
  apply ConstructibleGround.relative_models hM stepSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) stepSentence).mp
    (step_models hL (ConstructionRoundSelection.l_order hM) hChoice)



end PPAC.Migration.ConstructionSaturationStep
