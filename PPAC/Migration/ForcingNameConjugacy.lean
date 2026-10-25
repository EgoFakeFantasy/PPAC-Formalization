/- Graph-coded form of stabilizer_smul_eq_stabilizer_map_conj, used by
pinned ForcingNames.Name.HS.smul. Existing condition/name action laws supply
composition and inverses; the fixed-name equivalence is proved, not assumed. -/
import PPAC.Migration.ForcingStabilizer

namespace PPAC.Migration.ForcingNameConjugacy
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2 args3)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (Mapped)
open ForcingStabilizer (Action action)
open ForcingConditionGraphs (Endomap Permutation InverseGraph CompositionGraph)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Changing parameter lists does not change the already constructed name action. -/
theorem action_iff {n : Nat} (params : Fin n → M.Carrier .set) (P r : Fin n) (sigma out : M.Carrier .set) :
    Mapped (ForcingConditionAction.actFormula P r) params sigma out ↔ Action (params P) (params r) sigma out :=
  ForcingMapLaws.mapping_congr (fun x y =>
    (ForcingConditionAction.relation_semantics params P r x y).trans
      (ForcingConditionAction.relation_semantics (args2 (params P) (params r)) (0 : Fin 2) 1 x y).symm) sigma out

theorem exists_action (hM : FirstOrder.Theory.Models M nativeZF) {P r : M.Carrier .set}
    (hr : Endomap P r) (sigma : M.Carrier .set) : ∃ out, Action P r sigma out :=
  ForcingMapConditions.exists_mapping hM (ForcingConditionAction.actFormula (0 : Fin 2) 1) (args2 P r)
    (ForcingConditionAction.act_function (args2 P r) (0 : Fin 2) 1 hr) sigma

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {P r sigma a b : M.Carrier .set}
    (hr : Endomap P r) (ha : Action P r sigma a) (hb : Action P r sigma b) : a = b :=
  ForcingMapConditions.unique hM (ForcingConditionAction.act_function (args2 P r) (0 : Fin 2) 1 hr) ha hb

theorem name_preservation (hM : FirstOrder.Theory.Models M nativeZF) {P r sigma out : M.Carrier .set}
    (hr : Endomap P r) (hn : ForcingNames.IsName P sigma) (hm : Action P r sigma out) : ForcingNames.IsName P out :=
  ForcingConditionAction.name_preservation hM (args2 P r) (0 : Fin 2) 1 hr hn hm

theorem composition (hM : FirstOrder.Theory.Models M nativeZF) {P r s t sigma mid out : M.Carrier .set}
    (hr : Endomap P r) (hs : Endomap P s) (hc : CompositionGraph P r s t)
    (hm : Action P s sigma mid) (ho : Action P r mid out) : Action P t sigma out := by
  let v : Fin 4 → M.Carrier .set := Fin.cases P (Fin.cases r (args2 s t))
  exact (action_iff v 0 3 sigma out).mp
    (ForcingConditionAction.name_composition hM v 0 1 2 3 hr hs hc
      ((action_iff v 0 2 sigma mid).mpr hm) ((action_iff v 0 1 mid out).mpr ho))

theorem inverse (hM : FirstOrder.Theory.Models M nativeZF) {P r i sigma mid out : M.Carrier .set}
    (hr : Endomap P r) (hi : Endomap P i) (hri : InverseGraph r i)
    (hn : ForcingNames.IsName P sigma) (hm : Action P r sigma mid) (ho : Action P i mid out) : out = sigma := by
  let v := args3 P r i
  exact ForcingConditionAction.name_inverse hM v 0 1 2 hr hi hri hn
    ((action_iff v 0 1 sigma mid).mpr hm) ((action_iff v 0 2 mid out).mpr ho)

theorem inverse_action (hM : FirstOrder.Theory.Models M nativeZF) {P r i sigma out : M.Carrier .set}
    (hr : Endomap P r) (hi : Endomap P i) (hri : InverseGraph r i)
    (hn : ForcingNames.IsName P sigma) (hm : Action P r sigma out) : Action P i out sigma := by
  obtain ⟨back,hback⟩ := exists_action hM hi out
  exact inverse hM hr hi hri hn hm hback ▸ hback

theorem injective (hM : FirstOrder.Theory.Models M nativeZF) {P r sigma tau out : M.Carrier .set}
    (hr : Permutation P r) (hsigma : ForcingNames.IsName P sigma) (htau : ForcingNames.IsName P tau)
    (ha : Action P r sigma out) (hb : Action P r tau out) : sigma = tau := by
  obtain ⟨i,hi,hri⟩ := ForcingConditionGraphs.exists_inverse hM hr
  exact unique hM hi.1 (inverse_action hM hr.1 hi.1 hri hsigma ha) (inverse_action hM hr.1 hi.1 hri htau hb)

/-- The graph t is exactly r o s o inverse(r), retaining the intermediate graph. -/
def conjugate {m : Nat} (P r i s t : Fin m) : Formula m :=
  .ex ((ForcingConditionGraphs.endomap P.castSucc (Fin.last m)).conj
    ((ForcingConditionGraphs.compositionGraph P.castSucc s.castSucc i.castSucc (Fin.last m)).conj
      (ForcingConditionGraphs.compositionGraph P.castSucc r.castSucc (Fin.last m) t.castSucc)))

def Conjugate (P r i s t : M.Carrier .set) : Prop :=
  ∃ mid, Endomap P mid ∧ CompositionGraph P s i mid ∧ CompositionGraph P r mid t

theorem conjugate_semantics {m : Nat} (env : Fin m → M.Carrier .set) (P r i s t : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (conjugate P r i s t) ↔
      Conjugate (env P) (env r) (env i) (env s) (env t) := by
  simp only [conjugate,Conjugate,Formula.Realize,ForcingConditionGraphs.endomap_semantics (M := M),
    ForcingConditionGraphs.compositionGraph_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem exists_conjugate (hM : FirstOrder.Theory.Models M nativeZF) {P r i s : M.Carrier .set}
    (hr : Permutation P r) (hi : Permutation P i) (hs : Permutation P s) :
    ∃ t, Permutation P t ∧ Conjugate P r i s t := by
  obtain ⟨mid,hm,hmi⟩ := ForcingConditionGraphs.exists_composition hM hs hi
  obtain ⟨t,ht,hrt⟩ := ForcingConditionGraphs.exists_composition hM hr hm
  exact ⟨t,ht,mid,hm.1,hmi,hrt⟩

/-- The stabilizer conjugacy identity from the actual map action, in both directions. -/
theorem fixed_conjugacy (hM : FirstOrder.Theory.Models M nativeZF) {P r i s t sigma out : M.Carrier .set}
    (hr : Permutation P r) (hi : Endomap P i) (hs : Endomap P s) (ht : Endomap P t)
    (hri : InverseGraph r i) (hc : Conjugate P r i s t) (hn : ForcingNames.IsName P sigma)
    (ha : Action P r sigma out) : Action P s sigma sigma ↔ Action P t out out := by
  obtain ⟨mid,hm,hsi,hrm⟩ := hc
  have hback := inverse_action hM hr.1 hi hri hn ha
  constructor
  · intro hf
    exact composition hM hr.1 hm hrm (composition hM hs hi hsi hback hf) ha
  · intro hf
    obtain ⟨x,hx⟩ := exists_action hM hs sigma
    obtain ⟨y,hy⟩ := exists_action hM hr.1 x
    have hty := composition hM hr.1 hm hrm (composition hM hs hi hsi hback hx) hy
    have heq := unique hM ht hty hf
    have hxsigma := injective hM hr (name_preservation hM hs hn hx) hn (heq ▸ hy) ha
    exact hxsigma ▸ hx

def sentence : Source.Sentence :=
  ((ForcingConditionGraphs.permutation (0 : Fin 7) 1).imp ((ForcingConditionGraphs.endomap 0 2).imp
    ((ForcingConditionGraphs.endomap 0 3).imp ((ForcingConditionGraphs.endomap 0 4).imp
      ((ForcingConditionGraphs.inverseGraph 1 2).imp ((conjugate 0 1 2 3 4).imp
        ((ForcingNames.isName 0 5).imp ((action 0 1 5 6).imp
          ((action 0 3 5 5).iff (action 0 4 6 6)))))))))).close

theorem models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence sentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hr hi hs ht hri hc hn ha
  have h := fixed_conjugacy hM ((ForcingConditionGraphs.permutation_semantics (M := M) env 0 1).mp hr)
    ((ForcingConditionGraphs.endomap_semantics (M := M) env 0 2).mp hi)
    ((ForcingConditionGraphs.endomap_semantics (M := M) env 0 3).mp hs)
    ((ForcingConditionGraphs.endomap_semantics (M := M) env 0 4).mp ht)
    ((ForcingConditionGraphs.inverseGraph_semantics (M := M) env 1 2).mp hri)
    ((conjugate_semantics (M := M) env 0 1 2 3 4).mp hc)
    ((ForcingNames.isName_semantics (M := M) env 0 5).mp hn)
    ((ForcingStabilizer.action_semantics (M := M) env 0 1 5 6).mp ha)
  have hl := ForcingStabilizer.action_semantics (M := M) env 0 3 5 5
  have hr := ForcingStabilizer.action_semantics (M := M) env 0 4 6 6
  exact ⟨fun hp => hr.mpr (h.mp (hl.mp hp)),fun hp => hl.mpr (h.mpr (hr.mp hp))⟩

theorem kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ModelTransfer.derives (fun _ hM => models hM)

end PPAC.Migration.ForcingNameConjugacy
