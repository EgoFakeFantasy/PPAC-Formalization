/- Pinned OpenAI SupportFilter.inf_mem. Reuse the newer native finite-union
bound and the already migrated fixing subgroups, without object Choice. -/
import PPAC.Migration.ExistingCardinalBounds
import PPAC.Migration.ForcingSupportFilter

namespace PPAC.Migration.ForcingSupportIntersection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingLabelPermutations (Carrier carrier Fixing fixing)
open ForcingConjugationGraph (Subgroup subgroup)
open ForcingSupportSize (Small small)
open ForcingSupportFilter (Supported Filter filter)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Intersection (H K L : M.Carrier .set) : Prop :=
  ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x H ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem x K ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x L

def intersection {m : Nat} (H K L : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) H.castSucc).iff
    ((Formula.mem (Fin.last m) K.castSucc).conj (.mem (Fin.last m) L.castSucc)))

theorem intersection_semantics {m : Nat} (env : Fin m → M.Carrier .set) (H K L : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (intersection H K L) ↔
      Intersection (env H) (env K) (env L) := by
  simp only [intersection,Intersection,Source.Formula.iff,Formula.Realize,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x => ⟨(h x).1,(h x).2⟩,fun h x => ⟨(h x).mp,(h x).mpr⟩⟩

theorem subgroup_intersection (hM : FirstOrder.Theory.Models M nativeZF) {I G K L H : M.Carrier .set}
    (hG : Carrier I G) (hK : Subgroup I G K) (hL : Subgroup I G L)
    (hH : Intersection H K L) : Subgroup I G H := by
  refine ⟨fun x hx => hK.1 x ((hH x).mp hx).1,?_,?_,?_⟩
  · obtain ⟨e,he,heId⟩ := hK.2.1
    obtain ⟨f,hf,hfId⟩ := hL.2.1
    have hef := ForcingConjugationGraph.endomap_ext hM ((hG e).mp (hK.1 e he)).1
      ((hG f).mp (hL.1 f hf)).1 (fun x y => (heId x y).trans (hfId x y).symm)
    exact ⟨e,(hH e).mpr ⟨he,hef ▸ hf⟩,heId⟩
  · intro r hr
    obtain ⟨i,hi,hri⟩ := hK.2.2.1 r ((hH r).mp hr).1
    obtain ⟨j,hj,hrj⟩ := hL.2.2.1 r ((hH r).mp hr).2
    have hij := ForcingConjugationGraph.endomap_ext hM ((hG i).mp (hK.1 i hi)).1
      ((hG j).mp (hL.1 j hj)).1 (fun x y => (hri y x).symm.trans (hrj y x))
    exact ⟨i,(hH i).mpr ⟨hi,hij ▸ hj⟩,hri⟩
  · intro r s hr hs
    obtain ⟨t,ht,hrt⟩ := hK.2.2.2 r s ((hH r).mp hr).1 ((hH s).mp hs).1
    obtain ⟨v,hv,hrv⟩ := hL.2.2.2 r s ((hH r).mp hr).2 ((hH s).mp hs).2
    have htv := ForcingConjugationGraph.endomap_ext hM ((hG t).mp (hK.1 t ht)).1
      ((hG v).mp (hL.1 v hv)).1 (fun x y => (hrt x y).trans (hrv x y).symm)
    exact ⟨t,(hH t).mpr ⟨ht,htv ▸ hv⟩,hrt⟩

/-- The donor finite-union theorem discharges the actual source cardinal bound. -/
theorem small_union (hM : FirstOrder.Theory.Models M nativeZF) {w mu J K U : M.Carrier .set}
    (hw : (Definitional.Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Definitional.Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hJ : Small J mu) (hK : Small K mu)
    (hU : (Definitional.Project.FirstOrderSemantics.reduct M).IsUnionOfTwo U J K) : Small U mu :=
  (ForcingSupportSize.native_small hM U mu).mpr (ExistingCardinalBounds.infinite_union_two_l
    (KuratowskiZF.interpretation hM) (ModelTransfer.project_models_iff.mp hM) hw hmu
    ((ForcingSupportSize.native_small hM J mu).mp hJ) ((ForcingSupportSize.native_small hM K mu).mp hK) hU)

theorem intersection_supported (hM : FirstOrder.Theory.Models M nativeZF) {I G w mu K L H : M.Carrier .set}
    (hw : (Definitional.Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Definitional.Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hG : Carrier I G) (hK : Supported I G mu K) (hL : Supported I G mu L)
    (hH : Intersection H K L) : Supported I G mu H := by
  obtain ⟨hKS,J,S,hJI,hJ,hS,hSK⟩ := hK
  obtain ⟨hLS,J',S',hJ'I,hJ',hS',hSL⟩ := hL
  obtain ⟨U,hU⟩ := SetTheory.KP.exists_unionOfTwo (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) J J'
  obtain ⟨T,hT⟩ := ForcingLabelPermutations.exists_fixing hM G U
  refine ⟨subgroup_intersection hM hG hKS hLS hH,U,T,?_,small_union hM hw hmu hJ hJ' hU,hT,?_⟩
  · intro x hx
    exact ((hU x).mp hx).elim (hJI x) (hJ'I x)
  · intro r hr
    obtain ⟨hrG,hrU⟩ := (hT r).mp hr
    apply (hH r).mpr
    exact ⟨hSK r ((hS r).mpr ⟨hrG,fun x hx => hrU x ((hU x).mpr (Or.inl hx))⟩),
      hSL r ((hS' r).mpr ⟨hrG,fun x hx => hrU x ((hU x).mpr (Or.inr hx))⟩)⟩

theorem intersection_mem (hM : FirstOrder.Theory.Models M nativeZF) {I G w mu F K L H : M.Carrier .set}
    (hw : (Definitional.Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Definitional.Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hG : Carrier I G) (hF : Filter I G mu F)
    (hK : (Definitional.Project.FirstOrderSemantics.reduct M).mem K F)
    (hL : (Definitional.Project.FirstOrderSemantics.reduct M).mem L F) (hH : Intersection H K L) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem H F :=
  (hF H).mpr (intersection_supported hM hw hmu hG ((hF K).mp hK) ((hF L).mp hL) hH)

end PPAC.Migration.ForcingSupportIntersection
