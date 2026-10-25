/- Original ForcingNames.evaluate_mapConditions (169-181), with object
formula-indexed condition classes and all parameters retained. The inverse
image is a formula, not an assumed internal set. Arbitrary external generic
filters still require their separate interpretation/amenability bridge. -/
import PPAC.Migration.ForcingClassEvaluation

namespace PPAC.Migration.ForcingEvaluationCovariance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
open ForcingMapConditions (MapRel IsFunction Mapped mapping)
open ForcingClassEvaluation (Predicate Evaluated evaluation)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def preimage {n : Nat} (f : Formula (n+2)) (p : Formula (n+1)) : Formula (n+1) :=
  .ex ((ReplacementPredicates.rel f (fun i => i.castSucc.castSucc)
    (Fin.last n).castSucc (Fin.last (n+1))).conj
      (MinimalPredicates.pred p (fun i => i.castSucc.castSucc) (Fin.last (n+1))))

theorem preimage_semantics {n : Nat} (f : Formula (n+2)) (p : Formula (n+1))
    (params : Fin n → M.Carrier .set) (x : M.Carrier .set) :
    Predicate (preimage f p) params x ↔ ∃ y, MapRel f params x y ∧ Predicate p params y := by
  change Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x params) (preimage f p) ↔ _
  simp only [preimage, Formula.Realize, ForcingMapConditions.rel_semantics (M := M),
    ForcingClassEvaluation.predicate_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def covarianceAt {n m : Nat} (f : Formula (n+2)) (p : Formula (n+1))
    (rho : Fin n → Fin m) (sigma : Fin m) : Formula m :=
  .all (.all ((mapping f (paramsUp (paramsUp rho)) sigma.castSucc.castSucc (Fin.last m).castSucc).imp
    ((evaluation p (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))).imp
      (evaluation (preimage f p) (paramsUp (paramsUp rho)) sigma.castSucc.castSucc (Fin.last (m+1))))))

theorem covarianceAt_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (f : Formula (n+2)) (p : Formula (n+1)) (rho : Fin n → Fin m) (sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (covarianceAt f p rho sigma) ↔
      ∀ mapped output, Mapped f (fun i => v (rho i)) (v sigma) mapped →
        Evaluated p (fun i => v (rho i)) mapped output → Evaluated (preimage f p) (fun i => v (rho i)) (v sigma) output := by
  simp only [covarianceAt, Formula.Realize, ForcingMapConditions.mapping_semantics (M := M),
    ForcingClassEvaluation.evaluation_semantics (M := M), paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem covariance (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f : Formula (n+2)} (p : Formula (n+1)) {params : Fin n → M.Carrier .set} (hf : IsFunction f params)
    {sigma mapped output : M.Carrier .set} (hm : Mapped f params sigma mapped) (hv : Evaluated p params mapped output) :
    Evaluated (preimage f p) params sigma output := by
  let q := covarianceAt f p Fin.castSucc (Fin.last n)
  have hq : ∀ s, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases s params) q ↔
      ∀ t o, Mapped f params s t → Evaluated p params t o → Evaluated (preimage f p) params s o := by
    intro s
    simpa only [q, Fin.lastCases_last, Fin.lastCases_castSucc] using
      (covarianceAt_semantics (Fin.lastCases s params) f p Fin.castSucc (Fin.last n))
  have hAll := ForcingMapLaws.formula_induction hM q params (by
    intro s ih
    apply (hq s).mpr
    intro t o ht ho
    obtain ⟨inverseValue, hi⟩ := ForcingClassEvaluation.exists_evaluation hM (preimage f p) params s
    have heq : o = inverseValue := by
      apply (ModelTransfer.extensionality hM).eq_of_same_members
      intro x
      constructor
      · intro hx
        obtain ⟨tau, condition, he, hp, hValue⟩ := (ForcingClassEvaluation.mem_evaluation hM ho x).mp hx
        obtain ⟨original, c, hOriginal, hMapped, hc⟩ := (ForcingMapConditions.edge_mapping hM hf ht tau condition).mp he
        exact (ForcingClassEvaluation.mem_evaluation hM hi x).mpr
          ⟨original, c, hOriginal, (preimage_semantics f p params c).mpr ⟨condition, hc, hp⟩,
            (hq original).mp (ih original c hOriginal) tau x hMapped hValue⟩
      · intro hx
        obtain ⟨tau, condition, he, hp, hValue⟩ := (ForcingClassEvaluation.mem_evaluation hM hi x).mp hx
        obtain ⟨c, hc, hpc⟩ := (preimage_semantics f p params condition).mp hp
        obtain ⟨mappedChild, hChild⟩ := ForcingMapConditions.exists_mapping hM f params hf tau
        obtain ⟨v, hEval⟩ := ForcingClassEvaluation.exists_evaluation hM p params mappedChild
        have hxv := ForcingClassEvaluation.unique hM hValue ((hq tau).mp (ih tau condition he) mappedChild v hChild hEval)
        exact (ForcingClassEvaluation.mem_evaluation hM ho x).mpr
          ⟨mappedChild, c, (ForcingMapConditions.edge_mapping hM hf ht mappedChild c).mpr
            ⟨tau, condition, he, hChild, hc⟩, hpc, hxv.symm ▸ hEval⟩
    exact heq.symm ▸ hi)
  exact (hq sigma).mp (hAll sigma) mapped output hm hv

/-- Both evaluations are the same value, using existing totality and uniqueness. -/
theorem covariance_iff (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f : Formula (n+2)} (p : Formula (n+1)) {params : Fin n → M.Carrier .set} (hf : IsFunction f params)
    {sigma mapped output : M.Carrier .set} (hm : Mapped f params sigma mapped) :
    Evaluated p params mapped output ↔ Evaluated (preimage f p) params sigma output := by
  constructor
  · exact covariance hM p hf hm
  · intro hi
    obtain ⟨value, hv⟩ := ForcingClassEvaluation.exists_evaluation hM p params mapped
    have heq := ForcingClassEvaluation.unique hM hi (covariance hM p hf hm hv)
    exact heq.symm ▸ hv

def covarianceSentence {n : Nat} (f : Formula (n+2)) (p : Formula (n+1)) : Source.Sentence :=
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  let sigma := (Fin.last n).castSucc.castSucc
  let mapped := (Fin.last (n+1)).castSucc
  let value := Fin.last (n+2)
  ((ForcingMapConditions.function f rho).imp ((mapping f rho sigma mapped).imp
    ((evaluation p rho mapped value).iff (evaluation (preimage f p) rho sigma value)))).close

theorem covariance_models {n : Nat} (f : Formula (n+2)) (p : Formula (n+1))
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (covarianceSentence f p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hFunction hMapped
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  let sigma := (Fin.last n).castSucc.castSucc
  let mapped := (Fin.last (n+1)).castSucc
  let value := Fin.last (n+2)
  have he := covariance_iff hM p ((ForcingMapConditions.function_semantics v f rho).mp hFunction)
    ((ForcingMapConditions.mapping_semantics v f rho sigma mapped).mp hMapped) (output := v value)
  have hl := ForcingClassEvaluation.evaluation_semantics v p rho mapped value
  have hr := ForcingClassEvaluation.evaluation_semantics v (preimage f p) rho sigma value
  exact ⟨fun h => hr.mpr (he.mp (hl.mp h)), fun h => hl.mpr (he.mpr (hr.mp h))⟩

theorem covariance_kernel_certificate {n : Nat} (f : Formula (n+2)) (p : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (covarianceSentence f p)) :=
  ModelTransfer.derives (fun _ hM => covariance_models f p hM)

end PPAC.Migration.ForcingEvaluationCovariance
