/- Pinned ForcingNames.lean:203-237 and Name.smul_check:474-478.
Each induction follows the original source proof, now through the existing
native formula-indexed membership induction and the exact check-name equation. -/
import PPAC.Migration.ForcingCheckName

namespace PPAC.Migration.ForcingCheckNameLaws
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
open ForcingCheckName (Checked checkName)
open ForcingMapConditions (Mapped MapRel IsFunction mapping)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def nameAt {m : Nat} (P t x : Fin m) : Formula m :=
  .all ((checkName t.castSucc x.castSucc (Fin.last m)).imp (ForcingNames.isName P.castSucc (Fin.last m)))

theorem nameAt_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P t x : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (nameAt P t x) ↔
      ∀ name, Checked (v t) (v x) name → ForcingNames.IsName (v P) name := by
  simp only [nameAt, Formula.Realize, ForcingCheckName.checkName_semantics (M := M),
    ForcingNames.isName_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem isName (hM : FirstOrder.Theory.Models M nativeZF) {P t : M.Carrier .set}
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P) :
    ∀ x name, Checked t x name → ForcingNames.IsName P name := by
  let params : Fin 2 → M.Carrier .set := Fin.cases P (fun _ => t)
  let p := nameAt (0 : Fin 3) 1 2
  have hp : ∀ x, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x params) p ↔
      ∀ name, Checked t x name → ForcingNames.IsName P name := by
    intro x
    exact nameAt_semantics (M := M) (Fin.lastCases x params) 0 1 2
  have all := ForcingCheckName.formula_induction hM p params (by
    intro x ih
    apply (hp x).mpr
    intro name hn
    apply ForcingNames.intro_name hM P name
    intro z hz
    obtain ⟨y, child, hy, hc, hCode⟩ := (ForcingCheckName.mem_checkName hM hn z).mp hz
    exact ⟨child, t, hCode, ht, (hp y).mp (ih y hy) child hc⟩)
  intro x
  exact (hp x).mp (all x)

def evaluationAt {n m : Nat} (p : Formula (n+1)) (rho : Fin n → Fin m) (t x : Fin m) : Formula m :=
  .all ((checkName t.castSucc x.castSucc (Fin.last m)).imp
    (ForcingClassEvaluation.evaluation p (paramsUp rho) (Fin.last m) x.castSucc))

theorem evaluationAt_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (p : Formula (n+1))
    (rho : Fin n → Fin m) (t x : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (evaluationAt p rho t x) ↔
      ∀ name, Checked (v t) (v x) name → ForcingClassEvaluation.Evaluated p (fun i => v (rho i)) name (v x) := by
  simp only [evaluationAt, Formula.Realize, ForcingCheckName.checkName_semantics (M := M),
    ForcingClassEvaluation.evaluation_semantics (M := M), paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem evaluate_checked (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+1)) (params : Fin n → M.Carrier .set) (t : M.Carrier .set)
    (ht : ForcingClassEvaluation.Predicate p params t) :
    ∀ x name, Checked t x name → ForcingClassEvaluation.Evaluated p params name x := by
  let inputs : Fin (n+1) → M.Carrier .set := Fin.lastCases t params
  let q := evaluationAt p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))
  have hq : ∀ x, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x inputs) q ↔
      ∀ name, Checked t x name → ForcingClassEvaluation.Evaluated p params name x := by
    intro x
    simpa only [inputs, q, Fin.lastCases_last, Fin.lastCases_castSucc] using
      (evaluationAt_semantics (M := M) (Fin.lastCases x inputs) p (fun i => i.castSucc.castSucc)
        (Fin.last n).castSucc (Fin.last (n+1)))
  have all := ForcingCheckName.formula_induction hM q inputs (by
    intro x ih
    apply (hq x).mpr
    intro name hn
    obtain ⟨value, hv⟩ := ForcingClassEvaluation.exists_evaluation hM p params name
    have heq : value = x := by
      apply (ModelTransfer.extensionality hM).eq_of_same_members
      intro z
      constructor
      · intro hz
        obtain ⟨child, condition, he, _, hEval⟩ := (ForcingClassEvaluation.mem_evaluation hM hv z).mp hz
        obtain ⟨y, hy, hc, _⟩ := (ForcingCheckName.edge_checkName hM hn child condition).mp he
        have hzEq := ForcingClassEvaluation.unique hM hEval ((hq y).mp (ih y hy) child hc)
        exact hzEq.symm ▸ hy
      · intro hz
        obtain ⟨child, hc⟩ := ForcingCheckName.exists_checked hM t z
        exact (ForcingClassEvaluation.mem_evaluation hM hv z).mpr
          ⟨child, t, (ForcingCheckName.edge_checkName hM hn child t).mpr ⟨z, hz, hc, rfl⟩,
            ht, (hq z).mp (ih z hz) child hc⟩
    exact heq ▸ hv)
  intro x
  exact (hq x).mp (all x)

def mappingAt {n m : Nat} (f : Formula (n+2)) (rho : Fin n → Fin m) (t q x : Fin m) : Formula m :=
  .all (.all ((checkName t.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc).imp
    ((mapping f (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))).imp
      (checkName q.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1))))))

theorem mappingAt_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (f : Formula (n+2))
    (rho : Fin n → Fin m) (t q x : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (mappingAt f rho t q x) ↔
      ∀ name output, Checked (v t) (v x) name → Mapped f (fun i => v (rho i)) name output → Checked (v q) (v x) output := by
  simp only [mappingAt, Formula.Realize, ForcingCheckName.checkName_semantics (M := M),
    ForcingMapConditions.mapping_semantics (M := M), paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem map_checked (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (f : Formula (n+2)) (params : Fin n → M.Carrier .set) (hf : IsFunction f params)
    (t q : M.Carrier .set) (ht : MapRel f params t q) :
    ∀ x name output, Checked t x name → Mapped f params name output → Checked q x output := by
  let inputs : Fin (n+2) → M.Carrier .set := Fin.lastCases q (Fin.lastCases t params)
  let p := mappingAt f (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))
  have hp : ∀ x, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x inputs) p ↔
      ∀ name output, Checked t x name → Mapped f params name output → Checked q x output := by
    intro x
    simpa only [inputs, p, Fin.lastCases_last, Fin.lastCases_castSucc] using
      (mappingAt_semantics (M := M) (Fin.lastCases x inputs) f (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2)))
  have all := ForcingCheckName.formula_induction hM p inputs (by
    intro x ih
    apply (hp x).mpr
    intro name output hn ho
    obtain ⟨target, htarget⟩ := ForcingCheckName.exists_checked hM q x
    have heq : output = target := by
      apply (ModelTransfer.extensionality hM).eq_of_same_members
      intro z
      constructor
      · intro hz
        obtain ⟨child, condition, v, r, he, hv, hr, hCode⟩ := (ForcingMapConditions.mem_mapping hM hf ho z).mp hz
        obtain ⟨y, hy, hc, hCondition⟩ := (ForcingCheckName.edge_checkName hM hn child condition).mp he
        subst condition
        have hrq := ForcingMapConditions.function_unique hf t r q hr ht
        subst r
        exact (ForcingCheckName.mem_checkName hM htarget z).mpr
          ⟨y, v, hy, (hp y).mp (ih y hy) child v hc hv, hCode⟩
      · intro hz
        obtain ⟨y, v, hy, hv, hCode⟩ := (ForcingCheckName.mem_checkName hM htarget z).mp hz
        obtain ⟨child, hc⟩ := ForcingCheckName.exists_checked hM t y
        obtain ⟨w, hw⟩ := ForcingMapConditions.exists_mapping hM f params hf child
        have hwv := ForcingCheckName.unique hM ((hp y).mp (ih y hy) child w hc hw) hv
        exact (ForcingMapConditions.mem_mapping hM hf ho z).mpr
          ⟨child, t, v, q, (ForcingCheckName.edge_checkName hM hn child t).mpr ⟨y, hy, hc, rfl⟩,
            hwv ▸ hw, ht, hCode⟩
    exact heq.symm ▸ htarget)
  intro x
  exact (hp x).mp (all x)

def nameSentence : Source.Sentence :=
  ((Formula.mem (1 : Fin 4) 0).imp ((checkName 1 2 3).imp (ForcingNames.isName 0 3))).close

def evaluationSentence {n : Nat} (p : Formula (n+1)) (t x name : Fin n) : Source.Sentence :=
  ((MinimalPredicates.pred p id t).imp ((checkName t x name).imp (ForcingClassEvaluation.evaluation p id name x))).close

def mappingSentence {n : Nat} (f : Formula (n+2)) (t q x name output : Fin n) : Source.Sentence :=
  ((ForcingMapConditions.function f id).imp ((ReplacementPredicates.rel f id t q).imp
    ((checkName t x name).imp ((mapping f id name output).imp (checkName q x output))))).close

theorem name_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence nameSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v ht hc
  exact (ForcingNames.isName_semantics (M := M) v 0 3).mpr
    (isName hM ht (v 2) (v 3) ((ForcingCheckName.checkName_semantics (M := M) v 1 2 3).mp hc))

theorem evaluation_models {n : Nat} (p : Formula (n+1)) (t x name : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (evaluationSentence p t x name)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v ht hc
  exact (ForcingClassEvaluation.evaluation_semantics (M := M) v p id name x).mpr
    (evaluate_checked hM p v (v t) ((ForcingClassEvaluation.predicate_semantics (M := M) v p id t).mp ht)
      (v x) (v name) ((ForcingCheckName.checkName_semantics (M := M) v t x name).mp hc))

theorem mapping_models {n : Nat} (f : Formula (n+2)) (t q x name output : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (mappingSentence f t q x name output)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hf ht hc ho
  exact (ForcingCheckName.checkName_semantics (M := M) v q x output).mpr
    (map_checked hM f v ((ForcingMapConditions.function_semantics (M := M) v f id).mp hf)
      (v t) (v q) ((ForcingMapConditions.rel_semantics (M := M) v f id t q).mp ht)
      (v x) (v name) (v output) ((ForcingCheckName.checkName_semantics (M := M) v t x name).mp hc)
      ((ForcingMapConditions.mapping_semantics (M := M) v f id name output).mp ho))

theorem name_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence nameSentence) :=
  ModelTransfer.derives (fun _ hM => name_models hM)
theorem evaluation_kernel_certificate {n : Nat} (p : Formula (n+1)) (t x name : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (evaluationSentence p t x name)) :=
  ModelTransfer.derives (fun _ hM => evaluation_models p t x name hM)
theorem mapping_kernel_certificate {n : Nat} (f : Formula (n+2)) (t q x name output : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (mappingSentence f t q x name output)) :=
  ModelTransfer.derives (fun _ hM => mapping_models f t q x name output hM)

/-- Original smul_check: fixed t gives exactly the same checked name. -/
theorem action_fixed (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (params : Fin n → M.Carrier .set) (P r : Fin n)
    (hr : ForcingConditionGraphs.Endomap (params P) (params r))
    {t x name output : M.Carrier .set} (ht : ForcingConditionAction.Act (params P) (params r) t t)
    (hn : Checked t x name) (ho : Mapped (ForcingConditionAction.actFormula P r) params name output) : output = name :=
  ForcingCheckName.unique hM
    (map_checked hM (ForcingConditionAction.actFormula P r) params
      (ForcingConditionAction.act_function params P r hr) t t
      ((ForcingConditionAction.relation_semantics params P r t t).mpr ht) x name output hn ho) hn

def actionSentence {n : Nat} (P r t x name output : Fin n) : Source.Sentence :=
  ((ForcingConditionGraphs.endomap P r).imp ((ForcingConditionAction.act P r t t).imp
    ((checkName t x name).imp ((mapping (ForcingConditionAction.actFormula P r) id name output).imp
      (.equal output name))))).close

theorem action_models {n : Nat} (P r t x name output : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (actionSentence P r t x name output)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hr ht hn ho
  exact action_fixed hM v P r ((ForcingConditionGraphs.endomap_semantics (M := M) v P r).mp hr)
    ((ForcingConditionAction.act_semantics (M := M) v P r t t).mp ht)
    ((ForcingCheckName.checkName_semantics (M := M) v t x name).mp hn)
    ((ForcingMapConditions.mapping_semantics (M := M) v (ForcingConditionAction.actFormula P r) id name output).mp ho)

theorem action_kernel_certificate {n : Nat} (P r t x name output : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (actionSentence P r t x name output)) :=
  ModelTransfer.derives (fun _ hM => action_models P r t x name output hM)

end PPAC.Migration.ForcingCheckNameLaws
