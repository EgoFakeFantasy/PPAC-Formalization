/- Pinned ForcingNames.evaluate with a formula-indexed condition class.
This consumes the accepted Child graph recursion and the original membership
equation. No set containing the condition class is assumed. This schema does
not identify an arbitrary external generic filter with a ground-model class. -/
import PPAC.Migration.ForcingMapLaws

namespace PPAC.Migration.ForcingClassEvaluation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Predicate {n : Nat} (p : Formula (n+1)) (params : Fin n → M.Carrier .set) (x : M.Carrier .set) : Prop :=
  Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x params) p

theorem predicate_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (p : Formula (n+1)) (rho : Fin n → Fin m) (x : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (MinimalPredicates.pred p rho x) ↔
      Predicate p (fun i => v (rho i)) (v x) :=
  ForcingNameInduction.pred_semantics _ v p rho x

def activeValue {n m : Nat} (p : Formula (n+1)) (rho : Fin n → Fin m) (sigma g value : Fin m) : Formula m :=
  .ex (.ex ((Source.SetLanguage.edge sigma.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    ((MinimalPredicates.pred p (paramsUp (paramsUp rho)) (Fin.last (m+1))).conj
      (Source.SetLanguage.edge g.castSucc.castSucc (Fin.last m).castSucc value.castSucc.castSucc))))

def equation {n m : Nat} (p : Formula (n+1)) (rho : Fin n → Fin m) (sigma g value : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) value.castSucc).iff
    (activeValue p (paramsUp rho) sigma.castSucc g.castSucc (Fin.last m)))

def operator {n : Nat} (p : Formula (n+1)) : Formula (n+3) :=
  equation p (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))

def Equation {n : Nat} (p : Formula (n+1)) (params : Fin n → M.Carrier .set)
    (sigma g output : M.Carrier .set) : Prop :=
  ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x output ↔
    ∃ tau condition, PureKuratowski.PairMember M tau condition sigma ∧
      Predicate p params condition ∧ PureKuratowski.PairMember M tau x g

theorem activeValue_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (p : Formula (n+1)) (rho : Fin n → Fin m) (sigma g value : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (activeValue p rho sigma g value) ↔
      ∃ tau condition, PureKuratowski.PairMember M tau condition (v sigma) ∧
        Predicate p (fun i => v (rho i)) condition ∧ PureKuratowski.PairMember M tau (v value) (v g) := by
  simp only [activeValue, Formula.Realize, KuratowskiZF.source_edge, predicate_semantics (M := M),
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem equation_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (p : Formula (n+1)) (rho : Fin n → Fin m) (sigma g output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (equation p rho sigma g output) ↔
      Equation p (fun i => v (rho i)) (v sigma) (v g) (v output) := by
  simp only [equation, Source.Formula.iff, Formula.Realize, activeValue_semantics (M := M),
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, Equation]
  exact forall_congr' (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)

theorem operator_semantics {n : Nat} (p : Formula (n+1)) (params : Fin n → M.Carrier .set)
    (sigma g output : M.Carrier .set) :
    ForcingNameRecursion.Step (operator p) params sigma g output ↔ Equation p params sigma g output := by
  unfold ForcingNameRecursion.Step operator
  simp only [equation_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]

theorem equation_exists (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+1)) (params : Fin n → M.Carrier .set) (sigma g : M.Carrier .set) :
    ∃ output, Equation p params sigma g output := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  obtain ⟨bound, hBound⟩ := ForcingMapConditions.coordinate_bound hM g
  let inputs : Fin (n+2) → M.Carrier .set := Fin.lastCases g (Fin.lastCases sigma params)
  let query := activeValue p (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))
  have hSep := (GodelDefOutput.separation_semantics E query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨output, hOutput⟩ := hSep inputs bound
  have hQuery : ∀ x, Formula.Realize E (Fin.lastCases x inputs) query ↔
      ∃ tau condition, PureKuratowski.PairMember M tau condition sigma ∧
        Predicate p params condition ∧ PureKuratowski.PairMember M tau x g := by
    intro x
    simpa only [inputs, query, Fin.lastCases_last, Fin.lastCases_castSucc] using
      (activeValue_semantics (M := M) (Fin.lastCases x inputs) p (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2)))
  refine ⟨output, fun x => ?_⟩
  constructor
  · intro hx
    exact (hQuery x).mp ((hOutput x).mp hx).2
  · rintro ⟨tau, condition, he, hp, hv⟩
    exact (hOutput x).mpr ⟨(hBound tau x hv).2, (hQuery x).mpr ⟨tau, condition, he, hp, hv⟩⟩

theorem operator_facts (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+1)) (params : Fin n → M.Carrier .set) :
    ForcingNameRecursion.OperatorFacts (operator p) params := by
  constructor
  · intro sigma g
    obtain ⟨output, h⟩ := equation_exists hM p params sigma g
    exact ⟨output, (operator_semantics p params sigma g output).mpr h⟩
  · intro sigma g x y hx hy
    exact (ModelTransfer.extensionality hM).eq_of_same_members x y
      (fun z => ((operator_semantics p params sigma g x).mp hx z).trans
        ((operator_semantics p params sigma g y).mp hy z).symm)
  · intro sigma g h ha output
    have he : ∀ x, (∃ tau condition, PureKuratowski.PairMember M tau condition sigma ∧
        Predicate p params condition ∧ PureKuratowski.PairMember M tau x g) ↔
      (∃ tau condition, PureKuratowski.PairMember M tau condition sigma ∧
        Predicate p params condition ∧ PureKuratowski.PairMember M tau x h) := by
      intro x
      constructor
      · rintro ⟨tau, condition, ht, hp, hv⟩
        exact ⟨tau, condition, ht, hp, (ha tau condition ht x).mp hv⟩
      · rintro ⟨tau, condition, ht, hp, hv⟩
        exact ⟨tau, condition, ht, hp, (ha tau condition ht x).mpr hv⟩
    constructor
    · intro hp
      apply (operator_semantics p params sigma h output).mpr
      intro x
      exact ((operator_semantics p params sigma g output).mp hp x).trans (he x)
    · intro hp
      apply (operator_semantics p params sigma g output).mpr
      intro x
      exact ((operator_semantics p params sigma h output).mp hp x).trans (he x).symm

def evaluation {n m : Nat} (p : Formula (n+1)) (rho : Fin n → Fin m) (sigma output : Fin m) : Formula m :=
  ForcingNameRecursion.value (operator p) rho sigma output

def Evaluated {n : Nat} (p : Formula (n+1)) (params : Fin n → M.Carrier .set) (sigma output : M.Carrier .set) : Prop :=
  ForcingNameRecursion.Value (operator p) params sigma output

theorem evaluation_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (p : Formula (n+1)) (rho : Fin n → Fin m) (sigma output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (evaluation p rho sigma output) ↔
      Evaluated p (fun i => v (rho i)) (v sigma) (v output) :=
  ForcingNameRecursion.value_semantics v (operator p) rho sigma output

theorem exists_evaluation (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+1)) (params : Fin n → M.Carrier .set) (sigma : M.Carrier .set) :
    ∃ output, Evaluated p params sigma output :=
  ForcingNameRecursion.exists_value hM (operator p) params (operator_facts hM p params) sigma

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {p : Formula (n+1)} {params : Fin n → M.Carrier .set} {sigma x y : M.Carrier .set}
    (hx : Evaluated p params sigma x) (hy : Evaluated p params sigma y) : x = y :=
  ForcingNameRecursion.unique hM (operator_facts hM p params) hx hy

theorem mem_evaluation (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {p : Formula (n+1)} {params : Fin n → M.Carrier .set} {sigma output : M.Carrier .set}
    (hs : Evaluated p params sigma output) (x : M.Carrier .set) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem x output ↔
      ∃ tau condition, PureKuratowski.PairMember M tau condition sigma ∧
        Predicate p params condition ∧ Evaluated p params tau x := by
  obtain ⟨g, hg, hv⟩ := hs
  obtain ⟨hc, hp⟩ := hg sigma output hv
  have he := (operator_semantics p params sigma g output).mp hp
  constructor
  · intro hx
    obtain ⟨tau, condition, ht, hCondition, hxg⟩ := (he x).mp hx
    exact ⟨tau, condition, ht, hCondition, g, hg, hxg⟩
  · rintro ⟨tau, condition, ht, hCondition, hx⟩
    obtain ⟨y, hy⟩ := hc tau condition ht
    have heq := unique hM hx ⟨g, hg, hy⟩
    exact (he x).mpr ⟨tau, condition, ht, hCondition, heq.symm ▸ hy⟩

def evaluatedEntry {n m : Nat} (p : Formula (n+1)) (rho : Fin n → Fin m) (sigma x : Fin m) : Formula m :=
  .ex (.ex ((Source.SetLanguage.edge sigma.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    ((MinimalPredicates.pred p (paramsUp (paramsUp rho)) (Fin.last (m+1))).conj
      (evaluation p (paramsUp (paramsUp rho)) (Fin.last m).castSucc x.castSucc.castSucc))))

theorem evaluatedEntry_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (p : Formula (n+1)) (rho : Fin n → Fin m) (sigma x : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (evaluatedEntry p rho sigma x) ↔
      ∃ tau condition, PureKuratowski.PairMember M tau condition (v sigma) ∧
        Predicate p (fun i => v (rho i)) condition ∧ Evaluated p (fun i => v (rho i)) tau (v x) := by
  simp only [evaluatedEntry, Formula.Realize, KuratowskiZF.source_edge, predicate_semantics (M := M),
    evaluation_semantics (M := M), paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def existenceSentence {n : Nat} (p : Formula (n+1)) : Source.Sentence :=
  (Formula.ex (evaluation p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1)))).close

def uniquenessSentence {n : Nat} (p : Formula (n+1)) : Source.Sentence :=
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  ((evaluation p rho (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).imp
    ((evaluation p rho (Fin.last n).castSucc.castSucc (Fin.last (n+2))).imp
      (.equal (Fin.last (n+1)).castSucc (Fin.last (n+2))))).close

def unfoldingSentence {n : Nat} (p : Formula (n+1)) : Source.Sentence :=
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  ((evaluation p rho (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).imp
    ((Formula.mem (Fin.last (n+2)) (Fin.last (n+1)).castSucc).iff
      (evaluatedEntry p rho (Fin.last n).castSucc.castSucc (Fin.last (n+2))))).close

theorem existence_models {n : Nat} (p : Formula (n+1)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (existenceSentence p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  obtain ⟨output, ho⟩ := exists_evaluation hM p (fun i => v i.castSucc) (v (Fin.last n))
  refine ⟨output, ?_⟩
  apply (evaluation_semantics (Fin.lastCases output v) p (fun i => i.castSucc.castSucc)
    (Fin.last n).castSucc (Fin.last (n+1))).mpr
  simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using ho

theorem uniqueness_models {n : Nat} (p : Formula (n+1)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (uniquenessSentence p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hx hy
  exact unique hM ((evaluation_semantics v p _ _ _).mp hx) ((evaluation_semantics v p _ _ _).mp hy)

theorem unfolding_models {n : Nat} (p : Formula (n+1)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (unfoldingSentence p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hs
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  have he := mem_evaluation hM ((evaluation_semantics v p rho
    (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).mp hs) (v (Fin.last (n+2)))
  have hr := evaluatedEntry_semantics v p rho (Fin.last n).castSucc.castSucc (Fin.last (n+2))
  exact ⟨fun hx => hr.mpr (he.mp hx), fun hx => he.mpr (hr.mp hx)⟩

theorem existence_kernel_certificate {n : Nat} (p : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence p)) :=
  ModelTransfer.derives (fun _ hM => existence_models p hM)

theorem uniqueness_kernel_certificate {n : Nat} (p : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence p)) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models p hM)

theorem unfolding_kernel_certificate {n : Nat} (p : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (unfoldingSentence p)) :=
  ModelTransfer.derives (fun _ hM => unfolding_models p hM)

/-- The previously accepted set-G evaluator is the membership instance. -/
def membershipPredicate : Formula 2 := .mem (Fin.last 1) (Fin.last 0).castSucc

theorem membership_predicate (G x : M.Carrier .set) :
    Predicate membershipPredicate (fun _ => G) x ↔ (Definitional.Project.FirstOrderSemantics.reduct M).mem x G := by
  simp only [Predicate, membershipPredicate, Formula.Realize, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem membership_equivalence (G sigma output : M.Carrier .set) :
    Evaluated membershipPredicate (fun _ => G) sigma output ↔ ForcingEvaluation.Evaluation G sigma output := by
  have he : ∀ s graph o, Equation membershipPredicate (fun _ => G) s graph o ↔ ForcingEvaluation.Equation G graph s o := by
    intro s graph o
    simp only [Equation, membership_predicate, ForcingEvaluation.Equation]
  constructor
  · rintro ⟨graph, hg, hv⟩
    refine ⟨graph, ?_, hv⟩
    intro s o hs
    obtain ⟨hc, hp⟩ := hg s o hs
    exact ⟨hc, (he s graph o).mp ((operator_semantics membershipPredicate (fun _ => G) s graph o).mp hp)⟩
  · rintro ⟨graph, hg, hv⟩
    refine ⟨graph, ?_, hv⟩
    intro s o hs
    obtain ⟨hc, hp⟩ := hg s o hs
    exact ⟨hc, (operator_semantics membershipPredicate (fun _ => G) s graph o).mpr ((he s graph o).mpr hp)⟩

def membershipSentence : Source.Sentence :=
  ((evaluation membershipPredicate (fun _ : Fin 1 => (Fin.last 0).castSucc.castSucc)
    (Fin.last 1).castSucc (Fin.last 2)).iff
      (ForcingEvaluation.evaluation (Fin.last 0).castSucc.castSucc (Fin.last 1).castSucc (Fin.last 2))).close

theorem membership_models : (Translation.sentence membershipSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  have he := membership_equivalence (v (Fin.last 0).castSucc.castSucc) (v (Fin.last 1).castSucc) (v (Fin.last 2))
  have hl := evaluation_semantics v membershipPredicate
    (fun _ : Fin 1 => (Fin.last 0).castSucc.castSucc) (Fin.last 1).castSucc (Fin.last 2)
  have hr := ForcingEvaluation.evaluation_semantics v
    (Fin.last 0).castSucc.castSucc (Fin.last 1).castSucc (Fin.last 2)
  exact ⟨fun h => hr.mpr (he.mp (hl.mp h)), fun h => hl.mpr (he.mpr (hr.mp h))⟩

theorem membership_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence membershipSentence) :=
  ModelTransfer.derives (fun _ _ => membership_models)

end PPAC.Migration.ForcingClassEvaluation
