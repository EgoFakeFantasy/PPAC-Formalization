/- Shared object implementation of the original child_wf.fix used by
ForcingNames.evaluate and mapConditions. Reuses accepted Child induction and
set graph operations. This lemma is consumed with proved operator obligations;
its hypotheses are not assertions that the PPAC mathematics has been proved. -/
import PPAC.Migration.ForcingEvaluation
import PPAC.Migration.OrdinalRecursionSyntax

namespace PPAC.Migration.ForcingNameRecursion
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Existing three-slot substitution: current name, partial graph, output. -/
abbrev op {n m : Nat} (p : Formula (n+3)) (rho : Fin n → Fin m) (sigma g value : Fin m) : Formula m :=
  OrdinalRecursionSyntax.operator p rho sigma g value

def good {n m : Nat} (p : Formula (n+3)) (rho : Fin n → Fin m) (g : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    ((ForcingEvaluation.childrenCovered g.castSucc.castSucc (Fin.last m).castSucc).conj
      (op p (paramsUp (paramsUp rho)) (Fin.last m).castSucc g.castSucc.castSucc (Fin.last (m+1))))))

def value {n m : Nat} (p : Formula (n+3)) (rho : Fin n → Fin m) (sigma output : Fin m) : Formula m :=
  .ex ((good p (paramsUp rho) (Fin.last m)).conj
    (Source.SetLanguage.edge (Fin.last m) sigma.castSucc output.castSucc))

def hasValue {n m : Nat} (p : Formula (n+3)) (rho : Fin n → Fin m) (sigma : Fin m) : Formula m :=
  .ex (value p (paramsUp rho) sigma.castSucc (Fin.last m))

def Step {n : Nat} (p : Formula (n+3)) (params : Fin n → M.Carrier .set)
    (sigma g output : M.Carrier .set) : Prop :=
  Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
    (Fin.lastCases output (Fin.lastCases g (Fin.lastCases sigma params))) p

def Good {n : Nat} (p : Formula (n+3)) (params : Fin n → M.Carrier .set) (g : M.Carrier .set) : Prop :=
  ∀ sigma output, PureKuratowski.PairMember M sigma output g →
    ForcingEvaluation.Covered g sigma ∧ Step p params sigma g output

def Value {n : Nat} (p : Formula (n+3)) (params : Fin n → M.Carrier .set)
    (sigma output : M.Carrier .set) : Prop :=
  ∃ g, Good p params g ∧ PureKuratowski.PairMember M sigma output g

/-- These are proved for each source operator, never added as object axioms. -/
structure OperatorFacts {n : Nat} (p : Formula (n+3)) (params : Fin n → M.Carrier .set) : Prop where
  total : ∀ sigma g, ∃ output, Step p params sigma g output
  unique : ∀ sigma g x y, Step p params sigma g x → Step p params sigma g y → x = y
  child_congr : ∀ sigma g h, (∀ tau condition, PureKuratowski.PairMember M tau condition sigma →
    ∀ x, PureKuratowski.PairMember M tau x g ↔ PureKuratowski.PairMember M tau x h) →
    ∀ output, Step p params sigma g output ↔ Step p params sigma h output

theorem op_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (p : Formula (n+3))
    (rho : Fin n → Fin m) (sigma g output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (op p rho sigma g output) ↔
      Step p (fun i => v (rho i)) (v sigma) (v g) (v output) := by
  rw [op, OrdinalRecursionSyntax.operator, DefinableMinimaChoice.realize_rename]
  have he : (fun i => v (Fin.lastCases output (Fin.lastCases g (Fin.lastCases sigma rho)) i)) =
      Fin.lastCases (v output) (Fin.lastCases (v g) (Fin.lastCases (v sigma) (fun i => v (rho i)))) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      · refine Fin.lastCases ?_ (fun t => ?_) k <;>
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  rw [he]
  rfl

theorem good_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (p : Formula (n+3))
    (rho : Fin n → Fin m) (g : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (good p rho g) ↔
      Good p (fun i => v (rho i)) (v g) := by
  simp only [good, Formula.Realize, KuratowskiZF.source_edge, ForcingEvaluation.covered_semantics (M := M),
    op_semantics (M := M), paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, Good]
  rfl

theorem value_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (p : Formula (n+3))
    (rho : Fin n → Fin m) (sigma output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (value p rho sigma output) ↔
      Value p (fun i => v (rho i)) (v sigma) (v output) := by
  simp only [value, Formula.Realize, good_semantics (M := M), KuratowskiZF.source_edge,
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, Value]
  rfl

theorem hasValue_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (p : Formula (n+3))
    (rho : Fin n → Fin m) (sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (hasValue p rho sigma) ↔
      ∃ output, Value p (fun i => v (rho i)) (v sigma) output := by
  simp only [hasValue, Formula.Realize, value_semantics (M := M), paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem compatible (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {p : Formula (n+3)} {params : Fin n → M.Carrier .set} (facts : OperatorFacts p params)
    {g h : M.Carrier .set} (hg : Good p params g) (hh : Good p params h) :
    ∀ sigma x y, PureKuratowski.PairMember M sigma x g → PureKuratowski.PairMember M sigma y h → x = y := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  let q := ForcingEvaluation.comparison (0 : Fin 3) 1 2
  let v : Fin 2 → M.Carrier .set := Fin.cases g (fun _ => h)
  have hc : ∀ sigma, Formula.Realize E (Fin.lastCases sigma v) q ↔
      ∀ x y, PureKuratowski.PairMember M sigma x g → PureKuratowski.PairMember M sigma y h → x = y := by
    intro sigma
    have hr := ForcingEvaluation.comparison_semantics (M := M) (Fin.lastCases sigma v) (0 : Fin 3) 1 2
    have h0 : Fin.lastCases sigma v (0 : Fin 3) = g := (Fin.lastCases_castSucc (0 : Fin 2)).trans Fin.cases_zero
    have h1 : Fin.lastCases sigma v (1 : Fin 3) = h := (Fin.lastCases_castSucc (1 : Fin 2)).trans (Fin.cases_succ (0 : Fin 1))
    have h2 : Fin.lastCases sigma v (2 : Fin 3) = sigma := Fin.lastCases_last
    rw [h0, h1, h2] at hr
    exact hr
  have hi := (GodelDefOutput.close_semantics E _).mp
    ((Translation.realizes_sentence M _).mp
      ((ForcingNameInduction.kernel_certificate q).semantically_entails M hM)) v
  change Formula.Realize E v (ForcingNameInduction.progressive q id) →
    Formula.Realize E v (SetInductionSyntax.holds q id) at hi
  have hAll := hi ((ForcingNameInduction.progressive_semantics v q id).mpr (by
    intro sigma ih
    apply (hc sigma).mpr
    intro x y hx hy
    obtain ⟨cg, sg⟩ := hg sigma x hx
    obtain ⟨ch, sh⟩ := hh sigma y hy
    have ha : ∀ tau condition, PureKuratowski.PairMember M tau condition sigma →
        ∀ z, PureKuratowski.PairMember M tau z g ↔ PureKuratowski.PairMember M tau z h := by
      intro tau condition he z
      constructor
      · intro hz
        obtain ⟨w, hw⟩ := ch tau condition he
        have heq := (hc tau).mp (ih tau ⟨condition, he⟩) z w hz hw
        exact heq.symm ▸ hw
      · intro hz
        obtain ⟨w, hw⟩ := cg tau condition he
        have heq := (hc tau).mp (ih tau ⟨condition, he⟩) w z hw hz
        exact heq ▸ hw
    exact facts.unique sigma h x y ((facts.child_congr sigma g h ha x).mp sg) sh))
  intro sigma
  exact (hc sigma).mp ((ForcingNameInduction.holds_semantics E v q id).mp hAll sigma)

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {p : Formula (n+3)} {params : Fin n → M.Carrier .set} (facts : OperatorFacts p params)
    {sigma x y : M.Carrier .set} (hx : Value p params sigma x) (hy : Value p params sigma y) : x = y := by
  obtain ⟨g, hg, hx⟩ := hx
  obtain ⟨h, hh, hy⟩ := hy
  exact compatible hM facts hg hh sigma x y hx hy

theorem union_good (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {p : Formula (n+3)} {params : Fin n → M.Carrier .set} (facts : OperatorFacts p params)
    {family U : M.Carrier .set}
    (hFamily : ∀ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family → Good p params part)
    (hU : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x U ↔
      ∃ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem x part) : Good p params U := by
  intro sigma output he
  obtain ⟨part, hPart, hValue⟩ := (ForcingEvaluation.union_edge hU sigma output).mp he
  obtain ⟨hc, hs⟩ := hFamily part hPart sigma output hValue
  have ha : ∀ tau condition, PureKuratowski.PairMember M tau condition sigma →
      ∀ x, PureKuratowski.PairMember M tau x part ↔ PureKuratowski.PairMember M tau x U := by
    intro tau condition he x
    constructor
    · intro hx
      exact (ForcingEvaluation.union_edge hU tau x).mpr ⟨part, hPart, hx⟩
    · intro hx
      obtain ⟨other, hOther, hOtherValue⟩ := (ForcingEvaluation.union_edge hU tau x).mp hx
      obtain ⟨v, hv⟩ := hc tau condition he
      have heq := compatible hM facts (hFamily other hOther) (hFamily part hPart) tau x v hOtherValue hv
      exact heq.symm ▸ hv
  refine ⟨?_, (facts.child_congr sigma part U ha output).mp hs⟩
  intro tau condition he
  obtain ⟨v, hv⟩ := hc tau condition he
  exact ⟨v, (ha tau condition he v).mp hv⟩

def entryWitness {n m : Nat} (p : Formula (n+3)) (rho : Fin n → Fin m) (z g : Fin m) : Formula m :=
  (good p rho g).conj (.all (.all ((PairSyntax.ordered z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1))).imp
      (.ex (Source.SetLanguage.edge g.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m+2)))))))

theorem entryWitness_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (p : Formula (n+3))
    (rho : Fin n → Fin m) (z g : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (entryWitness p rho z g) ↔
      Good p (fun i => v (rho i)) (v g) ∧ ∀ tau condition, PureKuratowski.Code M (v z) tau condition →
        ∃ output, PureKuratowski.PairMember M tau output (v g) := by
  simp only [entryWitness, Formula.Realize, good_semantics (M := M), KuratowskiZF.source_code,
    KuratowskiZF.source_edge, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem collect_children (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+3)) (params : Fin n → M.Carrier .set) (facts : OperatorFacts p params)
    (sigma : M.Carrier .set)
    (ih : ∀ tau condition, PureKuratowski.PairMember M tau condition sigma → ∃ output, Value p params tau output) :
    ∃ g, Good p params g ∧ ForcingEvaluation.Covered g sigma := by
  classical
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hKP := SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨empty, hEmpty⟩ := SetTheory.KP.exists_empty hKP
  have hEmptyGood : Good p params empty := by
    intro tau output he
    obtain ⟨z, _, hz⟩ := he
    exact False.elim (hEmpty z hz)
  have hWitness : ∀ z, E z sigma → ∃ g, Good p params g ∧
      ∀ tau condition, PureKuratowski.Code M z tau condition → ∃ output, PureKuratowski.PairMember M tau output g := by
    intro z hz
    by_cases he : ∃ tau condition, PureKuratowski.Code M z tau condition
    · obtain ⟨tau, condition, hCode⟩ := he
      obtain ⟨output, g, hg, hv⟩ := ih tau condition ⟨z, hCode, hz⟩
      refine ⟨g, hg, ?_⟩
      intro tau' condition' hCode'
      obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hCode hCode'
      exact ⟨output, hv⟩
    · exact ⟨empty, hEmptyGood, fun tau condition hCode => False.elim (he ⟨tau, condition, hCode⟩)⟩
  let matrix := entryWitness p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))
  have hc := (GodelDefOutput.close_semantics E (CollectionSyntax.core matrix)).mp
    ((Translation.realizes_sentence M _).mp ((CollectionSyntax.source_collection matrix).semantically_entails M hM)) params
  simp only [E, matrix, CollectionSyntax.core, Formula.Realize, DefinableMinimaChoice.realize_rename,
    entryWitness_semantics (M := M), CollectionSyntax.firstIndex, CollectionSyntax.secondIndex,
    Fin.lastCases_last, Fin.lastCases_castSucc] at hc
  obtain ⟨family, hFamily⟩ := hc sigma hWitness
  let query := good p Fin.castSucc (Fin.last n)
  have hSep := (GodelDefOutput.separation_semantics E query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨filtered, hFiltered⟩ := hSep params family
  have hf : ∀ part, E part filtered ↔ E part family ∧ Good p params part := by
    intro part
    apply (hFiltered part).trans
    apply and_congr Iff.rfl
    have hr := good_semantics (M := M) (Fin.lastCases part params) p Fin.castSucc (Fin.last n)
    simpa only [Fin.lastCases_castSucc, Fin.lastCases_last] using hr
  obtain ⟨g, hg⟩ := SetTheory.KP.exists_union hKP filtered
  refine ⟨g, union_good hM facts (fun part hp => ((hf part).mp hp).2) hg, ?_⟩
  intro tau condition he
  obtain ⟨z, hCode, hz⟩ := he
  obtain ⟨part, hPart, hGood, hValues⟩ := hFamily z hz
  obtain ⟨output, hv⟩ := hValues tau condition hCode
  exact ⟨output, (ForcingEvaluation.union_edge hg tau output).mpr ⟨part, (hf part).mpr ⟨hPart, hGood⟩, hv⟩⟩

theorem extend_good {n : Nat} {p : Formula (n+3)} {params : Fin n → M.Carrier .set}
    (facts : OperatorFacts p params) {g sigma output extended : M.Carrier .set}
    (hg : Good p params g) (hc : ForcingEvaluation.Covered g sigma) (hs : Step p params sigma g output)
    (he : ∀ tau x, PureKuratowski.PairMember M tau x extended ↔
      PureKuratowski.PairMember M tau x g ∨ (tau = sigma ∧ x = output)) : Good p params extended := by
  have hAgree : ∀ x, PureKuratowski.PairMember M sigma x g → x = output :=
    fun x hx => facts.unique sigma g x output (hg sigma x hx).2 hs
  have transfer : ∀ parent x, ForcingEvaluation.Covered g parent → Step p params parent g x →
      ForcingEvaluation.Covered extended parent ∧ Step p params parent extended x := by
    intro parent x hCover hStep
    have ha : ∀ tau condition, PureKuratowski.PairMember M tau condition parent →
        ∀ z, PureKuratowski.PairMember M tau z g ↔ PureKuratowski.PairMember M tau z extended := by
      intro tau condition hChild z
      constructor
      · intro hz
        exact (he tau z).mpr (Or.inl hz)
      · intro hz
        rcases (he tau z).mp hz with hOld | ⟨hTau, hZ⟩
        · exact hOld
        · subst tau
          subst z
          obtain ⟨v, hv⟩ := hCover sigma condition hChild
          exact hAgree v hv ▸ hv
    refine ⟨?_, (facts.child_congr parent g extended ha x).mp hStep⟩
    intro tau condition hChild
    obtain ⟨v, hv⟩ := hCover tau condition hChild
    exact ⟨v, (ha tau condition hChild v).mp hv⟩
  intro parent x hx
  rcases (he parent x).mp hx with hOld | ⟨hParent, hX⟩
  · exact transfer parent x (hg parent x hOld).1 (hg parent x hOld).2
  · subst parent
    subst x
    exact transfer sigma output hc hs

theorem existence_step (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+3)) (params : Fin n → M.Carrier .set) (facts : OperatorFacts p params)
    (sigma : M.Carrier .set)
    (ih : ∀ tau condition, PureKuratowski.PairMember M tau condition sigma → ∃ output, Value p params tau output) :
    ∃ output, Value p params sigma output := by
  obtain ⟨g, hg, hc⟩ := collect_children hM p params facts sigma ih
  obtain ⟨output, hs⟩ := facts.total sigma g
  obtain ⟨code, hCode⟩ := KuratowskiZF.exists_code hM sigma output
  obtain ⟨extended, hInsert⟩ := SetTheory.KP.exists_insert
    (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) g code
  have he := ForcingEvaluation.insert_edge hCode hInsert
  exact ⟨output, extended, extend_good facts hg hc hs he, (he sigma output).mpr (Or.inr ⟨rfl, rfl⟩)⟩

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+3)) (params : Fin n → M.Carrier .set) (facts : OperatorFacts p params)
    (sigma : M.Carrier .set) : ∃ output, Value p params sigma output := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  let q := hasValue p Fin.castSucc (Fin.last n)
  have hq : ∀ tau, Formula.Realize E (Fin.lastCases tau params) q ↔ ∃ output, Value p params tau output := by
    intro tau
    have hr := hasValue_semantics (M := M) (Fin.lastCases tau params) p Fin.castSucc (Fin.last n)
    simpa only [Fin.lastCases_castSucc, Fin.lastCases_last] using hr
  have hi := (GodelDefOutput.close_semantics E _).mp
    ((Translation.realizes_sentence M _).mp
      ((ForcingNameInduction.kernel_certificate q).semantically_entails M hM)) params
  change Formula.Realize E params (ForcingNameInduction.progressive q id) →
    Formula.Realize E params (SetInductionSyntax.holds q id) at hi
  have hAll := hi ((ForcingNameInduction.progressive_semantics params q id).mpr (by
    intro tau ih
    apply (hq tau).mpr
    apply existence_step hM p params facts tau
    intro child condition he
    exact (hq child).mp (ih child ⟨condition, he⟩)))
  exact (hq sigma).mp ((ForcingNameInduction.holds_semantics E params q id).mp hAll sigma)

end PPAC.Migration.ForcingNameRecursion
