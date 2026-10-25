/-
Object-theory adaptation of OpenAI math 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
OAI/SetTheory/PartitionConsistency/Forcing/ForcingNames.lean: Child and child_wf.
The source proof uses the three links tau in {tau} in pair(tau,p) in sigma.
We keep that exact Kuratowski relation and reuse the accepted ZF set-induction
schema. In arbitrary nativeZF models it supplies formula-indexed internal
induction, not a false assertion that the external membership relation is
WellFounded. Consumers include source IsName/evaluate/mapConditions and
AtomicForcing.eq_refl. The separate pair/triple-rank recursions and these
constructions are not asserted by this module.
-/
import PPAC.Migration.GodelDefOutput
import PPAC.Migration.SetInduction

namespace PPAC.Migration.ForcingNameInduction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
universe u
variable {A : Type u}

/-- Exact original Child: some condition labels the pair edge into the parent. -/
def child {m : Nat} (subname parent : Fin m) : Formula m :=
  .ex (Source.SetLanguage.edge parent.castSucc subname.castSucc (Fin.last m))

def below {n m : Nat} (p : Formula (n+1)) (rho : Fin n → Fin m) (x : Fin m) : Formula m :=
  .all ((child (Fin.last m) x.castSucc).imp
    (MinimalPredicates.pred p (ReplacementPredicates.paramsUp rho) (Fin.last m)))

def progressive {n m : Nat} (p : Formula (n+1)) (rho : Fin n → Fin m) : Formula m :=
  .all ((below p (ReplacementPredicates.paramsUp rho) (Fin.last m)).imp
    (MinimalPredicates.pred p (ReplacementPredicates.paramsUp rho) (Fin.last m)))

def sentence {n : Nat} (p : Formula (n+1)) : Source.Sentence :=
  ((progressive p id).imp (SetInductionSyntax.holds p id)).close

/-- The two finite membership levels used in the original three-link descent. -/
def members {n : Nat} (p : Formula (n+1)) : Formula (n+1) :=
  SetInductionSyntax.below p Fin.castSucc (Fin.last n)

def strengthened {n : Nat} (p : Formula (n+1)) : Formula (n+1) :=
  p.conj ((members p).conj (members (members p)))

theorem pred_semantics (E : A → A → Prop) {n m : Nat} (v : Fin m → A)
    (p : Formula (n+1)) (rho : Fin n → Fin m) (x : Fin m) :
    Formula.Realize E v (MinimalPredicates.pred p rho x) ↔
      Formula.Realize E (Fin.lastCases (v x) (fun i => v (rho i))) p := by
  rw [MinimalPredicates.pred, DefinableMinimaChoice.realize_rename]
  have he : (fun i => v (Fin.lastCases x rho i)) = Fin.lastCases (v x) (fun i => v (rho i)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  rw [he]

theorem member_below_semantics (E : A → A → Prop) {n m : Nat} (v : Fin m → A)
    (p : Formula (n+1)) (rho : Fin n → Fin m) (x : Fin m) :
    Formula.Realize E v (SetInductionSyntax.below p rho x) ↔
      ∀ y, E y (v x) → Formula.Realize E (Fin.lastCases y (fun i => v (rho i))) p := by
  simp only [SetInductionSyntax.below, Formula.Realize, pred_semantics,
    ReplacementPredicates.paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem holds_semantics (E : A → A → Prop) {n m : Nat} (v : Fin m → A)
    (p : Formula (n+1)) (rho : Fin n → Fin m) :
    Formula.Realize E v (SetInductionSyntax.holds p rho) ↔
      ∀ x, Formula.Realize E (Fin.lastCases x (fun i => v (rho i))) p := by
  simp only [SetInductionSyntax.holds, Formula.Realize, pred_semantics,
    ReplacementPredicates.paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem member_progressive_semantics (E : A → A → Prop) {n m : Nat} (v : Fin m → A)
    (p : Formula (n+1)) (rho : Fin n → Fin m) :
    Formula.Realize E v (SetInductionSyntax.progressive p rho) ↔
      ∀ x, (∀ y, E y x → Formula.Realize E (Fin.lastCases y (fun i => v (rho i))) p) →
        Formula.Realize E (Fin.lastCases x (fun i => v (rho i))) p := by
  simp only [SetInductionSyntax.progressive, Formula.Realize, member_below_semantics,
    pred_semantics, ReplacementPredicates.paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem members_semantics (E : A → A → Prop) {n : Nat} (v : Fin n → A)
    (p : Formula (n+1)) (x : A) :
    Formula.Realize E (Fin.lastCases x v) (members p) ↔
      ∀ y, E y x → Formula.Realize E (Fin.lastCases y v) p := by
  simp only [members, member_below_semantics, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem strengthened_semantics (E : A → A → Prop) {n : Nat} (v : Fin n → A)
    (p : Formula (n+1)) (x : A) :
    Formula.Realize E (Fin.lastCases x v) (strengthened p) ↔
      Formula.Realize E (Fin.lastCases x v) p ∧
      (∀ y, E y x → Formula.Realize E (Fin.lastCases y v) p) ∧
      (∀ y, E y x → ∀ z, E z y → Formula.Realize E (Fin.lastCases z v) p) := by
  simp only [strengthened, Formula.Realize, members_semantics]

variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem child_semantics {m : Nat} (v : Fin m → M.Carrier .set) (x y : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (child x y) ↔
      ∃ condition, PureKuratowski.PairMember M (v x) condition (v y) := by
  simp only [child, Formula.Realize, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

/-- Same three membership steps as source child_wf; no external WellFounded premise. -/
theorem child_descent {x y : M.Carrier .set}
    (h : ∃ condition, PureKuratowski.PairMember M x condition y) :
    ∃ single edge,
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x single ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem single edge ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem edge y := by
  obtain ⟨condition, edge, hCode, hEdge⟩ := h
  obtain ⟨single, pair, hSingle, _, hPair⟩ := hCode
  exact ⟨single, edge, (hSingle x).mpr rfl, (hPair single).mpr (Or.inl rfl), hEdge⟩

theorem progressive_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (p : Formula (n+1)) (rho : Fin n → Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (progressive p rho) ↔
      ∀ x, (∀ y, (∃ condition, PureKuratowski.PairMember M y condition x) →
        Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
          (Fin.lastCases y (fun i => v (rho i))) p) →
        Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
          (Fin.lastCases x (fun i => v (rho i))) p := by
  simp only [progressive, below, Formula.Realize, child_semantics, pred_semantics,
    ReplacementPredicates.paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

/-- Internal definable induction on the exact all-rank source subname relation. -/
theorem models {n : Nat} (p : Formula (n+1))
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence p)).TrueIn M := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics E _).mpr
  intro v
  change Formula.Realize E v (progressive p id) → Formula.Realize E v (SetInductionSyntax.holds p id)
  intro hProgress
  have hStep := (progressive_semantics v p id).mp hProgress
  have hInd := (Translation.realizes_sentence M _).mp
    ((SetInduction.native_induction (strengthened p)).semantically_entails M hM)
  have hIndAt := (GodelDefOutput.close_semantics E _).mp hInd v
  change Formula.Realize E v (SetInductionSyntax.progressive (strengthened p) id) →
    Formula.Realize E v (SetInductionSyntax.holds (strengthened p) id) at hIndAt
  have hAll := hIndAt ((member_progressive_semantics E v (strengthened p) id).mpr (by
    intro x ih
    apply (strengthened_semantics E v p x).mpr
    refine ⟨hStep x ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨single, edge, hySingle, hSingleEdge, hEdge⟩ := child_descent hy
      exact ((strengthened_semantics E v p edge).mp (ih edge hEdge)).2.2 single hSingleEdge y hySingle
    · intro y hy
      exact ((strengthened_semantics E v p y).mp (ih y hy)).1
    · intro y hy z hz
      exact ((strengthened_semantics E v p y).mp (ih y hy)).2.1 z hz))
  apply (holds_semantics E v p id).mpr
  intro x
  exact ((strengthened_semantics E v p x).mp
    ((holds_semantics E v (strengthened p) id).mp hAll x)).1

/-- Every arbitrary-parameter instance is a closed theorem in the original ZF kernel. -/
theorem kernel_certificate {n : Nat} (p : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence p)) :=
  ModelTransfer.derives (fun _ hM => models p hM)

theorem source_certificate {n : Nat} (p : Formula (n+1)) :
    Source.Derives (Source.SetLanguage.ZF.at 1) ((sentence p).rename Fin.elim0) :=
  ReverseZFReplay.source_sentence (kernel_certificate p)

end PPAC.Migration.ForcingNameInduction
