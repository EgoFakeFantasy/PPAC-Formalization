/- Pinned OpenAI Forcing/ForcingNames.lean: mapConditions and its exact
membership equation. The condition map is an arbitrary definable total
single-valued relation, with all object parameters retained. The actual
ConditionAction.actCode is a later instance, not a restriction of this schema. -/
import PPAC.Migration.ForcingNameRecursion
import PPAC.Migration.GodelDefRecursion
import YesMetaZFC.SetTheory.ProductConstruction

namespace PPAC.Migration.ForcingMapConditions
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def MapRel {n : Nat} (f : Formula (n+2)) (params : Fin n → M.Carrier .set) (x y : M.Carrier .set) : Prop :=
  Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases y (Fin.lastCases x params)) f

def IsFunction {n : Nat} (f : Formula (n+2)) (params : Fin n → M.Carrier .set) : Prop :=
  ∀ x, ∃ y, MapRel f params x y ∧ ∀ z, MapRel f params x z → z = y

def function {n m : Nat} (f : Formula (n+2)) (rho : Fin n → Fin m) : Formula m :=
  .all (.ex ((ReplacementPredicates.rel f (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))).conj
    (.all ((ReplacementPredicates.rel f (paramsUp (paramsUp (paramsUp rho)))
      (Fin.last m).castSucc.castSucc (Fin.last (m+2))).imp (.equal (Fin.last (m+2)) (Fin.last (m+1)).castSucc)))))

theorem rel_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (f : Formula (n+2))
    (rho : Fin n → Fin m) (x y : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (ReplacementPredicates.rel f rho x y) ↔
      MapRel f (fun i => v (rho i)) (v x) (v y) := by
  rw [ReplacementPredicates.rel, Source.SetLanguage.relation, DefinableMinimaChoice.realize_rename]
  have he : (fun i => v (Fin.lastCases y (Fin.lastCases x rho) i)) =
      Fin.lastCases (v y) (Fin.lastCases (v x) (fun i => v (rho i))) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
    · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  rw [he]
  rfl

theorem function_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (f : Formula (n+2)) (rho : Fin n → Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (function f rho) ↔
      IsFunction f (fun i => v (rho i)) := by
  simp only [function, Formula.Realize, rel_semantics (M := M), paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, IsFunction]
  rfl

theorem function_unique {n : Nat} {f : Formula (n+2)} {params : Fin n → M.Carrier .set}
    (hf : IsFunction f params) (x y z : M.Carrier .set) (hy : MapRel f params x y) (hz : MapRel f params x z) : y = z := by
  obtain ⟨v, _, hv⟩ := hf x
  exact (hv y hy).trans (hv z hz).symm

def entry {n m : Nat} (f : Formula (n+2)) (rho : Fin n → Fin m) (sigma g z : Fin m) : Formula m :=
  .ex (.ex (.ex (.ex ((Source.SetLanguage.edge sigma.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc).conj
      ((Source.SetLanguage.edge g.castSucc.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc).conj
        ((ReplacementPredicates.rel f (fun i => (rho i).castSucc.castSucc.castSucc.castSucc)
          (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3))).conj
          (PairSyntax.ordered z.castSucc.castSucc.castSucc.castSucc
            (Fin.last (m+2)).castSucc (Fin.last (m+3)))))))))

def equation {n m : Nat} (f : Formula (n+2)) (rho : Fin n → Fin m) (sigma g output : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) output.castSucc).iff
    (entry f (paramsUp rho) sigma.castSucc g.castSucc (Fin.last m)))

def operator {n : Nat} (f : Formula (n+2)) : Formula (n+3) :=
  equation f (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))

def Equation {n : Nat} (f : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (sigma g output : M.Carrier .set) : Prop :=
  ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z output ↔
    ∃ tau condition childValue mappedCondition, PureKuratowski.PairMember M tau condition sigma ∧
      PureKuratowski.PairMember M tau childValue g ∧ MapRel f params condition mappedCondition ∧
      PureKuratowski.Code M z childValue mappedCondition

theorem entry_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (f : Formula (n+2))
    (rho : Fin n → Fin m) (sigma g z : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (entry f rho sigma g z) ↔
      ∃ tau condition childValue mappedCondition, PureKuratowski.PairMember M tau condition (v sigma) ∧
        PureKuratowski.PairMember M tau childValue (v g) ∧ MapRel f (fun i => v (rho i)) condition mappedCondition ∧
        PureKuratowski.Code M (v z) childValue mappedCondition := by
  simp only [entry, Formula.Realize, KuratowskiZF.source_edge, KuratowskiZF.source_code,
    rel_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem equation_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (f : Formula (n+2))
    (rho : Fin n → Fin m) (sigma g output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (equation f rho sigma g output) ↔
      Equation f (fun i => v (rho i)) (v sigma) (v g) (v output) := by
  simp only [equation, Source.Formula.iff, Formula.Realize, entry_semantics (M := M), paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, Equation]
  exact forall_congr' (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)

theorem operator_semantics {n : Nat} (f : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (sigma g output : M.Carrier .set) :
    ForcingNameRecursion.Step (operator f) params sigma g output ↔ Equation f params sigma g output := by
  unfold ForcingNameRecursion.Step operator
  simp only [equation_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Reuse the exact existing Source-to-Project encoder for functional Replacement. -/
theorem binary_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (f : Formula (n+2)) (params : Fin n → M.Carrier .set) (default x y : M.Carrier .set) :
    (ProjectSyntax.binary f).denote
      ({ bound := fun i => params i.rev, free := fun _ => default } :
        SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) n) x y ↔ MapRel f params x y := by
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) n :=
    { bound := fun i => params i.rev, free := fun _ => default }
  have he := GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM) f Fin.rev ((env.push x).push y)
  have hr : (fun i => ((env.push x).push y).bound i.rev) = Fin.lastCases y (Fin.lastCases x params) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.rev_last, SetTheory.Env.push, Fin.cases_zero, Fin.lastCases_last]
    · refine Fin.lastCases ?_ (fun k => ?_) j <;>
        simp only [Fin.rev_castSucc, Fin.rev_last, SetTheory.Env.push, Fin.cases_succ,
          Fin.cases_zero, Fin.lastCases_castSucc, Fin.lastCases_last, env, Fin.rev_rev]
  rw [hr] at he
  exact he

theorem coordinate_bound (hM : FirstOrder.Theory.Models M nativeZF) (g : M.Carrier .set) :
    ∃ bound, ∀ x y, PureKuratowski.PairMember M x y g →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x bound ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem y bound := by
  have hKP := SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨U, hU⟩ := SetTheory.KP.exists_union hKP g
  obtain ⟨V, hV⟩ := SetTheory.KP.exists_union hKP U
  refine ⟨V, ?_⟩
  intro x y he
  obtain ⟨code, hCode, hMem⟩ := he
  have hb : ∀ z, z = x ∨ z = y → (Definitional.Project.FirstOrderSemantics.reduct M).mem z V := by
    intro z hz
    obtain ⟨part, hPart, hZ⟩ := (PureKuratowski.code_union hCode z).mpr hz
    exact (hV z).mpr ⟨part, (hU part).mpr ⟨code, hMem, hPart⟩, hZ⟩
  exact ⟨hb x (Or.inl rfl), hb y (Or.inr rfl)⟩

theorem equation_exists (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (f : Formula (n+2)) (params : Fin n → M.Carrier .set) (hf : IsFunction f params)
    (sigma g : M.Carrier .set) : ∃ output, Equation f params sigma g output := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨conditionBound, hConditionBound⟩ := coordinate_bound hM sigma
  obtain ⟨valueBound, hValueBound⟩ := coordinate_bound hM g
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) n :=
    { bound := fun i => params i.rev, free := fun _ => sigma }
  have hRel := binary_semantics hM f params sigma
  obtain ⟨mappedBound, hMappedBound⟩ := SetTheory.ZF.exists_functionalImage hZF (ProjectSyntax.binary f) env conditionBound
    (fun x _ => by
      obtain ⟨y, hy, _⟩ := hf x
      exact ⟨y, (hRel x y).mpr hy⟩)
    (fun x y z hy hz => function_unique hf x y z ((hRel x y).mp hy) ((hRel x z).mp hz))
  obtain ⟨product, hProduct⟩ := SetTheory.ZF.exists_cartesianProduct hZF (KuratowskiZF.interpretation hM) valueBound mappedBound
  let query := entry f (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))
  let inputs : Fin (n+2) → M.Carrier .set := Fin.lastCases g (Fin.lastCases sigma params)
  have hSep := (GodelDefOutput.separation_semantics E query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨output, hOutput⟩ := hSep inputs product
  have hEntry : ∀ z, Formula.Realize E (Fin.lastCases z inputs) query ↔
      ∃ tau condition childValue mappedCondition, PureKuratowski.PairMember M tau condition sigma ∧
        PureKuratowski.PairMember M tau childValue g ∧ MapRel f params condition mappedCondition ∧
        PureKuratowski.Code M z childValue mappedCondition := by
    intro z
    have hr := entry_semantics (M := M) (Fin.lastCases z inputs) f
      (fun i => i.castSucc.castSucc.castSucc) (Fin.last n).castSucc.castSucc
      (Fin.last (n+1)).castSucc (Fin.last (n+2))
    simpa only [inputs, Fin.lastCases_castSucc, Fin.lastCases_last] using hr
  refine ⟨output, fun z => ?_⟩
  constructor
  · intro hz
    exact (hEntry z).mp ((hOutput z).mp hz).2
  · rintro ⟨tau, condition, childValue, mappedCondition, he, hv, hfValue, hCode⟩
    apply (hOutput z).mpr
    refine ⟨?_, (hEntry z).mpr ⟨tau, condition, childValue, mappedCondition, he, hv, hfValue, hCode⟩⟩
    apply (hProduct z).mpr
    exact ⟨childValue, (hValueBound tau childValue hv).2, mappedCondition,
      (hMappedBound mappedCondition).mpr ⟨condition, (hConditionBound tau condition he).2, (hRel condition mappedCondition).mpr hfValue⟩,
      hCode⟩

theorem operator_facts (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (f : Formula (n+2)) (params : Fin n → M.Carrier .set) (hf : IsFunction f params) :
    ForcingNameRecursion.OperatorFacts (operator f) params := by
  constructor
  · intro sigma g
    obtain ⟨output, hs⟩ := equation_exists hM f params hf sigma g
    exact ⟨output, (operator_semantics f params sigma g output).mpr hs⟩
  · intro sigma g x y hx hy
    have hx' := (operator_semantics f params sigma g x).mp hx
    have hy' := (operator_semantics f params sigma g y).mp hy
    exact (ModelTransfer.extensionality hM).eq_of_same_members x y (fun z => (hx' z).trans (hy' z).symm)
  · intro sigma g h ha output
    have hp : ∀ z, (∃ tau condition v q, PureKuratowski.PairMember M tau condition sigma ∧
        PureKuratowski.PairMember M tau v g ∧ MapRel f params condition q ∧ PureKuratowski.Code M z v q) ↔
      (∃ tau condition v q, PureKuratowski.PairMember M tau condition sigma ∧
        PureKuratowski.PairMember M tau v h ∧ MapRel f params condition q ∧ PureKuratowski.Code M z v q) := by
      intro z
      constructor
      · rintro ⟨tau, condition, v, q, he, hv, hfValue, hCode⟩
        exact ⟨tau, condition, v, q, he, (ha tau condition he v).mp hv, hfValue, hCode⟩
      · rintro ⟨tau, condition, v, q, he, hv, hfValue, hCode⟩
        exact ⟨tau, condition, v, q, he, (ha tau condition he v).mpr hv, hfValue, hCode⟩
    constructor
    · intro hs
      apply (operator_semantics f params sigma h output).mpr
      intro z
      exact ((operator_semantics f params sigma g output).mp hs z).trans (hp z)
    · intro hs
      apply (operator_semantics f params sigma g output).mpr
      intro z
      exact ((operator_semantics f params sigma h output).mp hs z).trans (hp z).symm

def mapping {n m : Nat} (f : Formula (n+2)) (rho : Fin n → Fin m) (sigma output : Fin m) : Formula m :=
  ForcingNameRecursion.value (operator f) rho sigma output

def Mapped {n : Nat} (f : Formula (n+2)) (params : Fin n → M.Carrier .set) (sigma output : M.Carrier .set) : Prop :=
  ForcingNameRecursion.Value (operator f) params sigma output

theorem mapping_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (f : Formula (n+2))
    (rho : Fin n → Fin m) (sigma output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (mapping f rho sigma output) ↔
      Mapped f (fun i => v (rho i)) (v sigma) (v output) :=
  ForcingNameRecursion.value_semantics v (operator f) rho sigma output

theorem exists_mapping (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (f : Formula (n+2)) (params : Fin n → M.Carrier .set) (hf : IsFunction f params) (sigma : M.Carrier .set) :
    ∃ output, Mapped f params sigma output :=
  ForcingNameRecursion.exists_value hM (operator f) params (operator_facts hM f params hf) sigma

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f : Formula (n+2)} {params : Fin n → M.Carrier .set} (hf : IsFunction f params)
    {sigma x y : M.Carrier .set} (hx : Mapped f params sigma x) (hy : Mapped f params sigma y) : x = y :=
  ForcingNameRecursion.unique hM (operator_facts hM f params hf) hx hy

theorem mem_mapping (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f : Formula (n+2)} {params : Fin n → M.Carrier .set} (hf : IsFunction f params)
    {sigma output : M.Carrier .set} (hs : Mapped f params sigma output) (z : M.Carrier .set) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem z output ↔
      ∃ tau condition childValue mappedCondition, PureKuratowski.PairMember M tau condition sigma ∧
        Mapped f params tau childValue ∧ MapRel f params condition mappedCondition ∧
        PureKuratowski.Code M z childValue mappedCondition := by
  obtain ⟨g, hg, hValue⟩ := hs
  obtain ⟨hc, hStep⟩ := hg sigma output hValue
  have heq := (operator_semantics f params sigma g output).mp hStep
  constructor
  · intro hz
    obtain ⟨tau, condition, v, q, he, hv, hfValue, hCode⟩ := (heq z).mp hz
    exact ⟨tau, condition, v, q, he, ⟨g, hg, hv⟩, hfValue, hCode⟩
  · rintro ⟨tau, condition, v, q, he, hv, hfValue, hCode⟩
    obtain ⟨w, hw⟩ := hc tau condition he
    have heq' := unique hM hf hv ⟨g, hg, hw⟩
    exact (heq z).mpr ⟨tau, condition, v, q, he, heq'.symm ▸ hw, hfValue, hCode⟩

def mappedEntry {n m : Nat} (f : Formula (n+2)) (rho : Fin n → Fin m) (sigma z : Fin m) : Formula m :=
  .ex (.ex (.ex (.ex ((Source.SetLanguage.edge sigma.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc).conj
      ((mapping f (fun i => (rho i).castSucc.castSucc.castSucc.castSucc)
        (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc).conj
        ((ReplacementPredicates.rel f (fun i => (rho i).castSucc.castSucc.castSucc.castSucc)
          (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3))).conj
          (PairSyntax.ordered z.castSucc.castSucc.castSucc.castSucc
            (Fin.last (m+2)).castSucc (Fin.last (m+3)))))))))

theorem mappedEntry_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (f : Formula (n+2))
    (rho : Fin n → Fin m) (sigma z : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (mappedEntry f rho sigma z) ↔
      ∃ tau condition childValue mappedCondition, PureKuratowski.PairMember M tau condition (v sigma) ∧
        Mapped f (fun i => v (rho i)) tau childValue ∧ MapRel f (fun i => v (rho i)) condition mappedCondition ∧
        PureKuratowski.Code M (v z) childValue mappedCondition := by
  simp only [mappedEntry, Formula.Realize, KuratowskiZF.source_edge, KuratowskiZF.source_code,
    mapping_semantics (M := M), rel_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def existenceSentence {n : Nat} (f : Formula (n+2)) : Source.Sentence :=
  ((function f Fin.castSucc).imp (.ex (mapping f (fun i => i.castSucc.castSucc)
    (Fin.last n).castSucc (Fin.last (n+1))))).close

def uniquenessSentence {n : Nat} (f : Formula (n+2)) : Source.Sentence :=
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  ((function f rho).imp ((mapping f rho (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).imp
    ((mapping f rho (Fin.last n).castSucc.castSucc (Fin.last (n+2))).imp
      (.equal (Fin.last (n+1)).castSucc (Fin.last (n+2)))))).close

def unfoldingSentence {n : Nat} (f : Formula (n+2)) : Source.Sentence :=
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  ((function f rho).imp ((mapping f rho (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).imp
    ((Formula.mem (Fin.last (n+2)) (Fin.last (n+1)).castSucc).iff
      (mappedEntry f rho (Fin.last n).castSucc.castSucc (Fin.last (n+2)))))).close

theorem existence_models {n : Nat} (f : Formula (n+2)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (existenceSentence f)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  have hf := (function_semantics v f Fin.castSucc).mp h
  obtain ⟨output, hOutput⟩ := exists_mapping hM f (fun i => v i.castSucc) hf (v (Fin.last n))
  refine ⟨output, ?_⟩
  apply (mapping_semantics (Fin.lastCases output v) f (fun i => i.castSucc.castSucc)
    (Fin.last n).castSucc (Fin.last (n+1))).mpr
  simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hOutput

theorem uniqueness_models {n : Nat} (f : Formula (n+2)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (uniquenessSentence f)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h hx hy
  exact unique hM ((function_semantics v f _).mp h)
    ((mapping_semantics v f _ _ _).mp hx) ((mapping_semantics v f _ _ _).mp hy)

theorem unfolding_models {n : Nat} (f : Formula (n+2)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (unfoldingSentence f)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h hs
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  have he := mem_mapping hM ((function_semantics v f rho).mp h)
    ((mapping_semantics v f rho (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).mp hs) (v (Fin.last (n+2)))
  have hr := mappedEntry_semantics v f rho (Fin.last n).castSucc.castSucc (Fin.last (n+2))
  exact ⟨fun hz => hr.mpr (he.mp hz), fun hz => he.mpr (hr.mp hz)⟩

theorem existence_kernel_certificate {n : Nat} (f : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence f)) :=
  ModelTransfer.derives (fun _ hM => existence_models f hM)

theorem uniqueness_kernel_certificate {n : Nat} (f : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence f)) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models f hM)

theorem unfolding_kernel_certificate {n : Nat} (f : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (unfoldingSentence f)) :=
  ModelTransfer.derives (fun _ hM => unfolding_models f hM)

theorem edge_mapping (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f : Formula (n+2)} {params : Fin n → M.Carrier .set} (hf : IsFunction f params)
    {sigma output : M.Carrier .set} (hs : Mapped f params sigma output) (child condition : M.Carrier .set) :
    PureKuratowski.PairMember M child condition output ↔
      ∃ tau p, PureKuratowski.PairMember M tau p sigma ∧ Mapped f params tau child ∧ MapRel f params p condition := by
  constructor
  · rintro ⟨z, hCode, hz⟩
    obtain ⟨tau, p, v, q, he, hv, hq, hCode'⟩ := (mem_mapping hM hf hs z).mp hz
    obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hCode hCode'
    exact ⟨tau, p, he, hv, hq⟩
  · rintro ⟨tau, p, he, hv, hq⟩
    obtain ⟨z, hCode⟩ := KuratowskiZF.exists_code hM child condition
    exact ⟨z, hCode, (mem_mapping hM hf hs z).mpr ⟨tau, p, child, condition, he, hv, hq, hCode⟩⟩

def edgeEntry {n m : Nat} (f : Formula (n+2)) (rho : Fin n → Fin m) (sigma child condition : Fin m) : Formula m :=
  .ex (.ex ((Source.SetLanguage.edge sigma.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    ((mapping f (paramsUp (paramsUp rho)) (Fin.last m).castSucc child.castSucc.castSucc).conj
      (ReplacementPredicates.rel f (paramsUp (paramsUp rho)) (Fin.last (m+1)) condition.castSucc.castSucc))))

theorem edgeEntry_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (f : Formula (n+2))
    (rho : Fin n → Fin m) (sigma child condition : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (edgeEntry f rho sigma child condition) ↔
      ∃ tau p, PureKuratowski.PairMember M tau p (v sigma) ∧
        Mapped f (fun i => v (rho i)) tau (v child) ∧ MapRel f (fun i => v (rho i)) p (v condition) := by
  simp only [edgeEntry, Formula.Realize, KuratowskiZF.source_edge, mapping_semantics (M := M),
    rel_semantics (M := M), paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def edgeSentence {n : Nat} (f : Formula (n+2)) : Source.Sentence :=
  let rho : Fin n → Fin (n+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let sigma := (Fin.last n).castSucc.castSucc.castSucc
  let output := (Fin.last (n+1)).castSucc.castSucc
  let child := (Fin.last (n+2)).castSucc
  let condition := Fin.last (n+3)
  ((function f rho).imp ((mapping f rho sigma output).imp
    ((Source.SetLanguage.edge output child condition).iff (edgeEntry f rho sigma child condition)))).close

theorem edge_models {n : Nat} (f : Formula (n+2)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (edgeSentence f)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h hs
  let rho : Fin n → Fin (n+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let sigma := (Fin.last n).castSucc.castSucc.castSucc
  let output := (Fin.last (n+1)).castSucc.castSucc
  let child := (Fin.last (n+2)).castSucc
  let condition := Fin.last (n+3)
  have he := edge_mapping hM ((function_semantics v f rho).mp h)
    ((mapping_semantics v f rho sigma output).mp hs) (v child) (v condition)
  have hl := KuratowskiZF.source_edge v output child condition
  have hr := edgeEntry_semantics v f rho sigma child condition
  exact ⟨fun hz => hr.mpr (he.mp (hl.mp hz)), fun hz => hl.mpr (he.mpr (hr.mp hz))⟩

theorem edge_kernel_certificate {n : Nat} (f : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (edgeSentence f)) :=
  ModelTransfer.derives (fun _ hM => edge_models f hM)

theorem empty_mapping (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f : Formula (n+2)} {params : Fin n → M.Carrier .set} (hf : IsFunction f params)
    (empty : M.Carrier .set) (hEmpty : ∀ x, ¬ (Definitional.Project.FirstOrderSemantics.reduct M).mem x empty) :
    Mapped f params empty empty := by
  obtain ⟨output, hs⟩ := exists_mapping hM f params hf empty
  have heq : output = empty := by
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    constructor
    · intro hz
      obtain ⟨tau, p, _, _, he, _, _, _⟩ := (mem_mapping hM hf hs z).mp hz
      obtain ⟨code, _, hCode⟩ := he
      exact False.elim (hEmpty code hCode)
    · intro hz
      exact False.elim (hEmpty z hz)
  exact heq ▸ hs

def emptySentence {n : Nat} (f : Formula (n+2)) : Source.Sentence :=
  ((function f Fin.castSucc).imp
    ((Formula.all ((Formula.mem (Fin.last (n+1)) (Fin.last n).castSucc).neg)).imp
      (mapping f Fin.castSucc (Fin.last n) (Fin.last n)))).close

theorem empty_models {n : Nat} (f : Formula (n+2)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (emptySentence f)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h hEmpty
  have hEmpty' : ∀ x, ¬ (Definitional.Project.FirstOrderSemantics.reduct M).mem x (v (Fin.last n)) := by
    simpa only [Source.Formula.neg, Formula.Realize, Fin.lastCases_last, Fin.lastCases_castSucc, Definitional.Project.FirstOrderSemantics.reduct] using hEmpty
  exact (mapping_semantics v f Fin.castSucc (Fin.last n) (Fin.last n)).mpr
    (empty_mapping hM ((function_semantics v f Fin.castSucc).mp h) (v (Fin.last n)) hEmpty')

theorem empty_kernel_certificate {n : Nat} (f : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (emptySentence f)) :=
  ModelTransfer.derives (fun _ hM => empty_models f hM)

end PPAC.Migration.ForcingMapConditions
